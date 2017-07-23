{-# LANGUAGE TemplateHaskell, FlexibleInstances, MultiParamTypeClasses,
             FlexibleContexts, UndecidableInstances #-}

module SimpleExtensions (module Unbound.LocallyNameless,
                         module Unbound.LocallyNameless.Alpha,
                         Type(..),
                         Term(..),
                         TmName,
                         substTest,
                         TypeException(..)) where

import Prelude
import Data.List
import Unbound.LocallyNameless hiding (fv)
import Unbound.LocallyNameless.Alpha
import Text.Parsec
import Control.Monad.Except

import Errors

----------------------------------------------------------------------
-- Syntax
----------------------------------------------------------------------
data Type = TyBool
          | TyArr Type Type
          | A                 -- (uninterpreted) base type
          | Unit              -- unit type
          | Prod Type Type    -- product type
          | ProdM [Type]      -- tuple type
          | Sum Type Type     -- sum type
          deriving (Show, Eq)

extType:: Type -> Type -> Type
extType ty (ProdM []) = ProdM [ty]
extType ty (ProdM tys) = ProdM (ty:tys)

type TmName = Name Term

data Term = TmTrue
          | TmFalse
          | TmIf Term Term Term
          | TmVar TmName
          | TmAbs Type (Bind TmName Term)
          | TmApp Term Term
          | I                                -- term for the unit type
          | Seq Term Term                    -- sequence: t1; t2
          | As Term Type                    -- ascription: t as T
          | Let Term Type (Bind TmName Term) -- let binding: let x:A be t1 in t2
          | Pair Term Term                   -- pair
          | Fst Term                         -- first projection
          | Snd Term                         -- second projection
          | Tuple [Term]                     -- tuple
          | Proj Int Term                    -- projection for tuple
          | Inl Term Type                    -- inl t as T
          | Inr Term Type                    -- inr t as T
          | Case Term (TmName, Term) (TmName, Term) -- Case t (Inl x, t1) (Inr x, t2)
                                                -- case t of inl x => t1 | inr x => t
          | Fix Term                         -- general recursion
          deriving (Show)

extTerm :: Term -> Term -> Term
extTerm t (Tuple []) = Tuple [t]
extTerm t (Tuple ts) = Tuple (t:ts)

$(derive [''Term, ''Type])

instance Alpha Term
instance Alpha Type

instance Subst Term Type
instance Subst Term Term where
  isvar (TmVar x) = Just (SubstName x)
  isvar _         = Nothing

substTest :: Fresh m => Name Term -> Term -> Term -> m Term
substTest n t t' = return $ subst n t t'

isVal :: Term -> Bool
isVal (TmAbs ty b) = True
isVal I = True
isVal (Pair t1 t2) | (isVal t1) && (isVal t2) = True
isVal (Tuple []) = True
isVal (Tuple (t:ts))
      | isVal t   = isVal (Tuple ts)
      | otherwise = False
isVal (Inl t ty)
      | isVal t   = True
      | otherwise = False
isVal (Inr t ty)
      | isVal t   = True
      | otherwise = False
isVal _ = False

----------------------------------------------------------------------
-- Typing Context 
----------------------------------------------------------------------
type Ctx = [(TmName, Type)]

emptyCtx :: Ctx
emptyCtx = []

extCtx :: Ctx -> TmName -> Type -> Ctx
extCtx ctx x ty = (x, ty) : ctx

infixr 5 |:|
(|:|) :: (TmName, Type) -> Ctx -> Ctx
(x, t) |:| ctx = extCtx ctx x t

subCtx :: [TmName] -> Ctx -> Maybe Ctx
subCtx _ [] = Just emptyCtx
subCtx (x:xs) ctx = do
  ty <- lookup x ctx
  (subCtx xs ctx) >>= (\ctx' -> return ((x, ty) : ctx'))

extractCtx :: Fresh m => Ctx -> Term -> ExceptT TypeException m Ctx
extractCtx ctx t = do
  t' <- fv t
  let mctx' = subCtx t' ctx in case mctx' of
    Just ctx' -> return ctx'
    Nothing   -> throwError InvalidContextError

----------------------------------------------------------------------
-- Free Variable Collection
----------------------------------------------------------------------
fv :: Fresh m => Term -> m [TmName]
fv TmTrue = return []
fv TmFalse = return []
fv (TmIf t1 t2 t3) = do
  t1' <- fv t1
  t2' <- fv t2
  t3' <- fv t3
  return $ t1' ++ t2' ++ t3'
fv (TmVar x) = return [x]
fv (TmAbs ty b) = do
  (x, t) <- unbind b
  t' <- fv t
  return (t' \\ [x])
fv (TmApp t1 t2) = do
  t1' <- fv t1
  t2' <- fv t2
  return $ t1' ++ t2'

----------------------------------------------------------------------
-- Typechecking
-- Use the inversion lemma instead of a direct translation
-- of the typing rules for more accuracy
----------------------------------------------------------------------
typeOf :: Fresh m => Ctx -> Term -> ExceptT TypeException m Type
typeOf ctx (TmVar x) = do
  xctx <- extractCtx ctx (TmVar x)
  case (lookup x ctx) of
    Nothing -> throwError VarException
    Just ty -> return ty

typeOf ctx (TmAbs ty b) = do
  (x, t) <- unbind b
  tty <- typeOf ((x, ty) |:| ctx) t
  return $ TyArr ty tty

typeOf ctx (TmApp t1 t2) = do
  ctx1 <- extractCtx ctx t1
  ctx2 <- extractCtx ctx t2
  ty1 <- typeOf ctx1 t1
  ty2 <- typeOf ctx2 t2
  case ty1 of
    (TyArr ty2 ty) -> return ty

typeOf ctx I = return Unit

typeOf ctx (As t ty) = do
  tctx <- extractCtx ctx t
  tty <- typeOf tctx t
  if (ty == tty)
    then return ty
    else throwError InvalidTypeError

typeOf ctx (Let t ty b) = do
  (x, t') <- unbind b
  tctx <- extractCtx ctx t
  tty <- typeOf tctx t
  ctx' <- extractCtx ((x, ty) |:| ctx) t'
  ty' <- typeOf ctx' t'
  if (tty == ty)
    then return ty'
    else throwError InvalidTypeError

typeOf ctx (Pair t1 t2) = do
  ctx1 <- extractCtx ctx t1
  ctx2 <- extractCtx ctx t2
  ty1 <- typeOf ctx1 t1
  ty2 <- typeOf ctx2 t2
  return $ Prod ty1 ty2
typeOf ctx (Fst t) = do
  ty <- typeOf ctx t
  case ty of
    (Prod t1 _) -> return t1
    _           -> throwError InvalidTypeError
typeOf ctx (Snd t) = do
  ty <- typeOf ctx t
  case ty of
    (Prod _ t2) -> return t2
    _           -> throwError InvalidTypeError

typeOf ctx (Tuple []) = return $ ProdM []
typeOf ctx (Tuple (t:ts)) = do
  ctx' <- extractCtx ctx t
  ty' <- typeOf ctx' t
  ty <- typeOf ctx (Tuple ts)
  return $ extType ty' ty

typeOf ctx (Inl t (Sum ty1 ty2)) = do
  ctx' <- extractCtx ctx t
  ty' <- typeOf ctx' t
  if (ty' == ty1)
    then return $ Sum ty1 ty2
    else throwError InvalidTypeError
typeOf ctx (Inr t (Sum ty1 ty2)) = do
  ctx' <- extractCtx ctx t
  ty' <- typeOf ctx' t
  if (ty' == ty2)
    then return $ Sum ty1 ty2
    else throwError InvalidTypeError

----------------------------------------------------------------------
-- (Multi-step) Evaluation
-- (Based on Fig 9-1. Not completely correct)
----------------------------------------------------------------------
eval :: Fresh m => Ctx -> Term -> ExceptT TypeException m Term
eval ctx (TmApp (TmAbs ty b) t) = do
  (x, t') <- unbind b
  case (isVal t) of
    True -> return $ subst x t t'

eval ctx (TmApp t1 t2) = do
  t1' <- eval ctx t1
  t2' <- eval ctx t2
  if (isVal t1)
    then return $ TmApp t1 t2'
    else return $ TmApp t1' t2

eval ctx (As t ty) = do
  t' <- eval ctx t
  if (isVal t)
    then return t
    else return $ As t' ty

eval ctx (Let t1 ty b) = do
  t1' <- eval ctx t1
  (x, t2) <- unbind b
  if (isVal t1)
    then return (subst x t1 t2)
    else return (Let t1' ty b)

eval ctx (Pair t1 t2) = do
  t1' <- eval ctx t1
  t2' <- eval ctx t2
  if (isVal t1)
    then return (Pair t1 t2')
    else return (Pair t1' t2)
eval ctx (Fst (Pair t1 t2)) = do
  t <- eval ctx (Pair t1 t2)
  if ((isVal t1) && (isVal t2))
    then return t1
    else return (Fst t)
eval ctx (Snd (Pair t1 t2)) = do
  t <- eval ctx (Pair t1 t2)
  if ((isVal t1) && (isVal t2))
    then return t2
    else return (Snd t)

eval ctx (Tuple []) = return $ Tuple []
eval ctx (Tuple (t:ts)) = do
  fst <- eval ctx ((t:ts) !! (evalTupleFind (Tuple (t:ts))))
  return $ Tuple (evalTupleReplace (evalTupleFind (Tuple (t:ts))) fst (t:ts))

eval ctx (Proj 0 (Tuple (t:ts))) = do
  t' <- eval ctx (Tuple (t:ts))
  if (isVal (Tuple (t:ts)))
    then return t
    else return $ Proj 0 t'
eval ctx (Proj n (Tuple (t:ts))) = do
  t' <- eval ctx (Tuple (t:ts))
  if (isVal (Tuple (t:ts)))
    then eval ctx (Proj (n-1) (Tuple ts))
    else return $ Proj n t'

eval ctx (Case t0 (x1, t1) (x2, t2)) = do
  case t0 of
    (Inl v0 ty0) -> if (isVal v0)
                      then return $ subst x1 v0 t1
                      else throwError InvalidArgError
    (Inr v0 ty0) -> if (isVal v0)
                      then return $ subst x2 v0 t2
                      else throwError InvalidArgError
eval ctx (Inl t ty) = do
  t' <- eval ctx t
  if ((isVal t) == False)
    then return $ Inl t' ty
    else throwError InvalidArgError
eval ctx (Inr t ty) = do
  ctx' <- extractCtx ctx t
  t' <- eval ctx' t
  if ((isVal t) == False)
    then return $ Inr t' ty
    else throwError InvalidArgError


evalRec :: Fresh m => Ctx -> Term -> ExceptT TypeException m Term
evalRec ctx t = do
  t' <- eval ctx t
  case t' of
    TmTrue      -> return t'
    TmFalse     -> return t'
    (TmAbs _ _) -> return t'
    _           -> evalRec ctx t'

----------------------------------------------------------------------
-- Utility functions for evaluation
----------------------------------------------------------------------
-- Find the index of the first term in (Tuple t) that is not a value
evalTupleFind :: Term -> Int
evalTupleFind (Tuple []) = 0
evalTupleFind (Tuple (t:ts)) | isVal t = 1 + (evalTupleFind (Tuple ts))

-- Given an integer n, a term t', and a list of terms (t:ts),
-- replace the nth term in (t:ts) by t'
evalTupleReplace :: Int -> Term -> [Term] -> [Term]
evalTupleReplace n t' [] = []
evalTupleReplace n t' (t:ts)
  | n == 0 = t':ts
  | otherwise = t:evalTupleReplace (n-1) t' ts















