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
          | TyRecord [Type]   -- record type
          | Sum Type Type     -- sum type
          deriving (Show, Eq)

extType:: Type -> Type -> Type
extType ty (ProdM []) = ProdM [ty]
extType ty (ProdM tys) = ProdM (ty:tys)
extType ty (TyRecord []) = TyRecord [ty]
extType ty (TyRecord tys) = TyRecord (ty:tys)


type TmName = Name Term

data Term = TmTrue
          | TmFalse
          | TmIf Term Term Term
          | TmVar TmName
          | TmAbs Type (Bind TmName Term)
          | TmApp Term Term
          | I                                -- term for the unit type
          | Seq Term Term                    -- sequence: t1; t2
          | Asb Term Type                    -- ascription: t as T
          | Let Term Type (Bind TmName Term) -- let binding: let x:A be t1 in t2
          | Pair Term Term                   -- pair
          | Fst Term                         -- first projection
          | Snd Term                         -- second projection
          | Tuple [Term]                     -- tuple
          | Proj Int Term                    -- projection for tuple
          | Record [(Term, Type)]            -- record
          | ProjR Term Term                  -- project for record
          | Inl Term Type                    -- inl t as T
          | Inr Term Type                    -- inr t as T
          | Case Term (Term, Term) (Term, Term) -- Case t (Inl x, t1) (Inr x, t2)
                                                -- case t of inl x => t1 | inr x => t
          | Fix Term                         -- general recursion
          deriving (Show)

$(derive [''Term, ''Type])
instance Alpha Term
instance Alpha Type

instance Subst Term Type
instance Subst Term Term where
  isvar (TmVar x) = Just (SubstName x)
  isvar _         = Nothing

substTest :: Fresh m => Name Term -> Term -> Term -> m Term
substTest n t t' = return $ subst n t t'


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
typeOf ctx TmTrue = return TyBool

typeOf ctx TmFalse = return TyBool

typeOf ctx (TmIf t1 t2 t3) = do
  t1ctx <- extractCtx ctx t1
  t2ctx <- extractCtx ctx t2
  t3ctx <- extractCtx ctx t3
  t1ty <- typeOf t1ctx t1
  t2ty <- typeOf t2ctx t2
  t3ty <- typeOf t3ctx t3
  if (t1ty == TyBool)
    then if (t2ty == t3ty)
         then return t2ty
         else throwError InvalidTypeError
    else throwError InvalidTypeError

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
  t1ctx <- extractCtx ctx t1
  t2ctx <- extractCtx ctx t2
  t1ty <- typeOf t1ctx t1
  t2ty <- typeOf t2ctx t2
  case t1ty of
    (TyArr ty ty') -> if (ty == t2ty)
                      then return ty'
                      else throwError AppSrcError
    _ -> throwError AppSrcError

typeOf ctx I = return Unit

typeOf ctx (Asb t ty) = do
  tctx <- extractCtx ctx t
  tty <- typeOf tctx t
  if (ty == tty)
    then return ty
    else throwError InvalidTypeError

typeOf ctx (Pair t1 t2) = do
  ctx1 <- extractCtx ctx t1
  ctx2 <- extractCtx ctx t2
  ty1 <- typeOf ctx1 t1
  ty2 <- typeOf ctx2 t2
  return (Prod ty1 ty2)

typeOf ctx (Fst t) = do
  ctx' <- extractCtx ctx t
  ty <- typeOf ctx' t
  case ty of
    (Prod ty1 _) -> return ty1
    _            -> throwError InvalidTypeError

typeOf ctx (Snd t) = do
  ctx' <- extractCtx ctx t
  ty <- typeOf ctx' t
  case ty of
    (Prod _ ty2) -> return ty2
    _            -> throwError InvalidTypeError

typeOf ctx (Tuple []) = return $ ProdM []
typeOf ctx (Tuple (t:ts)) = do
  ctx' <- extractCtx ctx t
  ty <- typeOf ctx' t
  ty' <- typeOf ctx (Tuple ts)
  return $ extType ty ty'

typeOf ctx (Proj n (Tuple [])) = throwError InvalidTypeError
typeOf ctx (Proj n (Tuple (t:ts))) = do
  ctx' <- extractCtx ctx t
  ty <- typeOf ctx' t
  if (n == 0)
    then return ty
    else (typeOf ctx (Proj (n-1) (Tuple ts)))
typeOf ctx (Proj n _) = throwError InvalidTypeError

typeOf ctx (Record []) = return $ TyRecord []
typeOf ctx (Record (tt:tts)) = do
  ty <- typeOf ctx (Record tts)
  return $ extType (snd tt) ty

typeOf ctx (ProjR t (Record [])) = throwError InvalidTypeError
typeOf ctx (ProjR t (Record (tt:tts))) = do
  case (fst tt) of
    t -> return $ snd tt
    _ -> typeOf ctx (ProjR t (Record tts))          -- redundant pattern matching?
typeOf ctx (ProjR t _) = throwError InvalidTypeError

typeOf ctx (Inl t (Sum ty1 ty2)) = do
  ty <- typeOf ctx t
  if (ty == ty1)
    then return (Sum ty1 ty2)
    else throwError InvalidTypeError

typeOf ctx (Inr t (Sum ty1 ty2)) = do
  ty <- typeOf ctx t
  if (ty == ty2)
    then return (Sum ty1 ty2)
    else throwError InvalidTypeError

typeOf ctx (Case t0 (TmVar x1, t1) (TmVar x2, t2)) = do
  ctx0 <- extractCtx ctx t0
  ctx1 <- extractCtx ctx t1
  ctx2 <- extractCtx ctx t2
  ty0 <- typeOf ctx0 t0
  ty1 <- typeOf ctx1 t1
  ty2 <- typeOf ctx2 t2
  if ((ty1 == ty2) && (ty0 == (Sum ty1 ty2)))
    then return ty1
    else throwError InvalidTypeError

typeOf ctx (Fix t) = do
  ty <- typeOf ctx t
  case ty of
    (TyArr ty1 ty2) -> if (ty1 == ty2)
                       then return ty1
                       else throwError InvalidTypeError
    _               -> throwError InvalidTypeError
  


----------------------------------------------------------------------
-- (Multi-step) Evaluation
-- (Based on Fig 9-1. Not completely correct)
----------------------------------------------------------------------
eval :: Fresh m => Ctx -> Term -> ExceptT TypeException m Term
eval ctx TmTrue = return TmTrue

eval ctx TmFalse = return TmFalse

eval ctx (TmIf t1 t2 t3) = do
  ctx1 <- extractCtx ctx t1
  ctx2 <- extractCtx ctx t2
  ctx3 <- extractCtx ctx t3
  t1' <- eval ctx1 t1
  t2' <- eval ctx2 t2
  t3' <- eval ctx3 t3
  case t1' of
    TmTrue  -> return t2'
    TmFalse -> return t3'
    _       -> throwError InvalidTypeError

-- eval ctx (TmVar x) = ?
--
eval ctx (TmApp (TmAbs ty b) TmTrue) = do
  (x, t) <- unbind b
  return (subst x TmTrue t)
eval ctx (TmApp (TmAbs ty b) TmFalse) = do
  (x, t) <- unbind b
  return (subst x TmFalse t)
eval ctx (TmApp (TmAbs ty b) (TmAbs ty' b')) = do
  (x, t) <- unbind b
  return (subst x (TmAbs ty' b') t)
eval ctx (TmApp (TmAbs ty b) t) = do
  (x, t') <- unbind b
  tctx <- extractCtx ctx t
  tty <- typeOf tctx t
  if (tty == ty)
    then return (subst x t t')
    else throwError AppSrcError
eval ctx (TmApp TmTrue t) = return t
eval ctx (TmApp TmFalse t) = return t
eval ctx (TmApp t1 t2) = do
  ctx' <- extractCtx ctx t1
  t1' <- eval ctx' t1
  return (TmApp t1' t2)

eval ctx (Asb TmTrue ty) = return TmTrue
eval ctx (Asb TmFalse ty) = return TmFalse
eval ctx (Asb I ty) = return I
eval ctx (Asb t ty) = do
  ctx' <- extractCtx ctx t
  t' <- eval ctx' t
  return (Asb t' ty)

eval ctx (Let t1 ty b) = do
  (x, t2) <- unbind b
  return (subst x t1 t2)

eval ctx (Fst (Pair TmTrue _)) = return TmTrue
eval ctx (Fst (Pair TmFalse _)) = return TmFalse
eval ctx (Fst (Pair (TmAbs ty b) _)) = return (TmAbs ty b)
eval ctx (Fst (Pair t1 t2)) = do
  ctx' <- extractCtx ctx t1
  t1' <- eval ctx' t1
  return t1'

eval ctx (Snd (Pair _ TmTrue)) = return TmTrue
eval ctx (Snd (Pair _ TmFalse)) = return TmFalse
eval ctx (Snd (Pair _ (TmAbs ty b))) = return (TmAbs ty b)
eval ctx (Snd (Pair t1 t2)) = do
  ctx' <- extractCtx ctx t2
  t2' <- eval ctx' t2
  return t2'

eval ctx (Pair TmTrue t) = do
  ctx' <- extractCtx ctx t
  t' <- eval ctx' t
  return (Pair TmTrue t')
eval ctx (Pair TmFalse t) = do
  ctx' <- extractCtx ctx t
  t' <- eval ctx' t
  return (Pair TmFalse t')
eval ctx (Pair (TmAbs ty b) t) = do
  ctx' <- extractCtx ctx t
  t' <- eval ctx' t
  return (Pair (TmAbs ty b) t')
eval ctx (Pair t1 t2) = do
  ctx' <- extractCtx ctx t1
  t' <- eval ctx' t1
  return t'

-- eval ctx (Tuple _) = ?
-- eval ctx (Record _) = ?

eval ctx (Fix (TmAbs ty b)) = do
  (x, t) <- unbind b
  return $ subst x (Fix (TmAbs ty b)) t
eval ctx (Fix t) = do
  t' <- eval ctx t
  return $ Fix t'



evalRec :: Fresh m => Ctx -> Term -> ExceptT TypeException m Term
evalRec ctx t = do
  t' <- eval ctx t
  case t' of
    TmTrue      -> return t'
    TmFalse     -> return t'
    (TmAbs _ _) -> return t'
    _           -> evalRec ctx t'



















