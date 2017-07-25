{-# LANGUAGE TemplateHaskell, FlexibleInstances, MultiParamTypeClasses,
             FlexibleContexts, UndecidableInstances #-}

----------------------------------------------------------------------
-- Implementation of subtypes: Fig. 16-3
-- With additions: Bot type
----------------------------------------------------------------------

module Subtype (module Unbound.LocallyNameless,
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
data Type = TyArr Type Type
          | TyTop
          | TyRecord [(String, Type)]
          | TyBot
          deriving (Show, Eq)

type TmName = Name Term

data Term = TmVar TmName
          | TmAbs Type (Bind TmName Term)
          | TmApp Term Term
          | TmRecord [(String, Term)]
          | TmProj Term String
          | TmIf Term Term Term 
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

isVal :: Term -> Bool
isVal (TmAbs ty b) = True
isVal _ = False

----------------------------------------------------------------------
-- Subtype: The algorithm on Page 212 with reflexivity and SA-BOT
----------------------------------------------------------------------
subtype :: Type -> Type -> Bool
subtype s t | s == t = True
subtype TyBot _ = True
subtype _ TyTop = True
subtype s t = do
  case s of
    (TyArr s1 s2) -> case t of
                       (TyArr t1 t2) -> (subtype t1 s1) && (subtype s2 t2)
    (TyRecord s') -> case t of
                       (TyRecord t') -> recSubtype t' s'
    _             -> False

-- Given a list of pairs (l,t) and a list of pairs (k,s),
-- checks if each l of (l,t) equals k in some (k,s) and s is a subtype of t
recSubtype :: [(String, Type)] -> [(String, Type)] -> Bool
recSubtype [] _ = True
recSubtype _ [] = False
recSubtype ((l,t):lt) ((k,s):ks)
              | recSubtypeHelper (l,t) ((k,s):ks) == True = recSubtype lt ((k,s):ks)
              | otherwise                                 = False

-- Given a pair (l,t) and a list of such pairs,
-- checks if the list contains a pair (k,s) where l == k and s is a subtype of t
recSubtypeHelper :: (String, Type) -> [(String, Type)] -> Bool
recSubtypeHelper _ [] = False
recSubtypeHelper (l,t) ((k,s):ks)
              | (l == k) && (subtype s t == True) = True
              | (l == k) && (subtype s t == False) = False
              | otherwise                          = recSubtypeHelper (l,t) ks

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
-- TA-VAR
typeOf ctx (TmVar x) = do
  case (lookup x ctx) of
    Nothing -> throwError VarException
    Just ty -> return ty
-- TA-ABS
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
    TyBot          -> return ty2                         -- TA-APPBOT
    (TyArr ty ty') -> if (subtype ty2 ty)
                        then return ty'                  -- TA-APP
                        else throwError InvalidTypeError
-- TA-RCD
typeOf ctx (TmRecord []) = return $ TyRecord []
typeOf ctx (TmRecord ((l,t):lts)) = do
  ctx' <- extractCtx ctx t
  t' <- typeOf ctx' t
  (TyRecord ty) <- typeOf ctx (TmRecord lts)
  return $ TyRecord ((l,t'):ty)
typeOf ctx (TmProj (TmRecord []) s) = throwError InvalidTypeError
typeOf ctx (TmProj (TmRecord (t:ts)) s) = do
  ctx' <- extractCtx ctx (TmRecord (t:ts))
  ty <- typeOf ctx' (TmRecord (t:ts))
  case ty of
    TyBot                     -> return TyBot                 -- TA-PROJBOT
    (TyRecord [])             -> throwError InvalidTypeError
    (TyRecord ((l,ty'):ltys)) -> if (l == s)
                                   then return ty'            -- TA-PROJ
                                   else typeOf ctx (TmProj (TmRecord ts) s)

----------------------------------------------------------------------
-- (One-step) Evaluation
----------------------------------------------------------------------
eval :: Fresh m => Term -> m Term
eval (TmApp (TmAbs ty b) t) = do
  (x, t') <- unbind b
  case (isVal t) of
    True -> return $ subst x t t'
eval (TmApp t1 t2) = do
  t1' <- eval t1
  t2' <- eval t2
  if (isVal t1)
    then return $ TmApp t1 t2'
    else return $ TmApp t1' t2

evalRec :: Fresh m => Term -> m Term
evalRec t = do
  t' <- eval t
  if (isVal t')
    then return t'
    else evalRec t'




























