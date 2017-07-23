{-# LANGUAGE TemplateHaskell, FlexibleInstances, MultiParamTypeClasses,
             FlexibleContexts, UndecidableInstances #-}

----------------------------------------------------------------------
-- Implementation of Chap 14 Exception: Fig 14-1, 14-2
----------------------------------------------------------------------

module Exception1 (module Unbound.LocallyNameless,
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
          deriving (Show, Eq)

type TmName = Name Term

data Term = TmVar TmName
          | TmAbs Type (Bind TmName Term)
          | TmApp Term Term
          | TmError
          -- TmTry t1 t2: try t1 with t2
          -- return the result of evaluating t1, unless it aborts,
          -- in which case evaluate the handler t2 instead
          | TmTry Term Term
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
typeOf ctx (TmVar x) = do
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

-- The type for TmError can be implemented using subtype or polymorphism,
-- which are introduced later

-- T-TRY
typeOf ctx (TmTry t1 t2) = do
  ty1 <- typeOf ctx t1
  ty2 <- typeOf ctx t2
  if (ty1 == ty2)
    then return ty1
    else throwError InvalidTypeError

----------------------------------------------------------------------
-- (One-step) Evaluation
----------------------------------------------------------------------
eval :: Fresh m => Ctx -> Term -> m Term
-- E-APPERR1
eval ctx (TmApp TmError t) = return TmError
-- E-APPERR2
eval ctx (TmApp t TmError) = do
  case (isVal t) of
    True -> return TmError
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
eval ctx (TmTry t1 t2) = do
  t1' <- eval ctx t1
  case t1 of
    TmError -> return t2                    -- E-TRYERROR
    _       -> if (isVal t1)
                 then return t1             -- E-TRYV
                 else return $ TmTry t1' t2 -- E-TRY

evalRec :: Fresh m => Ctx -> Term -> m Term
evalRec ctx t = do
  t' <- eval ctx t
  if (isVal t')
    then return t'
    else evalRec ctx t'




























