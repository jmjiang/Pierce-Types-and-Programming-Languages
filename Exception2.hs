{-# LANGUAGE TemplateHaskell, FlexibleInstances, MultiParamTypeClasses,
             FlexibleContexts, UndecidableInstances #-}

----------------------------------------------------------------------
-- Implementation of Chap 14 Exception: Fig 14-3
----------------------------------------------------------------------

module Exception2 (module Unbound.LocallyNameless,
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
data Label = DivideByZero
           | OverFlow
           | FileNotFound
           | FileNotReadable
           deriving (Show, Eq)

data Type = TyUnit
          | TyString
          | TyArr Type Type
          | TyExn Label
          deriving (Show, Eq)

type TmName = Name Term

data Term = TmVar TmName
          | TmAbs Type (Bind TmName Term)
          | TmApp Term Term
          -- TmRaise t
          -- t is the extra information passed to the exception handler
          | TmRaise Term
          -- TmTry t1 t2
          -- t2 now is a function that takes the extra information as an argument
          | TmTry Term Term
          deriving (Show)

$(derive [''Term, ''Type, ''Label])
instance Alpha Term
instance Alpha Type
instance Alpha Label

instance Subst Term Type
instance Subst Term Term where
  isvar (TmVar x) = Just (SubstName x)
  isvar _         = Nothing
instance Subst Term Label

substTest :: Fresh m => Name Term -> Term -> Term -> m Term
substTest n t t' = return $ subst n t t'

isVal :: Term -> Bool
isVal (TmAbs ty b) = True
isVal _ = False

errorType :: Type -> Type
errorType (TyExn DivideByZero) = TyUnit
errorType (TyExn OverFlow) = TyUnit
errorType (TyExn FileNotFound) = TyString
errorType (TyExn FileNotReadable) = TyString

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

-- T-TRY
typeOf ctx (TmTry t1 t2) = do
  ty1 <- typeOf ctx t1
  ty2 <- typeOf ctx t2
  case ty2 of
    (TyArr (TyExn lab) ty1') -> if (ty1 == ty1')
                                  then return ty1
                                  else throwError InvalidTypeError
    _                        -> throwError InvalidTypeError
-- T-EXN
typeOf ctx (TmRaise t) = do
  ty <- typeOf ctx t
  case ty of
    (TyExn lab) -> return $ errorType (TyExn lab)
    _           -> throwError InvalidTypeError

----------------------------------------------------------------------
-- (One-step) Evaluation
----------------------------------------------------------------------
eval :: Fresh m => Term -> m Term
-- E-APPRAISE1
eval (TmApp (TmRaise t1) t2) | (isVal t1) = return $ TmRaise t1
-- E-APPRAISE1
eval (TmApp t1 (TmRaise t2)) | (isVal t1) && (isVal t2) = return $ TmRaise t2
eval (TmRaise t) = do
  t1 <- eval t
  case t of
    (TmRaise t') -> case (isVal t') of
                      True -> return $ TmRaise t'     -- E-RAISERAISE
    _            -> return $ TmRaise t1               -- E-RAISE
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
-- E-TRYRAISE
eval (TmTry (TmRaise t1) t2) | isVal t1 = return $ TmApp t2 t1
eval (TmTry t1 t2) = do
  t1' <- eval t1
  if (isVal t1)
    then return t1                                    -- E-TRYV
    else return $ TmTry t1' t2                        -- E-TRY

evalRec :: Fresh m => Term -> m Term
evalRec t = do
  t' <- eval t
  if (isVal t')
    then return t'
    else evalRec t'




























