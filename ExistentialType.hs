{-# LANGUAGE TemplateHaskell, FlexibleInstances, MultiParamTypeClasses,
             FlexibleContexts, UndecidableInstances #-}

module ExistentialType (module Unbound.LocallyNameless,
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
type TyName = Name Type

data Type = TyVar TyName
          | Ex TyName Type                   -- Ex X t: {Exists X, T}
          deriving (Show, Eq)

type TmName = Name Term

data Term = TmVar TmName
          | As Type Term Type
          | Let Term (Bind TyName (Bind TmName Term))
          deriving (Show)

$(derive [''Term, ''Type])
instance Alpha Term
instance Alpha Type

instance Subst Type Type
instance Subst Type Term
instance Subst Term Type
instance Subst Term Term where
  isvar (TmVar x) = Just (SubstName x)
  isvar _         = Nothing

substTest :: Fresh m => Name Term -> Term -> Term -> m Term
substTest n t t' = return $ subst n t t'

isVal :: Term -> Bool
isVal (As _ t _) | isVal t = True
isVal _ = False

----------------------------------------------------------------------
-- Typing Context: term variable binding
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
-- Typing Context: type variable binding
----------------------------------------------------------------------
type TyCtx = [TyName]

----------------------------------------------------------------------
-- Free Variable Collection
----------------------------------------------------------------------
fv :: Fresh m => Term -> m [TmName]
fv (TmVar x) = return [x]
fv (As _ t _) = fv t
fv (Let t b) = do
  (a, b') <- unbind b
  (x, t') <- unbind b'
  fvt <- fv t'
  return $ fvt \\ [x]

----------------------------------------------------------------------
-- Typechecking
----------------------------------------------------------------------
typeOf :: Fresh m => Ctx -> TyCtx -> Term -> ExceptT TypeException m Type
typeOf ctx yctx (As u t2 (Ex tyx ty2)) = do
  ty <- typeOf ctx yctx t2
  if (ty == subst tyx u ty2)
  then return $ Ex tyx ty2
  else throwError InvalidTypeError
typeOf ctx yctx (Let t1 b) = do
  (tyx, b') <- unbind b
  (x, t2) <- unbind b'
  ty1 <- typeOf ctx yctx t1
  case ty1 of
    (Ex tyx ty12) -> typeOf ((x,ty12):ctx) (tyx:yctx) t2
    _             -> throwError InvalidTypeError

----------------------------------------------------------------------
-- (One-step) Evaluation
----------------------------------------------------------------------
eval :: Fresh m => Term -> m Term
eval (Let t1 b) = do
  (tyx, b') <- unbind b
  (x, t2) <- unbind b'
  t1' <- eval t1
  case t1 of
    (As ty11 t12 ty1) -> if (isVal t12)
                         then return $ subst tyx ty11 (subst x t12 t2)     -- E-UnpackPack
                         else return $ Let t1' (bind tyx (bind x t2))      -- E-Unpack
    _                  -> return $ Let t1' (bind tyx (bind x t2))          -- E-Unpack
eval (As ty1 t ty2) = do
  t' <- eval t
  return $ As ty1 t' ty2
