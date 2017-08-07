{-# LANGUAGE TemplateHaskell, FlexibleInstances, MultiParamTypeClasses,
             FlexibleContexts, UndecidableInstances #-}

----------------------------------------------------------------------
-- Implementation of Figure 23-1: Polymorphic lambda-calculus (System F)
----------------------------------------------------------------------

module SystemF (module Unbound.LocallyNameless,
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

data Type = TyFun Type Type               -- TyFun ty1 ty2: ty1 -> ty2
          | TyVar TyName
          | Forall (Bind TyName Type)     -- Forall (Bind X T): forall X.T
          deriving (Show)

type TmName = Name Term

data Term = TmVar TmName
          | TmAbs Type (Bind TmName Term) -- TmAbs ty (Bind x t): lambda x:ty.t
          | TmApp Term Term
          | TyAbs (Bind TyName Term)      -- TyAbs (Bind ty t): lambda X.t
          | TyApp Term Type               -- TyApp t ty: t [ty]
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
isVal (TmAbs ty b) = True
isVal (TyAbs b) = True
isVal _ = False

----------------------------------------------------------------------
-- Typing Context: term variable binding
----------------------------------------------------------------------
type TmCtx = [(TmName, Type)]

subTmCtx :: [TmName] -> TmCtx -> Maybe TmCtx
subTmCtx _ [] = Just []
subTmCtx (x:xs) ctx = do
  ty <- lookup x ctx
  (subTmCtx xs ctx) >>= (\ctx' -> return ((x, ty) : ctx'))

extractTmCtx :: Fresh m => TmCtx -> Term -> ExceptT TypeException m TmCtx
extractTmCtx ctx t = do
  t' <- fv t
  let mctx' = subTmCtx t' ctx in case mctx' of
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
fv (TmAbs ty b) = do
  (x, t) <- unbind b
  t' <- fv t
  return (t' \\ [x])
fv (TmApp t1 t2) = do
  t1' <- fv t1
  t2' <- fv t2
  return $ t1' ++ t2'

----------------------------------------------------------------------
-- Type Checking
----------------------------------------------------------------------
typeOf :: Fresh m => TmCtx -> TyCtx -> Term -> ExceptT TypeException m Type
-- T-var
typeOf mctx _ (TmVar x) = do
  case (lookup x mctx) of
    Nothing -> throwError VarException
    Just ty -> return ty
-- T-abs
typeOf mctx yctx (TmAbs ty b) = do
  (x, t) <- unbind b
  tty <- typeOf ((x, ty):mctx) yctx t
  return $ TyFun ty tty
-- T-app
typeOf mctx yctx (TmApp t1 t2) = do
  ty1 <- typeOf mctx yctx t1
  ty2 <- typeOf mctx yctx t2
  case ty1 of
    (TyFun ty2 ty) -> return ty
-- T-Tabs
typeOf mctx yctx (TyAbs b) = do
  (a, t) <- unbind b
  ty <- typeOf mctx (a:yctx) t
  return $ Forall (bind a ty)
-- T-Tapp
typeOf mctx yctx (TyApp t ty2) = do
  ty <- typeOf mctx yctx t
  case ty of
    (Forall b) -> do
                  (a, ty1) <- unbind b
                  return $ subst a ty2 ty1
    _          -> throwError InvalidTypeError

----------------------------------------------------------------------
-- Evaluation
----------------------------------------------------------------------
eval :: Fresh m => Term -> m Term
eval (TmApp t1 t2) = do
  t1' <- eval t1
  t2' <- eval t2
  case t1 of
    (TmAbs ty b) -> if (isVal t2)
                    then do
                         (x, t) <- unbind b
                         return $ subst x t2 t  -- E-appabs
                    else return $ TmApp t1 t2'  -- part of E-app2
    _            -> if (isVal t1)
                 then return $ TmApp t1 t2'     -- E-app2
                 else return $ TmApp t1' t2     -- E-app1
eval (TyApp t ty) = do
  case t of
    (TyAbs b) -> do
                 (a, t') <- unbind b
                 return $ subst a ty t'         -- E-TappTabs
    _         -> do
                 t' <- eval t
                 return $ TyApp t' ty           -- E-Tapp
