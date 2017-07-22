{-# LANGUAGE TemplateHaskell, FlexibleInstances, MultiParamTypeClasses,
             FlexibleContexts, UndecidableInstances #-}

----------------------------------------------------------------------
-- Implementation of Chap 13 Reference: Fig 13-1
----------------------------------------------------------------------

module Reference (module Unbound.LocallyNameless,
                  module Unbound.LocallyNameless.Alpha,
                  Type(..),
                  Term(..),
                  VarName,
                  LocName,
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
data Type = TyUnit
          | Imp Type Type
          | TyRef Type
          deriving (Show, Eq)

type VarName = Name Term
type LocName = Name Term

data Term = TmUnit
          | Var VarName
          | Lam Type (Bind VarName Term)
          | App Term Term
          | TmRef Term
          | Assign Term Term               -- := in the book
          | Deref Term                     -- ! in the book
          | Loc LocName                    -- store location
          deriving (Show)

$(derive [''Term, ''Type])
instance Alpha Term
instance Alpha Type

instance Subst Term Type
instance Subst Term Term where
  isvar (Var x) = Just (SubstName x)
  isvar _       = Nothing

substTest :: Fresh m => Name Term -> Term -> Term -> m Term
substTest n t t' = return $ subst n t t'

isVal :: Term -> Bool
isVal TmUnit = True
isVal (Lam ty b) = True
isVal (Loc _) = True
isVal _ = False

----------------------------------------------------------------------
-- Typing Context 
----------------------------------------------------------------------
type Ctx = [(VarName, Type)]

emptyCtx :: Ctx
emptyCtx = []

----------------------------------------------------------------------
-- Store
----------------------------------------------------------------------
type Store = [(LocName, Term)]     -- the second Term must be a value

emptyStore :: Store
emptyStore = []

extStore :: LocName -> Term -> Store -> Store
extStore l t st | isVal t == True = (l, t) : st

substStore :: LocName -> Term -> Store -> Store
substStore l t [] = []
substStore l t ((l',t'):st)
  | l == l' = (l, t) : st
  | otherwise = (l', t') : substStore l t st

infix 5 |:|
(|:|) :: (LocName, Term) -> Store -> Store
(l, t) |:| st = extStore l t st

type StoreTy = [(LocName, Type)]

emptyStoreTy :: StoreTy
emptyStoreTy = []

----------------------------------------------------------------------
-- Typechecking
----------------------------------------------------------------------
typeOf :: Fresh m => Ctx -> StoreTy -> Term -> ExceptT TypeException m Type
-- T-UNIT
typeOf _ _ TmUnit = return TyUnit
-- T-VAR
typeOf ctx _ (Var x) = do
  case (lookup x ctx) of
    Nothing -> throwError VarException
    Just ty -> return ty
-- T-ABS
typeOf ctx sty (Lam ty b) = do
  (x, t) <- unbind b
  ty' <- typeOf ((x, ty):ctx) sty t
  return $ Imp ty ty'
-- T-APP
typeOf ctx sty (App t1 t2) = do
  ty1 <- typeOf ctx sty t1
  ty2 <- typeOf ctx sty t2
  case ty1 of
    (Imp ty ty') -> if (ty == ty2)
                      then return ty'
                      else throwError InvalidTypeError
    _            -> throwError InvalidTypeError
-- T-LOC
typeOf _ sty (Loc l) = do
  case (lookup l sty) of
    Nothing -> throwError VarException
    Just ty -> return $ TyRef ty
-- T-REF
typeOf ctx sty (TmRef t) = do
  ty <- typeOf ctx sty t
  return $ TyRef ty
-- T-DEREF
typeOf ctx sty (Deref t) = do
  ty <- typeOf ctx sty t
  case ty of
    (TyRef ty') -> return ty'
    _         -> throwError InvalidTypeError
-- T-ASSIGN
typeOf ctx sty (Assign t1 t2) = do
  ty1 <- typeOf ctx sty t1
  ty2 <- typeOf ctx sty t2
  case ty1 of
    (TyRef ty1') -> if (ty1' == ty2)
                      then return TyUnit
                      else throwError InvalidTypeError
    _            -> throwError InvalidTypeError

----------------------------------------------------------------------
-- (One-step) Evaluation
----------------------------------------------------------------------
-- Should not throw any type error but don't how to the case for E-DEREFLOC otherwise
eval :: Fresh m => (Term, Store) -> ExceptT TypeException m (Term, Store)
-- E-APPABS
eval (App (Lam ty b) t2, st) = do
  (x, t1) <- unbind b
  (t2', st') <- eval (t2, st)
  if (isVal t2)
    then return (subst x t2 t1, st)
    else return (App (Lam ty b) t2', st')
eval (App t1 t2, st) = do
  (t1', st1) <- eval (t1, st)
  (t2', st2) <- eval (t2, st)
  if (isVal t1)
    then return (App t1 t2', st2)     -- E-APP2
    else return (App t1' t2, st1)     -- E-APP1
eval (TmRef t, st) = do
  (t', st') <- eval (t, st)
  -- TODO: how to generate a fresh Name that is not in st?
  if (isVal t)
    then return (TmUnit, st)          -- E-REFV; TODO: WRONG. need a new location
    else return (TmRef t', st')       -- E-REF
-- E-DEREFLOC
eval (Deref (Loc l), st) = do
  case (lookup l st) of
    Just t -> if (isVal t)
                then return (t, st)
                else throwError InvalidTypeError
    Nothing -> throwError InvalidTypeError
-- E-DEREF
eval (Deref t, st) = do
  (t', st') <- eval (t, st)
  return (Deref t', st')
-- E-ASSIGN
eval (Assign (Loc l) t, st) = do
  case (lookup l st) of
    Just t' -> if (isVal t)
                 then return (TmUnit, substStore l t st)
                 else throwError InvalidTypeError
    _       -> return (TmUnit, (l, t) : st)
eval (Assign t1 t2, st) = do
  (t1', st1) <- eval (t1, st)
  (t2', st2) <- eval (t2, st)
  if (isVal t1)
    then return (Assign t1 t2', st2)
    else return (Assign t1' t2, st1)
  
evalRec :: Fresh m => (Term, Store) -> ExceptT TypeException m (Term, Store)
evalRec (t, st) = do
  (t', st') <- eval (t, st)
  if (isVal t')
    then return (t', st')
    else evalRec (t', st')
