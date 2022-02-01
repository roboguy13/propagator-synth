{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}

module Expr
  where

import           Data.String
import           GHC.Tuple (Solo (..))

import           Data.MonoTraversable

import           Subst
import           Unify

getSolo :: Solo a -> a
getSolo (Solo x) = x

data Pair a = Pair a a
  deriving (Functor, Foldable)

onPair :: (a -> a -> b) -> Pair a -> b
onPair f (Pair x y) = f x y

type instance Element (Pair a) = a
type instance Element (Solo a) = a

instance MonoFoldable (Solo a)
instance MonoFoldable (Pair a)

data Expr n a where
  ExprVar :: n -> Expr n Int
  Lit :: Int -> Expr n Int
  ExprTrue :: Expr n Bool
  ExprFalse :: Expr n Bool
  ExprNot :: Expr n Bool -> Expr n Bool
  ExprAnd :: Expr n Bool -> Expr n Bool -> Expr n Bool
  Add :: Expr n Int -> Expr n Int -> Expr n Int
  Negate :: Expr n Int -> Expr n Int
  Mul :: Expr n Int -> Expr n Int -> Expr n Int
  ExprLe :: Expr n Int -> Expr n Int -> Expr n Bool

deriving instance Show n => Show (Expr n a)
deriving instance Eq n => Eq (Expr n a)

instance forall n. IsString n => IsString (Expr n Int) where
  fromString = ExprVar . fromString @n

exprSize :: Expr n a -> Int
exprSize (ExprVar _) = 1
exprSize (Lit _) = 1
exprSize ExprTrue = 1
exprSize ExprFalse = 1
exprSize (ExprNot x) = succ (exprSize x)
exprSize (ExprAnd x y) = succ (exprSize x + exprSize y)
exprSize (Add x y) = succ (exprSize x + exprSize y)
exprSize (Negate x) = succ (exprSize x)
exprSize (Mul x y) = succ (exprSize x + exprSize y)
exprSize (ExprLe x y) = succ (exprSize x + exprSize y)

instance forall n. Eq n => Unify (Expr (UnifyVar n UVar)) where
  type VarTy (Expr (UnifyVar n UVar)) = UVar

  -- unifyParts :: Expr (UnifyVar n UVar) a -> Either UVar (UnifyParts (Expr (UnifyVar n UVar) a))
  unifyParts (ExprVar (UnifyVar v)) = Left v

  unifyParts (ExprVar (HostVar v)) = Right $ UnifyLeaf (\case ExprVar (HostVar v') -> v' == v; _ -> False)
  unifyParts (Lit i) = Right $ UnifyLeaf (\case Lit i' -> i' == i; _ -> False)
  unifyParts ExprTrue = Right $ UnifyLeaf (\case ExprTrue -> True; _ -> False)
  unifyParts ExprFalse = Right $ UnifyLeaf (\case ExprFalse -> True; _ -> False)

  unifyParts (ExprNot x) = Right $ UnifyChildren (ExprNot . getSolo) (Solo x)
  unifyParts (ExprAnd x y) = Right $ UnifyChildren (onPair ExprAnd) (Pair x y)
  unifyParts (Add x y) = Right $ UnifyChildren (onPair Add) (Pair x y)
  unifyParts (Negate x) = Right $ UnifyChildren (Negate . getSolo) (Solo x)
  unifyParts (Mul x y) = Right $ UnifyChildren (onPair Mul) (Pair x y)
  unifyParts (ExprLe x y) = Right $ UnifyChildren (onPair ExprLe) (Pair x y)

class Sized a where
  size :: a -> Int

instance Sized (Expr n a) where
  size = exprSize

-- instance Eq (Expr n a) where
--   x == y = exprSize x == exprSize y

-- instance Ord (Expr n a) where
--   compare x y = compare (exprSize x) (exprSize y)

instance Eq n => Subst n (Expr n a) where
  type Var (Expr n a) = Expr n Int

  var = ExprVar

  -- subst :: Name -> Expr n Int -> Expr n a -> Expr n a
  subst n e (ExprVar v) = naiveSubst n e v
  subst _ _ e'@(Lit {}) = e'
  subst _ _ ExprTrue = ExprTrue
  subst _ _ ExprFalse = ExprFalse
  subst n e (ExprNot e') = ExprNot (subst n e e')
  subst n e (ExprAnd x y) = ExprAnd (subst n e x) (subst n e y)
  subst n e (Add x y) = Add (subst n e x) (subst n e y)
  subst n e (Negate x) = Negate (subst n e x)
  subst n e (Mul x y) = Mul (subst n e x) (subst n e y)
  subst n e (ExprLe x y) = ExprLe (subst n e x) (subst n e y)

