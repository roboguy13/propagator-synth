{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Expr
  where

import           Data.String

import           Subst

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

instance Eq (Expr n a) where
  x == y = exprSize x == exprSize y

instance Ord (Expr n a) where
  compare x y = compare (exprSize x) (exprSize y)

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

