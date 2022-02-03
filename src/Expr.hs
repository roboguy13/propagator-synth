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
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TemplateHaskell #-}

{-# OPTIONS_GHC -Wincomplete-patterns #-}

module Expr
  where

import           Data.String
import           GHC.Tuple (Solo (..))

import           Data.Void

import           Subst
import           Unify

import           GHC.OverloadedLabels
import           GHC.TypeLits

import           Data.Proxy

import           Text.Show.Deriving

getSolo :: Solo a -> a
getSolo (Solo x) = x

data Pair a = Pair a a
  deriving (Functor, Foldable)

onPair :: (a -> a -> b) -> Pair a -> b
onPair f (Pair x y) = f x y

data Expr n a where
  ExprVar :: String -> Expr n Int
  ExprUVar :: UVar n -> Expr n a
  Lit :: Int -> Expr n Int
  ExprTrue :: Expr n Bool
  ExprFalse :: Expr n Bool
  ExprNot :: Expr n Bool -> Expr n Bool
  ExprAnd :: Expr n Bool -> Expr n Bool -> Expr n Bool
  Add :: Expr n Int -> Expr n Int -> Expr n Int
  Negate :: Expr n Int -> Expr n Int
  Mul :: Expr n Int -> Expr n Int -> Expr n Int
  ExprLe :: Expr n Int -> Expr n Int -> Expr n Bool

deriveShow1 ''Expr

pattern UV v = ExprUVar (UVar v ())

instance forall str a. KnownSymbol str => IsLabel str (Expr () a) where
  fromLabel = ExprUVar (UVar (symbolVal (Proxy @str)) ())


  -- | Expr without unification variables
type Expr' = Expr Void

deriving instance Show n => Show (Expr n a)
deriving instance Eq n => Eq (Expr n a)

instance IsString (Expr () Int) where
  fromString s = ExprUVar (UVar s ())
  -- fromString = ExprVar . fromString @n

exprSize :: Expr n a -> Int
exprSize (ExprVar _) = 1
exprSize (ExprUVar _) = 1
exprSize (Lit _) = 1
exprSize ExprTrue = 1
exprSize ExprFalse = 1
exprSize (ExprNot x) = succ (exprSize x)
exprSize (ExprAnd x y) = succ (exprSize x + exprSize y)
exprSize (Add x y) = succ (exprSize x + exprSize y)
exprSize (Negate x) = succ (exprSize x)
exprSize (Mul x y) = succ (exprSize x + exprSize y)
exprSize (ExprLe x y) = succ (exprSize x + exprSize y)

instance Unify Expr where
  -- type VarTy (Expr (UnifyVar n UVar)) = UVar

  -- unifyParts :: Expr (UnifyVar n UVar) a -> Either UVar (UnifyParts (Expr (UnifyVar n UVar) a))
  unifyParts (ExprVar v) = UnifyLeaf undefined
  unifyParts (ExprUVar v) = UnifyVar v

  -- unifyParts (ExprVar (HostVar v)) = Right $ UnifyLeaf (\case ExprVar (HostVar v') -> v' == v; _ -> False)
  unifyParts (Lit i) = UnifyLeaf (\case Lit i' -> i' == i; _ -> False)
  unifyParts ExprTrue = UnifyLeaf (\case ExprTrue -> True; _ -> False)
  unifyParts ExprFalse = UnifyLeaf (\case ExprFalse -> True; _ -> False)

  unifyParts (ExprNot x) = UnifyNode [SomeF x]
  unifyParts (ExprAnd x y) = UnifyNode [SomeF x, SomeF y]
  unifyParts (Add x y) = UnifyNode [SomeF x, SomeF y]
  unifyParts (Negate x) = UnifyNode [SomeF x]
  unifyParts (Mul x y) = UnifyNode [SomeF x, SomeF y]
  unifyParts (ExprLe x y) = UnifyNode [SomeF x, SomeF y]


  traverseUVars f (ExprVar v) = pure $ ExprVar v
  traverseUVars f (ExprUVar v) = ExprUVar <$> f v
  traverseUVars f (Lit i) = pure (Lit i)
  traverseUVars f ExprTrue = pure ExprTrue
  traverseUVars f ExprFalse = pure ExprFalse
  traverseUVars f (ExprNot b) = ExprNot <$> traverseUVars f b
  traverseUVars f (ExprAnd x y) = ExprAnd <$> traverseUVars f x <*> traverseUVars f y
  traverseUVars f (Add x y) = Add <$> traverseUVars f x <*> traverseUVars f y
  traverseUVars f (Negate x) = Negate <$> traverseUVars f x
  traverseUVars f (Mul x y) = Mul <$> traverseUVars f x <*> traverseUVars f y
  traverseUVars f (ExprLe x y) = ExprLe <$> traverseUVars f x <*> traverseUVars f y

class Sized a where
  size :: a -> Int

instance Sized (Expr n a) where
  size = exprSize

-- instance Eq (Expr n a) where
--   x == y = exprSize x == exprSize y

-- instance Ord (Expr n a) where
--   compare x y = compare (exprSize x) (exprSize y)

instance Eq n => Subst1 (UVar n) (Expr n) where
  -- type Var (Expr n a) = Expr n Int

  var1 = ExprUVar

  -- subst :: Name -> Expr n Int -> Expr n a -> Expr n a
  subst1 _ _ (ExprVar v) = ExprVar v
  subst1 n e (ExprUVar v) = naiveSubst1 n e v
  subst1 _ _ e'@(Lit {}) = e'
  subst1 _ _ ExprTrue = ExprTrue
  subst1 _ _ ExprFalse = ExprFalse
  subst1 n e (ExprNot e') = ExprNot (subst1 n e e')
  subst1 n e (ExprAnd x y) = ExprAnd (subst1 n e x) (subst1 n e y)
  subst1 n e (Add x y) = Add (subst1 n e x) (subst1 n e y)
  subst1 n e (Negate x) = Negate (subst1 n e x)
  subst1 n e (Mul x y) = Mul (subst1 n e x) (subst1 n e y)
  subst1 n e (ExprLe x y) = ExprLe (subst1 n e x) (subst1 n e y)

{-
instance Eq n => Subst n (Expr n a) where
  -- type Var (Expr n a) = Expr n Int

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
-}
