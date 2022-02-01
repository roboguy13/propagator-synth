{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}

module TreeUnify
  where

import           Data.String
import           Data.Void

import           Control.Monad.State
import           Control.Applicative

import           Unify

import           Lens.Micro
import           Lens.Micro.Mtl

data Tree a = Node String [Tree a] | Var a deriving (Show)

-- IsString instances for convenience
instance IsString (Tree a) where
  fromString x = Node x []

instance Unify (Tree String) where
  type VarTy (Tree String) = String

  unifyParts (Var v) = Left v
  unifyParts (Node n []) = Right (UnifyLeaf (\case Node n' [] -> n' == n; _ -> False))
  unifyParts (Node n xs) = Right (UnifyChildren (Node n) xs)

-- solveVarEqs :: forall a. Env a -> Env' a Void
-- solveVarEqs e0 = go e0
--   where
--     go :: Env a -> Env' a Void
--     go (Env []) = emptyEnv
--     go (Env ((v, x):rest)) =
--       case x of
--         Var v2 -> undefined
--         Node n ys -> undefined --extendEnv' v (Node n ys) undefined --(go (Env rest))

test0 :: Tree String
test0 = Node "f" []

test1 :: Tree String
test1 = Node "f" ["x"]

test2 :: Tree String
test2 = Node "g" ["x"]

test3 :: Tree String
test3 = Node "f" ["y"]

test4 :: Tree String
test4 = Node "f" [Var "?v", "z"]

test5 :: Tree String
test5 = Node "f" [Var "?s", Var "?s"]

test6 :: Tree String
test6 = Node "f" ["x", "y"]

