{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module TreeUnify
  where

import           Data.String
import           Data.Void

import           Control.Monad.State
import           Control.Applicative

import           Unify
import           Subst

import           Lens.Micro
import           Lens.Micro.Mtl

import           Data.Void
import           Data.Functor.Classes

import           Text.Show.Deriving

data Tree a b = Node String [Tree a b] | Var (UVar a) deriving (Show)

type Tree' = Tree ()

deriveShow1 ''Tree

-- type Tree' a = Tree a ()

-- instance Show a => Show1 (Tree a) where
--   lift

-- IsString instances for convenience
instance IsString (Tree a b) where
  fromString x = Node x []

instance Eq a => Subst1 (UVar a) (Tree a) where
  var1 = Var
  subst1 uv e (Var uv') = naiveSubst1 uv e uv'
  subst1 uv e (Node str ts) = Node str $ map (subst1 uv e) ts

instance Unify Tree where
  traverseUVars f (Var uv) = Var <$> f uv
  traverseUVars f (Node str ts) = Node str <$> traverse (traverseUVars f) ts

  unifyParts (Var v) = UnifyVar v
  unifyParts (Node n []) = UnifyLeaf (\case Node n' [] -> n' == n; _ -> False)
  unifyParts n0@(Node _ xs) = UnifyNode (map SomeF xs)

test0 :: Tree' String
test0 = Node "f" []

test1 :: Tree' String
test1 = Node "f" ["x"]

test2 :: Tree' String
test2 = Node "g" ["x"]

test3 :: Tree' String
test3 = Node "f" ["y"]

test4 :: Tree' String
test4 = Node "f" [Var "?v", "z"]

test5 :: Tree' String
test5 = Node "f" [Var "?s", Var "?s"]

test6 :: Tree' String
test6 = Node "f" ["x", "y"]

test7 :: Tree' String
test7 = Node "f" ["y", "z"]

test8 :: Tree' String
test8 = Node "f" ["z", "z"]

