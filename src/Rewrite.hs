{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Rewrite where

import           Subst
import           Unify

import           Data.Typeable
import           Data.Functor.Classes

-- When rewriting, ensure that we are always either reducing the size of
-- the expression or applying rules that haven't been applied yet (or both).

data Rewrite a =
  Rewrite a a
  deriving (Show)

pattern x :=> y = Rewrite x y

isReducing :: Ord a => Rewrite a -> Bool
isReducing (Rewrite lhs rhs) = rhs < lhs

flipRewrite :: Rewrite a -> Rewrite a
flipRewrite (Rewrite x y) = Rewrite y x

applyRewrite :: (Unify f, Subst1 (UVar ()) (f ()), Subst1 (UVar Int) (f Int), Show a, Typeable a, Show1 (f Int)) => Rewrite (f () a) -> f () a -> Maybe (f () a)
applyRewrite (Rewrite lhs rhs) e =
  case unify lhs e of
    Left {} -> Nothing
    Right sub -> Just $ applyEnvSubst sub e



