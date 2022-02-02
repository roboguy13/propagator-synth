{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Subst
  where

import           Data.Typeable

type Name = String

-- | Deep embedding of a "enrichment" of a given type with substitution
data DeepSubst n a
  = DSubstLeaf a
  | DSubst n a (DeepSubst n a)

pattern L x = DSubstLeaf x

-- TODO: Make sure the order of substitution makes sense
runDeepSubst :: Subst n a => DeepSubst n a -> a
runDeepSubst (DSubstLeaf x) = x
runDeepSubst (DSubst n x e) = subst n x (runDeepSubst e)

class Eq n => Subst n a where
  -- type Var a
  var :: n -> a
  subst :: n -> a -> a -> a

naiveSubst :: forall n a. (Subst n a) => n -> a -> n -> a
naiveSubst n x n'
  | n' == n   = x
  | otherwise = var @n @a n'

class Eq n => Subst1 n f where
  var1 :: n -> f a
  subst1 :: (Typeable a, Typeable b) => n -> f a -> f b -> f b

naiveSubst1 :: forall f n a b. (Subst1 n f, Typeable a, Typeable b) => n -> f a -> n -> f b
naiveSubst1 n x n'
  | n' == n   =
      case gcast @a @b x of
        Just x' -> x'
        Nothing -> var1 n'
  | otherwise = var1 n'

