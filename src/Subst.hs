{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Subst
  where

type Name = String

-- | Deep embedding of a "enrichment" of a given type with substitution
data DeepSubst n a
  = DSubstLeaf a
  | DSubst n (Var a) (DeepSubst n a)

pattern L x = DSubstLeaf x

-- TODO: Make sure the order of substitution makes sense
runDeepSubst :: Subst n a => DeepSubst n a -> a
runDeepSubst (DSubstLeaf x) = x
runDeepSubst (DSubst n x e) = subst n x (runDeepSubst e)

class Eq n => Subst n a where
  type Var a
  var :: n -> Var a
  subst :: n -> Var a -> a -> a

naiveSubst :: forall n a. (Var a ~ a, Subst n a) => n -> a -> n -> a
naiveSubst n x n'
  | n' == n   = x
  | otherwise = var @n @a n'

