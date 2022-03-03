--
-- Horn clause satisfiability algorithm
--

{-# LANGUAGE GADTs #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}

module Horn
  where

-- import           Unify
-- import           Subst

import           Data.Coerce
import           Data.Void
import           Data.Typeable
import           Data.Foldable

import           Data.Set (Set)
import qualified Data.Set as Set

import           GHC.Stack

data HornAtom_ x v where
  HornVar_ :: x -> v -> HornAtom_ x v
  deriving Show

pattern HornVar uv = HornVar_ () uv
-- pattern HornSymbol s = HornSymbol_ () s

data Horn_ x v where
  HornImplies_ :: x -> HornAtom_ x v -> [HornAtom_ x v] -> Horn_ x v
  HornFact_ :: x -> HornAtom_ x v -> Horn_ x v
  HornGoal_ :: x -> [HornAtom_ x v] -> Horn_ x v
  deriving Show

type Horn = Horn_ ()

pattern HornImplies u xs = HornImplies_ () u xs
pattern HornFact x = HornFact_ () x
pattern HornGoal xs = HornGoal_ () xs

class Ord v => HornVars v a where
  hornVars :: a -> Set v

instance HornVars v a => HornVars v [a] where
  hornVars = Set.unions . map hornVars

instance Ord v => HornVars v (HornAtom_ x v) where
  hornVars (HornVar_ _ v) = Set.singleton v

instance Ord v => HornVars v (Horn_ x v) where
  hornVars (HornImplies_ _ x xs) = hornVars x <> hornVars xs
  hornVars (HornFact_ _ x) = hornVars x
  hornVars (HornGoal_ _ xs) = hornVars xs

lookup' :: (Eq a, HasCallStack) => a -> [(a, b)] -> b
lookup' x assocs =
  case lookup x assocs of
    Nothing -> error "lookup'"
    Just y -> y

-- | Precondition: All variables are in assignment
class Ord v => EvalHorn v a where
  evalHorn :: [(v, Bool)] -> a -> Bool

instance Ord v => EvalHorn v (HornAtom_ x v) where
  evalHorn assocs (HornVar_ _ v) = lookup' v assocs

instance Ord v => EvalHorn v (Horn_ x v) where
  evalHorn assocs (HornFact_ _ x) = evalHorn assocs x
  evalHorn assocs (HornImplies_ _ h xs) = evalHorn assocs h && not (and (map (evalHorn assocs) xs))
  evalHorn assocs (HornGoal_ _ xs) = not (and (map (evalHorn assocs) xs))

select :: (a -> Bool) -> [a] -> Maybe (a, [a])
select p = go []
  where
    go acc [] = Nothing
    go acc (x:xs)
      | p x = Just (x, acc ++ xs)
      | otherwise = go (x:acc) xs

flipAssigned :: (Eq v, HasCallStack) => [(v, Bool)] -> v -> [(v, Bool)]
flipAssigned [] v = error "flipAssigned"
flipAssigned ((v', x):xs) v
  | v' == v = (v', not x):xs
  | otherwise = (v', x) : flipAssigned xs v

getPositive :: Horn_ x v -> Maybe v
getPositive (HornFact_ z (HornVar_ _ x)) = Just x
getPositive (HornImplies_ z (HornVar_ _ x) _) = Just x
getPositive (HornGoal_ {}) = Nothing

data Unsat_ x v = Unsat (Horn_ x v) [(v, Bool)]
  deriving (Show)

hornSat :: forall x v. (Ord v) => [Horn_ x v] -> Either (Unsat_ x v) [(v, Bool)]
hornSat cs = go (map (, False) (toList (hornVars cs)))
  where
    go :: [(v, Bool)] -> Either (Unsat_ x v) [(v, Bool)]
    go assocs =
      case select (not . evalHorn assocs) cs of
        Nothing -> Right assocs
        Just (c, rest) ->
          case getPositive c of
            Nothing -> Left $ Unsat c assocs
            Just v -> go (flipAssigned assocs v)


{-
instance forall v. Eq v => Subst1 (UVar v) (Unify0 (Horn_ ()) v) where
  var1 = Unify0 . HornFact . HornVar

  subst1 uv0 x0 y0 = coerce $ go uv0 (coerce x0) (coerce y0)
    where
      coerce' :: Horn_ () v -> Unify0 (Horn_ ()) v Void
      coerce' = coerce

      coerce'' :: Unify0 (Horn_ ()) v Void -> Horn_ () v
      coerce'' = coerce

      go :: UVar v -> Horn_ () v -> Horn_ () v -> Horn_ () v
      go uv e (HornFact (HornVar uv')) = naiveSubst uv e uv'
      go uv e (HornGoal xs0) = HornGoal (go' xs0)
        where
          go' [] = []
          go (HornVar uv':xs) = naiveSubst uv e uv' : go xs
      go uv e (HornImplies h t) =
-}

