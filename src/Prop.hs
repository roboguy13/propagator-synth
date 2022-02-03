{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TemplateHaskell #-}

module Prop
  where

import           Expr
import           Cmd
import           Subst
import           Unify
import           Rewrite

import           Data.Typeable
import           Data.Functor.Classes
import           Text.Show.Deriving

data Prop n
  -- = PropVar Name
  = PropEqual (Expr n Int) (Expr n Int)
  | SepConj (Prop n) (Prop n)

deriving instance Show n => Show (Prop n)

-- instance Eq n => Subst n (Prop n) where
--   type Var (Prop n) = Expr n Int

--   var = ExprVar

--   subst n s (PropEqual x y) = PropEqual (subst n s x) (subst n s y)
--   subst n s (SepConj x y) = SepConj (subst n s x) (subst n s y)

pattern x :==: y = PropEqual x y

type ExprFact' n = Rewrite (Expr n Int)
type CmdFact'  n = (Cmd n, Rewrite (DeepSubst n (Prop n)))

type ExprFact = ExprFact' ()
type CmdFact = CmdFact' ()

natFacts :: [ExprFact]
natFacts = undefined

-- Ring axioms
addComm :: ExprFact
addComm = (#x `Add` #y) :=> (#y `Add` #x)

addAssoc :: ExprFact
addAssoc = ((#x `Add` #y) `Add` #z) :=> (#x `Add` (#y `Add` #z))

addInv :: ExprFact
addInv = ((Negate #x) `Add` #x) :=> #x

addNeutral :: ExprFact
addNeutral = (#x `Add` Lit 0) :=> #x

mulComm :: ExprFact
mulComm = (#x `Mul` #y) :=> (#y `Mul` #x)

mulNeutral :: ExprFact
mulNeutral = (#x `Mul` Lit 1) :=> #x

mulAssoc :: ExprFact
mulAssoc = ((#x `Mul` #y) `Mul` #z) :=> (#x `Mul` (#y `Mul` #z))

mulAnn :: ExprFact
mulAnn = (#x `Mul` Lit 0) :=> Lit 0

distr :: ExprFact
distr = (#x `Mul` (#y `Add` #z)) :=> ((#x `Mul` #y) `Add` (#x `Mul` #z))

-- test :: Expr () Int
-- test = Lit 1 `Add` (Lit 2 `Add` Lit 3)

-- -- Cmd axioms
-- assignFact :: Expr () Int -> CmdFact
-- assignFact e =
--   let xEqY = L ("?x" :==: "?y")
--   in
--   (Assign "?x" e
--   ,Rewrite
--     (DSubst "?x" e xEqY)
--     xEqY
--   )

