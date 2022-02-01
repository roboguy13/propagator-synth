{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ExistentialQuantification #-}
-- {-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleInstances #-}

module Unify
  where

import           Subst

import           Control.Monad.State
import           Control.Applicative

import           Data.Coerce
import           Data.Kind

import           Data.Functor.Classes

import           Lens.Micro
import           Lens.Micro.TH
import           Lens.Micro.Mtl

import           Data.Type.Equality

import           Data.Foldable

-- import           Data.MonoTraversable

show1 :: (Show1 f, Show a) => f a -> String
show1 x = showsPrec1 0 x ""

{-
instance Eq host => Subst Int (UnifyVar host) where
  type Var (UnifyVar host) = Int

  var = id

  -- subst :: UnifyVarName host -> UnifyVarName host -> UnifyVar host -> UnifyVar host
  -- subst = _
-}

-- data UnifyParts a
--   = UnifyChildren ([a] -> a) [a]
--   | UnifyLeaf (a -> Bool)

-- class Unify a where
--   type HostVar a

--   isUnifyVar :: a -> Maybe (UnifyVar (HostVar a))

--   -- | Get the immediate children (does not include itself) and
--   -- a reconstruction function.
--   unifyParts :: a -> UnifyParts a

  -- unifyReconstruct :: [a] -> a

newtype UVar = UVar String
  deriving (Show, Eq, Ord)

data UnifyVar a b
  = UnifyVar b
  | HostVar a

data UnifyParts f a
  -- = forall z x. (MonoFoldable z, Element z ~ a) => UnifyChildren (z -> a) z
  = forall g x. (Show x, Foldable g) => UnifyChildren (g (f x) -> f a) (g (f x))
  | UnifyLeaf (forall x. f x -> Bool)

class (Eq (VarTy f)) => Unify (f :: Type -> Type) where
  type VarTy f

  -- | Get the immediate children (does not include itself) and
  -- a reconstruction function.
  unifyParts :: Show a => f a -> Either (VarTy f) (UnifyParts f a)

data DepPair' ct a f = forall z. ct z => DepPair a (f z)

type DepPair = DepPair' Show

instance (Show1 f, Show a) => Show (DepPair' Show a f) where
  show (DepPair x fz) = "(" ++ show x ++ " |-> " ++ show1 fz ++ ")"

-- newtype Env a f = Env [forall b. (a, f b)]
newtype Env a f = Env [DepPair a f]
  deriving (Show)

emptyEnv :: Env a f
emptyEnv = Env []

lookupEnv' :: Eq a => a -> Env a f -> Maybe (DepPair a f)
lookupEnv' x (Env []) = Nothing
lookupEnv' x (Env (p@(DepPair x' _) : rest))
  | x' == x = Just p
  | otherwise = lookupEnv' x (Env rest)

extendEnv' :: Show z => a -> f z -> Env a f -> Env a f
extendEnv' x y (Env e) = Env (DepPair x y : e)

newtype WorkList a = WorkList { getWorkList :: [(a, a)] }
  deriving (Semigroup, Monoid)

data UnifierState (f :: Type -> Type) =
  UnifierState
  { _unifierStateUniq :: Int
  , _unifierEnv :: Env (VarTy f) f
  }

makeLenses ''UnifierState

initState :: UnifierState f
initState = UnifierState 0 emptyEnv

newtype UnifyError = UnifyError String
  deriving (Show)


newtype Unifier (f :: Type -> Type) r = Unifier { runUnifier :: StateT (UnifierState f) (Either UnifyError) r }
  deriving (Functor, Applicative, Monad, MonadState (UnifierState f))

execUnifier :: Unifier f r -> Either UnifyError (UnifierState f)
execUnifier = flip execStateT initState . runUnifier

unifyError :: String -> Unifier f r
unifyError str = Unifier . lift . Left . UnifyError $ str

-- nextWorkListItem :: Unifier a (Maybe (a, a))
-- nextWorkListItem =
--   use unifierStateWorkList >>= \case
--     WorkList [] -> pure Nothing
--     WorkList (x:_) -> pure (Just x)

-- extendWorkList :: forall a. a -> a -> Unifier a ()
-- extendWorkList x y = unifierStateWorkList %= coerce ((x,y) :)

lookupEnv :: Unify f => VarTy f -> Unifier f (Maybe (DepPair (VarTy f) f))
lookupEnv i = lookupEnv' i <$> use unifierEnv

extendEnv :: forall f a. Show a => VarTy f -> f a -> Unifier f ()
extendEnv i x = do
  s <- get
  put (s { _unifierEnv = extendEnv' i x (_unifierEnv s) })
-- extendEnv i x = unifierEnv %= extendEnv' i x
-- extendEnv i x = do
--   e <- use unifierEnv

--   case extendEnv' i x e of
--     Left z -> pure $ Just z
--     Right e' -> do
--       unifierEnv .= e'
--       pure Nothing

cannotUnify :: (Show1 f, Show a, Show b) => f a -> f b -> Unifier f r
cannotUnify x y =
  Unifier . lift . Left . UnifyError $ unlines
    ["Unify error: Cannot match "
    ,"  " ++ show1 x
    ,"with"
    ,"  " ++ show1 y
    ]

unifyGuard :: (Show1 f, Show a, Show b) => f a -> f b -> Bool -> Unifier f ()
unifyGuard _ _ True = pure ()
unifyGuard x y False = cannotUnify x y

-- zipSameLength :: (Show a, Show b) =>
--   (z -> a, z) -> (z' -> b, z') -> Unifier x [(a, b)]
zipSameLength (f, xs) (g, ys) = do
  unifyGuard (f xs) (g ys) (length xs == length ys)
  pure $ zip (toList xs) (toList ys)

unify' :: (Unify f, Show1 f, Show a, Show b) => f a -> f b -> Either UnifyError (Env (VarTy f) f)
unify' x = fmap _unifierEnv . execUnifier . unify x

unify'' :: (Unify f, Show (VarTy f), Show1 f, Show a, Show b) => f a -> f b -> String
unify'' x y =
  case unify' x y of
    Left (UnifyError str) -> str
    Right r -> show r

unify :: (Unify f, Show a, Show b, Show1 f) => f a -> f b -> Unifier f ()
unify x y =
  case (unifyParts x, unifyParts y) of
    (Left n, Right {}) ->
        lookupEnv n >>= \case
          Just (DepPair _ t) -> unify t y
          Nothing -> extendEnv n y

    (Right {}, Left n) -> unify y x

    (Right (UnifyLeaf f), Right (UnifyLeaf g)) -> unifyGuard x y (f y && g x)
    (Right (UnifyLeaf {}), Right (UnifyChildren {})) -> cannotUnify x y
    (Right (UnifyChildren {}), Right (UnifyLeaf {})) -> cannotUnify x y

    (Right (UnifyChildren f xs), Right (UnifyChildren g ys)) -> do
      zipped <- zipSameLength (f, xs) (g, ys)
      mapM_ (uncurry unify) zipped

    (Left nX, Left nY) ->
      liftA2 (,) (lookupEnv nX) (lookupEnv nY) >>= \case
        (Nothing, Nothing) -> extendEnv nX y
        (Just (DepPair _ xVal), Nothing) -> extendEnv nY xVal
        (Nothing, Just (DepPair _ yVal)) -> extendEnv nX yVal
        (Just (DepPair _ x), Just (DepPair _ y)) -> unify x y

