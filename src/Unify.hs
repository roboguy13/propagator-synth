{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE FlexibleContexts #-}

module Unify
  where

import           Subst

import           Control.Monad.State
import           Control.Applicative

import           Data.Coerce

import           Lens.Micro
import           Lens.Micro.TH
import           Lens.Micro.Mtl

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

data UnifyVar a
  = UnifyVar (VarTy a)
  | HostVar a

data UnifyParts a
  = UnifyChildren ([a] -> a) [a]
  | UnifyLeaf (a -> Bool)

class (Eq (VarTy a)) => Unify a where
  type VarTy a

  -- | Get the immediate children (does not include itself) and
  -- a reconstruction function.
  unifyParts :: a -> Either (VarTy a) (UnifyParts a)

newtype Env a b = Env [(a, b)]
  deriving (Show)

emptyEnv :: Env a b
emptyEnv = Env []

lookupEnv' :: Eq a => a -> Env a t -> Maybe t
lookupEnv' x (Env e) = lookup x e

extendEnv' :: a -> t -> Env a t -> Env a t
extendEnv' x y (Env e) = Env ((x,y) : e)

newtype WorkList a = WorkList { getWorkList :: [(a, a)] }
  deriving (Semigroup, Monoid)

data UnifierState a =
  UnifierState
  { _unifierStateUniq :: Int
  , _unifierEnv :: Env (VarTy a) a
  }

makeLenses ''UnifierState

initState :: UnifierState a
initState = UnifierState 0 emptyEnv

newtype UnifyError = UnifyError String
  deriving (Show)


newtype Unifier a r = Unifier { runUnifier :: StateT (UnifierState a) (Either UnifyError) r }
  deriving (Functor, Applicative, Monad, MonadState (UnifierState a))

evalUnifier :: Unifier a r -> Either UnifyError r
evalUnifier = flip evalStateT initState . runUnifier

unifyError :: String -> Unifier a r
unifyError str = Unifier . lift . Left . UnifyError $ str

-- nextWorkListItem :: Unifier a (Maybe (a, a))
-- nextWorkListItem =
--   use unifierStateWorkList >>= \case
--     WorkList [] -> pure Nothing
--     WorkList (x:_) -> pure (Just x)

-- extendWorkList :: forall a. a -> a -> Unifier a ()
-- extendWorkList x y = unifierStateWorkList %= coerce ((x,y) :)

lookupEnv :: Unify a => VarTy a -> Unifier a (Maybe a)
lookupEnv i = lookupEnv' i <$> use unifierEnv

extendEnv :: forall a. VarTy a -> a -> Unifier a ()
extendEnv i x = unifierEnv %= extendEnv' i x
-- extendEnv i x = do
--   e <- use unifierEnv

--   case extendEnv' i x e of
--     Left z -> pure $ Just z
--     Right e' -> do
--       unifierEnv .= e'
--       pure Nothing

cannotUnify :: (Show a, Show b) => a -> b -> Unifier t r
cannotUnify x y =
  Unifier . lift . Left . UnifyError $ unlines
    ["Unify error: Cannot match "
    ,"  " ++ show x
    ,"with"
    ,"  " ++ show y
    ]

unifyGuard :: (Show a, Show b) => a -> b -> Bool -> Unifier x ()
unifyGuard _ _ True = pure ()
unifyGuard x y False = cannotUnify x y

zipSameLength :: (Show a, Show b) => ([a] -> a, [a]) -> ([b] -> b, [b]) -> Unifier x [(a, b)]
zipSameLength (f, xs) (g, ys) = do
  unifyGuard (f xs) (g ys) (length xs == length ys)
  pure $ zip xs ys

unify :: (Unify t, Show t) => t -> t -> Unifier t ()
unify x y =
  case (unifyParts x, unifyParts y) of
    (Left n, Right {}) ->
        lookupEnv n >>= \case
          Just t -> unify t y
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
        (Just xVal, Nothing) -> extendEnv nY xVal
        (Nothing, Just yVal) -> extendEnv nX yVal
        (Just x, Just y) -> unify x y
