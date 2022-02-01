{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}

module Unify
  where

import           Subst

import           Control.Monad.State
import           Control.Applicative

import           Data.Coerce

import           Lens.Micro
import           Lens.Micro.TH
import           Lens.Micro.Mtl

data UnifyVar host
  = UnifyVar (Int, host)

getUniq :: UnifyVar a -> Int
getUniq (UnifyVar (i, _)) = i

{-
instance Eq host => Subst Int (UnifyVar host) where
  type Var (UnifyVar host) = Int

  var = id

  -- subst :: UnifyVarName host -> UnifyVarName host -> UnifyVar host -> UnifyVar host
  -- subst = _
-}

data UnifyParts a
  = UnifyChildren ([a] -> a) [a]
  | UnifyLeaf (a -> Bool)

class Unify a where
  type HostVar a

  isUnifyVar :: a -> Maybe (UnifyVar (HostVar a))

  -- | Get the immediate children (does not include itself) and
  -- a reconstruction function.
  unifyParts :: a -> UnifyParts a

  -- unifyReconstruct :: [a] -> a

newtype Env a = Env [(Int, a)]
  deriving (Semigroup, Monoid)

lookupEnv' :: Int -> Env a -> Maybe a
lookupEnv' i (Env e) = lookup i e

-- -- | Gives back a 'Left' if the name already exists in the environment.
-- extendEnv' :: Int -> a -> Env a -> Either a (Env a)
-- extendEnv' i x (Env e) =
--   case lookup i e of
--     Nothing -> Right (Env ((i, x) : e))
--     Just z -> Left z

extendEnv' :: Int -> a -> Env a -> Env a
extendEnv' i x (Env e) = Env ((i, x) : e)

newtype WorkList a = WorkList { getWorkList :: [(a, a)] }
  deriving (Semigroup, Monoid)

data UnifierState a =
  UnifierState
  { _unifierStateUniq :: Int
  , _unifierStateWorkList :: WorkList a
  , _unifierEnv :: Env a
  }

makeLenses ''UnifierState

initState :: UnifierState a
initState = UnifierState 0 mempty mempty

newtype UnifyError = UnifyError String
  deriving (Show)


newtype Unifier a r = Unifier { runUnifier :: StateT (UnifierState a) (Either UnifyError) r }
  deriving (Functor, Applicative, Monad, MonadState (UnifierState a))

evalUnifier :: Unifier a r -> Either UnifyError r
evalUnifier = flip evalStateT initState . runUnifier

unifyError :: String -> Unifier a r
unifyError str = Unifier . lift . Left . UnifyError $ str

nextWorkListItem :: Unifier a (Maybe (a, a))
nextWorkListItem =
  use unifierStateWorkList >>= \case
    WorkList [] -> pure Nothing
    WorkList (x:_) -> pure (Just x)

extendWorkList :: forall a. a -> a -> Unifier a ()
extendWorkList x y = unifierStateWorkList %= coerce ((x,y) :)

lookupEnv :: Int -> Unifier a (Maybe a)
lookupEnv i = lookupEnv' i <$> use unifierEnv

extendEnv :: forall a. Int -> a -> Unifier a ()
extendEnv i x = unifierEnv %= extendEnv' i x
-- extendEnv i x = do
--   e <- use unifierEnv

--   case extendEnv' i x e of
--     Left z -> pure $ Just z
--     Right e' -> do
--       unifierEnv .= e'
--       pure Nothing

-- | Generate worklist items
generate :: Unify a => a -> Unifier a ()
generate = undefined

-- | Solve worklist item
solveItem :: (Show a, Unify a) => (a, a) -> Unifier a ()
solveItem (x0, y0) =
  case (isUnifyVar x0, isUnifyVar y0) of
    (Just x, Just {}) -> extendEnv (getUniq x) y0
    (Just x, Nothing) -> extendEnv (getUniq x) y0
    (Nothing, Just y) -> extendEnv (getUniq y) x0

    (Nothing, Nothing) ->
      case (unifyParts x0, unifyParts y0) of
        (UnifyLeaf f, UnifyLeaf g) ->
          unifyGuard x0 y0 (f y0 && g x0)

        (UnifyChildren f xs, UnifyChildren g ys) -> do
          zipped <- zipSameLength (f, xs) (g, ys)
          mapM_ solveItem zipped

        (_, _) -> unifyGuard x0 y0 False

unifyGuard :: (Show a, Show b) => a -> b -> Bool -> Unifier x ()
unifyGuard _ _ True = pure ()
unifyGuard x y False =
  unifyError $
    unlines
      ["Unify error: Cannot match "
      ,"  " ++ show x
      ,"with"
      ,"  " ++ show y
      ]

zipSameLength :: (Show a, Show b) => ([a] -> a, [a]) -> ([b] -> b, [b]) -> Unifier x [(a, b)]
zipSameLength (f, xs) (g, ys) = do
  unifyGuard (f xs) (g ys) (length xs == length ys)
  pure $ zip xs ys

-- unify :: 

