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

import           Lens.Micro
import           Lens.Micro.Mtl

data Tree a = Node String [Tree a] | Var a deriving (Show)

-- IsString instances for convenience
instance IsString (Tree a) where
  fromString x = Node x []

newtype Env a b = Env [(a, b)]
  deriving (Show)

-- type Env a = Env' a a

emptyEnv :: Env a b
emptyEnv = Env []

lookupEnv' :: Eq a => a -> Env a t -> Maybe t
lookupEnv' x (Env e) = lookup x e

extendEnv' :: a -> t -> Env a t -> Env a t
extendEnv' x y (Env e) = Env ((x,y) : e)

newtype UnifyError = UnifyError String
  deriving (Show)

cannotUnify :: (Show a, Show b) => a -> b -> Unifier t r
cannotUnify x y =
  Unifier . lift . Left . UnifyError $ unlines
    ["Unify error: Cannot match "
    ,"  " ++ show x
    ,"with"
    ,"  " ++ show y
    ]

unifyGuard :: (Show a, Show b) => a -> b -> Bool -> Unifier t ()
unifyGuard _ _ True = pure ()
unifyGuard x y False = cannotUnify x y

newtype Unifier' a t r = Unifier { runUnifier :: StateT (Env a t) (Either UnifyError) r }
  deriving (Functor, Applicative, Monad, MonadState (Env a t))

type Unifier t = Unifier' (VarTy t) t

evalUnifier :: Unifier t r -> Either UnifyError (Env (VarTy t) t)
evalUnifier = flip execStateT emptyEnv . runUnifier

lookupEnv :: Unify t => VarTy t -> Unifier t (Maybe t)
lookupEnv x = lookupEnv' x <$> get

extendEnv :: Unify t => VarTy t -> t -> Unifier t ()
extendEnv x t = modify (extendEnv' x t)

zipSameLength :: (Show a, Show b) => ([a] -> a, [a]) -> ([b] -> b, [b]) -> Unifier t [(a, b)]
zipSameLength (f, xs) (g, ys) = do
  unifyGuard (f xs) (g ys) (length xs == length ys)
  pure $ zip xs ys

unify' :: (Unify t, Show t) => t -> t -> Either UnifyError (Env (VarTy t) t)
unify' x = evalUnifier . unify x

unify'' :: (Unify t, Show (VarTy t), Show t) => t -> t -> String
unify'' x y =
  case unify' x y of
    Left (UnifyError str) -> str
    Right r -> show r

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


-- unify (Var n) t2@(Node n2 ys0) =
--   lookupEnv n >>= \case
--     Just t -> unify t t2
--     Nothing -> extendEnv n t2

-- unify t1@(Node {}) v2@(Var {}) = unify v2 t1

-- unify t1@(Node n1 xs0) t2@(Node n2 ys0) = do
--   unifyGuard t1 t2 (n1 == n2)

--   zipped <- zipSameLength (Node n1, xs0) (Node n2, ys0)
--   mapM_ (uncurry unify) zipped

-- unify (Var n1) (Var n2) = do
--   liftA2 (,) (lookupEnv n1) (lookupEnv n2) >>= \case
--     (Nothing, Nothing) -> extendEnv n1 (Var n2)
--     (Just x, Nothing) -> extendEnv n2 x
--     (Nothing, Just y) -> extendEnv n1 y
--     (Just x, Just y) -> unify x y

data UnifyParts a
  = UnifyChildren ([a] -> a) [a]
  | UnifyLeaf (a -> Bool)

class (Eq (VarTy a)) => Unify a where
  type VarTy a

  -- var :: VarTy a -> a

  -- isUnifyVar :: a -> Maybe (VarTy a)

  -- | Get the immediate children (does not include itself) and
  -- a reconstruction function.
  unifyParts :: a -> Either (VarTy a) (UnifyParts a)

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

