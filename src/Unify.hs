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
{-# LANGUAGE QuantifiedConstraints #-}

module Unify
  where

import           Subst

import           Control.Monad.State
import           Control.Monad.Writer

import           Control.Applicative

import           Data.Coerce
import           Data.Kind

import           Data.String

import           Data.Functor.Classes

import           Lens.Micro
import           Lens.Micro.TH
import           Lens.Micro.Mtl

import           Data.Type.Equality

import           Data.Foldable

import           Data.Bifunctor
import           Data.Bitraversable

import           Data.Typeable

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

data UVar a = UVar String a
  deriving (Show, Eq)

getUniq :: UVar Int -> Int
getUniq (UVar _ i) = i

instance IsString (UVar ()) where
  fromString s = UVar s ()

-- instance Eq (UVar Int) where
--   x == y = getUniq x == getUniq y

-- instance Ord (UVar Int) where
--   compare x y = compare (getUniq x) (getUniq y)

-- data UnifyVar a
--   = UnifyVar (UVar Int)
--   | HostVar a

data SomeF f = forall x. (Show x, Typeable x) => SomeF (f x)

onSomeF :: (forall x. Show x => f x -> r) -> SomeF f -> r
onSomeF f (SomeF z) = f z

data UnifyParts v f a
  -- = forall z x. (MonoFoldable z, Element z ~ a) => UnifyChildren (z -> a) z
  = forall g. UnifyChildren (f v a) [SomeF (f v)]
  | UnifyLeaf (forall x. f v x -> Bool)
  | UnifyVar (UVar v)


class Unify (f :: Type -> Type -> Type) where
  -- type VarTy f

  -- getUVars :: f a -> [UVar Int]

  -- | Get the immediate children (does not include itself) and
  -- a reconstruction function.
  unifyParts :: (Show a, Typeable a) => f v a -> UnifyParts v f a

  traverseUVars :: Applicative g => (UVar v -> g (UVar v')) -> f v a -> g (f v' a)

data DepPair' ct a f = forall z. ct z => DepPair a (f z)

type DepPair = DepPair' Show

instance (Show1 f, Show a) => Show (DepPair' Show a f) where
  show (DepPair x fz) = "(" ++ show x ++ " |-> " ++ show1 fz ++ ")"

data DepPair2 f g = forall a b. (Show a, Show b, Typeable a, Typeable b) => DepPair2 (f a) (g b)


-- substDepPair :: (Subst

substDepPair2 :: (Subst1 (UVar v) (f v), Typeable a) => UVar v -> f v a -> DepPair2 (f v) (f v) -> DepPair2 (f v) (f v)
substDepPair2 v fva (DepPair2 x y) = DepPair2 (subst1 v fva x) (subst1 v fva y)

-- instance (Subst1 (UVar Int) (f Int), Unify f) => Subst (UVar Int) (DepPair2' Show (f Int) (f Int)) where
--   -- type Var (DepPair2' Show (f Int) (f Int)) = UVar Int

--   -- var = _
--   subst uv (DepPair2 x y) (DepPair2 x' y') = DepPair2 (subst1 uv x x') (subst1 uv y y')

instance (Show1 f, Show1 g) => Show (DepPair2 f g) where
  show (DepPair2 x y) = "(" ++ show1 x ++ " := " ++ show1 y ++ ")"

newtype Env a f = Env [DepPair a f]
  deriving (Show)

emptyEnv :: Env a f
emptyEnv = Env []

lookupEnv :: Eq a => a -> Env a f -> Maybe (DepPair a f)
lookupEnv x (Env []) = Nothing
lookupEnv x (Env (p@(DepPair x' _) : rest))
  | x' == x = Just p
  | otherwise = lookupEnv x (Env rest)

extendEnv :: Show z => a -> f z -> Env a f -> Env a f
extendEnv x y (Env e) = Env (DepPair x y : e)

newtype Cts f = Cts { getCts :: [DepPair2 f f] }
  deriving (Semigroup, Monoid, Show)

substCts :: (Subst1 (UVar v) (f v), Typeable a) => UVar v -> f v a -> Cts (f v) -> Cts (f v)
substCts v fva (Cts e) = Cts $ map (substDepPair2 v fva) e

extendCts :: (Show a, Show b, Typeable a, Typeable b) => f a -> f b -> Cts f -> Cts f
extendCts x y (Cts rest) = Cts (DepPair2 x y : rest)

data UnifierState (f :: Type -> Type) =
  UnifierState
  { _unifierUniq :: Int
  , _unifierVars :: [(String, Int)]
  -- , _unifierEnv :: Env (UVar Int) f
  }

makeLenses ''UnifierState

initState :: UnifierState f
initState = UnifierState 0 mempty

newtype UnifyError = UnifyError String
  deriving (Show)

newtype Unifier (f :: Type -> Type) r = Unifier { runUnifier :: StateT (UnifierState f) (Either UnifyError) r }
  deriving (Functor, Applicative, Monad, MonadState (UnifierState f))

evalUnifier :: Unifier f r -> Either UnifyError r
evalUnifier = flip evalStateT initState . runUnifier

unifyError :: String -> Unifier f r
unifyError str = Unifier . lift . Left . UnifyError $ str

tagUVar :: UVar () -> Unifier f (UVar Int)
tagUVar (UVar str ()) =
  fmap (lookup str) (use unifierVars)
    >>= \case
      Nothing -> do
        uv@(UVar _ i) <- freshUVar str
        unifierVars %= ((str, i):)
        pure uv
      Just i -> pure $ UVar str i

tagUVars :: Unify f => f () a -> Unifier (f Int) (f Int a)
tagUVars = traverseUVars tagUVar

freshUVar :: String -> Unifier f (UVar Int)
freshUVar str = do
  r <- UVar str <$> use unifierUniq
  unifierUniq %= succ
  pure r

freshUVar' :: Unifier f (UVar Int)
freshUVar' = freshUVar "alpha"

-- nextWorkListItem :: Unifier a (Maybe (a, a))
-- nextWorkListItem =
--   use unifierStateWorkList >>= \case
--     WorkList [] -> pure Nothing
--     WorkList (x:_) -> pure (Just x)

-- extendWorkList :: forall a. a -> a -> Unifier a ()
-- extendWorkList x y = unifierStateWorkList %= coerce ((x,y) :)

-- lookupEnv :: Unify f => UVar Int -> Unifier (f Int) (Maybe (DepPair (UVar Int) (f Int)))
-- lookupEnv i = lookupEnv' i <$> use unifierEnv

-- extendEnv :: forall f a. Show a => (UVar Int) -> f a -> Unifier f ()
-- extendEnv i x = do
--   s <- get
--   put (s { _unifierEnv = extendEnv' i x (_unifierEnv s) })
-- -- extendEnv i x = unifierEnv %= extendEnv' i x
-- -- extendEnv i x = do
-- --   e <- use unifierEnv

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
zipSameLength (x, xs) (y, ys) = do
  unifyGuard x y (length xs == length ys)
  pure $ zip (toList xs) (toList ys)

-- generate :: forall v a b f. (Show a, Show b, Unify f) => f Int a -> f Int b -> Cts (f Int)
-- generate = go mempty
--   where
--     -- go :: WorkList (f v) -> f a -> f b -> WorkList f
--     go cts x y =
--       case (unifyParts x, unifyParts y) of
--         (UnifyChildren f xs, UnifyChildren g ys) ->
--           mconcat $ zipWith (\(SomeF x) (SomeF y) -> generate x y) xs ys
--         _ ->
--           extendCts x y cts

freeUVars :: Unify f => f v a -> [UVar v]
freeUVars = snd . runWriter . traverseUVars (\uv -> tell [uv] *> pure uv)

ctsFreeUVars :: Unify f => Cts (f v) -> [UVar v]
ctsFreeUVars (Cts []) = []
ctsFreeUVars (Cts (DepPair2 x y : rest)) = freeUVars x ++ freeUVars y ++ ctsFreeUVars (Cts rest)

initialCt :: (Show a, Show b, Typeable a, Typeable b) => f Int a -> f Int b -> Cts (f Int)
initialCt x y = Cts [DepPair2 x y]

unify :: (Unify f, Subst1 (UVar Int) (f Int), Show a, Show b, Typeable a, Typeable b, Show1 (f Int)) => f () a -> f () b -> Either UnifyError (Env (UVar Int) (f Int))
unify x0 y0 = evalUnifier $ do
  x <- tagUVars x0
  y <- tagUVars y0
  unifyCts (initialCt x y)

unify' :: (Unify f, Subst1 (UVar Int) (f Int), Show a, Show b, Typeable a, Typeable b, Show1 (f Int)) => f () a -> f () b -> String
unify' x y =
  case unify x y of
    Left (UnifyError str) -> str
    Right r -> show r

unifyCts :: (Unify f, Subst1 (UVar Int) (f Int), Show1 (f Int)) => Cts (f Int) -> Unifier (f Int) (Env (UVar Int) (f Int))
unifyCts (Cts []) = pure emptyEnv
unifyCts (Cts (DepPair2 x0 y0 : cts)) = do
  let xParts = unifyParts x0
      yParts = unifyParts y0

  case (xParts, yParts) of

    (UnifyLeaf f, UnifyLeaf g) -> do
      unifyGuard x0 y0 (f y0 && g x0)
      unifyCts (Cts cts)

    (UnifyVar xv, UnifyVar yv)
      | xv == yv -> unifyCts (Cts cts)

    (UnifyVar xv, _) -> do
      unifyGuard x0 y0 (xv `notElem` freeUVars y0)
      let z = substCts xv y0 (Cts cts)
      extendEnv xv y0 <$> unifyCts z


    (UnifyChildren x xs, UnifyChildren y ys) -> do
      zs <- mconcat . map (\(SomeF x, SomeF y) -> Cts [DepPair2 x y]) <$> zipSameLength (x, xs) (y, ys)
      unifyCts (zs <> Cts cts)

    _ -> cannotUnify x0 y0

    -- (UnifyLeaf {}, UnifyChildren {}) -> cannotUnify x0 y0
    -- (UnifyChildren {}, UnifyLeaf {}) -> cannotUnify x0 y0

      -- -- swap
    -- (Right x, Left y) -> do
      -- -- extendEnv y x0
      -- unifyCts (Cts cts)

      -- -- eliminate
    -- (Left x, Right y)
      -- | x `notElem` freeUVars y0 && x `elem` (ctsFreeUVars (Cts cts)) -> do
      --     undefined



-- unify :: (Unify f, Show a, Show b, Show1 f) => f a -> f b -> Unifier f ()
-- unify x y = unifyWorkList (generate x y)

-- -- unify' :: (Unify f, Show1 f, Show a, Show b) => f a -> f b -> Either UnifyError (Env UVar f)
-- -- unify' x = fmap _unifierEnv . execUnifier . unify x

-- -- unify'' :: (Unify f, Show UVar, Show1 f, Show a, Show b) => f a -> f b -> String
-- -- unify'' x y =
-- --   case unify' x y of
-- --     Left (UnifyError str) -> str
-- --     Right r -> show r

-- -- unify :: (Unify f, Show a, Show b, Show1 f) => f a -> f b -> Unifier f ()
-- -- unify x y =
-- --   case (unifyParts x, unifyParts y) of
-- --     (Left n, Right {}) ->
-- --         lookupEnv n >>= \case
-- --           Just (DepPair _ t) -> unify t y
-- --           Nothing -> extendEnv n y

-- --     (Right {}, Left n) -> unify y x

-- --     (Right (UnifyLeaf f), Right (UnifyLeaf g)) -> unifyGuard x y (f y && g x)
-- --     (Right (UnifyLeaf {}), Right (UnifyChildren {})) -> cannotUnify x y
-- --     (Right (UnifyChildren {}), Right (UnifyLeaf {})) -> cannotUnify x y

-- --     (Right (UnifyChildren f xs), Right (UnifyChildren g ys)) -> do
-- --       zipped <- zipSameLength (f, xs) (g, ys)
-- --       mapM_ (uncurry unify) zipped

-- --     (Left nX, Left nY) ->
-- --       liftA2 (,) (lookupEnv nX) (lookupEnv nY) >>= \case
-- --         (Nothing, Nothing) -> extendEnv nX y
-- --         (Just (DepPair _ xVal), Nothing) -> extendEnv nY xVal
-- --         (Nothing, Just (DepPair _ yVal)) -> extendEnv nX yVal
-- --         (Just (DepPair _ x), Just (DepPair _ y)) -> unify x y

