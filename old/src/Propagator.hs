-- | Based on Tom Harding's propagators: https://www.youtube.com/watch?v=qYmW4TSBnVI
--

{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE RankNTypes #-}

module Propagator where

import           Prelude hiding (id, (.))
import           Data.STRef
import           Control.Monad.ST
import           Control.Monad.ST.Class
import           Control.Category
import           Control.Applicative
import           Control.Monad

import           Data.Bifunctor

import qualified Data.Map as Map
import           Data.Map (Map)

import           Data.Set (Set)
import qualified Data.Set as Set
import qualified Data.Set.Extra as Set

import           Data.List

import           Data.Coerce

import           Data.Functor.Apply

import           Data.Maybe (catMaybes)

import           Ppr

import Debug.Trace

-- TODO: Keep track of the origin of inconsistencies
data Defined ann a
  = Unknown
  | Known a
  | Inconsistent [(ann, String, String)]
  deriving (Show, Read, Functor, Foldable, Traversable)
  -- deriving (Eq, Ord, Show, Read, Functor, Foldable, Traversable)

instance Bifunctor Defined where
  bimap _ _ Unknown = Unknown
  bimap _ g (Known x) = Known (g x)
  bimap f _ (Inconsistent i) = Inconsistent $ map (\(ann, x, y) -> (f ann, x, y)) i

instance (Ppr ann, Ppr a) => Ppr (Defined ann a) where
  -- ppr _ = "<Defined>"
  ppr x = show (bimap PprShow PprShow x)

-- TODO: Should Known and Unknown potentially give True?
definedEq :: Eq a => Defined ann a -> Defined ann a -> Bool
definedEq Unknown Unknown = True
definedEq (Known x) (Known y) = x == y
definedEq (Inconsistent xs) (Inconsistent ys) = map go xs == map go ys
  where go (_, x, y) = (x, y)
-- definedEq (Inconsistent {}) (Inconsistent {}) = True --False
definedEq _ _ = False

instance Monoid ann => Apply (Defined ann) where
  (<.>) = (<*>)

instance (Monoid ann, Ppr a, Eq a) => Semigroup (Defined ann a) where
  Inconsistent xs <> Inconsistent ys = Inconsistent (xs <> ys)
  Inconsistent xs <> _ = Inconsistent xs
  _ <> Inconsistent ys = Inconsistent ys
  Known x <> Known y
    | x == y        = Known x
    | otherwise     = Inconsistent [(mempty, ppr x, ppr y)]
  Known x <> _      = Known x
  _ <> Known y      = Known y
  _ <> _            = Unknown

instance (Monoid ann, Eq a, Ppr a) => Monoid (Defined ann a) where
  mempty = Unknown

instance Monoid ann => Applicative (Defined ann) where
  pure = Known
  Known f <*> Known x = Known (f x)
  Inconsistent xs <*> Inconsistent ys = Inconsistent (xs <> ys)
  Inconsistent xs <*> _ = Inconsistent xs
  _ <*> Inconsistent ys = Inconsistent ys
  Unknown <*> _ = Unknown
  _ <*> Unknown = Unknown

-- -- NOTE: 'ap' is different from (<*>) with this:
-- instance Monad Defined where
--   return = pure
--   Inconsistent >>= _ = Inconsistent
--   x >>= f = theJoin (fmap f x)
--     where
--       theJoin (Known (Known k)) = Known k
--       theJoin Unknown = Unknown
--       theJoin Inconsistent = Inconsistent

applyToDefined :: (a -> b) -> Defined ann a -> Defined ann b
applyToDefined = fmap

applyToDefined2 :: Monoid ann => (a -> b -> c) -> Defined ann a -> Defined ann b -> Defined ann c
applyToDefined2 = liftA2

-- | Indexed (partial function-like) version of @Defined@
newtype MapDefined ann a b = MkMapDefined (Defined ann (Map a b))
  deriving (Functor, Foldable, Traversable)
  -- deriving (Functor, Apply)

mapDefinedEq :: (Eq a, Eq b) => MapDefined ann a b -> MapDefined ann a b -> Bool
mapDefinedEq (MkMapDefined x) (MkMapDefined y) = definedEq x y

mkMapDefined :: Defined ann (Map a b) -> MapDefined ann a b
mkMapDefined (Known m) = if Map.null m then MkMapDefined Unknown else MkMapDefined (Known m)
mkMapDefined d = MkMapDefined d

instance (Semigroup ann, Ord a) => Apply (MapDefined ann a) where
  -- MkMapDefined (Known f) <.> MkMapDefined (Known x) = mkMapDefined (Known _)
  MkMapDefined (Known f) <.> MkMapDefined (Known x) = mkMapDefined (Known (f <.> x))
  MkMapDefined (Inconsistent xs) <.> MkMapDefined (Inconsistent ys) = mkMapDefined  (Inconsistent (xs <> ys))
  MkMapDefined (Inconsistent xs) <.> _ = mkMapDefined (Inconsistent xs)
  _ <.> MkMapDefined (Inconsistent ys) = mkMapDefined (Inconsistent ys)
  _ <.> _ = mkMapDefined Unknown

mapDefined :: Map a b -> MapDefined ann a b
mapDefined = mkMapDefined . Known

pointMap :: Ord a => (a, b) -> MapDefined ann a b
pointMap (x, y) = mapDefined $ Map.fromList [(x, y)]

pointRestriction :: Ord a => a -> MapDefined ann a b -> MapDefined ann a b
pointRestriction x (MkMapDefined (Known m)) =
  case Map.lookup x m of
    Nothing -> mkMapDefined Unknown
    Just y  -> pointMap (x, y)
pointRestriction _ md = md

rekeyedPointRestriction :: (Ord x, Ord y) => x -> y -> MapDefined ann x a -> MapDefined ann y a
rekeyedPointRestriction origKey newKey (MkMapDefined (Known m)) =
  case Map.lookup origKey m of
    Nothing -> mkMapDefined Unknown
    Just v  -> pointMap (newKey, v)
rekeyedPointRestriction _ _ (MkMapDefined Unknown) = mkMapDefined Unknown
rekeyedPointRestriction _ _ (MkMapDefined (Inconsistent xs)) = mkMapDefined (Inconsistent xs)

rekey :: (Ord x) => x -> x -> MapDefined ann x a -> MapDefined ann x a
rekey origKey newKey (MkMapDefined (Known m)) =
  case Map.lookup origKey m of
    Nothing -> mkMapDefined Unknown
    Just x -> mkMapDefined $ Known $ Map.insert newKey x $ Map.delete origKey m
rekey _ _ md = md

mapDefinedLookup :: Ord a => MapDefined ann a b -> a -> Defined ann b
mapDefinedLookup (MkMapDefined (Known m)) x =
  case Map.lookup x m of
    Just r -> Known r
    Nothing -> Unknown
mapDefinedLookup (MkMapDefined Unknown) _ = Unknown
mapDefinedLookup (MkMapDefined (Inconsistent xs)) _ = Inconsistent xs

mapDefinedCompose :: forall ann a b c. (Ord a, Ord b) => MapDefined ann b c -> MapDefined ann a b -> MapDefined ann a c
mapDefinedCompose (MkMapDefined (Known f)) (MkMapDefined (Known g)) =
  let gAssocs = Map.assocs g
  in
  case map go gAssocs of
    [] -> mkMapDefined Unknown
    xs -> mkMapDefined $ Known $ Map.fromList $ catMaybes xs
  where
    go :: (a, b) -> Maybe (a, c)
    go (x, y) =
      case Map.lookup y f of
        Just z -> Just (x, z)
        Nothing -> Nothing

joinDefined :: Defined ann (Defined ann a) -> Defined ann a
joinDefined (Known x) = x
joinDefined Unknown = Unknown
joinDefined (Inconsistent ann) = Inconsistent ann

collapseMapDefined :: Monoid ann => MapDefined ann a (Defined ann b) -> MapDefined ann a b
collapseMapDefined = mkMapDefined . joinDefined . coerce . sequenceA

instance (Monoid ann, Ppr a, Ppr b, Ord a, Eq b) => Semigroup (MapDefined ann a b) where
  MkMapDefined (Known m1) <> MkMapDefined (Known m2) =
    let inc = Map.intersectionWith (\x y -> (x /= y, (x, y))) m1 m2
    in
    if or . map fst . Map.elems $ inc
      then mkMapDefined (Inconsistent (map (\(ix, (_, (x, y))) -> (mempty, ppr (ix, x), ppr (ix, y))) (Map.assocs inc)))
      else mkMapDefined (Known (m1 <> m2))

  MkMapDefined x <> MkMapDefined y = mkMapDefined (x <> y)

instance (Monoid ann, Ppr a, Ppr b, Ord a, Eq b) => Monoid (MapDefined ann a b) where
  mempty = mkMapDefined Unknown

mapDefinedImage :: (Monoid ann, Ord a) => MapDefined ann a b -> [a] -> Defined ann [b]
mapDefinedImage md xs =
  sequenceA $ map (mapDefinedLookup md) xs

mapDefinedExtend :: (Monoid ann, Ppr a, Ppr b, Ord a, Eq b) => MapDefined ann a b -> (a, b) -> MapDefined ann a b
mapDefinedExtend (MkMapDefined Unknown) p = pointMap p
mapDefinedExtend (MkMapDefined (Inconsistent xs)) _ = mkMapDefined (Inconsistent xs)
mapDefinedExtend md@(MkMapDefined (Known m)) (x, y) =
  case Map.lookup x m of
    Nothing -> mkMapDefined (Known (Map.insert x y m))
    Just y' ->
      if y' == y
        then md
        else mkMapDefined (Inconsistent [(mempty, ppr (x, y'), ppr (x, y))])

newtype IxedCell m ann a b = MkIxedCell { getIxedCell :: STRef (World m) (m (), MapDefined ann a b) }

ixedCell :: MonadST m => MapDefined ann a b -> m (IxedCell m ann a b)
ixedCell df = MkIxedCell <$> liftST (newSTRef (pure (), df))

-- -- known :: a -> ST s (IxedCell s x a)
-- -- known x = MkIxedCell <$> newSTRef (definedFun (const (Known x)))

knownAt :: (Ord x, MonadST m) => (x, a) -> m (IxedCell m ann x a)
knownAt p = MkIxedCell <$> liftST (newSTRef (pure (), pointMap p))

unknown :: MonadST m => m (IxedCell m ann x a)
unknown = MkIxedCell <$> liftST (newSTRef (pure (), mkMapDefined Unknown))

inconsistent :: (Ppr x, Ppr a, MonadST m) => ann -> (x, a) -> (x, a) -> m (IxedCell m ann x a)
inconsistent ann (ixX, x) (ixY, y) = MkIxedCell <$> liftST (newSTRef (pure (), mkMapDefined (Inconsistent [(ann, ppr (ixX, x), ppr (ixY, y))])))

readIxedCell :: MonadST m => IxedCell m ann x a -> m (MapDefined ann x a)
readIxedCell (MkIxedCell ref) =
  snd <$> liftST (readSTRef ref)

-- TODO: Propagate inconsistencies here?
readIxedCellAt :: (MonadST m, Ord x) => IxedCell m ann x a -> x -> m (Defined ann a)
readIxedCellAt (MkIxedCell ref) x =
  (`mapDefinedLookup` x) . snd <$> liftST (readSTRef ref)

ixedCellImage :: (Monoid ann, MonadST m, Ord x) => IxedCell m ann x a -> [x] -> m (Defined ann [a])
ixedCellImage c xs =
  fmap sequenceA $ mapM (readIxedCellAt c) xs

pushToAnnList :: Semigroup ann => ann -> [(ann, a, a)] -> [(ann, a, a)]
pushToAnnList ann = map $ \(existingAnn, x, y) -> (existingAnn <> ann, x, y)

pushAnn :: Semigroup ann => ann -> MapDefined ann x a -> MapDefined ann x a
pushAnn ann (MkMapDefined (Inconsistent xs)) = mkMapDefined (Inconsistent (pushToAnnList ann xs))
pushAnn _ md = md

updateDefined :: (Monoid ann, Ppr x, Ppr a, MonadST m, Ord x, Eq a) => ann -> IxedCell m ann x a -> MapDefined ann x a -> m ()
updateDefined ann (MkIxedCell c) x = do
  (act, md) <- liftST $ readSTRef c
  let mdx = pushAnn ann (md <> x)
  liftST $ writeSTRef c (act, mdx)
  -- when (mdx /= md) act
  when (not (mdx `mapDefinedEq` md)) act

  -- where
  --   go (def, act) = (def <> x, act)

getAct :: MonadST m => IxedCell m ann x a -> m ()
getAct (MkIxedCell c) = fst =<< liftST (readSTRef c)

-- TODO: Propagate inconsistencies here?
update :: (Monoid ann, Ppr x, Ppr a, MonadST m, Ord x, Eq a) => ann -> IxedCell m ann x a -> (x, a) -> m ()
update ann c@(MkIxedCell ref) (x, y) = do
  -- md <- readIxedCellAt c x
  (act, md) <- liftST $ readSTRef ref
  liftST $ writeSTRef ref (act, pushAnn ann (mapDefinedExtend md (x, y)))
  act
  -- act
  -- updateDefined c (definedFun f)
  -- where
  --   f z
  --     | z == x    = Known y
  --     | otherwise = Unknown

watch :: (Semigroup ann, MonadST m) => ann -> IxedCell m ann x a -> (MapDefined ann x a -> m ()) -> m ()
watch ann c@(MkIxedCell ref) k = do
  (act, md_) <- liftST $ readSTRef ref
  let md = pushAnn ann md_

  liftST $ writeSTRef ref (act *> prop md, md)
  -- modifySTRef ref (`extendAct` prop)
  prop md
  where
    prop md = do -- k md
      (act, md) <- liftST $ readSTRef ref
      k md
    -- go def = (def, act *> prop)

unaryWith :: (Monoid ann, Ord x, Ord y, Ppr y, Ppr b, Eq a, Eq b, MonadST m) =>
  ann -> (MapDefined ann x a -> MapDefined ann y a) -> (a -> m (Defined ann b)) -> IxedCell m ann x a -> IxedCell m ann y b -> m ()
unaryWith ann modifyMD f cX cY =
  watch ann cX (updateDefined ann cY <=< (fmap collapseMapDefined . sequenceA . fmap f . modifyMD))
  -- watch cX (updateDefined cY . _ f . modifyMD)

  -- watch cX (updateDefined cY . (knownFun f .))

unary :: (Monoid ann, Ppr x, Ppr b, Ord x, Eq a, Eq b, MonadST m) => ann -> (a -> b) -> IxedCell m ann x a -> IxedCell m ann x b -> m ()
unary ann f = unaryWith ann id (pure . Known . f)

unaryAt :: (Monoid ann, Ppr x, Ppr b, Ord x, Eq a, Eq b, MonadST m) => ann -> x -> (a -> b) -> IxedCell m ann x a -> IxedCell m ann x b -> m ()
unaryAt ann x f = unaryWith ann (pointRestriction x) (pure . Known . f)

unaryAt2 :: (Monoid ann, Ppr x, Ppr y, Ppr b, Ord x, Ord y, Eq a, Eq b, MonadST m) => ann -> x -> y -> (a -> b) -> IxedCell m ann x a -> IxedCell m ann y b -> m ()
unaryAt2 ann x y f = unaryWith ann (rekeyedPointRestriction x y) (pure . Known . f)

unaryAt2M :: (Monoid ann, Ppr x, Ppr y, Ppr b, Ord x, Ord y, Eq a, Eq b, MonadST m) => ann -> x -> y -> (a -> m (Defined ann b)) -> IxedCell m ann x a -> IxedCell m ann y b -> m ()
unaryAt2M ann x y = unaryWith ann (rekeyedPointRestriction x y)

binaryWith :: forall m ann x y z a b c.
    (Monoid ann, Ppr z, Ppr c, Ord x, Ord y, Ord z, Eq a, Eq b, Eq c, MonadST m) =>
  ann
  -> (forall r. MapDefined ann x r -> MapDefined ann y r) -> (forall r. MapDefined ann y r -> MapDefined ann z r)
  -> (a -> b -> c)
  -> IxedCell m ann x a -> IxedCell m ann y b -> IxedCell m ann z c -> m ()
binaryWith ann modifyMD_xy modifyMD_yz f cA cB cC = do
  watch ann cA $ \g -> do
    readIxedCell cB >>= \h ->
      updateDefined ann cC (go (modifyMD_xy g) h)

  watch ann cB $ \g -> do
    readIxedCell cA >>= \h ->
      updateDefined ann cC (go (modifyMD_xy h) g)
  where
    -- go :: MapDefined x a -> MapDefined x b -> MapDefined z c
    go g h = modifyMD_yz (f <$> g <.> h)

trinaryWith :: forall m ann x y z w a b c d. (Monoid ann, Ppr w, Ppr d, Ord x, Ord y, Ord z, Ord w, Eq a, Eq b, Eq c, Eq d, MonadST m) =>
  ann
  -> (forall r. MapDefined ann x r -> MapDefined ann y r) -> (forall r. MapDefined ann y r -> MapDefined ann z r) -> (forall r. MapDefined ann z r -> MapDefined ann w r)
  -> (a -> b -> c -> d) -> IxedCell m ann x a -> IxedCell m ann y b -> IxedCell m ann z c -> IxedCell m ann w d -> m ()
trinaryWith ann modifyMD_xy modifyMD_yz modifyMD_zw f cA cB cC cD = do
  watch ann cA $ \g -> do
    readIxedCell cB >>= \h ->
      readIxedCell cC >>= \i ->
        updateDefined ann cD (go (modifyMD_xz g) (modifyMD_yz h) i)

  watch ann cB $ \g -> do
    readIxedCell cA >>= \h ->
      readIxedCell cC >>= \i ->
        updateDefined ann cD (go (modifyMD_xz h) (modifyMD_yz g) i)

  watch ann cC $ \g -> do
    readIxedCell cA >>= \h ->
      readIxedCell cB >>= \i ->
        updateDefined ann cD (go (modifyMD_xz h) (modifyMD_yz i) g)

  where
    go g h i = modifyMD_zw (f <$> g <.> h <.> i)
    modifyMD_xz = modifyMD_yz . modifyMD_xy

trinary :: (Monoid ann, Ppr x, Ppr d, Ord x, Eq a, Eq b, Eq c, Eq d, MonadST m) =>
  ann -> (a -> b -> c -> d) -> IxedCell m ann x a -> IxedCell m ann x b -> IxedCell m ann x c -> IxedCell m ann x d -> m ()
trinary ann = trinaryWith ann id id id

trinaryAt2 :: (Monoid ann, Ppr w, Ppr x, Ppr d, Ord x, Ord y, Ord z, Ord w, Eq a, Eq b, Eq c, Eq d, MonadST m) =>
  ann ->
  x -> y -> z -> w -> (a -> b -> c -> d) -> IxedCell m ann x a -> IxedCell m ann y b -> IxedCell m ann z c -> IxedCell m ann w d -> m ()
trinaryAt2 ann x y z w = trinaryWith ann (rekeyedPointRestriction x y) (rekeyedPointRestriction y z) (rekeyedPointRestriction z w)

binary :: forall m ann x a b c. (Monoid ann, Ppr x, Ppr c, Ord x, Eq a, Eq b, Eq c, MonadST m) => ann -> (a -> b -> c) -> IxedCell m ann x a -> IxedCell m ann x b -> IxedCell m ann x c -> m ()
binary ann = binaryWith ann id id

binaryAt :: (Monoid ann, Ppr x, Ppr c, Ord x, Eq a, Eq b, Eq c, MonadST m) => ann -> x -> (a -> b -> c) -> IxedCell m ann x a -> IxedCell m ann x b -> IxedCell m ann x c -> m ()
binaryAt ann x = binaryWith ann id (pointRestriction x)

binaryAt2 :: (Monoid ann, Ppr z, Ppr c, Ord x, Ord y, Ord z, Eq a, Eq b, Eq c, MonadST m) =>
  ann -> x -> y -> z -> (a -> b -> c) -> IxedCell m ann x a -> IxedCell m ann y b -> IxedCell m ann z c -> m ()
binaryAt2 ann x y z = binaryWith ann (rekeyedPointRestriction x y) (rekeyedPointRestriction y z)

type Cell m ann = IxedCell m ann ()

known :: MonadST m => a -> m (Cell m ann a)
known x = knownAt ((), x)

-- knownAt p = MkIxedCell <$> newSTRef (pure (), pointMap p)
defined :: (Monoid ann, Ppr a, MonadST m, Eq a) => Defined ann a -> m (Cell m ann a)
defined (Known x) = MkIxedCell <$> liftST (newSTRef (pure (), pointMap ((), x)))
defined Unknown = MkIxedCell <$> liftST (newSTRef (pure (), mempty))
defined (Inconsistent xs) = MkIxedCell <$> liftST (newSTRef (pure (), MkMapDefined (Inconsistent xs)))

zipper :: [a] -> [(a, [a])]
zipper = go []
  where
    go soFar [] = []
    go soFar (x:xs) = (x, soFar ++ xs) : go (soFar ++ [x]) xs

nub' :: Ord a => [a] -> [a]
nub' = Set.toList . Set.fromList

-- sequenceCells :: (Monoid ann, Ppr a, MonadST m, Eq a) => ann -> Set (Cell m ann a) -> m (Cell m ann (Set a))
sequenceCells :: (Monoid ann, Ord a, Ppr a, MonadST m, Eq a) => ann -> [Cell m ann a] -> m (Cell m ann [a])
sequenceCells ann cs = do
  r <- unknown
  forM (zipper cs) $ \(c, rest) ->
    watch ann c $ \f -> do
      case mapDefinedLookup f () of
        Unknown -> return ()
        Inconsistent xs -> updateDefined ann r (mkMapDefined (Inconsistent xs))
        Known x ->
          sequenceA <$> fmap (`mapDefinedLookup` ()) <$> mapM readIxedCell rest >>= \case
            Unknown -> return ()
            Inconsistent xs -> updateDefined ann r (mkMapDefined (Inconsistent xs))
            Known xs -> update ann r ((), nub' (x : xs))
  return r

readCell :: MonadST m => Cell m ann a -> m (Defined ann a)
readCell c = readIxedCellAt c ()

sameAt :: (Monoid ann, Ppr x, Ppr a, Ord x, Eq a, MonadST m) => ann -> x -> IxedCell m ann x a -> IxedCell m ann x a -> m ()
sameAt ann x c1 c2 = do
  unaryAt ann x id c1 c2
  unaryAt ann x id c2 c1

sameAt2 :: (Monoid ann, Ppr x, Ppr y, Ppr a, Ord x, Ord y, Eq a, MonadST m) => ann -> x -> y -> IxedCell m ann x a -> IxedCell m ann y a -> m ()
sameAt2 ann x y c1 c2 = do
  unaryAt2 ann x y id c1 c2
  unaryAt2 ann y x id c2 c1

add :: (Monoid ann, Ppr x, Ppr a, Ord x, Eq a, Num a, MonadST m) => ann -> IxedCell m ann x a -> IxedCell m ann x a -> IxedCell m ann x a -> m ()
add ann cX cY cZ = do
    -- cX + cY = cZ
  binary ann (+) cX cY cZ

    -- cZ - cY = cX
  binary ann (-) cZ cY cX

    -- cZ - cX = cY
  binary ann (-) cZ cX cY

negation :: (Monoid ann, Ppr x, Ppr a, Ord x, Eq a, Num a, MonadST m) => ann -> IxedCell m ann x a -> IxedCell m ann x a -> m ()
negation ann cX cY = do
  unary ann negate cX cY
  unary ann negate cY cX




ifThenElse :: Bool -> a -> a -> a
ifThenElse True t _ = trace "True" t
ifThenElse False _ f = trace "False" f

example1 :: forall s. ST s (Defined () Int, Defined () Int, Defined () Int)
example1 = do
  x <- known 2 :: ST s (Cell (ST s) () Int)
  y <- known 3 :: ST s (Cell (ST s) () Int)

  z <- unknown
  w <- unknown
  o <- unknown

  add () x y z
  negation () z w
  add () y w o

  -- sameAt () x y


  [a, b, c] <- mapM readCell [z, w, o]
  return (a, b, c)

example2 :: forall s. ST s (Defined () Int)
example2 = do
  x <- ixedCell (pointMap ('a', 1))
  y <- ixedCell (pointMap ('a', 2))
  z <- unknown
  w <- unknown

  updateDefined () x $ pointMap ('a', 10)
  -- sameAt 'b' x w
  sameAt () 'a' z w

  add () x y z
  readIxedCellAt w 'a'

example3 :: forall s. ST s (Defined () Char)
example3 = do
  c <- unknown :: ST s (Cell (ST s) () Bool)
  t <- unknown
  f <- unknown

  r <- unknown

  trinary () ifThenElse c t f r

  updateDefined () t $ pointMap ((), 't')
  updateDefined () c $ pointMap ((), False)

  updateDefined () f $ pointMap ((), 'f')

  readCell r

example4 :: forall s. ST s (Defined () Char)
example4 = do
  x <- unknown :: ST s (Cell (ST s) () Char)
  y <- unknown
  z <- known 'a'

  sameAt2 () () () x y
  sameAt2 () () () z y

  -- updateDefined x $ pointMap ((), 'a')

  readCell y

