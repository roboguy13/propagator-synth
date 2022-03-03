{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PatternSynonyms #-}

module AST
  where

import           Data.String

newtype Name = MkName String
  deriving (Eq, Ord, Show)

instance IsString Name where
  fromString = MkName

data SuslikType = BoolType | IntType | LocType deriving (Eq, Ord)

data Expr a where
  Var :: Name -> Expr IntType
  Old :: Name -> Expr IntType -- | Refers to source data structure of a transformation
  -- New :: Name -> Expr IntType -- | Refers to target data structure of a transformation

  Lit :: Int -> Expr IntType

  Add :: Expr IntType -> Expr IntType -> Expr IntType
  Sub :: Expr IntType -> Expr IntType -> Expr IntType
  Mul :: Expr IntType -> Expr IntType -> Expr IntType

  ExprBool :: Bool -> Expr BoolType

  Le :: Expr IntType -> Expr IntType -> Expr BoolType
  And :: Expr BoolType -> Expr BoolType -> Expr BoolType
  Or :: Expr BoolType -> Expr BoolType -> Expr BoolType
  Not :: Expr BoolType -> Expr BoolType
  Equal :: Expr IntType -> Expr IntType -> Expr BoolType

  Self :: Expr a

  Access :: Name -> Name -> Expr IntType -- | Field accessor

  -- Index :: Name -> Expr IntType -> Expr IntType -- | List indexing

  -- Head :: Expr ListType -> Expr IntType
  -- Tail :: Expr ListType -> Expr ListType
  -- IsNull :: Expr ListType -> Expr BoolType
  IsNull :: Expr a -> Expr BoolType

  Apply :: PredApply -> Expr BoolType

(.==) = Equal
(.*) = Mul
(.+) = Add
(.-) = Sub
(.&&) = And
(.||) = Or

 -- | Predicate application
data PredApply where
  MkPredApply :: Name -> [Name] -> PredApply

pattern App f args = Apply (MkPredApply f args)

data Cmd where
  Assign :: Name -> Expr IntType -> Cmd
  IfThenElse :: Expr BoolType -> Cmd -> Cmd -> Cmd
  Seq :: Cmd -> Cmd -> Cmd

data Implication a b = a :=> b

type StructInv = Implication (Expr BoolType) [Expr BoolType]

implLhs :: Implication a b -> a
implLhs (x :=> _) = x

implRhs :: Implication a b -> b
implRhs (_ :=> y) = y

data Struct =
  MkStruct
  { structName :: Name
  , structFields :: [(Name, SuslikType)]
  , structInvs :: [StructInv]
  -- , structCollecting :: [(Name, [Name])] -- | Collect these into set arguments for the inductive predicate
  }

data StructTransform =
  MkStructTransform
  -- { structTransformArgs :: [Name]
  { structTransformFrom :: Struct
  , structTransformTo   :: Struct
  }

-- synthStructTransform :: StructTransform -> Cmd
-- synthStructTransform = undefined

isRec :: Name -> Expr a -> Bool
isRec recName = go
  where
    go :: Expr b -> Bool
    go (Var _) = False
    go (Old n) = False

    go (Lit i) = False
    go (Add x y) = go x || go y
    go (Sub x y) = go x || go y
    go (Mul x y) = go x || go y

    go (ExprBool True) = False
    go (ExprBool False) = False

    go (Le x y) = go x || go y
    go (And x y) = go x || go y
    go (Or x y) = go x || go y
    go (Not x) = go x
    go (Equal x y) = go x || go y

    go (IsNull x) = go x

    go (App f _) = f == recName


exprOldNames :: Expr a -> [Name]
exprOldNames = go
  where
    go :: Expr b -> [Name]
    go (Var _) = []
    go (Old n) = [n]

    go (Lit i) = []
    go (Add x y) = go x ++ go y
    go (Sub x y) = go x ++ go y
    go (Mul x y) = go x ++ go y

    go (ExprBool True) = []
    go (ExprBool False) = []

    go (Le x y) = go x ++ go y
    go (And x y) = go x ++ go y
    go (Or x y) = go x ++ go y
    go (Not x) = go x
    go (Equal x y) = go x ++ go y

    go (IsNull x) = go x

    go (App f args) = []

exprVars :: Expr a -> [Name]
exprVars = go
  where
    go :: Expr b -> [Name]
    go (Var n) = [n]
    go (Old _) = []

    go (Lit i) = []
    go (Add x y) = go x ++ go y
    go (Sub x y) = go x ++ go y
    go (Mul x y) = go x ++ go y

    go (ExprBool True) = []
    go (ExprBool False) = []

    go (Le x y) = go x ++ go y
    go (And x y) = go x ++ go y
    go (Or x y) = go x ++ go y
    go (Not x) = go x
    go (Equal x y) = go x ++ go y

    go (IsNull x) = go x

    go (App f args) = []

occursInEveryBranch :: Name -> Name -> [StructInv] -> Bool
occursInEveryBranch recName n0 = all go
  where
    go (_ :=> rhs) = occursIn recName n0 rhs

-- | Checks for occurrences outside of applications
occursIn :: Name -> Name -> [Expr a] -> Bool
occursIn recName = all . occursInExpr recName

occursInExpr :: Name -> Name -> Expr a -> Bool
occursInExpr recName n0 = go
  where
    go :: Expr b -> Bool
    go (Var n) = n == n0
    go (Old n) = False -- TODO: Is this correct?

    go (Lit i) = False
    go (Add x y) = go x || go y
    go (Sub x y) = go x || go y
    go (Mul x y) = go x || go y

    go (ExprBool True) = False
    go (ExprBool False) = False

    go (Le x y) = go x || go y
    go (And x y) = go x || go y
    go (Or x y) = go x || go y
    go (Not x) = go x
    go (Equal x y) = go x || go y

    go (IsNull x) = go x

    go (App f args)
      | f == recName = False
      | otherwise    = n0 `elem` args

recOccursIn :: Name -> Name -> [Expr a] -> Bool
recOccursIn recName = any . recOccursInExpr recName

-- | Check if the Name occurs in a recursive application
recOccursInExpr :: Name -> Name -> Expr a -> Bool
recOccursInExpr recName n0 = go
  where
    go :: Expr b -> Bool
    go (Var n) = False
    go (Old n) = False

    go (Lit i) = False
    go (Add x y) = go x || go y
    go (Sub x y) = go x || go y
    go (Mul x y) = go x || go y

    go (ExprBool True) = False
    go (ExprBool False) = False

    go (Le x y) = go x || go y
    go (And x y) = go x || go y
    go (Or x y) = go x || go y
    go (Not x) = go x
    go (Equal x y) = go x || go y

    go (IsNull x) = go x

    go (App f args)
      | f == recName = n0 `elem` args
      | otherwise    = False

