{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}

module Suslik
  where

import           AST

import           Data.List
import           Data.Proxy
import           Data.Maybe

import           Data.Char

import qualified Data.Set as Set

nub' :: Ord a => [a] -> [a]
nub' = Set.toList . Set.fromList

newtype Suslik = MkSuslik String
  deriving (Semigroup, Monoid, Show)

unlines' = intercalate "\n"

mangle :: Name -> String
mangle (MkName n) = "_" <> n

orig :: Name -> String
orig (MkName n) = "orig_" <> n

setMangle :: Name -> String
setMangle (MkName n) = "set_" <> n

origSetMangle :: Name -> String
origSetMangle (MkName n) = "orig_set_" <> n

reprType :: SuslikType -> String
reprType BoolType = "int"
reprType IntType  = "int"
reprType LocType = "loc"

-- class Repr a where
--   reprType :: Proxy a -> Suslik

-- instance Repr IntType where
--   reprType Proxy = MkSuslik "int"

-- instance Repr ListType where
--   reprType Proxy = MkSuslik "set"

-- instance Repr BoolType where
--   reprType Proxy = MkSuslik "int"

-- | A simple syntactic check
selfIsNull :: Expr BoolType -> Bool
selfIsNull (And x y) = selfIsNull x || selfIsNull y
selfIsNull (IsNull Self) = True
selfIsNull _ = False

genStruct :: Struct -> Suslik
genStruct (MkStruct name params fields invs) =
  MkSuslik $ unlines'
    [ "predicate " <> mangle name <> "(" <> intercalate ", " ("loc x" : paramStrings ++ argStrings) <> ")"  --, " <> intercalate ", " (map (uncurry decl) fields) <> ") {"
    , "{"
    , unlines' $ map ("| " <>) $ genBranches hasRec name (map fst args) linked invs
    -- , "  true => " <> intercalate " && " (map genExpr invs) <> " ; [x," <> show (length fields) <> "] ** " <> genLinks linked <> ";"
    , "}"
    ]
  where
    linked = MkLinkedFields $ zipWith ((,) . fst) fields [0..]

    oldNames = concatMap (concatMap exprOldNames . implRhs) invs

    notRecIn n = not $ recOccursIn name n (concatMap implRhs invs)

    -- setArgStrings = map setMangle setArgs

    paramStrings = map (\(n, ty) -> reprType ty <> " " <> mangle n) params

    argStrings =
      if hasRec
        then map (("set " <>) . setMangle) (map fst args)
        else map (\(n, ty) -> reprType ty <> " " <> mangle n) args

    hasRec = any (isRec name) (concatMap implRhs invs)

    args =
      if True --any (isRec name) (concatMap implRhs invs)
        then
          nub' (
            -- oldNames
            --   ++
            filter (notRecIn . fst) fields
            )
        else []
    -- setArgs = map fst collecting
    -- setArgs = map ("s" <>) $ map show [1 .. length collecting]

setSingleton :: Expr a -> String
setSingleton e = "{" <> genExpr e <> "}"

setUnion :: String -> String -> String
setUnion x y = x <> " ++ " <> y

data Parens = NoParens | Parens

withParens :: Parens -> String -> String
withParens NoParens = id
withParens Parens = ("(" <>) . (<> ")")

genBranches :: Bool -> Name -> [Name] -> LinkedFields -> [StructInv] -> [String]
genBranches hasRec recName setArgs linked = map (genBranch hasRec recName setArgs linked)

genBranch :: Bool -> Name -> [Name] -> LinkedFields -> StructInv -> String
-- genBranch _ _      (_   :=> []) = ""
genBranch hasRec recName setArgs linked (lhs :=> rhs) =
  genExpr lhs <> " => { " <> intercalate " && " (filter (not . null) (setArgUpdates : filter (not . all isSpace) (map genExpr rhs)))
    <> " ; " <>
    (if selfIsNull lhs
      then "emp"
      else
        intercalate " ** "
          ("[x, " <> show (linkedCount linked) <> "]"
           : genLinks linked
           ++ genPredApplies setArgs (getPredApps rhs)
          ))
    <> " }"
  where
    setArgUpdates =
      if hasRec
        then intercalate " && " $ filter (not . null) $ filter (not . all isSpace) $ map go setArgs
        else []
      where
        setRhs setArg =
          if any (isRec recName) rhs
            then setUnion (setSingleton origSetArg) (origSetMangle setArg)
            else "{}"
            where
              origSetArg =
                if setArg `elem` concatMap exprOldNames rhs
                  then Old setArg
                  else Var setArg

        go setArg = setMangle setArg <> " =i " <> setRhs setArg


binOp :: Parens -> String -> (Parens -> a -> String) -> a -> a -> String
binOp p opName f x y = withParens p (f Parens x <> " " <> opName <> " " <> f Parens y)

genPredApplies :: [Name] -> [PredApply] -> [String]
genPredApplies setArgs = map go
  where
    go (MkPredApply f args) = mangle f <> "(" <> intercalate ", " (map mangle args ++ map origSetMangle setArgs) <> ")"

getPredApps :: [Expr BoolType] -> [PredApply]
getPredApps = mapMaybe $ \case
  Apply p -> Just p
  _ -> Nothing

genExpr :: Expr a -> String
genExpr = go NoParens
  where
    go :: Parens -> Expr b -> String
    go _ (Var n) = mangle n
    go _ (Old n) = orig n

    go _ (Lit i) = show i
    go p (Add x y) = binOp p "+" go x y
    go p (Sub x y) = binOp p "-" go x y
    go p (Mul x y) = binOp p "*" go x y

    go _ (ExprBool True) = "true"
    go _ (ExprBool False) = "false"

    go p (Le x y) = binOp p "<=" go x y
    go p (And x y) = binOp p "&&" go x y
    go p (Or x y) = binOp p "||" go x y
    go p (Not x) = withParens p ("not " <> go Parens x)
    go p (Equal x y) = binOp p "==" go x y

    go p (IsNull x) = withParens p (go Parens x <> " == null")

    go _ Self = "x"

    go _ (Apply {}) = "" -- This should only be generated elsewhere


-- genInv :: Expr BoolType -> String
-- genInv (ExprBool True) = "true"
-- genInv (ExprBool False) = "false"

-- genInv (Le x y) =

-- linkFields ::

newtype LinkedFields = MkLinkedFields { getLinkedFields :: [(Name, Int)] }

linkedCount :: LinkedFields -> Int
linkedCount = length . getLinkedFields

genLinks :: LinkedFields -> [String]
genLinks = map (uncurry go) . getLinkedFields
  where
    go n 0 = "x :-> " <> mangle n
    go n i = "(x+" <> show i <> ") :-> " <> mangle n

lookupFieldIx :: Name -> LinkedFields -> Int
lookupFieldIx x (MkLinkedFields xs) =
  case lookup x xs of
    Nothing -> error $ "lookupFieldIx: Cannot find " <> show x
    Just r -> r

decl :: Name -> SuslikType -> String
decl n ty = reprType ty <> " " <> mangle n

generate :: Suslik -> String
generate (MkSuslik s) = s

listExample :: Struct
listExample =
  MkStruct
  { structName = "list"
  , structParams = []
  , structFields = [("head", IntType), ("tail", LocType)]

  , structInvs = [ IsNull Self       :=> []

                 , Not (IsNull Self) :=> [ Var "head" .== Old "head"
                                         , App "list" ["tail"]
                                         ]
                 ]
  }

personExample :: Struct
personExample =
  MkStruct
  { structName = "person"
  , structParams = []
  , structFields = [("me", LocType), ("isMarried", IntType), ("spouse", LocType)]

  , structInvs = [ IsNull (Var "spouse") :=> [Var "isMarried" .== Lit 0]

                 , Not (IsNull (Var "spouse")) :=> [ Var "isMarried" .== Lit 1
                                                   , Not (Var "self" .== Var "me")
                                                   ]
                 ]
  }

list2Example :: Struct
list2Example =
  MkStruct
  { structName = "list2"
  , structParams = []
  , structFields = [("v", IntType), ("tail", IntType)]

  , structInvs = [ IsNull Self       :=> []

                 , Not (IsNull Self) :=> [ Var "v" .== (Lit 2 .* Old "v")
                                         , App "list2" ["tail"]
                                         ]
                 ]
  }

budgetExample :: Struct
budgetExample =
  MkStruct
  { structName = "budget"
  , structParams = []
  , structFields = [("w", IntType), ("d", IntType), ("nxt", LocType)]

  , structInvs = [ IsNull Self :=> []
                 , Not (IsNull Self) :=> [ Var "w" .== (Lit 7 .* Var "d")
                                         , App "budget" ["nxt"]
                                         ]
                 ]
  }

budgetColaExample :: Struct
budgetColaExample =
  MkStruct
  { structName = "budget2"
  , structParams = [("cola", IntType)]
  , structFields = [("w", IntType), ("d", IntType), ("nxt", LocType)]

  , structInvs = [ IsNull Self :=> []
                 , Not (IsNull Self) :=> [ Old "w" .== (Lit 7 .* Old "d")
                                         , Var "w" .== (Lit 7 .* Var "d")
                                         , Var "d" .== (Param "cola" .* Old "d")

                                         , App "budget2" ["nxt", "cola"]
                                         ]
                 ]
  }

-- predicate list2(loc x, set s)
-- {
-- | x == null       => { s =i {} ; emp }
-- | not (x == null) => { s =i {v1} ++ s1 && v == 2*v1 ; x :-> v ** (x+1) :-> rest ** list2(rest, s1) }
-- }

-- exampleList2 =
--   MkStruct
--   { structName = "list2"
--   , structFields = ["v", "tail"]
--   , structInvs = [ IsNull Self       :=> [ ]
--                  , Not (IsNull Self) :=> [ Var "v" `Equal` (Mul 2 (Old "v"))
--                                          , App "list2" ["tail"]
--                                          ]
--                  ]
--   }

