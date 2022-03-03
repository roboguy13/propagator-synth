module Parser.Suslik.ADT
  where

type Name = String

data SPredicate =
  SPredicate
  { predicateName :: Name
  , predicateArgs :: [VarDecl]
  , predicateBranches :: [PredicateBranch]
  }

data VarDecl =
  VarDecl
  { varDeclType :: SuslikType
  , varDeclVar  :: Name
  }

data SuslikType = IntType | SetType | LocType

data PredicateBranch =
  PredicateBranch
  { predicateBranchCond :: PureProp
  , predicateBranchBody :: SProp
  }

data SProp =
  SProp
  { propPure :: PureProp
  , propSep :: SepProp
  }

data PureProp
  = BoolLit Bool
  | And PureProp PureProp
  | Or  PureProp PureProp
  | Not PureProp
  | PropVar Name
  | Equal Expr Expr
  | Le Expr Expr

data SepProp =
  MkSepProp
  { sepPropClauses :: [SepPropClause]
  }

data SepPropClause
  = LocSize Expr Int
  | PointsTo Expr Expr
  | PredApply Name [Expr]

data Expr
  = Lit Int
  | ExprVar Name
  | Add Expr Expr
  | Sub Expr Expr
  | Mul Expr Expr
  | IfThenElse PureProp Expr Expr
  | SetLit [Expr]
  | SetUnion Expr Expr
  | SetEmpty
  | Apply Name [Expr]

