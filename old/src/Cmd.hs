module Cmd
  where

import           Expr
import           Subst
import           Unify

data Cmd n
  = Assign (Name n) (Expr n Int)
  | IfThenElse (Expr n Bool) (Cmd n) (Cmd n)
  | While (Expr n Bool) (Cmd n)
  | Seq (Cmd n) (Cmd n)
  | Skip

