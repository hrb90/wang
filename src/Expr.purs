module Expr where

import Prelude

data Expr x = Atom x
              | Not (Expr x)
              | Or (Expr x) (Expr x)
              | And (Expr x) (Expr x)
              | Implies (Expr x) (Expr x)

derive instance eqExpr :: Eq x => Eq (Expr x)

type Proposition = Expr String

instance showExpr :: Show x => Show (Expr x) where
  show (Atom x) = show x
  show (Not x) = "¬(" <> show x <> ")"
  show (And x y) = "(" <> show x <> ") ∧ (" <> show y <> ")"
  show (Or x y) = "(" <> show x <> ") ∨ (" <> show y <> ")"
  show (Implies x y) = "(" <> show x <> ") ⊃ (" <> show y <> ")"

isNot :: forall x. Expr x -> Boolean
isNot (Not _) = true
isNot _ = false

isOr :: forall x. Expr x -> Boolean
isOr (Or _ _) = true
isOr _ = false

isAnd :: forall x. Expr x -> Boolean
isAnd (And _ _) = true
isAnd _ = false

isImplies :: forall x. Expr x -> Boolean
isImplies (Implies _ _) = true
isImplies _ = false

removeNot :: forall x. Expr x -> Expr x
removeNot (Not x) = x
removeNot y = y

splitAnd :: forall x. Expr x -> Array (Expr x)
splitAnd (And x y) = [x, y]
splitAnd z = [z]

splitOr :: forall x. Expr x -> Array (Expr x)
splitOr (Or x y) = [x, y]
splitOr z = [z]

headImp :: forall x. Expr x -> Expr x
headImp (Implies x _) = x
headImp y = y

tailImp :: forall x. Expr x -> Expr x
tailImp (Implies _ y) = y
tailImp z = z