module Main where

import Prelude

import Data.Array ((\\), intersect, partition, head, delete, null, find)
import Data.Foldable (any, foldMap)
import Data.Maybe (Maybe(..))

data Expr x = Atom x
              | Not (Expr x)
              | Or (Expr x) (Expr x)
              | And (Expr x) (Expr x)
              | Implies (Expr x) (Expr x)

derive instance eqExpr :: Eq x => Eq (Expr x)

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

data Sequent x = Sequent { left :: Array (Expr x), right :: Array (Expr x) }

-- An infix alias to construct Sequents 
proves :: forall x. Array (Expr x) -> Array (Expr x) -> Sequent x
proves left right = Sequent { left, right }

infix 4 proves as |-

data Rule = Id
            | WeakeningLeft
            | WeakeningRight
            | NotLeft
            | NotRight
            | AndLeft
            | AndRight
            | OrLeft
            | OrRight
            | ImpliesLeft
            | ImpliesRight

derive instance eqRule :: Eq Rule

data ProofStep x = ProofStep { rule :: Rule, before :: Sequent x }

-- An infix alias for ProofStep
step :: forall x. Rule -> Sequent x -> ProofStep x
step rule before = ProofStep { rule, before }

data Proof x = Linear { rule :: ProofStep x, next :: Maybe (Proof x) }
             | Branch { rule :: ProofStep x, first :: Maybe (Proof x), second :: Maybe (Proof x) }

linear :: forall x. ProofStep x -> Maybe (Proof x) -> Maybe (Proof x)
linear rule next = Just $ Linear { rule, next }

branch :: forall x. ProofStep x -> Maybe (Proof x) -> Maybe (Proof x) -> Maybe (Proof x)
branch rule first second = Just $ Branch { rule, first, second }

prove :: forall x. Eq x => Sequent x -> Maybe (Proof x)
prove sequent@(Sequent { left, right })
  -- The empty sequent
  | null left && null right = linear (step Id sequent) Nothing
  -- Weakening and identity
  | not $ null $ intersect left right =
      case head $ left \\ right, head $ right \\ left of
        Just x, _ -> let new = delete x left |- right in
                        linear (step WeakeningLeft sequent) (prove new)
        Nothing, Just y -> let new = left |- delete y right in
                              linear (step WeakeningRight sequent) (prove new)
        -- The two sides are equal and we are done
        Nothing, Nothing -> linear (step Id sequent) Nothing
  -- If we have negations on either side of the turnstile, strip the negations and move to the other side
  | any isNot left =
      let { yes, no } = partition isNot left in
      let new = no |- (right <> map removeNot yes) in
      linear (step NotLeft sequent) (prove new)
  | any isNot right =
      let { yes, no } = partition isNot right in
      let new = (left <> map removeNot yes) |- no in
      linear (step NotRight sequent) (prove new)
  -- Conjunctions on the left can be removed and replaced by a list of the subformulas
  | any isAnd left =
      let new = foldMap splitAnd left |- right in
      linear (step AndLeft sequent) (prove new)
  -- As can disjunctions on the right
  | any isOr right =
      let new = left |- foldMap splitOr right in
      linear (step OrRight sequent) (prove new)
  -- Move the hypotheses of any implications on the right to the left
  | any isImplies right =
      let { yes, no } = partition isImplies right in
      let new = (left <> map headImp yes) |- (no <> map tailImp yes) in
      linear (step ImpliesRight sequent) (prove new)
  -- Branching
  | otherwise =
      let leftOr = find isOr left
          rightAnd = find isAnd right
          leftImp = find isImplies left
      in
      case leftOr, rightAnd, leftImp of
        Just o@(Or fst snd), _, _ -> let cleanedLeft = delete o left in
                                       let first = (cleanedLeft <> [fst]) |- right in
                                       let second = (cleanedLeft <> [snd]) |- right in
                                       branch (step OrLeft sequent) (prove first) (prove second)
        Nothing, Just a@(And fst snd), _ -> let cleanedRight = delete a right in
                                              let first = left |- (cleanedRight <> [fst]) in
                                              let second = left |- (cleanedRight <> [snd]) in
                                              branch (step AndRight sequent) (prove first) (prove second)
        Nothing, Nothing, Just i@(Implies fst snd) -> let cleanedLeft = delete i left in
                                                      let first = cleanedLeft |- (right <> [fst]) in
                                                      let second = (cleanedLeft <> [snd]) |- right in
                                                      branch (step ImpliesLeft sequent) (prove first) (prove second)
        _, _, _ -> Nothing