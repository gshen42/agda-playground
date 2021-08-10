module RefinementType.Refinement where

-- A refinement type { x : A | P x } is written as [ x ∈ A ∣ P x ] in
-- Agda where A is the base type and P x is the (refinement)
-- predicate. Note that we mark refinement predicate as irrelevant
-- to refrain from using them in computation, this matches how
-- predicate is used in Liquid Haskell.

record Refinement (B : Set) (P : B → Set) : Set where
  constructor _,_
  field value  : B
        .proof : P value

syntax Refinement A (λ x → P) = [ x ∈ A ∣ P ]
