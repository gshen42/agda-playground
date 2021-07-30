{-# OPTIONS --allow-exec #-}
{-# OPTIONS --guardedness #-}

open import Agda.Builtin.Nat using (div-helper)
open import Data.Refinement using (Refinement; Refinement-syntax; _,_)
open import Data.Erased using (Erased; [_])
open import Data.Nat using (ℕ; zero; suc; _≤_; z≤n; s≤s; _+_)
open import Data.List using (List; []; _∷_; length)
open import Data.Empty using (⊥)
open import Data.Empty.Irrelevant using (⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; _≢_)
import SMT.Theories.Ints as Ints
open import SMT.Backend.Z3 Ints.reflectable

module RefinementType.Simple where

-- Converted from
-- http://ucsd-progsys.github.io/lh-workshop/02-refinements.html

-- A refinement type { x : A | P x } is written as [ x ∈ A ∣ P x ] in
-- Agda where A is the base type and P x is the (refinement)
-- predicate. Note that we mark refinement predicate as irrelevant
-- (using Erased record) to refrain from using them in computation,
-- this matches how predicate is used in Liquid Haskell.  Each { } in
-- the following code denotes a point to discharge proof obiligations
-- to an SMT solver.

-- refine a single term
_ : [ x ∈ ℕ ∣ x ≡ 2 ]
_ = 2 , [ {!!} ]

-- a single term can have multiple refinement types
_ : [ x ∈ ℕ ∣ x ≤ 10 ]
_ = 2 , [ {!!} ]

-- refine a computed term
_ : [ x ∈ ℕ ∣ x ≤ 10 ]
_ = (1 + 1) , [ {!!} ]

-- refinement as pre-condition
impossible : {A B : Set} → [ x ∈ A ∣ ⊥ ] → B
impossible ()

div : ℕ → [ n ∈ ℕ ∣ n ≢ 0 ] → ℕ
div x (zero , [ p ]) = ⊥-elim (p refl)
div x (suc y , _)    = div-helper 0 y x y

-- pre-condition checked at call-site
avg2 : ℕ → ℕ → ℕ
avg2 x y = div (x + y) (2 , [ {!!} ])

sum : List ℕ → ℕ
sum []       = 0
sum (x ∷ xs) = x + sum xs

-- rejected
avg : List ℕ → ℕ
avg xs = let total = sum xs
             n     = length xs
         in div total (n , [ {!!} ])

size : List ℕ → [ x ∈ ℕ ∣ 0 ≤ x ]
size []       = 1 , [ {!!} ]
size (x ∷ xs) = let (v , [ p ]) = size xs in (1 + v) , [ {!!} ]

-- accepted
avg′ : List ℕ → ℕ
avg′ xs = let total     = sum xs
              n , [ p ] = size xs
          in div total (n , [ {!!} ])
