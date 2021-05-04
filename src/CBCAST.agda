open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.Product using (Σ; _,_; ∃; Σ-syntax; ∃-syntax)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

module CBCAST (A : Set) where

-- Instead of first define events then define processes as some collection of events,
-- we define process and event at the same time, in particular,
-- a process also represents the latest event just happened on it.
data Process : Set where
  empty   : Process

  send    : ∀ (msg : A)
          → Process
          → Process

  receive : ∀ (msg : A) (from : Process)
          → (∃[ p ] from ≡ send msg p)
          → Process
          → Process

data _happensBefore_ : Process → Process → Set where
  processOrder₁     : ∀ {p p' a}
                    → p ≡ send a p'
                    → p' happensBefore p

  processOrder₂     : ∀ {p p' p'' a p'a}
                    → p ≡ receive a p' p'a p''
                    → p'' happensBefore p

  sendBeforeReceive : ∀ {p p' p'' a p'a}
                    → p ≡ receive a p' p'a p''
                    → p' happensBefore p

  trans             : ∀ {p p' p''}
                    → p happensBefore p'
                    → p' happensBefore p''
                    → p happensBefore p''

nothing-happensBefore-empty : ∀ p → ¬ (p happensBefore empty)
nothing-happensBefore-empty _ (trans {_} {p'} _ q) = nothing-happensBefore-empty p' q
