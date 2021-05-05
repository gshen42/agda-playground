open import Data.Nat using (ℕ; zero; suc; _+_; _<_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-refl; ≤-stepsˡ; ≤-stepsʳ; ≤-trans; <⇒≤; 1+n≰n)
open import Data.Product using (Σ; _,_; ∃; Σ-syntax; ∃-syntax)
open import Data.Empty using (⊥; ⊥-elim)
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

  processOrder₂     : ∀ {p p' p'' a p''a}
                    → p ≡ receive a p'' p''a p'
                    → p' happensBefore p

  sendBeforeReceive : ∀ {p p' p'' a p''a}
                    → p ≡ receive a p'' p''a p'
                    → p'' happensBefore p

  trans             : ∀ {p p' p''}
                    → p happensBefore p'
                    → p' happensBefore p''
                    → p happensBefore p''

size : Process → ℕ
size empty              = zero
size (send  _ p)        = suc (size p)
size (receive _ p' _ p) = suc (size p' + size p)

hb-monotonic : ∀ {p₁ p₂} → p₁ happensBefore p₂ → size p₁ < size p₂
hb-monotonic (processOrder₁ refl)               = s≤s ≤-refl
hb-monotonic (processOrder₂ {p'' = p''} refl)   = s≤s (≤-stepsˡ (size p'') ≤-refl)
hb-monotonic (sendBeforeReceive {p' = p'} refl) = s≤s (≤-stepsʳ (size p') ≤-refl)
hb-monotonic (trans p[hb]p' p'[hb]p'')          = ≤-trans (hb-monotonic p[hb]p') (<⇒≤ (hb-monotonic p'[hb]p''))

nothing-happensBefore-empty : ∀ {p} → ¬ (p happensBefore empty)
nothing-happensBefore-empty (trans _ p'[hb]empty) with hb-monotonic p'[hb]empty
...                                                  | ()

-- `happensBefore` is a strict partial order, so it's irreflexivie, antisymmetric, transitive (trivially by definition), and also asymmetric (implied by irreflexivity and transitivity)
hb-irreflexive : ∀ {p} → ¬ (p happensBefore p)
hb-irreflexive p[hb]p with hb-monotonic p[hb]p
...                    | suc[n]≤n = 1+n≰n suc[n]≤n

hb-antisymmetric : ∀ {p₁ p₂} → (p₁ happensBefore p₂) → (p₂ happensBefore p₁) → p₁ ≡ p₂
hb-antisymmetric p₁[hb]p₂ p₂[hb]p₁ with ≤-trans (s≤s (hb-monotonic p₁[hb]p₂)) (hb-monotonic p₂[hb]p₁)
...                                   | p₁+2≤p₁ = ⊥-elim (1+n≰n (≤-trans (s≤s (≤-stepsˡ 1 ≤-refl)) p₁+2≤p₁))

hb-asymmetric : ∀ {p₁ p₂} → (p₁ happensBefore p₂) → ¬ (p₂ happensBefore p₁)
hb-asymmetric p₁[hb]p₂ p₂[hb]p₁ = hb-irreflexive (trans p₁[hb]p₂ p₂[hb]p₁)
