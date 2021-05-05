open import Data.Nat using (ℕ; zero; suc; _+_; _<_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-refl; ≤-stepsˡ; ≤-stepsʳ; ≤-trans; <⇒≤; 1+n≰n)
open import Data.Product using (Σ; _,_; ∃; Σ-syntax; ∃-syntax)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

module CBCAST (A : Set) where

data Event : Set where
  empty   : Event

  send    : ∀ (msg : A)
          → Event
          → Event

  receive : ∀ (msg : A) (from : Event)
          → (∃[ e ] from ≡ send msg e)
          → Event
          → Event

data _happensBefore_ : Event → Event → Set where
  processOrder₁     : ∀ {e e' a}
                    → e ≡ send a e'
                    → e' happensBefore e

  processOrder₂     : ∀ {e e' e'' a e''a}
                    → e ≡ receive a e'' e''a e'
                    → e' happensBefore e

  sendBeforeReceive : ∀ {e e' e'' a e''a}
                    → e ≡ receive a e'' e''a e'
                    → e'' happensBefore e

  trans             : ∀ {e e' e''}
                    → e happensBefore e'
                    → e' happensBefore e''
                    → e happensBefore e''

size : Event → ℕ
size empty              = zero
size (send  _ e)        = suc (size e)
size (receive _ e' _ e) = suc (size e' + size e)

hb-monotonic : ∀ {e₁ e₂} → e₁ happensBefore e₂ → size e₁ < size e₂
hb-monotonic (processOrder₁ refl)               = s≤s ≤-refl
hb-monotonic (processOrder₂ {e'' = e''} refl)   = s≤s (≤-stepsˡ (size e'') ≤-refl)
hb-monotonic (sendBeforeReceive {e' = e'} refl) = s≤s (≤-stepsʳ (size e') ≤-refl)
hb-monotonic (trans e[hb]e' e'[hb]e'')          = ≤-trans (hb-monotonic e[hb]e') (<⇒≤ (hb-monotonic e'[hb]e''))

nothing-happensBefore-empty : ∀ {e} → ¬ (e happensBefore empty)
nothing-happensBefore-empty (trans _ e'[hb]empty) with hb-monotonic e'[hb]empty
...                                                  | ()

-- `happensBefore` is a strict partial order, so it's irreflexivie, antisymmetric, transitive (trivially by definition), and also asymmetric (implied by irreflexivity and transitivity)
hb-irreflexive : ∀ {e} → ¬ (e happensBefore e)
hb-irreflexive e[hb]e with hb-monotonic e[hb]e
...                    | suc[n]≤n = 1+n≰n suc[n]≤n

hb-antisymmetric : ∀ {e₁ e₂} → (e₁ happensBefore e₂) → (e₂ happensBefore e₁) → e₁ ≡ e₂
hb-antisymmetric e₁[hb]e₂ e₂[hb]e₁ with ≤-trans (s≤s (hb-monotonic e₁[hb]e₂)) (hb-monotonic e₂[hb]e₁)
...                                   | e₁+2≤e₁ = ⊥-elim (1+n≰n (≤-trans (s≤s (≤-stepsˡ 1 ≤-refl)) e₁+2≤e₁))

hb-asymmetric : ∀ {e₁ e₂} → (e₁ happensBefore e₂) → ¬ (e₂ happensBefore e₁)
hb-asymmetric e₁[hb]e₂ e₂[hb]e₁ = hb-irreflexive (trans e₁[hb]e₂ e₂[hb]e₁)
