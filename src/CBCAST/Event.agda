open import Data.Nat using (ℕ; zero; suc; _+_; _<_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-refl; ≤-stepsˡ; ≤-stepsʳ; ≤-trans; <⇒≤; 1+n≰n)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_)

module CBCAST.Event (Msg : Set) where

data Event : Set where
  empty   : Event

  send    : Msg
          → Event -- previous local event
          → Event

  receive : Event -- sending event
          → Event -- previous local event
          → Event

data _hb_ : Event → Event → Set where
  processOrder₁     : ∀ {e a}
                    → e hb (send a e)

  processOrder₂     : ∀ {e e'}
                    → e hb (receive e' e)

  sendBeforeReceive : ∀ {e e'}
                    → e hb (receive e e')

  trans             : ∀ {e e' e''}
                    → e  hb e'
                    → e' hb e''
                    → e  hb e''

size : Event → ℕ
size empty          = zero
size (send _ e)     = suc (size e)
size (receive e e') = suc (size e + size e')

hb-monotonic : ∀ {e₁ e₂} → (e₁ hb e₂) → (size e₁ < size e₂)
hb-monotonic (processOrder₁)              = s≤s ≤-refl
hb-monotonic (processOrder₂ {_} {e'})     = s≤s (≤-stepsˡ (size e') ≤-refl)
hb-monotonic (sendBeforeReceive {_} {e'}) = s≤s (≤-stepsʳ (size e') ≤-refl)
hb-monotonic (trans e[hb]e' e'[hb]e'')    = ≤-trans (hb-monotonic e[hb]e') (<⇒≤ (hb-monotonic e'[hb]e''))

nothing-happensBefore-empty : ∀ {e} → ¬ (e hb empty)
nothing-happensBefore-empty (trans _ e'[hb]empty) with hb-monotonic e'[hb]empty
...                                                  | ()

-- `hb` is a strict partial order, so it's irreflexivie, antisymmetric, transitive (trivially by definition), and also asymmetric (implied by irreflexivity and transitivity)
hb-irreflexive : ∀ {e} → ¬ (e hb e)
hb-irreflexive e[hb]e with hb-monotonic e[hb]e
...                    | suc[n]≤n = 1+n≰n suc[n]≤n

hb-antisymmetric : ∀ {e₁ e₂} → (e₁ hb e₂) → (e₂ hb e₁) → e₁ ≡ e₂
hb-antisymmetric e₁[hb]e₂ e₂[hb]e₁ with ≤-trans (s≤s (hb-monotonic e₁[hb]e₂)) (hb-monotonic e₂[hb]e₁)
...                                   | e₁+2≤e₁ = ⊥-elim (1+n≰n (≤-trans (s≤s (≤-stepsˡ 1 ≤-refl)) e₁+2≤e₁))

hb-asymmetric : ∀ {e₁ e₂} → (e₁ hb e₂) → ¬ (e₂ hb e₁)
hb-asymmetric e₁[hb]e₂ e₂[hb]e₁ = hb-irreflexive (trans e₁[hb]e₂ e₂[hb]e₁)
