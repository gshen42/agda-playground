open import Data.Nat as ℕ using (ℕ; zero; suc; _+_; _≟_; _⊔_)
open import Data.Product using (_×_)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_)

module CBCAST.VectorClock where

VectorClock : Set
VectorClock = ℕ → ℕ

infix 10 _[_]
_[_] : VectorClock → ℕ → ℕ
vc [ k ] = vc k

_≤_ : VectorClock → VectorClock → Set
vc₁ ≤ vc₂ = ∀ k → vc₁ [ k ] ℕ.≤ vc₂ [ k ]

_<_ : VectorClock → VectorClock → Set
vc₁ < vc₂ = vc₁ ≤ vc₂
          × vc₁ ≢ vc₂

tick : VectorClock → ℕ → VectorClock
tick vc n n' with n ≟ n'
...             | (yes _) = vc n' + 1
...             | (no  _) = vc n'

combine : VectorClock → VectorClock → VectorClock
combine vc₁ vc₂ n = (vc₁ n) ⊔ (vc₂ n)

postulate
  ≤-refl : ∀ {vc} → vc ≤ vc

  ≤-trans : ∀ {vc₁ vc₂ vc₃} → vc₁ ≤ vc₂ → vc₂ ≤ vc₃ → vc₁ ≤ vc₃

  <⇒≤ : ∀ {vc₁ vc₂} → vc₁ < vc₂ → vc₁ ≤ vc₂

  <-trans : ∀ {vc₁ vc₂ vc₃} → vc₁ < vc₂ → vc₂ < vc₃ → vc₁ < vc₃

  <-transˡ : ∀ {vc₁ vc₂ vc₃} → vc₁ ≤ vc₂ → vc₂ < vc₃ → vc₁ < vc₃

  vc<tick[vc] : ∀ {vc p} → vc < tick vc p

  vc<combine[vc,vc′] : ∀ {vc vc′} → vc < combine vc vc′
