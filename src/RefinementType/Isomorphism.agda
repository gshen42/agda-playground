open import Data.Product using (_×_; _,_)
open import Function using (_∘′_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

module RefinementType.Isomorphism where

-- function type takes two arguments by currying
Fun₂ : Set → Set → Set → Set
Fun₂ A B C = A → B → C

-- function type takes two arguments by product
Fun₂′ : Set → Set → Set → Set
Fun₂′ A B C = A × B → C

to : ∀ {A B C : Set} → Fun₂ A B C → Fun₂′ A B C
to f₁ (a , b) = f₁ a b

from : ∀ {A B C : Set} → Fun₂′ A B C → Fun₂ A B C
from f₂ a b = f₂ (a , b)

postulate
  -- non dependently typed version of functional extensionality (therefore a prime)
  fun-ext′ : ∀ {A : Set} {B : Set} {f g : A → B}
          → (∀ (x : A) → f x ≡ g x)
          → f ≡ g

from∘to : ∀ {A B C : Set} {f : Fun₂ A B C} → from (to f) ≡ f
from∘to = fun-ext′ λ a → fun-ext′ λ b → refl

to∘from : ∀ {A B C : Set} {f : Fun₂′ A B C} → to (from f) ≡ f
to∘from = fun-ext′ λ (a , b) → refl
