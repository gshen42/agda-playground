open import Data.Refinement using (Refinement; Refinement-syntax; _,_; value; proof)
open import Data.Erased using (Erased; [_])
open import Data.Nat using (ℕ; zero; suc; _≤_; z≤n; s≤s; _<_; _+_)
open import Data.List using (List; []; _∷_; length)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

module RefinementType.DataTypes where

variable
  A : Set

-- typed holes examples
-- although I know these examples are contrived and only for demonstration purpose
-- it still feels wired to me to use length to verify listLength
listLength : (xs : List A) → [ v ∈ ℕ ∣ v ≡ length xs ]
listLength []       = {!!}
listLength (x ∷ xs) = (1 + {!!}) , {!!}

listLengthProof : (xs : List A) → value (listLength xs) ≡ (length xs)
listLengthProof []       = {!!}
listLengthProof (x ∷ xs) = {!!}

-- Non-empty list,
List⁺ : Set → Set
List⁺ a = [ x ∈ List a ∣ 0 < length x ]

head : List⁺ A → A
head ((x ∷ xs) , proof) = x -- quite suprising to me that Agda knows
                            -- that list can't be empty without calling
                            -- the smt solver

tail : List⁺ A → List A
tail ((x ∷ xs) , proof) = xs
