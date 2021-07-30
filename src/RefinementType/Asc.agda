open import Data.Nat as ℕ using (ℕ; zero; suc)
open import Data.Refinement using (Refinement; _,_; Refinement-syntax)
open import Data.Erased using ([_])

module RefinementType.Asc where

record Ord (A : Set) : Set₁ where
  field
    _<_ : A → A → Set
open Ord {{...}}

instance
  Ord[ℕ] : Ord ℕ
  Ord[ℕ] = record { _<_ = ℕ._<_ }

  lift : {A : Set} → {R : A → Set} → {{Ord A}} → Ord [ x ∈ A ∣ R x ]
  lift {{record { _<_ = _<_ }}} = record { _<_ = λ (x , _) (y , _) → x < y }

infixr 5 _∷_

data Asc (A : Set) {{Ord[A] : Ord A}} : Set where
  []  : Asc A
  _∷_ : (h : A) → Asc [ x ∈ A ∣ h < x ] → Asc A

_ : [ x ∈ ℕ ∣ x < 0 ]
_ = 1 , {!!}

ex1 : Asc ℕ
ex1 = []

ex2 : Asc ℕ
ex2 = 2 ∷ []

ex3 : Asc ℕ
ex3 = 1 ∷ {!!}

ex4 : Asc ℕ
ex4 = 3 ∷ (2 , {!!}) ∷ []
