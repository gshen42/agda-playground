module ATP.SeqCalc where

open import ATP.Prop
open import ATP.Ctx

open import Data.Product using (∃; ∃-syntax; proj₁; proj₂; -,_) renaming (_,_ to infix 4 ⟨_,_⟩)
open import Reflection as Refl

infix  20 _⇒_^_
infixr 21 _+_

data Size : Set where
  zero : Size
  suc  : Size → Size
  _+_  : Size → Size → Size

private
  variable
    P       : Atom
    A B C D : Prop′
    Γ Δ     : Ctx
    m n     : Size

-- to facilitate termination checking, each sequent is indexed by the
-- size of the derivation
data _⇒_^_ : Ctx → Prop′ → Size → Set where
  idᵖ : Γ     ∋ ` P
      → Γ     ⇒ ` P   ^ zero
  -- this rule only allows atomic proposition to be concluded this
  -- matches well with the verificationist point of view the general
  -- version for all proposition is admissible (see "id" below)

  ∧R  : Γ     ⇒ A     ^ m
      → Γ     ⇒ B     ^ n
      → Γ     ⇒ A ∧ B ^ m + n

  ∧L₁ : Γ     ∋ A ∧ B
      → Γ , A ⇒ C     ^ m
      → Γ     ⇒ C     ^ suc m

  ∧L₂ : Γ     ∋ A ∧ B
      → Γ , B ⇒ C     ^ m
      → Γ     ⇒ C     ^ suc m

  ⊃R  : Γ , A ⇒ B     ^ m
      → Γ     ⇒ A ⊃ B ^ suc m

  ⊃L  : Γ     ∋ A ⊃ B
      → Γ     ⇒ A     ^ m
      → Γ , B ⇒ C     ^ n
      → Γ     ⇒ C     ^ m + n

  ∨R₁ : Γ     ⇒ A     ^ m
      → Γ     ⇒ A ∨ B ^ suc m

  ∨R₂ : Γ     ⇒ B     ^ m
      → Γ     ⇒ A ∨ B ^ suc m

  ∨L  : Γ     ∋ A ∨ B
      → Γ , A ⇒ C     ^ m
      → Γ , B ⇒ C     ^ n
      → Γ     ⇒ C     ^ m + n

  ⊤R  : Γ ⇒ ⊤         ^ zero

  ⊥L  : Γ ∋ ⊥
      → Γ ⇒ C         ^ zero

-- structural rules
struct : Γ ⊆ Δ
       → Γ ⇒ C ^ m
       → Δ ⇒ C ^ m
struct Γ⊆Δ (idᵖ a)    = idᵖ (Γ⊆Δ a)
struct Γ⊆Δ (∧R a b)   = ∧R (struct Γ⊆Δ a) (struct Γ⊆Δ b)
struct Γ⊆Δ (∧L₁ a b)  = ∧L₁ (Γ⊆Δ a) (struct (⊆-step Γ⊆Δ) b)
struct Γ⊆Δ (∧L₂ a b)  = ∧L₂ (Γ⊆Δ a) (struct (⊆-step Γ⊆Δ) b)
struct Γ⊆Δ (⊃R a)     = ⊃R (struct (⊆-step Γ⊆Δ) a)
struct Γ⊆Δ (⊃L a b c) = ⊃L (Γ⊆Δ a) (struct Γ⊆Δ b) (struct (⊆-step Γ⊆Δ) c)
struct Γ⊆Δ (∨R₁ a)    = ∨R₁ (struct Γ⊆Δ a)
struct Γ⊆Δ (∨R₂ a)    = ∨R₂ (struct Γ⊆Δ a)
struct Γ⊆Δ (∨L a b c) = ∨L (Γ⊆Δ a) (struct (⊆-step Γ⊆Δ) b) (struct (⊆-step Γ⊆Δ) c)
struct Γ⊆Δ ⊤R         = ⊤R
struct Γ⊆Δ (⊥L a)     = ⊥L (Γ⊆Δ a)

wk : Γ     ⇒ C ^ m
   → Γ , A ⇒ C ^ m
wk x = struct S x

wk′ : Γ , A     ⇒ C ^ m
    → Γ , B , A ⇒ C ^ m
wk′ x = struct (λ { Z → Z ; (S i) → S (S i) }) x

exch : Γ , A , B ⇒ C ^ m
     → Γ , B , A ⇒ C ^ m
exch x = struct ((λ { Z → S Z ; (S Z) → Z ; (S (S i)) → S (S i) })) x

id : Γ ∋ A
   → ∃[ q ] Γ ⇒ A ^ q
id {A = ` P}   x = -, idᵖ x
id {A = A ∧ B} x = -, ∧R (∧L₁ x (proj₂ (id Z))) (∧L₂ x (proj₂ (id Z)))
id {A = A ⊃ B} x = -, ⊃R (⊃L (S x) (proj₂ (id Z)) (proj₂ (id Z)))
id {A = A ∨ B} x = -, ∨L x (∨R₁ (proj₂ (id Z))) (∨R₂ (proj₂ (id Z)))
id {A = ⊤}     x = -, ⊤R
id {A = ⊥}     x = -, ⊥L x
-- this shows global completeness of the calculus
-- which means eliminations (left rules) are strong enough to
-- extract all the information introductions (right rule) put into

cut :        Γ ⇒ D     ^ m
    →        Γ , D ⇒ C ^ n
    → ∃[ q ] Γ     ⇒ C ^ q
-- idᵖ + arbitrary rule
cut (idᵖ a) b = -, struct (λ { Z → a ; (S i) → i }) b
-- arbitrary rule + idᵖ
cut a (idᵖ Z)     = -, a
cut a (idᵖ (S b)) = -, idᵖ b
-- right rule + arbitrary rule
cut (∧L₁ a b)  c = -, ∧L₁ a (proj₂ (cut b (wk′ c)))
cut (∧L₂ a b)  c = -, ∧L₂ a (proj₂ (cut b (wk′ c)))
cut (⊃L a b c) d = -, ⊃L a b (proj₂ (cut c (wk′ d)))
cut (∨L a b c) d = -, ∨L a (proj₂ (cut b (wk′ d))) (proj₂ (cut c (wk′ d)))
cut (⊥L a)     b = -, ⊥L a
-- arbitrary rule + left rule
cut a (∧R b c) = -, ∧R (proj₂ (cut a b)) (proj₂ (cut a c))
cut a (⊃R b)   = -, ⊃R (proj₂ (cut (wk a) (exch b)))
cut a (∨R₁ b)  = -, ∨R₁ (proj₂ (cut a b))
cut a (∨R₂ b)  = -, ∨R₂ (proj₂ (cut a b))
cut a ⊤R       = -, ⊤R
--right rule + left rule
-- the cut proposition is not used
cut o@(∧R a b) (∧L₁ (S c) d)  = -, ∧L₁ c (proj₂ (cut (wk o) (exch d)))
cut o@(⊃R a)   (∧L₁ (S c) d)  = -, ∧L₁ c (proj₂ (cut (wk o) (exch d)))
cut o@(∨R₁ a)  (∧L₁ (S c) d)  = -, ∧L₁ c (proj₂ (cut (wk o) (exch d)))
cut o@(∨R₂ a)  (∧L₁ (S c) d)  = -, ∧L₁ c (proj₂ (cut (wk o) (exch d)))
cut o@⊤R       (∧L₁ (S c) d)  = -, ∧L₁ c (proj₂ (cut (wk o) (exch d)))
cut o@(∧R a b) (∧L₂ (S c) d)  = -, ∧L₂ c (proj₂ (cut (wk o) (exch d)))
cut o@(⊃R a)   (∧L₂ (S c) d)  = -, ∧L₂ c (proj₂ (cut (wk o) (exch d)))
cut o@(∨R₁ a)  (∧L₂ (S c) d)  = -, ∧L₂ c (proj₂ (cut (wk o) (exch d)))
cut o@(∨R₂ a)  (∧L₂ (S c) d)  = -, ∧L₂ c (proj₂ (cut (wk o) (exch d)))
cut o@⊤R       (∧L₂ (S c) d)  = -, ∧L₂ c (proj₂ (cut (wk o) (exch d)))
cut o@(∧R a b) (⊃L (S c) d e) = -, ⊃L c (proj₂ (cut o d)) (proj₂ (cut (wk o) (exch e)))
cut o@(⊃R a)   (⊃L (S c) d e) = -, ⊃L c (proj₂ (cut o d)) (proj₂ (cut (wk o) (exch e)))
cut o@(∨R₁ a)  (⊃L (S c) d e) = -, ⊃L c (proj₂ (cut o d)) (proj₂ (cut (wk o) (exch e)))
cut o@(∨R₂ a)  (⊃L (S c) d e) = -, ⊃L c (proj₂ (cut o d)) (proj₂ (cut (wk o) (exch e)))
cut o@⊤R       (⊃L (S c) d e) = -, ⊃L c (proj₂ (cut o d)) (proj₂ (cut (wk o) (exch e)))
cut o@(∧R a b) (∨L (S c) d e) = -, ∨L c (proj₂ (cut (wk o) (exch d))) (proj₂ (cut (wk o) (exch e)))
cut o@(⊃R a)   (∨L (S c) d e) = -, ∨L c (proj₂ (cut (wk o) (exch d))) (proj₂ (cut (wk o) (exch e)))
cut o@(∨R₁ a)  (∨L (S c) d e) = -, ∨L c (proj₂ (cut (wk o) (exch d))) (proj₂ (cut (wk o) (exch e)))
cut o@(∨R₂ a)  (∨L (S c) d e) = -, ∨L c (proj₂ (cut (wk o) (exch d))) (proj₂ (cut (wk o) (exch e)))
cut o@⊤R       (∨L (S c) d e) = -, ∨L c (proj₂ (cut (wk o) (exch d))) (proj₂ (cut (wk o) (exch e)))
cut o@(∧R a b) (⊥L (S c))     = -, ⊥L c
cut o@(⊃R a)   (⊥L (S c))     = -, ⊥L c
cut o@(∨R₁ a)  (⊥L (S c))     = -, ⊥L c
cut o@(∨R₂ a)  (⊥L (S c))     = -, ⊥L c
cut o@⊤R       (⊥L (S c))     = -, ⊥L c
-- right rule + left rule
-- the cut proposition is used
cut o@(∧R a b) (∧L₁ Z d)   = -, proj₂ (cut a (proj₂ (cut (wk o) (exch d))))
cut o@(∧R a b) (∧L₂ Z d)   = -, proj₂ (cut b (proj₂ (cut (wk o) (exch d))))
cut o@(⊃R a)   (⊃L Z d e)  = -, proj₂ (cut (proj₂ (cut (proj₂ (cut o d)) a)) (proj₂ (cut (wk o) (exch e))))
cut o@(∨R₁ a)  (∨L Z d e)  = -, proj₂ (cut a (proj₂ (cut (∨R₁ (wk a)) (exch d))))
cut o@(∨R₂ a)  (∨L Z d e)  = -, proj₂ (cut a (proj₂ (cut (∨R₂ (wk a)) (exch e))))

-- examples
ex₀ : ∃[ q ] · ⇒ A ⊃ B ⊃ A ∧ B ^ q
ex₀ = -, ⊃R (⊃R (∧R (proj₂ (id (S Z)))
                    (proj₂ (id Z))))

ex₁ : ∃[ q ] · ⇒ (A ⊃ B ∧ C) ⊃ ((A ⊃ B) ∧ (A ⊃ C)) ^ q
ex₁ = -, ⊃R (∧R (⊃R (⊃L (S Z) (proj₂ (id Z)) (∧L₁ Z (proj₂ (id Z)))))
                (⊃R (⊃L (S Z) (proj₂ (id Z)) (∧L₂ Z (proj₂ (id Z))))))

ex₂ : ∃[ q ] · ⇒ A ⊃ A ^ q
ex₂ = -, ⊃R (proj₂ (id Z))
-- unlike natural deduction, there couldn't be any other proof of A ⊃ A
