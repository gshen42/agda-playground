open import Data.Nat using (ℕ; zero; suc; _≤_; _<_)
open import Data.Fin using (Fin; zero; suc)
open import Data.Product using (Σ; _,_; proj₁; proj₂; Σ-syntax)

module RefinementType.Fin where

Finʳ : ℕ → Set
Finʳ n = Σ[ x ∈ ℕ ] x < n
