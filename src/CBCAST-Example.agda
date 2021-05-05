open import Data.String using (String)
open import Data.Product using (Σ; _,_; ∃; Σ-syntax; ∃-syntax)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; _≢_; sym)

import CBCAST
open CBCAST String

module CBCAST-Example where

alice₁ : Process
alice₁ = send "I lost my wallet..." empty

alice₂ : Process
alice₂ = send "Found it!" alice₁

bob₁ : Process
bob₁ = receive "I lost my wallet..." alice₁ p empty
  where
    p = empty , refl

bob₂ : Process
bob₂ = receive "Found it!" alice₂ p bob₁
  where
    p = alice₁ , refl

bob₃ : Process
bob₃ = send "Glad to hear it!" bob₂

carol₁ : Process
carol₁ = receive "I lost my wallet..." alice₁ p empty
  where
    p = empty , refl

carol₂ : Process
carol₂ = receive "Glad to hear it!" bob₃ p carol₁
  where
    p = bob₂ , refl

carol₃ : Process
carol₃ = receive "I lost my wallet..." alice₁ p carol₂
  where
    p = empty , refl

foo₁ : alice₁ happensBefore alice₂
foo₁ = processOrder₁ refl

foo₂ : alice₁ happensBefore bob₁
foo₂ = sendBeforeReceive refl

foo₃ : bob₁ happensBefore bob₂
foo₃ = processOrder₂ refl

foo₄ : alice₂ happensBefore bob₂
foo₄ = sendBeforeReceive refl

foo₅ : alice₁ happensBefore bob₂
foo₅ = trans foo₁ foo₄

foo₆ : ¬ (bob₂ happensBefore alice₁)
foo₆ = hb-asymmetric foo₅
