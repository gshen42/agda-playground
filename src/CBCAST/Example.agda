open import Data.String using (String)
open import Data.Product using (Σ; _,_; ∃; Σ-syntax; ∃-syntax)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; _≢_; sym)

import CBCAST.Event as Event
open Event String

module CBCAST.Example where

alice₁ : Event
alice₁ = send "I lost my wallet..." empty

alice₂ : Event
alice₂ = send "Found it!" alice₁

bob₁ : Event
bob₁ = receive alice₁ empty

bob₂ : Event
bob₂ = receive alice₂ bob₁

bob₃ : Event
bob₃ = send "Glad to hear it!" bob₂

carol₁ : Event
carol₁ = receive alice₁ empty

carol₂ : Event
carol₂ = receive bob₃ carol₁

carol₃ : Event
carol₃ = receive alice₁ carol₂

foo₁ : alice₁ hb alice₂
foo₁ = processOrder₁

foo₂ : alice₁ hb bob₁
foo₂ = sendBeforeReceive

foo₃ : bob₁ hb bob₂
foo₃ = processOrder₂

foo₄ : alice₂ hb bob₂
foo₄ = sendBeforeReceive

foo₅ : alice₁ hb bob₂
foo₅ = trans foo₁ foo₄

foo₆ : ¬ (bob₂ hb alice₁)
foo₆ = hb-asymmetric foo₅
