open import Data.Nat using (ℕ; _≟_)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

import CBCAST.Event as Event

module CBCAST.Execution (Msg : Set) where

open Event Msg

-- because `Event` contains a history of events happened before, we can also use it to model process
Process : Set
Process = Event

data _∈_ : Event → Process → Set where
  here   : ∀ {e}
         → e ∈ e

  there₁ : ∀ {e m}
         → e ∈ (send m e)

  there₂ : ∀ {e e'}
         → e ∈ (receive e' e)

World : Set
World = ℕ → Process

update : World → ℕ → Process → World
update w n p n' with n ≟ n'
...                | yes _ = p
...                | no  _ = w n

infix 4 _==>_

data _==>_ : World → World → Set where
  broadcast : ∀ m n w
            → w ==> (update w n (send m (w n)))

  deliver   : ∀ {m p} n n' w
            → (send m p) ∈ (w n')
            → w ==> (update w n (receive (send m p) (w n)))

infix 4 _==>*_

data _==>*_ : World → World → Set where
  lift : ∀ {w w'}
       → w ==>  w'
       → w ==>* w'

  refl : ∀ {w}
       → w ==>* w

  tran : ∀ {w w' w''}
       → w  ==>* w'
       → w' ==>* w''
       → w  ==>* w''

world₀ : World
world₀ _ = empty

reachable : World → Set
reachable w = world₀ ==>* w

causal-delivery : World → Set
causal-delivery w = ∀ n e₁ e₂ e₃ m
                  → (receive e₁ e₂) ∈ (w n)
                  → (send m e₃) hb e₁
                  → (send m e₃) ∈ (w n)
