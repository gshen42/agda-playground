open import Data.Nat using (ℕ; _≟_)
open import Data.List using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Relation.Nullary using (yes; no)

open import CBCAST.VectorClock

module CBCAST.RawExecution (Message : Set) where

data Event : Set where
  send    : Message → VectorClock → Event
  receive : Event   → VectorClock → Event

vc : Event → VectorClock
vc (send    _ vc) = vc
vc (receive _ vc) = vc

_hb_ : Event → Event → Set
e₁ hb e₂ = vc e₁ ≤ vc e₂

record Process : Set where
  field
    procVc  : VectorClock
    sends   : List Event
    history : List Event

open Process

World : Set
World = ℕ → Process

update : World → ℕ → Process → World
update w n p n' with n ≟ n'
...                | (yes _) = p
...                | (no  _) = w n'

data _==>_ : World → World → Set where
  broadcast : ∀ (w : World) (sender : ℕ) (msg : Message)
            → let senderP  = w sender
                  senderVc = tick (procVc senderP) sender
              in
              w ==> (update w sender record { procVc  = senderVc
                                            ; sends   = send msg senderVc ∷ sends senderP
                                            ; history = send msg senderVc ∷ history senderP
                                            })

  deliver : ∀ (w : World) (sender receiver : ℕ) (e : Event)
          → let senderP    = w sender
                receiverP  = w receiver
                receiverVc = tick (combine (vc e) (procVc receiverP)) receiver
            in
            e ∈ sends senderP
          → w ==> (update w receiver record { procVc  = receiverVc
                                            ; sends   = sends receiverP
                                            ; history = receive e receiverVc ∷ history receiverP
                                            })

world₀ : World
world₀ = λ _ → record { procVc  = (λ _ → 0)
                      ; sends   = []
                      ; history = []
                      }

data _==>*_ : World → World → Set where
  lift : ∀ {w₁ w₂}
       → w₁ ==>  w₂
       → w₁ ==>* w₂

  refl : ∀ {w}
       → w ==>* w

  tran : ∀ {w₁ w₂ w₃}
       → w₁ ==>* w₂
       → w₂ ==>* w₃
       → w₁ ==>* w₃

Reachable : World → Set
Reachable w = world₀ ==>* w

postulate
  causal-delivery : ∀ {msg₁ msg₂ vc₁ vc₂ p₁ p₂ vc₁' vc₂' p}
                    → let e  = (send msg₁ vc₁)
                          e' = (send msg₂ vc₂)
                          deliverₚe  = (receive e  vc₁')
                          deliverₚe' = (receive e' vc₂')
                      in
                    ∀ {w} → Reachable w
                    → e  ∈ (history (w p₁))
                    → e' ∈ (history (w p₂))
                    → deliverₚe  ∈ (history (w p))
                    → deliverₚe' ∈ (history (w p))
                    → e hb e'
                    → deliverₚe hb deliverₚe'
