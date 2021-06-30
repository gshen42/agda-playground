open import Data.Nat using (ℕ; _≟_)
open import Data.List using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Product using (_×_; _,_)
open import Relation.Nullary using (yes; no)

open import CBCAST.VectorClock
open import CBCAST.Protocol

module CBCAST.Execution (Message : Set) (protocol : Protocol) where

MessageMetadata  = Protocol.MessageMetadata  protocol
ProcessMetadata  = Protocol.ProcessMetadata  protocol
processMetadata₀ = Protocol.processMetadata₀ protocol
BroadcastHandler = Protocol.BroadcastHandler protocol
Deliverable      = Protocol.Deliverable      protocol
DeliverHandler   = Protocol.DeliverHandler   protocol

data Event : Set where
  send    : (Message × MessageMetadata) → VectorClock → Event
  receive : Event                       → VectorClock → Event

vc : Event → VectorClock
vc (send    _ vc) = vc
vc (receive _ vc) = vc

meta : Event → MessageMetadata
meta (send    (_ , m) _) = m
meta (receive e       _) = meta e

_hb_ : Event → Event → Set
e₁ hb e₂ = vc e₁ ≤ vc e₂

record Process : Set where
  field
    procVc   : VectorClock
    history  : List Event
    procMeta : ProcessMetadata

open Process

World : Set
World = ℕ → Process

update : World → ℕ → Process → World
update w n p n' with n ≟ n'
...                | (yes _) = p
...                | (no  _) = w n'

data _==>_ : World → World → Set where
  broadcast : ∀ (w : World) (sender : ℕ) (msg : Message) (msgMeta : MessageMetadata) (procMetaNew : ProcessMetadata)
            → let senderP   = w sender
                  senderVc  = tick (procVc senderP) sender
                  sendEvent = send (msg , msgMeta) senderVc
              in
              BroadcastHandler sender msgMeta (procMeta senderP) procMetaNew
            → w ==> (update w sender record { procVc   = senderVc
                                            ; history  = sendEvent ∷ history senderP
                                            ; procMeta = procMetaNew
                                            })

  deliver : ∀ (w : World) (sender receiver : ℕ) (msg : Message) (msgMeta : MessageMetadata) (senderVc : VectorClock) (procMetaNew : ProcessMetadata)
          → let senderP      = w sender
                receiverP    = w receiver
                receiverVc   = tick (combine senderVc (procVc receiverP)) receiver
                sendEvent    = send (msg , msgMeta) senderVc
                receiveEvent = receive sendEvent receiverVc
            in
            sendEvent ∈ history senderP
          → Deliverable receiver msgMeta (procMeta receiverP)
          → DeliverHandler receiver msgMeta (procMeta receiverP) procMetaNew
          → w ==> (update w receiver record { procVc  = receiverVc
                                            ; history = receiveEvent ∷ history receiverP
                                            ; procMeta = procMetaNew
                                            })

world₀ : World
world₀ = λ pid → record { procVc   = (λ _ → 0)
                        ; history  = []
                        ; procMeta = processMetadata₀ pid
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

causal-delivery : Set
causal-delivery = ∀ {msg₁ msg₂ vc₁ vc₂ p₁ p₂ vc₁' vc₂' p}
                  → let e  = (send msg₁ vc₁)
                        e' = (send msg₂ vc₂)
                        deliverₚe  = (receive e  vc₁')
                        deliverₚe' = (receive e' vc₂')
                    in
                  ∀ {w}
                  → Reachable w
                  → e  ∈ (history (w p₁))
                  → e' ∈ (history (w p₂))
                  → deliverₚe  ∈ (history (w p))
                  → deliverₚe' ∈ (history (w p))
                  → e hb e'
                  → deliverₚe hb deliverₚe'
