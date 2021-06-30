open import Data.Nat as ℕ using (ℕ)
open import Data.List using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.Product using (_×_; _,_)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; _≢_)

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
e₁ hb e₂ = vc e₁ < vc e₂

record Process : Set where
  field
    procVc   : VectorClock
    history  : List Event
    procMeta : ProcessMetadata

open Process

World : Set
World = ℕ → Process

update : World → ℕ → Process → World
update w n p n' with n ℕ.≟ n'
...                | yes _   = p
...                | no  _   = w n'

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
                receiverVc   = tick (combine (procVc receiverP) senderVc) receiver
                sendEvent    = send (msg , msgMeta) senderVc
                receiveEvent = receive sendEvent receiverVc
            in
            sender ≢ receiver
          → sendEvent ∈ history senderP
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

causal-delivery[_] : World → Set
causal-delivery[ w ] = ∀ {p e₁ e₂ vc₁ vc₂}
                     → let deliverₚe₁ = receive e₁ vc₁
                           deliverₚe₂ = receive e₂ vc₂
                       in
                       deliverₚe₁ ∈ history (w p)
                     → deliverₚe₂ ∈ history (w p)
                     → e₁ hb e₂
                     → deliverₚe₁ hb deliverₚe₂

history≤procVc[_] : World → Set
history≤procVc[ w ] = ∀ {p e} → e ∈ history (w p) → vc e ≤ procVc (w p)

history≤procVc : ∀ {w} → Reachable w → history≤procVc[ w ]
history≤procVc x {p} = history≤procVc-inductive* x (history≤procVc₀ {p})
  where
  history≤procVc₀ : history≤procVc[ world₀ ]
  history≤procVc₀ ()

  history≤procVc-inductive : ∀ {w w′} → w ==> w′ → history≤procVc[ w ] → history≤procVc[ w′ ]
  history≤procVc-inductive (broadcast _ sender _ _ _ _)           h {p} x           with sender ℕ.≟ p
  history≤procVc-inductive (broadcast _ sender _ _ _ _)           h {p} (here refl)    | yes _          = ≤-refl
  history≤procVc-inductive (broadcast _ sender _ _ _ _)           h {p} (there x)      | yes _          = ≤-trans (h x) (<⇒≤ (vc<tick[vc] {p = sender}))
  history≤procVc-inductive (broadcast _ sender _ _ _ _)           h {p} x              | no  _          = h x
  history≤procVc-inductive (deliver _ _ receiver _ _ _ _ _ _ _ _) h {p} x           with receiver ℕ.≟ p
  history≤procVc-inductive (deliver _ _ receiver _ _ _ _ _ _ _ _) h {p} (here refl)    | yes _          = ≤-refl
  history≤procVc-inductive (deliver _ _ receiver _ _ _ _ _ _ _ _) h {p} (there x)      | yes _          = ≤-trans (h x) (<⇒≤ (<-trans vc<combine[vc,vc′] (vc<tick[vc] {p = receiver})))
  history≤procVc-inductive (deliver _ _ receiver _ _ _ _ _ _ _ _) h {p} x              | no  _          = h x

  history≤procVc-inductive* : ∀ {w w′} → w ==>* w′ → history≤procVc[ w ] → history≤procVc[ w′ ]
  history≤procVc-inductive* (lift x)   h = history≤procVc-inductive x h
  history≤procVc-inductive* refl       h = h
  history≤procVc-inductive* (tran x y) h = history≤procVc-inductive* y (history≤procVc-inductive* x h)
