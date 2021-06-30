open import Data.Nat as ℕ using (ℕ; _+_; _≤_; _≟_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (Any; here; there) -- _∈_ is defined in terms of Any, why the above module doesn't import this module transitively?
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_)

open import CBCAST.Protocol
open import CBCAST.VectorClock

module CBCAST.Cbcast where

open Protocol -- open Protocol record namespace

cbcast : Protocol
MessageMetadata  cbcast                                       = VectorClock × ℕ
ProcessMetadata  cbcast                                       = VectorClock
processMetadata₀ cbcast pid                                   = λ _ → 0
BroadcastHandler cbcast pid (msgVc , sender) procVc procVcNew = msgVc ≡ tick procVc pid × procVcNew ≡ tick procVc pid
Deliverable      cbcast pid (msgVc , sender) procVc           = ∀ (k : ℕ) → (k ≡ sender → msgVc [ k ] ≡ procVc [ k ] + 1) × (k ≢ sender → msgVc [ k ] ℕ.≤ procVc [ k ])
DeliverHandler   cbcast pid (msgVc , sender) procVc procVcNew = procVcNew ≡ combine msgVc procVc

postulate
  Message : Set

open import CBCAST.Execution Message cbcast
open Process

cbcast-causal-delivery : ∀ {w} → Reachable w → causal-delivery w
cbcast-causal-delivery reachable[w]
                       receive[e₁]∈w[p]
                       receive[e₂]∈w[p]
                       e₁[hb]e₂
                       = {!!}
