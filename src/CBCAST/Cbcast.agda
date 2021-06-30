open import Data.Nat using (ℕ; _+_; _≤_)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_)

open import CBCAST.Protocol
open import CBCAST.VectorClock hiding (_≤_)

module CBCAST.Cbcast where

open Protocol -- open Protocol record namespace

cbcast : Protocol
MessageMetadata  cbcast                                       = VectorClock × ℕ
ProcessMetadata  cbcast                                       = VectorClock
processMetadata₀ cbcast pid                                   = λ _ → 0
BroadcastHandler cbcast pid (msgVc , sender) procVc procVcNew = msgVc ≡ tick procVc pid × procVcNew ≡ tick procVc pid
Deliverable      cbcast pid (msgVc , sender) procVc           = ∀ (k : ℕ) → (k ≡ sender → msgVc [ k ] ≡ procVc [ k ] + 1) × (k ≢ sender → msgVc [ k ] ≤ procVc [ k ])
DeliverHandler   cbcast pid (msgVc , sender) procVc procVcNew = procVcNew ≡ combine msgVc procVc
