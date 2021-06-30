open import Data.Nat as ℕ using (ℕ; _+_; _≤_; _≟_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (Any; here; there) -- _∈_ is defined in terms of Any, why the above module doesn't import this module transitively?
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; _≢_)

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

open import CBCAST.Execution Message cbcast as Execution
open Process

lemma₁ : ∀ {w p e e′ vc}
       → Reachable w
       → receive e vc ∈ history (w p)
       → e′ hb e
       → ¬ Execution.Deliverable p (meta e′) (procMeta (w p))

causal-delivery : ∀ {w} → Reachable w → causal-delivery[ w ]
causal-delivery rw {p} = causal-delivery-inductive* refl rw (causal-delivery₀ {p})
  where
  causal-delivery₀ : causal-delivery[ world₀ ]
  causal-delivery₀ ()

  causal-delivery-inductive : ∀ {w w′} → Reachable w → w ==> w′ → causal-delivery[ w ] → causal-delivery[ w′ ]
  causal-delivery-inductive _  (broadcast _ sender _ _ _ _)           h {p}      x           y           z with sender ≟ p
  causal-delivery-inductive _  (broadcast _ sender _ _ _ _)           h {p}      (there x)   (there y)   z    | yes _              = h x y z
  causal-delivery-inductive _  (broadcast _ sender _ _ _ _)           h {p}      x           y           z    | no  _              = h x y z
  causal-delivery-inductive _  (deliver _ _ receiver _ _ _ _ _ _ _ _) h {p}      x           y           z       with receiver ≟ p
  causal-delivery-inductive _  (deliver _ _ receiver _ _ _ _ _ _ _ _) h {p}      (here refl) (here refl) (_ , z)    | yes _        = ⊥-elim (z refl)
  causal-delivery-inductive rw (deliver _ _ receiver _ _ _ _ _ _ d _) h {p} {e₁} (here refl) (there y)   z          | yes _        = ⊥-elim (lemma₁ {e′ = e₁} rw y z d)
  causal-delivery-inductive rw (deliver _ _ receiver _ _ _ _ _ _ _ _) h {p}      (there x)   (here refl) z          | yes _        = <-transˡ (history≤procVc rw x) (<-trans vc<combine[vc,vc′] (vc<tick[vc] {p = receiver}))
  causal-delivery-inductive _  (deliver _ _ receiver _ _ _ _ _ _ _ _) h {p}      (there x)   (there y)   z          | yes _        = h x y z
  causal-delivery-inductive _  (deliver _ _ receiver _ _ _ _ _ _ _ _) h {p}      x           y           z          | no  _        = h x y z

  causal-delivery-inductive* : ∀ {w w′} → Reachable w → w ==>* w′ → causal-delivery[ w ] → causal-delivery[ w′ ]
  causal-delivery-inductive* rw (lift x)   h = causal-delivery-inductive rw x h
  causal-delivery-inductive* rw refl       h = h
  causal-delivery-inductive* rw (tran x y) h = causal-delivery-inductive* (tran rw x) y (causal-delivery-inductive* rw x h)
