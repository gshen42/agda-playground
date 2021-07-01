open import Data.Nat as ℕ using (ℕ; _+_; _≟_)
import Data.Nat.Properties as ℕₚ
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

metaVc : Event → VectorClock
metaVc e = proj₁ (meta e)

hb⇒metaVc : ∀ {w p₁ p₂ e₁ e₂}
          → Reachable w
          → e₁ ∈ history (w p₁)
          → e₂ ∈ history (w p₂)
          → e₁ hb e₂
          → metaVc e₁ ≤ metaVc e₂

history≤procMeta[_] : World → Set
history≤procMeta[ w ] = ∀ {p e}
                      → e ∈ history (w p)
                      → metaVc e ≤ procMeta (w p)

-- this proof is very similar to 'history≤procVc' in 'Execution.agda'
history≤procMeta : ∀ {w} → Reachable w → history≤procMeta[ w ]
history≤procMeta x {p} = history≤procMeta-inductive* x (history≤procMeta₀ {p})
  where
  history≤procMeta₀ : history≤procMeta[ world₀ ]
  history≤procMeta₀ ()

  history≤procMeta-inductive : ∀ {w w′} → w ==> w′ → history≤procMeta[ w ] → history≤procMeta[ w′ ]
  history≤procMeta-inductive (broadcast _ sender _ _ _ (refl , refl))           h {p} x           with sender ≟ p
  history≤procMeta-inductive (broadcast _ sender _ _ _ (refl , refl))           h {p} (here refl)    | yes _      = ≤-refl
  history≤procMeta-inductive (broadcast _ sender _ _ _ (refl , refl))           h {p} (there x)      | yes _      = ≤-trans (h x) (<⇒≤ (vc<tick[vc] {p = sender}))
  history≤procMeta-inductive (broadcast _ sender _ _ _ (refl , refl))           h {p} x              | no  _      = h x
  history≤procMeta-inductive (deliver _ _ receiver _ _ _ _ _ _ _ refl)          h {p} x           with receiver ≟ p
  history≤procMeta-inductive (deliver _ _ receiver _ _ _ _ _ _ _ refl)          h {p} (here refl)    | yes _      = <⇒≤ vc<combine[vc,vc′]
  history≤procMeta-inductive (deliver _ _ receiver _ _ _ _ _ _ _ refl)          h {p} (there x)      | yes _      = ≤-trans (h x) (<⇒≤ vc<combine[vc′,vc])
  history≤procMeta-inductive (deliver _ _ receiver _ _ _ _ _ _ _ refl)          h {p} x              | no  _      = h x

  history≤procMeta-inductive* : ∀ {w w′} → w ==>* w′ → history≤procMeta[ w ] → history≤procMeta[ w′ ]
  history≤procMeta-inductive* (lift x)   h = history≤procMeta-inductive x h
  history≤procMeta-inductive* refl       h = h
  history≤procMeta-inductive* (tran x y) h = history≤procMeta-inductive* y (history≤procMeta-inductive* x h)


no-delivery : ∀ {w p p′ e e′ vc}
            → Reachable w
            → receive e vc ∈ history (w p)
            → e′ ∈ history (w p′)
            → e′ hb e
            → ¬ Execution.Deliverable p (meta e′) (procMeta (w p))
no-delivery {e′ = e′} rw a b c d = let (p₂ , ∃p₂)                        = receive-wellformed rw a
                                       metaVc[e′]≤metaVc[e]              = hb⇒metaVc {p₂ = p₂} rw b ∃p₂ c
                                       metaVc[e]≤procMeta[w[p]]          = history≤procMeta rw a
                                       metaVc[e′]≤procMeta[w[p]]         = ≤-trans metaVc[e′]≤metaVc[e] metaVc[e]≤procMeta[w[p]]
                                       k                                 = proj₂ (meta e′)
                                       metaVc[e′][k]≡procMeta[w[p]][k]+1 = proj₁ (d k) refl
                                       metaVc[e′][k]≤procMeta[w[p]][k]   = metaVc[e′]≤procMeta[w[p]] k
                                   in foo metaVc[e′][k]≡procMeta[w[p]][k]+1 metaVc[e′][k]≤procMeta[w[p]][k]
  where
  foo : ∀ {x y} → x ≡ y + 1 → ¬ (x ℕ.≤ y)
  foo {y = y} refl rewrite ℕₚ.+-comm y 1 = ℕₚ.1+n≰n

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
  causal-delivery-inductive rw (deliver _ _ receiver _ _ _ _ _ i d _) h {p} {e₁} (here refl) (there y)   z          | yes _        = ⊥-elim (no-delivery {e′ = e₁} rw y i z d)
  causal-delivery-inductive rw (deliver _ _ receiver _ _ _ _ _ _ _ _) h {p}      (there x)   (here refl) z          | yes _        = <-transˡ (history≤procVc rw x) (<-trans vc<combine[vc,vc′] (vc<tick[vc] {p = receiver}))
  causal-delivery-inductive _  (deliver _ _ receiver _ _ _ _ _ _ _ _) h {p}      (there x)   (there y)   z          | yes _        = h x y z
  causal-delivery-inductive _  (deliver _ _ receiver _ _ _ _ _ _ _ _) h {p}      x           y           z          | no  _        = h x y z

  causal-delivery-inductive* : ∀ {w w′} → Reachable w → w ==>* w′ → causal-delivery[ w ] → causal-delivery[ w′ ]
  causal-delivery-inductive* rw (lift x)   h = causal-delivery-inductive rw x h
  causal-delivery-inductive* rw refl       h = h
  causal-delivery-inductive* rw (tran x y) h = causal-delivery-inductive* (tran rw x) y (causal-delivery-inductive* rw x h)
