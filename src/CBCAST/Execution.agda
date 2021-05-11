open import Data.Nat using (ℕ; zero; suc; _+_; _≤_; _<_)
open import Data.Fin using (Fin; zero; suc; _≟_)
open import Data.List using (List; []; _∷_)
open import Data.List.NonEmpty using (List⁺; _∷_; head; tail; _∷⁺_; toList)
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃; ∃-syntax)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; _≢_)

import CBCAST.Event as Event

module CBCAST.Execution (A : Set) (n : ℕ) where

Process : Set
Process = Fin n

VectorClock : Set
VectorClock = Process → ℕ

_[_] : VectorClock → Process → ℕ
vc [ k ] = vc k

_vcLess_ : VectorClock → VectorClock → Set
vc₁ vcLess vc₂ = ∀ p → vc₁ p < vc₂ p

_vcLessEqual_ : VectorClock → VectorClock → Set
vc₁ vcLessEqual vc₂ = ∀ p → vc₁ p ≤ vc₂ p

deliverable : (Process × VectorClock) → (Process × VectorClock) → Set
deliverable (sender , vcₘ) (receiver , vcₚ) = ∀ k → (k ≡ sender → vcₘ [ k ] ≡ vcₚ [ k ] + 1)
                                                  × (k ≢ sender → vcₘ [ k ] ≤ vcₚ [ k ])

postulate
  vcTick : VectorClock → Process → VectorClock

  vcCombine : VectorClock → VectorClock → VectorClock

  deliverable→vcCombine≡vcTick : ∀ {p₁ p₂ vc₁ vc₂}
                               → deliverable (p₁ , vc₁) (p₂ , vc₂)
                               → vcCombine vc₁ vc₂ ≡ vcTick vc₂ p₁

open Event A

record World : Set where
  constructor world
  field
    processState : Process → List⁺ (Event × VectorClock)

open World

update : ∀ {B : Set} → (Process → List⁺ B) → Process → B → (Process → List⁺ B)
update m p b p' with p' ≟ p
...                | yes _ = b ∷⁺ m p'
...                | no  _ = m p'

infix 4 _==>_

data _==>_ : World → World → Set where
  broadcast : ∀ {w} p m
            → let (e , vc) = head (processState w p) in
              w ==> world (update (processState w) p (send m e , vcTick vc p))

  deliver   : ∀ {w e' vc'} p p' m
            → let (e , vc) = head (processState w p) in
              (send m e' , vc') ∈ (toList (processState w p'))
            → deliverable (p' , vc') (p , vc)
            → w ==> world (update (processState w) p (receive m (send m e') (e' , refl) e , vcCombine vc vc'))

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

vc₀ : VectorClock
vc₀ _ = 0

processState₀ : Process → List⁺ (Event × VectorClock)
processState₀ _ = (empty , vc₀) ∷ []

world₀ : World
world₀ = world processState₀

reachable : World → Set
reachable w = world₀ ==>* w

causal-delivery : World → Set
causal-delivery w = ∀ {p₁ p₂ p vc₁ vc₂ vc₁' vc₂' e₁p e₂p e₁p' e₂p' m₁ m₂ }
                  → (send m₁ e₁p , vc₁)                                 ∈ (toList (processState w p₁))
                  → (send m₂ e₂p , vc₂)                                 ∈ (toList (processState w p₂))
                  → (receive m₁ (send m₁ e₁p) (e₁p , refl) e₁p' , vc₁') ∈ (toList (processState w p))
                  → (receive m₂ (send m₂ e₂p) (e₂p , refl) e₂p' , vc₂') ∈ (toList (processState w p))
                  → (send m₁ e₁p) ─→ (send m₂ e₂p)
                  → (receive m₁ (send m₁ e₁p) (e₁p , refl) e₁p') ─→ (receive m₂ (send m₂ e₂p) (e₂p , refl) e₂p')

safety : ∀ {w} → reachable w → causal-delivery w
-- proof is in the end

postulate
  wellformed : ∀ {w p e e' vc vc'}
             → reachable w
             → (e , vc) ∈ (toList (processState w p))
             → e' ─→ e
             → ∃[ p' ] (e' , vc') ∈ (toList (processState w p'))

  hb→vcLess₁ : ∀ {e₁ e₂ vc₁ vc₂ p₁ p₂ w}
             → (e₁ , vc₁) ∈ (toList (processState w p₁))
             → (e₂ , vc₂) ∈ (toList (processState w p₂))
             → e₁ ─→ e₂
             → vc₁ vcLess vc₂

  send≤receive : ∀ {w p₁ p₂ vc₁ vc₂ m e₁p e₂p}
               → (send m e₁p , vc₁)                              ∈ (toList (processState w p₁))
               → (receive m (send m e₁p) (e₁p , refl) e₂p , vc₂) ∈ (toList (processState w p₂))
               → vc₁ vcLessEqual vc₂

  list≤head : ∀ {e vc p w}
            → (e , vc) ∈ (toList (processState w p))
            → vc vcLess (proj₂ (head (processState w p)))

step₀ : ∀ {w}
      → world₀ ==> w
      → causal-delivery w
step₀ (deliver _ _ _ (here ())  _)
step₀ (deliver _ _ _ (there ()) _)
step₀ (broadcast p _) {p = p'} _ _ t               with p' ≟ p
step₀ (broadcast p _) {p = p'} _ _ (there (there ())) | yes _
step₀ (broadcast p _) {p = p'} _ _ (there ())         | no _

step-inductive : ∀ {w w'}
               → reachable w
               → causal-delivery w
               → w ==> w'
               → causal-delivery w'
step-inductive a b (broadcast p m) {p = p'}                         c d e         f          g with p' ≟ p
step-inductive a b (broadcast p m) {p = p'} {vc₁ = vc₁} {vc₂ = vc₂} c d (there e) (there f)  g    | yes _ = b {vc₁ = vc₁} {vc₂ = vc₂} (proj₂ (wellformed a e (sendBeforeReceive refl))) ((proj₂ (wellformed a f (sendBeforeReceive refl)))) e f g
step-inductive a b (broadcast p m) {p = p'} {vc₁ = vc₁} {vc₂ = vc₂} c d e         f          g    | no  _ = b {vc₁ = vc₁} {vc₂ = vc₂} (proj₂ (wellformed a e (sendBeforeReceive refl))) ((proj₂ (wellformed a f (sendBeforeReceive refl)))) e f g

-- continute with deliver case
step-inductive a b (deliver p p' m x y) {p = p''}                         c d e           f           g with p'' ≟ p
step-inductive a b (deliver p p' m x y) {p = p''} {vc₁ = vc₁} {vc₂ = vc₂} c d e           f           g | no  _ = b {vc₁ = vc₁} {vc₂ = vc₂} (proj₂ (wellformed a e (sendBeforeReceive refl))) (proj₂ (wellformed a f (sendBeforeReceive refl))) e f g
step-inductive a b (deliver p p' m x y) {p = p''} {vc₁ = vc₁} {vc₂ = vc₂} c d (there e)   (there f)   g | yes _ = b {vc₁ = vc₁} {vc₂ = vc₂} (proj₂ (wellformed a e (sendBeforeReceive refl))) (proj₂ (wellformed a f (sendBeforeReceive refl))) e f g
step-inductive a b (deliver p p' m x y) {p = p''}                         c d (here refl) (here refl) g | yes _ = ⊥-elim (hb-irreflexive g)

-- e₂ delivered first case, contradiction
step-inductive {w} {w'} a b (deliver p p' m x y) {p₁} {p₂} {p''} {vc₁} {vc₂} {vc₁'} {vc₂'} c d (here e) (there f) g | yes refl = {!!}
  where
    vc₁<vc₂ : vc₁ vcLess vc₂
    vc₁<vc₂ = hb→vcLess₁ {p₁ = p₁} {p₂ = p₂} {w = w'} c d g

    -- vc₂≤vc₂' : vc₂ vcLessEqual vc₂'
    -- vc₂≤vc₂' = send≤receive {w'} {p₂} {p} d {!there f!}

--    vc₂≤vcₚ : vc₂ vcLess (proj₂ (head (processState w p)))
--    vc₂≤vcₚ = list≤head {p = p} {w = w} d

    -- vc₁[p]≡vcₚ[p]+1 : (vc₁ p') ≡ ((proj₂ (head (processState w' p₂))) p')
    -- vc₁[p]≡vcₚ[p]+1 = proj₁ (y p') refl

-- e₁ delivered first case
step-inductive a b (deliver p p' m x y) {p = p''}                         c d (there e)   (here f)    g | yes _ = {!!}


causal-delivery-inductive : ∀ {w w'}
                          → reachable w
                          → causal-delivery w
                          → w ==>* w'
                          → causal-delivery w'
causal-delivery-inductive a b refl = b
causal-delivery-inductive a b (tran x y) = causal-delivery-inductive (tran a x) (causal-delivery-inductive a b x) y
causal-delivery-inductive a b (lift x)   = step-inductive a b x

-- proof of `safety`
safety refl (here ())
safety refl (there ())
safety (tran x y) = causal-delivery-inductive x (safety x) y
safety (lift x)   = step₀ x
