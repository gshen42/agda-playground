open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin using (Fin; zero; suc; _≟_)
open import Data.List using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Product using (_,_)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

import CBCAST.Event as Event

-- unconstrained broadcast execution, parameterized over the message type `Msg` and the number of process `n`
-- here we assume a reliable asynchronous network, that is messages can be arbitrarily delayed or reordered but never lost
-- inspired by Verdi, see this post http://jamesrwilcox.com/NetworkSemantics.html
module CBCAST.Broadcast (A : Set) (n : ℕ) where

open Event A

Process : Set
Process = Fin n

-- a world is a snapshot of a system's execution
-- which is essentially a list of events, coupled with the latest event of each process
record World : Set where
  constructor world
  field
    processState : Process → Event
    history      : List Event

open World

update : ∀ {B : Set} → (Process → B) → Process → B → (Process → B)
update m p b p' with p' ≟ p
...                | yes _ = b
...                | no  _ = m p'

infix 4 _==>_

data _==>_ : World → World → Set where
  send    : ∀ {p m w}
          → let ev = send m (processState w p)
            in w ==> (world (update (processState w) p ev)
                             (ev ∷ (history w)))

  receive : ∀ {p m ev' w}
          → (send m ev' ∈ (history w))
          → let ev = receive m (send m ev') (ev' , refl) (processState w p)
            in w ==> w

infix  2 _==>*_
infix  1 begin_
infixr 2 _==>⟨_⟩_
infix  3 _∎

data _==>*_ : World → World → Set where
  _∎       : ∀ {w}
           → w ==>* w

  _==>⟨_⟩_ : ∀ {w w' w''}
           → w ==> w'
           → w' ==>* w''
           → w ==>* w''

begin_ : ∀ {w w'} → w ==> w' → w ==> w'
begin w==>w' = w==>w'

world₀ : World
world₀ = world (λ {_ → empty}) []

Reachable : World → Set
Reachable w = world₀ ==>* w

causal-consistent : World → Set
causal-consistent w = ∀ {m₁ e₁ e₁[send]m₁ e' m₂ e₂ e₂[send]m₂ e''}
                    → (receive m₁ e₁ e₁[send]m₁ e')  ∈ (history w)
                    → (receive m₂ e₂ e₂[send]m₂ e'') ∈ (history w)
                    → (receive m₁ e₁ e₁[send]m₁ e') happensBefore (receive m₂ e₂ e₂[send]m₂ e'')
                    → ¬ (e₂ happensBefore e₁)

postulate
  -- this property is not true for unconstrained broadcast, list here only for completeness
  safety : ∀ {w} → Reachable w → causal-consistent w
