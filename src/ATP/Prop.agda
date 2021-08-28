module ATP.Prop where

infixr 40 _⊃_
infixr 41 _∨_
infixr 42 _∧_
infix  43 ¬_
infix  44 `_

-- the atomic proposition is kept abstract
postulate
  Atom : Set

-- there's already a Prop primitive in Agda, so we name our proposition Prop′
data Prop′ : Set where
  `_  : Atom → Prop′
  _∧_ : Prop′ → Prop′ → Prop′
  _⊃_ : Prop′ → Prop′ → Prop′
  _∨_ : Prop′ → Prop′ → Prop′
  ⊤   : Prop′
  ⊥   : Prop′

¬_ : Prop′ → Prop′
¬ A = A ⊃ ⊥
