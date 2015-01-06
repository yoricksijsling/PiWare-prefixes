open import PiWare.Atom using (Atomic)
open import PiWare.Gates using (Gates)

module PiWarePrefixes.Simulation.Properties.Core {At : Atomic} (Gt : Gates At) where

open import Data.Nat using (ℕ; _+_)
open import Data.Product
open import Function
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as PropEq

open import PiWare.Circuit.Core Gt
open import PiWarePrefixes.Circuit.Core Gt using (combℂ')
open import PiWare.Simulation.Core Gt
open import PiWare.Synthesizable At using (W)

-- Equivalence up to combinational evaluation

infix 4 _≡e'_
_≡e'_ : ∀ {i o} (c₁ c₂ : combℂ' i o) → Set
_≡e'_ {i} (c₁ , comb₁) (c₂ , comb₂) = (w : W i) → ⟦ c₁ ⟧' {comb₁} w ≡ ⟦ c₂ ⟧' {comb₂} w

≡e'-setoid : (i o : ℕ) → Setoid _ _
≡e'-setoid i o = record
  { Carrier = combℂ' i o
  ; _≈_     = _≡e'_
  ; isEquivalence = record
    { refl    = λ         w → refl
    ; sym     = λ i≡j     w → sym (i≡j w)
    ; trans   = λ i≡j j≡k w → trans (i≡j w) (j≡k w)
    }
  }

-- import Relation.Binary.EqReasoning as EqR
-- module ≡e'-Reasoning {i o : ℕ} = EqR (≡e'-setoid i o)

import Relation.Binary.EqReasoning as EqR
module ≡e'-Reasoning {i o : ℕ} where
  open EqR (≡e'-setoid i o) public

  infixr 2 _,≈⟨_⟩_
  _,≈⟨_⟩_ : ∀ x {y z} {cx : comb' x} → (x , cx) ≡e' y → y IsRelatedTo z → (x , cx) IsRelatedTo z
  _,≈⟨_⟩_ x {cx = cx} x≡y y≡z = x , cx ≈⟨ x≡y ⟩ y≡z

  infix  2 _,∎
  _,∎ : ∀ x {cx : comb' x} → (x , cx) IsRelatedTo (x , cx)
  _,∎ x {cx} = x , cx ∎
 
infix 4 _≡E'_
_≡E'_ : ∀ {i o} (c₁ c₂ : ℂ' i o) {cc₁ : comb' c₁} {cc₂ : comb' c₂} → Set
_≡E'_ c₁ c₂ {cc₁} {cc₂} = c₁ , cc₁ ≡e' c₂ , cc₂
