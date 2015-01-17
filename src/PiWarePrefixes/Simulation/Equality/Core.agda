open import PiWare.Atom using (Atomic)
open import PiWare.Gates using (Gates)

module PiWarePrefixes.Simulation.Equality.Core {At : Atomic} (Gt : Gates At) where

open import Data.Nat using (ℕ; _+_)
open import Data.Product using (proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Vec using (splitAt; _++_)
open import Function
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as PropEq

open import PiWare.Circuit.Core Gt
open import PiWarePrefixes.Circuit.Context.Core Gt
open import PiWare.Simulation.Core Gt
open import PiWare.Synthesizable At using (W; untag)

-- Equivalence up to combinational evaluation

infix 4 _≡e_
_≡e_ : ∀ {i o} (c₁ c₂ : ℂ' {Comb} i o) → Set
_≡e_ {i} c₁ c₂ = (w : W i) → ⟦ c₁ ⟧' w ≡ ⟦ c₂ ⟧' w

≡e-setoid : (i o : ℕ) → Setoid _ _
≡e-setoid i o = record
  { Carrier = ℂ' {Comb} i o
  ; _≈_     = _≡e_
  ; isEquivalence = record
    { refl    = λ         w → refl
    ; sym     = λ i≡j     w → sym (i≡j w)
    ; trans   = λ i≡j j≡k w → trans (i≡j w) (j≡k w)
    }
  }

-- Congruence
-- Shows that a composed circuit is equal up to evaluation if the parts are
-- equal up to evaluation. This does not seem to imply composability of
-- equality, because it only goes one way.

-- Agda is not able to derive c₁ and c₂ from the type c₁ ≡e c₂

≡e-cong : ∀ {iₓ oₓ i o} (cxt : Cxt' iₓ oₓ i o) {c₁ c₂ : ℂ' iₓ oₓ} →
          c₁ ≡e c₂ → plugCxt' cxt c₁ ≡e plugCxt' cxt c₂
≡e-cong ∙ p w = p w
≡e-cong (x ⟫'∙ cxt) p w = ≡e-cong cxt p (⟦ x ⟧' w)
≡e-cong (cxt ∙⟫' x) {c₁} {c₂} p w rewrite ≡e-cong cxt {c₁} {c₂} p w = refl
≡e-cong (_|'∙_ {i₁ = i₁} x cxt) {c₁} {c₂} p w
        rewrite ≡e-cong cxt {c₁} {c₂} p (proj₁ (proj₂ (splitAt i₁ w))) = refl
≡e-cong (_∙|'_ {i₁ = i₁} cxt x) {c₁} {c₂} p w
        rewrite ≡e-cong cxt {c₁} {c₂} p (proj₁ (splitAt i₁ w)) = refl
≡e-cong (_|+'∙_ {i₁ = i₁} x cxt) p w with untag {i₁} w
... | inj₁ _ = refl
... | inj₂ y = ≡e-cong cxt p y
≡e-cong (_∙|+'_ {i₁ = i₁} cxt x) p w with untag {i₁} w
... | inj₁ y = ≡e-cong cxt p y
... | inj₂ _ = refl
≡e-cong (cxt ∙Named x) p w = ≡e-cong cxt p w


-- Equational reasoning

import Relation.Binary.EqReasoning as EqR
module ≡e-Reasoning {i o : ℕ} where
  open EqR (≡e-setoid i o) public
    hiding (_≡⟨_⟩_; _≡⟨⟩_)
    renaming (_≈⟨_⟩_ to _≡e⟨_⟩_)

  -- Whether a context can be applied to a circuit is decidable..
  -- Apply the context to get the holes on both sides, if possible.
  -- If it is not allowed, we can ask for a ⊥ somewhere?

  -- _≡e⟨_⟩_ : ∀ x {y z} → x ≡e y → y IsRelatedTo z → x IsRelatedTo z
  -- infixr 2 _≡e-cong⟨_⟩_
  -- _≡e-cong⟨_⟩_ : ∀ x {y z} → f → x ≡e y → f y IsRelatedTo z → f x IsRelatedTo z
