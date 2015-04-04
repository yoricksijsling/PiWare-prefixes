open import PiWare.Atom using (Atomic; module Atomic)
open import PiWare.Gates using (Gates)

module PiWarePrefixes.Simulation.Equality.Core {At : Atomic} (Gt : Gates At) where

open import Data.Nat using (ℕ)
open import Data.Product using (_×_; uncurry)
open import Function using (id; _∘_)
import Relation.Binary.Indexed as I
open import Relation.Binary.PropositionalEquality as PropEq using (_≡_; refl)

open import PiWare.Circuit Gt
open import PiWare.Simulation Gt
open import PiWare.Synthesizable At using (untag)

open Atomic At using (W)

private
  import Data.Vec.Equality
  module VE = Data.Vec.Equality.PropositionalEquality

infix 4 _≈e_
_≈e_ : ∀ {i₁ o₁ i₂ o₂} (f : ℂ {σ} i₁ o₁) (g : ℂ {σ} i₂ o₂) → Set
_≈e_ {i₁} {i₂ = i₂} f g = {w₁ : W i₁} {w₂ : W i₂} (w≈w : w₁ VE.≈ w₂) → ⟦ f ⟧ w₁ VE.≈ ⟦ g ⟧ w₂

-- ≈e is a useful alias, but is not a full definition of equality. When the
-- sizes are different, all circuits are equal.
module dont-use-≈e where
  silly≈ : (f : ℂ 0 0) (g : ℂ 1 1) → f ≈e g
  silly≈ f g ()

infix 4 _≈⟦⟧_
data _≈⟦⟧_ {i₁ o₁ i₂ o₂ : ℕ} :
     (f : ℂ {σ} i₁ o₁) (g : ℂ {σ} i₂ o₂) → Set where
  Mk≈⟦⟧ : {f : ℂ i₁ o₁} {g : ℂ i₂ o₂}
          (pi : i₁ ≡ i₂) (f≈g : f ≈e g) → f ≈⟦⟧ g

i-equal : ∀ {i₁ o₁ i₂ o₂} {f : ℂ i₁ o₁} {g : ℂ i₂ o₂} →
          f ≈⟦⟧ g → i₁ ≡ i₂
i-equal (Mk≈⟦⟧ refl f≈g) = refl

abstract
  o-equal : ∀ {i₁ o₁ i₂ o₂} {f : ℂ i₁ o₁} {g : ℂ i₂ o₂} →
            f ≈⟦⟧ g → o₁ ≡ o₂
  o-equal (Mk≈⟦⟧ refl f≈g) = VE.length-equal (f≈g (VE.refl dummyW))
    where
    open import Data.Fin using (#_)
    open import Data.Vec using (replicate)
    dummyW : ∀ {n} → W n
    dummyW = replicate (Atomic.n→atom At (# 0))

-- A convenient function so you can often skip the `with`.
easy-≈⟦⟧ : ∀ {i o₁ o₂} {f : ℂ i o₁} {g : ℂ i o₂} →
           ((w : W i) → ⟦ f ⟧ w VE.≈ ⟦ g ⟧ w) →
           f ≈⟦⟧ g
easy-≈⟦⟧ {i} {f = f} {g} f≈g = Mk≈⟦⟧ refl to-≈e
  where
  to-≈e : {w₁ w₂ : W i} → w₁ VE.≈ w₂ → ⟦ f ⟧ w₁ VE.≈ ⟦ g ⟧ w₂
  to-≈e w≈w with VE.to-≡ w≈w
  to-≈e w≈w | refl = f≈g _


--------------------------------------------------------------------------------
-- ≈⟦⟧ is a setoid

≈⟦⟧-refl : ∀ {i o} {f : ℂ i o} → f ≈⟦⟧ f
≈⟦⟧-refl = easy-≈⟦⟧ (λ w≈w → VE.refl _)

≈⟦⟧-sym : ∀ {i₁ o₁ i₂ o₂} {f : ℂ i₁ o₁} {g : ℂ i₂ o₂} →
          f ≈⟦⟧ g → g ≈⟦⟧ f
≈⟦⟧-sym (Mk≈⟦⟧ refl f≈g) = easy-≈⟦⟧ (λ w → VE.sym (f≈g (VE.sym (VE.refl w))))

≈⟦⟧-trans : ∀ {i₁ o₁ i₂ o₂ i₃ o₃} {f : ℂ i₁ o₁} {g : ℂ i₂ o₂} {h : ℂ i₃ o₃} →
            f ≈⟦⟧ g → g ≈⟦⟧ h → f ≈⟦⟧ h
≈⟦⟧-trans (Mk≈⟦⟧ refl f≈g) (Mk≈⟦⟧ refl g≈h) = easy-≈⟦⟧ (λ w → VE.trans (f≈g (VE.refl w)) (g≈h (VE.refl w)))

≈⟦⟧-setoid : I.Setoid (ℕ × ℕ) _ _
≈⟦⟧-setoid = record
  { Carrier = uncurry ℂ
  ; _≈_ = _≈⟦⟧_
  ; isEquivalence = record
    { refl = ≈⟦⟧-refl
    ; sym = ≈⟦⟧-sym
    ; trans = ≈⟦⟧-trans
    }
  }

reindex-setoid : ∀ {i j s₁ s₂} {I : Set i} {J : Set j} (f : J → I) → I.Setoid I s₁ s₂ → I.Setoid J s₁ s₂
reindex-setoid f s = record
  { Carrier = S.Carrier ∘ f
  ; _≈_ = S._≈_
  ; isEquivalence = record { refl = E.refl ; sym = E.sym ; trans = E.trans }
  }
  where
  module S = I.Setoid s
  module E = I.IsEquivalence S.isEquivalence

reindexed-≈⟦⟧-setoid : ∀ {a} {A : Set a} (f : A → ℕ × ℕ) → I.Setoid A _ _
reindexed-≈⟦⟧-setoid f = reindex-setoid f ≈⟦⟧-setoid

--------------------------------------------------------------------------------
-- Equational reasoning

-- Our custom equational reasoning. Eqreasoning from the standard library does
-- not support indexed setoids.

module ≈⟦⟧-Reasoning where
  infix  2 _∎
  infixr 2 _≈⟦⟧⟨_⟩_ _≈⟦⟧⟨⟩_
  infix  1 begin_

  begin_ : ∀ {i₁ o₁ i₂ o₂} {f : ℂ i₁ o₁} {g : ℂ i₂ o₂} → f ≈⟦⟧ g → f ≈⟦⟧ g
  begin_ = id

  _≈⟦⟧⟨_⟩_ : ∀ {i₁ o₁ i₂ o₂ i₃ o₃} (f : ℂ i₁ o₁) {g : ℂ i₂ o₂} {h : ℂ i₃ o₃} →
          f ≈⟦⟧ g → g ≈⟦⟧ h → f ≈⟦⟧ h
  _≈⟦⟧⟨_⟩_ _ = ≈⟦⟧-trans

  _≈⟦⟧⟨⟩_ : ∀ {i₁ o₁ i₂ o₂} (f : ℂ i₁ o₁) {g : ℂ i₂ o₂} →
          f ≈⟦⟧ g → f ≈⟦⟧ g
  _≈⟦⟧⟨⟩_ _ = id

  _∎ : ∀ {i o} (f : ℂ i o) → f ≈⟦⟧ f
  _∎ _ = ≈⟦⟧-refl

