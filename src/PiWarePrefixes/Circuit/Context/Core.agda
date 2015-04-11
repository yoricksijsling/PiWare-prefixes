open import PiWare.Atom using (Atomic; module Atomic)
open import PiWare.Gates using (Gates)

module PiWarePrefixes.Circuit.Context.Core {At : Atomic} (Gt : Gates At) where

open import Data.Nat using (ℕ; suc; _+_; _⊔_)
open import Data.String using (String)
open import Data.Sum as Sum using (inj₁; inj₂)
open import Data.Vec using (_++_; splitAt)
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)

open import PiWare.Circuit {Gt = Gt}
open import PiWare.Simulation Gt using (⟦_⟧)
open import PiWarePrefixes.Simulation.Equality.Core {Gt = Gt} as SimEq using (Mk≈⟦⟧; easy-≈⟦⟧)
open import PiWarePrefixes.Simulation.Properties Gt using (_⟫-cong_; _∥-cong_)
open import PiWare.Synthesizable At using (untag)

open Atomic At using (W)

private
  import Data.Vec.Equality
  module VE = Data.Vec.Equality.PropositionalEquality

-- Indices describe the hole, parameters describe the full circuit when the hole is plugged.

data Cxt' {csₓ : IsComb} (iₓ oₓ : ℕ) : {cs : IsComb} → ℕ → ℕ → Set where
    ●-cxt : Cxt' {csₓ} iₓ oₓ {csₓ} iₓ oₓ
    DelayLoop●-cxt : ∀ {i o l} → Cxt' {csₓ} iₓ oₓ {σ} (i + l) (o + l) → Cxt' {csₓ} iₓ oₓ {ω} i o
    _⟫●-cxt_ : ∀ {cs i m o} → ℂ {cs} i m → Cxt' {csₓ} iₓ oₓ {cs} m o → Cxt' {csₓ} iₓ oₓ {cs} i o
    _●⟫-cxt_ : ∀ {cs i m o} → Cxt' {csₓ} iₓ oₓ {cs} i m → ℂ {cs} m o → Cxt' {csₓ} iₓ oₓ {cs} i o
    _∥●-cxt_ : ∀ {cs i o j p} → ℂ {cs} i o → Cxt' {csₓ} iₓ oₓ {cs} j p → Cxt' {csₓ} iₓ oₓ {cs} (i + j) (o + p)
    _●∥-cxt_ : ∀ {cs i o j p} → Cxt' {csₓ} iₓ oₓ {cs} i o → ℂ {cs} j p → Cxt' {csₓ} iₓ oₓ {cs} (i + j) (o + p)

infixr 5 _∥●-cxt_  _●∥-cxt_
infixl 4 _⟫●-cxt_  _●⟫-cxt_

plugCxt' : ∀ {csₓ iₓ oₓ cs i o} → Cxt' {csₓ} iₓ oₓ {cs} i o → ℂ {csₓ} iₓ oₓ → ℂ {cs} i o
plugCxt' ●-cxt                cₓ = cₓ
plugCxt' (DelayLoop●-cxt cxt) cₓ = DelayLoop (plugCxt' cxt cₓ)
plugCxt' (x    ⟫●-cxt cxt)   cₓ = x ⟫ (plugCxt' cxt cₓ)
plugCxt' (cxt ●⟫-cxt    x)   cₓ = (plugCxt' cxt cₓ) ⟫ x
plugCxt' (x    ∥●-cxt cxt)   cₓ = x ∥ (plugCxt' cxt cₓ)
plugCxt' (cxt ●∥-cxt    x)   cₓ = (plugCxt' cxt cₓ) ∥ x


-- For now, this only works with combinational circuits, because SimEq.≈⟦⟧ only
-- works on combinational circuits too.

data _Cxt-≈⟦⟧_ {iₓ¹ oₓ¹ iₓ² oₓ²} :
         ∀ {i¹ o¹ i² o²} →
         (cxt¹ : Cxt' {σ} iₓ¹ oₓ¹ {σ} i¹ o¹) → (cxt² : Cxt' {σ} iₓ² oₓ² {σ} i² o²) → Set where
    ● : ●-cxt Cxt-≈⟦⟧ ●-cxt
    _⟫●_ : ∀ {i¹ m¹ o¹} {c¹ : ℂ i¹ m¹} {cxt¹ : Cxt' iₓ¹ oₓ¹ m¹ o¹} →
                 ∀ {i² m² o²} {c² : ℂ i² m²} {cxt² : Cxt' iₓ² oₓ² m² o²} →
                 c¹ SimEq.≈⟦⟧ c² → cxt¹ Cxt-≈⟦⟧ cxt² →
                 (c¹ ⟫●-cxt cxt¹) Cxt-≈⟦⟧ (c² ⟫●-cxt cxt²)
    _●⟫_ : ∀ {i¹ m¹ o¹} {cxt¹ : Cxt' iₓ¹ oₓ¹ i¹ m¹} {c¹ : ℂ m¹ o¹} →
                 ∀ {i² m² o²} {cxt² : Cxt' iₓ² oₓ² i² m²} {c² : ℂ m² o²} →
                 cxt¹ Cxt-≈⟦⟧ cxt² → c¹ SimEq.≈⟦⟧ c² →
                 (cxt¹ ●⟫-cxt c¹) Cxt-≈⟦⟧ (cxt² ●⟫-cxt c²)
    _∥●_ : ∀ {i¹ o¹ j¹ p¹} {c¹ : ℂ i¹ o¹} {cxt¹ : Cxt' iₓ¹ oₓ¹ j¹ p¹} →
                 ∀ {i² o² j² p²} {c² : ℂ i² o²} {cxt² : Cxt' iₓ² oₓ² j² p²} →
                 c¹ SimEq.≈⟦⟧ c² → cxt¹ Cxt-≈⟦⟧ cxt² →
                 (c¹ ∥●-cxt cxt¹) Cxt-≈⟦⟧ (c² ∥●-cxt cxt²)
    _●∥_ : ∀ {i¹ o¹ j¹ p¹} {cxt¹ : Cxt' iₓ¹ oₓ¹ i¹ o¹} {c¹ : ℂ j¹ p¹} →
                 ∀ {i² o² j² p²} {cxt² : Cxt' iₓ² oₓ² i² o²} {c² : ℂ j² p²} →
                 cxt¹ Cxt-≈⟦⟧ cxt² → c¹ SimEq.≈⟦⟧ c² →
                 (cxt¹ ●∥-cxt c¹) Cxt-≈⟦⟧ (cxt² ●∥-cxt c²)

infixr 5 _∥●_  _●∥_
infixl 4 _⟫●_  _●⟫_

-- Congruence
-- Shows that a composed circuit is equal up to evaluation if the parts are
-- equal up to evaluation. This does not seem to imply composability of
-- equality, because it only goes one way.

≈⟦⟧-cong : ∀ {iₓ¹ oₓ¹ iₓ² oₓ² i¹ o¹ i² o²} →
             {cxt¹ : Cxt' iₓ¹ oₓ¹ i¹ o¹} {cxt² : Cxt' iₓ² oₓ² i² o²} →
             {c¹ : ℂ iₓ¹ oₓ¹} {c² : ℂ iₓ² oₓ²} →
             (cxts : cxt¹ Cxt-≈⟦⟧ cxt²) (holes : c¹ SimEq.≈⟦⟧ c²) →
             plugCxt' cxt¹ c¹ SimEq.≈⟦⟧ plugCxt' cxt² c²
≈⟦⟧-cong ● holes = holes
≈⟦⟧-cong (f≈f ⟫● cxts) holes = f≈f ⟫-cong (≈⟦⟧-cong cxts holes)
≈⟦⟧-cong (cxts ●⟫ g≈g) holes = (≈⟦⟧-cong cxts holes) ⟫-cong g≈g
≈⟦⟧-cong (f≈f ∥● cxts) holes = f≈f ∥-cong (≈⟦⟧-cong cxts holes)
≈⟦⟧-cong (cxts ●∥ g≈g) holes = (≈⟦⟧-cong cxts holes) ∥-cong g≈g
