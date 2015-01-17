open import PiWare.Atom using (Atomic)
open import PiWare.Gates using (Gates)

module PiWarePrefixes.Circuit.Context.Core {At : Atomic} (Gt : Gates At) where

open import Data.Nat using (ℕ; suc; _+_; _⊔_)
open import Data.String using (String)
open import PiWare.Circuit.Core Gt

-- Indices describe the hole, parameters describe the full circuit when the hole is plugged.

data Cxt' {csₓ : CombSeq} (iₓ oₓ : ℕ) : {cs : CombSeq} → ℕ → ℕ → Set where
    ∙ : Cxt' {csₓ} iₓ oₓ {csₓ} iₓ oₓ
    DelayLoop∙ : ∀ {i o l} → Cxt' {csₓ} iₓ oₓ {Comb} (i + l) (o + l) → Cxt' {csₓ} iₓ oₓ {Seq} i o
    _⟫'∙_ : ∀ {cs i m o} → ℂ' {cs} i m → Cxt' {csₓ} iₓ oₓ {cs} m o → Cxt' {csₓ} iₓ oₓ {cs} i o
    _∙⟫'_ : ∀ {cs i m o} → Cxt' {csₓ} iₓ oₓ {cs} i m → ℂ' {cs} m o → Cxt' {csₓ} iₓ oₓ {cs} i o
    _|'∙_ : ∀ {cs i₁ o₁ i₂ o₂} → ℂ' {cs} i₁ o₁ → Cxt' {csₓ} iₓ oₓ {cs} i₂ o₂ → Cxt' {csₓ} iₓ oₓ {cs} (i₁ + i₂) (o₁ + o₂)
    _∙|'_ : ∀ {cs i₁ o₁ i₂ o₂} → Cxt' {csₓ} iₓ oₓ {cs} i₁ o₁ → ℂ' {cs} i₂ o₂ → Cxt' {csₓ} iₓ oₓ {cs} (i₁ + i₂) (o₁ + o₂)
    _|+'∙_ : ∀ {cs i₁ i₂ o} → ℂ' {cs} i₁ o → Cxt' {csₓ} iₓ oₓ {cs} i₂ o → Cxt' {csₓ} iₓ oₓ {cs} (suc (i₁ ⊔ i₂)) o
    _∙|+'_ : ∀ {cs i₁ i₂ o} → Cxt' {csₓ} iₓ oₓ {cs} i₁ o → ℂ' {cs} i₂ o → Cxt' {csₓ} iₓ oₓ {cs} (suc (i₁ ⊔ i₂)) o
    _∙Named_ : ∀ {cs i o} → Cxt' {csₓ} iₓ oₓ {cs} i o → String → Cxt' {csₓ} iₓ oₓ {cs} i o

infixr 5 _|'∙_  _∙|'_
infixr 5 _|+'∙_ _∙|+'_
infixl 4 _⟫'∙_  _∙⟫'_

plugCxt' : ∀ {csₓ iₓ oₓ cs i o} → Cxt' {csₓ} iₓ oₓ {cs} i o → ℂ' {csₓ} iₓ oₓ → ℂ' {cs} i o
plugCxt' ∙                cₓ = cₓ
plugCxt' (DelayLoop∙ cxt) cₓ = DelayLoop (plugCxt' cxt cₓ)
plugCxt' (x    ⟫'∙ cxt)   cₓ = x ⟫' (plugCxt' cxt cₓ)
plugCxt' (cxt ∙⟫'    x)   cₓ = (plugCxt' cxt cₓ) ⟫' x
plugCxt' (x    |'∙ cxt)   cₓ = x |' (plugCxt' cxt cₓ)
plugCxt' (cxt ∙|'    x)   cₓ = (plugCxt' cxt cₓ) |' x
plugCxt' (x    |+'∙ cxt)  cₓ = x |+' (plugCxt' cxt cₓ)
plugCxt' (cxt ∙|+'    x)  cₓ = (plugCxt' cxt cₓ) |+' x
plugCxt' (cxt ∙Named s)   cₓ = (plugCxt' cxt cₓ) Named s
