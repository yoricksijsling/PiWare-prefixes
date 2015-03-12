open import PiWare.Atom using (Atomic; module Atomic)
open import PiWare.Gates using (Gates)

module PiWarePrefixes.Patterns.Core {At : Atomic} (Gt : Gates At) where

open import Data.Fin as Fin using (Fin)
open import Data.Nat using (ℕ; zero; suc; _*_; _+_)
open import Data.Nat.Properties.Simple using (+-right-identity; *-comm)
open import Data.Product using (_,_; <_,_>)
open import Data.Vec hiding (zipWith)
open import Function using (id; _$_; flip)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import PiWare.Circuit Gt using (ℂ; 𝐂; Plug; _⟫_; _∥_)
open import PiWarePrefixes.MinGroups using (ExtractInsert; size)
open import PiWare.Patterns Gt using (parsN)
import PiWarePrefixes.Patterns.Stretch Gt as Stretch
open import PiWare.Plugs Gt using (id⤨)
open import PiWarePrefixes.Plugs.Core Gt using (zip⤨)

open Atomic At using (W; Atom)


zipWith : ∀ {k n cs} → ℂ {cs} k 1 → ℂ {cs} (k * n) (1 * n)
zipWith {k} {n} f with (zip⤨ {k} {n} ⟫ parsN {n} f)
zipWith {k} {n} f | z rewrite *-comm n 1 | +-right-identity n = z

⤙-direction : ExtractInsert
⤙-direction = record
  { extf = < head , tail >
  ; insf = _∷_
  ; extf-insf-id = extf-insf-id
  ; insf-extf-id = insf-extf-id
  }
  where
  extf-insf-id : ∀ {A n} (x : Vec A (suc n)) → head x ∷ tail x ≡ x
  extf-insf-id (x ∷ xs) = refl
  insf-extf-id : ∀ {A n} (x : A) (xs : Vec A n) → head (x ∷ xs) , tail (x ∷ xs) ≡ (x , xs)
  insf-extf-id x xs = refl

_⤙_ : ∀ {n cs} → ℂ {cs} n n → (as : Vec ℕ n) → ℂ {cs} (size 1 as) (size 1 as)
_⤙_ = Stretch.WithDirection.stretch ⤙-direction

-- open import Level using (_⊔_)
-- open import Data.Product using (Σ; ∃!; ∃; _×_)

-- ∃₂! : ∀ {a b c ℓ} {A : Set a} {B : A → Set b} →
--      (_≈_ : A → A → Set ℓ) → ({x x' : A} {p : x ≈ x'} → B x → B x' → Set ℓ) →
--      (C : (x : A) → B x → Set c) → Set (a ⊔ b ⊔ c ⊔ ℓ)
-- ∃₂! _≈_ _~_ C = ∃ λ a → ∃ λ b → C a b × (∀ {a' b'} → C a' b' → Σ (a ≈ a') (λ p → _~_ {p = p} b b') )

-- initLast′ : ∀ {a n} {A : Set a} (xs : Vec A (1 + n)) →
--   ∃₂! _≡_ _≡_ λ ys y → xs ≡ ys ∷ʳ y
-- initLast′ {n = zero} (x ∷ []) = [] , x , refl , (λ { {[]} refl → refl , refl})
-- initLast′ {n = suc n} (x ∷ xs) with initLast′ xs

⤚-direction : ExtractInsert
⤚-direction = record
  { extf = < last , init >
  ; insf = flip _∷ʳ_
  ; extf-insf-id = extf-insf-id
  ; insf-extf-id = insf-extf-id
  }
  where
  extf-insf-id : ∀ {A n} (x : Vec A (suc n)) → init x ∷ʳ last x ≡ x
  extf-insf-id xs with initLast xs
  extf-insf-id .(xs ∷ʳ x) | xs , x , refl = refl
  postulate
    insf-extf-id : ∀ {A n} (x : A) (xs : Vec A n) → last (xs ∷ʳ x) , init (xs ∷ʳ x) ≡ x , xs

_⤚_ : ∀ {n cs} → (as : Vec ℕ n) → ℂ {cs} n n → ℂ {cs} (size 1 as) (size 1 as)
_⤚_ = flip (Stretch.WithDirection.stretch ⤚-direction)
