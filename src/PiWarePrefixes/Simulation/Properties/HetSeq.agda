open import PiWare.Atom using (Atomic; module Atomic)
open import PiWare.Gates using (Gates)

module PiWarePrefixes.Simulation.Properties.HetSeq {At : Atomic} (Gt : Gates At) where

open import Function using (_⟨_⟩_)
open import PiWare.Circuit Gt using (ℂ; _⟫_; _∥_)
open import PiWarePrefixes.Patterns.HetSeq Gt
open import PiWare.Plugs Gt using (id⤨)
open import PiWarePrefixes.Simulation.Properties Gt
open import PiWarePrefixes.Simulation.Equality.Core Gt as SimEq
  renaming (≈⟦⟧-refl to refl; ≈⟦⟧-sym to sym; ≈⟦⟧-trans to trans)
open import Relation.Binary.PropositionalEquality as P using (_≡_)

open Atomic At using (W)

-- With ⟫[-cong and ⟫]-cong we can convert ⟫ to and from ⟫[]. In between we can use ⟫[]-cong
-- for operations where we keep the ⟫[].
-- The definitions are picked in such a way that the proofs for ⟫[] are created with the information
-- on the left hand side of the ≈⟦⟧-equalities.

_⟫[-cong_ : ∀ {i₁ m₁ o₁} {f₁ : ℂ i₁ m₁} {g₁ : ℂ m₁ o₁} →
            ∀ {i₂ m₂ n₂ o₂} {f₂ : ℂ i₂ m₂} {g₂ : ℂ n₂ o₂} →
            (f≈f : f₁ ≈⟦⟧ f₂) → (g≈g : g₁ ≈⟦⟧ g₂) →
            f₁ ⟫ g₁ ≈⟦⟧ f₂ ⟫[ P.sym (o-equal f≈f) ⟨ P.trans ⟩ i-equal g≈g ] g₂
f≈f ⟫[-cong g≈g = f≈f ⟫[-cong′ g≈g
  where
  _⟫[-cong′_ : ∀ {i₁ m₁ o₁} {f₁ : ℂ i₁ m₁} {g₁ : ℂ m₁ o₁} →
              ∀ {i₂ m₂ n₂ o₂} {f₂ : ℂ i₂ m₂} {p₂ : m₂ ≡ n₂} {g₂ : ℂ n₂ o₂} →
              (f≈f : f₁ ≈⟦⟧ f₂) → (g≈g : g₁ ≈⟦⟧ g₂) →
              f₁ ⟫ g₁ ≈⟦⟧ f₂ ⟫[ p₂ ] g₂
  _⟫[-cong′_ {p₂ = P.refl} f≈f g≈g = (f≈f ⟨ trans ⟩ sym (⟫-right-identity _)) ⟫-cong g≈g

-- Proof for RHS is generated from the LHS (thus from p₁).
_⟫[]-cong_ : ∀ {i₁ m₁ n₁ o₁} {f₁ : ℂ i₁ m₁} {p₁ : m₁ ≡ n₁} {g₁ : ℂ n₁ o₁} →
             ∀ {i₂ m₂ n₂ o₂} {f₂ : ℂ i₂ m₂} {g₂ : ℂ n₂ o₂} →
             (f≈f : f₁ ≈⟦⟧ f₂) → (g≈g : g₁ ≈⟦⟧ g₂) →
             f₁ ⟫[ p₁ ] g₁ ≈⟦⟧ f₂ ⟫[ P.sym (o-equal f≈f) ⟨ P.trans ⟩ p₁ ⟨ P.trans ⟩ i-equal g≈g ] g₂
_⟫[]-cong_ {p₁ = P.refl} f≈f g≈g with o-equal f≈f | i-equal g≈g
_⟫[]-cong_ {p₁ = P.refl} f≈f g≈g | P.refl | P.refl = f≈f ⟫-cong refl ⟫-cong g≈g

_⟫]-cong_ : ∀ {i₁ m₁ n₁ o₁} {f₁ : ℂ i₁ m₁} {p₁ : m₁ ≡ n₁} {g₁ : ℂ n₁ o₁} →
            ∀ {i₂ m₂ o₂} {f₂ : ℂ i₂ m₂} {g₂ : ℂ m₂ o₂} →
            (f≈f : f₁ ≈⟦⟧ f₂) → (g≈g : g₁ ≈⟦⟧ g₂) →
            f₁ ⟫[ p₁ ] g₁ ≈⟦⟧ f₂ ⟫ g₂
_⟫]-cong_ {p₁ = P.refl} f≈f g≈g = (⟫-right-identity _ ⟨ trans ⟩ f≈f) ⟫-cong g≈g

-- Sometimes you want to replace the automatically generated proof by something else.
⟫[]-replace : ∀ {i m n o} {f : ℂ i m} {p : m ≡ n} {g : ℂ n o} →
              (q : m ≡ n) → f ⟫[ p ] g ≈⟦⟧ f ⟫[ q ] g
⟫[]-replace {p = P.refl} P.refl = refl


-- Most of the laws for ⟫ also hold for ⟫[]
⟫[]-right-identity : ∀ {i m o} (f : ℂ i m) {p : m ≡ o} → f ⟫[ p ] id⤨ ≈⟦⟧ f
⟫[]-right-identity f {P.refl} = ⟫-right-identity _
                      ⟨ trans ⟩ ⟫-right-identity f

⟫[]-left-identity : ∀ {i m o} {p : i ≡ m} (f : ℂ m o) → id⤨ ⟫[ p ] f ≈⟦⟧ f
⟫[]-left-identity {p = P.refl} f = ⟫-assoc _ _ _
                         ⟨ trans ⟩ ⟫-left-identity _
                         ⟨ trans ⟩ ⟫-left-identity f

⟫[]-assoc : ∀ {i j k m n o} (f : ℂ i j) {p : j ≡ k} (g : ℂ k m) {q : m ≡ n} (h : ℂ n o) →
            f ⟫[ p ] g ⟫[ q ] h ≈⟦⟧ f ⟫[ p ] (g ⟫[ q ] h)
⟫[]-assoc f {P.refl} g {P.refl} h = (⟫-assoc _ _ _) ⟫-cong refl
                             ⟨ trans ⟩ ⟫-assoc _ _ _ 
