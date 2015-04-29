open import PiWare.Atom using (Atomic; module Atomic)
open import PiWare.Gates using (Gates)

module PiWarePrefixes.Simulation.Properties.HetSeq {At : Atomic} {Gt : Gates At} where

open import Data.Nat using (_+_; pred)
open import Data.Nat.Properties using (cancel-+-left)
open import Data.Nat.Properties.Simple using (+-comm)
open import Function using (flip; _∘_; _⟨_⟩_)
open import PiWare.Circuit {Gt = Gt} using (ℂ; _⟫_; _∥_; σ)
open import PiWarePrefixes.Patterns.HetSeq {Gt = Gt}
open import PiWare.Plugs Gt using (id⤨)
open import PiWare.Simulation Gt using (⟦_⟧)
open import PiWarePrefixes.Simulation.Properties {Gt = Gt}
open import PiWarePrefixes.Simulation.Equality.Core {Gt = Gt} as SimEq
  renaming (≈⟦⟧-refl to refl; ≈⟦⟧-sym to sym; ≈⟦⟧-trans to trans)
open import Relation.Binary.PropositionalEquality as P using (_≡_)

open Atomic At using (W)




⟫[]-to-⟫ : ∀ {i m o} {f : ℂ i m} {g : ℂ m o} →
            f ⟫[ P.refl ] g ≈⟦⟧ f ⟫ g
⟫[]-to-⟫ = reveal-⟫[] ⟨ trans ⟩ ⟫-right-identity _ ⟫-cong refl

-- Sometimes you want to replace the automatically generated proof by something else.
⟫[]-replace : ∀ {i m n o} {f : ℂ i m} {p : m ≡ n} {g : ℂ n o} →
              (q : m ≡ n) → f ⟫[ p ] g ≈⟦⟧ f ⟫[ q ] g
⟫[]-replace {p = P.refl} P.refl = refl


-- With ⟫[-cong and ⟫]-cong we can convert ⟫ to and from ⟫[]. In between we can use ⟫[]-cong
-- for operations where we keep the ⟫[].
-- The definitions are picked in such a way that the proofs for ⟫[] are created with the information
-- on the left hand side of the ≈⟦⟧-equalities.

abstract
  ⟫[-cong-proof : ∀ {i₁ m₁ o₁} {f₁ : ℂ i₁ m₁} {g₁ : ℂ m₁ o₁} →
                  ∀ {i₂ m₂ n₂ o₂} {f₂ : ℂ i₂ m₂} {g₂ : ℂ n₂ o₂} →
                  (f≈f : f₁ ≈⟦⟧ f₂) → (g≈g : g₁ ≈⟦⟧ g₂) →
                  m₂ ≡ n₂
  ⟫[-cong-proof f≈f g≈g = P.sym (o-equal f≈f) ⟨ P.trans ⟩ i-equal g≈g

            
  _⟫[-cong_ : ∀ {i₁ m₁ o₁} {f₁ : ℂ i₁ m₁} {g₁ : ℂ m₁ o₁} →
              ∀ {i₂ m₂ n₂ o₂} {f₂ : ℂ i₂ m₂} {g₂ : ℂ n₂ o₂} →
              (f≈f : f₁ ≈⟦⟧ f₂) → (g≈g : g₁ ≈⟦⟧ g₂) →
              f₁ ⟫ g₁ ≈⟦⟧ _⟫[]_ f₂ {⟫[-cong-proof f≈f g≈g} g₂
  f≈f ⟫[-cong g≈g = f≈f ⟫[-cong′ g≈g
    where
    _⟫[-cong′_ : ∀ {i₁ m₁ o₁} {f₁ : ℂ i₁ m₁} {g₁ : ℂ m₁ o₁} →
                ∀ {i₂ m₂ n₂ o₂} {f₂ : ℂ i₂ m₂} {p₂ : m₂ ≡ n₂} {g₂ : ℂ n₂ o₂} →
                (f≈f : f₁ ≈⟦⟧ f₂) → (g≈g : g₁ ≈⟦⟧ g₂) →
                f₁ ⟫ g₁ ≈⟦⟧ f₂ ⟫[ p₂ ] g₂
    _⟫[-cong′_ {p₂ = P.refl} f≈f g≈g = (f≈f ⟨ trans ⟩ sym (⟫-right-identity _)) ⟫-cong g≈g
                              ⟨ trans ⟩ sym reveal-⟫[]

-- Proof for RHS is generated from the LHS (thus from p₁).
-- We prefer to use the implicit variant of ⟫[] for the RHS, because we don't
-- want the proof to always show up in goals.
abstract
  ⟫[]-cong-proof : ∀ {i₁ m₁ n₁ o₁} {f₁ : ℂ i₁ m₁} (p₁ : m₁ ≡ n₁) {g₁ : ℂ n₁ o₁} →
                   ∀ {i₂ m₂ n₂ o₂} {f₂ : ℂ i₂ m₂} {g₂ : ℂ n₂ o₂} →
                   (f≈f : f₁ ≈⟦⟧ f₂) → (g≈g : g₁ ≈⟦⟧ g₂) →
                   m₂ ≡ n₂
  ⟫[]-cong-proof p₁ f≈f g≈g = P.sym (o-equal f≈f) ⟨ P.trans ⟩ p₁ ⟨ P.trans ⟩ i-equal g≈g

  _⟫[]-cong_ : ∀ {i₁ m₁ n₁ o₁} {f₁ : ℂ i₁ m₁} {p₁ : m₁ ≡ n₁} {g₁ : ℂ n₁ o₁} →
               ∀ {i₂ m₂ n₂ o₂} {f₂ : ℂ i₂ m₂} {g₂ : ℂ n₂ o₂} →
               (f≈f : f₁ ≈⟦⟧ f₂) → (g≈g : g₁ ≈⟦⟧ g₂) →
               f₁ ⟫[ p₁ ] g₁ ≈⟦⟧ _⟫[]_ f₂ {⟫[]-cong-proof p₁ f≈f g≈g} g₂
  _⟫[]-cong_ {p₁ = P.refl} f≈f g≈g with o-equal f≈f | i-equal g≈g | ⟫[]-cong-proof P.refl f≈f g≈g
  _⟫[]-cong_ {p₁ = P.refl} f≈f g≈g | P.refl | P.refl | P.refl = reveal-⟫[]
                                     ⟨ trans ⟩ f≈f ⟫-cong refl ⟫-cong g≈g
                                     ⟨ trans ⟩ sym reveal-⟫[]

  _⟫]-cong_ : ∀ {i₁ m₁ n₁ o₁} {f₁ : ℂ i₁ m₁} {p₁ : m₁ ≡ n₁} {g₁ : ℂ n₁ o₁} →
              ∀ {i₂ m₂ o₂} {f₂ : ℂ i₂ m₂} {g₂ : ℂ m₂ o₂} →
              (f≈f : f₁ ≈⟦⟧ f₂) → (g≈g : g₁ ≈⟦⟧ g₂) →
              f₁ ⟫[ p₁ ] g₁ ≈⟦⟧ f₂ ⟫ g₂
  _⟫]-cong_ {p₁ = P.refl} f≈f g≈g = reveal-⟫[]
                           ⟨ trans ⟩ (⟫-right-identity _ ⟨ trans ⟩ f≈f) ⟫-cong g≈g

-- Most of the laws for ⟫ also hold for ⟫[]
abstract
  ⟫[]-right-identity : ∀ {i m o} (f : ℂ i m) {p : m ≡ o} → _⟫[]_ f {p} id⤨ ≈⟦⟧ f
  ⟫[]-right-identity f {P.refl} = ⟫[]-to-⟫
                        ⟨ trans ⟩ ⟫-right-identity f
  
  ⟫[]-left-identity : ∀ {i m o} {p : i ≡ m} (f : ℂ m o) → _⟫[]_ id⤨ {p} f ≈⟦⟧ f
  ⟫[]-left-identity {p = P.refl} f = ⟫[]-to-⟫
                           ⟨ trans ⟩ ⟫-left-identity f

  ⟫[]-assoc : ∀ {i j k m n o} (f : ℂ i j) {p : j ≡ k} (g : ℂ k m) {q : m ≡ n} (h : ℂ n o) →
              _⟫[]_ (_⟫[]_ f {p} g) {q} h ≈⟦⟧ _⟫[]_ f {p} (_⟫[]_ g {q} h)
  ⟫[]-assoc f {P.refl} g {P.refl} h = ⟫[]-to-⟫
                             ⟨ trans ⟩ ⟫[]-to-⟫ ⟫-cong refl
                             ⟨ trans ⟩ ⟫-assoc _ _ _
                             ⟨ trans ⟩ sym (refl ⟫-cong ⟫[]-to-⟫)
                             ⟨ trans ⟩ sym ⟫[]-to-⟫

postulate
  ⟫[]-∥-distrib′ : ∀ {i₁ m₁ n₁ o₁ i₂ m₂ n₂ o₂} (f₁ : ℂ i₁ m₁) (g₁ : ℂ n₁ o₁) (f₂ : ℂ i₂ m₂) (g₂ : ℂ n₂ o₂) →
                {p : m₁ + m₂ ≡ n₁ + n₂} {q₁ : m₁ ≡ n₁} {q₂ : m₂ ≡ n₂} →
                (f₁ ∥ f₂) ⟫[ p ] (g₁ ∥ g₂) ≈⟦⟧ (f₁ ⟫[ q₁ ] g₁) ∥ (f₂ ⟫[ q₂ ] g₂)

abstract
  -- For this direction we can't generate the proofs automatically
  ⟫[]-∥-distrib : ∀ {i₁ m₁ n₁ o₁ i₂ m₂ n₂ o₂} →
     {f₁ : ℂ i₁ m₁} {g₁ : ℂ n₁ o₁} {f₂ : ℂ i₂ m₂} {g₂ : ℂ n₂ o₂} →
     {p : m₁ + m₂ ≡ n₁ + n₂} (q₁ : m₁ ≡ n₁) (q₂ : m₂ ≡ n₂) →
     (f₁ ∥ f₂) ⟫[ p ] (g₁ ∥ g₂) ≈⟦⟧ (f₁ ⟫[ q₁ ] g₁) ∥ (f₂ ⟫[ q₂ ] g₂)
  ⟫[]-∥-distrib q₁ q₂ = ⟫[]-∥-distrib′ _ _ _ _

  -- In this direction we can generate the proofs
  ⟫[]-∥-distribᵣ : ∀ {i₁ m₁ n₁ o₁ i₂ m₂ n₂ o₂} →
    {f₁ : ℂ i₁ m₁} {g₁ : ℂ n₁ o₁} {f₂ : ℂ i₂ m₂} {g₂ : ℂ n₂ o₂} →
    {q₁ : m₁ ≡ n₁} {q₂ : m₂ ≡ n₂} →
    (f₁ ⟫[ q₁ ] g₁) ∥ (f₂ ⟫[ q₂ ] g₂) ≈⟦⟧ _⟫[]_ (f₁ ∥ f₂) {P.cong₂ _+_ q₁ q₂} (g₁ ∥ g₂)
  ⟫[]-∥-distribᵣ = sym (⟫[]-∥-distrib′ _ _ _ _)

  ⟫[]-id⤨-left-distrib : ∀ {s i m n o} {f : ℂ i m} {g : ℂ n o} {p : m ≡ n} →
                          id⤨ {s} ∥ (f ⟫[ p ] g) ≈⟦⟧ _⟫[]_ (id⤨ {s} ∥ f) {P.cong (_+_ s) p} (id⤨ {s} ∥ g)
  ⟫[]-id⤨-left-distrib {s} {p = p} = sym (⟫[]-right-identity id⤨ {P.refl}) ∥-cong refl
                            ⟨ trans ⟩ ⟫[]-∥-distribᵣ
                            ⟨ trans ⟩ ⟫[]-replace _

  ⟫[]-id⤨-left-distribᵣ : ∀ {s i m n o} {f : ℂ i m} {g : ℂ n o} {p : s + m ≡ s + n} →
                          id⤨ {s} ∥ f ⟫[ p ] id⤨ {s} ∥ g ≈⟦⟧ id⤨ {s} ∥ _⟫[]_ f {cancel-+-left s p} g
  ⟫[]-id⤨-left-distribᵣ {s} {p = p} = ⟫[]-∥-distrib P.refl _
                             ⟨ trans ⟩ (⟫[]-right-identity id⤨) ∥-cong refl

  ⟫[]-id⤨-right-distrib : ∀ {s i m n o} {f : ℂ i m} {g : ℂ n o} {p : m ≡ n} →
                          let q = P.cong (flip _+_ s) p in
                          (f ⟫[ p ] g) ∥ id⤨ {s} ≈⟦⟧ _⟫[]_ (f ∥ id⤨ {s}) {q} (g ∥ id⤨ {s})
  ⟫[]-id⤨-right-distrib {s} {p = p} = refl ∥-cong sym (⟫[]-right-identity id⤨ {P.refl})
                             ⟨ trans ⟩ ⟫[]-∥-distribᵣ
                             ⟨ trans ⟩ ⟫[]-replace _

  ⟫[]-id⤨-right-distribᵣ : ∀ {s i m n o} {f : ℂ i m} {g : ℂ n o} {p : m + s ≡ n + s} →
    let q = cancel-+-left s (+-comm s _ ⟨ P.trans ⟩ p ⟨ P.trans ⟩ +-comm _ s) in
    f ∥ id⤨ {s} ⟫[ p ] g ∥ id⤨ {s} ≈⟦⟧ (_⟫[]_ f {q} g) ∥ id⤨ {s}
  ⟫[]-id⤨-right-distribᵣ {s} {p = p} = ⟫[]-∥-distrib _ P.refl
                              ⟨ trans ⟩ refl ∥-cong ⟫[]-right-identity id⤨
