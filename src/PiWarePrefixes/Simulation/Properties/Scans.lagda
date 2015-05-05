\begin{code}
open import PiWare.Atom using (Atomic; module Atomic)
open import PiWare.Gates using (Gates)
open import PiWarePrefixes.Circuit.Monoid using (module ℂ-Monoid; ℂ-Monoid)

module PiWarePrefixes.Simulation.Properties.Scans {At : Atomic} {Gt : Gates At}
                                                  {ℂ-monoid : ℂ-Monoid {Gt = Gt}} where

open Atomic At using (W)
open ℂ-Monoid ℂ-monoid using (plusℂ; plusℂ-assoc)

open import Data.Nat using (ℕ; zero; suc; _+_; pred)
open import Data.Nat.Properties using (cancel-+-left)
open import Data.Nat.Properties.Simple using (+-suc; +-comm; +-assoc)
open import Data.Vec using ([]; _∷_)
open import Function using (flip; _⟨_⟩_)
open import PiWare.Circuit {Gt = Gt} using (ℂ; 𝐂; Plug; _⟫_; _∥_; σ)
open import PiWarePrefixes.Patterns.Fan {plusℂ = plusℂ}
open import PiWarePrefixes.Patterns.HetSeq {Gt = Gt}
open import PiWarePrefixes.Patterns.Scan {ℂ-monoid = ℂ-monoid}
open import PiWare.Plugs Gt using (id⤨)
open import PiWarePrefixes.Plugs.Core {Gt = Gt} using (rewire⤨)
open import PiWare.Simulation Gt using (⟦_⟧)
open import PiWarePrefixes.Simulation.Equality.Core {Gt = Gt} as SimEq
  renaming (≈⟦⟧-refl to refl; ≈⟦⟧-sym to sym; ≈⟦⟧-trans to trans)
open import PiWarePrefixes.Simulation.Properties {Gt = Gt}
open import PiWarePrefixes.Simulation.Properties.HetSeq {Gt = Gt}
open import PiWarePrefixes.Simulation.Properties.Fans {plusℂ = plusℂ} as FanProps
open FanProps.WithAssociativity {plusℂ-assoc = plusℂ-assoc}
open import Relation.Binary.PropositionalEquality as P using (_≡_; cong)

open SimEq.≈⟦⟧-Reasoning

scan-cong : ∀ {m n} (p : m ≡ n) → scan m ≈⟦⟧ scan n
scan-cong P.refl = refl

scan-succ-cong : ∀ {m n} {f : ℂ m m} {g : ℂ n n} (f≈g : f ≈⟦⟧ g) →
                 scan-succ f ≈⟦⟧ scan-succ g
scan-succ-cong f≈g = (refl ∥-cong f≈g) ⟫-cong (fan-cong (cong suc (i-equal f≈g)))

scan-to-spec : ∀ n (w : W n) → ⟦ scan n ⟧ w ≡ scan-spec w
scan-to-spec zero [] = P.refl
scan-to-spec (suc n) (x ∷ xs) rewrite fan-to-spec (suc n) (x ∷ ⟦ scan n ⟧ xs)
                                    | scan-to-spec n xs = P.refl

scan1-id : scan 1 ≈⟦⟧ id⤨
scan1-id = ∥-id⤨ ⟫-cong fan1-id ⟨ trans ⟩ ⟫-right-identity id⤨


_▱-cong_ : ∀ {m₁ n₁ o₁ p₁} {f₁ : ℂ m₁ (suc o₁)} {g₁ : ℂ (suc n₁) p₁} →
           ∀ {m₂ n₂ o₂ p₂} {f₂ : ℂ m₂ (suc o₂)} {g₂ : ℂ (suc n₂) p₂} →
           f₁ ≈⟦⟧ f₂ → g₁ ≈⟦⟧ g₂ → f₁ ▱ g₁ ≈⟦⟧ f₂ ▱ g₂
_▱-cong_ {f₁ = f₁} {g₁} {f₂ = f₂} {g₂} f≈f g≈g = begin
  f₁ ▱ g₁
    ≈⟦⟧⟨⟩
  f₁ ∥ id⤨ ⟫[] id⤨ ∥ g₁
    ≈⟦⟧⟨           (f≈f ∥-cong id⤨-cong (cong pred (i-equal g≈g)))
         ⟫[]-cong (id⤨-cong (cong pred (o-equal f≈f)) ∥-cong g≈g) ⟩
  f₂ ∥ id⤨ ⟫[] id⤨ ∥ g₂
    ≈⟦⟧⟨ ⟫[]-replace _ ⟩
  f₂ ∥ id⤨ ⟫[] id⤨ ∥ g₂
    ≈⟦⟧⟨⟩
  f₂ ▱ g₂
    ∎

▱-left-identity : ∀ {n o} (f : ℂ (suc n) (suc o)) → id⤨ {1} ▱ f ≈⟦⟧ f
▱-left-identity {n} {o} f = begin
  id⤨ {1} ▱ f
    ≈⟦⟧⟨ ⟫[]-to-⟫ ⟩
  id⤨ {1} ∥ id⤨ {n} ⟫ id⤨ {0} ∥ f
    ≈⟦⟧⟨ ∥-id⤨ ⟫-cong (∥-left-identity f) ⟩
  id⤨ ⟫ f
    ≈⟦⟧⟨ ⟫-left-identity f ⟩
  f
    ∎

▱-right-identity : ∀ {n o} (f : ℂ (suc n) (suc o)) → f ▱ id⤨ {1} ≈⟦⟧ f
▱-right-identity {n} {o} f = begin
  f ▱ id⤨ {1}
    ≈⟦⟧⟨⟩
  f ∥ id⤨ {0} ⟫[] id⤨ {o} ∥ id⤨ {1}
    ≈⟦⟧⟨ (∥-right-identity f) ⟫[]-cong ∥-id⤨ ⟩
  f ⟫[] id⤨
    ≈⟦⟧⟨ ⟫[]-right-identity f ⟩
  f
    ∎

⌷-▱ : ∀ {m n} (f : ℂ (suc m) (suc m)) (g : ℂ (n) (n)) → f ⌷ g ≈⟦⟧ f ▱ scan-succ g
⌷-▱ {m} {n} f g = begin
  f ⌷ g
    ≈⟦⟧⟨⟩
  f ∥ g ⟫[] id⤨ ∥ fan (suc n)
    ≈⟦⟧⟨ (lem₁ ⟨ trans ⟩ refl ⟫[-cong refl) ⟫[]-cong refl ⟩
  f ∥ id⤨ ⟫[] id⤨ {suc m} ∥ g ⟫[] id⤨ ∥ fan (suc n)
    ≈⟦⟧⟨ (refl ⟫[]-cong ((id⤨-cong (+-comm 1 m)) ∥-cong refl)) ⟫[]-cong refl ⟩
  f ∥ id⤨ {n} ⟫[] id⤨ {m + 1} ∥ g ⟫[] id⤨ ∥ fan (suc n)
    ≈⟦⟧⟨ ⟫[]-assoc _ _ _ ⟨ trans ⟩ refl ⟫[]-cong lem₂ ⟩
  f ∥ id⤨ ⟫[] id⤨ ∥ (id⤨ {1} ∥ g ⟫ fan (suc n))
    ≈⟦⟧⟨⟩
  f ∥ id⤨ ⟫[] id⤨ ∥ scan-succ g
    ≈⟦⟧⟨ ⟫[]-replace _ ⟩
  f ▱ scan-succ g
    ∎
  where
  lem₁ : f ∥ g ≈⟦⟧ f ∥ id⤨ {n} ⟫ id⤨ {suc m} ∥ g
  lem₁ = (sym (⟫-right-identity f)) ∥-cong (sym (⟫-left-identity g))
    ⟨ trans ⟩ sym (⟫-∥-distrib _ _ _ _)
  lem₂ : id⤨ {m + 1} ∥ g ⟫[] id⤨ ∥ fan (suc n)
     ≈⟦⟧ id⤨ {m} ∥ (id⤨ {1} ∥ g ⟫ fan (suc n))
  lem₂ = begin
    id⤨ {m + 1} ∥ g ⟫[] id⤨ ∥ fan (suc n)
      ≈⟦⟧⟨ (sym ∥-id⤨ ∥-cong refl) ⟫[]-cong refl ⟩
    (id⤨ ∥ id⤨) ∥ g ⟫[] id⤨ ∥ fan (suc n)
      ≈⟦⟧⟨ ∥-assoc _ _ _ ⟫[]-cong refl ⟩
    id⤨ ∥ id⤨ ∥ g ⟫[] id⤨ ∥ fan (suc n)
      ≈⟦⟧⟨ ⟫[]-∥-distrib P.refl P.refl ⟩
    (id⤨ ⟫[] id⤨) ∥ (id⤨ ∥ g ⟫[] fan (suc n))
      ≈⟦⟧⟨ (⟫[]-right-identity id⤨) ∥-cong ⟫[]-to-⟫ ⟩
    id⤨ ∥ (id⤨ ∥ g ⟫ fan (suc n))
      ∎

_⌷-cong_ : ∀ {m₁ n₁} {f₁ : ℂ (suc m₁) (suc m₁)} {g₁ : ℂ n₁ n₁} →
           ∀ {m₂ n₂} {f₂ : ℂ (suc m₂) (suc m₂)} {g₂ : ℂ n₂ n₂} →
           f₁ ≈⟦⟧ f₂ → g₁ ≈⟦⟧ g₂ → f₁ ⌷ g₁ ≈⟦⟧ f₂ ⌷ g₂
_⌷-cong_ {f₁ = f₁} {g₁} {f₂ = f₂} {g₂} f≈f g≈g = begin
  f₁ ⌷ g₁
    ≈⟦⟧⟨ ⌷-▱ f₁ g₁ ⟩
  f₁ ▱ scan-succ g₁
    ≈⟦⟧⟨ f≈f ▱-cong (scan-succ-cong g≈g) ⟩
  f₂ ▱ scan-succ g₂
    ≈⟦⟧⟨ sym (⌷-▱ f₂ g₂) ⟩
  f₂ ⌷ g₂
    ∎

⌷-right-identity : ∀ {n} (f : ℂ (suc n) (suc n)) → f ⌷ id⤨ {0} ≈⟦⟧ f
⌷-right-identity f = begin
  f ⌷ id⤨ {0}
    ≈⟦⟧⟨ ⌷-▱ f (id⤨ {0}) ⟩
  f ▱ scan 1
    ≈⟦⟧⟨ refl ▱-cong scan1-id ⟩
  f ▱ id⤨
    ≈⟦⟧⟨ ▱-right-identity f ⟩
  f
    ∎
\end{code}
