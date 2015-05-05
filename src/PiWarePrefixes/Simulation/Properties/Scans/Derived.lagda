\begin{code}
open import PiWare.Atom using (Atomic; module Atomic)
open import PiWare.Gates using (Gates)
open import PiWarePrefixes.Circuit.Monoid using (module ℂ-Monoid; ℂ-Monoid)

module PiWarePrefixes.Simulation.Properties.Scans.Derived {At : Atomic} {Gt : Gates At}
                                                          {ℂ-monoid : ℂ-Monoid {Gt = Gt}} where

open ℂ-Monoid ℂ-monoid using (plusℂ; plusℂ-assoc)

open import Data.Nat using (ℕ; zero; suc; _+_; pred)
open import Data.Nat.Properties using (cancel-+-left)
open import Data.Nat.Properties.Simple using (+-suc; +-comm; +-assoc)
open import Function using (flip; _⟨_⟩_)
open import PiWare.Circuit {Gt = Gt} using (ℂ; 𝐂; Plug; _⟫_; _∥_; σ)
open import PiWarePrefixes.Patterns.Fan {plusℂ = plusℂ}
open import PiWarePrefixes.Patterns.HetSeq {Gt = Gt}
open import PiWarePrefixes.Patterns.Scan {ℂ-monoid = ℂ-monoid}
open import PiWare.Plugs Gt using (id⤨)
open import PiWarePrefixes.Plugs.Core {Gt = Gt} using (rewire⤨)
open import PiWarePrefixes.Simulation.Equality.Core {Gt = Gt} as SimEq
  renaming (≈⟦⟧-refl to refl; ≈⟦⟧-sym to sym; ≈⟦⟧-trans to trans)
open import PiWarePrefixes.Simulation.Properties {Gt = Gt}
open import PiWarePrefixes.Simulation.Properties.HetSeq {Gt = Gt}
open import PiWarePrefixes.Simulation.Properties.Fans {plusℂ = plusℂ} as FanProps
open import PiWarePrefixes.Simulation.Properties.Scans {ℂ-monoid = ℂ-monoid}
open import PiWarePrefixes.Simulation.Properties.Scans.SuccProp {ℂ-monoid = ℂ-monoid} using (▱-scan-succ)
open FanProps.WithAssociativity {plusℂ-assoc = plusℂ-assoc}
open import Relation.Binary.PropositionalEquality as P using (_≡_; cong)

open SimEq.≈⟦⟧-Reasoning

▱-assoc : ∀ {l m n} (f : ℂ (suc l) (suc l)) (g : ℂ (suc m) (suc m)) (h : ℂ (suc n) (suc n)) →
          f ▱ (g ▱ h) ≈⟦⟧ (f ▱ g ⟫[ +-suc l m ] id⤨) ▱ h
▱-assoc {l} {m} {n} f g h = begin
  f ▱ (g ▱ h)
    ≈⟦⟧⟨⟩
  f ∥ id⤨ {m + n} ⟫[] id⤨ {l} ∥ (g ▱ h)
    ≈⟦⟧⟨⟩
  f ∥ id⤨ {m + n} ⟫[] id⤨ {l} ∥ (g ∥ id⤨ {n} ⟫[] id⤨ {m} ∥ h)
    ≈⟦⟧⟨ refl ⟫[]-cong ((sym (⟫[]-right-identity id⤨)) ∥-cong refl) ⟩
  f ∥ id⤨ {m + n} ⟫[] (id⤨ {l} ⟫[ P.refl ] id⤨ {l}) ∥ (g ∥ id⤨ {n} ⟫[] id⤨ {m} ∥ h)
    ≈⟦⟧⟨ refl ⟫[]-cong ⟫[]-∥-distribᵣ ⟩
  f ∥ id⤨ {m + n} ⟫[] (id⤨ {l} ∥ g ∥ id⤨ {n} ⟫[] id⤨ {l} ∥ id⤨ {m} ∥ h)
    ≈⟦⟧⟨ lem ⟩
  ((f ∥ id⤨ {m} ⟫[] id⤨ {l} ∥ g) ⟫[ +-suc l m ] id⤨ {suc (l + m)}) ∥ id⤨ {n} ⟫[] id⤨ {l + m} ∥ h
    ≈⟦⟧⟨⟩
  (f ▱ g ⟫[ +-suc l m ] id⤨) ∥ id⤨ {n} ⟫[] id⤨ {l + m} ∥ h
    ≈⟦⟧⟨⟩
  (f ▱ g ⟫[ +-suc l m ] id⤨) ▱ h
    ∎
  where
  postulate
    lem : f ∥ id⤨ {m + n} ⟫[] (id⤨ {l} ∥ g ∥ id⤨ {n} ⟫[] id⤨ {l} ∥ id⤨ {m} ∥ h)
      ≈⟦⟧ ((f ∥ id⤨ {m} ⟫[] id⤨ {l} ∥ g) ⟫[ +-suc l m ] id⤨ {suc (l + m)}) ∥ id⤨ {n} ⟫[] id⤨ {l + m} ∥ h

⌷-assoc : ∀ {l m n} (f : ℂ (suc l) (suc l)) (g : ℂ (suc m) (suc m)) (h : ℂ n n) →
          f ⌷ (g ⌷ h ⟫[ +-suc m n ] id⤨) ≈⟦⟧ (f ⌷ g ⟫[ +-suc l (suc m) ] id⤨) ⌷ h
⌷-assoc {l} {m} {n} f g h = begin
  f ⌷ (g ⌷ h ⟫[] id⤨)
    ≈⟦⟧⟨ refl ⌷-cong ((⌷-▱ _ _) ⟫[]-cong refl) ⟩
  f ⌷ (g ▱ scan-succ h ⟫[] id⤨)
    ≈⟦⟧⟨ ⌷-▱ f _ ⟩
  f ▱ scan-succ (g ▱ scan-succ h ⟫[] id⤨)
    ≈⟦⟧⟨ refl ▱-cong ▱-scan-succ g h ⟩
  f ▱ (scan-succ g ▱ scan-succ h)
    ≈⟦⟧⟨ ▱-assoc f (scan-succ g) (scan-succ h) ⟩
  (f ▱ scan-succ g ⟫[] id⤨) ▱ scan-succ h
    ≈⟦⟧⟨ sym (⌷-▱ _ _) ⟩
  (f ▱ scan-succ g ⟫[] id⤨) ⌷ h
    ≈⟦⟧⟨ (sym (⌷-▱ _ _) ⟫[]-cong refl) ⌷-cong refl ⟩
  (f ⌷ g ⟫[] id⤨) ⌷ h
    ≈⟦⟧⟨ (⟫[]-replace _) ⌷-cong refl ⟩
  (f ⌷ g ⟫[] id⤨) ⌷ h
    ∎


-- When you combine two scans, the result is also a scan.

▱-combinator : ∀ m n → scan (suc m) ▱ scan (suc n) ≈⟦⟧ scan (m + suc n)
▱-combinator zero n = begin
  scan 1 ▱ scan (suc n)
    ≈⟦⟧⟨ scan1-id ▱-cong refl ⟩
  id⤨ ▱ scan (suc n)
    ≈⟦⟧⟨ ▱-left-identity _ ⟩
  scan (suc n)
    ∎
▱-combinator (suc m) n = begin
  scan (2 + m) ▱ scan (suc n)
    ≈⟦⟧⟨⟩
  scan-succ (scan (suc m)) ▱ scan (suc n)
    ≈⟦⟧⟨ sym (▱-scan-succ (scan (suc m)) (scan n)) ⟩
  scan-succ (scan (suc m) ▱ scan (suc n) ⟫[ +-suc m n ] id⤨)
    ≈⟦⟧⟨ scan-succ-cong (▱-combinator m n ⟫]-cong id⤨-cong (P.sym (+-suc m n))) ⟩
  scan-succ (scan (m + suc n) ⟫ id⤨)
    ≈⟦⟧⟨ scan-succ-cong (⟫-right-identity _) ⟩
  scan-succ (scan (m + suc n))
    ≈⟦⟧⟨⟩
  scan (suc m + suc n)
    ∎

⌷-combinator : ∀ m n → scan (suc m) ⌷ scan n ≈⟦⟧ scan (suc m + n)
⌷-combinator m n = begin
  scan (suc m) ⌷ scan n
    ≈⟦⟧⟨ ⌷-▱ (scan (suc m)) (scan n) ⟩
  scan (suc m) ▱ scan (suc n)
    ≈⟦⟧⟨ ▱-combinator m n ⟩
  scan (m + suc n)
    ≈⟦⟧⟨ scan-cong (+-suc m n) ⟩
  scan (suc m + n)
    ∎

--------------------------------------------------------------------------------
-- Serial scans are scans

serial-scan : ∀ n → 𝐂 n n
serial-scan 0 = id⤨
serial-scan 1 = id⤨
serial-scan (suc (suc n)) = id⤨ ⟫[ P.cong suc (+-comm 1 n) ] serial-scan (suc n) ⌷ id⤨ {1} ⟫[ +-comm n 2 ] id⤨

serial-scan-is-scan : ∀ n → serial-scan n ≈⟦⟧ scan n
serial-scan-is-scan 0 = refl
serial-scan-is-scan 1 = sym scan1-id
serial-scan-is-scan (suc (suc n)) = begin
  serial-scan (2 + n)
    ≈⟦⟧⟨ refl ⟩
  id⤨ ⟫[] serial-scan (suc n) ⌷ id⤨ {1} ⟫[] id⤨
    ≈⟦⟧⟨ ⟫[]-right-identity _ ⟩
  id⤨ ⟫[] serial-scan (suc n) ⌷ id⤨ {1}
    ≈⟦⟧⟨ ⟫[]-left-identity _ ⟩
  serial-scan (suc n) ⌷ id⤨ {1}
    ≈⟦⟧⟨ (serial-scan-is-scan (suc n)) ⌷-cong (sym scan1-id) ⟩
  scan (suc n) ⌷ scan 1
    ≈⟦⟧⟨ ⌷-combinator n 1 ⟩
  scan (suc n + 1)
    ≈⟦⟧⟨ scan-cong (cong suc (+-comm n 1)) ⟩
  scan (2 + n)
    ∎

--------------------------------------------------------------------------------
-- Fibonacci scans are scans

fib : ℕ → ℕ
fib zero = 0
fib (suc zero) = 1
fib (suc (suc n)) = fib (suc n) + fib n

fib-is-suc : ∀ n → fib (suc n) ≡ suc (pred (fib (suc n)))
fib-is-suc zero = P.refl
fib-is-suc (suc n) = cong (flip _+_ (fib n)) (fib-is-suc n)
         ⟨ P.trans ⟩ lem (fib-is-suc n)
  where
  lem : ∀ {x y z} → x ≡ suc z → suc (pred x) + y ≡ suc (pred (x + y))
  lem p rewrite p = P.refl

fib-scan : ∀ n → 𝐂 (fib n) (fib n)
fib-scan zero = id⤨
fib-scan (suc zero) = id⤨
fib-scan (suc (suc n)) = id⤨ ⟫[ p ] (id⤨ ⟫[ P.sym (fib-is-suc n) ] fib-scan (suc n) ⟫[ fib-is-suc n ] id⤨) ⌷ fib-scan n ⟫[ q ] id⤨
  where
  p : fib (suc n) + fib n ≡ suc (pred (fib (suc n))) + fib n
  p = cong (flip _+_ (fib n)) (fib-is-suc n)
  q : pred (fib (suc n)) + suc (fib n) ≡ fib (suc n) + fib n
  q = +-suc (pred (fib (suc n))) (fib n) ⟨ P.trans ⟩ P.sym p

fib-scan-is-scan : ∀ n → fib-scan n ≈⟦⟧ scan (fib n)
fib-scan-is-scan 0 = refl
fib-scan-is-scan 1 = sym scan1-id
fib-scan-is-scan (suc (suc n)) = begin
  fib-scan (2 + n)
    ≈⟦⟧⟨ refl ⟩
  id⤨ ⟫[] (id⤨ ⟫[] fib-scan (suc n) ⟫[] id⤨) ⌷ fib-scan n ⟫[] id⤨
    ≈⟦⟧⟨ ⟫[]-right-identity _ ⟩
  id⤨ ⟫[] (id⤨ ⟫[] fib-scan (suc n) ⟫[] id⤨) ⌷ fib-scan n
    ≈⟦⟧⟨ ⟫[]-left-identity _ ⟩
  (id⤨ ⟫[] fib-scan (suc n) ⟫[] id⤨) ⌷ fib-scan n
    ≈⟦⟧⟨ (⟫[]-right-identity _ ⟨ trans ⟩ ⟫[]-left-identity _ ⟨ trans ⟩ fib-scan-is-scan (suc n) ⟨ trans ⟩ scan-cong (fib-is-suc n)) ⌷-cong (fib-scan-is-scan n) ⟩
  scan (suc (pred (fib (suc n)))) ⌷ scan (fib n)
    ≈⟦⟧⟨ ⌷-combinator (pred (fib (suc n))) (fib n) ⟩
  scan (suc (pred (fib (suc n)) + fib n))
    ≈⟦⟧⟨ scan-cong (cong (flip _+_ (fib n)) (P.sym (fib-is-suc n))) ⟩
  scan (fib (2 + n))
    ∎
\end{code}
