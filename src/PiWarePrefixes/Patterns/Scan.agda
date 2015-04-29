open import PiWare.Atom using (Atomic; module Atomic)
open import PiWare.Gates using (Gates)
open import PiWarePrefixes.Circuit.Monoid using (module ℂ-Monoid; ℂ-Monoid)

module PiWarePrefixes.Patterns.Scan {At : Atomic} {Gt : Gates At} {ℂ-monoid : ℂ-Monoid {Gt = Gt}} where

open ℂ-Monoid ℂ-monoid using (plusℂ; plusℂ-assoc)

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties.Simple using (+-suc)
open import PiWare.Circuit {Gt = Gt} using (ℂ; 𝐂; _⟫_; _∥_)
open import PiWarePrefixes.Patterns.Fan {plusℂ = plusℂ}
open import PiWarePrefixes.Patterns.HetSeq {Gt = Gt}
open import PiWare.Plugs Gt using (id⤨)
open import Relation.Binary.PropositionalEquality as P

-- ▱ \paw
-- ⌷ \apl2

scan-succ : ∀ {n σω} → ℂ {σω} n n → ℂ {σω} (suc n) (suc n)
scan-succ {n} f = id⤨ {1} ∥ f ⟫ fan (suc n)

scan : ∀ n → 𝐂 n n
scan zero = id⤨ {0}
scan (suc n) = scan-succ (scan n)

_▱_ : ∀ {σω m n o p} (f : ℂ {σω} m (suc o)) (g : ℂ {σω} (suc n) p) →
         ℂ {σω} (m + n) (o + p)
_▱_ {n = n} {o} f g = f ∥ id⤨ {n} ⟫[ sym (+-suc o n) ] id⤨ {o} ∥ g

_⌷_ : ∀ {σω m n} (f : ℂ {σω} (suc m) (suc m)) (g : ℂ {σω} n n) →
         ℂ {σω} (suc m + n) (m + suc n)
_⌷_ {m = m} {n} f g = f ∥ g ⟫[ P.sym (+-suc m n) ] id⤨ {m} ∥ fan (suc n)
