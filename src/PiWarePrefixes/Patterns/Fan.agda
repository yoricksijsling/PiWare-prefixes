module PiWarePrefixes.Patterns.Fan where

open import PiWare.Atom using (Atomic; module Atomic)
open import PiWare.Gates using (Gates)
open import PiWarePrefixes.Atom.Int8 using (Atomic-Int8)
open import PiWarePrefixes.Gates.Plus using (Plus; Plus#; _+m_)

At : Atomic
At = Atomic-Int8

Gt : Gates At
Gt = Plus

open import Data.Nat using (zero; suc; _+_)
open import Data.Nat.Properties.Simple using (+-right-identity; *-comm)
open import Data.Vec using ([]; _∷_) renaming (map to mapᵥ)
open import PiWare.Circuit Gt using (ℂ; 𝐂; Gate; _⟫_; _∥_)
-- open import PiWarePrefixes.Patterns.Core Gt using (zipWith)
open import PiWare.Plugs Gt using (forkVec⤨; id⤨)
open import PiWare.Simulation Gt using (⟦_⟧)

open Atomic At using (Atom; W)

private
  plusℂ : 𝐂 2 1
  plusℂ = Gate Plus#

  _⊕_ : Atom → Atom → Atom
  _⊕_ = _+m_

postulate
  fan : ∀ n → 𝐂 n n
{-
fan : ∀ n → 𝐂 n n
fan zero = Nil
fan (suc n) {p} with zipWith {2} {n} {p} plusℂ
fan (suc n) | z rewrite (+-right-identity) n = forkFirst⤨ ⟫ id⤨ {1} ∥ z
  where
  fork1 : ∀ k → 𝐂 1 k
  fork1 k {p} with forkVec⤨ {k} {1} {p}
  fork1 k | forked rewrite *-comm k 1 | +-right-identity k = forked

  forkFirst⤨ : ∀ {n} → 𝐂 (suc n) (suc (n + n))
  forkFirst⤨ {n} = fork1 (suc n) ∥ (id⤨ {n})
-}

fan-spec : ∀ {n} → W n → W n
fan-spec [] = []
fan-spec (x ∷ xs) = x ∷ mapᵥ (_⊕_ x) xs

