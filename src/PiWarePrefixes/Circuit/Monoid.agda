open import PiWare.Atom using (Atomic; module Atomic)
open import PiWare.Gates using (Gates)

module PiWarePrefixes.Circuit.Monoid {At : Atomic} {Gt : Gates At} where

open import PiWare.Circuit {Gt = Gt}
open import PiWare.Plugs Gt using (id⤨)
open import PiWarePrefixes.Simulation.Equality.Core {Gt = Gt}

Plusℂ : Set
Plusℂ = 𝐂 2 1

Plusℂ-Assoc : (plusℂ : Plusℂ) → Set
Plusℂ-Assoc plusℂ = plusℂ ∥ id⤨ {1} ⟫ plusℂ ≈⟦⟧ id⤨ {1} ∥ plusℂ ⟫ plusℂ

record ℂ-Monoid : Set where
  field
    plusℂ : Plusℂ
    plusℂ-assoc : Plusℂ-Assoc plusℂ
