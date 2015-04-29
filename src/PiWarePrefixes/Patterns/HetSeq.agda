open import PiWare.Atom using (Atomic; module Atomic)
open import PiWare.Gates using (Gates)

module PiWarePrefixes.Patterns.HetSeq {At : Atomic} {Gt : Gates At} where

open import PiWare.Circuit {Gt = Gt} using (ℂ; _⟫_; σ)
open import PiWarePrefixes.Plugs.Core {Gt = Gt} using (rewire⤨)
open import PiWarePrefixes.Simulation.Equality.Core {Gt = Gt} as SimEq
open import Relation.Binary.PropositionalEquality as P using (_≡_)

infixl 4 _⟫[_]-impl_  _⟫[_]_  _⟫[]_

-- _⟫[_]′_ : ∀ {i m n o σω} (f : ℂ {σω} i m) (p : m ≡ n) (g : ℂ {σω} n o) → ℂ {σω} i o
-- f ⟫[ p ]′ g = f ⟫ rewire⤨ p ⟫ g

_⟫[_]-impl_ : ∀ {i m n o σω} (f : ℂ {σω} i m) (p : m ≡ n) (g : ℂ {σω} n o) → ℂ {σω} i o
f ⟫[ p ]-impl g = f ⟫ rewire⤨ p ⟫ g

-- Hide the implementation of _⟫[_]_, so it won't be expanded in the goals. This
-- also prevents `f ⟫[ P.refl ] g` from reducing to `f ⟫ id⤨ ⟫ g`, which would
-- cause problems because the type checker does not realize that that can be
-- equal to `f ⟫ p ⟫ g‵ if you don't explicitly pass P.refl there.
abstract
  _⟫[_]_ : ∀ {i m n o σω} (f : ℂ {σω} i m) (p : m ≡ n) (g : ℂ {σω} n o) → ℂ {σω} i o
  f ⟫[ p ] g = f ⟫[ p ]-impl g

  reveal-⟫[] : ∀ {i m o} {f : ℂ i m} {g : ℂ m o} →
               f ⟫[ P.refl ] g ≈⟦⟧ f ⟫[ P.refl ]-impl g
  reveal-⟫[] = ≈⟦⟧-refl

_⟫[]_ : ∀ {i m n o σω} (f : ℂ {σω} i m) {p : m ≡ n} (g : ℂ {σω} n o) → ℂ {σω} i o
_⟫[]_ f {p} g = f ⟫[ p ] g
