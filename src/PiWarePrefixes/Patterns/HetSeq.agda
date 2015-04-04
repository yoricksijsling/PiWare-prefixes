open import PiWare.Atom using (Atomic; module Atomic)
open import PiWare.Gates using (Gates)

module PiWarePrefixes.Patterns.HetSeq {At : Atomic} (Gt : Gates At) where

open import PiWare.Circuit Gt using (ℂ; _⟫_)
open import PiWarePrefixes.Plugs.Core Gt using (rewire⤨)
open import Relation.Binary.PropositionalEquality as P using (_≡_)

infixl 4 _⟫[_]_

_⟫[_]_ : ∀ {i m n o σω} (f : ℂ {σω} i m) (p : m ≡ n) (g : ℂ {σω} n o) → ℂ {σω} i o
f ⟫[ p ] g = f ⟫ rewire⤨ p ⟫ g

infixl 4 _⟫[]_

_⟫[]_ : ∀ {i m n o σω} (f : ℂ {σω} i m) {p : m ≡ n} (g : ℂ {σω} n o) → ℂ {σω} i o
_⟫[]_ f {p} g = f ⟫[ p ] g
