open import PiWare.Atom using (Atomic)
open import PiWare.Gates using (Gates)

module PiWarePrefixes.Circuit.Core {At : Atomic} (Gt : Gates At) where

open import Data.Nat
open import Data.Product

open import PiWare.Circuit.Core Gt

-- Combinational circuits
combℂ' : ℕ → ℕ → Set
combℂ' i o = Σ (ℂ' i o) comb'
