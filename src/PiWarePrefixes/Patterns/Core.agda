open import PiWare.Atom using (Atomic)
open import PiWare.Gates using (Gates)

module PiWarePrefixes.Patterns.Core {At : Atomic} (Gt : Gates At) where

open import Data.Nat using (_*_)

open import PiWare.Circuit.Core Gt using (ℂ'; _⟫'_)
open import PiWare.Patterns.Core Gt using (parsN')
open import PiWarePrefixes.Plugs.Core Gt using (pZip')

open import Data.Nat.Properties.Simple using (+-right-identity; *-comm)

zipWith' : ∀ {k n} → ℂ' k 1 → ℂ' (k * n) (1 * n)
zipWith' {k} {n} f with (pZip' {k} {n} ⟫' parsN' {n} f)
zipWith' {k} {n} f | z rewrite *-comm n 1 | +-right-identity n = z
