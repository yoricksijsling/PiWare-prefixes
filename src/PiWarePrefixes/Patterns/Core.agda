open import PiWare.Atom using (Atomic; module Atomic)
open import PiWare.Gates using (Gates)

module PiWarePrefixes.Patterns.Core {At : Atomic} (Gt : Gates At) where

open import Data.Fin as Fin using (Fin)
open import Data.Nat using (ℕ; zero; suc; _*_; _+_)
open import Data.Nat.Properties.Simple using (+-right-identity; *-comm)
open import Data.Product renaming (map to map×)
open import Data.Vec hiding (zipWith) renaming (map to mapᵥ)
open import Function using (id; _$_; _∘_; flip)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; cong₂)

open import PiWare.Circuit {Gt = Gt} using (ℂ; 𝐂; Plug; _⟫_; _∥_)
open import PiWare.Interface using (Ix)
open import PiWare.Patterns Gt using (parsN)
open import PiWare.Plugs Gt using (id⤨)

open Atomic At using (W; Atom)

{-
zipWith : ∀ {k n cs} → ℂ {cs} k 1 → ℂ {cs} (k * n) (1 * n)
zipWith {k} {n} f with (zip⤨ {k} {n} ⟫ parsN {n} f)
zipWith {k} {n} f | z rewrite *-comm n 1 | +-right-identity n = z
-}
