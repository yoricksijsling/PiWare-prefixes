open import PiWare.Atom using (Atomic; module Atomic)
open import PiWare.Gates using (Gates)

module PiWarePrefixes.Patterns.Core {At : Atomic} (Gt : Gates At) where

open import Data.Fin as Fin using (Fin)
open import Data.Nat using (ℕ; zero; suc; _*_; _+_)
open import Data.Nat.Properties.Simple using (+-right-identity; *-comm)
open import Data.Product renaming (map to map×) --using (uncurry; _,_; <_,_>)
open import Data.Vec hiding (zipWith) renaming (map to mapᵥ)
open import Function using (id; _$_; flip)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; cong₂)

open import PiWare.Circuit Gt using (ℂ; 𝐂; Plug; _⟫_; _∥_)
open import PiWarePrefixes.MinGroups using (ExtractInsert; size)
open import PiWare.Patterns Gt using (parsN)
import PiWarePrefixes.Patterns.Stretch Gt as Stretch
open import PiWare.Plugs Gt using (id⤨)
open import PiWarePrefixes.Plugs.Core Gt using (zip⤨)
open import PiWarePrefixes.Utils using (∷ʳ-injective)

open Atomic At using (W; Atom)

zipWith : ∀ {k n cs} → ℂ {cs} k 1 → ℂ {cs} (k * n) (1 * n)
zipWith {k} {n} f with (zip⤨ {k} {n} ⟫ parsN {n} f)
zipWith {k} {n} f | z rewrite *-comm n 1 | +-right-identity n = z

