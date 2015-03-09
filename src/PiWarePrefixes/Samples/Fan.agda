module PiWarePrefixes.Samples.Fan where

open import Data.Nat using (zero; suc; _+_)
open import Data.Nat.Properties.Simple using (+-right-identity; *-comm)

open import PiWarePrefixes.Gates.Plus using (Plus)
open import PiWare.Circuit Plus using (ℂ; 𝐂; Nil; _⟫_; _∥_)
open import PiWarePrefixes.Patterns.Core Plus using (zipWith)
open import PiWare.Plugs Plus using (forkVec⤨; id⤨)
open import PiWare.Simulation Plus using (⟦_⟧)


fan' : ∀ {n cs} → ℂ {cs} 2 1 → ℂ {cs} n n
fan' {zero} +ℂ = Nil
fan' {suc n} +ℂ with zipWith {2} {n} +ℂ
fan' {suc n} +ℂ | z rewrite (+-right-identity) n = forkFirst⤨ ⟫ id⤨ {1} ∥ z
  where
  fork1 : ∀ k → 𝐂 1 k
  fork1 k {cs} with forkVec⤨ {k} {1} {cs}
  fork1 k | forked rewrite *-comm k 1 | +-right-identity k = forked

  forkFirst⤨ : ∀ {n} → 𝐂 (suc n) (suc (n + n))
  forkFirst⤨ {n} = fork1 (suc n) ∥ (id⤨ {n})
