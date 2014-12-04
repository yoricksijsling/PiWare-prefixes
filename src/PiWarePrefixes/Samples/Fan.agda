module PiWarePrefixes.Samples.Fan where

open import Data.Nat using (zero; suc; _+_)
open import Data.Product using (proj₂)

open import PiWarePrefixes.Gates.Plus using (Plus)
open import PiWare.Circuit.Core Plus using (ℂ'; Nil; _⟫'_; _|'_)
open import PiWarePrefixes.Patterns.Core Plus using (zipWith')
open import PiWare.Plugs.Core Plus using (pFork'; pid')

open import Data.Nat.Properties.Simple using (+-right-identity; *-comm)

fan' : ∀ {n} → ℂ' 2 1 → ℂ' n n
fan' {zero} +ℂ = Nil
fan' {suc n} +ℂ with zipWith' {2} {n} +ℂ
fan' {suc n} +ℂ | z rewrite (+-right-identity) n = pForkFirst'
                                                ⟫' pid' {1} |' z
  where
  fork1 : ∀ k → ℂ' 1 k
  fork1 k with pFork' {k} {1}
  fork1 k | forked rewrite *-comm k 1 | +-right-identity k = forked

  pForkFirst' : ∀ {n} → ℂ' (suc n) (suc (n + n))
  pForkFirst' {n} = fork1 (suc n) |' (pid' {n})
