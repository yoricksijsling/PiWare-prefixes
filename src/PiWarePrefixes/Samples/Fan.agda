module PiWarePrefixes.Samples.Fan where

open import Function using (_∘_)
open import Data.Fin using (Fin; toℕ; fromℕ; inject; #_)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.DivMod using (_mod_)
open import Data.Product using (proj₂)
open import Data.Vec using (Vec; map) renaming (_∷_ to _◁_; [] to ε)

open import PiWarePrefixes.Gates.Plus using (Plus; Plus#)
open import PiWare.Circuit.Core Plus using (ℂ'; Nil; Gate; _⟫'_; _|'_; comb')
open import PiWarePrefixes.Patterns.Core Plus using (zipWith')
open import PiWare.Plugs.Core Plus using (pFork'; pid')

open import PiWarePrefixes.Atom.Int8 using (Atomic-Int8)
open import PiWare.Synthesizable Atomic-Int8 using (W)
open import PiWare.Simulation.Core Plus using (⟦_⟧')

open import Data.Nat.Properties.Simple using (+-right-identity; *-comm)

ℂ=' : ℕ -> Set
ℂ=' n = ℂ' n n

fan' : ∀ {n} → ℂ' 2 1 → ℂ=' n
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

ex : ∀ {i o} → (c : ℂ' i o) → {p : comb' c} → Vec (Fin 256) i → Vec ℕ o
ex c {p} = map toℕ ∘ ⟦ c ⟧' {p}

ev3 : Vec ℕ 3
ev3 = ex (fan' (Gate Plus#)) (# 2 ◁ # 3 ◁ # 4 ◁ ε)
