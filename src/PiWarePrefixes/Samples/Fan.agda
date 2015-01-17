module PiWarePrefixes.Samples.Fan where

open import Function using (_∘_)
open import Data.Fin using (Fin; toℕ; fromℕ; inject; #_)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.DivMod using (_mod_)
open import Data.Product using (proj₂)
open import Data.Vec using (Vec; map) renaming (_∷_ to _◁_; [] to ε)

open import PiWarePrefixes.Gates.Plus using (Plus; Plus#)
open import PiWare.Circuit.Core Plus using (ℂ'; Anyℂ'; CombSeq; Comb; Nil; Gate; _⟫'_; _|'_)
open import PiWarePrefixes.Patterns.Core Plus using (zipWith')
open import PiWare.Plugs.Core Plus using (pFork'; pid')

open import PiWarePrefixes.Atom.Int8 using (Atomic-Int8)
open import PiWare.Synthesizable Atomic-Int8 using (W)
open import PiWare.Simulation.Core Plus using (⟦_⟧')

open import Data.Nat.Properties.Simple using (+-right-identity; *-comm)

ℂ=' : {cs : CombSeq} → ℕ → Set
ℂ=' {cs} n = ℂ' {cs} n n

fan' : ∀ {n cs} → ℂ' {cs} 2 1 → ℂ=' {cs} n
fan' {zero} +ℂ = Nil
fan' {suc n} +ℂ with zipWith' {2} {n} +ℂ
fan' {suc n} +ℂ | z rewrite (+-right-identity) n = pForkFirst'
                                                ⟫' pid' {1} |' z
  where
  fork1 : ∀ k → Anyℂ' 1 k
  fork1 k {cs} with pFork' {k} {1} {cs}
  fork1 k | forked rewrite *-comm k 1 | +-right-identity k = forked

  pForkFirst' : ∀ {n} → Anyℂ' (suc n) (suc (n + n))
  pForkFirst' {n} = fork1 (suc n) |' (pid' {n})

ex : ∀ {i o} → (c : ℂ' {Comb} i o) → Vec (Fin 256) i → Vec ℕ o
ex c = map toℕ ∘ ⟦ c ⟧'

ev3 : Vec ℕ 3
ev3 = ex (fan' (Gate Plus#)) (# 2 ◁ # 3 ◁ # 4 ◁ ε)
