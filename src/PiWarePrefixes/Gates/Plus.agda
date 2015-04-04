module PiWarePrefixes.Gates.Plus where

open import Data.Nat using (ℕ; _+_)
open import Data.Nat.DivMod using (_mod_)
open import Data.Fin using (Fin; toℕ) renaming (zero to Fz; suc to Fs)
open import Data.Vec using (Vec; [_]) renaming (_∷_ to _◁_; [] to ε)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import PiWare.Atom using (module Atomic)
open import PiWarePrefixes.Atom.Int8 using (Atomic-Int8)
open import PiWare.Gates Atomic-Int8 using (Gates)
open Atomic Atomic-Int8 using (W)

|Plus| = 1

pattern Plus#       = Fz
pattern Absurd# n   = Fs n

|in| |out| : Fin |Plus| → ℕ
|in| = λ { Plus# → 2; (Absurd# ()) }
|out| _ = 1

_+m_ : Fin 256 → Fin 256 → Fin 256
i +m j = (toℕ i + toℕ j) mod 256

postulate
  +m-assoc : ∀ m n o → (m +m n) +m o ≡ m +m (n +m o)

spec : (g : Fin |Plus|) → (W (|in| g) → W (|out| g))
spec Plus# (x ◁ y ◁ ε) = [ x +m y ]
spec (Absurd# ())

Plus : Gates
Plus = record {
       |Gates| = |Plus|
     ; |in|    = |in|
     ; |out|   = |out|
     ; spec    = spec
     }
