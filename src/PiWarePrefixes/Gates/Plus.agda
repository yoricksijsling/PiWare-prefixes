module PiWarePrefixes.Gates.Plus where

open import Data.Nat using (ℕ)
open import Data.Fin using (Fin) renaming (zero to Fz; suc to Fs)
open import Data.Vec using (Vec; [_]) renaming (_∷_ to _◁_; [] to ε)
open import Data.Bool using (_∧_) renaming (Bool to B)

-- For now, we just Bool atoms. It should work on every semiring.
open import PiWare.Atom.Bool using (Atomic-B)
open import PiWare.Synthesizable Atomic-B using (W)
open import PiWare.Gates Atomic-B using (Gates)

|Plus| = 1

pattern Plus# = Fz
pattern Absurd# n = Fs n

|in| |out| : Fin |Plus| → ℕ
|in| Plus# = 2
|in| (Absurd# ())
|out| Plus# = 1
|out| (Absurd# ())

spec : (g : Fin |Plus|) → (W (|in| g) → W (|out| g))
spec Plus# (x ◁ y ◁ ε) = [ x ∧ y ]
spec (Absurd# ())

Plus : Gates
Plus = record {
       |Gates| = |Plus|
     ; |in|    = |in|
     ; |out|   = |out|
     ; spec    = spec
     }
