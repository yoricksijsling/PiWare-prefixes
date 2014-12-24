module PiWarePrefixes.Atom.Int8 where

open import Data.Fin using (Fin)
open import Function using (id)

open import Relation.Binary.PropositionalEquality using (refl)
open import PiWare.Atom using (Atomic)

Atomic-Int8 : Atomic
Atomic-Int8 = record {
      Atom     = Fin 256
    ; |Atom|-1 = 255
    ; n→atom   = id
    ; atom→n   = id
   
    ; inv-left  = λ _ → refl
    ; inv-right = λ _ → refl
    }
