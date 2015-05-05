\begin{code}
open import PiWare.Atom using (Atomic; module Atomic)
open import PiWare.Gates using (Gates)

module PiWarePrefixes.Plugs.Core {At : Atomic} {Gt : Gates At} where

open import Data.Fin using (Fin; toℕ)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _≟_)
open import Data.Nat.DivMod using (DivMod; _divMod_; _mod_)
open import Data.Nat.Properties.Simple using (*-right-zero)
open import Data.Vec using (lookup; allFin; tabulate; map) renaming (applicative to vec-applicative)
open import Data.Vec.Properties using (lookup-morphism; tabulate∘lookup; map-lookup-allFin)
open import Data.Unit using (tt)
open import Function using (id; flip; _∘_)
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Decidable using (False; fromWitnessFalse)
open import Relation.Binary.PropositionalEquality using (_≡_; sym; refl; cong)

open import PiWare.Circuit {Gt = Gt} using (𝐂; Plug)
open import PiWare.Interface using (Ix)
open import PiWare.Plugs Gt using (id⤨)
open import PiWare.Simulation Gt using (⟦_⟧)
open import PiWarePrefixes.Utils

open Atomic At using (W)
open Morphism using (op;  op-<$>)

plug-FM : ∀ {i o} → Morphism (vec-functor i) (vec-functor o) → 𝐂 i o
plug-FM M = Plug (op M (allFin _))

plug-FM-⟦⟧ : ∀ {i o} (M : Morphism (vec-functor i) (vec-functor o)) (w : W i) →
             ⟦ plug-FM M ⟧ w ≡ op M w
plug-FM-⟦⟧ {i} M w = begin
  tabulate (λ fin → flip lookup w (lookup fin (op M (allFin _))))
    ≡⟨ tabulate-extensionality (λ fin → sym (op-<$> (AM-to-FM (lookup-morphism fin)) (flip lookup w) _)) ⟩
  tabulate (λ fin → lookup fin (map (flip lookup w) (op M (allFin _))))
    ≡⟨ tabulate-extensionality (λ fin → sym (cong (lookup fin) (op-<$> M (flip lookup w) _))) ⟩
  tabulate (λ fin → lookup fin (op M (map (flip lookup w) (allFin _))))
    ≡⟨ tabulate∘lookup _ ⟩
  op M (map (flip lookup w) (allFin _))
    ≡⟨ cong (op M) (map-lookup-allFin _) ⟩
  op M w
    ∎
  where
  open Relation.Binary.PropositionalEquality.≡-Reasoning

rewire⤨ : ∀ {i o} → (p : i ≡ o) → 𝐂 i o
rewire⤨ refl = id⤨
\end{code}
