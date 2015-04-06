module PiWarePrefixes.Patterns.Fan where

open import PiWare.Atom using (Atomic; module Atomic)
open import PiWare.Gates using (Gates)
open import PiWarePrefixes.Atom.Int8 using (Atomic-Int8)
open import PiWarePrefixes.Gates.Plus using (Plus; Plus#; _+m_)

At : Atomic
At = Atomic-Int8

Gt : Gates At
Gt = Plus

open import Category.Functor using (module RawFunctor)
open import Data.Fin using (Fin)
open import Data.Nat using (zero; suc; _+_)
open import Data.Nat.Properties.Simple using (+-right-identity; +-comm; *-comm)
open import Data.Product using (_,_)
open import Data.Vec using (Vec; []; _∷_; [_]; _++_; _∷ʳ_; initLast) renaming (map to mapᵥ)
open import Function using (_$_; _⟨_⟩_)
open import PiWare.Circuit Gt using (ℂ; 𝐂; Nil; Plug; Gate; _⟫_; _∥_)
open import PiWarePrefixes.Patterns.Core Gt using (zipWith)
open import PiWarePrefixes.Patterns.HetSeq Gt using (_⟫[_]_)
open import PiWarePrefixes.Plugs.Core Gt using (plug-FM)
open import PiWare.Plugs Gt using (forkVec⤨; id⤨)
open import PiWare.Simulation Gt using (⟦_⟧; W⟶W)
open import PiWarePrefixes.Utils using (module Morphism; Morphism; vec-functor)
open import Relation.Binary.PropositionalEquality as P using (cong; cong₂; trans; _≡_)

open Atomic At using (Atom; W)
open RawFunctor
open Morphism using (op; op-<$>)

private
  plusℂ : 𝐂 2 1
  plusℂ = Gate Plus#

  _⊕_ : Atom → Atom → Atom
  _⊕_ = _+m_

fan : ∀ n → 𝐂 n n
fan zero = Nil
fan (suc n) {p} with zipWith {2} {n} {p} plusℂ
fan (suc n) | z rewrite (+-right-identity) n = forkFirst⤨ ⟫ id⤨ {1} ∥ z
  where
  fork1 : ∀ k → 𝐂 1 k
  fork1 k {p} with forkVec⤨ {k} {1} {p}
  fork1 k | forked rewrite *-comm k 1 | +-right-identity k = forked

  forkFirst⤨ : ∀ {n} → 𝐂 (suc n) (suc (n + n))
  forkFirst⤨ {n} = fork1 (suc n) ∥ (id⤨ {n})

fanpart-M : ∀ n → Morphism (vec-functor (suc n)) (vec-functor (n + 2))
fanpart-M n = record
  { op = fanpart-op
  ; op-<$> = fanpart-<$>
  }
  where
  fanpart-op : ∀ {X : Set} → Vec X (suc n) → Vec X (n + 2)
  fanpart-op (x ∷ xs) with initLast (x ∷ xs)
  fanpart-op (x ∷ xs) | ys , y , _ = ys ++ x ∷ y ∷ []

  import Data.Vec.Equality
  module VE = Data.Vec.Equality.PropositionalEquality
  import Data.Vec.Properties
  module VEP {A : Set} = Data.Vec.Properties.UsingVectorEquality (P.setoid A)

  postulate
    fanpart-<$> : ∀ {X Y : Set} → (f : X → Y) (xs : Vec X (suc n)) →
      fanpart-op (mapᵥ f xs) ≡ mapᵥ f (fanpart-op xs)
  -- fanpart-<$> f (x ∷ xs) with initLast (x ∷ xs)
  -- fanpart-<$> f (x ∷ xs) | ys , y , _ = VE.to-≡ $
  --                {!cong₂ _++_!}
  --   ⟨ VE.trans ⟩ VE.sym (VEP.map-++-commute f ys)

fanblob : ∀ n → 𝐂 (suc n) (n + 1)
fanblob n = plug-FM (fanpart-M n) ⟫ (id⤨ {n}) ∥ plusℂ

fanblob-spec : ∀ n → W⟶W (suc n) (n + 1)
fanblob-spec n (x ∷ xs) with initLast (x ∷ xs)
fanblob-spec n (x ∷ xs) | ys , y , p = ys ++ [ x ⊕ y ]

fan′ : ∀ n → 𝐂 n n
fan′ zero = id⤨ {0}
fan′ (suc n) = fanblob n ⟫ fan′ n ∥ id⤨ {1} ⟫[ +-comm n 1 ] id⤨

fan-spec : ∀ {n} → W⟶W n n
fan-spec [] = []
fan-spec (x ∷ xs) = x ∷ mapᵥ (_⊕_ x) xs

