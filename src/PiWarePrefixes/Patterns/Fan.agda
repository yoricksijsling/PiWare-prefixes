module PiWarePrefixes.Patterns.Fan where

open import PiWare.Atom using (Atomic; module Atomic)
open import PiWare.Gates using (Gates)
open import PiWarePrefixes.Atom.Int8 using (Atomic-Int8)
open import PiWarePrefixes.Gates.Plus using (Plus; Plus#; _+m_)

abstract -- Should not be expanded by agda, so we can easily convert them to module parameters.
  At : Atomic
  At = Atomic-Int8
  Gt : Gates At
  Gt = Plus

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties.Simple using (+-comm)
open import Data.Product using (proj₁; _,_; _×_; uncurry′)
                         renaming (map to map×)
open import Data.Vec using (Vec; []; _∷_; [_]; _++_; _∷ʳ_; initLast; head)
                     renaming (map to mapᵥ)
open import Function using (id; _$_; _∘_; _⟨_⟩_)
open import PiWare.Circuit {Gt = Gt} using (ℂ; 𝐂; Plug; Gate; _⟫_; _∥_)
open import PiWarePrefixes.Patterns.HetSeq {Gt = Gt} using (_⟫[_]_)
open import PiWarePrefixes.Plugs.Core {Gt = Gt} using (plug-FM)
open import PiWare.Plugs Gt using (id⤨)
open import PiWare.Simulation Gt using (⟦_⟧; W⟶W)
open import PiWarePrefixes.Utils using (initLast′; Morphism; vec-functor)
open import Relation.Binary.PropositionalEquality as P using (_≡_)

open Atomic At using (Atom; W)

abstract -- Should not be expanded by agda, so we can easily convert it to a module parameter.
  plusℂ : 𝐂 2 1
  plusℂ = Gate Plus#

_⊕_ : Atom → Atom → Atom
x ⊕ y = head (⟦ plusℂ ⟧ (x ∷ y ∷ []))


fan-plus-prepare-M : ∀ n → Morphism (vec-functor (suc n)) (vec-functor (n + 2))
fan-plus-prepare-M n = record { op = fanpart-op ; op-<$> = fanpart-<$> }
  where
  fanpart-op : ∀ {X : Set} → Vec X (suc n) → Vec X (n + 2)
  fanpart-op (x ∷ xs) = (uncurry′ _++_ ∘ map× id (λ y → x ∷ y ∷ []) ∘ initLast′) (x ∷ xs)
  postulate -- Theorem for free due to parametricity
    fanpart-<$> : ∀ {X Y : Set} → (f : X → Y) (xs : Vec X (suc n)) →
      fanpart-op (mapᵥ f xs) ≡ mapᵥ f (fanpart-op xs)

fan-plus : ∀ n → 𝐂 (suc n) (n + 1)
fan-plus n = plug-FM (fan-plus-prepare-M n) ⟫ (id⤨ {n}) ∥ plusℂ

fan-plus-spec : ∀ n → W⟶W (suc n) (n + 1)
fan-plus-spec n (x ∷ xs) = (uncurry′ _++_ ∘ map× id (λ y → [ x ⊕ y ]) ∘ initLast′) (x ∷ xs)

swapℕ : ℕ → ℕ
swapℕ zero = zero
swapℕ (suc n) = n + 1

swapℕ-id : ∀ n → swapℕ n ≡ n
swapℕ-id zero = P.refl
swapℕ-id (suc n) = +-comm n 1

mutual
  fan′ : ∀ n → 𝐂 n (swapℕ n)
  fan′ 0 = id⤨ {0}
  fan′ 1 = id⤨ {1}
  fan′ (suc (suc n)) = fan-plus (suc n) ⟫ fan (suc n) ∥ id⤨ {1}

  fan : ∀ n → 𝐂 n n
  fan n = fan′ n ⟫[ swapℕ-id n ] id⤨

fan-spec : ∀ {n} → W⟶W n n
fan-spec [] = []
fan-spec (x ∷ xs) = x ∷ mapᵥ (_⊕_ x) xs
