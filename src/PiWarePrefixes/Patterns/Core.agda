open import PiWare.Atom using (Atomic; module Atomic)
open import PiWare.Gates using (Gates)

module PiWarePrefixes.Patterns.Core {At : Atomic} (Gt : Gates At) where

open import Data.Fin as Fin using (Fin)
open import Data.Nat using (ℕ; zero; suc; _*_; _+_)
open import Data.Nat.Properties.Simple using (+-right-identity; *-comm)
open import Data.Product renaming (map to map×) --using (uncurry; _,_; <_,_>)
open import Data.Vec hiding (zipWith) renaming (map to mapᵥ)
open import Function using (id; _$_; flip)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; cong₂)

open import PiWare.Circuit Gt using (ℂ; 𝐂; Plug; _⟫_; _∥_)
open import PiWarePrefixes.MinGroups using (ExtractInsert; size)
open import PiWare.Patterns Gt using (parsN)
import PiWarePrefixes.Patterns.Stretch Gt as Stretch
open import PiWare.Plugs Gt using (id⤨)
open import PiWarePrefixes.Plugs.Core Gt using (zip⤨)
open import PiWarePrefixes.Utils using (∷ʳ-injective)

open Atomic At using (W; Atom)


zipWith : ∀ {k n cs} → ℂ {cs} k 1 → ℂ {cs} (k * n) (1 * n)
zipWith {k} {n} f with (zip⤨ {k} {n} ⟫ parsN {n} f)
zipWith {k} {n} f | z rewrite *-comm n 1 | +-right-identity n = z

⤙-direction : ExtractInsert
⤙-direction = record
  { extf = record { op = < head , tail > ; op-<$> = extf-op-<$> }
  ; insf = record { op = uncurry _∷_ ; op-<$> = λ f x → refl }
  ; extf-insf-id = extf-insf-id
  ; insf-extf-id = insf-extf-id
  }
  where
  extf-op-<$> : ∀ {n} {X Y : Set} (f : X → Y) (x : Vec X (suc n)) →
                (head (f ∷ replicate f ⊛ x) , tail (f ∷ replicate f ⊛ x)) ≡
                (f (head x) , (replicate f ⊛ tail x))
  extf-op-<$> f (x ∷ _) = cong (_,_ (f x)) refl
  extf-insf-id : {A : Set} {n : ℕ} (xs : Vec A (suc n)) → head xs ∷ tail xs ≡ xs
  extf-insf-id (_ ∷ _) = refl
  insf-extf-id : {A : Set} {n : ℕ} (x : A × Vec A n) → (proj₁ x , proj₂ x) ≡ x
  insf-extf-id (_ , _) = refl

_⤙_ : ∀ {n cs} → ℂ {cs} n n → (as : Vec ℕ n) → ℂ {cs} (size 1 as) (size 1 as)
_⤙_ = Stretch.WithDirection.stretch ⤙-direction


⤚-direction : ExtractInsert
⤚-direction = record
  { extf = record { op = < last , init > ; op-<$> = extf-op-<$> }
  ; insf = record { op = uncurry (flip _∷ʳ_) ; op-<$> = λ f → uncurry (insf-op-<$> f) }
  ; extf-insf-id = extf-insf-id
  ; insf-extf-id = uncurry insf-extf-id
  }
  where
  extf-insf-id : {A : Set} {n : ℕ} (xs : Vec A (suc n)) → init xs ∷ʳ last xs ≡ xs
  extf-insf-id xs with initLast xs
  extf-insf-id .(xs ∷ʳ x) | xs , x , refl = refl

  insf-extf-id : {A : Set} {n : ℕ} (x : A) (xs : Vec A n) → last (xs ∷ʳ x) , init (xs ∷ʳ x) ≡ x , xs
  insf-extf-id x xs with initLast (xs ∷ʳ x)
  insf-extf-id x xs | ys , y , p with ∷ʳ-injective xs ys p
  insf-extf-id x xs | ys , y , p | xs=ys , x=y rewrite p | x=y | xs=ys = refl

  postulate
    extf-op-<$> : ∀ {n} {X Y : Set} (f : X → Y) (xs : Vec X (suc n)) →
      last (mapᵥ f xs) , init (mapᵥ f xs) ≡ f (last xs) , (mapᵥ f (init xs))
    insf-op-<$> : ∀ {n} {X Y : Set} (f : X → Y) (x : X) (xs : Vec X n) →
      mapᵥ f xs ∷ʳ f x ≡ mapᵥ f (xs ∷ʳ x)

_⤚_ : ∀ {n cs} → (as : Vec ℕ n) → ℂ {cs} n n → ℂ {cs} (size 1 as) (size 1 as)
_⤚_ = flip (Stretch.WithDirection.stretch ⤚-direction)
