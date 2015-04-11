open import PiWare.Atom using (Atomic; module Atomic)
open import PiWare.Gates using (Gates)

module PiWarePrefixes.Simulation.Properties.Stretching.Derived {At : Atomic} (Gt : Gates At) where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Product using (proj₁; proj₂; _,_; ,_; <_,_>)
open import Data.Vec using (Vec; _++_; _∷_; []; [_]; _∷ʳ_; replicate; splitAt)
                     renaming (sum to sumᵥ; map to mapᵥ)
open import PiWarePrefixes.MinGroups using (size)
open import PiWare.Circuit {Gt = Gt} using (ℂ; 𝐂; Plug; _⟫_; _∥_; σ)
open import PiWarePrefixes.Circuit.Context.Core Gt
open import PiWarePrefixes.Patterns.HetSeq {Gt = Gt}
open import PiWarePrefixes.Patterns.Stretch {Gt = Gt} as Stretch
  using (_⤚_; ⤚-direction; _⤙_; ⤙-direction; _⤛_; _⤜_; Stretching-ℂ; par-stretching)
open import PiWare.Plugs Gt using (id⤨)
open import PiWarePrefixes.Plugs.Core {Gt = Gt} using (rewire⤨)
open import PiWarePrefixes.Simulation.Equality.Core {Gt = Gt} as SimEq
  renaming (≈⟦⟧-refl to refl; ≈⟦⟧-sym to sym)
open import PiWarePrefixes.Simulation.Properties Gt
open import PiWarePrefixes.Simulation.Properties.HetSeq Gt
open import PiWarePrefixes.Simulation.Properties.Stretching Gt
open import PiWarePrefixes.Utils using (map-replicate)
open import Relation.Binary.PropositionalEquality as P using (_≡_)

private
  import Data.Vec.Equality
  import Data.Vec.Equality.Indexed
  module VE = Data.Vec.Equality.PropositionalEquality
  open VE using ([]-cong; _∷-cong_)
  module VES = Data.Vec.Equality.Indexed.Equality (reindexed-≈⟦⟧-setoid (< suc , suc >))
  open VES using ([]-cong; _∷-cong_)

open Atomic At using (W)

-- Derived stretch law 1
-- f ⤙ x ++ [j + k] = (f ⤙ x ++ [j]) × id{k}
stretch-derived-1 : ∀ {n j k} (f : ℂ (suc n) (suc n)) (xs : Vec ℕ n) →
                    f ⤙ (xs ∷ʳ (j + k)) ≈⟦⟧ (f ⤙ (xs ∷ʳ j)) ∥ id⤨ {k}
stretch-derived-1 {n} {j} {k} f xs = begin
  f ⤙ (xs ∷ʳ (j + k))
    ≈⟦⟧⟨ sym (∥-left-identity _) ⟩
  (id⤨ {0}) ∥ (f ⤙ (xs ∷ʳ (j + k)))
    ≈⟦⟧⟨ stretch-flip f xs ⟩
  (0 ∷ xs) ⤚ f ∥ id⤨ {j + k}
    ≈⟦⟧⟨ refl ∥-cong (sym ∥-id⤨) ⟩
  (0 ∷ xs) ⤚ f ∥ id⤨ {j} ∥ id⤨ {k}
    ≈⟦⟧⟨ sym (∥-assoc _ _ _) ⟩
  ((0 ∷ xs) ⤚ f ∥ id⤨ {j}) ∥ id⤨ {k}
    ≈⟦⟧⟨ (sym (stretch-flip f xs)) ∥-cong refl ⟩
  (id⤨ {0} ∥ f ⤙ (xs ∷ʳ j)) ∥ id⤨ {k}
    ≈⟦⟧⟨ (∥-left-identity _) ∥-cong refl ⟩
  f ⤙ (xs ∷ʳ j) ∥ id⤨ {k}
    ∎
  where
  open SimEq.≈⟦⟧-Reasoning

-- Derived stretch law 2
-- (f × id{#y-1}) ⤙ x ++ y = f ⤙ x ++ [Σy]
stretch-derived-2 : ∀ {n m} (f : ℂ (suc n) (suc n)) (xs : Vec ℕ n) (y : ℕ) (ys : Vec ℕ m) →
                    (f ∥ id⤨ {m}) ⤙ ((xs ∷ʳ y) ++ ys) ≈⟦⟧ f ⤙ (xs ∷ʳ y + size 1 ys)
stretch-derived-2 {n} {m} f xs y ys = begin
  (f ∥ id⤨ {m}) ⤙ ((xs ∷ʳ y) ++ ys)
    ≈⟦⟧⟨ ⤙-∥-distrib (xs ∷ʳ y) ys f id⤨ ⟩
  f ⤙ (xs ∷ʳ y) ∥ id⤨ {m} ⤙ ys
    ≈⟦⟧⟨ refl ∥-cong (⤙-preserves-id ys) ⟩
  f ⤙ (xs ∷ʳ y) ∥ id⤨ {size 1 ys}
    ≈⟦⟧⟨ sym (stretch-derived-1 f xs) ⟩
  f ⤙ (xs ∷ʳ y + size 1 ys)
    ∎
  where
  open SimEq.≈⟦⟧-Reasoning

par-stretching-cong : ∀ {m n} {cs : Vec Stretching-ℂ m} {ds : Vec Stretching-ℂ n} →
                      cs VES.≈ ds → par-stretching cs ≈⟦⟧ par-stretching ds
par-stretching-cong []-cong = refl
par-stretching-cong {cs = (i , c) ∷ cs} {(j , d) ∷ ds} (c≈d ∷-cong cs≈ds) = c≈d ∥-cong (par-stretching-cong cs≈ds)

_⤛-cong_ : ∀ {m n} {f : ℂ m m} {g : ℂ n n} {cs : Vec Stretching-ℂ m} {ds : Vec Stretching-ℂ n} →
          f ≈⟦⟧ g → cs VES.≈ ds → f ⤛ cs ≈⟦⟧ g ⤛ ds
_⤛-cong_ {f = f} {g} {cs} {ds} f≈g cs≈ds = (f≈g ⤙-cong lem cs≈ds) ⟫-cong (par-stretching-cong cs≈ds) 
  where
  lem : ∀ {m n} {cs : Vec Stretching-ℂ m} {ds : Vec Stretching-ℂ n} →
        cs VES.≈ ds → mapᵥ proj₁ cs VE.≈ mapᵥ proj₁ ds
  lem []-cong = []-cong
  lem ((Mk≈⟦⟧ P.refl f≈g) ∷-cong cs≈ds) = P.refl ∷-cong lem cs≈ds

⤛-on-identity : ∀ {n} (cs : Vec Stretching-ℂ n) →
                 id⤨ {n} ⤛ cs ≈⟦⟧ par-stretching cs
⤛-on-identity {n} cs = begin
  id⤨ {n} ⤙ mapᵥ proj₁ cs ⟫ par-stretching cs
    ≈⟦⟧⟨ (⤙-preserves-id _) ⟫-cong refl ⟩
  id⤨ {size 1 (mapᵥ proj₁ cs)} ⟫ par-stretching cs
    ≈⟦⟧⟨ ⟫-left-identity _ ⟩
  par-stretching cs
    ∎
  where
  open SimEq.≈⟦⟧-Reasoning

⤛-by-identity : ∀ {n} (f : ℂ n n) → f ⤛ (replicate (, id⤨ {1})) ≈⟦⟧ f
⤛-by-identity {n} f = begin
  f ⤙ mapᵥ proj₁ (replicate (, id⤨ {1})) ⟫ par-stretching {n} (replicate (, id⤨ {1}))
    ≈⟦⟧⟨ refl ⟫[-cong (par-ids=id n) ⟩
  f ⤙ mapᵥ proj₁ (replicate (, id⤨ {1})) ⟫[] id⤨ {n}
    ≈⟦⟧⟨ ⟫[]-right-identity _ ⟩
  f ⤙ mapᵥ proj₁ (replicate (, id⤨ {1}))
    ≈⟦⟧⟨ refl ⤙-cong (VE.from-≡ (map-replicate proj₁ (, id⤨ {1}))) ⟩
  f ⤙ replicate 0
    ≈⟦⟧⟨ ⤙-by-identity f ⟩
  f
    ∎
  where
  open SimEq.≈⟦⟧-Reasoning
  par-ids=id : ∀ n → par-stretching {n} (replicate (, id⤨ {1})) ≈⟦⟧ id⤨ {n}
  par-ids=id zero = refl
  par-ids=id (suc n) = begin
    id⤨ {1} ∥ par-stretching {n} (replicate (, id⤨ {1}))
      ≈⟦⟧⟨ refl ∥-cong par-ids=id n ⟩
    id⤨ {1} ∥ id⤨ {n}
      ≈⟦⟧⟨ ∥-id⤨ ⟩
    id⤨ {suc n}
      ∎
