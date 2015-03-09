open import PiWare.Atom using (Atomic; module Atomic)
open import PiWare.Gates using (Gates)

module PiWarePrefixes.Simulation.Properties.Stretching {At : Atomic} (Gt : Gates At) where

open import Data.Fin using (Fin)
open import Data.Nat using (ℕ; suc; _+_)
open import Data.Nat.Properties.Simple using (+-comm; +-suc; +-assoc)
open import Data.Vec using (Vec; _++_; _∷_; [])
                     renaming (sum to sumᵥ)
open import Relation.Binary.PropositionalEquality as PropEq using (refl; cong; sym; _≡_; subst; trans)

open import PiWare.Circuit Gt using (ℂ; σ; Plug; _⟫_; _∥_)
open import PiWarePrefixes.Circuit.Context.Core Gt
open import PiWarePrefixes.Patterns.Core Gt using (_⤚_; ⤚-perm; _⤙_)
open import PiWarePrefixes.Permutation as P using (Perm; _§_; _*)
open import PiWare.Plugs Gt using (id⤨)
open import PiWarePrefixes.Simulation.Equality.Core Gt as SimEq
open import PiWarePrefixes.Simulation.Properties Gt

private
  import Data.Vec.Equality
  module VE = Data.Vec.Equality.PropositionalEquality


----------------------------------------------------
-- Stretching

postulate
  ⤙-equal : ∀ {n} (f : ℂ n n) {xs ys : Vec ℕ n} →
             xs ≡ ys → f ⤙ xs ≈⟦⟧ f ⤙ ys

-- id{#x} ⤙ x ≡ id{Σx}
postulate
  ⤙-preserves-id : ∀ {n} (xs : Vec ℕ n) → id⤨ {n} ⤙ xs ≈⟦⟧ id⤨ {sumᵥ xs + n}

⤚-preserves-id : ∀ {n} (xs : Vec ℕ n) → xs ⤚ id⤨ {n} ≈⟦⟧ id⤨ {sumᵥ xs + n}
⤚-preserves-id {n} xs = begin
  Plug to ⟫ id⤨ {sumᵥ xs} ∥ id⤨ {n} ⟫ Plug from
    ≈⟦⟧⟨ ≈⟦⟧-cong (bla ⟫● ● ●⟫ bla)
                ∥-id⤨ ⟩
  Plug to ⟫ id⤨ {sumᵥ xs + n} ⟫ Plug from
    ≈⟦⟧⟨ ≈⟦⟧-cong (● ●⟫ bla)
                (⟫-right-identity (Plug to)) ⟩
  Plug to ⟫ Plug from
    ≈⟦⟧⟨ pid-plugs to-from-id ⟩
  id⤨
    ∎
  where
  open SimEq.≈⟦⟧-Reasoning
  to : Fin (sumᵥ xs + n) → Fin (sumᵥ xs + n)
  to = _§_ (⤚-perm xs)
  from : Fin (sumᵥ xs + n) → Fin (sumᵥ xs + n)
  from = _§_ (⤚-perm xs *)
  to-from-id : ∀ x → to (from x) ≡ x
  to-from-id = P.§-right-inverse (⤚-perm xs)


-- (f ⟫ g) ⤙ x ≡ f ⤙ x ⟫ g ⤙ x
postulate
  ⤙-⟫-distrib' : ∀ {n} (xs : Vec ℕ n) (f g : ℂ n n) → (f ⤙ xs) ⟫ (g ⤙ xs) ≈⟦⟧ (f ⟫ g) ⤙ xs

-- x ⤚ (f ⟫ g) ≡ x ⤚ f ⟫ x ⤚ g
⤚-⟫-distrib' : ∀ {n} (xs : Vec ℕ n) (f g : ℂ n n) → (xs ⤚ f) ⟫ (xs ⤚ g) ≈⟦⟧ xs ⤚ (f ⟫ g)
⤚-⟫-distrib' {n} xs f g = begin
  Plug to ⟫ id⤨ {sumᵥ xs} ∥ f ⟫ Plug from ⟫
  (Plug to ⟫ id⤨ {sumᵥ xs} ∥ g ⟫ Plug from)
    ≈⟦⟧⟨ easy-≈⟦⟧ (λ w → VE.refl _) ⟩
  Plug to ⟫
  (id⤨ {sumᵥ xs} ∥ f ⟫ (Plug from ⟫ Plug to) ⟫ id⤨ {sumᵥ xs} ∥ g) ⟫
  Plug from
    ≈⟦⟧⟨ ≈⟦⟧-cong (bla ⟫● ● ●⟫ bla) (begin
        id⤨ {sumᵥ xs} ∥ f ⟫ (Plug from ⟫ Plug to) ⟫ id⤨ {sumᵥ xs} ∥ g
          ≈⟦⟧⟨ ≈⟦⟧-cong (bla ⟫● ● ●⟫ bla) (pid-plugs from-to-id) ⟩
        id⤨ {sumᵥ xs} ∥ f ⟫ id⤨ ⟫ id⤨ {sumᵥ xs} ∥ g
          ≈⟦⟧⟨ ≈⟦⟧-cong (● ●⟫ bla) (⟫-right-identity _) ⟩
        id⤨ {sumᵥ xs} ∥ f ⟫ id⤨ {sumᵥ xs} ∥ g
          ≈⟦⟧⟨ ⟫-∥-distrib _ _ _ _ ⟩
        (id⤨ {sumᵥ xs} ⟫ id⤨ {sumᵥ xs}) ∥ (f ⟫ g)
          ≈⟦⟧⟨ ≈⟦⟧-cong (● ●∥ bla) (⟫-right-identity _) ⟩
        id⤨ {sumᵥ xs} ∥ (f ⟫ g)
          ∎) ⟩
  Plug to ⟫ id⤨ {sumᵥ xs} ∥ (f ⟫ g) ⟫ Plug from
    ∎
  where
  open SimEq.≈⟦⟧-Reasoning
  to : Fin (sumᵥ xs + n) → Fin (sumᵥ xs + n)
  to = _§_ (⤚-perm xs)
  from : Fin (sumᵥ xs + n) → Fin (sumᵥ xs + n)
  from = _§_ (⤚-perm xs *)
  from-to-id : ∀ x → from (to x) ≡ x
  from-to-id = P.§-left-inverse (⤚-perm xs)

postulate
  ⤙-||-distrib' : ∀ {n m} (xs : Vec ℕ n) (ys : Vec ℕ m)
        (f : ℂ {σ} n n) (g : ℂ {σ} m m) →
        (f ∥ g) ⤙ (xs ++ ys) ≈⟦⟧ (f ⤙ xs) ∥ (g ⤙ ys)

  ⤚-||-distrib' : ∀ {n m} (xs : Vec ℕ n) (ys : Vec ℕ m)
        (f : ℂ {σ} n n) (g : ℂ {σ} m m) →
        (xs ++ ys) ⤚ (f ∥ g) ≈⟦⟧ (xs ⤚ f) ∥ (ys ⤚ g)

_∷ʳ_ : ∀ {a n} {A : Set a} (xs : Vec A n) (x : A) → Vec A (suc n)
_∷ʳ_ {n = n} xs x rewrite +-comm 1 n = xs ++ (x ∷ [])

-- flip law
postulate
  -- stretch-flip : ∀ {i k n} (f : ℂ (suc n) (suc n)) (ys : Vec ℕ n) →
  --                id⤨ {i} ∥ (f ⤙ (ys ∷ʳ suc k)) ≈⟦⟧ ((suc i ∷ ys) ⤚ f) ∥ id⤨ {k}
  stretch-flip : ∀ {i k n} (f : ℂ (suc n) (suc n)) (ys : Vec ℕ n) →
                 id⤨ {i} ∥ (f ⤙ (ys ∷ʳ k)) ≈⟦⟧ ((i ∷ ys) ⤚ f) ∥ id⤨ {k}

-- Derived stretch law 1
-- f ⤙ x ++ [j + k] = (f ⤙ x ++ [j]) × id{k}
stretch-derived-1 : ∀ {n j k} (f : ℂ (suc n) (suc n)) (xs : Vec ℕ n) →
                    f ⤙ (xs ∷ʳ (j + k)) ≈⟦⟧ (f ⤙ (xs ∷ʳ j)) ∥ id⤨ {k}
stretch-derived-1 {n} {j} {k} f xs = begin
  f ⤙ (xs ∷ʳ (j + k))
    ≈⟦⟧⟨ ≈⟦⟧-sym (∥-left-identity _) ⟩
  (id⤨ {0}) ∥ (f ⤙ (xs ∷ʳ (j + k)))
    ≈⟦⟧⟨ stretch-flip f xs ⟩
  (0 ∷ xs) ⤚ f ∥ id⤨ {j + k}
    ≈⟦⟧⟨ ≈⟦⟧-cong (bla ∥● ●) (≈⟦⟧-sym ∥-id⤨) ⟩
  (0 ∷ xs) ⤚ f ∥ id⤨ {j} ∥ id⤨ {k}
    ≈⟦⟧⟨ ≈⟦⟧-sym (∥-assoc _ _ _) ⟩
  ((0 ∷ xs) ⤚ f ∥ id⤨ {j}) ∥ id⤨ {k}
    ≈⟦⟧⟨ ≈⟦⟧-cong (● ●∥ bla) (≈⟦⟧-sym (stretch-flip f xs)) ⟩
  (id⤨ {0} ∥ f ⤙ (xs ∷ʳ j)) ∥ id⤨ {k}
    ≈⟦⟧⟨ ≈⟦⟧-cong (● ●∥ bla) (∥-left-identity _) ⟩
  f ⤙ (xs ∷ʳ j) ∥ id⤨ {k}
    ∎
  where
  open SimEq.≈⟦⟧-Reasoning

-- (f × id{#y-1}) ⤙ x ++ y = f ⤙ x ++ [Σy]
stretch-derived-2 : ∀ {n m} (f : ℂ (suc n) (suc n)) (xs : Vec ℕ n) (ys : Vec ℕ (suc m)) →
                    (f ∥ id⤨ {m}) ⤙ subst (Vec ℕ) (+-suc n m) (xs ++ ys)
                      ≈⟦⟧ (f ⤙ (xs ∷ʳ (sumᵥ ys + m)))
stretch-derived-2 {n} {m} f xs (y ∷ ys) = begin
  (f ∥ id⤨ {m}) ⤙ subst (Vec ℕ) (+-suc n m) (xs ++ (y ∷ ys))
    ≈⟦⟧⟨ ⤙-equal _ {!!} ⟩
  (f ∥ id⤨ {m}) ⤙ (xs ∷ʳ y ++ ys)
    ≈⟦⟧⟨ ⤙-||-distrib' _ _ _ _ ⟩
  f ⤙ (xs ∷ʳ y) ∥ id⤨ {m} ⤙ ys
    ≈⟦⟧⟨ ≈⟦⟧-cong (bla ∥● ●) (⤙-preserves-id _) ⟩
  f ⤙ (xs ∷ʳ y) ∥ id⤨ {sumᵥ ys + m}
    ≈⟦⟧⟨ ≈⟦⟧-sym (stretch-derived-1 f xs) ⟩
  f ⤙ (xs ∷ʳ (y + (sumᵥ ys + m)))
    ≈⟦⟧⟨ ⤙-equal f (cong (_∷ʳ_ xs) (sym (+-assoc y (sumᵥ ys) m))) ⟩
  f ⤙ (xs ∷ʳ (sumᵥ (y ∷ ys) + m))
    ∎
  where
  open SimEq.≈⟦⟧-Reasoning

