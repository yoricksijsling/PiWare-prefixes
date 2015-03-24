open import PiWare.Atom using (Atomic; module Atomic)
open import PiWare.Gates using (Gates)

module PiWarePrefixes.Simulation.Properties.Stretching {At : Atomic} (Gt : Gates At) where

open import Data.Fin using (Fin)
open import Data.Nat using (ℕ; suc; _+_)
open import Data.Nat.Properties.Simple using (+-comm; +-suc; +-assoc)
open import Data.Product renaming (map to map×)
open import Data.Vec using (Vec; _++_; _∷_; []; [_]; _∷ʳ_)
                     renaming (sum to sumᵥ; map to mapᵥ)
open import Data.Vec.Extra using (splitAt')
open import Function using (id; _$_; _∘_)
open import Relation.Binary.PropositionalEquality as PropEq using (refl; cong; cong₂; sym; _≡_; subst; trans)

open import PiWare.Circuit Gt using (ℂ; 𝐂; Plug; _⟫_; _∥_)
open import PiWarePrefixes.Circuit.Context.Core Gt
open import PiWarePrefixes.MinGroups as MinGroups
open import PiWarePrefixes.Patterns.Core Gt using (_⤚_; ⤚-direction; _⤙_; ⤙-direction)
import PiWarePrefixes.Patterns.Stretch Gt as Stretch
open import PiWarePrefixes.Permutation as P using (Perm; _§_; _*)
open import PiWare.Plugs Gt using (id⤨)
open import PiWarePrefixes.Plugs.Core Gt using (plug-M; plug-M-⟦⟧; M-∘)
open import PiWare.Simulation Gt using (⟦_⟧; W⟶W)
open import PiWarePrefixes.Simulation.Equality.Core Gt as SimEq
open import PiWarePrefixes.Simulation.Properties Gt

private
  import Data.Vec.Equality
  module VE = Data.Vec.Equality.PropositionalEquality

open Atomic At using (W; Atom)


module WithDirection (extract-insert : ExtractInsert) where
  open MinGroups.WithExtractInsert extract-insert
  open Stretch.WithDirection extract-insert

  stretch-cong : ∀ {m n} {f : ℂ m m} {g : ℂ n n} {as : Vec ℕ m} {bs : Vec ℕ n} →
                 f ≈⟦⟧ g → as VE.≈ bs → stretch f as ≈⟦⟧ stretch g bs
  stretch-cong {f = f} {g} {as} (Mk≈⟦⟧ refl f≈g) q with VE.to-≡ q
  ... | refl = easy-≈⟦⟧ (VE.from-≡ ∘ helper)
    where
    helper : ∀ w → ⟦ stretch f as ⟧ w ≡ ⟦ stretch g as ⟧ w
    helper w rewrite conv f as w | conv g as w
      = cong ungroup (extract-map-cong (VE.to-≡ ∘ f≈g ∘ VE.refl) (group 1 as w))

  preserves-id : ∀ {n} (as : Vec ℕ n) → stretch (id⤨ {n}) as ≈⟦⟧ id⤨ {sumᵥ (mapᵥ suc as)}
  preserves-id {n} as = easy-≈⟦⟧ (VE.from-≡ ∘ helper)
    where
    open PropEq.≡-Reasoning
    helper : ∀ w → ⟦ stretch id⤨ as ⟧ w ≡ ⟦ id⤨ ⟧ w
    helper w = begin
      ⟦ stretch id⤨ as ⟧ w
        ≡⟨ conv id⤨ as w ⟩
      (ungroup ∘ extract-map ⟦ id⤨ ⟧ ∘ group 1 as) w
        ≡⟨ cong ungroup (extract-map-cong id⤨-id (group 1 as w)) ⟩
      (ungroup ∘ extract-map id ∘ group 1 as) w
        ≡⟨ cong ungroup (extract-map-id (group 1 as w)) ⟩
      (ungroup ∘ group 1 as) w
        ≡⟨ group-ungroup-identity as w ⟩
      w
        ≡⟨ sym (id⤨-id w) ⟩
      ⟦ id⤨ ⟧ w
        ∎

  ⟫-distrib : ∀ {n} (as : Vec ℕ n) (f g : ℂ n n) → (stretch f as) ⟫ (stretch g as) ≈⟦⟧ stretch (f ⟫ g) as
  ⟫-distrib {n} as f g = easy-≈⟦⟧ (VE.from-≡ ∘ helper)
    where
    open PropEq.≡-Reasoning
    helper : ∀ w → ⟦ (stretch f as) ⟫ (stretch g as) ⟧ w ≡ ⟦ stretch (f ⟫ g) as ⟧ w
    helper w = begin
      (⟦ stretch g as ⟧ ∘ ⟦ stretch f as ⟧) w
        ≡⟨ cong ⟦ stretch g as ⟧ (conv f as w) ⟩
      (⟦ stretch g as ⟧ ∘ ungroup ∘ extract-map ⟦ f ⟧ ∘ group 1 as) w
        ≡⟨ conv g as _ ⟩
      (ungroup ∘ extract-map ⟦ g ⟧ ∘ group 1 as ∘ ungroup ∘ extract-map ⟦ f ⟧ ∘ group 1 as) w
        ≡⟨ cong (ungroup ∘ extract-map ⟦ g ⟧) (ungroup-group-identity as ((extract-map ⟦ f ⟧ ∘ group 1 as) w)) ⟩
      (ungroup ∘ extract-map ⟦ g ⟧ ∘ extract-map ⟦ f ⟧ ∘ group 1 as) w
        ≡⟨ cong ungroup (extract-map-∘ ⟦ g ⟧ ⟦ f ⟧ (group 1 as w)) ⟩
      (ungroup ∘ extract-map ⟦ f ⟫ g ⟧ ∘ group 1 as) w
        ≡⟨ sym (conv (f ⟫ g) as w) ⟩
      ⟦ stretch (f ⟫ g) as ⟧ w
        ∎

  ∥-distrib : ∀ {n m} (as : Vec ℕ n) (bs : Vec ℕ m) (f : ℂ n n) (g : ℂ m m) →
    stretch (f ∥ g) (as ++ bs) ≈⟦⟧ (stretch f as) ∥ (stretch g bs)
  ∥-distrib {n} as bs f g = Mk≈⟦⟧ (pi as bs) helper
    where
    open PropEq.≡-Reasoning

    pi : ∀ {n m} (as : Vec ℕ n) (bs : Vec ℕ m) → size 1 (as ++ bs) ≡ size 1 as + size 1 bs
    pi [] bs = refl
    pi (a ∷ as) bs rewrite pi as bs = cong suc (sym (+-assoc a _ _))

    postulate
      split-group-commute : ∀ {A} i {m n} (as : Vec ℕ m) {bs : Vec ℕ n} →
        {xs : Vec A (size i (as ++ bs))} {ys : Vec A (size i as + size i bs)} →
        (p : xs VE.≈ ys) →
        (map× (group i as) (group i bs) ∘ splitAt' (size i as)) ys ≡ (splitᵍ as ∘ group i (as ++ bs)) xs
      extract-map-++-commute : ∀ {A i m n} (as : Vec ℕ m) {bs : Vec ℕ n} →
        (f₁ : Vec A m → Vec A m) (f₂ : Vec A n → Vec A n)→
        (gs : MinGroups A (suc i) (as ++ bs)) →
        extract-map (uncurry _++_ ∘ map× f₁ f₂ ∘ splitAt' m) gs ≡
          (uncurry _++ᵍ_ ∘ map× (extract-map f₁) (extract-map f₂) ∘ splitᵍ as) gs

    group-++-commute : ∀ {w₁ : W (size 1 (as ++ bs))} {w₂ : W (size 1 as + size 1 bs)} (w≈w : w₁ VE.≈ w₂) →
           (ungroup ∘ uncurry _++ᵍ_ ∘ map× (extract-map ⟦ f ⟧)
                                           (extract-map ⟦ g ⟧) ∘ splitᵍ as ∘ group 1 (as ++ bs)) w₁
             VE.≈
           (uncurry _++_ ∘ map× (ungroup ∘ extract-map ⟦ f ⟧ ∘ group 1 as)
                                (ungroup ∘ extract-map ⟦ g ⟧ ∘ group 1 bs) ∘ splitAt' (size 1 as)) w₂
    group-++-commute {w₁} {w₂} w≈w with split-group-commute 1 as w≈w
    ... | r rewrite sym r = uncurry ++-ungroup-commute ((map× (extract-map ⟦ f ⟧ ∘ group 1 as)
                                                              (extract-map ⟦ g ⟧ ∘ group 1 bs) ∘ splitAt' (size 1 as)) w₂)

    helper : stretch (f ∥ g) (as ++ bs) ≈e (stretch f as) ∥ (stretch g bs)
    helper {w₁} {w₂} w≈w with extract-map-++-commute as ⟦ f ⟧ ⟦ g ⟧ (group 1 (as ++ bs) w₁)
    ... | comm rewrite conv (f ∥ g) (as ++ bs) w₁
                     | conv f as (proj₁ (splitAt' (size 1 as) w₂))
                     | conv g bs (proj₂ (splitAt' (size 1 as) w₂))
                     | comm
                     = group-++-commute w≈w

--------------------------------------------------------------------------------

module With-⤙ = WithDirection ⤙-direction
module With-⤚ = WithDirection ⤚-direction

⤙-cong : ∀ {m n} {f : ℂ m m} {g : ℂ n n} {as : Vec ℕ m} {bs : Vec ℕ n} →
          f ≈⟦⟧ g → as VE.≈ bs → f ⤙ as ≈⟦⟧ g ⤙ bs
⤙-cong = With-⤙.stretch-cong

⤚-cong : ∀ {m n} {f : ℂ m m} {g : ℂ n n} {as : Vec ℕ m} {bs : Vec ℕ n} →
          f ≈⟦⟧ g → as VE.≈ bs → as ⤚ f ≈⟦⟧ bs ⤚ g
⤚-cong = With-⤚.stretch-cong

-- id{#x} ⤙ x ≡ id{Σx}
⤙-preserves-id : ∀ {n} (as : Vec ℕ n) →
                 id⤨ {n} ⤙ as ≈⟦⟧ id⤨ {size 1 as}
⤙-preserves-id = With-⤙.preserves-id

⤚-preserves-id : ∀ {n} (as : Vec ℕ n) →
                 as ⤚ id⤨ {n} ≈⟦⟧ id⤨ {size 1 as}
⤚-preserves-id = With-⤚.preserves-id

-- (f ⟫ g) ⤙ x ≡ f ⤙ x ⟫ g ⤙
⤙-⟫-distrib : ∀ {n} (xs : Vec ℕ n) (f g : ℂ n n) → (f ⤙ xs) ⟫ (g ⤙ xs) ≈⟦⟧ (f ⟫ g) ⤙ xs
⤙-⟫-distrib = With-⤙.⟫-distrib

-- x ⤚ (f ⟫ g) ≡ x ⤚ f ⟫ x ⤚ g
⤚-⟫-distrib : ∀ {n} (xs : Vec ℕ n) (f g : ℂ n n) → (xs ⤚ f) ⟫ (xs ⤚ g) ≈⟦⟧ xs ⤚ (f ⟫ g)
⤚-⟫-distrib = With-⤚.⟫-distrib


⤙-∥-distrib : ∀ {n m} (as : Vec ℕ n) (bs : Vec ℕ m) (f : ℂ n n) (g : ℂ m m) →
              (f ∥ g) ⤙ (as ++ bs) ≈⟦⟧ (f ⤙ as) ∥ (g ⤙ bs)
⤙-∥-distrib = With-⤙.∥-distrib

⤚-∥-distrib : ∀ {n m} (as : Vec ℕ n) (bs : Vec ℕ m) (f : ℂ n n) (g : ℂ m m) →
              (as ++ bs) ⤚ (f ∥ g) ≈⟦⟧ (as ⤚ f) ∥ (bs ⤚ g)
⤚-∥-distrib = With-⤚.∥-distrib

-- flip law
postulate
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

-- Derived stretch law 2
-- (f × id{#y-1}) ⤙ x ++ y = f ⤙ x ++ [Σy]
stretch-derived-2 : ∀ {n m} (f : ℂ (suc n) (suc n)) (xs : Vec ℕ n) (y : ℕ) (ys : Vec ℕ m) →
                    (f ∥ id⤨ {m}) ⤙ ((xs ∷ʳ y) ++ ys) ≈⟦⟧ (f ⤙ (xs ∷ʳ y + size 1 ys))
stretch-derived-2 {n} {m} f xs y ys = begin
  (f ∥ id⤨ {m}) ⤙ ((xs ∷ʳ y) ++ ys)
    ≈⟦⟧⟨ ⤙-∥-distrib (xs ∷ʳ y) ys f id⤨ ⟩
  f ⤙ (xs ∷ʳ y) ∥ id⤨ {m} ⤙ ys
    ≈⟦⟧⟨ ≈⟦⟧-refl ⟩
  f ⤙ (xs ∷ʳ y) ∥ id⤨ {m} ⤙ ys
    ≈⟦⟧⟨ ≈⟦⟧-cong (bla ∥● ●) (⤙-preserves-id ys) ⟩
  f ⤙ (xs ∷ʳ y) ∥ id⤨ {size 1 ys}
    ≈⟦⟧⟨ ≈⟦⟧-sym (stretch-derived-1 f xs) ⟩
  f ⤙ (xs ∷ʳ y + size 1 ys)
    ∎
  where
  open SimEq.≈⟦⟧-Reasoning
