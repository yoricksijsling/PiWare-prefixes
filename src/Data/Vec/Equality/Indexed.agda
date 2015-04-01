module Data.Vec.Equality.Indexed where

open import Data.Product hiding (map)
open import Data.Vec
open import Data.Nat using (suc)
open import Function
open import Level using (_⊔_)
import Relation.Binary as RB
open import Relation.Binary.Indexed
open import Relation.Binary.PropositionalEquality as P using (_≡_)

module Equality {i} {I : Set i} {s₁ s₂} (S : Setoid I s₁ s₂) where

  private
    open module SS = Setoid S
      using () renaming (_≈_ to _≊_; Carrier to A)

  infix 4 _≈_

  data _≈_ : ∀ {n¹} → Vec (∃ A) n¹ →
             ∀ {n²} → Vec (∃ A) n² → Set (s₁ ⊔ s₂ ⊔ i) where
    []-cong  : [] ≈ []
    _∷-cong_ : ∀ {i¹} {x¹ : A i¹} {n¹} {xs¹ : Vec (∃ A) n¹}
                 {i²} {x² : A i²} {n²} {xs² : Vec (∃ A) n²}
                 (x¹≈x² : x¹ ≊ x²) (xs¹≈xs² : xs¹ ≈ xs²) →
                 (i¹ , x¹) ∷ xs¹ ≈ (i² , x²) ∷ xs²

  length-equal : ∀ {n¹} {xs¹ : Vec (∃ A) n¹}
                   {n²} {xs² : Vec (∃ A) n²} →
                 xs¹ ≈ xs² → n¹ ≡ n²
  length-equal []-cong        = P.refl
  length-equal (_ ∷-cong eq₂) = P.cong suc $ length-equal eq₂

  refl : ∀ {n} (xs : Vec (∃ A) n) → xs ≈ xs
  refl []       = []-cong
  refl (x ∷ xs) = SS.refl ∷-cong refl xs

  sym : ∀ {n m} {xs : Vec (∃ A) n} {ys : Vec (∃ A) m} →
        xs ≈ ys → ys ≈ xs
  sym []-cong                = []-cong
  sym (x¹≡x² ∷-cong xs¹≈xs²) = SS.sym x¹≡x² ∷-cong sym xs¹≈xs²

  trans : ∀ {n m l} {xs : Vec (∃ A) n} {ys : Vec (∃ A) m} {zs : Vec (∃ A) l} →
          xs ≈ ys → ys ≈ zs → xs ≈ zs
  trans []-cong            []-cong            = []-cong
  trans (x≈y ∷-cong xs≈ys) (y≈z ∷-cong ys≈zs) =
    SS.trans x≈y y≈z ∷-cong trans xs≈ys ys≈zs

  _++-cong_ : ∀ {n₁¹ n₂¹} {xs₁¹ : Vec (∃ A) n₁¹} {xs₂¹ : Vec (∃ A) n₂¹}
                {n₁² n₂²} {xs₁² : Vec (∃ A) n₁²} {xs₂² : Vec (∃ A) n₂²} →
              xs₁¹ ≈ xs₁² → xs₂¹ ≈ xs₂² →
              xs₁¹ ++ xs₂¹ ≈ xs₁² ++ xs₂²
  []-cong          ++-cong eq₃ = eq₃
  (eq₁ ∷-cong eq₂) ++-cong eq₃ = eq₁ ∷-cong (eq₂ ++-cong eq₃)

  -- Extra properties
  ++-∷ʳ : ∀ {n} (xs : Vec (∃ A) n) (x : ∃ A) →
          xs ∷ʳ x ≈ xs ++ (x ∷ [])
  ++-∷ʳ [] x = refl [ x ]
  ++-∷ʳ (y ∷ ys) x = SS.refl ∷-cong (++-∷ʳ ys x)

  map-++-commute : ∀ {b m n} {B : I → Set b}
                   (f : (∃ B) → ∃ A) (xs : Vec (∃ B) m) {ys : Vec (∃ B) n} →
                   map f (xs ++ ys) ≈ map f xs ++ map f ys
  map-++-commute f []       = refl _
  map-++-commute f (x ∷ xs) = SS.refl ∷-cong map-++-commute f xs

module PropositionalEquality {i} {I : Set i} {a} {A : I → Set (a ⊔ i)} where
  open import Function.Equality

  s : Setoid I (a ⊔ i) (a ⊔ i)
  s = record
    { Carrier = A
    ; _≈_ = λ {i} {j} x y → (i , x) ≡ (j , y)
    ; isEquivalence = record
      { refl = P.refl
      ; sym = P.sym
      ; trans = P.trans
      }
    }
  
  open Equality s public

  to-≡ : ∀ {n} {xs ys : Vec (∃ A) n} → xs ≈ ys → xs ≡ ys
  to-≡ []-cong                 = P.refl
  to-≡ (P.refl ∷-cong xs¹≈xs²) = P.cong (_∷_ _) $ to-≡ xs¹≈xs²

  from-≡ : ∀ {n} {xs ys : Vec (∃ A) n} → xs ≡ ys → xs ≈ ys
  from-≡ P.refl = refl _
