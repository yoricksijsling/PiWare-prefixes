module PiWarePrefixes.Utils where

open import Data.Fin using (Fin; zero; suc)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_,_; proj₁; proj₂; _×_) renaming (map to map×)
open import Data.Vec using (Vec; _++_; []; _∷_; [_]; splitAt; tabulate; _∷ʳ_; replicate; _⊛_)
                     renaming (map to mapᵥ)
open import Data.Vec.Properties using (∷-injective)
open import Function using (id; _∘_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)

private 
  import Data.Vec.Equality
  open module VE = Data.Vec.Equality.PropositionalEquality using ([]-cong; _∷-cong_; to-≡; from-≡)

-- ++-equal-parts : ∀ {m n} {A : Set} (xs ys : Vec A m) {us vs : Vec A n} (p : xs ++ us ≡ ys ++ vs) → xs ≡ ys × us ≡ vs
-- ++-equal-parts [] [] p = refl , p
-- ++-equal-parts (x ∷ xs) (y ∷ ys) p with VE.from-≡ p
-- ++-equal-parts (y ∷ xs) (.y ∷ ys) p | refl ∷-cong rest with ++-equal-parts xs ys (VE.to-≡ rest)
-- ++-equal-parts (y ∷ xs) (.y ∷ .xs) p | refl ∷-cong rest | refl , refl = refl , refl

-- ++-splitAt : ∀ {n m} {A : Set} (xs : Vec A n) (ys : Vec A m) → let s = splitAt n (xs ++ ys) in
--              xs ≡ proj₁ s ×
--              ys ≡ proj₁ (proj₂ s)
-- ++-splitAt {n} xs ys with splitAt n (xs ++ ys)
-- ++-splitAt xs ys | xs′ , ys′ , p with ++-equal-parts xs xs′ p
-- ++-splitAt xs ys | xs′ , ys′ , p | p₁ , p₂ = p₁ , p₂

split-++' : ∀ {a} {A : Set a} {n m} (ys ys' : Vec A n) (zs zs' : Vec A m)
            (p : ys ++ zs VE.≈ ys' ++ zs') → ys VE.≈ ys' × zs VE.≈ zs'
split-++' [] [] zs zs' zs≈zs' = []-cong , zs≈zs'
split-++' (y ∷ ys) (y' ∷ ys') zs zs' (y≈y' ∷-cong rest) with split-++' ys ys' zs zs' rest
split-++' (y ∷ ys) (y' ∷ ys') zs zs' (y≈y' ∷-cong rest) | ys≈ys' , zs≈zs' = y≈y' ∷-cong ys≈ys' , zs≈zs'

split-++ : ∀ {a} {A : Set a} {n m} (ys ys' : Vec A n) (zs zs' : Vec A m)
      (p : ys ++ zs ≡ ys' ++ zs') → ys ≡ ys' × zs ≡ zs'
split-++ ys ys' zs zs' p = map× to-≡ to-≡ (split-++' ys ys' zs zs' (from-≡ p))

splitAt-++ : ∀ {a} {A : Set a} {n m} (ys : Vec A n) (zs : Vec A m) → splitAt n (ys ++ zs) ≡ ys , zs , refl
splitAt-++ {n = n} ys zs with splitAt n (ys ++ zs)
splitAt-++ ys zs | ys' , zs' , p with split-++ ys ys' zs zs' p | p
splitAt-++ ys zs | .ys , .zs , p | refl , refl | refl = refl

tabulate-extensionality : ∀ {n} {r : Set} {f g : Fin n → r} →
  (∀ x → f x ≡ g x) → tabulate f ≡ tabulate g
tabulate-extensionality {zero} p = refl
tabulate-extensionality {suc n} p rewrite p zero | (tabulate-extensionality (p ∘ suc)) = refl

++-assoc : ∀ {A : Set} {#xs #ys #zs} (xs : Vec A #xs) (ys : Vec A #ys) (zs : Vec A #zs) →
           (xs ++ ys) ++ zs VE.≈ xs ++ ys ++ zs
++-assoc [] ys zs = VE.refl (ys ++ zs)
++-assoc (x ∷ xs) ys zs = refl ∷-cong ++-assoc xs ys zs

∷ʳ-injective : ∀ {a n} {A : Set a} {x y : A} (xs ys : Vec A n) →
               (xs ∷ʳ x) ≡ (ys ∷ʳ y) → xs ≡ ys × x ≡ y
∷ʳ-injective [] [] refl = refl , refl
∷ʳ-injective {x = x'} {y'} (x ∷ xs) (y ∷ ys) p with ∷-injective p
∷ʳ-injective {x = x'} {y'} (x ∷ xs) (y ∷ ys) p | x=y , p' = map× (cong₂ _∷_ x=y) id (∷ʳ-injective xs ys p')

++-∷ʳ : ∀ {a n} {A : Set a} (xs : Vec A n) (x : A) →
        xs ∷ʳ x VE.≈ xs ++ (x ∷ [])
++-∷ʳ [] x = VE.refl [ x ]
++-∷ʳ (y ∷ ys) x = refl ∷-cong (++-∷ʳ ys x)

map-replicate : ∀ {n} {A B : Set} (f : A → B) (x : A) → mapᵥ f (replicate {n = n} x) ≡ replicate (f x)
map-replicate {zero} f x = refl
map-replicate {suc n} f x = cong (_∷_ (f x)) (map-replicate f x)


--------------------------------------------------------------------------------
-- Functor morphisms

open import Category.Functor
import Category.Applicative.Indexed as AI
import Level
open import Data.Product renaming (map to map×)
open import Data.Vec renaming (applicative to vec-applicative)
open import Data.Unit using (⊤)
open import Function using (id; _$_)

record Morphism {ℓ} {F₁ F₂ : Set ℓ → Set ℓ}
                (A : RawFunctor F₁) (B : RawFunctor F₂) : Set (Level.suc ℓ) where
  module A = RawFunctor A
  module B = RawFunctor B
  field
    op : ∀ {X} → F₁ X → F₂ X
    op-<$> : ∀ {X Y} (f : X → Y) (x : F₁ X) →
             op (f A.<$> x) ≡ f B.<$> op x

open RawFunctor
open Morphism
open AI.RawIApplicative using (rawFunctor)

FM-∘ : ∀ {ℓ} {F₁ F₂ F₃ : Set ℓ → Set ℓ}
       {A : RawFunctor F₁} {B : RawFunctor F₂} {C : RawFunctor F₃} →
       Morphism B C → Morphism A B → Morphism A C
FM-∘ {A = A} {B} {C} M₁ M₂ = record { op = op M₁ ∘ op M₂ ; op-<$> = ∘-<$> }
  where
  ∘-<$> : ∀ {X Y} (f : X → Y) x →
          (op M₁ (op M₂ (_<$>_ A f x))) ≡ _<$>_ C f (op M₁ (op M₂ x))
  ∘-<$> f x rewrite op-<$> M₂ f x = op-<$> M₁ f (op M₂ x)

AM-to-FM : ∀ {f} {F₁ F₂ : AI.IFun ⊤ f}
         {A : AI.RawIApplicative F₁} {B : AI.RawIApplicative F₂} →
         AI.Morphism A B → Morphism (rawFunctor A) (rawFunctor B)
AM-to-FM M = record { op = AI.Morphism.op M ; op-<$> = AI.Morphism.op-<$> M }

identity-functor : ∀ {ℓ} → RawFunctor (id)
identity-functor {ℓ} = record { _<$>_ = _$_ {a = ℓ} }

×-functor : ∀ {ℓ} {F₁ F₂ : Set ℓ → Set ℓ} →
            (A : RawFunctor F₁) (B : RawFunctor F₂) → RawFunctor (λ x → F₁ x × F₂ x)
×-functor A B = record { _<$>_ = λ f → map× (_<$>_ A f) (_<$>_ B f) }

vec-functor : ∀ {ℓ} n → RawFunctor (λ (x : Set ℓ) → Vec x n)
vec-functor {ℓ} n = rawFunctor (vec-applicative {ℓ} {n})

-- vec-morphism : ∀ {a} → ℕ → ℕ → Set _
-- vec-morphism {a} i o = Morphism (vec-functor {a} i) (vec-functor {a} o)
