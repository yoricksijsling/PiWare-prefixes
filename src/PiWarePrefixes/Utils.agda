module PiWarePrefixes.Utils where

open import Data.Fin using (Fin; zero; suc)
open import Data.Nat using (zero; suc)
open import Data.Product using (_,_; proj₁; proj₂; _×_) renaming (map to map×)
open import Data.Vec using (Vec; _++_; []; _∷_; splitAt; tabulate)
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

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
