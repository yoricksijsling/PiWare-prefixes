module PiWarePrefixes.Utils where

open import Data.Product using (_,_; proj₁; proj₂; _×_) renaming (map to map×)
open import Data.Vec using (Vec; _++_; []; _∷_; splitAt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

import Data.Vec.Equality
open module PE = Data.Vec.Equality.PropositionalEquality using ([]-cong; _∷-cong_; to-≡; from-≡)

split-++' : ∀ {A : Set} {n m} (ys ys' : Vec A n) (zs zs' : Vec A m)
            (p : ys ++ zs PE.≈ ys' ++ zs') → ys PE.≈ ys' × zs PE.≈ zs'
split-++' [] [] zs zs' zs≈zs' = []-cong , zs≈zs'
split-++' (y ∷ ys) (y' ∷ ys') zs zs' (y≈y' ∷-cong rest) with split-++' ys ys' zs zs' rest
split-++' (y ∷ ys) (y' ∷ ys') zs zs' (y≈y' ∷-cong rest) | ys≈ys' , zs≈zs' = y≈y' ∷-cong ys≈ys' , zs≈zs'

split-++ : ∀ {A : Set} {n m} (ys ys' : Vec A n) (zs zs' : Vec A m)
      (p : ys ++ zs ≡ ys' ++ zs') → ys ≡ ys' × zs ≡ zs'
split-++ ys ys' zs zs' p = map× to-≡ to-≡ (split-++' ys ys' zs zs' (from-≡ p))

splitAt-++ : ∀ {A : Set} n {m} (ys : Vec A n) (zs : Vec A m) → splitAt n (ys ++ zs) ≡ ys , zs , refl
splitAt-++ n ys zs with splitAt n (ys ++ zs)
splitAt-++ n ys zs | ys' , zs' , p with split-++ ys ys' zs zs' p | p
splitAt-++ n ys zs | .ys , .zs , p | refl , refl | refl = refl
