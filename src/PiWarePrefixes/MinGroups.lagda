\begin{code}
module PiWarePrefixes.MinGroups where

open import Data.Fin as Fin using (Fin)
open import Data.Nat using (ℕ; zero; suc; _*_; _+_; _<_; s≤s)
open import Data.Nat.Properties as NP using (m≤m+n)
open import Data.Nat.Properties.Simple using (+-suc; +-right-identity; *-comm)
open import Data.Vec using (Vec; sum; []; _∷_) renaming (applicative to vec-applicative)
open import Function using (id; _$_; _∘′_; _⟨_⟩_)

open import Data.Fin using (toℕ)
open import Data.Nat.Properties.Simple using (+-assoc; +-comm)
open import Data.Product using (_,_; _×_; uncurry; <_,_>; proj₁; proj₂; ∃₂) renaming (zip to zip×; map to map×)
open import Data.Vec hiding (group)
open import Data.Vec.Extra
open import Function using (flip; _∘_)
open import Relation.Binary.PropositionalEquality
open import PiWarePrefixes.Utils

open Morphism using (op)

private
  import Data.Vec.Equality
  import Data.Vec.Properties
  module VE = Data.Vec.Equality.PropositionalEquality
  module VecPropEq {a} {A : Set a} = Data.Vec.Properties.UsingVectorEquality (Relation.Binary.PropositionalEquality.setoid A)

data MinGroups (A : Set) (i : ℕ) : ∀ {n} (as : Vec ℕ n) → Set where
  [] : MinGroups A i []
  _∷_ : ∀ {a n} {as : Vec ℕ n} (x : Vec A (i + a)) (g : MinGroups A i as) → MinGroups A i (a ∷ as)

size : ∀ (i : ℕ) {n} (as : Vec ℕ n) → ℕ
size i as = sum (map (_+_ i) as)

size-++ : ∀ {m n} (as : Vec ℕ m) (bs : Vec ℕ n) →
          size 1 (as ++ bs) ≡ size 1 as + size 1 bs
size-++ [] bs = refl
size-++ (a ∷ as) bs = cong (suc) (cong (_+_ a) (size-++ as bs)
                        ⟨ trans ⟩ sym (+-assoc a (size 1 as) (size 1 bs)))

group : ∀ {A} i {n} (as : Vec ℕ n) (xs : Vec A (size i as)) → MinGroups A i as
group i [] [] = []
group i (a ∷ as) = uncurry _∷_ ∘′ map× id (group i as) ∘ splitAt′ (i + a)

ungroup : ∀ {A i n} {as : Vec ℕ n} → MinGroups A i as → Vec A (size i as)
ungroup [] = []
ungroup (g ∷ gs) = g ++ (ungroup gs)

group-ungroup-identity : ∀ {A i n} (as : Vec ℕ n) (xs : Vec A (size i as)) → ungroup (group i as xs) ≡ xs
group-ungroup-identity [] [] = refl
group-ungroup-identity {i = i} (a ∷ as) xs with splitAt (i + a) xs
group-ungroup-identity {i = i} (a ∷ as) .(x ++ xs) | x , xs , refl with group-ungroup-identity {i = i} as xs
... | p rewrite p = refl

ungroup-group-identity : ∀ {A i n} (as : Vec ℕ n) (gs : MinGroups A i as) → group i as (ungroup gs) ≡ gs
ungroup-group-identity [] [] = refl
ungroup-group-identity {i = i} (a ∷ as) (g ∷ gs) with splitAt-++ _ g (ungroup gs)
                                                    | ungroup-group-identity as gs
... | split | rec rewrite split | rec = refl

----------------------------------------
-- Split and concat

-- mapᵍ : ∀ {A B i n} {as : Vec ℕ n} (f : ∀ {m} → Vec A m → Vec B m) →
--        MinGroups A i as → MinGroups B i as
-- mapᵍ f [] = []
-- mapᵍ f (g ∷ gs) = f g ∷ mapᵍ f gs

map-to-vec : ∀ {A B : Set} {i n} {as : Vec ℕ n} (f : ∀ {m} → Vec A (i + m) → B) →
             MinGroups A i as → Vec B n
map-to-vec f [] = []
map-to-vec f (g ∷ gs) = f g ∷ map-to-vec f gs

_++ᵍ_ : ∀ {A i m n} {as : Vec ℕ m} {bs : Vec ℕ n}
        (gs : MinGroups A i as) (hs : MinGroups A i bs) → MinGroups A i (as ++ bs)
[] ++ᵍ hs = hs
(g ∷ gs) ++ᵍ hs = g ∷ (gs ++ᵍ hs)

splitᵍ : ∀ {A i m n} (as : Vec ℕ m) {bs : Vec ℕ n}
            (gs : MinGroups A i (as ++ bs)) → MinGroups A i as × MinGroups A i bs
splitᵍ [] gs = [] , gs
splitᵍ (a ∷ as) (g ∷ gs) = map× (_∷_ g) id (splitᵍ as gs)

++-ungroup-commute : ∀ {A i m n} {as : Vec ℕ m} {bs : Vec ℕ n} →
  (gs : MinGroups A i as) (hs : MinGroups A i bs) →
  ungroup (gs ++ᵍ hs) VE.≈ ungroup gs ++ ungroup hs
++-ungroup-commute [] hs = VE.refl (ungroup hs)
++-ungroup-commute (g ∷ gs) hs = VE.trans ((VE.refl g) VE.++-cong (++-ungroup-commute gs hs)) (VE.sym (++-assoc g (ungroup gs) (ungroup hs)))

----------------------------------------

record ExtractInsert : Set₁ where
  field
    extf : ∀ {n} → Morphism (vec-functor (suc n)) (×-functor identity-functor (vec-functor n))
    insf : ∀ {n} → Morphism (×-functor identity-functor (vec-functor n)) (vec-functor (suc n))
    extf-insf-id : ∀ {A : Set} {n} (xs : Vec A (suc n)) → op insf (op extf xs) ≡ xs
    insf-extf-id : ∀ {A : Set} {n} (x : A × Vec A n) → op extf (op insf x) ≡ x


module WithExtractInsert (extract-insert : ExtractInsert) where
  open ExtractInsert extract-insert public

  extract : ∀ {A i n} {as : Vec ℕ n} → MinGroups A (suc i) as → Vec A n × MinGroups A i as
  extract [] = [] , []
  extract (g ∷ gs) = zip× _∷_ _∷_ (op extf g) (extract gs)
  
  insert : ∀ {A i n} {as : Vec ℕ n} → Vec A n → MinGroups A i as → MinGroups A (suc i) as
  insert [] [] = []
  insert (r ∷ rs) (g ∷ gs) = (op insf (r , g)) ∷ (insert rs gs)
  
  extract-insert-identity : ∀ {A i n} {as : Vec ℕ n} →
     (gs : MinGroups A (suc i) as) → uncurry insert (extract gs) ≡ gs
  extract-insert-identity [] = refl
  extract-insert-identity (g ∷ gs) = cong₂ _∷_ (extf-insf-id g) (extract-insert-identity gs)

  insert-extract-identity : ∀ {A i n} {as : Vec ℕ n} →
    (xs : Vec A n) (gs : MinGroups A i as) → extract (insert xs gs) ≡ xs , gs
  insert-extract-identity [] [] = refl
  insert-extract-identity (x ∷ xs) (g ∷ gs) rewrite insf-extf-id (x , g)
                                                  | insert-extract-identity xs gs = refl

  -- extract-map should be equal to something like: mapᵍ (op insf ∘ map× f id ∘ op extf)
  extract-map : ∀ {A i n} {as : Vec ℕ n} → (Vec A n → Vec A n) → MinGroups A (suc i) as → MinGroups A (suc i) as
  extract-map f = uncurry insert ∘ map× f id ∘ extract
  

  -- extract-map is a congruence

  extract-map-cong : ∀ {A : Set} {i n} {as : Vec ℕ n} →
                    {f h : Vec A n → Vec A n} → (∀ x → f x ≡ h x) →
                    (gs : MinGroups A (suc i) as) → extract-map f gs ≡ extract-map h gs
  extract-map-cong p gs rewrite p (proj₁ (extract gs)) = refl

  -- extract-map is functorial

  extract-map-id : ∀ {A i n} {as : Vec ℕ n} (gs : MinGroups A (suc i) as) →
                   extract-map id gs ≡ gs
  extract-map-id [] = refl
  extract-map-id (g ∷ gs) = cong₂ _∷_ (extf-insf-id g) (extract-map-id gs)

  extract-map-∘ : ∀ {A i n} {as : Vec ℕ n} (f h : Vec A n → Vec A n) (gs : MinGroups A (suc i) as) →
              extract-map f (extract-map h gs) ≡ extract-map (f ∘ h) gs
  extract-map-∘ f h gs rewrite uncurry insert-extract-identity (map× h id (extract gs)) = refl

  postulate
    -- This is why insf and extf have to be functor morphisms
    extract-map-++-commute : ∀ {A i m n} (as : Vec ℕ m) {bs : Vec ℕ n} →
      (f₁ : Vec A m → Vec A m) (f₂ : Vec A n → Vec A n)→
      (gs : MinGroups A (suc i) (as ++ bs)) →
      extract-map (uncurry _++_ ∘ map× f₁ f₂ ∘ splitAt′ m) gs ≡
        (uncurry _++ᵍ_ ∘ map× (extract-map f₁) (extract-map f₂) ∘ splitᵍ as) gs
\end{code}
