module PiWarePrefixes.MinGroups where

open import Category.Applicative using (RawApplicative; module RawApplicative)
open import Data.Fin as Fin using (Fin)
open import Data.Nat using (ℕ; zero; suc; _*_; _+_; _<_; s≤s)
open import Data.Nat.Properties as NP using (m≤m+n)
open import Data.Nat.Properties.Simple using (+-suc; +-right-identity; *-comm)
open import Data.Vec using (Vec; sum; []; _∷_) renaming (applicative to vec-applicative)
open import Function using (id; _$_; _∘′_)

open import Data.Fin using (toℕ)
open import Data.Nat.Properties.Simple using (+-assoc; +-comm)
open import Data.Product using (_,_; _×_; uncurry; <_,_>; proj₁; proj₂; ∃₂) renaming (zip to zip×; map to map×)
open import Data.Vec hiding (group)
open import Data.Vec.Extra
open import Function using (flip; _∘_)
open import Relation.Binary.PropositionalEquality
open import PiWarePrefixes.Utils


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

group : ∀ {A} i {n} (as : Vec ℕ n) (xs : Vec A (size i as)) → MinGroups A i as
group i [] [] = []
group i (a ∷ as) = uncurry _∷_ ∘′ map× id (group i as) ∘ splitAt' (i + a)

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
ungroup-group-identity {i = i} (a ∷ as) (g ∷ gs) with splitAt-++ g (ungroup gs)
                                                    | ungroup-group-identity as gs
... | split | rec rewrite split | rec = refl

----------------------------------------
-- Split and concat

_++ᵍ_ : ∀ {A i m n} {as : Vec ℕ m} {bs : Vec ℕ n}
        (gs : MinGroups A i as) (hs : MinGroups A i bs) → MinGroups A i (as ++ bs)
[] ++ᵍ hs = hs
(g ∷ gs) ++ᵍ hs = g ∷ (gs ++ᵍ hs)

splitᵍ : ∀ {A i m n} (as : Vec ℕ m) {bs : Vec ℕ n}
            (gs : MinGroups A i (as ++ bs)) → MinGroups A i as × MinGroups A i bs
splitᵍ [] gs = [] , gs
splitᵍ (a ∷ as) (g ∷ gs) = map× (_∷_ g) id (splitᵍ as gs)

open import Relation.Binary using (Setoid; module Setoid)

-- module Equality (S : Setoid {!!} {!!}) where
--   private
--     open module SS = Setoid S
--       using () renaming (_≈_ to _≊_; Carrier to A)

--   infix 4 _≈_
--   data _≈_ {i¹ i² : ℕ} : ∀ {n¹} {as¹ : Vec ℕ n¹} (gs¹ : MinGroups A i¹ as¹) →
--                          ∀ {n²} {as² : Vec ℕ n²} (gs² : MinGroups A i² as²) → Set where
--     []-cong : [] ≈ []
--     _∷-cong_ : ∀ {a¹ n¹} {as¹ : Vec ℕ n¹} {g¹ : Vec A (i¹ + a¹)} {gs¹ : MinGroups A i¹ as¹} →
--                ∀ {a² n²} {as² : Vec ℕ n²} {g² : Vec A (i² + a²)} {gs² : MinGroups A i² as²} →
--                (g≈g : g¹ VE.≈ g²) → (gs≈gs : gs¹ ≈ gs²) →
--                g¹ ∷ gs¹ ≈ g² ∷ gs²

-- postulate
-- split-group-commute i [] p with VE.to-≡ p
-- split-group-commute i [] p | refl = refl
-- split-group-commute i (a ∷ as) {xs = xs} {ys} p with splitAt (i + a) xs
-- split-group-commute i (a ∷ as) {xs = .(x' ++ xs')} {ys} p | x' , xs' , refl = {!!}

++-ungroup-commute : ∀ {A i m n} {as : Vec ℕ m} {bs : Vec ℕ n} →
  (gs : MinGroups A i as) (hs : MinGroups A i bs) →
  ungroup (gs ++ᵍ hs) VE.≈ ungroup gs ++ ungroup hs
++-ungroup-commute [] hs = VE.refl (ungroup hs)
++-ungroup-commute (g ∷ gs) hs = VE.trans ((VE.refl g) VE.++-cong (++-ungroup-commute gs hs)) (VE.sym (++-assoc g (ungroup gs) (ungroup hs)))

-- sg : ∀ {A} i {m n} (as : Vec ℕ m) {bs : Vec ℕ n} →
--   (f : MinGroups A i as × MinGroups A i bs → MinGroups A i as × MinGroups A i bs) →
--   {xs : Vec A (size i (as ++ bs))} {ys : Vec A (size i as + size i bs)} →
--   (xs VE.≈ ys) →
--   (ungroup ∘ uncurry _++ᵍ_ ∘ f ∘ splitᵍ as ∘ group i (as ++ bs)) xs
--     VE.≈ (uncurry _++_ ∘ map× ungroup ungroup ∘ f ∘ map× (group i as) (group i bs) ∘ splitAt' (size i as)) ys
-- sg i as {bs} f {xs} {ys} p rewrite split-group-commute i as p = uncurry ++-ungroup-commute (f _)

----------------------------------------

minGroups-applicative : ∀ (i : ℕ) {n} (as : Vec ℕ n) → RawApplicative (λ A → MinGroups A i as)
minGroups-applicative i as = record
  { pure = minGroups-pure i as
  ; _⊛_ = minGroups-⊛ i as
  }
  where
  minGroups-pure : ∀ (i : ℕ) {n} (as : Vec ℕ n) → {A : Set} → A → MinGroups A i as
  minGroups-pure i [] x = []
  minGroups-pure i (a ∷ as) x = (replicate x) ∷ (minGroups-pure i as x)
  minGroups-⊛ : ∀ (i : ℕ) {n} (as : Vec ℕ n) → {A B : Set} →
                MinGroups (A → B) i as → MinGroups A i as → MinGroups B i as
  minGroups-⊛ i [] [] [] = []
  minGroups-⊛ i (a ∷ as) (f ∷ fs) (x ∷ xs) = (f ⊛ x) ∷ (minGroups-⊛ i as fs xs)

----------------------------------------

record ExtractInsert : Set₁ where
  field
    extf : ∀ {A n} → Vec A (suc n) → A × Vec A n
    insf : ∀ {A n} → A → Vec A n → Vec A (suc n)
    extf-insf-id : ∀ {A : Set} {n} (xs : Vec A (suc n)) → uncurry insf (extf xs) ≡ xs
    insf-extf-id : ∀ {A : Set} {n} (x : A) (xs : Vec A n) → extf (insf x xs) ≡ x , xs

module WithExtractInsert (extract-insert : ExtractInsert) where
  open ExtractInsert extract-insert public

  extract : ∀ {A i n} {as : Vec ℕ n} → MinGroups A (suc i) as → Vec A n × MinGroups A i as
  extract [] = [] , []
  extract (g ∷ gs) = zip× _∷_ _∷_ (extf g) (extract gs)
  
  insert : ∀ {A i n} {as : Vec ℕ n} → Vec A n → MinGroups A i as → MinGroups A (suc i) as
  insert [] [] = []
  insert (r ∷ rs) (g ∷ gs) = (insf r g) ∷ (insert rs gs)
  
  extract-insert-identity : ∀ {A i n} {as : Vec ℕ n} →
     (gs : MinGroups A (suc i) as) → uncurry insert (extract gs) ≡ gs
  extract-insert-identity [] = refl
  extract-insert-identity (g ∷ gs) = cong₂ _∷_ (extf-insf-id g) (extract-insert-identity gs)

  insert-extract-identity : ∀ {A i n} {as : Vec ℕ n} →
    (xs : Vec A n) (gs : MinGroups A i as) → extract (insert xs gs) ≡ xs , gs
  insert-extract-identity [] [] = refl
  insert-extract-identity (x ∷ xs) (g ∷ gs) rewrite insf-extf-id x g
                                                  | insert-extract-identity xs gs = refl

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
    extract-map-split : ∀ {A i m n}
      (as : Vec ℕ m) {bs : Vec ℕ n} →
      (f₁ : Vec A m → Vec A m) (f₂ : Vec A n → Vec A n)→
      (gs : MinGroups A (suc i) (as ++ bs)) →
      extract-map (uncurry _++_ ∘ map× f₁ f₂ ∘ splitAt' m) gs ≡
        (uncurry _++ᵍ_ ∘ map× (extract-map f₁) (extract-map f₂) ∘ splitᵍ as) gs

  -- extract-map-split f₁ f₂ gs = {!!}
  -- extract-map-++ {as = []} f₁ f₂ gs with f₁ []
  -- extract-map-++ {as = []} f₁ f₂ gs | [] = refl
  -- extract-map-++ {as = a ∷ as} f₁ f₂ (g ∷ gs) with extract-map-++ f₁ f₂ gs
  -- ... | rec = {!!}

  -- extract-map-split : ∀ {A i m n}
  --   (as : Vec ℕ m) (bs : Vec ℕ n) →
  --   (f : Vec A m → Vec A m) (g : Vec A n → Vec A n) →
  --   ∀ w₁ w₂ (w≈w : w₁ VE.≈ w₂) →
  --   (ungroup ∘′ extract-map (uncurry _++_ ∘′ map× f g ∘′ splitAt' m) ∘′ group (suc i) (as ++ bs)) w₁
  --   VE.≈ (uncurry _++_ ∘′
  --        map× (ungroup ∘′ extract-map f ∘′ group (suc i) as)
  --             (ungroup ∘′ extract-map g ∘′ group (suc i) bs) ∘′ splitAt' (size (suc i) as)) w₂
  -- extract-map-split as bs f g w₁ w₂ w≈w = {!!}

  -- Can't case split on as, because f and g only work on the whole vec.

  -- extract-map-split [] bs f g w₁ w₂ w≈w with f [] | VE.to-≡ w≈w
  -- extract-map-split [] bs f g w₁ .w₁ w≈w | [] | refl = VE.refl _

  -- extract-map-split (a ∷ as) bs f g ._ ._ (x¹≈x² Data.Vec.Equality.Equality.∷-cong w≈w)
  --   with extract-map-split as bs f g _ _ w≈w
  -- ... | cc = {!!}
