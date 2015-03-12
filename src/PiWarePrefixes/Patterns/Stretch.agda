open import PiWare.Atom using (Atomic; module Atomic)
open import PiWare.Gates using (Gates)

module PiWarePrefixes.Patterns.Stretch {At : Atomic} (Gt : Gates At) where

open import Category.Applicative using (RawApplicative; module RawApplicative)
open import Category.Applicative.Indexed using (Morphism; module Morphism; IFun; RawIApplicative; module RawIApplicative)
open import Data.Fin as Fin using (Fin; toℕ)
open import Data.Nat using (ℕ; zero; suc; _*_; _+_; _<_; s≤s)
open import Data.Nat.Properties as NP using (m≤m+n)
open import Data.Nat.Properties.Simple using (+-suc; +-right-identity; +-assoc; +-comm; *-comm)
open import Data.Product renaming (zip to zip×; map to map×)
open import Data.Vec renaming (applicative to vec-applicative) hiding (group)
open import Data.Vec.Extra
open import Data.Vec.Properties as VecProps
open import Function using (id; _$_; flip; const; _∘_; _∘′_)
open import Relation.Binary.PropositionalEquality

open import PiWare.Circuit Gt using (ℂ; 𝐂; Plug; _⟫_; _∥_)
open import PiWarePrefixes.MinGroups as MinGroups
open import PiWare.Patterns Gt using (parsN)
open import PiWarePrefixes.Permutation as P using (Perm; _§_; ε; _◀_; _*)
open import PiWare.Plugs Gt using (id⤨)
open import PiWarePrefixes.Plugs.Core Gt
open import PiWare.Simulation Gt using (⟦_⟧)
open import PiWarePrefixes.Utils

open Atomic At using (W; Atom)
open Morphism using (op; op-pure; op-⊛; op-<$>)

private
  import Data.Vec.Equality
  import Data.Vec.Properties
  module VE = Data.Vec.Equality.PropositionalEquality
  module VecPropEq {a} {A : Set a} = Data.Vec.Properties.UsingVectorEquality (Relation.Binary.PropositionalEquality.setoid A)


module WithDirection (extract-insert : ExtractInsert) where
  open MinGroups.WithExtractInsert extract-insert
  
  in-table : ∀ {A : Set} {n} (as : Vec ℕ n) →
             Vec A (size 1 as) → Vec A (n + size 0 as)
  in-table as = uncurry _++_ ∘ map× id ungroup ∘ extract ∘ group 1 as

  in-M : ∀ {n} (as : Vec ℕ n) → vec-morphism (size 1 as) (n + size 0 as)
  in-M as = record
    { op = in-table as
    ; op-pure = in-pure as
    ; op-⊛ = in-⊛ as
    }
    where
    postulate
      in-pure : ∀ {n} (as : Vec ℕ n) {X : Set} (x : X) → in-table as (replicate x) ≡ replicate x
      in-⊛ : ∀ {n} (as : Vec ℕ n) {X Y : Set} (fs : Vec (X → Y) (size 1 as)) (xs : Vec (X) (size 1 as)) →
        in-table as (fs ⊛ xs) ≡ in-table as fs ⊛ in-table as xs

  in-⤨ : ∀ {n} (as : Vec ℕ n) → 𝐂 (size 1 as) (n + size 0 as)
  in-⤨ as = plug-M (in-M as)
  
  out-table : ∀ {A : Set} {n} (as : Vec ℕ n) →
               Vec A (n + size 0 as) → Vec A (size 1 as)
  out-table {n = n} as = ungroup ∘ uncurry insert ∘ map× id (group 0 as) ∘ splitAt' n
  
  out-M : ∀ {n} (as : Vec ℕ n) → vec-morphism (n + size 0 as) (size 1 as)
  out-M as = record
    { op = out-table as
    ; op-pure = out-pure as
    ; op-⊛ = out-⊛ as
    }
    where
    postulate
      out-pure : ∀ {n} (as : Vec ℕ n) {X : Set} (x : X) → out-table as (replicate x) ≡ replicate x
      out-⊛ : ∀ {n} (as : Vec ℕ n) {X Y : Set} (fs : Vec (X → Y) (n + size 0 as)) (xs : Vec (X) (n + size 0 as)) →
          out-table as (fs ⊛ xs) ≡ out-table as fs ⊛ out-table as xs
  
  out-⤨ : ∀ {n} (as : Vec ℕ n) → 𝐂 (n + size 0 as) (size 1 as)
  out-⤨ as = plug-M (out-M as)
  
  stretch : ∀ {n cs} → ℂ {cs} n n → (as : Vec ℕ n) → ℂ {cs} (size 1 as) (size 1 as)
  stretch {n} c as = in-⤨ as
                   ⟫ c ∥ id⤨
                   ⟫ out-⤨ as

  out-in-table-identity : ∀ {n} (as : Vec ℕ n) {A} (xs : Vec A (size 1 as)) →
                          out-table as (in-table as xs) ≡ xs
  out-in-table-identity {n} as xs with splitAt-++ (proj₁ (extract (group 1 as xs)))
                                                  (ungroup (proj₂ (extract (group 1 as xs))))
                                     | ungroup-group-identity as (proj₂ (extract (group 1 as xs)))
  ... | s | p rewrite s | p = begin
    ungroup (uncurry insert (extract (group 1 as xs)))
      ≡⟨ cong ungroup (extract-insert-identity (group 1 as xs)) ⟩
    ungroup (group 1 as xs)
      ≡⟨ group-ungroup-identity as xs ⟩
    xs
      ∎
    where
    open Relation.Binary.PropositionalEquality.≡-Reasoning

  IdentityApplicative : ∀ {f} → RawApplicative {f = f} id
  IdentityApplicative = RawMonad.rawIApplicative IdentityMonad
    where
    open import Category.Monad
    open import Category.Monad.Identity

  conv : ∀ {n} (f : ℂ n n) (as : Vec ℕ n) (w : W (size 1 as)) → ⟦ stretch f as ⟧ w ≡ (ungroup ∘ (extract-map ⟦ f ⟧) ∘ (group 1 as)) w
  conv {n} f as w = begin
    (⟦ out-⤨ as ⟧ $ ⟦ f ∥ id⤨ ⟧ $ ⟦ in-⤨ as ⟧ w)
      ≡⟨ expand-plugs ⟩
    (out-table as ∘ ⟦ f ∥ id⤨ ⟧ ∘ in-table as) w
      ≡⟨ cong (out-table as) (expand-par (in-table as w)) ⟩
    (ungroup ∘ uncurry insert ∘ map× id (group 0 as) ∘ splitAt' n ∘
       uncurry′ _++_ ∘ map× ⟦ f ⟧ id ∘ splitAt' _ ∘
       uncurry _++_ ∘ map× id ungroup ∘ extract ∘ group 1 as) w
      ≡⟨ cong (ungroup ∘ uncurry insert ∘ map× id (group 0 as)) (splitAt'-++ (cong (map× ⟦ f ⟧ id) (splitAt'-++ refl))) ⟩
    (ungroup ∘ uncurry insert ∘ map× ⟦ f ⟧ (group 0 as ∘ ungroup) ∘ extract ∘ group 1 as) w
      ≡⟨ cong (ungroup ∘ uncurry insert) (map×-from-to (extract (group 1 as w))) ⟩
    (ungroup ∘ extract-map ⟦ f ⟧ ∘ group 1 as) w
      ∎
    where
    open Relation.Binary.PropositionalEquality.≡-Reasoning
    expand-plugs : (⟦ out-⤨ as ⟧ ∘ ⟦ f ∥ id⤨ ⟧ ∘ ⟦ in-⤨ as ⟧) w ≡ (out-table as ∘ ⟦ f ∥ id⤨ ⟧ ∘ in-table as) w
    expand-plugs with plug-M-⟦⟧ (out-M as) (⟦ f ∥ id⤨ ⟧ (⟦ in-⤨ as ⟧ w))
                    | plug-M-⟦⟧ (in-M as) w
    ... | r1 | r2 rewrite r1 | r2  = refl
    expand-par : ∀ (w : W (n + size 0 as)) → ⟦ f ∥ id⤨ ⟧ w ≡ (uncurry′ _++_ ∘ map× ⟦ f ⟧ id ∘ splitAt' _) w
    expand-par w rewrite tabulate∘lookup (proj₂ (splitAt' n w)) = refl
    map×-from-to : (x : W n × MinGroups Atom 0 as) → (map× {Q = const (MinGroups Atom 0 as)} ⟦ f ⟧ (group 0 as ∘ ungroup)) x ≡ map× ⟦ f ⟧ id x
    map×-from-to (w' , gs) rewrite ungroup-group-identity as gs = refl
    splitAt'-++ : ∀ {A : Set} {m n} {x y : Vec A m × Vec A n} (p : x ≡ y) → splitAt' m (uncurry′ _++_ x) ≡ y
    splitAt'-++ {x = xs , ys} p rewrite splitAt-++ xs ys = p
  



  -- out-in-identity-M : ∀ {n} (as : Vec ℕ n) → M-∘ 

  -- out-in-identity : ∀ {n} (as : Vec ℕ n) i → in-⤪ as (out-⤪ as i) ≡ i
  -- out-in-identity {n} as i = begin
  --   in-⤪ as (lookup i (out-table as _))
  --     ≡⟨ ? ⟩
  --   lookup i _
  --     ≡⟨ lookup-allFin i ⟩
  --   i
  --     ∎
  --   where
  --   open Relation.Binary.PropositionalEquality.≡-Reasoning
    --   ≡⟨ sym (op-<$> (lookup-out-morphism as i) (in-⤪ as) _) ⟩
    -- lookup i (out-table as (map (in-⤪ as) _))
    --   ≡⟨⟩
    -- lookup i (out-table as (map (flip lookup (in-table as _)) _))
    --   ≡⟨ cong (lookup i ∘ out-table as) (map-lookup-allFin (in-table as _)) ⟩
    -- lookup i (out-table as (in-table as _))
    --   ≡⟨ cong (lookup i) (out-in-table-identity as _) ⟩
    -- lookup i _
    --   ≡⟨ lookup-allFin i ⟩
    -- i
    --   ∎
    -- where
    -- open Relation.Binary.PropositionalEquality.≡-Reasoning









--   --------------------------------------------------------------------------------
--   -- Lots of applicatives
  
--   ×-applicative : ∀ {i f} {I : Set i} {F₁ F₂ : IFun I f}
--                   (A₁ : RawIApplicative F₁) (A₂ : RawIApplicative F₂) →
--                   RawIApplicative (λ i j x → F₁ i j x × F₂ i j x)
--   ×-applicative {F₁ = F₁} {F₂} A₁ A₂ = record
--     { pure = < A₁.pure , A₂.pure >
--     -- ; _⊛_ = λ { (f₁ , f₂) (x₁ , x₂) → (f₁ A₁.⊛ x₁) , (f₂ A₂.⊛ x₂) }
--     ; _⊛_ = zip× A₁._⊛_ A₂._⊛_
--     }
--     where
--     module A₁ = RawIApplicative A₁
--     module A₂ = RawIApplicative A₂

--   ++-pure : ∀ m {n ℓ} {X : Set ℓ} → (x : X) → replicate {n = m} x ++ replicate {n = n} x ≡ replicate {n = m + n} x
--   ++-pure zero x = refl
--   ++-pure (suc m) x = cong (_∷_ _) (++-pure m x)
  
--   ++-⊛ : ∀ {m n ℓ} {X Y : Set ℓ} (fs : Vec (X → Y) m) (gs : Vec (X → Y) n) →
--                                  (xs : Vec X m) (ys : Vec X n) → 
--                                  (fs ⊛ xs) ++ (gs ⊛ ys) ≡ (fs ++ gs) ⊛ (xs ++ ys)
--   ++-⊛ {zero} [] gs [] ys = refl
--   ++-⊛ {suc n} (f ∷ fs) gs (x ∷ xs) ys = cong (_∷_ (f x)) (++-⊛ fs gs xs ys)

--   ++-morphism : ∀ {f m n} → Morphism {f = f} (×-applicative (vec-applicative {_} {m}) (vec-applicative {_} {n}))
--                                              (vec-applicative {_} {m + n})
--   ++-morphism {m = m} = record
--     { op = uncurry _++_
--     ; op-pure = ++-pure m
--     ; op-⊛ = λ { (f₁ , f₂) (x₁ , x₂) → ++-⊛ f₁ f₂ x₁ x₂ }
--     }

--   splitAt-morphism : ∀ {f m n} → Morphism {f = f} (vec-applicative {_} {m + n})
--                                           (×-applicative (vec-applicative {_} {m}) (vec-applicative {_} {n}))
--   splitAt-morphism {f} {m} {n} = record
--     { op = splitAt' m
--     ; op-pure = splitAt-pure
--     ; op-⊛ = splitAt-⊛
--     }
--     where
--     splitAt-pure : {X : Set f} (x : X) → splitAt' m (replicate x) ≡ replicate x , replicate x
--     splitAt-pure x = cong₂ _,_ p₁ p₂
--       where
--       p₁ : proj₁ (splitAt' m (replicate {n = m + n} x)) ≡ replicate {n = m} x
--       p₁ rewrite sym (++-pure m {n} x) = splitAt-proj₁ (replicate x) (replicate x)
--       p₂ : proj₂ (splitAt' m (replicate {n = m + n} x)) ≡ replicate {n = n} x
--       p₂ rewrite sym (++-pure m {n} x) = splitAt-proj₂ (replicate {n = m} x) (replicate x)
--     splitAt-⊛ : {X Y : Set f} (fs : Vec (X → Y) (m + n)) (xs : Vec X (m + n)) →
--                 splitAt' m (fs ⊛ xs) ≡ zip× _⊛_ _⊛_ (splitAt' m fs) (splitAt' m xs)
--     splitAt-⊛ fs xs with splitAt m fs | splitAt m xs
--     ... | f₁  , f₂  , fp | x₁  , x₂  , xp rewrite fp | xp
--                                                 | sym (++-⊛ f₁ f₂ x₁ x₂)
--                                                 | splitAt-++ (f₁ ⊛ x₁) (f₂ ⊛ x₂) = refl

--   group-morphism : ∀ {n} i (as : Vec ℕ n) → Morphism (vec-applicative {_} {size i as})
--                                                         (minGroups-applicative i as)
--   group-morphism i as = record
--     { op = group i as
--     ; op-pure = group-pure i as
--     ; op-⊛ = group-⊛ i as
--     }
--     where
--     module MGA {i : ℕ} {n : ℕ} {as : Vec ℕ n} = RawApplicative (minGroups-applicative i as)

--     group-pure : ∀ {n} i (as : Vec ℕ n) {X : Set} (x : X) →
--                     group i as (replicate x) ≡ MGA.pure x
--     group-pure i [] x = refl
--     group-pure {suc n} i (a ∷ as) {X} x with op-pure (splitAt-morphism {m = i + a} {size i as}) x
--     ... | sa-pure rewrite cong proj₁ sa-pure | cong proj₂ sa-pure
--       = cong (_∷_ _) (group-pure i as x)

--     group-⊛ : ∀ i {n} (as : Vec ℕ n) {X Y : Set} (fs : Vec (X → Y) (size i as)) (xs : Vec X (size i as))
--                  → group i as (fs ⊛ xs) ≡ (group i as fs) MGA.⊛ (group i as xs)
--     group-⊛ i [] [] [] = refl
--     group-⊛ i (a ∷ as) fs xs with op-⊛ (splitAt-morphism {m = i + a} {size i as}) fs xs
--     ... | sa-⊛ rewrite cong proj₁ sa-⊛ | cong proj₂ sa-⊛
--       = cong (_∷_ _) (group-⊛ i as (proj₂ (splitAt' (i + a) fs)) (proj₂ (splitAt' (i + a) xs)))

--   ungroup-morphism : ∀ {i n} {as : Vec ℕ n} → Morphism (minGroups-applicative i as)
--                                                       (vec-applicative {_} {size i as})
--   ungroup-morphism {i} {as = as} = record
--     { op = ungroup
--     ; op-pure = ungroup-pure i as
--     ; op-⊛ = ungroup-⊛ i as
--     }
--     where
--     module MGA {i : ℕ} {n : ℕ} {as : Vec ℕ n} = RawApplicative (minGroups-applicative i as)
--     ungroup-pure : ∀ i {n} (as : Vec ℕ n) → {X : Set} (x : X) →
--                   ungroup {i = i} {as = as} (MGA.pure x) ≡ replicate x
--     ungroup-pure i [] x = refl
--     ungroup-pure i (a ∷ as) x rewrite sym (++-pure (i + a) {size i as} x)
--       = cong (_++_ (replicate {n = i + a} x)) (ungroup-pure i as x)
    
--     ungroup-⊛ : ∀ i {n} (as : Vec ℕ n) {X Y : Set} (fs : MinGroups (X → Y) i as) (xs : MinGroups X i as) →
--                ungroup (fs MGA.⊛ xs) ≡ ungroup fs ⊛ ungroup xs
--     to-vec-⊛ i [] [] [] = refl
--     to-vec-⊛ i (a ∷ as) (f ∷ fs) (x ∷ xs) rewrite sym (++-⊛ f (to-vec fs) x (to-vec xs))
--       = cong (_++_ (f ⊛ x)) (to-vec-⊛ i as fs xs)

--   extract-morphism : ∀ {i n} {as : Vec ℕ n} → Morphism (minGroups-applicative (suc i) as)
--                                   (×-applicative (vec-applicative {_} {n}) (minGroups-applicative i as))
--   extract-morphism = record
--     { op = extract
--     ; op-pure = extract-pure _
--     ; op-⊛ = {!!}
--     }
--     where
--     module MGA (i : ℕ) {n : ℕ} (as : Vec ℕ n) = RawApplicative (minGroups-applicative i as)
--     extract-pure : ∀ {i n} (as : Vec ℕ n) {X : Set} (x : X) → extract (MGA.pure (suc i) as x) ≡ (replicate x , MGA.pure i as x)
--     extract-pure [] x = refl
--     extract-pure (a ∷ as) x = cong₂ _,_ (cong₂ _∷_ {!!} {!!}) {!!}


--   -- insert-morphism


--   -- map×-morphism




  
--   in-morphism : ∀ {n} (as : Vec ℕ n) → Morphism (vec-applicative {_} {size 1 as})
--                                                 (vec-applicative {_} {n + size 0 as})
--   in-morphism as = record
--     { op = in-table as
--     ; op-pure = in-pure as
--     ; op-⊛ = in-⊛ as
--     }
--     where
--     postulate
--       in-pure : ∀ {n} (as : Vec ℕ n) {X : Set} (x : X) → in-table as (replicate x) ≡ replicate x
--       in-⊛ : ∀ {n} (as : Vec ℕ n) {X Y : Set} (fs : Vec (X → Y) (size 1 as)) (xs : Vec (X) (size 1 as)) →
--         in-table as (fs ⊛ xs) ≡ in-table as fs ⊛ in-table as xs
    
--     -- in-pure : ∀ {n} (as : Vec ℕ n) {X : Set} (x : X) → in-table as (replicate {n = size 1 as} x) ≡ replicate {n = n + size 0 as} x
--     -- -- in-pure {n} as x with sym (replicate-++ n {size 0 as} x) | ++-splitAt (replicate {n = n} x) (replicate {n = size 0 as} x)
--     -- -- in-pure as x | r=r++r | proj₁ , proj₂ 
--     -- -- in-pure [] x = refl
--     -- -- in-pure {suc n} (a ∷ as) x with splitAt a (replicate {n = a + size 1 as} x)
--     -- -- in-pure {suc n} (a ∷ as) x | proj₁ , proj₂ , proj₃ rewrite proj₃ = {!!}
--     -- in-pure [] x = refl
--     -- in-pure {suc n} (a ∷ as) x with splitAt (1 + a) (replicate {n = 1 + a + size 1 as} x)
--     -- in-pure {suc n} (a ∷ as) x | proj₁ , proj₂ , proj₃ = begin
--     --   {!!}
--     --     ≡⟨ {!!} ⟩
--     --   replicate {n = 1 + (n + (a + size 0 as))} x
--     --     ∎
--     --   where open Relation.Binary.PropositionalEquality.≡-Reasoning
  
--     -- in-⊛ : ∀ {n} (as : Vec ℕ n) {X Y : Set} (fs : Vec (X → Y) (size 1 as)) (xs : Vec (X) (size 1 as)) →
--     --   in-table as (fs ⊛ xs) ≡ in-table as fs ⊛ in-table as xs
--     -- in-⊛ = {!!}
    
--   out-morphism : ∀ {n} (as : Vec ℕ n) → Morphism (vec-applicative {_} {n + size 0 as})
--                                                  (vec-applicative {_} {size 1 as})
--   out-morphism as = record
--     { op = out-table as
--     ; op-pure = out-pure as
--     ; op-⊛ = out-⊛ as
--     }
--     where
--     postulate
--       out-pure : ∀ {n} (as : Vec ℕ n) {X : Set} (x : X) → out-table as (replicate x) ≡ replicate x
--       out-⊛ : ∀ {n} (as : Vec ℕ n) {X Y : Set} (fs : Vec (X → Y) (n + size 0 as)) (xs : Vec (X) (n + size 0 as)) →
--         out-table as (fs ⊛ xs) ≡ out-table as fs ⊛ out-table as xs
  
--   IdentityApplicative : ∀ {f} → RawApplicative {f = f} id
--   IdentityApplicative = RawMonad.rawIApplicative IdentityMonad
--     where
--     open import Category.Monad
--     open import Category.Monad.Identity
  
--   lookup-in-morphism : ∀ {n} (as : Vec ℕ n) i → Morphism (vec-applicative {_} {size 1 as})
--                                                           (IdentityApplicative)
--   lookup-in-morphism as i = morphism-∘ (lookup-morphism i) (in-morphism as)

--   lookup-out-morphism : ∀ {n} (as : Vec ℕ n) i → Morphism (vec-applicative {_} {n + size 0 as})
--                                                           (IdentityApplicative)
--   lookup-out-morphism as i = morphism-∘ (lookup-morphism i) (out-morphism as)


--   out-in-table-identity : ∀ {n} (as : Vec ℕ n) {A} (xs : Vec A (size 1 as)) →
--                           out-table as (in-table as xs) ≡ xs
--   out-in-table-identity {n} as xs with splitAt-++ (proj₁ (extract (group 1 as xs)))
--                                                   (to-vec (proj₂ (extract (group 1 as xs))))
--                                      | to-from-identity as (proj₂ (extract (group 1 as xs)))
--   ... | s | p rewrite s | p = begin
--     to-vec (uncurry insert (extract (group 1 as xs)))
--       ≡⟨ cong to-vec (extract-insert-identity (group 1 as xs)) ⟩
--     to-vec (group 1 as xs)
--       ≡⟨ from-to-identity as xs ⟩
--     xs
--       ∎
--     where
--     open Relation.Binary.PropositionalEquality.≡-Reasoning
  
--   out-in-identity : ∀ {n} (as : Vec ℕ n) i → in-⤪ as (out-⤪ as i) ≡ i
--   out-in-identity {n} as i = begin
--     in-⤪ as (lookup i (out-table as _))
--       ≡⟨ sym (op-<$> (lookup-out-morphism as i) (in-⤪ as) _) ⟩
--     lookup i (out-table as (map (in-⤪ as) _))
--       ≡⟨⟩
--     lookup i (out-table as (map (flip lookup (in-table as _)) _))
--       ≡⟨ cong (lookup i ∘ out-table as) (map-lookup-allFin (in-table as _)) ⟩
--     lookup i (out-table as (in-table as _))
--       ≡⟨ cong (lookup i) (out-in-table-identity as _) ⟩
--     lookup i _
--       ≡⟨ lookup-allFin i ⟩
--     i
--       ∎
--     where
--     open Relation.Binary.PropositionalEquality.≡-Reasoning

--   conv : ∀ {n} (f : 𝐂 n n) (as : Vec ℕ n) (w : W (size 1 as)) → ⟦ stretch f as ⟧ w ≡ (to-vec ∘ (extract-map ⟦ f ⟧) ∘ (group 1 as)) w
--   conv {n} f as w = begin
--     -- (⟦ out-⤨ as ⟧ ∘ ⟦ f ∥ id⤨ ⟧ ∘ ⟦ in-⤨ as ⟧) w
--     --   ≡⟨ cong ⟦ out-⤨ as ⟧ (expand-par (⟦ in-⤨ as ⟧ w)) ⟩
--     -- (⟦ out-⤨ as ⟧ ∘ uncurry′ _++_ ∘ map× ⟦ f ⟧ id ∘ splitAt' _ ∘ ⟦ in-⤨ as ⟧) w
--     --   ≡⟨⟩
--     -- (⟦ Plug (flip lookup (out-table as (allFin _))) ⟧ ∘ uncurry′ _++_ ∘ map× ⟦ f ⟧ id ∘ splitAt' _ ∘ ⟦ in-⤨ as ⟧) w
--     --   ≡⟨ {!!} ⟩
--     -- ( (λ ins → tabulate (λ fin → lookup (lookup fin (out-table as (allFin _))) ins)) ∘ uncurry′ _++_ ∘ map× ⟦ f ⟧ id ∘ splitAt' _ ∘ ⟦ in-⤨ as ⟧) w
--     --   ≡⟨ {!!} ⟩
--     -- (to-vec ∘ uncurry insert ∘ map× ⟦ f ⟧ id ∘ extract ∘ group 1 as) w

--   -- out-in-identity : ∀ {n} (as : Vec ℕ n) i → in-⤪ as (out-⤪ as i) ≡ i
--   --   in-⤪ as (lookup i (out-table as _))

--     (⟦ out-⤨ as ⟧ $ ⟦ f ∥ id⤨ ⟧ $ ⟦ in-⤨ as ⟧ w)
--       ≡⟨⟩
--     (⟦ out-⤨ as ⟧ $ ⟦ f ∥ id⤨ ⟧ $ ⟦ in-⤨ as ⟧ w)
--       ≡⟨ {!!} ⟩
--     (to-vec ∘ extract-map ⟦ f ⟧ ∘ group 1 as) w
--       ∎
--     where
--     open Relation.Binary.PropositionalEquality.≡-Reasoning
--     expand-par : ∀ (w : W (n + size 0 as)) → ⟦ f ∥ id⤨ ⟧ w ≡ (uncurry′ _++_ ∘ map× ⟦ f ⟧ id ∘ splitAt' _) w
--     expand-par w rewrite tabulate∘lookup (proj₂ (splitAt' n w)) = refl
--     -- expand-plugs : (⟦ out-⤨ as ⟧ ∘ ⟦ f ∥ id⤨ ⟧ ∘ ⟦ in-⤨ as ⟧) w ≡ ()

-- -- stretch : ∀ {n cs} → ℂ {cs} n n → (as : Vec ℕ n) → ℂ {cs} (size 1 as) (size 1 as)


