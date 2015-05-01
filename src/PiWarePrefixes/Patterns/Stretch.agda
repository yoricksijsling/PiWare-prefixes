open import PiWare.Atom using (Atomic; module Atomic)
open import PiWare.Gates using (Gates)

module PiWarePrefixes.Patterns.Stretch {At : Atomic} {Gt : Gates At} where

open import Category.Functor using (module RawFunctor)
open import Data.Fin as Fin using (Fin; toℕ)
open import Data.Nat using (ℕ; zero; suc; _*_; _+_; _<_; s≤s)
open import Data.Nat.Properties as NP using (m≤m+n)
open import Data.Nat.Properties.Simple using (+-suc; +-right-identity; +-assoc; +-comm; *-comm)
open import Data.Product renaming (zip to zip×; map to map×)
open import Data.Vec renaming (map to mapᵥ; applicative to vec-applicative) hiding (group)
open import Data.Vec.Extra
open import Data.Vec.Properties as VecProps
open import Function using (id; _$_; flip; const; _∘_; _∘′_)
open import Relation.Binary.PropositionalEquality

open import PiWare.Circuit {Gt = Gt} using (ℂ; 𝐂; Plug; _⟫_; _∥_)
open import PiWarePrefixes.MinGroups as MinGroups
open import PiWare.Patterns Gt using (parsN)
open import PiWare.Plugs Gt using (id⤨)
open import PiWarePrefixes.Plugs.Core using (plug-FM)
open import PiWare.Simulation Gt using (⟦_⟧)
open import PiWarePrefixes.Utils

open Atomic At using (W; Atom)
open RawFunctor
open Morphism using (op; op-<$>)

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

  in-FM : ∀ {n} (as : Vec ℕ n) → Morphism (vec-functor (size 1 as)) (vec-functor (n + size 0 as))
  in-FM as = record { op = in-table as ; op-<$> = in-<$> as }
    where
    postulate
      -- Free property by parametricity
      in-<$> : ∀ {n} (as : Vec ℕ n) {X Y} (f : X → Y) (xs : Vec X (size 1 as)) →
               in-table as (mapᵥ f xs) ≡ mapᵥ f (in-table as xs)

  in-⤨ : ∀ {n} (as : Vec ℕ n) → 𝐂 (size 1 as) (n + size 0 as)
  in-⤨ as = plug-FM (in-FM as)
  
  out-table : ∀ {A : Set} {n} (as : Vec ℕ n) →
               Vec A (n + size 0 as) → Vec A (size 1 as)
  out-table {n = n} as = ungroup ∘ uncurry insert ∘ map× id (group 0 as) ∘ splitAt′ n

  out-FM : ∀ {n} (as : Vec ℕ n) → Morphism (vec-functor (n + size 0 as)) (vec-functor (size 1 as))
  out-FM as = record { op = out-table as ; op-<$> = out-<$> as }
    where
    postulate
      -- Free property by parametricity
      out-<$> : ∀ {n} (as : Vec ℕ n) {X Y} (f : X → Y) (xs : Vec X (n + size 0 as)) →
               out-table as (mapᵥ f xs) ≡ mapᵥ f (out-table as xs)
    
  out-⤨ : ∀ {n} (as : Vec ℕ n) → 𝐂 (n + size 0 as) (size 1 as)
  out-⤨ as = plug-FM (out-FM as)
  
  stretch : ∀ {n cs} → ℂ {cs} n n → (as : Vec ℕ n) → ℂ {cs} (size 1 as) (size 1 as)
  stretch {n} c as = in-⤨ as
                   ⟫ c ∥ id⤨
                   ⟫ out-⤨ as

⤙-direction : ExtractInsert
⤙-direction = record
  { extf = record { op = < head , tail > ; op-<$> = extf-op-<$> }
  ; insf = record { op = uncurry _∷_ ; op-<$> = λ f x → refl }
  ; extf-insf-id = extf-insf-id
  ; insf-extf-id = insf-extf-id
  }
  where
  extf-op-<$> : ∀ {n} {X Y : Set} (f : X → Y) (x : Vec X (suc n)) →
                (head (f ∷ replicate f ⊛ x) , tail (f ∷ replicate f ⊛ x)) ≡
                (f (head x) , (replicate f ⊛ tail x))
  extf-op-<$> f (x ∷ _) = cong (_,_ (f x)) refl
  extf-insf-id : {A : Set} {n : ℕ} (xs : Vec A (suc n)) → head xs ∷ tail xs ≡ xs
  extf-insf-id (_ ∷ _) = refl
  insf-extf-id : {A : Set} {n : ℕ} (x : A × Vec A n) → (proj₁ x , proj₂ x) ≡ x
  insf-extf-id (_ , _) = refl

infix 6 _⤙_
_⤙_ : ∀ {n cs} → ℂ {cs} n n → (as : Vec ℕ n) → ℂ {cs} (size 1 as) (size 1 as)
_⤙_ = WithDirection.stretch ⤙-direction


⤚-direction : ExtractInsert
⤚-direction = record
  { extf = record { op = < last , init > ; op-<$> = extf-op-<$> }
  ; insf = record { op = uncurry (flip _∷ʳ_) ; op-<$> = λ f → uncurry (insf-op-<$> f) }
  ; extf-insf-id = extf-insf-id
  ; insf-extf-id = uncurry insf-extf-id
  }
  where
  extf-insf-id : {A : Set} {n : ℕ} (xs : Vec A (suc n)) → init xs ∷ʳ last xs ≡ xs
  extf-insf-id xs with initLast xs
  extf-insf-id .(xs ∷ʳ x) | xs , x , refl = refl

  insf-extf-id : {A : Set} {n : ℕ} (x : A) (xs : Vec A n) → last (xs ∷ʳ x) , init (xs ∷ʳ x) ≡ x , xs
  insf-extf-id x xs with initLast (xs ∷ʳ x)
  insf-extf-id x xs | ys , y , p with ∷ʳ-injective xs ys p
  insf-extf-id x xs | ys , y , p | xs=ys , x=y rewrite p | x=y | xs=ys = refl

  postulate
    extf-op-<$> : ∀ {n} {X Y : Set} (f : X → Y) (xs : Vec X (suc n)) →
      last (mapᵥ f xs) , init (mapᵥ f xs) ≡ f (last xs) , (mapᵥ f (init xs))
    insf-op-<$> : ∀ {n} {X Y : Set} (f : X → Y) (x : X) (xs : Vec X n) →
      mapᵥ f xs ∷ʳ f x ≡ mapᵥ f (xs ∷ʳ x)

infix 6 _⤚_
_⤚_ : ∀ {n cs} → (as : Vec ℕ n) → ℂ {cs} n n → ℂ {cs} (size 1 as) (size 1 as)
_⤚_ = flip (WithDirection.stretch ⤚-direction)

----------------------------------------

Stretching-ℂ : ∀ {p} → Set
Stretching-ℂ {p} = (∃ λ i → ℂ {p} (suc i) (suc i))

par-stretching : ∀ {n p} (cs : Vec (Stretching-ℂ {p}) n) →
     ℂ {p} (size 1 (mapᵥ proj₁ cs)) (size 1 (mapᵥ proj₁ cs))
par-stretching [] = id⤨ {0}
par-stretching ((i , c) ∷ cs) = c ∥ (par-stretching cs)

infix 6 _⤛_
_⤛_ : ∀ {n p} → ℂ {p} n n → (cs : Vec (Stretching-ℂ {p}) n) →
      ℂ {p} (size 1 (mapᵥ proj₁ cs)) (size 1 (mapᵥ proj₁ cs))
_⤛_ f cs = f ⤙ mapᵥ proj₁ cs ⟫ par-stretching cs

infix 6 _⤜_
_⤜_ : ∀ {n p} → (cs : Vec (Stretching-ℂ {p}) n) → ℂ {p} n n →
      ℂ {p} (size 1 (mapᵥ proj₁ cs)) (size 1 (mapᵥ proj₁ cs))
_⤜_ cs f = par-stretching cs ⟫ mapᵥ proj₁ cs ⤚ f







--   --------------------------------------------------------------------------------
--   -- Lots of applicatives

  -- IdentityApplicative : ∀ {f} → RawApplicative {f = f} id
  -- IdentityApplicative = RawMonad.rawIApplicative IdentityMonad
  --   where
  --   open import Category.Monad
  --   open import Category.Monad.Identity
  
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
--     { op = splitAt′ m
--     ; op-pure = splitAt-pure
--     ; op-⊛ = splitAt-⊛
--     }
--     where
--     splitAt-pure : {X : Set f} (x : X) → splitAt′ m (replicate x) ≡ replicate x , replicate x
--     splitAt-pure x = cong₂ _,_ p₁ p₂
--       where
--       p₁ : proj₁ (splitAt′ m (replicate {n = m + n} x)) ≡ replicate {n = m} x
--       p₁ rewrite sym (++-pure m {n} x) = splitAt-proj₁ (replicate x) (replicate x)
--       p₂ : proj₂ (splitAt′ m (replicate {n = m + n} x)) ≡ replicate {n = n} x
--       p₂ rewrite sym (++-pure m {n} x) = splitAt-proj₂ (replicate {n = m} x) (replicate x)
--     splitAt-⊛ : {X Y : Set f} (fs : Vec (X → Y) (m + n)) (xs : Vec X (m + n)) →
--                 splitAt′ m (fs ⊛ xs) ≡ zip× _⊛_ _⊛_ (splitAt′ m fs) (splitAt′ m xs)
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
--       = cong (_∷_ _) (group-⊛ i as (proj₂ (splitAt′ (i + a) fs)) (proj₂ (splitAt′ (i + a) xs)))

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

