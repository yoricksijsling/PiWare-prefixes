open import PiWare.Atom using (Atomic; module Atomic)
open import PiWare.Gates using (Gates)

module PiWarePrefixes.Simulation.Properties {At : Atomic} (Gt : Gates At) where

open import Category.Applicative using (RawApplicative; module RawApplicative)
open import Category.Applicative.Indexed using (Morphism; module Morphism; IFun; RawIApplicative; module RawIApplicative)
open import Data.Fin using (Fin; zero; suc)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties.Simple using (+-right-identity; +-assoc)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Vec using (Vec; tabulate; lookup; splitAt; _++_; []; _∷_) renaming (applicative to vec-applicative)
open import Data.Vec.Properties using (tabulate-allFin; lookup∘tabulate; map-lookup-allFin)
open import Function using (id; _$_; _∘_; flip)
open import Relation.Binary.PropositionalEquality as PropEq using (refl; cong; sym; _≡_; trans)

open import PiWarePrefixes.Circuit.Context.Core Gt
open import PiWare.Circuit Gt using (ℂ; σ; Plug; _⟫_; _∥_)
open import PiWarePrefixes.Patterns.Core Gt using (_⤚_; _⤙_)
open import PiWarePrefixes.Permutation as P using (Perm; _§_; _*)
open import PiWare.Plugs Gt using (id⤨)
open import PiWarePrefixes.Plugs.Core Gt using (vec-morphism; plug-M; plug-M-⟦⟧; M-∘)
open import PiWare.Simulation Gt using (⟦_⟧)
open import PiWarePrefixes.Simulation.Equality.Core Gt as SimEq
  using (_≈⟦⟧_; Mk≈⟦⟧; easy-≈⟦⟧; ≈⟦⟧-trans; _≈e_)
open import PiWare.Synthesizable At
open import PiWarePrefixes.Utils

open Atomic At using (W)
open Morphism using (op; op-pure; op-⊛; op-<$>)

private
  import Data.Vec.Equality
  module VE = Data.Vec.Equality.PropositionalEquality
  module VecPropEq {a} {A : Set a} = Data.Vec.Properties.UsingVectorEquality (PropEq.setoid A)
  open VecPropEq using (xs++[]=xs)


----------------------------------------------------
-- Plugs

id⤨-id : ∀ {i} (w : W i) → ⟦ id⤨ ⟧ w ≡ w
id⤨-id w rewrite tabulate-allFin (λ fin → lookup fin w) = map-lookup-allFin w

plug-∘ : ∀ {i j o} (f : Fin j → Fin i) (g : Fin o → Fin j) → Plug f ⟫ Plug g ≈⟦⟧ Plug (f ∘ g)
plug-∘ f g = easy-≈⟦⟧ $ VE.from-≡ ∘ λ w →
  tabulate-extensionality (λ fin → lookup∘tabulate (λ fin₁ → lookup (f fin₁) w) (g fin))

plug-extensionality : ∀ {i o} {f : Fin o → Fin i} {g : Fin o → Fin i} → (∀ x → f x ≡ g x) → Plug f ≈⟦⟧ Plug g
plug-extensionality p = easy-≈⟦⟧ $ VE.from-≡ ∘ λ w →
  tabulate-extensionality (cong (flip lookup w) ∘ p)

pid-plugs : ∀ {i o} {f : Fin o → Fin i} {g : Fin i → Fin o} → (∀ x → f (g x) ≡ x) → Plug f ⟫ Plug g ≈⟦⟧ id⤨ {i}
pid-plugs {f = f} {g} p = ≈⟦⟧-trans (plug-∘ f g) (plug-extensionality p)

plug-id-M : ∀ {i} (M : vec-morphism i i) →
              (∀ {X : Set} (w : Vec X i) → op M w ≡ w)→
              plug-M M ≈⟦⟧ id⤨ {i}
plug-id-M M p = easy-≈⟦⟧ $ λ w → VE.from-≡ (trans (trans (plug-M-⟦⟧ M w) (p w)) (sym (id⤨-id w)))

plug-M-∘ : ∀ {i j o} (M₁ : vec-morphism i j) (M₂ : vec-morphism j o) →
                     plug-M M₁ ⟫ plug-M M₂ ≈⟦⟧ plug-M (M-∘ M₂ M₁)
plug-M-∘ {i} M₁ M₂ = easy-≈⟦⟧ (VE.from-≡ ∘ helper)
  where
  helper : (w : W i) → ⟦ plug-M M₁ ⟫ plug-M M₂ ⟧ w ≡
                       ⟦ plug-M (M-∘ M₂ M₁) ⟧ w
  helper w rewrite plug-M-⟦⟧ (M-∘ M₂ M₁) w
                 | plug-M-⟦⟧ M₁ w
                 | plug-M-⟦⟧ M₂ (op M₁ w) = refl

plug-M-extensionality : ∀ {i o} {M₁ : vec-morphism i o} {M₂ : vec-morphism i o} →
                        (∀ {X : Set} (w : Vec X i) → op M₁ w ≡ op M₂ w) → plug-M M₁ ≈⟦⟧ plug-M M₂
plug-M-extensionality p = plug-extensionality (λ x → cong (lookup x) (p _))

pid-plugs-M : ∀ {i o} (M₁ : vec-morphism i o) (M₂ : vec-morphism o i) →
              (∀ {X : Set} (w : Vec X i) → op M₂ (op M₁ w) ≡ w) → plug-M M₁ ⟫ plug-M M₂ ≈⟦⟧ id⤨ {i}
pid-plugs-M M₁ M₂ p = ≈⟦⟧-trans (plug-M-∘ M₁ M₂) (plug-id-M (M-∘ M₂ M₁) p)


----------------------------------------------------
-- Sequence

-- f ⟫ id ≡ f
⟫-right-identity : ∀ {i o} (f : ℂ i o) → f ⟫ id⤨ ≈⟦⟧ f
⟫-right-identity f = easy-≈⟦⟧ $ VE.from-≡ ∘ λ w → id⤨-id (⟦ f ⟧ w)

-- id ⟫ f ≡ f
⟫-left-identity : ∀ {i o} (f : ℂ i o) → id⤨ ⟫ f ≈⟦⟧ f
⟫-left-identity f = easy-≈⟦⟧ $ VE.from-≡ ∘ λ w → cong ⟦ f ⟧ (id⤨-id w)

-- (f ⟫ g) ⟫ h ≡ f ⟫ (g ⟫ h)
⟫-assoc : ∀ {i m n o} (f : ℂ i m) (g : ℂ m n) (h : ℂ n o) → f ⟫ g ⟫ h ≈⟦⟧ f ⟫ (g ⟫ h)
⟫-assoc f g h = easy-≈⟦⟧ $ VE.from-≡ ∘ λ w → refl


----------------------------------------------------
-- Parallel

-- id{0} || f ≡ f
∥-left-identity : ∀ {i o} (f : ℂ i o) → id⤨ {0} ∥ f ≈⟦⟧ f
∥-left-identity f = easy-≈⟦⟧ (λ w → VE.refl _)

-- f || id{0} ≡ f
∥-right-identity : {i o : ℕ} (f : ℂ i o) → f ∥ id⤨ {0} ≈⟦⟧ f
∥-right-identity f = Mk≈⟦⟧ (+-right-identity _) ∥-right-identity-≈e
  where
  lem₁ : ∀ {i} {xs : W (i + 0)} {ys : W i} (xs≈ys : xs VE.≈ ys) → (proj₁ (splitAt i xs)) VE.≈ ys
  lem₁ {i} {xs} xs≈ys with splitAt i xs
  lem₁ xs≈ys | xs₁ , [] , refl = VE.trans (VE.sym (xs++[]=xs xs₁)) xs≈ys

  ∥-right-identity-≈e : f ∥ id⤨ {0} ≈e f
  ∥-right-identity-≈e w≈w with VE.to-≡ (lem₁ w≈w)
  ∥-right-identity-≈e {w₂ = w₂} w≈w | a rewrite a = xs++[]=xs (⟦ f ⟧ w₂)

-- (f || g) || h ≡ f || (g || h)
∥-assoc : ∀ {i₁ o₁ i₂ o₂ i₃ o₃} (f : ℂ i₁ o₁) (g : ℂ i₂ o₂) (h : ℂ i₃ o₃) →
            (f ∥ g) ∥ h ≈⟦⟧ f ∥ (g ∥ h)
∥-assoc {i₁} {o₁} {i₂} {o₂} {i₃} {o₃} f g h = Mk≈⟦⟧ (+-assoc i₁ i₂ i₃) ∥-assoc-≈e
  where
  takeEq : ∀ {n m} (xs₁ : W n) {xs₂ : W m} (ys₁ : W n) {ys₂ : W m} → xs₁ ++ xs₂ VE.≈ ys₁ ++ ys₂ → xs₁ VE.≈ ys₁
  takeEq [] [] xs≈ys = VE.[]-cong
  takeEq (x ∷ xs₁) (x₁ ∷ ys₁) (x¹≈x² VE.∷-cong xs≈ys) = x¹≈x² VE.∷-cong takeEq xs₁ ys₁ xs≈ys

  dropEq : ∀ {n m} (xs₁ : W n) (xs₂ : W m) (ys₁ : W n) (ys₂ : W m) → xs₁ ++ xs₂ VE.≈ ys₁ ++ ys₂ → xs₂ VE.≈ ys₂
  dropEq [] xs₂ [] ys₂ xs≈ys = xs≈ys
  dropEq (x ∷ xs₁) xs₂ (x₁ ∷ ys₁) ys₂ (x¹≈x² VE.∷-cong xs≈ys) = dropEq xs₁ xs₂ ys₁ ys₂ xs≈ys

  lem₁ : ∀ {n m o} (xs : W (n + m + o)) (ys : W (n + (m + o))) → xs VE.≈ ys →
         proj₁ (splitAt n (proj₁ (splitAt (n + m) xs))) VE.≈ proj₁ (splitAt n ys)
  lem₁ {n} {m} xs ys xs≈ys with splitAt (n + m) xs
                              | splitAt n (proj₁ (splitAt (n + m) xs))
                              | splitAt n ys
  lem₁ ._ ._ xs≈ys | ._ , xs_o , refl | xs_n , xs_m , refl | ys_n , ys_mo , refl
    = takeEq xs_n ys_n (VE.trans (VE.sym (++-assoc xs_n xs_m xs_o)) xs≈ys)

  lem₂ : ∀ {n m o} (xs : W (n + m + o)) (ys : W (n + (m + o))) → xs VE.≈ ys →
         proj₁ (proj₂ (splitAt n (proj₁ (splitAt (n + m) xs)))) VE.≈ proj₁ (splitAt m (proj₁ (proj₂ (splitAt n ys))))
  lem₂ {n} {m} xs ys xs≈ys with splitAt (n + m) xs
                              | splitAt n (proj₁ (splitAt (n + m) xs))
                              | splitAt n ys
                              | splitAt m (proj₁ (proj₂ (splitAt n ys)))
  lem₂ ._ ._ xs≈ys | ._ , xs_o , refl | xs_n , xs_m , refl | ys_n , ._ , refl | ys_m , ys_o , refl
    = dropEq xs_n xs_m ys_n ys_m (takeEq (xs_n ++ xs_m) (ys_n ++ ys_m) (VE.trans xs≈ys (VE.sym (++-assoc ys_n ys_m ys_o))))

  lem₃ : ∀ {n m o} (xs : W (n + m + o)) (ys : W (n + (m + o))) → xs VE.≈ ys →
         proj₁ (proj₂ (splitAt (n + m) xs)) VE.≈ proj₁ (proj₂ (splitAt m (proj₁ (proj₂ (splitAt n ys)))))
  lem₃ {n} {m} xs ys xs≈ys with splitAt (n + m) xs
                              | splitAt n ys
                              | splitAt m (proj₁ (proj₂ (splitAt n ys)))
  lem₃ ._ ._ xs≈ys | xs_nm , xs_o , refl | ys_n , ._ , refl | ys_m , ys_o , refl
    = dropEq xs_nm xs_o (ys_n ++ ys_m) ys_o (VE.trans xs≈ys (VE.sym (++-assoc ys_n ys_m ys_o)))

  ∥-assoc-≈e : (f ∥ g) ∥ h ≈e f ∥ (g ∥ h)
  ∥-assoc-≈e {w₁} {w₂} w≈w with VE.to-≡ (lem₁ {i₁} w₁ w₂ w≈w) | VE.to-≡ (lem₂ {i₁} w₁ w₂ w≈w) | VE.to-≡ (lem₃ {i₁} w₁ w₂ w≈w)
  ... | l₁ | l₂ | l₃ rewrite l₁ | l₂ | sym l₃ = ++-assoc (⟦ f ⟧ (proj₁ (splitAt i₁ w₂)))
                                                         (⟦ g ⟧ (proj₁ (splitAt i₂ (proj₁ (proj₂ (splitAt i₁ w₂))))))
                                                         (⟦ h ⟧ (proj₁ (proj₂ (splitAt (i₁ + i₂) w₁))))

-- id{m} || id{n} = id{m+n}
∥-id⤨ : ∀ {n m} → id⤨ {n} ∥ id⤨ {m} ≈⟦⟧ id⤨ {n + m}
∥-id⤨ {n} {m} = easy-≈⟦⟧ (VE.from-≡ ∘ imp)
  where
  imp : ∀ w → ⟦ id⤨ {n} ∥ id⤨ {m} ⟧ w ≡ ⟦ id⤨ {n + m} ⟧ w
  imp w with splitAt n w
  ... | vn , vm , w≡vn++vm with id⤨-id vn | id⤨-id vm | id⤨-id w
  ... | vn' | vm' | w' rewrite vn' | vm' | w' = sym w≡vn++vm

-- (f₁ || f₂) ⟫ (g₁ || g₂) ≡ (f₁ ⟫ g₁) || (f₂ ⟫ g₂)
⟫-∥-distrib : ∀ {i₁ m₁ o₁ i₂ m₂ o₂} (f₁ : ℂ i₁ m₁) (g₁ : ℂ m₁ o₁) (f₂ : ℂ i₂ m₂) (g₂ : ℂ m₂ o₂) → (f₁ ∥ f₂) ⟫ (g₁ ∥ g₂) ≈⟦⟧ (f₁ ⟫ g₁) ∥ (f₂ ⟫ g₂)
⟫-∥-distrib {i₁} {m₁} f₁ g₁ f₂ g₂ = easy-≈⟦⟧ (VE.from-≡ ∘ imp)
  where
  imp : ∀ w → ⟦ f₁ ∥ f₂ ⟫ g₁ ∥ g₂ ⟧ w ≡ ⟦ (f₁ ⟫ g₁) ∥ (f₂ ⟫ g₂) ⟧ w
  imp w rewrite splitAt-++ (⟦ f₁ ⟧ (proj₁ (splitAt i₁ w))) (⟦ f₂ ⟧ (proj₁ (proj₂ (splitAt i₁ w)))) = refl
-- seq-par-distrib can be generalized to arbitrary width and height..

