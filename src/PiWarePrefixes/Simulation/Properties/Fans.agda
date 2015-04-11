module PiWarePrefixes.Simulation.Properties.Fans where

open import PiWarePrefixes.Patterns.Fan -- At, Gt and plusℂ are imported from here.

open import PiWare.Atom using (module Atomic)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Data.Nat.Properties.Simple using (+-suc; +-right-identity; +-comm)
open import Data.Product using (∃; _,_; ,_; proj₁; proj₂; uncurry; uncurry′; <_,_>) renaming (map to map×)
open import Data.Vec using (Vec; []; _∷_; _++_; [_]; sum; replicate; _∷ʳ_; initLast)
                     renaming (map to mapᵥ)
open import Data.Vec.Extra using (splitAt′)
open import Function using (id; _$_; _∘_; _⟨_⟩_)
open import PiWare.Circuit {Gt = Gt} using (ℂ; 𝐂; σ; Gate; Plug; _⟫_; _∥_)
open import PiWarePrefixes.Circuit.Context.Core Gt
open import PiWarePrefixes.MinGroups using (size)
open import PiWarePrefixes.Patterns.HetSeq {Gt = Gt}
open import PiWarePrefixes.Patterns.Stretch {Gt = Gt} using (_⤙_; Stretching-ℂ; par-stretching; _⤛_)
open import PiWare.Plugs Gt using (id⤨)
open import PiWarePrefixes.Plugs.Core {Gt = Gt} using (rewire⤨; plug-FM; plug-FM-⟦⟧)
open import PiWare.Simulation Gt using (⟦_⟧; W⟶W)
open import PiWarePrefixes.Simulation.Equality.Core {Gt = Gt} as SimEq
  renaming (≈⟦⟧-refl to refl; ≈⟦⟧-sym to sym; ≈⟦⟧-trans to trans)
open import PiWarePrefixes.Simulation.Properties Gt
open import PiWarePrefixes.Simulation.Properties.HetSeq Gt
open import PiWarePrefixes.Simulation.Properties.Stretching Gt
open import PiWarePrefixes.Simulation.Properties.Stretching.Derived Gt
open import PiWarePrefixes.Utils using ( initLast′; drop-initLast′; map-cong; map-replicate; ++-∷ʳ
                                       ; module Morphism; splitAt′-++)
open import Relation.Binary.PropositionalEquality as P using (_≡_; cong; cong₂)

private
  import Data.Vec.Equality
  import Data.Vec.Equality.Indexed
  module VE = Data.Vec.Equality.PropositionalEquality
  open VE using ([]-cong; _∷-cong_)
  module VES = Data.Vec.Equality.Indexed.Equality (reindexed-≈⟦⟧-setoid (< suc , suc >))
  open VES using ([]-cong; _∷-cong_)
  import Data.Vec.Properties
  module PVE {a} {A : Set a} = Data.Vec.Properties.UsingVectorEquality (P.setoid A)


open Atomic At using (Atom; W)
open Morphism using (op; op-<$>)

fan-plus-to-spec : ∀ n (w : W (suc n)) → ⟦ fan-plus n ⟧ w ≡ fan-plus-spec n w
fan-plus-to-spec n (x ∷ xs) = begin
  ⟦ fan-plus n ⟧ (x ∷ xs)
    ≡⟨⟩
  (⟦ id⤨ {n} ∥ plusℂ ⟧ ∘ ⟦ plug-FM (fan-plus-prepare-M n) ⟧) (x ∷ xs)
    ≡⟨ cong ⟦ id⤨ {n} ∥ plusℂ ⟧ (plug-FM-⟦⟧ (fan-plus-prepare-M n) (x ∷ xs)) ⟩
  (⟦ id⤨ {n} ∥ plusℂ ⟧ ∘ op (fan-plus-prepare-M n)) (x ∷ xs)
    ≡⟨⟩
  (uncurry′ _++_ ∘ map× ⟦ id⤨ {n} ⟧ ⟦ plusℂ ⟧ ∘ splitAt′ n ∘ op (fan-plus-prepare-M n)) (x ∷ xs)
    ≡⟨ cong₂ _++_ (id⤨-id ((proj₁ ∘ splitAt′ n ∘ op (fan-plus-prepare-M n)) (x ∷ xs))) P.refl ⟩
  (uncurry′ _++_ ∘ map× id ⟦ plusℂ ⟧ ∘ splitAt′ n ∘ op (fan-plus-prepare-M n)) (x ∷ xs)
    ≡⟨⟩
  (uncurry′ _++_ ∘ map× id ⟦ plusℂ ⟧ ∘ splitAt′ n ∘ uncurry′ _++_ ∘ map× id (λ y → x ∷ y ∷ []) ∘ initLast′) (x ∷ xs)
    ≡⟨ cong (uncurry′ _++_ ∘ map× id ⟦ plusℂ ⟧) (splitAt′-++ (proj₁ (initLast′ (x ∷ xs))) _) ⟩
  (uncurry′ _++_ ∘ map× id ⟦ plusℂ ⟧ ∘ map× id (λ y → x ∷ y ∷ []) ∘ initLast′) (x ∷ xs)
    ≡⟨ cong (_++_ (proj₁ (initLast′ (x ∷ xs)))) (singleton-⊕ x (proj₂ (initLast′ (x ∷ xs)))) ⟩
  (uncurry′ _++_ ∘ map× id (λ y → [ x ⊕ y ]) ∘ initLast′) (x ∷ xs)
    ∎
  where
  open P.≡-Reasoning
  singleton-⊕ : ∀ x y → ⟦ plusℂ ⟧ (x ∷ y ∷ []) ≡ [ x ⊕ y ]
  singleton-⊕ x y with ⟦ plusℂ ⟧ (x ∷ y ∷ [])
  singleton-⊕ x y | r ∷ [] = P.refl

private
  fan-spec-combine : ∀ {n} x (xs : W (suc n)) →
         fan-spec (x ∷ proj₁ (initLast′ xs)) ++ [ x ⊕ (proj₂ (initLast′ xs)) ] VE.≈ fan-spec (x ∷ xs)
  fan-spec-combine x xs = P.refl ∷-cong helper (_⊕_ x) xs
    where
    helper : ∀ {A B : Set} {n} (f : A → B) (xs : Vec A (suc n)) → mapᵥ f (proj₁ (initLast′ xs)) ++ [ f (proj₂ (initLast′ xs)) ] VE.≈ mapᵥ f xs
    helper {n = zero} f (x ∷ []) = VE.refl (f x ∷ [])
    helper {n = suc n} f (x ∷ xs) with initLast xs
    helper {A} {B} {suc n} f (x ∷ .(ys ∷ʳ y)) | ys , y , P.refl = P.refl ∷-cong
        (VE.sym (PVE.map-++-commute f ys {[ y ]}) ⟨ VE.trans ⟩ map-cong f (VE.sym (++-∷ʳ ys y)))

mutual
  fan′-to-spec : ∀ n (w : W n) → ⟦ fan′ n ⟧ w VE.≈ fan-spec w
  fan′-to-spec 0 [] = VE.refl []
  fan′-to-spec 1 (x ∷ []) = VE.refl [ x ]
  fan′-to-spec (suc (suc n)) (x ∷ xs) = VE.from-≡ (fan′-to-part-of-spec (fan-to-spec (suc n))) ⟨ VE.trans ⟩ fan-spec-combine x xs
    where
    open P.≡-Reasoning
    fa : W⟶W (suc n + 1) (suc n + 1)
    fa = ⟦ fan (suc n) ∥ id⤨ ⟧

    fan′-to-part-of-spec : ((w : W (suc n)) → ⟦ fan (suc n) ⟧ w ≡ fan-spec w) →
      ⟦ fan′ (2 + n) ⟧ (x ∷ xs) ≡ fan-spec (x ∷ proj₁ (initLast′ xs)) ++ [ x ⊕ proj₂ (initLast′ xs) ]
    fan′-to-part-of-spec rec = begin
      ⟦ fan-plus (suc n) ⟫ fan (suc n) ∥ id⤨ {1} ⟧ (x ∷ xs)
        ≡⟨⟩
      (fa ∘ ⟦ fan-plus (suc n) ⟧) (x ∷ xs)
        ≡⟨ cong fa (fan-plus-to-spec (suc n) (x ∷ xs)) ⟩
      (fa ∘ uncurry′ _++_ ∘ map× id (λ y → [ x ⊕ y ]) ∘ initLast′) (x ∷ xs)
        ≡⟨ cong (fa ∘ uncurry′ _++_ ∘ map× id (λ y → [ x ⊕ y ])) (drop-initLast′ x xs) ⟩
      (fa ∘ uncurry′ _++_ ∘ map× (_∷_ x) (λ y → [ x ⊕ y ]) ∘ initLast′) xs
       ≡⟨⟩
      (uncurry′ _++_ ∘ map× ⟦ fan (suc n) ⟧ ⟦ id⤨ ⟧ ∘ splitAt′ (suc n) ∘
       uncurry′ _++_ ∘ map× (_∷_ x) (λ y → [ x ⊕ y ]) ∘ initLast′) xs
        ≡⟨ cong (uncurry′ _++_ ∘ map× ⟦ fan (suc n) ⟧ ⟦ id⤨ ⟧)
                (splitAt′-++ (x ∷ (proj₁ (initLast′ xs))) _) ⟩
      (uncurry′ _++_ ∘ map× (⟦ fan (suc n) ⟧ ∘ _∷_ x)
                            (⟦ id⤨ ⟧ ∘ (λ y → [ x ⊕ y ])) ∘ initLast′) xs
        ≡⟨ cong₂ _++_ (rec (x ∷ proj₁ (initLast′ xs)))
                      (id⤨-id [ x ⊕ proj₂ (initLast′ xs) ]) ⟩
      (uncurry′ _++_ ∘ map× (fan-spec {suc n} ∘ _∷_ x)
                            (λ y → [ x ⊕ y ]) ∘ initLast′) xs
        ≡⟨⟩
      fan-spec (x ∷ proj₁ (initLast′ xs)) ++ [ x ⊕ proj₂ (initLast′ xs) ]
        ∎

  fan-to-spec : ∀ n (w : W n) → ⟦ fan n ⟧ w ≡ fan-spec w
  fan-to-spec n w with ⟫[]-right-identity (fan′ n) {swapℕ-id n}
  fan-to-spec n w | Mk≈⟦⟧ pi fan≈fan′ = VE.to-≡ (fan≈fan′ (VE.refl w) ⟨ VE.trans ⟩ fan′-to-spec n w)


fan-cong : ∀ {m n} (p : m ≡ n) → fan m ≈⟦⟧ fan n
fan-cong P.refl = refl

postulate
  fan-law-1 : ∀ {n m} (f : Stretching-ℂ) (fs : Vec Stretching-ℂ m) (gs : Vec Stretching-ℂ n) →
              (fan (suc n)) ⤛ ((, fan (suc m) ⤛ (f ∷ fs)) ∷ gs) ≈⟦⟧ fan (suc m + n) ⤛ ((f ∷ fs) ++ gs)
-- fan-law-1 {n} {m} f fs gs = Mk≈⟦⟧ pi helper
--   where
--     pi : size 1 (mapᵥ proj₁ (f ∷ fs)) + size 1 (mapᵥ proj₁ gs) ≡ size 1 (mapᵥ proj₁ (f ∷ fs ++ gs))
--     helper : (fan (suc n)) ⤛ ((, fan (suc m) ⤛ (f ∷ fs)) ∷ gs) ≈e fan (suc m + n) ⤛ ((f ∷ fs) ++ gs)

fans : ∀ {n p} (xs : Vec ℕ n) → Vec (Stretching-ℂ {p}) n
fans = mapᵥ (λ x → x , fan (suc x))

postulate
  fan-law-2′ : ∀ {n} i (xs : Vec ℕ n) →
            par-stretching ((, id⤨ {suc i}) ∷ fans xs) ⟫ fan (size 1 (i ∷ mapᵥ proj₁ (fans xs)))
              ≈⟦⟧ fan (1 + n) ⤛ ((, fan (suc i)) ∷ fans xs)
-- fan-law-2′ {n} i xs = easy-≈⟦⟧ (VE.from-≡ ∘ helper)
--   where
--   open P.≡-Reasoning
--   helper : ∀ w → ⟦ par-stretching ((, id⤨ {suc i}) ∷ fans xs) ⟫ fan (size 1 (i ∷ mapᵥ proj₁ (fans xs))) ⟧ w
--                ≡ ⟦ fan (1 + n) ⤛ ((, fan (suc i)) ∷ fans xs) ⟧ w
--   helper w = begin
--     ⟦ par-stretching ((, id⤨ {suc i}) ∷ fans xs) ⟫ fan (size 1 (i ∷ mapᵥ proj₁ (fans xs))) ⟧ w
--       ≡⟨ {!!} ⟩
--     {!!}
--       ≡⟨ {!!} ⟩
--     {!!}
--       ≡⟨ sym {!fan-to-spec!} ⟩
--     ⟦ fan (1 + n) ⤛ ((, fan (suc i)) ∷ fans xs) ⟧ w
--       ∎

  

fan-law-2 : ∀ {n} i (xs : Vec ℕ n) →
            id⤨ {1 + n} ⤛ ((, id⤨ {suc i}) ∷ fans xs) ⟫ fan (size 1 (i ∷ mapᵥ proj₁ (fans xs)))
              ≈⟦⟧ fan (1 + n) ⤛ ((, fan (suc i)) ∷ fans xs)
fan-law-2 {n} i xs = begin
  id⤨ ⤛ ((, id⤨ {suc i}) ∷ fans xs) ⟫ fan _
    ≈⟦⟧⟨ ≈⟦⟧-cong (● ●⟫ refl) (⤛-on-identity _) ⟩
  par-stretching ((, id⤨ {suc i}) ∷ fans xs) ⟫ fan _
    ≈⟦⟧⟨ fan-law-2′ i xs ⟩
  fan (1 + n) ⤛ ((, fan (suc i)) ∷ fans xs)
    ∎
  where
  open SimEq.≈⟦⟧-Reasoning

binary-fan-law : ∀ m n → id⤨ {suc m} ∥ fan (suc n) ⟫ fan (suc m + suc n)
    ≈⟦⟧ fan (2 + m) ∥ id⤨ {n} ⟫[ P.sym (+-suc (suc m) n) ] id⤨ {suc m} ∥ fan (suc n)
binary-fan-law m n = begin
  id⤨ {suc m} ∥ fan (suc n) ⟫ fan (suc m + suc n)
    ≈⟦⟧⟨ (sym (∥-right-identity _) ⟨ trans ⟩ ∥-assoc _ _ _)
         ⟫-cong fan-cong (cong (_+_ (suc m) ∘ suc) (P.sym (+-right-identity n))) ⟩
  id⤨ {suc m} ∥ fan (suc n) ∥ id⤨ {0} ⟫ fan (suc m + (suc n + 0))
    ≈⟦⟧⟨ fan-law-2′ m [ n ] ⟩
  fan 2 ⤛ ((, fan (suc m)) ∷ [ , fan (suc n) ])
    ≈⟦⟧⟨ refl ⤛-cong (sym (⤛-by-identity (fan (suc m))) ∷-cong (refl ∷-cong []-cong)) ⟩
  fan 2 ⤛ ((, fan (suc m) ⤛ ids) ∷ [ , fan (suc n) ])
    ≈⟦⟧⟨ fan-law-1 (, id⤨ {1}) ids [ , fan (suc n) ] ⟩
  fan (suc m + 1) ⤛ (ids {suc m} ++ [ , fan (suc n) ])
    ≈⟦⟧⟨⟩ -- left side
  fan (suc m + 1) ⤙ mapᵥ proj₁ (ids {suc m} ++ [ , fan (suc n) ]) ⟫ _
    ≈⟦⟧⟨ (fan-cong (+-comm (suc m) 1) ⤙-cong lem₁) ⟫[-cong refl ⟩
  fan (2 + m) ⤙ (replicate 0 ∷ʳ n) ⟫[] _
    ≈⟦⟧⟨ (stretch-derived-1 (fan (2 + m)) (replicate 0)) ⟫[]-cong refl ⟩
  (fan (2 + m) ⤙ (replicate 0 ∷ʳ 0)) ∥ id⤨ {n} ⟫[] _
    ≈⟦⟧⟨ ((refl ⤙-cong (lem₂ (suc m))) ∥-cong refl) ⟫[]-cong refl ⟩
  fan (2 + m) ⤙ replicate 0 ∥ id⤨ {n} ⟫[] _ 
    ≈⟦⟧⟨ ((⤙-by-identity (fan (2 + m))) ∥-cong refl) ⟫[]-cong refl ⟩
  fan (2 + m) ∥ id⤨ {n} ⟫[] _
    ≈⟦⟧⟨⟩ -- right side
  _ ⟫[] par-stretching (ids {suc m} ++ [ , fan (suc n) ])
    ≈⟦⟧⟨ refl ⟫[]-cong (lem₃ (suc m)) ⟩
  _ ⟫[] id⤨ {suc m} ∥ fan (suc n)
    ≈⟦⟧⟨ ⟫[]-replace (P.sym (cong suc (+-suc m n))) ⟩
  _ ⟫[] _
    ∎
  where
  open SimEq.≈⟦⟧-Reasoning

  ids : ∀ {n} → Vec (Stretching-ℂ {σ}) n
  ids {_} = replicate (, id⤨ {1})

  lem₁ : mapᵥ proj₁ (ids {suc m} ++ [ , fan (suc n) ]) VE.≈ (replicate 0) ∷ʳ n
  lem₁ =         PVE.map-++-commute proj₁ (ids {suc m})
    ⟨ VE.trans ⟩ VE.from-≡ (map-replicate {suc m} proj₁ (0 , id⤨ {1})) VE.++-cong VE.refl [ n ]
    ⟨ VE.trans ⟩ VE.sym (++-∷ʳ (replicate {n = suc m} 0) n)

  lem₂ : ∀ n → replicate {n = n} 0 ∷ʳ 0 VE.≈ replicate {n = suc n} 0
  lem₂ zero = P.refl ∷-cong []-cong
  lem₂ (suc n) = P.refl ∷-cong lem₂ n

  lem₃ : ∀ m → par-stretching (ids {m} ++ [ , fan (suc n) ]) ≈⟦⟧ id⤨ {m} ∥ fan (suc n)
  lem₃ zero = ∥-right-identity (fan (suc n)) ⟨ trans ⟩ sym (∥-left-identity (fan (suc n)))
  lem₃ (suc m) = refl ∥-cong (lem₃ m) ⟨ trans ⟩ sym (∥-assoc _ _ _) ⟨ trans ⟩ ∥-id⤨ ∥-cong refl
