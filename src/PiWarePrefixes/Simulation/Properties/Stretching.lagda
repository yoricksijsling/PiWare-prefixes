\begin{code}
open import PiWare.Atom using (Atomic; module Atomic)
open import PiWare.Gates using (Gates)

module PiWarePrefixes.Simulation.Properties.Stretching {At : Atomic} (Gt : Gates At) where

open import Data.Fin using (Fin)
open import Data.Nat using (ℕ; suc; pred; _+_)
open import Data.Nat.Properties.Simple using (+-comm; +-suc; +-assoc; +-right-identity)
open import Data.Product renaming (map to map×)
open import Data.Vec using (Vec; _++_; _∷_; []; [_]; _∷ʳ_; replicate; splitAt)
                     renaming (sum to sumᵥ; map to mapᵥ)
open import Data.Vec.Extra using (splitAt′; splitAt-++)
open import Function using (id; const; flip; _$_; _∘_; _∘′_; _⟨_⟩_)
open import Relation.Binary.PropositionalEquality as PropEq using (refl; cong; cong₂; sym; _≡_; subst; trans)

open import PiWare.Circuit {Gt = Gt} using (ℂ; 𝐂; Plug; _⟫_; _∥_)
open import PiWarePrefixes.Circuit.Context.Core Gt
open import PiWarePrefixes.MinGroups as MinGroups
open import PiWarePrefixes.Patterns.Stretch {Gt = Gt} as Stretch
  using (_⤚_; ⤚-direction; _⤙_; ⤙-direction)
open import PiWare.Plugs Gt using (id⤨)
open import PiWarePrefixes.Plugs.Core {Gt = Gt} using (plug-FM; plug-FM-⟦⟧)
open import PiWare.Simulation Gt using (⟦_⟧; W⟶W)
open import PiWarePrefixes.Simulation.Equality.Core {Gt = Gt} as SimEq
open import PiWarePrefixes.Simulation.Properties {Gt = Gt}

private
  import Data.Vec.Equality
  module VE = Data.Vec.Equality.PropositionalEquality

open Atomic At using (W; Atom)

private
  x+size1xs : ∀ {m} → Vec ℕ (suc m) → ℕ
  x+size1xs (x ∷ xs) = x + size 1 xs

  join-minGroups : ∀ {n} (as : Vec ℕ n) (bs : Vec ℕ (size 1 as)) → Vec ℕ n
  join-minGroups as = map-to-vec x+size1xs ∘ group 1 as

module WithDirection (extract-insert : ExtractInsert) where
  open MinGroups.WithExtractInsert extract-insert public
  open Stretch.WithDirection extract-insert
  open PropEq.≡-Reasoning

  -- A note in general:
  -- Many of these proofs could be written more easily by rewriting with
  -- stretch-to-spec. However, this makes agda very slow so we try not to do that.

  stretch-to-spec : ∀ {n} (f : ℂ n n) (as : Vec ℕ n) (w : W (size 1 as)) → ⟦ stretch f as ⟧ w ≡ (ungroup ∘ (extract-map ⟦ f ⟧) ∘ (group 1 as)) w
  stretch-to-spec {n} f as w = begin
    (⟦ out-⤨ as ⟧ $ ⟦ f ∥ id⤨ ⟧ $ ⟦ in-⤨ as ⟧ w)
      ≡⟨ expand-plugs ⟩
    (out-table as ∘ ⟦ f ∥ id⤨ ⟧ ∘ in-table as) w
      ≡⟨ cong (out-table as) (expand-par (in-table as w)) ⟩
    (ungroup ∘ uncurry insert ∘ map× id (group 0 as) ∘ splitAt′ n ∘
       uncurry′ _++_ ∘ map× ⟦ f ⟧ id ∘ splitAt′ _ ∘
       uncurry _++_ ∘ map× id ungroup ∘ extract ∘ group 1 as) w
      ≡⟨ cong (ungroup ∘ uncurry insert ∘ map× id (group 0 as)) (splitAt′-++ (cong (map× ⟦ f ⟧ id) (splitAt′-++ refl))) ⟩
    (ungroup ∘ uncurry insert ∘ map× ⟦ f ⟧ (group 0 as ∘ ungroup) ∘ extract ∘ group 1 as) w
      ≡⟨ cong (ungroup ∘ uncurry insert) (map×-from-to (extract (group 1 as w))) ⟩
    (ungroup ∘ extract-map ⟦ f ⟧ ∘ group 1 as) w
      ∎
    where
    open import Data.Vec.Properties
    expand-plugs : (⟦ out-⤨ as ⟧ ∘ ⟦ f ∥ id⤨ ⟧ ∘ ⟦ in-⤨ as ⟧) w ≡ (out-table as ∘ ⟦ f ∥ id⤨ ⟧ ∘ in-table as) w
    expand-plugs with plug-FM-⟦⟧ (out-FM as) (⟦ f ∥ id⤨ ⟧ (⟦ in-⤨ as ⟧ w))
                    | plug-FM-⟦⟧ (in-FM as) w
    ... | r1 | r2 rewrite r1 | r2  = refl
    expand-par : ∀ (w : W (n + size 0 as)) → ⟦ f ∥ id⤨ ⟧ w ≡ (uncurry′ _++_ ∘ map× ⟦ f ⟧ id ∘ splitAt′ _) w
    expand-par w rewrite id⤨-id (proj₂ (splitAt′ n w)) = refl
    map×-from-to : (x : W n × MinGroups Atom 0 as) → (map× {Q = const (MinGroups Atom 0 as)} ⟦ f ⟧ (group 0 as ∘ ungroup)) x ≡ map× ⟦ f ⟧ id x
    map×-from-to (w' , gs) rewrite ungroup-group-identity as gs = refl
    splitAt′-++ : ∀ {A : Set} {m n} {x y : Vec A m × Vec A n} (p : x ≡ y) → splitAt′ m (uncurry′ _++_ x) ≡ y
    splitAt′-++ {x = xs , ys} p rewrite splitAt-++ _ xs ys = p
  
  stretch-cong : ∀ {m n} {f : ℂ m m} {g : ℂ n n} {as : Vec ℕ m} {bs : Vec ℕ n} →
                 f ≈⟦⟧ g → as VE.≈ bs → stretch f as ≈⟦⟧ stretch g bs
  stretch-cong {f = f} {g} {as} (Mk≈⟦⟧ refl f≈g) q with VE.to-≡ q
  ... | refl = easy-≈⟦⟧ (VE.from-≡ ∘ helper)
    where
    helper : ∀ w → ⟦ stretch f as ⟧ w ≡ ⟦ stretch g as ⟧ w
    helper w = begin
      ⟦ stretch f as ⟧ w
        ≡⟨ stretch-to-spec f as w ⟩
      (ungroup ∘ extract-map ⟦ f ⟧ ∘ group 1 as) w
        ≡⟨ cong ungroup (extract-map-cong (VE.to-≡ ∘ f≈g ∘ VE.refl) (group 1 as w)) ⟩
      (ungroup ∘ extract-map ⟦ g ⟧ ∘ group 1 as) w
        ≡⟨ sym (stretch-to-spec g as w) ⟩
      ⟦ stretch g as ⟧ w
        ∎

  preserves-id : ∀ {n} (as : Vec ℕ n) → stretch (id⤨ {n}) as ≈⟦⟧ id⤨ {sumᵥ (mapᵥ suc as)}
  preserves-id {n} as = easy-≈⟦⟧ (VE.from-≡ ∘ helper)
    where
    helper : ∀ w → ⟦ stretch id⤨ as ⟧ w ≡ ⟦ id⤨ ⟧ w
    helper w = begin
      ⟦ stretch id⤨ as ⟧ w
        ≡⟨ stretch-to-spec id⤨ as w ⟩
      (ungroup ∘ extract-map ⟦ id⤨ ⟧ ∘ group 1 as) w
        ≡⟨ cong ungroup (extract-map-cong id⤨-id (group 1 as w)) ⟩
      (ungroup ∘ extract-map id ∘ group 1 as) w
        ≡⟨ cong ungroup (extract-map-id (group 1 as w)) ⟩
      (ungroup ∘ group 1 as) w
        ≡⟨ group-ungroup-identity as w ⟩
      w
        ≡⟨ sym (id⤨-id w) ⟩
      ⟦ id⤨ ⟧ w
        ∎

  by-identity : ∀ {n} (f : ℂ n n) → stretch f (replicate 0) ≈⟦⟧ f
  by-identity {n} f = Mk≈⟦⟧ (pi n) helper
    where
    pi : ∀ n → size 1 (replicate {n = n} 0) ≡ n
    pi Data.Nat.zero = refl
    pi (suc n) = cong suc (pi n)
    postulate
      lem : ∀ {w₁ : W (size 1 (replicate {n = n} 0))} {w₂ : W n} (w≈w : w₁ VE.≈ w₂) →
          (ungroup ∘ extract-map ⟦ f ⟧ ∘ group 1 (replicate 0)) w₁ VE.≈ ⟦ f ⟧ w₂
    helper : stretch f (replicate 0) ≈e f
    helper {w₁} {w₂} w≈w = VE.from-≡ (stretch-to-spec f (replicate 0) w₁) ⟨ VE.trans ⟩ lem w≈w

  ⟫-distrib : ∀ {n} (as : Vec ℕ n) (f g : ℂ n n) → (stretch f as) ⟫ (stretch g as) ≈⟦⟧ stretch (f ⟫ g) as
  ⟫-distrib {n} as f g = easy-≈⟦⟧ (VE.from-≡ ∘ helper)
    where
    helper : ∀ w → ⟦ (stretch f as) ⟫ (stretch g as) ⟧ w ≡ ⟦ stretch (f ⟫ g) as ⟧ w
    helper w = begin
      (⟦ stretch g as ⟧ ∘ ⟦ stretch f as ⟧) w
        ≡⟨ cong ⟦ stretch g as ⟧ (stretch-to-spec f as w) ⟩
      (⟦ stretch g as ⟧ ∘ ungroup ∘ extract-map ⟦ f ⟧ ∘ group 1 as) w
        ≡⟨ stretch-to-spec g as _ ⟩
      (ungroup ∘ extract-map ⟦ g ⟧ ∘ group 1 as ∘ ungroup ∘ extract-map ⟦ f ⟧ ∘ group 1 as) w
        ≡⟨ cong (ungroup ∘ extract-map ⟦ g ⟧) (ungroup-group-identity as ((extract-map ⟦ f ⟧ ∘ group 1 as) w)) ⟩
      (ungroup ∘ extract-map ⟦ g ⟧ ∘ extract-map ⟦ f ⟧ ∘ group 1 as) w
        ≡⟨ cong ungroup (extract-map-∘ ⟦ g ⟧ ⟦ f ⟧ (group 1 as w)) ⟩
      (ungroup ∘ extract-map ⟦ f ⟫ g ⟧ ∘ group 1 as) w
        ≡⟨ sym (stretch-to-spec (f ⟫ g) as w) ⟩
      ⟦ stretch (f ⟫ g) as ⟧ w
        ∎

  ∥-distrib : ∀ {n m} (as : Vec ℕ n) (bs : Vec ℕ m) (f : ℂ n n) (g : ℂ m m) →
    stretch (f ∥ g) (as ++ bs) ≈⟦⟧ (stretch f as) ∥ (stretch g bs)
  ∥-distrib {n} as bs f g = Mk≈⟦⟧ (pi as bs) helper
    where
    pi : ∀ {n m} (as : Vec ℕ n) (bs : Vec ℕ m) → size 1 (as ++ bs) ≡ size 1 as + size 1 bs
    pi [] bs = refl
    pi (a ∷ as) bs rewrite pi as bs = cong suc (sym (+-assoc a _ _))

    postulate
      split-group-commute : ∀ {A} i {m n} (as : Vec ℕ m) {bs : Vec ℕ n} →
        {xs : Vec A (size i (as ++ bs))} {ys : Vec A (size i as + size i bs)} →
        (p : xs VE.≈ ys) →
        (map× (group i as) (group i bs) ∘ splitAt′ (size i as)) ys ≡ (splitᵍ as ∘ group i (as ++ bs)) xs

    group-++-commute : ∀ {w₁ : W (size 1 (as ++ bs))} {w₂ : W (size 1 as + size 1 bs)} (w≈w : w₁ VE.≈ w₂) →
           (ungroup ∘ uncurry _++ᵍ_ ∘ map× (extract-map ⟦ f ⟧)
                                           (extract-map ⟦ g ⟧) ∘ splitᵍ as ∘ group 1 (as ++ bs)) w₁
             VE.≈
           (uncurry _++_ ∘ map× (ungroup ∘ extract-map ⟦ f ⟧ ∘ group 1 as)
                                (ungroup ∘ extract-map ⟦ g ⟧ ∘ group 1 bs) ∘ splitAt′ (size 1 as)) w₂
    group-++-commute {w₁} {w₂} w≈w = VE.from-≡ (sym (cong (ungroup ∘ uncurry _++ᵍ_ ∘ map× (extract-map ⟦ f ⟧) (extract-map ⟦ g ⟧))
                                                          (split-group-commute 1 as w≈w)))
                         ⟨ VE.trans ⟩ uncurry ++-ungroup-commute ((map× (extract-map ⟦ f ⟧ ∘ group 1 as)
                                                                 (extract-map ⟦ g ⟧ ∘ group 1 bs) ∘ splitAt′ (size 1 as)) w₂)

    helper : stretch (f ∥ g) (as ++ bs) ≈e (stretch f as) ∥ (stretch g bs)
    helper {w₁} {w₂} w≈w = VE.from-≡ (stretch-to-spec (f ∥ g) (as ++ bs) w₁)
              ⟨ VE.trans ⟩ VE.from-≡ (cong ungroup (extract-map-++-commute as ⟦ f ⟧ ⟦ g ⟧ (group 1 (as ++ bs) w₁)))
              ⟨ VE.trans ⟩ group-++-commute w≈w
              ⟨ VE.trans ⟩ VE.from-≡ (sym (cong₂ _++_ (stretch-to-spec f as (proj₁ (splitAt′ (size 1 as) w₂)))
                                                      (stretch-to-spec g bs (proj₂ (splitAt′ (size 1 as) w₂)))))

  postulate
    lep : ∀ {n} (as : Vec ℕ n) (bs : Vec ℕ (size 1 as)) (f : W n → W n) →
        {w₁ : W (size 1 bs)} {w₂ : W (size 1 (join-minGroups as bs))} (w≈w : w₁ VE.≈ w₂) →
        (ungroup ∘ extract-map (ungroup ∘ extract-map f ∘ group 1 as) ∘ group 1 bs) w₁
        VE.≈
        (ungroup ∘ extract-map f ∘ group 1 (join-minGroups as bs)) w₂

  join : ∀ {n} (as : Vec ℕ n) (bs : Vec ℕ (size 1 as)) (f : ℂ n n) →
    stretch (stretch f as) bs ≈⟦⟧ stretch f (join-minGroups as bs)
  join as bs f = Mk≈⟦⟧ (pi as bs) helper
    where
    pi : ∀ {n} (as : Vec ℕ n) (bs : Vec ℕ (size 1 as)) →
         size 1 bs ≡ size 1 (join-minGroups as bs)
    pi [] [] = refl
    pi (a ∷ as) bs with splitAt (1 + a) bs
    pi (a ∷ as) .(x ∷ xs ++ ys) | x ∷ xs , ys , refl rewrite sym (pi as ys) = size-++ (x ∷ xs) ys

    lem : ∀ {w₁ : W (size 1 bs)} {w₂ : W (size 1 (join-minGroups as bs))} (w≈w : w₁ VE.≈ w₂) →
          (ungroup ∘ extract-map (ungroup ∘ extract-map ⟦ f ⟧ ∘ group 1 as) ∘ group 1 bs) w₁
          VE.≈
          (ungroup ∘ extract-map ⟦ f ⟧ ∘ group 1 (join-minGroups as bs)) w₂
    lem w≈w = lep as bs ⟦ f ⟧ w≈w

    helper : stretch (stretch f as) bs ≈e stretch f (join-minGroups as bs)
    helper {w₁} {w₂} w≈w = VE.from-≡ (stretch-to-spec (stretch f as) bs w₁)
              ⟨ VE.trans ⟩ VE.from-≡ (cong (ungroup ∘ uncurry insert) (cong₂ _,_ (stretch-to-spec f as (proj₁ (extract (group 1 bs w₁)))) refl))
              ⟨ VE.trans ⟩ lem w≈w
              ⟨ VE.trans ⟩ VE.from-≡ (sym (stretch-to-spec f (join-minGroups as bs) w₂))

--------------------------------------------------------------------------------

module With-⤙ = WithDirection ⤙-direction
module With-⤚ = WithDirection ⤚-direction

-- Stretch is a congruence
_⤙-cong_ : ∀ {m n} {f : ℂ m m} {g : ℂ n n} {as : Vec ℕ m} {bs : Vec ℕ n} →
            f ≈⟦⟧ g → as VE.≈ bs → f ⤙ as ≈⟦⟧ g ⤙ bs
_⤙-cong_ = With-⤙.stretch-cong

_⤚-cong_ : ∀ {m n} {f : ℂ m m} {g : ℂ n n} {as : Vec ℕ m} {bs : Vec ℕ n} →
            f ≈⟦⟧ g → as VE.≈ bs → as ⤚ f ≈⟦⟧ bs ⤚ g
_⤚-cong_ = With-⤚.stretch-cong

-- Stretch preserves identity
⤙-preserves-id : ∀ {n} (as : Vec ℕ n) →
                 id⤨ {n} ⤙ as ≈⟦⟧ id⤨ {size 1 as}
⤙-preserves-id = With-⤙.preserves-id

⤚-preserves-id : ∀ {n} (as : Vec ℕ n) →
                 as ⤚ id⤨ {n} ≈⟦⟧ id⤨ {size 1 as}
⤚-preserves-id = With-⤚.preserves-id

-- Stretching with a list of 0's
⤙-by-identity : ∀ {n} (f : ℂ n n) → f ⤙ (replicate 0) ≈⟦⟧ f
⤙-by-identity = With-⤙.by-identity

⤚-by-identity : ∀ {n} (f : ℂ n n) → (replicate 0) ⤚ f ≈⟦⟧ f
⤚-by-identity = With-⤚.by-identity

-- Stretch distributes over ⟫
⤙-⟫-distrib : ∀ {n} (xs : Vec ℕ n) (f g : ℂ n n) → f ⤙ xs ⟫ g ⤙ xs ≈⟦⟧ (f ⟫ g) ⤙ xs
⤙-⟫-distrib = With-⤙.⟫-distrib

⤚-⟫-distrib : ∀ {n} (xs : Vec ℕ n) (f g : ℂ n n) → xs ⤚ f ⟫ xs ⤚ g ≈⟦⟧ xs ⤚ (f ⟫ g)
⤚-⟫-distrib = With-⤚.⟫-distrib


-- Stretch distributes over ∥
⤙-∥-distrib : ∀ {n m} (as : Vec ℕ n) (bs : Vec ℕ m) (f : ℂ n n) (g : ℂ m m) →
              (f ∥ g) ⤙ (as ++ bs) ≈⟦⟧ f ⤙ as ∥ g ⤙ bs
⤙-∥-distrib = With-⤙.∥-distrib

⤚-∥-distrib : ∀ {n m} (as : Vec ℕ n) (bs : Vec ℕ m) (f : ℂ n n) (g : ℂ m m) →
              (as ++ bs) ⤚ (f ∥ g) ≈⟦⟧ as ⤚ f ∥ bs ⤚ g
⤚-∥-distrib = With-⤚.∥-distrib


⤙-join : ∀ {n} (as : Vec ℕ n) (bs : Vec ℕ (size 1 as)) (f : ℂ n n) →
    (f ⤙ as) ⤙ bs ≈⟦⟧ f ⤙ (join-minGroups as bs)
⤙-join = With-⤙.join

⤚-join : ∀ {n} (as : Vec ℕ n) (bs : Vec ℕ (size 1 as)) (f : ℂ n n) →
    bs ⤚ (as ⤚ f) ≈⟦⟧ (join-minGroups as bs) ⤚ f
⤚-join = With-⤚.join


-- flip law
stretch-flip : ∀ {i k n} (f : ℂ (suc n) (suc n)) (ys : Vec ℕ n) →
               id⤨ {i} ∥ f ⤙ (ys ∷ʳ k) ≈⟦⟧ (i ∷ ys) ⤚ f ∥ id⤨ {k}
stretch-flip {i} {k} f ys = Mk≈⟦⟧ (pi ys) helper
  where
  pi : ∀ {n} (ys : Vec ℕ n) → i + size 1 (ys ∷ʳ k) ≡ size 1 (i ∷ ys) + k
  pi [] rewrite +-right-identity k | +-right-identity i = +-suc i k
  pi (y ∷ ys) with pi ys
  ... | rec = begin
    i + (1 + (y + size 1 (ys ∷ʳ k)))
      ≡⟨ solve 3 (λ i y s → i :+ (con 1 :+ (y :+ s)) := con 1 :+ y :+ (i :+ s)) refl i y (size 1 (ys ∷ʳ k)) ⟩
    (1 + y) + (i + size 1 (ys ∷ʳ k))
      ≡⟨ cong (_+_ (1 + y)) (pi ys) ⟩
    (1 + y) + (1 + i + size 1 ys + k)
      ≡⟨ solve 4 (λ i y s k → con 1 :+ y :+ (con 1 :+ i :+ s :+ k) := con 1 :+ (i :+ (con 1 :+ (y :+ s)) :+ k))
               refl i y (size 1 ys) k ⟩
    1 + (i + (1 + (y + size 1 ys)) + k)
      ∎
    where
    open PropEq.≡-Reasoning
    import Data.Nat.Properties
    open Data.Nat.Properties.SemiringSolver

  postulate
    lem : ∀ {w₁ : W (i + size 1 (ys ∷ʳ k))} {w₂ : W (size 1 (i ∷ ys) + k)} (w≈w : w₁ VE.≈ w₂) →
          (uncurry _++_ ∘ map× id (ungroup ∘ With-⤙.extract-map ⟦ f ⟧ ∘ group 1 (ys ∷ʳ k)) ∘ splitAt′ i) w₁ VE.≈
          (uncurry _++_ ∘ map× (ungroup ∘ With-⤚.extract-map ⟦ f ⟧ ∘ group 1 (i ∷ ys)) id ∘ splitAt′ (size 1 (i ∷ ys))) w₂

  helper : id⤨ {i} ∥ f ⤙ (ys ∷ʳ k) ≈e (i ∷ ys) ⤚ f ∥ id⤨ {k}
  helper {w₁} {w₂} w≈w = VE.from-≡ (cong₂ _++_ (id⤨-id (proj₁ (splitAt′ i w₁)))
                                               (With-⤙.stretch-to-spec f (ys ∷ʳ k) (proj₂ (splitAt′ i w₁))))
            ⟨ VE.trans ⟩ lem w≈w
            ⟨ VE.trans ⟩ VE.from-≡ (cong₂ _++_ (sym (With-⤚.stretch-to-spec f (i ∷ ys) (proj₁ (splitAt′ (size 1 (i ∷ ys)) w₂))))
                                               (sym (id⤨-id (proj₂ (splitAt′ (size 1 (i ∷ ys)) w₂)))))

\end{code}
