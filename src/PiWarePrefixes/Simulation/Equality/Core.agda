open import PiWare.Atom using (Atomic)
open import PiWare.Gates using (Gates)

module PiWarePrefixes.Simulation.Equality.Core {At : Atomic} (Gt : Gates At) where

open import Data.Nat using (ℕ; _+_)
open import Data.Product using (proj₁; proj₂; _×_; uncurry; _,_)
open import Data.Sum using (inj₁; inj₂)
open import Data.Vec using (splitAt; _++_)
open import Function
open import Relation.Binary
open import Relation.Binary.Indexed as I using ()
open import Relation.Binary.PropositionalEquality as PropEq

open import PiWare.Circuit.Core Gt
open import PiWarePrefixes.Circuit.Context.Core Gt
open import PiWare.Simulation.Core Gt
open import PiWare.Synthesizable At using (W; untag)


--------------------------------------------------------------------------------
-- Low-level equivalence

-- Evaluational equivalence in the simplest way
infix 4 _≡e_
_≡e_ : ∀ {i o} (f g : ℂ' {Comb} i o) → Set
_≡e_ {i} f g = (w : W i) → ⟦ f ⟧' w ≡ ⟦ g ⟧' w

-- Congruence
-- Shows that a composed circuit is equal up to evaluation if the parts are
-- equal up to evaluation. This does not seem to imply composability of
-- equality, because it only goes one way.

-- Agda is not able to derive c₁ and c₂ from the type c₁ ≡e c₂

≡e-cong : ∀ {iₓ oₓ i o} (cxt : Cxt' iₓ oₓ i o) (f g : ℂ' iₓ oₓ) →
          f ≡e g → plugCxt' cxt f ≡e plugCxt' cxt g
≡e-cong ● f g p w = p w
≡e-cong (x ⟫'● cxt) f g p w = ≡e-cong cxt f g p (⟦ x ⟧' w)
≡e-cong (cxt ●⟫' x) f g p w rewrite ≡e-cong cxt f g p w = refl
≡e-cong (_|'●_ {i₁ = i₁} x cxt) f g p w
        rewrite ≡e-cong cxt f g p (proj₁ (proj₂ (splitAt i₁ w))) = refl
≡e-cong (_●|'_ {i₁ = i₁} cxt x) f g p w
        rewrite ≡e-cong cxt f g p (proj₁ (splitAt i₁ w)) = refl
≡e-cong (_|+'●_ {i₁ = i₁} x cxt) f g p w with untag {i₁} w
... | inj₁ _ = refl
... | inj₂ y = ≡e-cong cxt f g p y
≡e-cong (_●|+'_ {i₁ = i₁} cxt x) f g p w with untag {i₁} w
... | inj₁ y = ≡e-cong cxt f g p y
... | inj₂ _ = refl
≡e-cong (cxt ●Named x) f g p w = ≡e-cong cxt f g p w


--------------------------------------------------------------------------------
-- Equivalence within a data type

-- Wrap the equivalence in a data type to make agda not evaluate the equality.
-- That way agda keeps more information on what circuits are actually on both
-- sides.

-- maybe move this somewhere else
coerceℂ' : ∀ {cs i₁ o₁ i₂ o₂} → i₁ ≡ i₂ → o₁ ≡ o₂ → ℂ' {cs} i₁ o₁ → ℂ' {cs} i₂ o₂
coerceℂ' p q c rewrite p | q = c


-- Heterogeneous in the circuit size.
-- We need the proofs as indices on this data type, because we need this
-- information on the type level. You can't define a type for an equality in
-- which the sizes are `really` not equal.
infix 4 _≈⟦⟧_
data _≈⟦⟧_ {i₁ o₁ i₂ o₂ : ℕ} :
     (f : ℂ' {Comb} i₁ o₁) (g : ℂ' {Comb} i₂ o₂) → Set where
  Mk≈⟦⟧ : {f : ℂ' i₁ o₁} {g : ℂ' i₂ o₂} (pi : i₁ ≡ i₂) (po : o₁ ≡ o₂)
          (f≡g : coerceℂ' pi po f ≡e g) → _≈⟦⟧_ f g

i-equal : ∀ {i₁ o₁ i₂ o₂} {f : ℂ' i₁ o₁} {g : ℂ' i₂ o₂} →
          f ≈⟦⟧ g → i₁ ≡ i₂
i-equal (Mk≈⟦⟧ pi po f≡g) = pi

o-equal : ∀ {i₁ o₁ i₂ o₂} {f : ℂ' i₁ o₁} {g : ℂ' i₂ o₂} →
          f ≈⟦⟧ g → o₁ ≡ o₂
o-equal (Mk≈⟦⟧ pi po f≡g) = po



--------------------------------------------------------------------------------
-- Basic properties of ≈⟦⟧

≈⟦⟧-refl : ∀ {i o} {f : ℂ' i o} → f ≈⟦⟧ f
≈⟦⟧-refl = Mk≈⟦⟧ refl refl (λ w → refl)

≈⟦⟧-sym : ∀ {i₁ o₁ i₂ o₂} {f : ℂ' i₁ o₁} {g : ℂ' i₂ o₂} →
          f ≈⟦⟧ g → g ≈⟦⟧ f
≈⟦⟧-sym (Mk≈⟦⟧ refl refl f≡g) = Mk≈⟦⟧ refl refl (λ w → sym (f≡g w))

≈⟦⟧-trans : ∀ {i₁ o₁ i₂ o₂ i₃ o₃} {f : ℂ' i₁ o₁} {g : ℂ' i₂ o₂} {h : ℂ' i₃ o₃} →
            f ≈⟦⟧ g → g ≈⟦⟧ h → f ≈⟦⟧ h
≈⟦⟧-trans (Mk≈⟦⟧ refl refl f≡g) (Mk≈⟦⟧ refl refl g≡h) = Mk≈⟦⟧ refl refl (λ w → trans (f≡g w) (g≡h w))

≈⟦⟧-cong : ∀ {iₓ oₓ i o igₓ ogₓ} (cxt : Cxt' iₓ oₓ i o) →
             {f : ℂ' iₓ oₓ} {g : ℂ' igₓ ogₓ} →
             (f≈g : f ≈⟦⟧ g) →
             plugCxt' cxt f ≈⟦⟧ plugCxt' cxt (coerceℂ' (sym (i-equal f≈g)) (sym (o-equal f≈g)) g)
≈⟦⟧-cong cxt {f} {g} (Mk≈⟦⟧ refl refl f≡g) = Mk≈⟦⟧ refl refl (≡e-cong cxt f g f≡g)

≈⟦⟧-setoid : I.Setoid (ℕ × ℕ) _ _
≈⟦⟧-setoid = record
  { Carrier = uncurry ℂ'
  ; _≈_ = _≈⟦⟧_
  ; isEquivalence = record
    { refl = ≈⟦⟧-refl
    ; sym = ≈⟦⟧-sym
    ; trans = ≈⟦⟧-trans
    }
  }

--------------------------------------------------------------------------------
-- Equational reasoning

-- Our custom equational reasoning. Eqreasoning from the standard library does
-- not support indexed setoids.

module ≈⟦⟧-Reasoning where
  infix  2 _∎
  infixr 2 _≈⟦⟧⟨_⟩_ _≈⟦⟧⟨⟩_
  infix  1 begin_

  begin_ : ∀ {i₁ o₁ i₂ o₂} {f : ℂ' i₁ o₁} {g : ℂ' i₂ o₂} → f ≈⟦⟧ g → f ≈⟦⟧ g
  begin_ = id

  _≈⟦⟧⟨_⟩_ : ∀ {i₁ o₁ i₂ o₂ i₃ o₃} (f : ℂ' i₁ o₁) {g : ℂ' i₂ o₂} {h : ℂ' i₃ o₃} →
          f ≈⟦⟧ g → g ≈⟦⟧ h → f ≈⟦⟧ h
  _≈⟦⟧⟨_⟩_ _ = ≈⟦⟧-trans

  _≈⟦⟧⟨⟩_ : ∀ {i₁ o₁ i₂ o₂} (f : ℂ' i₁ o₁) {g : ℂ' i₂ o₂} →
          f ≈⟦⟧ g → f ≈⟦⟧ g
  _≈⟦⟧⟨⟩_ _ = id

  _∎ : ∀ {i o} (f : ℂ' i o) → f ≈⟦⟧ f
  _∎ _ = ≈⟦⟧-refl


--------------------------------------------------------------------------------
-- Heterogeneous low level equivalence

-- This one is useful to construct proofs for heterogeneous stuff on the low
-- level. _≈e_ is isomorphic with ≈⟦⟧ p q.

private
  import Data.Vec.Equality
  module VE = Data.Vec.Equality.PropositionalEquality

infix 4 _≈e_
_≈e_ : ∀ {i₁ o₁ i₂ o₂} (f : ℂ' {Comb} i₁ o₁) (g : ℂ' {Comb} i₂ o₂) → Set
_≈e_ {i₁} {i₂ = i₂} f g = {w₁ : W i₁} {w₂ : W i₂} (p : w₁ VE.≈ w₂) → ⟦ f ⟧' w₁ VE.≈ ⟦ g ⟧' w₂

≈⟦⟧-to-≈e : ∀ {i₁ o₁ i₂ o₂}
     {f : ℂ' {Comb} i₁ o₁} {g : ℂ' {Comb} i₂ o₂} →
     f ≈⟦⟧ g → f ≈e g
≈⟦⟧-to-≈e (Mk≈⟦⟧ refl refl f≡g) w≈w with (VE.to-≡ w≈w)
... | w≡w rewrite w≡w = VE.from-≡ (f≡g _)

≈e-to-≈⟦⟧ : ∀ {i₁ o₁ i₂ o₂} (pi : i₁ ≡ i₂) (po : o₁ ≡ o₂)
      {f : ℂ' {Comb} i₁ o₁} {g : ℂ' {Comb} i₂ o₂} →
      f ≈e g → f ≈⟦⟧ g
≈e-to-≈⟦⟧ refl refl ≈e = Mk≈⟦⟧ refl refl (λ w → VE.to-≡ (≈e (VE.from-≡ refl)))

