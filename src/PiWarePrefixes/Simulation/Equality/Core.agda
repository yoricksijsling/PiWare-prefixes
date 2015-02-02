open import PiWare.Atom using (Atomic)
open import PiWare.Gates using (Gates)

module PiWarePrefixes.Simulation.Equality.Core {At : Atomic} (Gt : Gates At) where

open import Data.Nat using (ℕ; _+_)
open import Data.Product using (proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Vec using (splitAt; _++_)
open import Function
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as PropEq

open import PiWare.Circuit.Core Gt
open import PiWarePrefixes.Circuit.Context.Core Gt
open import PiWare.Simulation.Core Gt
open import PiWare.Synthesizable At using (W; untag)

-- Equivalence up to combinational evaluation

infix 4 _≈⟦⟧_
_≈⟦⟧_ : ∀ {i o} (f g : ℂ' {Comb} i o) → Set
_≈⟦⟧_ {i} f g = (w : W i) → ⟦ f ⟧' w ≡ ⟦ g ⟧' w

≈⟦⟧-setoid : (i o : ℕ) → Setoid _ _
≈⟦⟧-setoid i o = record
  { Carrier = ℂ' {Comb} i o
  ; _≈_     = _≈⟦⟧_
  ; isEquivalence = record
    { refl    = λ w         → refl
    ; sym     = λ i≡j w     → sym (i≡j w)
    ; trans   = λ i≡j j≡k w → trans (i≡j w) (j≡k w)
    }
  }

-- Congruence
-- Shows that a composed circuit is equal up to evaluation if the parts are
-- equal up to evaluation. This does not seem to imply composability of
-- equality, because it only goes one way.

-- Agda is not able to derive c₁ and c₂ from the type c₁ ≈⟦⟧ c₂

≈⟦⟧-cong : ∀ {iₓ oₓ i o} (cxt : Cxt' iₓ oₓ i o) (f g : ℂ' iₓ oₓ) →
          f ≈⟦⟧ g → plugCxt' cxt f ≈⟦⟧ plugCxt' cxt g
≈⟦⟧-cong ● f g p w = p w
≈⟦⟧-cong (x ⟫'● cxt) f g p w = ≈⟦⟧-cong cxt f g p (⟦ x ⟧' w)
≈⟦⟧-cong (cxt ●⟫' x) f g p w rewrite ≈⟦⟧-cong cxt f g p w = refl
≈⟦⟧-cong (_|'●_ {i₁ = i₁} x cxt) f g p w
        rewrite ≈⟦⟧-cong cxt f g p (proj₁ (proj₂ (splitAt i₁ w))) = refl
≈⟦⟧-cong (_●|'_ {i₁ = i₁} cxt x) f g p w
        rewrite ≈⟦⟧-cong cxt f g p (proj₁ (splitAt i₁ w)) = refl
≈⟦⟧-cong (_|+'●_ {i₁ = i₁} x cxt) f g p w with untag {i₁} w
... | inj₁ _ = refl
... | inj₂ y = ≈⟦⟧-cong cxt f g p y
≈⟦⟧-cong (_●|+'_ {i₁ = i₁} cxt x) f g p w with untag {i₁} w
... | inj₁ y = ≈⟦⟧-cong cxt f g p y
... | inj₂ _ = refl
≈⟦⟧-cong (cxt ●Named x) f g p w = ≈⟦⟧-cong cxt f g p w


--------------------------------------------------
-- Equivalence within a data type

infix 4 _≡⟦⟧_
data _≡⟦⟧_ {i o : ℕ} (f g : ℂ' {Comb} i o) : Set where
  from-≈⟦⟧ : (f≡g : f ≈⟦⟧ g) → f ≡⟦⟧ g

to-≈⟦⟧ : {i o : ℕ} {f g : ℂ' {Comb} i o} → f ≡⟦⟧ g → f ≈⟦⟧ g
to-≈⟦⟧ (from-≈⟦⟧ f≡g) = f≡g

≡⟦⟧-refl : ∀ {i o} {f : ℂ' {Comb} i o} → f ≡⟦⟧ f
≡⟦⟧-refl = from-≈⟦⟧ (λ w → refl)

≡⟦⟧-sym : ∀ {i o} {f g : ℂ' {Comb} i o} → f ≡⟦⟧ g → g ≡⟦⟧ f
≡⟦⟧-sym (from-≈⟦⟧ f≡g) = from-≈⟦⟧ (λ w → sym (f≡g w))

≡⟦⟧-trans : ∀ {i o} {f g h : ℂ' {Comb} i o} → f ≡⟦⟧ g → g ≡⟦⟧ h → f ≡⟦⟧ h
≡⟦⟧-trans (from-≈⟦⟧ f≡g) (from-≈⟦⟧ g≡h) = from-≈⟦⟧ (λ w → trans (f≡g w) (g≡h w))

≡⟦⟧-setoid : (i o : ℕ) → Setoid _ _
≡⟦⟧-setoid i o = record
  { Carrier = ℂ' {Comb} i o
  ; _≈_ = _≡⟦⟧_
  ; isEquivalence = record
    { refl = ≡⟦⟧-refl
    ; sym = ≡⟦⟧-sym
    ; trans = ≡⟦⟧-trans
    }
  }

≡⟦⟧-cong : ∀ {iₓ oₓ i o} (cxt : Cxt' iₓ oₓ i o) {f g : ℂ' iₓ oₓ} →
          f ≡⟦⟧ g → plugCxt' cxt f ≡⟦⟧ plugCxt' cxt g
≡⟦⟧-cong cxt {f} {g} (from-≈⟦⟧ f≡g) = from-≈⟦⟧ (≈⟦⟧-cong cxt f g f≡g)

module ≡⟦⟧-Reasoning {i o : ℕ} where
  private
    import Relation.Binary.EqReasoning
    module EqR {i o : ℕ} = Relation.Binary.EqReasoning (≡⟦⟧-setoid i o)
      -- hiding (_≡⟨_⟩_; _≡⟨⟩_)
      renaming (_≈⟨_⟩_ to _≡⟦⟧⟨_⟩_)

  open EqR {i} {o} public

  infixr 2 _≈⟦⟧⟨_⟩_
  _≈⟦⟧⟨_⟩_ : ∀ x {y z} → x ≈⟦⟧ y → y IsRelatedTo z → x IsRelatedTo z
  x ≈⟦⟧⟨ x≡y ⟩ y~z = x ≡⟦⟧⟨ from-≈⟦⟧ x≡y ⟩ y~z
