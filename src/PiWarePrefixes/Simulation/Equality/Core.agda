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

-- Low-level equivalence up to combinational evaluation
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
infix 4 _≡⟦⟧_
data _≡⟦⟧_ {i o : ℕ} (f g : ℂ' i o) : Set where
  from-≡e : (f≡g : f ≡e g) → f ≡⟦⟧ g

≡⟦⟧-refl : ∀ {i o} {f : ℂ' i o} → f ≡⟦⟧ f
≡⟦⟧-refl = from-≡e (λ w → refl)

≡⟦⟧-sym : ∀ {i o} {f g : ℂ' i o} → f ≡⟦⟧ g → g ≡⟦⟧ f
≡⟦⟧-sym (from-≡e f≡g) = from-≡e (λ w → sym (f≡g w))

≡⟦⟧-trans : ∀ {i o} {f g h : ℂ' i o} → f ≡⟦⟧ g → g ≡⟦⟧ h → f ≡⟦⟧ h
≡⟦⟧-trans (from-≡e f≡g) (from-≡e g≡h) = from-≡e (λ w → trans (f≡g w) (g≡h w))

≡⟦⟧-setoid : (i o : ℕ) → Setoid _ _
≡⟦⟧-setoid i o = record
  { Carrier = ℂ' i o
  ; _≈_ = _≡⟦⟧_
  ; isEquivalence = record
    { refl = ≡⟦⟧-refl
    ; sym = ≡⟦⟧-sym
    ; trans = ≡⟦⟧-trans
    }
  }

≡⟦⟧-cong : ∀ {iₓ oₓ i o} (cxt : Cxt' iₓ oₓ i o) {f g : ℂ' iₓ oₓ} →
          f ≡⟦⟧ g → plugCxt' cxt f ≡⟦⟧ plugCxt' cxt g
≡⟦⟧-cong cxt {f} {g} (from-≡e f≡g) = from-≡e (≡e-cong cxt f g f≡g)



-- --------------------------------------------------------------------------------
-- -- Heterogenous on top of high-level

-- resize : ∀ {cs i₁ o₁ i₂ o₂} → i₁ ≡ i₂ → o₁ ≡ o₂ → ℂ' {cs} i₁ o₁ → ℂ' {cs} i₂ o₂
-- resize p q c rewrite p | q = c

-- data ≈⟦⟧-with-proofs {i₁ o₁ i₂ o₂ : ℕ} :
--      (pi : i₁ ≡ i₂) (po : o₁ ≡ o₂)
--      (f : ℂ' {Comb} i₁ o₁) (g : ℂ' {Comb} i₂ o₂) → Set where
--   Mk≈⟦⟧ : {f : ℂ' i₁ o₁} {g : ℂ' i₂ o₂} (pi : i₁ ≡ i₂) (po : o₁ ≡ o₂)
--           (f≡g : resize pi po f ≡⟦⟧ g) → ≈⟦⟧-with-proofs pi po f g

-- _≈⟦⟧_ : ∀ {i o} (f g : ℂ' {Comb} i o) → Set
-- f ≈⟦⟧ g = ≈⟦⟧-with-proofs refl refl f g

-- ≈⟦⟧-refl : ∀ {i o} {f : ℂ' i o} → f ≈⟦⟧ f
-- ≈⟦⟧-refl = Mk≈⟦⟧ refl refl ≡⟦⟧-refl

-- ≈⟦⟧-sym : ∀ {i₁ o₁ i₂ o₂ pi po} {f : ℂ' i₁ o₁} {g : ℂ' i₂ o₂} →
--           ≈⟦⟧-with-proofs pi po f g → ≈⟦⟧-with-proofs (sym pi) (sym po) g f
-- ≈⟦⟧-sym (Mk≈⟦⟧ refl refl f≡g) = Mk≈⟦⟧ refl refl (≡⟦⟧-sym f≡g)

-- ≈⟦⟧-trans : ∀ {i₁ o₁ i₂ o₂ i₃ o₃} {f : ℂ' i₁ o₁} {g : ℂ' i₂ o₂} {h : ℂ' i₃ o₃}
--             {fgi : i₁ ≡ i₂} {fgo : o₁ ≡ o₂} {ghi : i₂ ≡ i₃} {gho : o₂ ≡ o₃} →
--             ≈⟦⟧-with-proofs fgi fgo f g → ≈⟦⟧-with-proofs ghi gho g h →
--             ≈⟦⟧-with-proofs (trans fgi ghi) (trans fgo gho) f h
-- ≈⟦⟧-trans (Mk≈⟦⟧ refl refl f≡g) (Mk≈⟦⟧ refl refl g≡h) = Mk≈⟦⟧ refl refl (≡⟦⟧-trans f≡g g≡h)

-- ≈⟦⟧-cong : ∀ {iₓ oₓ i o igₓ ogₓ} (cxt : Cxt' iₓ oₓ i o) →
--              {f : ℂ' iₓ oₓ} {g : ℂ' igₓ ogₓ} {pi : iₓ ≡ igₓ} {po : oₓ ≡ ogₓ} →
--              ≈⟦⟧-with-proofs pi po f g →
--              plugCxt' cxt f ≈⟦⟧ plugCxt' cxt (resize (sym pi) (sym po) g)
-- ≈⟦⟧-cong cxt (Mk≈⟦⟧ refl refl f≡g) = Mk≈⟦⟧ refl refl (≡⟦⟧-cong cxt f≡g)

-- ≈⟦⟧-setoid : (i o : ℕ) → Setoid _ _
-- ≈⟦⟧-setoid i o = record
--   { Carrier = ℂ' i o
--   ; _≈_ = ≈⟦⟧-with-proofs _ _
--   ; isEquivalence = record
--     { refl = ≈⟦⟧-refl
--     ; sym = ≈⟦⟧-sym
--     ; trans = ≈⟦⟧-trans
--     }
--   }

--------------------------------------------------------------------------------
-- Make high-level itself heterogeneous

resize : ∀ {cs i₁ o₁ i₂ o₂} → i₁ ≡ i₂ → o₁ ≡ o₂ → ℂ' {cs} i₁ o₁ → ℂ' {cs} i₂ o₂
resize p q c rewrite p | q = c

data ≈⟦⟧-with-proofs {i₁ o₁ i₂ o₂ : ℕ} :
     (pi : i₁ ≡ i₂) (po : o₁ ≡ o₂)
     (f : ℂ' {Comb} i₁ o₁) (g : ℂ' {Comb} i₂ o₂) → Set where
  Mk≈⟦⟧ : {f : ℂ' i₁ o₁} {g : ℂ' i₂ o₂} (pi : i₁ ≡ i₂) (po : o₁ ≡ o₂)
          (f≡g : resize pi po f ≡e g) → ≈⟦⟧-with-proofs pi po f g

infix 4 _≈⟦⟧_
_≈⟦⟧_ : ∀ {i o} (f g : ℂ' {Comb} i o) → Set
f ≈⟦⟧ g = ≈⟦⟧-with-proofs refl refl f g

≈⟦⟧-refl : ∀ {i o} {f : ℂ' i o} → f ≈⟦⟧ f
≈⟦⟧-refl = Mk≈⟦⟧ refl refl (λ w → refl)

≈⟦⟧-sym : ∀ {i₁ o₁ i₂ o₂ pi po} {f : ℂ' i₁ o₁} {g : ℂ' i₂ o₂} →
          ≈⟦⟧-with-proofs pi po f g → ≈⟦⟧-with-proofs (sym pi) (sym po) g f
≈⟦⟧-sym (Mk≈⟦⟧ refl refl f≡g) = Mk≈⟦⟧ refl refl (λ w → sym (f≡g w))

≈⟦⟧-trans : ∀ {i₁ o₁ i₂ o₂ i₃ o₃} {f : ℂ' i₁ o₁} {g : ℂ' i₂ o₂} {h : ℂ' i₃ o₃}
            {fgi : i₁ ≡ i₂} {fgo : o₁ ≡ o₂} {ghi : i₂ ≡ i₃} {gho : o₂ ≡ o₃} →
            ≈⟦⟧-with-proofs fgi fgo f g → ≈⟦⟧-with-proofs ghi gho g h →
            ≈⟦⟧-with-proofs (trans fgi ghi) (trans fgo gho) f h
≈⟦⟧-trans (Mk≈⟦⟧ refl refl f≡g) (Mk≈⟦⟧ refl refl g≡h) = Mk≈⟦⟧ refl refl (λ w → trans (f≡g w) (g≡h w))

≈⟦⟧-cong : ∀ {iₓ oₓ i o igₓ ogₓ} (cxt : Cxt' iₓ oₓ i o) →
             {f : ℂ' iₓ oₓ} {g : ℂ' igₓ ogₓ} {pi : iₓ ≡ igₓ} {po : oₓ ≡ ogₓ} →
             ≈⟦⟧-with-proofs pi po f g →
             plugCxt' cxt f ≈⟦⟧ plugCxt' cxt (resize (sym pi) (sym po) g)
≈⟦⟧-cong cxt {f} {g} (Mk≈⟦⟧ refl refl f≡g) = Mk≈⟦⟧ refl refl (≡e-cong cxt f g f≡g)

≈⟦⟧-setoid : (i o : ℕ) → Setoid _ _
≈⟦⟧-setoid i o = record
  { Carrier = ℂ' i o
  ; _≈_ = _≈⟦⟧_
  ; isEquivalence = record
    { refl = ≈⟦⟧-refl
    ; sym = ≈⟦⟧-sym
    ; trans = ≈⟦⟧-trans
    }
  }

private
  import Data.Vec.Equality
  module VE = Data.Vec.Equality.PropositionalEquality

infix 4 _≈e_
_≈e_ : ∀ {i₁ o₁ i₂ o₂} (f : ℂ' {Comb} i₁ o₁) (g : ℂ' {Comb} i₂ o₂) → Set
_≈e_ {i₁} {i₂ = i₂} f g = {w₁ : W i₁} {w₂ : W i₂} (p : w₁ VE.≈ w₂) → ⟦ f ⟧' w₁ VE.≈ ⟦ g ⟧' w₂

≈⟦⟧-to-≈e : ∀ {i₁ o₁ i₂ o₂} (pi : i₁ ≡ i₂) (po : o₁ ≡ o₂)
     {f : ℂ' {Comb} i₁ o₁} {g : ℂ' {Comb} i₂ o₂} →
     ≈⟦⟧-with-proofs pi po f g → f ≈e g
≈⟦⟧-to-≈e refl refl (Mk≈⟦⟧ .refl .refl f≡g) w≈w with (VE.to-≡ w≈w)
... | w≡w rewrite w≡w = VE.from-≡ (f≡g _)

≈e-to-≈⟦⟧ : ∀ {i₁ o₁ i₂ o₂} (pi : i₁ ≡ i₂) (po : o₁ ≡ o₂)
      {f : ℂ' {Comb} i₁ o₁} {g : ℂ' {Comb} i₂ o₂} →
      f ≈e g → ≈⟦⟧-with-proofs pi po f g
≈e-to-≈⟦⟧ refl refl ≈e = Mk≈⟦⟧ refl refl (λ w → VE.to-≡ (≈e (VE.from-≡ refl)))


module ≡⟦⟧-Reasoning {i o : ℕ} where
  private
    import Relation.Binary.EqReasoning
    module EqR {i o : ℕ} = Relation.Binary.EqReasoning (≡⟦⟧-setoid i o)
      -- hiding (_≡⟨_⟩_; _≡⟨⟩_)
      renaming (_≈⟨_⟩_ to _≡⟦⟧⟨_⟩_)

  open EqR {i} {o} public

  infixr 2 _≡e⟨_⟩_
  _≡e⟨_⟩_ : ∀ x {y z} → x ≡e y → y IsRelatedTo z → x IsRelatedTo z
  x ≡e⟨ x≡y ⟩ y~z = x ≡⟦⟧⟨ from-≡e x≡y ⟩ y~z
