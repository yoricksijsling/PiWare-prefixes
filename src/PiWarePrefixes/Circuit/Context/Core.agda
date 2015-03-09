open import PiWare.Atom using (Atomic)
open import PiWare.Gates using (Gates)

module PiWarePrefixes.Circuit.Context.Core {At : Atomic} (Gt : Gates At) where

open import Data.Nat using (ℕ; suc; _+_; _⊔_)
open import Data.String using (String)
open import Data.Sum as Sum using (inj₁; inj₂)
open import Data.Vec using (_++_; splitAt)
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)

open import PiWare.Circuit.Core Gt
open import PiWare.Simulation.Core Gt using (⟦_⟧')
open import PiWarePrefixes.Simulation.Equality.Core Gt as SimEq using (Mk≈⟦⟧; easy-≈⟦⟧)
open import PiWare.Synthesizable At using (W; untag)

private
  import Data.Vec.Equality
  module VE = Data.Vec.Equality.PropositionalEquality

-- Indices describe the hole, parameters describe the full circuit when the hole is plugged.

data Cxt' {csₓ : CombSeq} (iₓ oₓ : ℕ) : {cs : CombSeq} → ℕ → ℕ → Set where
    ●-cxt : Cxt' {csₓ} iₓ oₓ {csₓ} iₓ oₓ
    DelayLoop●-cxt : ∀ {i o l} → Cxt' {csₓ} iₓ oₓ {Comb} (i + l) (o + l) → Cxt' {csₓ} iₓ oₓ {Seq} i o
    _⟫'●-cxt_ : ∀ {cs i m o} → ℂ' {cs} i m → Cxt' {csₓ} iₓ oₓ {cs} m o → Cxt' {csₓ} iₓ oₓ {cs} i o
    _●⟫'-cxt_ : ∀ {cs i m o} → Cxt' {csₓ} iₓ oₓ {cs} i m → ℂ' {cs} m o → Cxt' {csₓ} iₓ oₓ {cs} i o
    _|'●-cxt_ : ∀ {cs i o j p} → ℂ' {cs} i o → Cxt' {csₓ} iₓ oₓ {cs} j p → Cxt' {csₓ} iₓ oₓ {cs} (i + j) (o + p)
    _●|'-cxt_ : ∀ {cs i o j p} → Cxt' {csₓ} iₓ oₓ {cs} i o → ℂ' {cs} j p → Cxt' {csₓ} iₓ oₓ {cs} (i + j) (o + p)
    _|+'●-cxt_ : ∀ {cs i j o} → ℂ' {cs} i o → Cxt' {csₓ} iₓ oₓ {cs} j o → Cxt' {csₓ} iₓ oₓ {cs} (suc (i ⊔ j)) o
    _●|+'-cxt_ : ∀ {cs i j o} → Cxt' {csₓ} iₓ oₓ {cs} i o → ℂ' {cs} j o → Cxt' {csₓ} iₓ oₓ {cs} (suc (i ⊔ j)) o
    _●Named-cxt_ : ∀ {cs i o} → Cxt' {csₓ} iₓ oₓ {cs} i o → String → Cxt' {csₓ} iₓ oₓ {cs} i o

infixr 5 _|'●-cxt_  _●|'-cxt_
infixr 5 _|+'●-cxt_ _●|+'-cxt_
infixl 4 _⟫'●-cxt_  _●⟫'-cxt_

plugCxt' : ∀ {csₓ iₓ oₓ cs i o} → Cxt' {csₓ} iₓ oₓ {cs} i o → ℂ' {csₓ} iₓ oₓ → ℂ' {cs} i o
plugCxt' ●-cxt                cₓ = cₓ
plugCxt' (DelayLoop●-cxt cxt) cₓ = DelayLoop (plugCxt' cxt cₓ)
plugCxt' (x    ⟫'●-cxt cxt)   cₓ = x ⟫' (plugCxt' cxt cₓ)
plugCxt' (cxt ●⟫'-cxt    x)   cₓ = (plugCxt' cxt cₓ) ⟫' x
plugCxt' (x    |'●-cxt cxt)   cₓ = x |' (plugCxt' cxt cₓ)
plugCxt' (cxt ●|'-cxt    x)   cₓ = (plugCxt' cxt cₓ) |' x
plugCxt' (x    |+'●-cxt cxt)  cₓ = x |+' (plugCxt' cxt cₓ)
plugCxt' (cxt ●|+'-cxt    x)  cₓ = (plugCxt' cxt cₓ) |+' x
plugCxt' (cxt ●Named-cxt s)   cₓ = (plugCxt' cxt cₓ) Named s


-- For now, this only works with combinational circuits, because SimEq.≈⟦⟧ only
-- works on combinational circuits too.

data _Cxt-≈⟦⟧_ {iₓ¹ oₓ¹ iₓ² oₓ²} :
         ∀ {i¹ o¹ i² o²} →
         (cxt¹ : Cxt' {Comb} iₓ¹ oₓ¹ {Comb} i¹ o¹) → (cxt² : Cxt' {Comb} iₓ² oₓ² {Comb} i² o²) → Set where
    ● : ●-cxt Cxt-≈⟦⟧ ●-cxt
    _⟫'●_ : ∀ {i¹ m¹ o¹} {c¹ : ℂ' i¹ m¹} {cxt¹ : Cxt' iₓ¹ oₓ¹ m¹ o¹} →
                 ∀ {i² m² o²} {c² : ℂ' i² m²} {cxt² : Cxt' iₓ² oₓ² m² o²} →
                 c¹ SimEq.≈⟦⟧ c² → cxt¹ Cxt-≈⟦⟧ cxt² →
                 (c¹ ⟫'●-cxt cxt¹) Cxt-≈⟦⟧ (c² ⟫'●-cxt cxt²)
    _●⟫'_ : ∀ {i¹ m¹ o¹} {cxt¹ : Cxt' iₓ¹ oₓ¹ i¹ m¹} {c¹ : ℂ' m¹ o¹} →
                 ∀ {i² m² o²} {cxt² : Cxt' iₓ² oₓ² i² m²} {c² : ℂ' m² o²} →
                 cxt¹ Cxt-≈⟦⟧ cxt² → c¹ SimEq.≈⟦⟧ c² →
                 (cxt¹ ●⟫'-cxt c¹) Cxt-≈⟦⟧ (cxt² ●⟫'-cxt c²)
    _|'●_ : ∀ {i¹ o¹ j¹ p¹} {c¹ : ℂ' i¹ o¹} {cxt¹ : Cxt' iₓ¹ oₓ¹ j¹ p¹} →
                 ∀ {i² o² j² p²} {c² : ℂ' i² o²} {cxt² : Cxt' iₓ² oₓ² j² p²} →
                 c¹ SimEq.≈⟦⟧ c² → cxt¹ Cxt-≈⟦⟧ cxt² →
                 (c¹ |'●-cxt cxt¹) Cxt-≈⟦⟧ (c² |'●-cxt cxt²)
    _●|'_ : ∀ {i¹ o¹ j¹ p¹} {cxt¹ : Cxt' iₓ¹ oₓ¹ i¹ o¹} {c¹ : ℂ' j¹ p¹} →
                 ∀ {i² o² j² p²} {cxt² : Cxt' iₓ² oₓ² i² o²} {c² : ℂ' j² p²} →
                 cxt¹ Cxt-≈⟦⟧ cxt² → c¹ SimEq.≈⟦⟧ c² →
                 (cxt¹ ●|'-cxt c¹) Cxt-≈⟦⟧ (cxt² ●|'-cxt c²)
    _|+'●_ : ∀ {i¹ j¹ o¹} {c¹ : ℂ' i¹ o¹} {cxt¹ : Cxt' iₓ¹ oₓ¹ j¹ o¹} →
                  ∀ {i² j² o²} {c² : ℂ' i² o²} {cxt² : Cxt' iₓ² oₓ² j² o²} →
                  c¹ SimEq.≈⟦⟧ c² → cxt¹ Cxt-≈⟦⟧ cxt² →
                  (c¹ |+'●-cxt cxt¹) Cxt-≈⟦⟧ (c² |+'●-cxt cxt²)
    _●|+'_ : ∀ {i¹ j¹ o¹} {cxt¹ : Cxt' iₓ¹ oₓ¹ i¹ o¹} {c¹ : ℂ' j¹ o¹} →
                  ∀ {i² j² o²} {cxt² : Cxt' iₓ² oₓ² i² o²} {c² : ℂ' j² o²} →
                  cxt¹ Cxt-≈⟦⟧ cxt² → c¹ SimEq.≈⟦⟧ c² →
                  (cxt¹ ●|+'-cxt c¹) Cxt-≈⟦⟧ (cxt² ●|+'-cxt c²)
    _●Named_ : ∀ {i¹ o¹} {cxt¹ : Cxt' iₓ¹ oₓ¹ i¹ o¹} {s¹ : String} →
                    ∀ {i² o²} {cxt² : Cxt' iₓ² oₓ² i² o²} {s² : String} →
                    cxt¹ Cxt-≈⟦⟧ cxt² → s¹ ≡ s² →
                    (cxt¹ ●Named-cxt s¹) Cxt-≈⟦⟧ (cxt² ●Named-cxt s²)

infixr 5 _|'●_  _●|'_
infixr 5 _|+'●_ _●|+'_
infixl 4 _⟫'●_  _●⟫'_

bla : {i o : ℕ} {f : ℂ' i o} → f SimEq.≈⟦⟧ f
bla = SimEq.≈⟦⟧-refl

-- Congruence
-- Shows that a composed circuit is equal up to evaluation if the parts are
-- equal up to evaluation. This does not seem to imply composability of
-- equality, because it only goes one way.

-- Agda is not able to derive c₁ and c₂ from the type c₁ ≡e c₂

wcong₂ : {o : ℕ → ℕ → ℕ} (f : ∀ {n m} → W n → W m → W (o n m)) →
         ∀ {n₁ n₂ m₁ m₂} {x y u v} → x VE.≈ y → u VE.≈ v → f {n₁} {m₁} x u VE.≈ f {n₂} {m₂} y v
wcong₂ f x≈y u≈v with VE.length-equal x≈y | VE.length-equal u≈v
... | refl | refl with VE.to-≡ x≈y | VE.to-≡ u≈v
... | refl | refl = VE.refl _

≈⟦⟧-cong : ∀ {iₓ¹ oₓ¹ iₓ² oₓ² i¹ o¹ i² o²} →
             {cxt¹ : Cxt' iₓ¹ oₓ¹ i¹ o¹} {cxt² : Cxt' iₓ² oₓ² i² o²} →
             {c¹ : ℂ' iₓ¹ oₓ¹} {c² : ℂ' iₓ² oₓ²} →
             (cxts : cxt¹ Cxt-≈⟦⟧ cxt²) (holes : c¹ SimEq.≈⟦⟧ c²) →
             plugCxt' cxt¹ c¹ SimEq.≈⟦⟧ plugCxt' cxt² c²
≈⟦⟧-cong ● holes = holes
≈⟦⟧-cong ((Mk≈⟦⟧ refl f≈f) ⟫'● cxts) holes with ≈⟦⟧-cong cxts holes
... | Mk≈⟦⟧ refl g≈g = easy-≈⟦⟧ (g≈g ∘ f≈f ∘ VE.refl)
≈⟦⟧-cong (cxts ●⟫' (Mk≈⟦⟧ refl g≈g)) holes with ≈⟦⟧-cong cxts holes
... | Mk≈⟦⟧ refl f≈f = easy-≈⟦⟧ (g≈g ∘ f≈f ∘ VE.refl)
≈⟦⟧-cong (Mk≈⟦⟧ refl f≈f |'● cxts) holes with ≈⟦⟧-cong cxts holes
... | Mk≈⟦⟧ refl g≈g = easy-≈⟦⟧ (λ w → wcong₂ _++_ (f≈f (VE.refl _)) (g≈g (VE.refl _)) )
≈⟦⟧-cong (cxts ●|' Mk≈⟦⟧ refl g≈g) holes with ≈⟦⟧-cong cxts holes
... | Mk≈⟦⟧ refl f≈f = easy-≈⟦⟧ (λ w → wcong₂ _++_ (f≈f (VE.refl _)) (g≈g (VE.refl _)))
≈⟦⟧-cong (_|+'●_ {i¹} {j¹} (Mk≈⟦⟧ refl f≈f) cxts) holes with ≈⟦⟧-cong cxts holes
-- ... | Mk≈⟦⟧ refl g≈g = easy-≈⟦⟧ (λ w → {!f≈f ∘ VE.refl!})
... | Mk≈⟦⟧ refl g≈g = easy-≈⟦⟧ helper
  where
  helper : ∀ w → Sum.[ _ , _ ]′ (untag {i¹} w) VE.≈ Sum.[ _ , _ ]′ (untag {i¹} w)
  helper w with untag {i¹} w
  helper w | inj₁ x = f≈f (VE.refl x)
  helper w | inj₂ y = g≈g (VE.refl y)
≈⟦⟧-cong (_●|+'_ {i¹} {j¹} cxts (Mk≈⟦⟧ refl g≈g)) holes with ≈⟦⟧-cong cxts holes
... | Mk≈⟦⟧ refl f≈f = easy-≈⟦⟧ helper
  where
  helper : ∀ w → Sum.[ _ , _ ]′ (untag {i¹} w) VE.≈ Sum.[ _ , _ ]′ (untag {i¹} w)
  helper w with untag {i¹} w
  helper w | inj₁ x = f≈f (VE.refl x)
  helper w | inj₂ y = g≈g (VE.refl y)
≈⟦⟧-cong (cxts ●Named refl) holes with ≈⟦⟧-cong cxts holes
... | Mk≈⟦⟧ refl f≈g = easy-≈⟦⟧ (f≈g ∘ VE.refl)
