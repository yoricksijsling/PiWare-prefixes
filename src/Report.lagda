\begin{code}
open import PiWare.Atom using (Atomic; module Atomic)
open import PiWare.Gates using (Gates; module Gates)
open import PiWarePrefixes.Circuit.Monoid using (module ℂ-Monoid; ℂ-Monoid)

module Report {At : Atomic} {Gt : Gates At}
              {ℂ-monoid : ℂ-Monoid {Gt = Gt}} where

open ℂ-Monoid ℂ-monoid using (plusℂ; plusℂ-assoc)

open import Data.Nat using (ℕ; _+_; suc; zero)
open import Data.Nat.Properties.Simple using (+-comm; +-suc)
open import Data.Vec using (Vec)
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality as PropEq using (_≡_; refl)

open Atomic At using (W)
open Gates At Gt using (|in|; |out|)

open import PiWare.Plugs.Core using (_⤪_)

private
  import Data.Vec.Equality
  module VE = Data.Vec.Equality.PropositionalEquality

_≈ᵥ_ : ∀ {a} {A : Set a} {m} → Vec A m → ∀ {n} → Vec A n → Set a
_≈ᵥ_ = VE._≈_

module Circuit where
  mutual
\end{code}

%<*circuit-old>
\begin{code}
    data ℂ : ℕ → ℕ → Set where
      Gate : ∀ g → ℂ (|in| g) (|out| g)
      Plug : ∀ {i o} → i ⤪ o → ℂ i o
      _⟫_ : ∀ {i m o} → ℂ i m → ℂ m o → ℂ i o
      _∥_ : ∀ {i₁ o₁ i₂ o₂} → ℂ i₁ o₁ → ℂ i₂ o₂ → ℂ (i₁ + i₂) (o₁ + o₂)
      DelayLoop : ∀ {i o l} (c : ℂ (i + l) (o + l)) {p : comb c} → ℂ i o
\end{code}
%</circuit-old>

\begin{code}
    postulate
      comb : ∀ {i o} → ℂ i o → Set
\end{code}

%<*circuit>
\begin{code}
    data CombSeq : Set where
      σ : CombSeq -- Required to be combinational
      ω : CombSeq -- Allowed to be sequential
    data ℂ′ : {p : CombSeq} → ℕ → ℕ → Set where
      Gate  : ∀ {p} g             → ℂ′ {p} (|in| g) (|out| g)
      Plug  : ∀ {i o p} → i ⤪ o → ℂ′ {p} i o
      _⟫_ : ∀ {i m o p}       → ℂ′ {p} i m   → ℂ′ {p} m o   → ℂ′ {p} i o
      _∥_ : ∀ {i₁ o₁ i₂ o₂ p} → ℂ′ {p} i₁ o₁ → ℂ′ {p} i₂ o₂ →
        ℂ′ {p} (i₁ + i₂) (o₁ + o₂)
      DelayLoop : ∀ {i o l} → ℂ′ {σ} (i + l) (o + l) → ℂ′ {ω} i o
\end{code}
%</circuit>

\begin{code}
open import PiWare.Circuit {Gt = Gt}
  renaming (ℂ to ℂ-orig)
open import PiWare.Interface using (Ix)
open import PiWare.Plugs Gt renaming (id⤨ to id⤨-orig)
open import PiWare.Simulation Gt
open import PiWare.Synthesizable At using (untag)

ℂ : Ix → Ix → Set
ℂ = ℂ-orig {σ}

id⤨ : (n : ℕ) → ℂ n n
id⤨ n = id⤨-orig


module Eq where
\end{code}

%<*eq1>
\begin{code}
  _≋₁_ : ∀ {i o} (f g : ℂ i o) → Set
  f ≋₁ g = ∀ w → ⟦ f ⟧ w ≡ ⟦ g ⟧ w
\end{code}
%</eq1>

%<*eq-e>
\begin{code}
  _≊_ : ∀ {i₁ o₁ i₂ o₂} (f : ℂ i₁ o₁) (g : ℂ i₂ o₂) → Set
  f ≊ g = ∀ {w₁ w₂} → (w₁ ≈ᵥ w₂) → ⟦ f ⟧ w₁ ≈ᵥ ⟦ g ⟧ w₂
\end{code}
%</eq-e>

%<*eq-e-incomplete>
\begin{code}
  ≊-incomplete : id⤨ 0 ≊ id⤨ 1
  ≊-incomplete ()
\end{code}
%</eq-e-incomplete>

%<*eq>
\begin{code}
  data _≋_ {i₁ o₁ i₂ o₂ : ℕ} : (f : ℂ i₁ o₁) (g : ℂ i₂ o₂) → Set where
    Mk≋ : {f : ℂ i₁ o₁} {g : ℂ i₂ o₂} (pi : i₁ ≡ i₂) (f≈g : f ≊ g) → f ≋ g
\end{code}
%</eq>

\begin{code}

open import PiWarePrefixes.Simulation.Equality.Core {Gt = Gt}
     renaming (_≈⟦⟧_ to _≋_; ≈⟦⟧-refl to ≋-refl; ≈⟦⟧-sym to ≋-sym)
open ≈⟦⟧-Reasoning renaming (_≈⟦⟧⟨_⟩_ to _≋⟨_⟩_; _≈⟦⟧⟨⟩_ to _≋⟨⟩_)

module Cong where
  open import PiWarePrefixes.Patterns.Stretch {Gt = Gt} as Stretch using (_⤙_)
  open import PiWarePrefixes.Patterns.Scan {ℂ-monoid = ℂ-monoid} using (scan)

  postulate
\end{code}

%<*seq-and-par-cong>
\begin{code}
    _⟫-cong_ : ∀ {i¹ m¹ o¹} {c¹ : ℂ i¹ m¹} {d¹ : ℂ m¹ o¹} →
               ∀ {i² m² o²} {c² : ℂ i² m²} {d² : ℂ m² o²} →
               c¹ ≋ c² → d¹ ≋ d² → c¹ ⟫ d¹ ≋ c² ⟫ d²
    _∥-cong_ : ∀ {i¹ o¹ j¹ p¹} {c¹ : ℂ i¹ o¹} {d¹ : ℂ j¹ p¹} →
               ∀ {i² o² j² p²} {c² : ℂ i² o²} {d² : ℂ j² p²} →
               c¹ ≋ c² → d¹ ≋ d² → c¹ ∥ d¹ ≋ c² ∥ d²
\end{code}
%</seq-and-par-cong>

%<*scan-and-stretch-cong>
\begin{code}
    scan-cong : ∀ {m n} → scan m ≋ scan n
    _⤙-cong_ : ∀ {m n} {f : ℂ m m} {g : ℂ n n}
      {as : Vec ℕ m} {bs : Vec ℕ n} →
      f ≋ g → as ≈ᵥ bs → f ⤙ as ≋ g ⤙ bs
\end{code}
%</scan-and-stretch-cong>

\begin{code}

open import PiWarePrefixes.Simulation.Properties {Gt = Gt}
     renaming (_∥-cong_ to _∥-cong_)

module Context where
\end{code}

%<*congTy>
\begin{code}
  cong : ∀ {A B : Set} → (f : A → B) → {x y : A} → x ≡ y → f x ≡ f y
\end{code}
%</congTy>

\begin{code}
  cong f refl = refl

  data Cxt (iₓ oₓ : ℕ) : ℕ → ℕ → Set where
    ●-cxt : Cxt iₓ oₓ iₓ oₓ
    _●∥-cxt_ : ∀ {i o j p} → Cxt iₓ oₓ i o → ℂ j p → Cxt iₓ oₓ (i + j) (o + p)
\end{code}

%<*plugCxtTy>
\begin{code}
  plugCxt : ∀ {iₓ oₓ i o} → Cxt iₓ oₓ i o → ℂ iₓ oₓ → ℂ i o
\end{code}
%</plugCxtTy>

\begin{code}
  plugCxt ●-cxt v = v
  plugCxt (cxt ●∥-cxt x) v = plugCxt cxt v ∥ x

  postulate
\end{code}

%<*eq-cong>
\begin{code}
    ≋-cong : ∀ {iₓ oₓ i o} → (cxt : Cxt iₓ oₓ i o) → {f g : ℂ iₓ oₓ} →
             f ≋ g → plugCxt cxt f ≋ plugCxt cxt g
\end{code}
%</eq-cong>

\begin{code}
  data _≈ₓ_ {iₓ¹ oₓ¹ iₓ² oₓ²} : ∀ {i¹ o¹ i² o²} →
       (cxt¹ : Cxt iₓ¹ oₓ¹ i¹ o¹) → (cxt² : Cxt iₓ² oₓ² i² o²) → Set where
    ● : ●-cxt ≈ₓ ●-cxt
    _●∥_ : ∀ {i¹ o¹ j¹ p¹} {cxt¹ : Cxt iₓ¹ oₓ¹ i¹ o¹} {c¹ : ℂ j¹ p¹} →
           ∀ {i² o² j² p²} {cxt² : Cxt iₓ² oₓ² i² o²} {c² : ℂ j² p²} →
           cxt¹ ≈ₓ cxt² → c¹ ≋ c² →
           (cxt¹ ●∥-cxt c¹) ≈ₓ (cxt² ●∥-cxt c²)
\end{code}

\begin{code}
  postulate
\end{code}

%<*eq-cong2>
\begin{code}
    ≋-cong₂ : ∀ {iₓ¹ oₓ¹ i¹ o¹ iₓ² oₓ² i² o²}
      {cxt¹ : Cxt iₓ¹ oₓ¹ i¹ o¹} {cxt² : Cxt iₓ² oₓ² i² o²}
      {f : ℂ iₓ¹ oₓ¹} {g : ℂ iₓ² oₓ²} →
      cxt¹ ≈ₓ cxt² → f ≋ g → plugCxt cxt¹ f ≋ plugCxt cxt² g
\end{code}
%</eq-cong2>

%<*cong2-example>
\begin{code}
  ≋-cong₂-example : ∀ {m n} (f : ℂ m m) (g : ℂ n n) →
                    ((f ⟫ id⤨ m) ∥ g) ≋ (f ∥ g)
  ≋-cong₂-example f g = ≋-cong₂ (● ●∥ ≋-refl) (⟫-right-identity _)
\end{code}
%</cong2-example>

\begin{code}
  ≋-cong₂-example-impl : ∀ {m n} (f : ℂ m m) (g : ℂ n n) →
                    ((f ⟫ id⤨ m) ∥ g) ≋ (f ∥ g)
  ≋-cong₂-example-impl f g =
\end{code}

%<*cong2-example-impl>
\begin{code}
    ≋-cong₂ (● ●∥ ≋-refl) (⟫-right-identity _)
\end{code}
%</cong2-example-impl>


\begin{code}
  x-cong-example : ∀ {m n} (f : ℂ m m) (g : ℂ n n) →
                   ((f ⟫ id⤨ m) ∥ g) ≋ (f ∥ g)
  x-cong-example f g =
\end{code}

%<*x-cong-example-impl>
\begin{code}
     ⟫-right-identity _ ∥-cong ≋-refl
\end{code}
%</x-cong-example-impl>

\begin{code}
module Plugs where
  open import Data.Vec using (tabulate; lookup; map; allFin)

  postulate
    vec-⤪ :
\end{code}

%<*vec-op-ty>
\begin{code}
      ∀ {i o} {X : Set} → Vec X i → Vec X o
\end{code}
%</vec-op-ty>

%<*vec-morphism>
\begin{code}
  record Vec-Morphism (i : ℕ) (o : ℕ) : Set₁ where
    field
      op : {X : Set} → Vec X i → Vec X o
      op-map-commute : {X Y : Set} (f : X → Y) → -- Free property
        (w : Vec X i) → (op ∘ map f) w ≡ (map f ∘ op) w
\end{code}
%</vec-morphism>

%<*plug-by-morphism>
\begin{code}
  plug-by-morphism : ∀ {i o} → Vec-Morphism i o → ℂ i o
  plug-by-morphism M = Plug (Vec-Morphism.op M (allFin _))
\end{code}
%</plug-by-morphism>

\begin{code}
  postulate
\end{code}

%<*plug-by-morphism-is-cool>
\begin{code}
    plug-by-morphism-⟦⟧ : ∀ {i o} (M : Vec-Morphism i o) (w : W i) →
      ⟦ plug-by-morphism M ⟧ w ≡ Vec-Morphism.op M w
\end{code}
%</plug-by-morphism-is-cool>



\begin{code}
module Pattern where

  postulate
\end{code}

%<*fan-ty>
\begin{code}
    fan : ∀ n → ℂ n n
\end{code}
%</fan-ty>

%<*fan-impl-ty>
\begin{code}
    fan-impl : ∀ n → ℂ n n
\end{code}
%</fan-impl-ty>

%<*fan-spec-ty>
\begin{code}
    fan-spec : ∀ n → W n → W n
\end{code}
%</fan-spec-ty>

%<*reveal-fan-ty>
\begin{code}
    reveal-fan : ∀ n → fan n ≋ fan-impl n
\end{code}
%</reveal-fan-ty>

%<*fan-to-spec-ty>
\begin{code}
    fan-to-spec : ∀ n → (w : W n) → ⟦ fan n ⟧ w ≡ fan-spec n w
\end{code}
%</fan-to-spec-ty>


\begin{code}
module HetSeq where
  postulate
\end{code}

%<*hetseq-ty>
\begin{code}
    _⟫[_]_ : ∀ {i m n o} (f : ℂ i m) (p : m ≡ n) (g : ℂ n o) → ℂ i o
\end{code}
%</hetseq-ty>

%<*hetseq-implicit-ty>
\begin{code}
    _⟫[]_ : ∀ {i m n o} (f : ℂ i m) {p : m ≡ n} (g : ℂ n o) → ℂ i o
\end{code}
%</hetseq-implicit-ty>

\begin{code}
  hetseq-example : ∀ n → ℂ (1 + n) (n + 1)
  hetseq-example n =
\end{code}

%<*hetseq-example-impl>
\begin{code}
    id⤨ (1 + n) ⟫[ +-comm 1 n ] id⤨ (n + 1)
\end{code}
%</hetseq-example-impl>

\begin{code}
  postulate
    ⟫[]-cong-proof : ∀ {i₁ m₁ n₁ o₁} {f₁ : ℂ i₁ m₁} (p₁ : m₁ ≡ n₁) {g₁ : ℂ n₁ o₁} →
                     ∀ {i₂ m₂ n₂ o₂} {f₂ : ℂ i₂ m₂} {g₂ : ℂ n₂ o₂} →
                     (ff : f₁ ≋ f₂) → (gg : g₁ ≋ g₂) →
                     m₂ ≡ n₂
    ⟫[-cong-proof : ∀ {i₁ m₁ o₁} {f₁ : ℂ i₁ m₁} {g₁ : ℂ m₁ o₁} →
                    ∀ {i₂ m₂ n₂ o₂} {f₂ : ℂ i₂ m₂} {g₂ : ℂ n₂ o₂} →
                    (ff : f₁ ≋ f₂) → (gg : g₁ ≋ g₂) →
                    m₂ ≡ n₂

\end{code}

%<*hetseq-cong>
\begin{code}
    _⟫[]-cong_ : ∀ {i₁ m₁ n₁ o₁} {f₁ : ℂ i₁ m₁} {p₁ : m₁ ≡ n₁} {g₁ : ℂ n₁ o₁} →
                 ∀ {i₂ m₂ n₂ o₂} {f₂ : ℂ i₂ m₂} {g₂ : ℂ n₂ o₂} →
                 (ff : f₁ ≋ f₂) → (gg : g₁ ≋ g₂) →
                 f₁ ⟫[ p₁ ] g₁ ≋ _⟫[]_ f₂ {⟫[]-cong-proof p₁ ff gg} g₂
\end{code}
%</hetseq-cong>

%<*hetseq-cong-tofrom>
\begin{code}
    _⟫[-cong_ : ∀ {i₁ m₁ o₁} {f₁ : ℂ i₁ m₁} {g₁ : ℂ m₁ o₁} →
                ∀ {i₂ m₂ n₂ o₂} {f₂ : ℂ i₂ m₂} {g₂ : ℂ n₂ o₂} →
                (f≈f : f₁ ≋ f₂) → (g≈g : g₁ ≋ g₂) →
                f₁ ⟫ g₁ ≋ _⟫[]_ f₂ {⟫[-cong-proof f≈f g≈g} g₂
    _⟫]-cong_ : ∀ {i₁ m₁ n₁ o₁} {f₁ : ℂ i₁ m₁} {p₁ : m₁ ≡ n₁} {g₁ : ℂ n₁ o₁} →
                ∀ {i₂ m₂ o₂} {f₂ : ℂ i₂ m₂} {g₂ : ℂ m₂ o₂} →
                (f≈f : f₁ ≋ f₂) → (g≈g : g₁ ≋ g₂) →
                f₁ ⟫[ p₁ ] g₁ ≋ f₂ ⟫ g₂
\end{code}
%</hetseq-cong-tofrom>

\begin{code}

open import PiWarePrefixes.Patterns.HetSeq {Gt = Gt}
open import PiWarePrefixes.Simulation.Properties.HetSeq {Gt = Gt}

module HetSeqExample where
\end{code}

%<*hetseq-proof-example>
\begin{code}
  hetseq-proof : ∀ {i m o} (f : ℂ i m) (g : ℂ m o) →
    (f ∥ id⤨ 0) ⟫ ((g ⟫ id⤨ o) ∥ id⤨ 0) ≋ f ⟫ g
  hetseq-proof f g = begin
    (f ∥ id⤨ 0) ⟫ ((g ⟫ id⤨ _) ∥ id⤨ 0)
      ≋⟨ (∥-right-identity f) ⟫[-cong ≋-refl ⟩
    f ⟫[] ((g ⟫ id⤨ _) ∥ id⤨ 0)
      ≋⟨ ≋-refl ⟫[]-cong (∥-right-identity _) ⟩
    f ⟫[] (g ⟫ id⤨ _)
      ≋⟨ ≋-refl ⟫]-cong (⟫-right-identity g) ⟩
    f ⟫ g
      ∎
\end{code}
%</hetseq-proof-example>

\begin{code}
open import PiWarePrefixes.MinGroups as MinGroups using (size; MinGroups)

module Stretching where
  open import PiWarePrefixes.Patterns.Stretch {Gt = Gt}
    using (module WithDirection; ⤙-direction)
  open WithDirection ⤙-direction using (in-⤨; out-⤨)
\end{code}

%<*stretch>
\begin{code}
  _⤙_ : ∀ {n} → ℂ n n → (as : Vec ℕ n) → ℂ (size 1 as) (size 1 as)
  c ⤙ as = in-⤨ as
    ⟫ c ∥ id⤨ (size 0 as)
    ⟫ out-⤨ as
\end{code}
%</stretch>

\begin{code}
  postulate
    in-out-id : ∀ {n} (as : Vec ℕ n) →
\end{code}

%<*in-out-id-ty>
\begin{code}
       ∀ w → ⟦ in-⤨ as ⟫ out-⤨ as ⟧ w ≡ w
\end{code}
%</in-out-id-ty>

%<*extract-map-ty>
\begin{code}
    extract-map : ∀ {A i n} {as : Vec ℕ n} →
      (Vec A n → Vec A n) → MinGroups A (suc i) as → MinGroups A (suc i) as
\end{code}
%</extract-map-ty>

\begin{code}
open import PiWarePrefixes.Patterns.Fan {plusℂ = plusℂ}
open import Relation.Binary.PropositionalEquality as PropEq using (cong; sym)

module Scans where
\end{code}

%<*scan-succ>
\begin{code}
  scan-succ : ∀ {n} → ℂ n n → ℂ (suc n) (suc n)
  scan-succ {n} f = id⤨ 1 ∥ f ⟫ fan (suc n)
\end{code}
%</scan-succ>

%<*scan>
\begin{code}
  scan : ∀ n → ℂ n n
  scan zero = id⤨ 0
  scan (suc n) = scan-succ (scan n)
\end{code}
%</scan>

%<*scan-combinators>
\begin{code}
  _▱_ : ∀ {m n o p}
    (f : ℂ m (suc o)) (g : ℂ (suc n) p) → ℂ (m + n) (o + p)
  _▱_ {n = n} {o} f g = f ∥ id⤨ n
    ⟫[ sym (+-suc o n) ] id⤨ o ∥ g

  _⌷_ : ∀ {m n}
    (f : ℂ (suc m) (suc m)) (g : ℂ n n) → ℂ (suc m + n) (m + suc n)
  _⌷_ {m = m} {n} f g = f ∥ g
    ⟫[ sym (+-suc m n) ] id⤨ m ∥ fan (suc n)
\end{code}
%</scan-combinators>

\begin{code}
  postulate
\end{code}

%<*scan-combinator-proofs>
\begin{code}
    ▱-combinator : ∀ m n → scan (suc m) ▱ scan (suc n) ≋ scan (m + suc n)
    ⌷-combinator : ∀ m n → scan (suc m) ⌷ scan n ≋ scan (suc m + n)
\end{code}
%</scan-combinator-proofs>

\begin{code}
open import PiWarePrefixes.Patterns.Scan {ℂ-monoid = ℂ-monoid}
open import PiWarePrefixes.Simulation.Properties.Scans {ℂ-monoid = ℂ-monoid}
open import PiWarePrefixes.Simulation.Properties.Scans.SuccProp {ℂ-monoid = ℂ-monoid} using (▱-scan-succ)
open import PiWarePrefixes.Simulation.Properties.Scans.Derived {ℂ-monoid = ℂ-monoid} using (⌷-combinator)

module SerialScan where
  id1=scan1 : id⤨ 1 ≋ scan 1
  id1=scan1 = ≋-sym scan1-id
\end{code}

%<*serial-scan>
\begin{code}
  serial-scan : ∀ n → ℂ n n
  serial-scan 0 = id⤨ 0
  serial-scan 1 = id⤨ 1
  serial-scan (suc (suc n)) = id⤨ (2 + n)
    ⟫[ cong suc (+-comm 1 n) ] serial-scan (suc n) ⌷ id⤨ 1
    ⟫[ +-comm n 2 ] id⤨ (2 + n)
\end{code}
%</serial-scan>

%<*serial-scan-is-scan>
\begin{code}
  serial-scan-is-scan : ∀ n → serial-scan n ≋ scan n
  serial-scan-is-scan 0 = ≋-refl
  serial-scan-is-scan 1 = id1=scan1
  serial-scan-is-scan (suc (suc n)) = begin
    serial-scan (2 + n)
      ≋⟨⟩ -- Expand definition of serial-scan
    id⤨ _ ⟫[] (serial-scan (suc n) ⌷ id⤨ 1) ⟫[] id⤨ _
      ≋⟨ ⟫[]-right-identity _ ⟩ -- f ⟫[] id⤨ ≋ f
    id⤨ _ ⟫[] (serial-scan (suc n) ⌷ id⤨ 1)
      ≋⟨ ⟫[]-left-identity _ ⟩ -- id⤨ ⟫[] f ≋ f
    serial-scan (suc n) ⌷ id⤨ 1
      ≋⟨ (serial-scan-is-scan (suc n)) -- Induction
         ⌷-cong id1=scan1
      ⟩
    scan (suc n) ⌷ scan 1
      ≋⟨ ⌷-combinator n 1 ⟩ -- ⌷ is a scan combinator
    scan (suc n + 1)
      ≋⟨ scan-cong (cong suc (+-comm n 1)) ⟩ -- suc n + 1 ≡ 2 + n
    scan (2 + n)
      ∎
\end{code}
%</serial-scan-is-scan>

