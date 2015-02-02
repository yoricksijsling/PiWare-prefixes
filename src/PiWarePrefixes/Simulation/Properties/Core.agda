open import PiWare.Atom using (Atomic)
open import PiWare.Gates using (Gates)

module PiWarePrefixes.Simulation.Properties.Core {At : Atomic} (Gt : Gates At) where

open import Data.Fin using (Fin; zero; suc)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Vec using (Vec; tabulate; lookup; splitAt)
                     renaming (sum to sumᵥ)
open import Data.Vec.Properties using (tabulate-allFin; lookup∘tabulate; map-lookup-allFin)
open import Function using (id; _$_; _∘_; flip)
open import Relation.Binary.PropositionalEquality as PropEq using (refl; cong; sym; _≡_)

open import PiWarePrefixes.Circuit.Context.Core Gt
open import PiWare.Circuit.Core Gt using (ℂ'; Comb; Plug; _⟫'_; _|'_; _Named_)
open import PiWarePrefixes.Patterns.Core Gt using (_⤚'_; ⤚-perm)
open import PiWarePrefixes.Permutation as P using (Perm; _§_; _*)
open import PiWare.Plugs.Core Gt using (pid')
open import PiWare.Simulation.Core Gt using (⟦_⟧')
open import PiWarePrefixes.Simulation.Equality.Core Gt as SimEq
open import PiWare.Synthesizable At
open import PiWarePrefixes.Utils


----------------------------------------------------
-- Named

named-identity : ∀ {i o s} (f : ℂ' i o) → f Named s ≡⟦⟧ f
named-identity f = from-≈⟦⟧ (λ w → refl)


----------------------------------------------------
-- Plugs

pid-id : ∀ {i} (w : W i) → ⟦ pid' ⟧' w ≡ w
pid-id w rewrite tabulate-allFin (λ fin → lookup fin w) = map-lookup-allFin w

private
  tabulate-extensionality : ∀ {n} {r : Set} {f g : Fin n → r} →
    (∀ x → f x ≡ g x) → tabulate f ≡ tabulate g
  tabulate-extensionality {zero} p = refl
  tabulate-extensionality {suc n} p rewrite p zero | (tabulate-extensionality (p ∘ suc)) = refl

plug-∘ : ∀ {i j o} (f : Fin j → Fin i) (g : Fin o → Fin j) → Plug f ⟫' Plug g ≡⟦⟧ Plug (f ∘ g)
plug-∘ f g = from-≈⟦⟧ $ λ w →
  tabulate-extensionality (λ fin → lookup∘tabulate (λ fin₁ → lookup (f fin₁) w) (g fin))

plug-extensionality : ∀ {i o} {f : Fin o → Fin i} {g : Fin o → Fin i} → (∀ x → f x ≡ g x) → Plug f ≡⟦⟧ Plug g
plug-extensionality p = from-≈⟦⟧ $ λ w →
  tabulate-extensionality (cong (flip lookup w) ∘ p)

pid-plugs : ∀ {i o} {f : Fin o → Fin i} {g : Fin i → Fin o} → (∀ x → f (g x) ≡ x) → Plug f ⟫' Plug g ≡⟦⟧ pid' {i}
pid-plugs {f = f} {g} p = ≡⟦⟧-trans (plug-∘ f g) (≡⟦⟧-trans (plug-extensionality p) (≡⟦⟧-sym (named-identity _)))


----------------------------------------------------
-- Sequence

-- f ⟫ id ≡ f
seq-right-identity : ∀ {i o} (f : ℂ' i o) → f ⟫' pid' ≡⟦⟧ f
seq-right-identity f = from-≈⟦⟧ $ λ w → pid-id (⟦ f ⟧' w)

-- id ⟫ f ≡ f
seq-left-identity : ∀ {i o} (f : ℂ' i o) → pid' ⟫' f ≡⟦⟧ f
seq-left-identity f = from-≈⟦⟧ $ λ w → cong ⟦ f ⟧' (pid-id w)

-- (f ⟫ g) ⟫ h ≡ f ⟫ (g ⟫ h)
seq-assoc : ∀ {i m n o} (f : ℂ' i m) (g : ℂ' m n) (h : ℂ' n o) → f ⟫' g ⟫' h ≡⟦⟧ f ⟫' (g ⟫' h)
seq-assoc f g h = from-≈⟦⟧ $ λ w → refl


----------------------------------------------------
-- Parallel

-- id{0} || f ≡ f
par-left-identity : ∀ {i o} (f : ℂ' i o) → pid' {0} |' f ≡⟦⟧ f
par-left-identity f = from-≈⟦⟧ (λ w → refl)

-- f || id{0} ≡ f
-- Should i define ≈⟦⟧ semi-heterogeneously to be abe to write this?
-- par-right-identity : ∀ {i o} (f : ℂ' i o) → f |' pid' {0} ≡⟦⟧ f
-- par-right-identity = {!!}

-- (f || g) || h ≡ f || (g || h)
-- par-assoc : ∀ {i₁ o₁ i₂ o₂ i₃ o₃} (f : ℂ' i₁ o₁) (g : ℂ' i₂ o₂) (h : ℂ' i₃ o₃) → (f |' g) |' h ≡⟦⟧ f |' (g |' h)
-- par-assoc = ?

-- id{m} || id{n} = id{m+n}
par-pid : ∀ {n m} → pid' {n} |' pid' {m} ≡⟦⟧ pid' {n + m}
par-pid {n} {m} = from-≈⟦⟧ imp
  where
  imp : pid' {n} |' pid' {m} ≈⟦⟧ pid' {n + m}
  imp w with splitAt n w
  ... | vn , vm , w≡vn++vm with pid-id vn | pid-id vm | pid-id w
  ... | vn' | vm' | w' rewrite vn' | vm' | w' = sym w≡vn++vm

-- (f₁ || f₂) ⟫ (g₁ || g₂) ≡ (f₁ ⟫ g₁) || (f₂ ⟫ g₂)
seq-par-distrib : ∀ {i₁ m₁ o₁ i₂ m₂ o₂} (f₁ : ℂ' i₁ m₁) (g₁ : ℂ' m₁ o₁) (f₂ : ℂ' i₂ m₂) (g₂ : ℂ' m₂ o₂) → (f₁ |' f₂) ⟫' (g₁ |' g₂) ≡⟦⟧ (f₁ ⟫' g₁) |' (f₂ ⟫' g₂)
seq-par-distrib {i₁} {m₁} f₁ g₁ f₂ g₂ = from-≈⟦⟧ imp
  where
  imp : (f₁ |' f₂) ⟫' (g₁ |' g₂) ≈⟦⟧ (f₁ ⟫' g₁) |' (f₂ ⟫' g₂)
  imp w rewrite splitAt-++ m₁ (⟦ f₁ ⟧' (proj₁ (splitAt i₁ w))) (⟦ f₂ ⟧' (proj₁ (proj₂ (splitAt i₁ w)))) = refl


----------------------------------------------------
-- Stretching

-- id{#x} ⤙ x ≡ id{Σx}
-- (todo)

⤚-preserves-id : ∀ {n} (xs : Vec ℕ n) → xs ⤚' pid' {n} ≡⟦⟧ pid' {sumᵥ xs + n}
⤚-preserves-id {n} xs = begin
  Plug to ⟫' pid' {sumᵥ xs} |' pid' {n} ⟫' Plug from
    ≡⟦⟧⟨ ≡⟦⟧-cong (Plug to ⟫'● ● ●⟫' Plug from)
                par-pid ⟩
  Plug to ⟫' pid' {sumᵥ xs + n} ⟫' Plug from
    ≡⟦⟧⟨ ≡⟦⟧-cong (● ●⟫' Plug from)
                (seq-right-identity (Plug to)) ⟩
  Plug to ⟫' Plug from
    ≡⟦⟧⟨ pid-plugs to-from-id ⟩
  pid'
    ∎
  where
  open SimEq.≡⟦⟧-Reasoning
  to : Fin (sumᵥ xs + n) → Fin (sumᵥ xs + n)
  to = _§_ (⤚-perm xs)
  from : Fin (sumᵥ xs + n) → Fin (sumᵥ xs + n)
  from = _§_ (⤚-perm xs *)
  to-from-id : ∀ x → to (from x) ≡ x
  to-from-id = P.§-right-inverse (⤚-perm xs)


-- (f ⟫ g) ⤙ x ≡ f ⤙ x ⟫ g ⤙ x
-- (todo)

-- x ⤚ (f ⟫ g) ≡ x ⤚ f ⟫ x ⤚ g
⤚-⟫-distrib' : ∀ {n} (xs : Vec ℕ n) (f g : ℂ' n n) → (xs ⤚' f) ⟫' (xs ⤚' g) ≡⟦⟧ xs ⤚' (f ⟫' g)
⤚-⟫-distrib' {n} xs f g = begin
  Plug to ⟫' pid' {sumᵥ xs} |' f ⟫' Plug from ⟫'
  (Plug to ⟫' pid' {sumᵥ xs} |' g ⟫' Plug from)
    ≡⟦⟧⟨ from-≈⟦⟧ (λ w → refl) ⟩
  Plug to ⟫'
  (pid' {sumᵥ xs} |' f ⟫' (Plug from ⟫' Plug to) ⟫' pid' {sumᵥ xs} |' g) ⟫'
  Plug from
    ≡⟦⟧⟨ ≡⟦⟧-cong (Plug to ⟫'● ● ●⟫' Plug from) (begin
        pid' {sumᵥ xs} |' f ⟫' (Plug from ⟫' Plug to) ⟫' pid' {sumᵥ xs} |' g
          ≡⟦⟧⟨ ≡⟦⟧-cong (pid' {sumᵥ xs} |' f ⟫'● ● ●⟫' pid' {sumᵥ xs} |' g) (pid-plugs from-to-id) ⟩
        pid' {sumᵥ xs} |' f ⟫' pid' ⟫' pid' {sumᵥ xs} |' g
          ≡⟦⟧⟨ ≡⟦⟧-cong (● ●⟫' pid' {sumᵥ xs} |' g) (seq-right-identity _) ⟩
        pid' {sumᵥ xs} |' f ⟫' pid' {sumᵥ xs} |' g
          ≡⟦⟧⟨ seq-par-distrib _ _ _ _ ⟩
        (pid' {sumᵥ xs} ⟫' pid' {sumᵥ xs}) |' (f ⟫' g)
          ≡⟦⟧⟨ ≡⟦⟧-cong (● ●|' (f ⟫' g)) (seq-right-identity _) ⟩
        pid' {sumᵥ xs} |' (f ⟫' g) ∎) ⟩
  Plug to ⟫' pid' {sumᵥ xs} |' (f ⟫' g) ⟫' Plug from
    ∎
  where
  open SimEq.≡⟦⟧-Reasoning
  to : Fin (sumᵥ xs + n) → Fin (sumᵥ xs + n)
  to = _§_ (⤚-perm xs)
  from : Fin (sumᵥ xs + n) → Fin (sumᵥ xs + n)
  from = _§_ (⤚-perm xs *)
  from-to-id : ∀ x → from (to x) ≡ x
  from-to-id = P.§-left-inverse (⤚-perm xs)
