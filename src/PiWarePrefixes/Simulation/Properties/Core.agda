open import PiWare.Atom using (Atomic)
open import PiWare.Gates using (Gates)

module PiWarePrefixes.Simulation.Properties.Core {At : Atomic} (Gt : Gates At) where

open import Data.Fin using (Fin; zero; suc)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Vec using (tabulate; lookup; splitAt)
open import Data.Vec.Properties using (tabulate-allFin; lookup∘tabulate; map-lookup-allFin)
open import Function using (_∘_; flip)
open import Relation.Binary.PropositionalEquality as PropEq using (refl; cong; sym; _≡_)

open import PiWare.Circuit.Core Gt using (ℂ'; Comb; Plug; _⟫'_; _|'_)
open import PiWare.Plugs.Core Gt using (pid')
-- open import PiWare.Plugs.Core using (pid')
open import PiWare.Simulation.Core Gt using (⟦_⟧')
open import PiWarePrefixes.Simulation.Equality.Core Gt using (_≡e_)
open import PiWare.Synthesizable At
open import PiWarePrefixes.Utils


-- Properties of plugs

pid-id : ∀ {i} (w : W i) → ⟦ pid' ⟧' w ≡ w
pid-id w rewrite tabulate-allFin (λ fin → lookup fin w) = map-lookup-allFin w

tabulate-extensionality : ∀ {n} {r : Set} {f g : Fin n → r} →
  (∀ x → f x ≡ g x) → tabulate f ≡ tabulate g
tabulate-extensionality {zero} p = refl
tabulate-extensionality {suc n} p rewrite p zero | (tabulate-extensionality (p ∘ suc)) = refl

plug-∘ : ∀ {i j o} (f : Fin j → Fin i) (g : Fin o → Fin j) → Plug f ⟫' Plug g ≡e Plug (f ∘ g)
plug-∘ f g w = tabulate-extensionality (λ fin → lookup∘tabulate (λ fin₁ → lookup (f fin₁) w) (g fin))

plug-extensionality : ∀ {i o} {f : Fin o → Fin i} {g : Fin o → Fin i} → (∀ x → f x ≡ g x) → Plug f ≡e Plug g
plug-extensionality p w = tabulate-extensionality (cong (flip lookup w) ∘ p)


-- Sequence

-- f ⟫ id ≡ f
seq-right-identity : ∀ {i o} (f : ℂ' i o) → f ⟫' pid' ≡e f
seq-right-identity f w = pid-id (⟦ f ⟧' w)

-- id ⟫ f ≡ f
seq-left-identity : ∀ {i o} (f : ℂ' i o) → pid' ⟫' f ≡e f
seq-left-identity f w = cong ⟦ f ⟧' (pid-id w)

-- (f ⟫ g) ⟫ h ≡ f ⟫ (g ⟫ h)
seq-assoc : ∀ {i m n o} (f : ℂ' i m) (g : ℂ' m n) (h : ℂ' n o) → f ⟫' g ⟫' h ≡e f ⟫' (g ⟫' h)
seq-assoc f g h w = refl


-- Parallel

-- id{0} || f ≡ f
par-left-identity : ∀ {i o} (f : ℂ' i o) → pid' {0} |' f ≡e f
par-left-identity f w = refl

-- f || id{0} ≡ f
-- Should i define ≡e semi-heterogeneously to be abe to write this?
-- par-right-identity : ∀ {i o} (f : ℂ' i o) → f |' pid' {0} ≡e f
-- par-right-identity = {!!}

-- (f || g) || h ≡ f || (g || h)
-- par-assoc : ∀ {i₁ o₁ i₂ o₂ i₃ o₃} (f : ℂ' i₁ o₁) (g : ℂ' i₂ o₂) (h : ℂ' i₃ o₃) → (f |' g) |' h ≡e f |' (g |' h)
-- par-assoc = ?

-- id{m} || id{n} = id{m+n}
par-pid : ∀ {n m} → pid' {n} |' pid' {m} ≡e pid' {n + m}
par-pid {n} {m} w with splitAt n w
par-pid {n} {m} w | vn , vm , w≡vn++vm with pid-id vn | pid-id vm | pid-id w
... | vn' | vm' | w' rewrite vn' | vm' | w' = sym w≡vn++vm
-- par-pid {n} {m} w | vn , vm , w≡vn++vm rewrite pid-id vn | pid-id vm | pid-id w = sym w≡vn++vm

-- (f₁ || f₂) ⟫ (g₁ || g₂) = (f₁ ⟫ g₁) || (f₂ ⟫ g₂)
seq-par-distributivity : ∀ {i₁ m₁ o₁ i₂ m₂ o₂} (f₁ : ℂ' i₁ m₁) (g₁ : ℂ' m₁ o₁) (f₂ : ℂ' i₂ m₂) (g₂ : ℂ' m₂ o₂) → (f₁ |' f₂) ⟫' (g₁ |' g₂) ≡e (f₁ ⟫' g₁) |' (f₂ ⟫' g₂)
seq-par-distributivity {i₁} {m₁} f₁ g₁ f₂ g₂ w rewrite splitAt-++ m₁ (⟦ f₁ ⟧' (proj₁ (splitAt i₁ w))) (⟦ f₂ ⟧' (proj₁ (proj₂ (splitAt i₁ w)))) = refl
