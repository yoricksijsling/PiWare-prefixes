open import PiWare.Atom using (Atomic)
open import PiWare.Gates using (Gates)

module PiWarePrefixes.Simulation.Properties.Core {At : Atomic} (Gt : Gates At) where

open import Data.Fin using (Fin; zero; suc)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties.Simple using (+-right-identity; +-assoc)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Vec using (Vec; tabulate; lookup; splitAt; _++_; []; _∷_)
                     renaming (sum to sumᵥ)
import Data.Vec.Equality
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

private
  module VE = Data.Vec.Equality.PropositionalEquality
  module VecPropEq {a} {A : Set a} = Data.Vec.Properties.UsingVectorEquality (PropEq.setoid A)
  open VecPropEq using (xs++[]=xs)

----------------------------------------------------
-- Named

named-identity : ∀ {i o s} (f : ℂ' i o) → f Named s ≡⟦⟧ f
named-identity f = Mk≡⟦⟧ (λ w → refl)

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
plug-∘ f g = Mk≡⟦⟧ $ λ w →
  tabulate-extensionality (λ fin → lookup∘tabulate (λ fin₁ → lookup (f fin₁) w) (g fin))

plug-extensionality : ∀ {i o} {f : Fin o → Fin i} {g : Fin o → Fin i} → (∀ x → f x ≡ g x) → Plug f ≡⟦⟧ Plug g
plug-extensionality p = Mk≡⟦⟧ $ λ w →
  tabulate-extensionality (cong (flip lookup w) ∘ p)

pid-plugs : ∀ {i o} {f : Fin o → Fin i} {g : Fin i → Fin o} → (∀ x → f (g x) ≡ x) → Plug f ⟫' Plug g ≡⟦⟧ pid' {i}
pid-plugs {f = f} {g} p = ≈⟦⟧-trans (plug-∘ f g) (≈⟦⟧-trans (plug-extensionality p) (≈⟦⟧-sym (named-identity _)))


----------------------------------------------------
-- Sequence

-- f ⟫ id ≡ f
seq-right-identity : ∀ {i o} (f : ℂ' i o) → f ⟫' pid' ≡⟦⟧ f
seq-right-identity f = Mk≡⟦⟧ $ λ w → pid-id (⟦ f ⟧' w)

-- id ⟫ f ≡ f
seq-left-identity : ∀ {i o} (f : ℂ' i o) → pid' ⟫' f ≡⟦⟧ f
seq-left-identity f = Mk≡⟦⟧ $ λ w → cong ⟦ f ⟧' (pid-id w)

-- (f ⟫ g) ⟫ h ≡ f ⟫ (g ⟫ h)
seq-assoc : ∀ {i m n o} (f : ℂ' i m) (g : ℂ' m n) (h : ℂ' n o) → f ⟫' g ⟫' h ≡⟦⟧ f ⟫' (g ⟫' h)
seq-assoc f g h = Mk≡⟦⟧ $ λ w → refl


----------------------------------------------------
-- Parallel

-- id{0} || f ≡ f
par-left-identity : ∀ {i o} (f : ℂ' i o) → pid' {0} |' f ≡⟦⟧ f
par-left-identity f = Mk≡⟦⟧ (λ w → refl)

-- f || id{0} ≡ f
par-right-identity : {i o : ℕ} (f : ℂ' i o) → ≈⟦⟧ (+-right-identity i) (+-right-identity o) (f |' pid' {0}) f
par-right-identity f = ≈e-to-≈⟦⟧ par-right-identity-≈e
  where
  lem₁ : ∀ {i} {xs : W (i + 0)} {ys : W i} (xs≈ys : xs VE.≈ ys) → (proj₁ (splitAt i xs)) VE.≈ ys
  lem₁ {i} {xs} xs≈ys with splitAt i xs
  lem₁ xs≈ys | xs₁ , [] , refl = VE.trans (VE.sym (xs++[]=xs xs₁)) xs≈ys

  par-right-identity-≈e : f |' pid' {0} ≈e f
  par-right-identity-≈e w≈w with VE.to-≡ (lem₁ w≈w)
  par-right-identity-≈e {w₂ = w₂} w≈w | a rewrite a = xs++[]=xs (⟦ f ⟧' w₂)

-- (f || g) || h ≡ f || (g || h)
par-assoc : ∀ {i₁ o₁ i₂ o₂ i₃ o₃} (f : ℂ' i₁ o₁) (g : ℂ' i₂ o₂) (h : ℂ' i₃ o₃) →
            ≈⟦⟧ (+-assoc i₁ i₂ i₃) (+-assoc o₁ o₂ o₃) ((f |' g) |' h) (f |' (g |' h))
par-assoc {i₁} {i₂ = i₂} {i₃ = i₃} f g h = ≈e-to-≈⟦⟧ par-assoc-≈e
  where
  takeEq : ∀ {n m} (xs₁ : W n) {xs₂ : W m} (ys₁ : W n) {ys₂ : W m} → xs₁ ++ xs₂ VE.≈ ys₁ ++ ys₂ → xs₁ VE.≈ ys₁
  takeEq [] [] xs≈ys = VE.[]-cong
  takeEq (x ∷ xs₁) (x₁ ∷ ys₁) (x¹≈x² VE.∷-cong xs≈ys) = x¹≈x² VE.∷-cong takeEq xs₁ ys₁ xs≈ys

  dropEq : ∀ {n m} (xs₁ : W n) (xs₂ : W m) (ys₁ : W n) (ys₂ : W m) → xs₁ ++ xs₂ VE.≈ ys₁ ++ ys₂ → xs₂ VE.≈ ys₂
  dropEq [] xs₂ [] ys₂ xs≈ys = xs≈ys
  dropEq (x ∷ xs₁) xs₂ (x₁ ∷ ys₁) ys₂ (x¹≈x² VE.∷-cong xs≈ys) = dropEq xs₁ xs₂ ys₁ ys₂ xs≈ys

  ++-assoc : ∀ {n m o} (xs : W n) (ys : W m) (zs : W o) → (xs ++ ys) ++ zs VE.≈ xs ++ ys ++ zs
  ++-assoc [] ys zs = VE.from-≡ refl
  ++-assoc (x ∷ xs) ys zs = refl VE.∷-cong ++-assoc xs ys zs

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

  par-assoc-≈e : (f |' g) |' h ≈e f |' (g |' h)
  par-assoc-≈e {w₁} {w₂} w≈w with VE.to-≡ (lem₁ {i₁} w₁ w₂ w≈w) | VE.to-≡ (lem₂ {i₁} w₁ w₂ w≈w) | VE.to-≡ (lem₃ {i₁} w₁ w₂ w≈w)
  ... | l₁ | l₂ | l₃ rewrite l₁ | l₂ | sym l₃ = ++-assoc (⟦ f ⟧' (proj₁ (splitAt i₁ w₂)))
                                                         (⟦ g ⟧' (proj₁ (splitAt i₂ (proj₁ (proj₂ (splitAt i₁ w₂))))))
                                                         (⟦ h ⟧' (proj₁ (proj₂ (splitAt (i₁ + i₂) w₁))))

-- id{m} || id{n} = id{m+n}
par-pid : ∀ {n m} → pid' {n} |' pid' {m} ≡⟦⟧ pid' {n + m}
par-pid {n} {m} = Mk≡⟦⟧ imp
  where
  imp : pid' {n} |' pid' {m} ≡e pid' {n + m}
  imp w with splitAt n w
  ... | vn , vm , w≡vn++vm with pid-id vn | pid-id vm | pid-id w
  ... | vn' | vm' | w' rewrite vn' | vm' | w' = sym w≡vn++vm

-- (f₁ || f₂) ⟫ (g₁ || g₂) ≡ (f₁ ⟫ g₁) || (f₂ ⟫ g₂)
seq-par-distrib : ∀ {i₁ m₁ o₁ i₂ m₂ o₂} (f₁ : ℂ' i₁ m₁) (g₁ : ℂ' m₁ o₁) (f₂ : ℂ' i₂ m₂) (g₂ : ℂ' m₂ o₂) → (f₁ |' f₂) ⟫' (g₁ |' g₂) ≡⟦⟧ (f₁ ⟫' g₁) |' (f₂ ⟫' g₂)
seq-par-distrib {i₁} {m₁} f₁ g₁ f₂ g₂ = Mk≡⟦⟧ imp
  where
  imp : (f₁ |' f₂) ⟫' (g₁ |' g₂) ≡e (f₁ ⟫' g₁) |' (f₂ ⟫' g₂)
  imp w rewrite splitAt-++ m₁ (⟦ f₁ ⟧' (proj₁ (splitAt i₁ w))) (⟦ f₂ ⟧' (proj₁ (proj₂ (splitAt i₁ w)))) = refl


----------------------------------------------------
-- Stretching

-- id{#x} ⤙ x ≡ id{Σx}
-- (todo)

⤚-preserves-id : ∀ {n} (xs : Vec ℕ n) → xs ⤚' pid' {n} ≡⟦⟧ pid' {sumᵥ xs + n}
⤚-preserves-id {n} xs = begin
  Plug to ⟫' pid' {sumᵥ xs} |' pid' {n} ⟫' Plug from
    ≡⟦⟧⟨ ≈⟦⟧-cong (Plug to ⟫'● ● ●⟫' Plug from)
                par-pid ⟩
  Plug to ⟫' pid' {sumᵥ xs + n} ⟫' Plug from
    ≡⟦⟧⟨ ≈⟦⟧-cong (● ●⟫' Plug from)
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
    ≡⟦⟧⟨ Mk≡⟦⟧ (λ w → refl) ⟩
  Plug to ⟫'
  (pid' {sumᵥ xs} |' f ⟫' (Plug from ⟫' Plug to) ⟫' pid' {sumᵥ xs} |' g) ⟫'
  Plug from
    ≡⟦⟧⟨ ≈⟦⟧-cong (Plug to ⟫'● ● ●⟫' Plug from) (begin
        pid' {sumᵥ xs} |' f ⟫' (Plug from ⟫' Plug to) ⟫' pid' {sumᵥ xs} |' g
          ≡⟦⟧⟨ ≈⟦⟧-cong (pid' {sumᵥ xs} |' f ⟫'● ● ●⟫' pid' {sumᵥ xs} |' g) (pid-plugs from-to-id) ⟩
        pid' {sumᵥ xs} |' f ⟫' pid' ⟫' pid' {sumᵥ xs} |' g
          ≡⟦⟧⟨ ≈⟦⟧-cong (● ●⟫' pid' {sumᵥ xs} |' g) (seq-right-identity _) ⟩
        pid' {sumᵥ xs} |' f ⟫' pid' {sumᵥ xs} |' g
          ≡⟦⟧⟨ seq-par-distrib _ _ _ _ ⟩
        (pid' {sumᵥ xs} ⟫' pid' {sumᵥ xs}) |' (f ⟫' g)
          ≡⟦⟧⟨ ≈⟦⟧-cong (● ●|' (f ⟫' g)) (seq-right-identity _) ⟩
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
