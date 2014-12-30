module PiWarePrefixes.Permutation where

-- Roughly based on https://github.com/ruisb/PiGraph/blob/master/Permutation.agda

open import Function
open import Data.Fin
open import Data.Fin.Properties as FinProps
open import Data.Nat as Nat using (ℕ; zero; suc)
open import Relation.Nullary.Core as NulCore using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality
import Algebra.FunctionProperties

{--
Perm is an implementation of Lehmer codes

The permutation #k ◀ σ is the permutation where #k is the first element
(the image of #0) and σ determines the order of the following.

As an example, #k ◀ id is
  permutation:   0   1  ...   i   ...   k    (k+1)  ...  j    ...  N
                 ↓   ↓        ↓         ↓      ↓         ↓         ↓
  image:         k   0       i-1       k-1   (k+1)       j         N
--}

data Perm : ℕ → Set where
  ε    : Perm 0
  _◀_ : {n : ℕ} → (v : Fin (suc n)) → (σ : Perm n) → Perm (suc n)

infixr 5 _◀_

private

  -- if m ≥ k then 'suc m' else 'm'
  bubble : {n : ℕ} → Fin n → Fin (suc n) → Fin (suc n)
  bubble m zero = suc m
  bubble zero (suc k) = zero
  bubble (suc m) (suc k) = suc (bubble m k)
  -- bubble m k with (toℕ k) Nat.≤? (toℕ m)
  -- bubble m k | yes p = suc m
  -- bubble m k | no ¬p = inject₁ m

down :  {n : ℕ} → Fin (suc (suc n)) -> Fin (suc n)
down zero    = zero
down (suc x) = x 

-- Remove an element from the image. ONLY WORKS FOR ZEROES
forget_at_ : {n : ℕ} → Perm (suc n) → Fin (suc n) → Perm n
forget_at_         (v ◀ σ) zero = σ
forget_at_ {zero}  (v ◀ ε) (suc ())
forget_at_ {suc m} (v ◀ σ) (suc k) = down v ◀ forget_at_ {m} σ k

-- Applying a permutation
_§_ : ∀ {n} → Perm n → Fin n → Fin n
(k ◀ σ) § zero    = k
(k ◀ σ) § (suc n) = bubble (σ § n) k

-- _§'_ : ∀ {n} → Perm n → Fin n → Fin n
-- (k ◀ σ) §' zero = k
-- -- (k ◀ σ) §' (suc n) = inject₁ (forget zero ◀ σ at # 0 §' n)
-- (zero ◀ σ) §' suc n = suc (σ § n)
-- (suc k ◀ σ) §' suc n = {!k!}

-- Composition
_∙_ :  ∀ {n} → Perm n → Perm n → Perm n
ε ∙ ε             = ε
σ₁ ∙ (k ◀ σ₂)  = (σ₁ § k) ◀ (forget σ₁ at k ∙ σ₂)

-- Identity
i : ∀ {n} → Perm n
i {zero}  = ε
i {suc m} = zero ◀ i

-- A perm always contains at least one zero
firstzero : ∀ {n} → Perm (suc n) → Fin (suc n)
firstzero {_} (zero ◀ σ) = zero
firstzero {zero} (suc () ◀ σ)
firstzero {suc n} (suc v ◀ σ) = suc (firstzero σ)

-- Make the inverse permutation
_* : ∀ {n} → Perm n → Perm n
_* {zero} ε = ε
_* {suc n} σ = firstzero σ ◀ ((forget σ at firstzero σ) *)

-----------------------------------------
-- EXAMPLES

example : Perm 6
example = # 3 ◀ # 0 ◀ # 2 ◀ # 0 ◀ # 1 ◀ # 0 ◀ ε

example-§-1 : example § (# 0) ≡ # 3
example-§-1 = refl
example-§-2 : example § (# 1) ≡ # 0
example-§-2 = refl
example-§-3 : example § (# 2) ≡ # 4
example-§-3 = refl
example-§-4 : example § (# 3) ≡ # 1
example-§-4 = refl
example-§-5 : example § (# 4) ≡ # 5
example-§-5 = refl
example-§-6 : example § (# 5) ≡ # 2
example-§-6 = refl

example-* : example * ≡ # 1 ◀ # 2 ◀ # 3 ◀ # 0 ◀ # 0 ◀ # 0 ◀ ε
example-* = refl

example-*-* : (example *) * ≡ example
example-*-* = refl


-----------------------------------------
-- PROPERTIES

-- Open FP in such a way that equality on Perm n is used if it is provided with
-- a parameter {n}.
open module FP {n : ℕ} = Algebra.FunctionProperties (_≡_ {A = Perm n})

i-* : ∀ {n} → (i {n}) * ≡ i {n}
i-* {zero } = refl
i-* {suc n} = cong (_◀_ zero) i-*

i-§ : ∀ {n} (k : Fin n) → i § k ≡ k
i-§ zero = refl
i-§ (suc k) = cong suc (i-§ k)

-- lem1 : ∀ {n} (σ : Perm (suc n)) (m : Fin n) (k : Fin (suc n))
--      → bubble ((forget σ at k) § m) (σ § k) ≡ σ § bubble m k --- FALSE. Counterexample σ=110, m=1, k=1
-- lem1 {n} σ m k = {!!}

∙-§ : ∀ {n} (σ₁ σ₂ : Perm n) (k : Fin n) → (σ₁ ∙ σ₂) § k ≡ σ₁ § (σ₂ § k)
∙-§ {zero} ε ε ()
∙-§ {suc n} (v₁ ◀ σ₁) (v₂ ◀ σ₂) zero = refl
-- ∙-§ {suc n} (v₁ ◀ σ₁) (v₂ ◀ σ₂) (suc k) = {!!}
∙-§ {suc n} (v₁ ◀ σ₁) (v₂ ◀ σ₂) (suc k) with ∙-§ (forget v₁ ◀ σ₁ at v₂) σ₂ k
... | rec = {!!}
--∙-§ {suc n} (v₁ ◀ σ₁) (v₂ ◀ σ₂) (suc k) rewrite ∙-§ (forget v₁ ◀ σ₁ at v₂) σ₂ k = lem1 (v₁ ◀ σ₁) (σ₂ § k) v₂

forget-i≡i : ∀ {n} (k : Fin (suc n)) → forget i at k ≡ i
forget-i≡i {_} zero = refl
forget-i≡i {zero} (suc ())
forget-i≡i {suc n} (suc k) rewrite forget-i≡i k = refl

∙-left-identity : ∀ {n} → LeftIdentity {n} i _∙_
∙-left-identity ε = refl
∙-left-identity (v ◀ σ) rewrite i-§ v
                              | forget-i≡i v
                              | ∙-left-identity σ = refl

∙-right-identity : ∀ {n} → RightIdentity {n} i _∙_
∙-right-identity ε = refl
∙-right-identity (v ◀ σ) rewrite ∙-right-identity σ = refl

§-firstzero : ∀ {n} (σ : Perm (suc n)) → σ § firstzero σ ≡ zero
§-firstzero {zero} (zero ◀ σ) = refl
§-firstzero {zero} (suc () ◀ σ)
§-firstzero {suc n} (zero ◀ σ) = refl
§-firstzero {suc n} (suc v ◀ σ) rewrite §-firstzero σ = refl

*-∙-right-inverse : ∀ {n} → RightInverse {n} i _* _∙_
*-∙-right-inverse ε = refl
*-∙-right-inverse (v ◀ σ) rewrite §-firstzero (v ◀ σ)
                                | *-∙-right-inverse (forget v ◀ σ at firstzero (v ◀ σ)) = refl

firstzero-*-identity : ∀ {n} (k : Fin (suc n)) (σ : Perm n) → firstzero ((k ◀ σ) *) ≡ k
firstzero-*-identity zero σ = refl
firstzero-*-identity (suc ()) ε
firstzero-*-identity (suc k) (v ◀ σ) rewrite firstzero-*-identity k (forget v ◀ σ at firstzero (v ◀ σ)) = refl

forget-*-identity : ∀ {n} (k : Fin (suc n)) (σ : Perm n) → (forget (k ◀ σ) * at k) ≡ σ *
forget-*-identity zero σ = refl
forget-*-identity (suc ()) ε
forget-*-identity (suc k) (v ◀ σ) rewrite forget-*-identity k (forget v ◀ σ at firstzero (v ◀ σ)) = refl

*-involutive : ∀ {n} → Involutive {n} _*
*-involutive ε = refl
*-involutive (v ◀ σ) rewrite firstzero-*-identity v σ
                           | forget-*-identity v σ
                           | *-involutive σ = refl

*-∙-left-inverse : ∀ {n} → LeftInverse {n} i _* _∙_
*-∙-left-inverse σ rewrite sym (*-∙-right-inverse (σ *))
                         | *-involutive σ = refl
