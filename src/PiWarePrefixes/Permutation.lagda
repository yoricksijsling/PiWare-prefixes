\begin{code}
module PiWarePrefixes.Permutation where

-- Roughly based on https://github.com/ruisb/PiGraph/blob/master/Permutation.agda

open import Function
open import Data.Fin
open import Data.Nat as Nat using (ℕ; zero; suc)
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

data Perm : ℕ → Set where
  ε    : Perm 0
  _◀_ : {n : ℕ} → (v : Fin (suc n)) → (σ : Perm n) → Perm (suc n)

infixr 5 _◀_

private

  -- if r ≥ v then 'suc r' else 'r'
  bubble-r : {n : ℕ} → Fin n → Fin (suc n) → Fin (suc n)
  bubble-r r       zero    = suc r
  bubble-r zero    (suc v) = zero
  bubble-r (suc r) (suc v) = suc (bubble-r r v)

  -- if r ≥ v then 'v' else 'pred v'
  bubble-v : {n : ℕ} → Fin (suc n) → Fin (suc (suc n)) → Fin (suc n)
  bubble-v         r        zero    = zero
  bubble-v         zero     (suc v) = v
  bubble-v {zero}  (suc ()) (suc v)
  bubble-v {suc n} (suc r)  (suc v) = suc (bubble-v r v)

-- Applying a permutation
_§_ : ∀ {n} → Perm n → Fin n → Fin n
(v ◀ σ) § zero    = v
(v ◀ σ) § (suc k) = bubble-r (σ § k) v

forget_at_ : {n : ℕ} → Perm (suc n) → Fin (suc n) → Perm n
forget_at_         (v ◀ σ) zero = σ
forget_at_ {zero}  (v ◀ ε) (suc ())
forget_at_ {suc m} (v ◀ σ) (suc k) = bubble-v (σ § k) v ◀ forget σ at k

-- -- if r ≥ v then (r + 1, v) else (r, v - 1)
-- bob : {n : ℕ} → Fin (suc n) → Fin (suc (suc n)) → Fin (suc (suc n)) × Fin (suc n)
-- bob r zero = suc r , zero
-- bob zero (suc v) = zero , v
-- bob {zero} (suc ()) (suc v)
-- bob {suc n} (suc r) (suc v) with bob r v
-- bob {suc n} (suc r) (suc v) | rₓ , vₓ = suc rₓ , suc vₓ
-- take_at_ : {n : ℕ} → Perm (suc n) → Fin (suc n) → Fin (suc n) × Perm n
-- take_at_         (v ◀ σ) zero = v , σ
-- take_at_ {zero}  (v ◀ ε) (suc ())
-- take_at_ {suc n} (v ◀ σ) (suc k) with take σ at k
-- take_at_ {suc n} (v ◀ σ) (suc k) | tr , tσ with bob tr v
-- take_at_ {suc n} (v ◀ σ) (suc k) | tr , tσ | bobr , bobv = bobr , bobv ◀ tσ
-- _§_ : ∀ {n} → Perm n → Fin n → Fin n
-- _§_ {zero} σ ()
-- _§_ {suc n} σ k = proj₁ (take σ at k)
-- forget_at_ : {n : ℕ} → Perm (suc n) → Fin (suc n) → Perm n
-- forget σ at k = proj₂ (take σ at k)

-- Composition
_∙_ :  ∀ {n} → Perm n → Perm n → Perm n
ε ∙ ε = ε
-- σ₁ ∙ (k ◀ σ₂) with take σ₁ at k
-- σ₁ ∙ (k ◀ σ₂) | tv , tσ₁ = tv ◀ tσ₁ ∙ σ₂
σ₁ ∙ (k ◀ σ₂) = (σ₁ § k) ◀ (forget σ₁ at k ∙ σ₂)

-- Identity
i : ∀ {n} → Perm n
i {zero} = ε
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

-- example : Perm 6
-- example = # 3 ◀ # 0 ◀ # 2 ◀ # 0 ◀ # 1 ◀ # 0 ◀ ε

-- example-§-1 : example § (# 0) ≡ # 3
-- example-§-1 = refl
-- example-§-2 : example § (# 1) ≡ # 0
-- example-§-2 = refl
-- example-§-3 : example § (# 2) ≡ # 4
-- example-§-3 = refl
-- example-§-4 : example § (# 3) ≡ # 1
-- example-§-4 = refl
-- example-§-5 : example § (# 4) ≡ # 5
-- example-§-5 = refl
-- example-§-6 : example § (# 5) ≡ # 2
-- example-§-6 = refl

-- example-* : example * ≡ # 1 ◀ # 2 ◀ # 3 ◀ # 0 ◀ # 0 ◀ # 0 ◀ ε
-- example-* = refl

-- example-*-* : (example *) * ≡ example
-- example-*-* = refl


-----------------------------------------
-- PROPERTIES

-- Open FP in such a way that equality on Perm n is used if it is provided with
-- a parameter {n}.
open module FP {n : ℕ} = Algebra.FunctionProperties (_≡_ {A = Perm n})

i-* : ∀ n → (i {n}) * ≡ i {n}
i-* zero = refl
i-* (suc n) rewrite i-* n = refl

i-§ : ∀ {n} (k : Fin n) → i § k ≡ k
i-§ zero = refl
i-§ (suc k) rewrite i-§ k = refl

∙-§ : ∀ {n} (σ₁ σ₂ : Perm n) (k : Fin n) → (σ₁ ∙ σ₂) § k ≡ σ₁ § (σ₂ § k)
∙-§ {zero} ε ε ()
∙-§ {suc n} (v₁ ◀ σ₁) (v₂ ◀ σ₂) zero = refl
∙-§ {suc zero} (v₁ ◀ σ₁) (v₂ ◀ σ₂) (suc ())
∙-§ {suc (suc n)} (v₁ ◀ σ₁) (v₂ ◀ σ₂) (suc k) rewrite ∙-§ (forget v₁ ◀ σ₁ at v₂) σ₂ k = lem1 (v₁ ◀ σ₁) (σ₂ § k) v₂
  where

  bubble-lem1 : ∀ {n} (k : Fin (suc n)) (m : Fin (suc (suc n))) → bubble-r (bubble-v k m) (bubble-r k m) ≡ m
  bubble-lem1 k zero = refl
  bubble-lem1 zero (suc m) = refl
  bubble-lem1 {zero} (suc ()) (suc m)
  bubble-lem1 {suc n} (suc k) (suc m) rewrite bubble-lem1 k m = refl
  
  bubble-lem2 : ∀ {n} (x : Fin (suc n)) (k : Fin (suc (suc n))) (v : Fin (suc (suc (suc n))))
       → bubble-r (bubble-r x (bubble-v k v)) (bubble-r k v) ≡ bubble-r (bubble-r x k) v
  bubble-lem2 x k zero = refl
  bubble-lem2 x zero (suc v) = refl
  bubble-lem2 zero (suc k) (suc v) = refl
  bubble-lem2 {zero} (suc ()) (suc k) (suc v)
  bubble-lem2 {suc n} (suc x) (suc k) (suc v) rewrite bubble-lem2 x k v = refl
  
  lem1 : ∀ {n} (σ : Perm (suc (suc n))) (m : Fin (suc n)) (k : Fin (suc (suc n)))
       → bubble-r ((forget σ at k) § m) (σ § k) ≡ σ § bubble-r m k
  lem1 {n}     (v ◀ σ) m zero = refl
  lem1 {n}     (v ◀ σ) zero (suc k) = bubble-lem1 (σ § k) v
  lem1 {zero}  (v ◀ σ) (suc ()) (suc k)
  lem1 {suc n} (v ◀ σ) (suc m) (suc k) rewrite sym (lem1 σ m k) = bubble-lem2 ((forget σ at k) § m) (σ § k) v


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
firstzero-*-identity (suc k) (v ◀ σ)
  rewrite §-firstzero (v ◀ σ)
        | firstzero-*-identity k (forget v ◀ σ at firstzero (v ◀ σ)) = refl

§-*-zero : ∀ {n} (k : Fin (suc n)) (σ : Perm n) → (k ◀ σ) * § k ≡ zero
§-*-zero k σ with §-firstzero ((k ◀ σ) *)
... | p rewrite firstzero-*-identity k σ = p

forget-*-identity : ∀ {n} (k : Fin (suc n)) (σ : Perm n) → forget (k ◀ σ) * at k ≡ σ *
forget-*-identity zero σ = refl
forget-*-identity (suc ()) ε
forget-*-identity (suc k) (v ◀ σ)
  rewrite §-firstzero (v ◀ σ)
        | §-*-zero k (forget v ◀ σ at firstzero (v ◀ σ))
        | forget-*-identity k (forget v ◀ σ at firstzero (v ◀ σ)) = refl

*-involutive : ∀ {n} → Involutive {n} _*
*-involutive ε = refl
*-involutive (v ◀ σ) rewrite firstzero-*-identity v σ
                           | forget-*-identity v σ
                           | *-involutive σ = refl

*-∙-left-inverse : ∀ {n} → LeftInverse {n} i _* _∙_
*-∙-left-inverse σ rewrite sym (*-∙-right-inverse (σ *))
                         | *-involutive σ = refl

§-right-inverse : ∀ {n} (σ : Perm n) → ∀ x → σ § (σ * § (x)) ≡ x
§-right-inverse σ x rewrite sym (∙-§ σ (σ *) x) | *-∙-right-inverse σ = i-§ x

§-left-inverse : ∀ {n} (σ : Perm n) → ∀ x → σ * § (σ § (x)) ≡ x
§-left-inverse σ x rewrite sym (∙-§ (σ *) σ x) | *-∙-left-inverse σ = i-§ x
\end{code}
