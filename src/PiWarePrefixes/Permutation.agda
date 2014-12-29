module PiWarePrefixes.Permutation where

-- Roughly based on https://github.com/ruisb/PiGraph/blob/master/Permutation.agda

open import Function
open import Data.Fin
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

  bubblefrom : {n : ℕ} → Fin (suc n) → Fin n → Fin (suc n)
  bubblefrom zero m = suc m
  bubblefrom (suc k) zero = zero
  bubblefrom (suc k) (suc m) = suc (bubblefrom k m)

-- Remove an element from the image
forget_at_ : {n : ℕ} → Perm (suc n) → Fin (suc n) → Perm n
forget_at_         (v ◀ σ) zero = σ
forget_at_ {zero}  (v ◀ ε) (suc ())
forget_at_ {suc m} (v ◀ σ) (suc k) = down v ◀ forget_at_ {m} σ k
  where
  down :  {n : ℕ} → Fin (suc (suc n)) -> Fin (suc n)
  down zero    = zero
  down (suc x) = x 

-- 'Using' a permutation
_§_ : ∀ {n} → Perm n → Fin n → Fin n
(k ◀ σ) § zero    = k
-- (k ◀ σ) § (suc n) = inject₁ (forget k ◀ σ at # 0 § n)
(k ◀ σ) § (suc n) = bubblefrom k (σ § n)

-- Composition
_∙_ :  ∀ {n} → Perm n → Perm n → Perm n
ε ∙ ε             = ε
σ₁ ∙ (k ◀ σ₂)  = (σ₁ § k) ◀ (forget σ₁ at k ∙ σ₂)

-- Identity
i : ∀ {n} → Perm n
i {zero}  = ε
i {suc m} = zero ◀ i

_◀*_ : ∀ {n} → Fin (suc n) → Perm n → Perm (suc n)
zero ◀* σ = zero ◀ σ
suc () ◀* ε
suc k ◀* (v ◀ σ) = suc v ◀ (k ◀* σ)

-- Get the inverse permutation
_* : ∀ {n} → Perm n → Perm n
ε *        = ε
(v ◀ σ) * = v ◀* (σ *)

-- A perm always contains at least one zero
firstzero : ∀ {n} → Perm (suc n) → Fin (suc n)
firstzero {_} (zero ◀ σ) = zero
firstzero {zero} (suc () ◀ σ)
firstzero {suc n} (suc v ◀ σ) = suc (firstzero σ)

-- Another way of making the inverse. Easy to traverse!
_*' : ∀ {n} → Perm n → Perm n
_*' {zero} ε = ε
_*' {suc n} σ = firstzero σ ◀ ((forget σ at firstzero σ) *')

-----------------------------------------
-- EXAMPLES

example : Perm 6
example = # 3 ◀ # 0 ◀ # 2 ◀ # 0 ◀ # 1 ◀ # 0 ◀ ε

test-§-1 : example § (# 0) ≡ # 3
test-§-1 = refl
test-§-2 : example § (# 1) ≡ # 0
test-§-2 = refl
test-§-3 : example § (# 2) ≡ # 4
test-§-3 = refl
test-§-4 : example § (# 3) ≡ # 1
test-§-4 = refl
test-§-5 : example § (# 4) ≡ # 5
test-§-5 = refl
test-§-6 : example § (# 5) ≡ # 2
test-§-6 = refl

test-* : example * ≡ # 1 ◀ # 2 ◀ # 3 ◀ # 0 ◀ # 0 ◀ # 0 ◀ ε
test-* = refl

test-*-* : (example *) * ≡ example
test-*-* = refl

test-*' : example *' ≡ # 1 ◀ # 2 ◀ # 3 ◀ # 0 ◀ # 0 ◀ # 0 ◀ ε
test-*' = refl

test-*'-*' : (example *') *' ≡ example
test-*'-*' = refl


-----------------------------------------
-- PROPERTIES

open module FP {n : ℕ} = Algebra.FunctionProperties (_≡_ {A = Perm n})

firstzero-◀* : ∀ {n} (k : Fin (suc n)) (σ : Perm n) → firstzero (k ◀* σ) ≡ k
firstzero-◀* zero σ = refl
firstzero-◀* (suc ()) ε
firstzero-◀* (suc k) (v ◀ σ) = cong suc (firstzero-◀* k σ)

*-*' : ∀ {n} (σ : Perm n) → σ * ≡ σ *'
*-*' ε = refl
*-*' (v ◀ σ) with *-*' σ
... | rec = {!!}

i-* : ∀ {n} → (i {n}) * ≡ i {n}
i-* {zero } = refl
i-* {suc n} = cong (_◀_ zero) i-*

i-*' : ∀ {n} → (i {n}) * ≡ i {n}
i-*' {zero } = refl
i-*' {suc n} = cong (_◀_ zero) i-*'

§-firstzero : ∀ {n} (σ : Perm (suc n)) → σ § firstzero σ ≡ zero
§-firstzero {zero} (zero ◀ σ) = refl
§-firstzero {zero} (suc () ◀ σ)
§-firstzero {suc n} (zero ◀ σ) = refl
§-firstzero {suc n} (suc v ◀ σ) rewrite §-firstzero σ = refl 

i-§ : ∀ {n} {k : Fin n} → i § k ≡ k
i-§ {k = zero } = refl
i-§ {k = suc k} = cong suc i-§

forget-i≡i : ∀ {n} {k : Fin (suc n)} → forget i at k ≡ i
forget-i≡i {_} {zero} = refl
forget-i≡i {zero} {suc ()}
forget-i≡i {suc n} {suc k} = cong (_◀_ zero) (forget-i≡i {k = k})

∙-left-identity : ∀ {n} → LeftIdentity {n} i _∙_
∙-left-identity {zero} ε = refl
∙-left-identity {suc n} (v ◀ σ)
  rewrite i-§ {k = v} | forget-i≡i {k = v} = cong (_◀_ v) (∙-left-identity σ)

∙-right-identity : ∀ {n} → RightIdentity {n} i _∙_
∙-right-identity ε = refl
∙-right-identity (v ◀ σ) = cong (_◀_ v) (∙-right-identity σ)

∙-left-zero : LeftZero {zero} ε _∙_
∙-left-zero ε = refl

∙-right-zero : RightZero {zero} ε _∙_
∙-right-zero ε = refl

forget-◀*-identity : ∀ {n} (v : Fin (suc n)) (σ : Perm n) → forget v ◀* σ at v ≡ σ
forget-◀*-identity zero σ = refl
forget-◀*-identity (suc ()) ε
forget-◀*-identity (suc v) (x ◀ σ) = cong (_◀_ x) (forget-◀*-identity v σ)

◀*-§ : ∀ {n} (v : Fin (suc n)) (σ : Perm n) → (v ◀* σ) § v ≡ zero
◀*-§ zero σ = refl
◀*-§ (suc ()) ε
◀*-§ (suc v) (x ◀ σ) rewrite ◀*-§ v σ = refl

lem3 : ∀ {n} (v : Fin (suc n)) (σ₁ σ₂ : Perm n) → (v ◀* σ₁) ∙ (v ◀ σ₂) ≡ zero ◀ (σ₁ ∙ σ₂)
lem3 zero σ₁ σ₂ = refl
lem3 (suc ()) ε ε
lem3 (suc v) (x ◀ σ₁) σ₂ rewrite forget-◀*-identity v σ₁ | ◀*-§ v σ₁ = refl

∙-*-left-inverse : ∀ {n} → LeftInverse {n} i _* _∙_
∙-*-left-inverse ε = refl
∙-*-left-inverse (v ◀ σ) rewrite sym (∙-*-left-inverse σ) = lem3 v (σ *) σ

∙-*'-right-inverse : ∀ {n} → RightInverse {n} i _*' _∙_
∙-*'-right-inverse ε = refl
∙-*'-right-inverse (v ◀ σ) rewrite §-firstzero (v ◀ σ) | ∙-*'-right-inverse (forget v ◀ σ at firstzero (v ◀ σ)) = refl

firstzero-*'-identity : ∀ {n} (k : Fin (suc n)) (σ : Perm n) → firstzero ((k ◀ σ) *') ≡ k
firstzero-*'-identity zero σ = refl
firstzero-*'-identity (suc ()) ε
firstzero-*'-identity (suc k) (v ◀ σ) = cong suc (firstzero-*'-identity k (forget v ◀ σ at firstzero (v ◀ σ)))

--lem5 : ∀ {n} (k : Fin (suc n)) (σ : Perm n) → (forget firstzero (k ◀ σ) ◀ (forget k ◀ σ at firstzero (k ◀ σ)) *' at k) ≡ σ *'
forget-*'-identity : ∀ {n} (k : Fin (suc n)) (σ : Perm n) → (forget (k ◀ σ) *' at k) ≡ σ *'
forget-*'-identity zero σ = refl
forget-*'-identity (suc ()) ε
forget-*'-identity (suc k) (v ◀ σ) = cong (_◀_ (firstzero (v ◀ σ))) (forget-*'-identity k (forget v ◀ σ at firstzero (v ◀ σ)))

*'-involutive : ∀ {n} → Involutive {n} _*'
*'-involutive ε = refl
*'-involutive (v ◀ σ) rewrite firstzero-*'-identity v σ | forget-*'-identity v σ = cong (_◀_ v) (*'-involutive σ)

∙-*'-left-inverse : ∀ {n} → LeftInverse {n} i _*' _∙_
∙-*'-left-inverse σ with ∙-*'-right-inverse (σ *')
... | ri rewrite *'-involutive σ = ri

-- ∙-assoc : ∀ {n} → Associative (_∙_ {n})
-- --∙-assoc xs ys zs = {!xs!}
-- ∙-assoc ε ε ε = refl
-- ∙-assoc (x ◀ xs) (y ◀ ys) (z ◀ zs) with ∙-assoc xs ys zs
-- ... | ih = {!!}

--∙-assoc : {n : ℕ} {σ₁ σ₂ σ₃ : Perm n} → (σ₁ ∙ σ₂) ∙ σ₃ ≡ σ₁ ∙ (σ₂ ∙ σ₃)
--∙-assoc {zero } {ε} {ε} {ε} = refl
--∙-assoc {suc m} {σ₁} {σ₂} {v ◀ σ₃'} = cong (?) (∙-assoc {m} {forget σ₁ at (σ₂ § v)} {forget σ₂ at v} {σ})
