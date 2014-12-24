module PiWarePrefixes.Permutation where

-- Based on https://github.com/ruisb/PiGraph/blob/master/Permutation.agda

open import Function
open import Data.Fin as Fin
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


private

  bubblefrom : {n : ℕ} → Fin (suc n) → Fin n → Fin (suc n)
  bubblefrom k m with (toℕ k) Nat.≤? (toℕ m)
  ...              | yes _  = suc     m 
  ...              | no  _  = inject₁ m

-- Remove an element from the image
forget_at_ : {n : ℕ} → Perm (suc n) → Fin (suc n) → Perm n
forget_at_         (v ◀ σ) zero = σ
forget_at_ {zero}  (v ◀ ε) (suc ())
forget_at_ {suc m} (v ◀ σ) (suc k) = down v ◀ forget_at_ {m} σ k
  where
  down :  {n : ℕ} → Fin (suc (suc n)) -> Fin (suc n)
  down zero    = zero
  down (suc x) = x 

putzero : ∀ {n} → Fin (suc n) → Perm n → Perm (suc n)
putzero zero     σ = zero ◀ σ
putzero (suc ()) ε
putzero (suc k) (v ◀ σ) = suc v ◀ putzero k σ

-- 'Using' a permutation
_§_ : ∀ {n} → Perm n → Fin n → Fin n
(k ◀ σ) § zero    = k
(k ◀ σ) § (suc n) = bubblefrom k (σ § n)

-- Composition
_∙_ :  ∀ {n} → Perm n → Perm n → Perm n
ε ∙ ε             = ε
σ₁ ∙ (k ◀ σ₂)  = (σ₁ § k) ◀ (forget σ₁ at k ∙ σ₂)

-- Identity
i : ∀ {n} → Perm n
i {zero}  = ε
i {suc m} = zero ◀ i

-- Get the inverse permutation
_* : ∀ {n} → Perm n → Perm n
ε *        = ε
(v ◀ σ) * = putzero v (σ *)


-----------------------------------------
-- PROPERTIES

open module FP {n : ℕ} = Algebra.FunctionProperties (_≡_ {A = Perm n})

i-* : ∀ {n} → (i {n}) * ≡ i {n}
i-* {zero } = refl
i-* {suc n} = cong (_◀_ zero) (i-* {n}) 

i-§ : ∀ {n} {k : Fin n} → i § k ≡ k
i-§ {k = zero } = refl
i-§ {k = suc m} = cong (bubblefrom zero) i-§

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

forget-putzero-identity : ∀ {n} (v : Fin (suc n)) (σ : Perm n) → forget putzero v σ at v ≡ σ
forget-putzero-identity zero σ = refl
forget-putzero-identity (suc ()) ε
forget-putzero-identity (suc v) (x ◀ σ) = cong (_◀_ x) (forget-putzero-identity v σ)

putzero-§ : ∀ {n} (v : Fin (suc n)) (σ : Perm n) → putzero v σ § v ≡ zero
putzero-§ zero σ = refl
putzero-§ (suc ()) ε
putzero-§ (suc v) (x ◀ σ) rewrite putzero-§ v σ = refl

lem3 : ∀ {n} (v : Fin (suc n)) (σ₁ σ₂ : Perm n) → putzero v σ₁ ∙ (v ◀ σ₂) ≡ zero ◀ (σ₁ ∙ σ₂)
lem3 zero σ₁ σ₂ = refl
lem3 (suc ()) ε ε
lem3 (suc v) (x ◀ σ₁) σ₂ rewrite forget-putzero-identity v σ₁ | putzero-§ v σ₁ = refl

∙-left-inverse : ∀ {n} → LeftInverse {n} i _* _∙_
∙-left-inverse ε = refl
∙-left-inverse (v ◀ σ) rewrite sym (∙-left-inverse σ) = lem3 v (σ *) σ

-- FALSE
-- lem4 : ∀ {n} (k : Fin (suc n)) (σ₁ σ₂ : Perm n) → (k ◀ σ₁) ∙ putzero k (σ₂) ≡ zero ◀ (σ₁ ∙ σ₂)


-- A perm always contains at least one zero
firstzero : ∀ {n} → Perm (suc n) → Fin (suc n)
firstzero {n} (zero ◀ σ) = zero
firstzero {zero} (suc () ◀ σ)
firstzero {suc n} (suc v ◀ σ) = suc (firstzero σ)

firstzero-putzero : ∀ {n} (k : Fin (suc n)) (σ : Perm n) → firstzero (putzero k σ) ≡ k
firstzero-putzero zero σ = refl
firstzero-putzero (suc ()) ε
firstzero-putzero (suc k) (v ◀ σ) = cong suc (firstzero-putzero k σ)

--what is the first element of an inversed perm ?
--  the position where the first 0 was in the original perm ?

lem4 : ∀ {n} (k : Fin (suc n)) (σ : Perm n) → (k ◀ σ) ∙ putzero k (σ *) ≡ zero ◀ (σ ∙ (σ *))
lem4 zero σ = refl
lem4 (suc ()) ε
lem4 (suc k) σ = {!!}
-- lem4 (suc k) σ with σ *
-- lem4 (suc ()) σ | ε
-- lem4 (suc k) σ | x ◀ si = {!!}
-- lem4 (suc k) σ | x ◀ si with (toℕ (suc k)) Nat.≤? (toℕ (σ § x))
-- lem4 (suc k) σ | x ◀ si | yes p = {!!}
-- lem4 (suc k) σ | x ◀ si | no ¬p = {!!}

∙-right-inverse : ∀ {n} → RightInverse {n} i _* _∙_
∙-right-inverse ε = refl
∙-right-inverse (v ◀ σ) rewrite sym (∙-right-inverse σ) = {!!} --lem4 v σ
-- ∙-right-inverse (v ◀ σ) rewrite sym (∙-right-inverse σ) with σ *

-- ∙-right-inverse (v ◀ σ) with forget ((v ◀ σ) *) at v | forget-putzero-identity v (σ *) 
-- ∙-right-inverse (v ◀ ε) | ε | refl = {!!}
-- ∙-right-inverse (v ◀ σ) | x ◀ si | fpi = {!!}

-- ∙-assoc : ∀ {n} → Associative (_∙_ {n})
-- --∙-assoc xs ys zs = {!xs!}
-- ∙-assoc ε ε ε = refl
-- ∙-assoc (x ◀ xs) (y ◀ ys) (z ◀ zs) with ∙-assoc xs ys zs
-- ... | ih = {!!}


-- p* : ∀ {n} (k : Fin (suc n)) (σ : Perm n) → putzero k (σ *) * ≡ k ◀ σ
-- p* zero σ = {!!}
-- p* (suc ()) ε
-- p* (suc k) (v ◀ σ) with p* v σ
-- ... | rec = {!!}
-- p* (suc zero) (zero ◀ ε) | ε = refl
-- p* (suc (suc ())) (_ ◀ ε) | ε
-- p* (suc zero) (suc () ◀ ε) | ε
--p* (suc k) (v ◀ σ) | x ◀ sr = {!sr!}
-- p* (suc zero) (zero ◀ (x ◀ σ)) | zero ◀ sr = {!!}
-- p* (suc zero) (zero ◀ σ) | suc x ◀ sr = {!!} --cong (_◀_ (suc zero)) (cong (_◀_ zero) {!x!})
-- p* (suc (suc k)) (zero ◀ σ) | x ◀ sr = {!!}
-- p* (suc k) (suc v ◀ σ) | x ◀ sr = {!!}

-- putzero-*-lemma : ∀ {n} (k : Fin n) (σ : Perm n) → putzero (suc k) (σ *) * ≡ (suc k) ◀ σ
-- putzero-*-lemma () ε
-- putzero-*-lemma k (v ◀ σ) with σ *

-- putzero-*-lemma zero (zero ◀ ε) | ε = refl
-- putzero-*-lemma (suc ()) (zero ◀ ε) | ε
-- putzero-*-lemma k (suc () ◀ σ) | ε

-- putzero-*-lemma k (v ◀ σ) | x ◀ p = {!v!}

-- ∙-involutive : ∀ {n : ℕ} → Involutive (_* {n})
-- ∙-involutive {zero} ε = refl
-- ∙-involutive {suc n} (zero ◀ σ) = cong (_◀_ zero) (∙-involutive σ)
-- -- ∙-involutive {suc n} (suc v ◀ σ) = {!!}
-- ∙-involutive {suc n} (suc v ◀ σ) with pp v (σ *)
--   where
--   pp : ∀ {n} (k : Fin n) (σ : Perm n) → putzero (suc k) σ * ≡ (suc k) ◀ (σ *)
--   pp () ε
--   pp zero (zero ◀ σ₁) = refl
--   pp (suc k) (zero ◀ σ₁) = {!!}
--   pp k (suc v₁ ◀ σ₁) = {!!}
  -- pp zero σ = cong (_◀_ zero) (∙-involutive σ)
  -- pp (suc ()) ε
  -- pp (suc k) (v ◀ σ) with pp v σ -- cong _* (pp v σ)
  -- ... | a = {!!} --rewrite ∙-involutive (putzero v (σ *)) = {!!} 
-- ... | a rewrite ∙-involutive σ = a

-- ∙-involutive {suc n} (v ◀ σ) with ∙-involutive {n} σ
-- ∙-involutive {suc n} (zero ◀ σ) | ih = cong (_◀_ zero) ih
-- ∙-involutive {suc .0} (suc () ◀ ε) | ih
-- ∙-involutive {suc ._} (suc v₁ ◀ (v₂ ◀ σ)) | ih = {!!}

--∙-§ : {n : ℕ} {σ₁ σ₂ : Perm n} {k : Fin n} → (σ₁ ∙ σ₂) § k ≡ σ₁ § (σ₂ § k)
--∙-§  {zero } {ε}  {ε}       {()} 
--∙-§  {suc n} {σ₁} {v ◀ σ₂} {zero } = ?
--∙-§  {suc n} {σ₁} {v ◀ σ₂} {suc k} = cong ? (∙-§ {n} {forget σ₁ at v} {σ₂} {k})

--∙-§  {suc n} {σ₁} {v ◀ σ₂} {k} = cong (?) (∙-§ {n} {forget σ₁ at v} {σ₂} {?})

--∙-assoc : {n : ℕ} {σ₁ σ₂ σ₃ : Perm n} → (σ₁ ∙ σ₂) ∙ σ₃ ≡ σ₁ ∙ (σ₂ ∙ σ₃)
--∙-assoc {zero } {ε} {ε} {ε} = refl
--∙-assoc {suc m} {σ₁} {σ₂} {v ◀ σ₃'} = cong (?) (∙-assoc {m} {forget σ₁ at (σ₂ § v)} {forget σ₂ at v} {σ})

--∙-linv : {n : ℕ} {σ : Perm n} → σ * ∙ σ ≡ i
--∙-linv {zero } {ε}      = refl
--∙-linv {suc n} {v ◀ σ} = ? (∙-linv {n} {σ})

-- ∙-rinv : {n : ℕ} {σ : Perm n} → σ ∙ σ * ≡ i
-- ∙-rinv {zero } {ε}      = refl
-- ∙-rinv {suc n} {v ◀ σ} = {!!} (∙-rinv {n} {σ})
