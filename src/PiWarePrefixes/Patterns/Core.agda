open import PiWare.Atom using (Atomic)
open import PiWare.Gates using (Gates)

module PiWarePrefixes.Patterns.Core {At : Atomic} (Gt : Gates At) where

open import Data.Fin as Fin using (Fin)
open import Data.Nat using (ℕ; zero; suc; _*_; _+_; _<_; s≤s)
open import Data.Nat.Properties as NP using (m≤m+n)
open import Data.Nat.Properties.Simple using (+-suc; +-right-identity; *-comm)
open import Data.Vec using (Vec; sum; []; _∷_)
open import Function using (_$_)

open import PiWare.Circuit Gt using (ℂ; Plug; _⟫_; _∥_)
open import PiWare.Patterns Gt using (parsN)
open import PiWarePrefixes.Permutation as P using (Perm; _§_; ε; _◀_; _*)
open import PiWare.Plugs Gt using (id⤨)
open import PiWarePrefixes.Plugs.Core Gt using (zip⤨)


zipWith : ∀ {k n cs} → ℂ {cs} k 1 → ℂ {cs} (k * n) (1 * n)
zipWith {k} {n} f with (zip⤨ {k} {n} ⟫ parsN {n} f)
zipWith {k} {n} f | z rewrite *-comm n 1 | +-right-identity n = z

⤚-perm : ∀ {n} → (xs : Vec ℕ n) → Perm (sum xs + n)
⤚-perm {n} xs = toPerm' 0 xs
  where
  toPerm' : ∀ {n} → (i : ℕ) → (xs : Vec ℕ n) → Perm (i + sum xs + n)
  toPerm' i [] = P.i
  toPerm' {suc n} i (zero ∷ xs) rewrite +-suc (i + sum xs) n = toPerm' (suc i) xs
  toPerm' {suc n} i (suc x ∷ xs) rewrite +-suc i (sum (x ∷ xs)) = Fin.fromℕ≤ i< ◀ toPerm' i (x ∷ xs)
    where
    i< : i < suc (i + sum (x ∷ xs) + suc n)
    i< = s≤s $ begin
      i                         ≤⟨ m≤m+n _ (sum (x ∷ xs)) ⟩
      i + sum (x ∷ xs)          ≤⟨ m≤m+n _ (suc n) ⟩
      i + sum (x ∷ xs) + suc n  ∎
      where open Data.Nat.≤-Reasoning

_⤚_ : ∀ {n cs} → (xs : Vec ℕ n) → ℂ {cs} n n → ℂ {cs} (sum xs + n) (sum xs + n)
_⤚_ {n} xs c = Plug (_§_ (⤚-perm xs))
              ⟫ id⤨ {sum xs} ∥ c
              ⟫ Plug (_§_ (⤚-perm xs *))

postulate
  ⤙-perm : ∀ {n} → (xs : Vec ℕ n) → Perm (sum xs + n)

_⤙_ : ∀ {n cs} → ℂ {cs} n n → (xs : Vec ℕ n) → ℂ {cs} (sum xs + n) (sum xs + n)
_⤙_ {n} c xs = Plug (_§_ (⤙-perm xs))
              ⟫ id⤨ {sum xs} ∥ c
              ⟫ Plug (_§_ (⤙-perm xs *))
