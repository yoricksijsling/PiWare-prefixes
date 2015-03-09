open import PiWare.Atom using (Atomic)
open import PiWare.Gates using (Gates)

module PiWarePrefixes.Plugs.Core {At : Atomic} (Gt : Gates At) where

open import Data.Fin using (Fin; toℕ)
open import Data.Nat using (zero; suc; _+_; _*_; _≟_)
open import Data.Nat.DivMod using (DivMod; _divMod_; _mod_)
open import Data.Nat.Properties.Simple using (*-right-zero)
open import Data.Unit using (tt)
open import Function using (id)
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Decidable using (False; fromWitnessFalse)

open import PiWare.Circuit Gt using (𝐂; Plug)
open import PiWare.Interface using (Ix)

≢0-*-≢0 : ∀ n m → False (n ≟ 0) → False (m ≟ 0) → False (n * m ≟ 0)
≢0-*-≢0 zero m () _
≢0-*-≢0 (suc n) zero _ ()
≢0-*-≢0 (suc n) (suc m) _ _ = tt

zip⤨ : ∀ {k n} → 𝐂 (k * n) (n * k)
zip⤨ {k} {n} = p k n
  where
  p : ∀ k n → 𝐂 (k * n) (n * k)
  p k n with k ≟ 0 | n ≟ 0
  p k n | yes k≡0 | _        rewrite k≡0 | *-right-zero n = Plug id
  p k n | no k≢0  | yes n≡0  rewrite n≡0 | *-right-zero k = Plug id
  p k n | no k≢0  | no n≢0   = Plug (finZip (fromWitnessFalse n≢0) (fromWitnessFalse k≢0))
    where
    -- We use _mod_ to make it a Fin (k * n), but it should actually already be in the range.
    -- From o<n*k and o=r+q*k (from DivMod) it follows that q<n. Then because r<k (from DivMod)
    -- we can deduce that n*r+q<n*k.
    finZip : False (n ≟ 0) → False (k ≟ 0) → Fin (n * k) → Fin (k * n)
    finZip n≢0 k≢0 o = _mod_ val (k * n) {≢0-*-≢0 k n k≢0 n≢0}
      where
      dm : DivMod (toℕ o) k
      dm = (toℕ o divMod k) {k≢0}
      val = n * toℕ (DivMod.remainder dm) + DivMod.quotient dm
