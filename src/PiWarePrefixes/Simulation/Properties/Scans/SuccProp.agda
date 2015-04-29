open import PiWare.Atom using (Atomic; module Atomic)
open import PiWare.Gates using (Gates)
open import PiWarePrefixes.Circuit.Monoid using (module ℂ-Monoid; ℂ-Monoid)

module PiWarePrefixes.Simulation.Properties.Scans.SuccProp {At : Atomic} {Gt : Gates At}
                                                           {ℂ-monoid : ℂ-Monoid {Gt = Gt}} where

open ℂ-Monoid ℂ-monoid using (plusℂ; plusℂ-assoc)

open import Data.Nat using (ℕ; zero; suc; _+_; pred)
open import Data.Nat.Properties using (cancel-+-left)
open import Data.Nat.Properties.Simple using (+-suc; +-comm; +-assoc)
open import Function using (flip; _⟨_⟩_)
open import PiWare.Circuit {Gt = Gt} using (ℂ; 𝐂; Plug; _⟫_; _∥_; σ)
open import PiWarePrefixes.Patterns.Fan {plusℂ = plusℂ}
open import PiWarePrefixes.Patterns.HetSeq {Gt = Gt}
open import PiWarePrefixes.Patterns.Scan {ℂ-monoid = ℂ-monoid}
open import PiWare.Plugs Gt using (id⤨)
open import PiWarePrefixes.Plugs.Core {Gt = Gt} using (rewire⤨)
open import PiWarePrefixes.Simulation.Equality.Core {Gt = Gt} as SimEq
  renaming (≈⟦⟧-refl to refl; ≈⟦⟧-sym to sym; ≈⟦⟧-trans to trans)
open import PiWarePrefixes.Simulation.Properties {Gt = Gt}
open import PiWarePrefixes.Simulation.Properties.HetSeq {Gt = Gt}
open import PiWarePrefixes.Simulation.Properties.Fans {plusℂ = plusℂ} as FanProps
open import PiWarePrefixes.Simulation.Properties.Scans {ℂ-monoid = ℂ-monoid}
open FanProps.WithAssociativity {plusℂ-assoc = plusℂ-assoc}
open import Relation.Binary.PropositionalEquality as P using (_≡_; cong)

open SimEq.≈⟦⟧-Reasoning


▱-scan-succ : ∀ {m n} (f : ℂ (suc m) (suc m)) (g : ℂ n n) →
             {p : m + suc n ≡ suc m + n} →
             scan-succ (f ▱ scan-succ g ⟫[ p ] id⤨) ≈⟦⟧ scan-succ f ▱ scan-succ g
▱-scan-succ {m} {n} f g = begin
 scan-succ (f ▱ scan-succ g ⟫[] id⤨)
   ≈⟦⟧⟨⟩
 id⤨ ∥ (f ▱ scan-succ g ⟫[] id⤨) ⟫ fan _
   ≈⟦⟧⟨ (refl ∥-cong (⟫[]-right-identity _)) ⟫[-cong refl ⟩
 id⤨ ∥ f ▱ scan-succ g ⟫[] fan (2 + (m + n))
   ≈⟦⟧⟨ lem₁ f g ⟫[]-cong fan-cong (cong suc (P.sym (+-suc m n))) ⟩
 id⤨ ∥ f ∥ id⤨ ⟫[] (id⤨ ∥ g ⟫[] id⤨ ∥ fan (suc n)) ⟫[] fan (suc m + suc n)
   ≈⟦⟧⟨ (sym (⟫[]-assoc _ _ _)) ⟫[]-cong refl ⟨ trans ⟩ ⟫[]-assoc _ _ _ ⟩
 id⤨ ∥ f ∥ id⤨ ⟫[] id⤨ ∥ g ⟫[] (id⤨ {suc m} ∥ fan (suc n) ⟫[] fan (suc m + suc n))
   ≈⟦⟧⟨ refl ⟫[]-cong (⟫[]-replace _ ⟨ trans ⟩ ⟫[]-to-⟫ ⟨ trans ⟩ binary-fan-law m n) ⟩
 id⤨ ∥ f ∥ id⤨ ⟫[] id⤨ ∥ g ⟫[] (fan (2 + m) ∥ id⤨ ⟫[] id⤨ ∥ fan (suc n))
   ≈⟦⟧⟨ lem₂ f g ⟩
 id⤨ ∥ f ∥ id⤨ ⟫[] fan (2 + m) ∥ id⤨ ⟫[] (id⤨ ∥ g ⟫[] id⤨ ∥ fan (suc n))
   ≈⟦⟧⟨ lem₃ f g ⟩
 scan-succ f ▱ scan-succ g
   ∎
 where

 abstract
   swaplem : ∀ {m mᵢ n} (f : ℂ m m) {p : mᵢ + n ≡ m + n} (g : ℂ n n) →
             id⤨ {mᵢ} ∥ g ⟫[ p ] f ∥ id⤨ {n} ≈⟦⟧ f ∥ id⤨ {n} ⟫[ P.sym p ] id⤨ {mᵢ} ∥ g
   swaplem {m} {mᵢ} {n} f {p} g = begin
     id⤨ {mᵢ} ∥ g ⟫[] f ∥ id⤨ {n}
       ≈⟦⟧⟨ ⟫[]-∥-distrib q P.refl ⟩
     (id⤨ {mᵢ} ⟫[] f) ∥ (g ⟫[] id⤨ {n})
       ≈⟦⟧⟨ ⟫[]-left-identity _ ∥-cong ⟫[]-right-identity _ ⟩
     f ∥ g
       ≈⟦⟧⟨ (sym (⟫[]-right-identity _)) ∥-cong sym (⟫[]-left-identity _) ⟩
     (f ⟫[ P.sym q ] id⤨ {mᵢ}) ∥ (id⤨ {n} ⟫[ P.refl ] g)
       ≈⟦⟧⟨ ⟫[]-∥-distribᵣ ⟩
     f ∥ id⤨ {n} ⟫[] id⤨ {mᵢ} ∥ g
       ≈⟦⟧⟨ ⟫[]-replace (P.sym p) ⟩
     _
       ∎
     where
     q : mᵢ ≡ m
     q = (cancel-+-left n (+-comm n _ ⟨ P.trans ⟩ p ⟨ P.trans ⟩ +-comm _ n))

 abstract
   ⟫[]-assoc-4 : ∀ {i j j′ m m′ n n′ o} →
                 (a : ℂ i j) {p : j ≡ j′} (b : ℂ j′ m) {q : m ≡ m′}
                 (c : ℂ m′ n) {r : n ≡ n′} (d : ℂ n′ o) →
                 a ⟫[ p ] b ⟫[ q ] (c ⟫[ r ] d) ≈⟦⟧ a ⟫[ p ] (b ⟫[ q ] c) ⟫[ r ] d
   ⟫[]-assoc-4 a b c d = sym (⟫[]-assoc _ _ _) ⟨ trans ⟩ (⟫[]-assoc _ _ _) ⟫[]-cong refl
               ⟨ trans ⟩ (refl ⟫[]-cong (⟫[]-replace _)) ⟫[]-cong refl
               ⟨ trans ⟩ ⟫[]-replace _ ⟫[]-cong refl
               ⟨ trans ⟩ ⟫[]-replace _

 lem₁ : ∀ {m n} (f : ℂ (suc m) (suc m)) (g : ℂ n n) →
        id⤨ {1} ∥ f ▱ scan-succ g
          ≈⟦⟧ (id⤨ {1} ∥ f ∥ id⤨ {n} ⟫[] (id⤨ {suc m + 1} ∥ g ⟫[] id⤨ {suc m} ∥ fan (suc n)))
 lem₁ {m} {n} f g = begin
   id⤨ ∥ f ▱ scan-succ g
     ≈⟦⟧⟨⟩
   id⤨ ∥ (f ∥ id⤨ ⟫[] id⤨ ∥ scan-succ g)
     ≈⟦⟧⟨ ⟫[]-id⤨-left-distrib ⟩
   _ ⟫[] id⤨ ∥ id⤨ ∥ scan-succ g
     ≈⟦⟧⟨ refl ⟫[]-cong (sym (∥-assoc _ _ _) ⟨ trans ⟩ ∥-id⤨ ∥-cong refl) ⟩
   _ ⟫[] id⤨ ∥ scan-succ g
     ≈⟦⟧⟨⟩
   _ ⟫[] id⤨ ∥ (id⤨ {1} ∥ g ⟫ fan (suc n))
     ≈⟦⟧⟨ refl ⟫[]-cong (sym ⟫-id⤨-left-distrib) ⟩
   _ ⟫[] (id⤨ ∥ id⤨ {1} ∥ g ⟫ id⤨ {suc m} ∥ fan (suc n))
     ≈⟦⟧⟨ refl ⟫[]-cong ((sym (∥-assoc _ _ _) ⟨ trans ⟩ ∥-id⤨ ∥-cong refl) ⟫[-cong refl) ⟩
   id⤨ ∥ f ∥ id⤨ ⟫[] (id⤨ ∥ g ⟫[] id⤨ ∥ fan (suc n))
     ≈⟦⟧⟨ refl ⟫[]-cong (⟫[]-replace (cong suc (+-assoc m 1 n))) ⟩
   _
     ≈⟦⟧⟨ ⟫[]-replace (cong (λ x → suc (x + n)) (+-comm 1 m)) ⟩
   _
     ∎

 lem₂ : ∀ {m n p q r} (f : ℂ (suc m) (suc m)) (g : ℂ n n) →
   id⤨ {1} ∥ f ∥ id⤨ {n} ⟫[ p ] id⤨ {suc m + 1} ∥ g ⟫[ q ] (fan (2 + m) ∥ id⤨ {n} ⟫[ r ] id⤨ {suc m} ∥ fan (suc n))
     ≈⟦⟧
   id⤨ {1} ∥ f ∥ id⤨ {n} ⟫[ P.refl ] fan (2 + m) ∥ id⤨ {n} ⟫[ cong (λ x → suc (x + n)) (+-comm 1 m) ] (id⤨ {suc m + 1} ∥ g ⟫[ cong suc (+-assoc m 1 n) ] id⤨ {suc m} ∥ fan (suc n))
 lem₂ {m} {n} {p} {q} {r} f g = begin
   a ⟫[] b ⟫[] (c ⟫[] d)
     ≈⟦⟧⟨ ⟫[]-assoc-4 a b c d ⟩
   a ⟫[] (b ⟫[] c) ⟫[] d
     ≈⟦⟧⟨ (refl ⟫[]-cong (swaplem (fan (2 + m)) g)) ⟫[]-cong refl ⟩
   a ⟫[] (c ⟫[] b) ⟫[] d
     ≈⟦⟧⟨ (refl ⟫[]-cong (⟫[]-replace _)) ⟫[]-cong refl
          ⟨ trans ⟩ ⟫[]-replace _ ⟫[]-cong refl ⟨ trans ⟩ ⟫[]-replace _ ⟩
   a ⟫[] (c ⟫[] b) ⟫[] d
     ≈⟦⟧⟨ sym (⟫[]-assoc-4 a c b d) ⟩
   a ⟫[] c ⟫[] (b ⟫[] d)
     ∎
   where
   a = id⤨ {1} ∥ f ∥ id⤨ {n}
   b = id⤨ {suc m + 1} ∥ g
   c = fan (2 + m) ∥ id⤨ {n}
   d = id⤨ {suc m} ∥ fan (suc n)

 lem₃ : ∀ {m n p q r} (f : ℂ (suc m) (suc m)) (g : ℂ n n) →
   id⤨ {1} ∥ f ∥ id⤨ {n} ⟫[ p ] fan (2 + m) ∥ id⤨ {n}
     ⟫[ q ] (id⤨ {suc m + 1} ∥ g ⟫[ r ] id⤨ {suc m} ∥ fan (suc n))
   ≈⟦⟧ scan-succ f ▱ scan-succ g
 lem₃ {m} {n} f g = begin
   id⤨ ∥ f ∥ id⤨ ⟫[] fan (2 + m) ∥ id⤨ ⟫[] (id⤨ ∥ g ⟫[] id⤨ {suc m} ∥ fan (suc n))
     ≈⟦⟧⟨ ((sym (∥-assoc _ _ _)) ⟫]-cong (refl ∥-cong refl))
          ⟫[]-cong ((sym (∥-id⤨ ∥-cong refl) ⟨ trans ⟩ ∥-assoc _ _ _) ⟫]-cong refl) ⟩
   (id⤨ ∥ f) ∥ id⤨ ⟫ fan (2 + m) ∥ id⤨ ⟫[] (id⤨ ∥ id⤨ ∥ g ⟫ id⤨ {suc m} ∥ fan (suc n))
     ≈⟦⟧⟨ ⟫-id⤨-right-distrib ⟫[]-cong ⟫-id⤨-left-distrib ⟩
   (id⤨ ∥ f ⟫ fan (2 + m)) ∥ id⤨ {n} ⟫[] id⤨ {suc m} ∥ (id⤨ ∥ g ⟫ fan (suc n))
     ≈⟦⟧⟨ ⟫[]-replace _ ⟩
   scan-succ f ∥ id⤨ ⟫[] id⤨ ∥ scan-succ g
     ≈⟦⟧⟨⟩
   scan-succ f ▱ scan-succ g
     ∎
