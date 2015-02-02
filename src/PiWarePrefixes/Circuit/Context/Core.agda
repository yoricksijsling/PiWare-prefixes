open import PiWare.Atom using (Atomic)
open import PiWare.Gates using (Gates)

module PiWarePrefixes.Circuit.Context.Core {At : Atomic} (Gt : Gates At) where

open import Data.Nat using (ℕ; suc; _+_; _⊔_)
open import Data.String using (String)
open import PiWare.Circuit.Core Gt

-- Indices describe the hole, parameters describe the full circuit when the hole is plugged.

data Cxt' {csₓ : CombSeq} (iₓ oₓ : ℕ) : {cs : CombSeq} → ℕ → ℕ → Set where
    ● : Cxt' {csₓ} iₓ oₓ {csₓ} iₓ oₓ
    DelayLoop● : ∀ {i o l} → Cxt' {csₓ} iₓ oₓ {Comb} (i + l) (o + l) → Cxt' {csₓ} iₓ oₓ {Seq} i o
    _⟫'●_ : ∀ {cs i m o} → ℂ' {cs} i m → Cxt' {csₓ} iₓ oₓ {cs} m o → Cxt' {csₓ} iₓ oₓ {cs} i o
    _●⟫'_ : ∀ {cs i m o} → Cxt' {csₓ} iₓ oₓ {cs} i m → ℂ' {cs} m o → Cxt' {csₓ} iₓ oₓ {cs} i o
    _|'●_ : ∀ {cs i₁ o₁ i₂ o₂} → ℂ' {cs} i₁ o₁ → Cxt' {csₓ} iₓ oₓ {cs} i₂ o₂ → Cxt' {csₓ} iₓ oₓ {cs} (i₁ + i₂) (o₁ + o₂)
    _●|'_ : ∀ {cs i₁ o₁ i₂ o₂} → Cxt' {csₓ} iₓ oₓ {cs} i₁ o₁ → ℂ' {cs} i₂ o₂ → Cxt' {csₓ} iₓ oₓ {cs} (i₁ + i₂) (o₁ + o₂)
    _|+'●_ : ∀ {cs i₁ i₂ o} → ℂ' {cs} i₁ o → Cxt' {csₓ} iₓ oₓ {cs} i₂ o → Cxt' {csₓ} iₓ oₓ {cs} (suc (i₁ ⊔ i₂)) o
    _●|+'_ : ∀ {cs i₁ i₂ o} → Cxt' {csₓ} iₓ oₓ {cs} i₁ o → ℂ' {cs} i₂ o → Cxt' {csₓ} iₓ oₓ {cs} (suc (i₁ ⊔ i₂)) o
    _●Named_ : ∀ {cs i o} → Cxt' {csₓ} iₓ oₓ {cs} i o → String → Cxt' {csₓ} iₓ oₓ {cs} i o

infixr 5 _|'●_  _●|'_
infixr 5 _|+'●_ _●|+'_
infixl 4 _⟫'●_  _●⟫'_

plugCxt' : ∀ {csₓ iₓ oₓ cs i o} → Cxt' {csₓ} iₓ oₓ {cs} i o → ℂ' {csₓ} iₓ oₓ → ℂ' {cs} i o
plugCxt' ●                cₓ = cₓ
plugCxt' (DelayLoop● cxt) cₓ = DelayLoop (plugCxt' cxt cₓ)
plugCxt' (x    ⟫'● cxt)   cₓ = x ⟫' (plugCxt' cxt cₓ)
plugCxt' (cxt ●⟫'    x)   cₓ = (plugCxt' cxt cₓ) ⟫' x
plugCxt' (x    |'● cxt)   cₓ = x |' (plugCxt' cxt cₓ)
plugCxt' (cxt ●|'    x)   cₓ = (plugCxt' cxt cₓ) |' x
plugCxt' (x    |+'● cxt)  cₓ = x |+' (plugCxt' cxt cₓ)
plugCxt' (cxt ●|+'    x)  cₓ = (plugCxt' cxt cₓ) |+' x
plugCxt' (cxt ●Named s)   cₓ = (plugCxt' cxt cₓ) Named s



---- Paths

-- open import Function
-- open import Data.Empty
-- open import Data.Maybe
-- open import Data.Product
-- open import Data.Sum
-- open import Data.Unit
-- open import Data.Fin using (Fin; #_)

-- data Direction : Fin 3 → Set where
--   down : Direction (# 1)
--   left : Direction (# 2)
--   right : Direction (# 2)

-- holeCount : ∀ {cs i o} → ℂ' {cs} i o → Fin 3
-- holeCount Nil = # 0
-- holeCount (Gate g#) = # 0
-- holeCount (DelayLoop c) = # 1 
-- holeCount (Plug f) = # 0
-- holeCount (c ⟫' c₁) = # 2
-- holeCount (c |' c₁) = # 2
-- holeCount (c |+' c₁) = # 2
-- holeCount (c Named x) = # 1

-- DirectionIn : ∀ {cs i o} → ℂ' {cs} i o → Set
-- DirectionIn = Direction ∘ holeCount

-- Someℂ' : Set
-- Someℂ' = Σ[ cs ∈ CombSeq ] Σ[ i ∈ ℕ ] Σ[ o ∈ ℕ ] (ℂ' {cs} i o)

-- step : ∀ {cs₁ i₁ o₁} → (c : ℂ' {cs₁} i₁ o₁) → DirectionIn c → Someℂ'
-- step Nil ()
-- step (Gate g#) ()
-- step (DelayLoop {i} {o} {l} c) down = _ , _ , _ , c
-- step (Plug f) ()
-- step (c₁ ⟫' c₂) left = _ , _ , _ , c₁
-- step (c₁ ⟫' c₂) right = _ , _ , _ , c₂
-- step (c₁ |' c₂) left = _ , _ , _ , c₁
-- step (c₁ |' c₂) right = _ , _ , _ , c₂
-- step (c₁ |+' c₂) left = _ , _ , _ , c₁
-- step (c₁ |+' c₂) right = _ , _ , _ , c₂
-- step (c Named s) down = _ , _ , _ , c

-- -- A path from c to cₓ
-- data Path {cs : CombSeq} {i o : ℕ} (c : ℂ' {cs} i o) : ∀ {csₓ iₓ oₓ} (cₓ : ℂ' {csₓ} iₓ oₓ) → Set where
--   here : Path c c
--   _▷_ : (dir : DirectionIn c) →
--         let (cs₁ , i₁ , o₁ , c₁) = step c dir in
--         ∀ {csₓ iₓ oₓ} {cₓ : ℂ' {csₓ} iₓ oₓ} →
--         Path c₁ cₓ → Path c cₓ

-- makeCxt' : ∀ {cs i o} (c : ℂ' {cs} i o) →
--            ∀ {csₓ iₓ oₓ} {cₓ : ℂ' {csₓ} iₓ oₓ} → Path c cₓ → Cxt' {csₓ} iₓ oₓ {cs} i o
-- makeCxt' c here = ●
-- makeCxt' Nil (() ▷ path)
-- makeCxt' (Gate g#) (() ▷ path)
-- makeCxt' (DelayLoop c) (down ▷ path) = DelayLoop● (makeCxt' c path)
-- makeCxt' (Plug f) (() ▷ path)
-- makeCxt' (c₁ ⟫' c₂) (left ▷ path) = makeCxt' c₁ path ●⟫' c₂
-- makeCxt' (c₁ ⟫' c₂) (right ▷ path) = c₁ ⟫'● makeCxt' c₂ path
-- makeCxt' (c₁ |' c₂) (left ▷ path) = makeCxt' c₁ path ●|' c₂
-- makeCxt' (c₁ |' c₂) (right ▷ path) = c₁ |'● makeCxt' c₂ path
-- makeCxt' (c₁ |+' c₂) (left ▷ path) = makeCxt' c₁ path ●|+' c₂
-- makeCxt' (c₁ |+' c₂) (right ▷ path) = c₁ |+'● makeCxt' c₂ path
-- makeCxt' (c Named s) (down ▷ path) = (makeCxt' c path) ●Named s


-- -- record Location {cs : CombSeq} (i o : ℕ) : Set where
-- --   constructor location
-- --   field
-- --     {csₓ} : CombSeq
-- --     {iₓ} : ℕ
-- --     {oₓ} : ℕ
-- --     circuit : ℂ' {csₓ} iₓ oₓ
-- --     cxt : Cxt' {csₓ} iₓ oₓ {cs} i o
-- -- start : ∀ {cs i o} → ℂ' {cs} i o → Location {cs} i o
-- -- start c = location c ●
