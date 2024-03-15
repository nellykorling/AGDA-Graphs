{-# OPTIONS --with-K #-}

open import Relation.Binary using (Irreflexive; Decidable; Symmetric; Irrelevant)
open import Data.Nat using (ℕ)
open import Data.Nat.Base using (_/_)
open import Data.Nat.Properties using (1+n≢n; 1+n≢0; 0≢1+n; _≟_)
open import Data.Fin using (Fin)
open import Relation.Binary.PropositionalEquality.Core using (_≡_)
open import Agda.Builtin.Bool using (Bool)
open import Data.Empty using (⊥)
open import Relation.Nullary using (Dec; yes; no)
open import Data.Fin.Base using (toℕ; fromℕ; inject₁; cast)
open import Data.Fin.Properties using (toℕ-inject₁; toℕ-fromℕ)
open import Data.Fin.Subset using (Subset)
open import Data.Vec.Base using (Vec; tabulate; sum; allFin; countᵇ)
open import Relation.Binary.PropositionalEquality as P using (_≡_; refl; sym; trans; cong)

open Dec

record Graph : Set₁ where
  field
    V : Set
    E : V → V → Set

    isDecidableE   : Decidable E
    isIrreflexiveE : Irreflexive _≡_ E
    isSymmetricE   : Symmetric E
    -- isIrrelevantE : Irrelevant E

  Eᵇ : V → V → Bool
  Eᵇ u v =  isDecidableE u v .does

record EnumeratedFiniteGraph : Set₁ where
  field
    n : ℕ                         -- ( |V| , V : Fin n)
    FiniteE : Fin n → Fin n → Set

    isDecidableE   : Decidable FiniteE
    isIrreflexiveE : Irreflexive _≡_ FiniteE
    isSymmetricE   : Symmetric FiniteE
    -- isIrrelevantE : Irrelevant FiniteE

  FiniteEᵇ : Fin n → Fin n → Bool
  FiniteEᵇ u v =  isDecidableE u v .does

  deg : Fin n → ℕ
  deg u = countᵇ (FiniteEᵇ u) (allFin n)

  |E| : ℕ
  |E| = (sum (tabulate {n} deg)) / 2

open EnumeratedFiniteGraph

data cycleE : (n : ℕ) → Fin n → Fin n → Set where

  sucRight : ∀ (n : ℕ) (i : Fin n) → cycleE (ℕ.suc n) (inject₁ i) (Fin.suc i)
  sucLeft :  ∀ (n : ℕ) (i : Fin n) → cycleE (ℕ.suc n) (Fin.suc i) (inject₁ i)
  zeroLast : ∀ (n : ℕ)             → cycleE (ℕ.suc (ℕ.suc n)) (Fin.zero)        (fromℕ (ℕ.suc n))
  lastZero : ∀ (n : ℕ)             → cycleE (ℕ.suc (ℕ.suc n)) (fromℕ (ℕ.suc n)) (Fin.zero)

cycleIrr : {n : ℕ} → {i j : Fin n} → i ≡ j → cycleE n i j → ⊥
cycleIrr i≡j (sucRight n₁ i) = 1+n≢n {toℕ i} (trans (cong toℕ (sym (i≡j))) (toℕ-inject₁ i))
cycleIrr i≡j (sucLeft n₁ i)  = 1+n≢n {toℕ i} (trans (cong toℕ (i≡j)) (toℕ-inject₁ i))
cycleIrr i≡j (zeroLast n₁)   = 0≢1+n {n₁}    (trans ((cong toℕ (i≡j))) (cong ℕ.suc (toℕ-fromℕ n₁)))
cycleIrr i≡j (lastZero n₁)   = 1+n≢0 {n₁}    (trans (cong ℕ.suc (sym (toℕ-fromℕ n₁))) (cong toℕ (i≡j))) 




cycleDec : (n : ℕ) → (i j : Fin n) → Dec (cycleE n i j)
cycleDec (ℕ.suc ℕ.zero)     Fin.zero Fin.zero = no (cycleIrr refl)

cycleDec (ℕ.suc (ℕ.suc n₁)) Fin.zero Fin.zero = no (cycleIrr refl)
cycleDec (ℕ.suc (ℕ.suc n₁)) Fin.zero (Fin.suc Fin.zero) = yes (sucRight (ℕ.suc n₁) Fin.zero)
cycleDec (ℕ.suc (ℕ.suc n₁)) (Fin.suc Fin.zero) Fin.zero = yes (sucLeft (ℕ.suc n₁) Fin.zero)

cycleDec (ℕ.suc (ℕ.suc n₁)) Fin.zero (Fin.suc (Fin.suc j)) with n₁ ≟ (toℕ j)
... | (yes n≡j) = yes {!zeroLast!}
... | (no  n≢j) = no  {!!}

cycleDec (ℕ.suc (ℕ.suc n₁)) (Fin.suc (Fin.suc i)) Fin.zero with n₁ ≟ (toℕ i)
... | (yes n≡i) = {!!}
... | (no  n≢i) = {!!}

cycleDec (ℕ.suc (ℕ.suc n₁)) (Fin.suc i) (Fin.suc j) = {!!}

cycleSym : {n : ℕ} → {i j : Fin n} → cycleE n i j → cycleE n j i
cycleSym (sucRight n i) = sucLeft  n i
cycleSym (sucLeft  n i) = sucRight n i
cycleSym (zeroLast n)   = lastZero n
cycleSym (lastZero n)   = zeroLast n

cycle : ℕ → EnumeratedFiniteGraph
cycle n = record
           { n = n
           ; FiniteE = cycleE n
           ; isDecidableE = cycleDec n
           ; isIrreflexiveE = cycleIrr 
           ; isSymmetricE = cycleSym
           }


