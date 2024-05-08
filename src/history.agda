{-# OPTIONS --with-K #-}


open import Data.Nat using (ℕ; _+_)
open import Data.Fin using (Fin)
open import Data.Fin.Base using (fromℕ; inject₁)
open import Data.Fin.Properties using (_≟_; 0≢1+n)
open import Data.Empty using (⊥)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Nullary.Negation.Core using (_¬-⊎_)
open import Relation.Nullary.Decidable.Core using (_⊎-dec_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)
open import Cycles using (cycleE; cycleIrreflexive)


data cycleE' : {n : ℕ} {i j : Fin n} → Set where

  sucRight : ∀ {n : ℕ} {i : Fin n} → cycleE' {ℕ.suc n} {inject₁ i} {Fin.suc i}
  sucLeft :  ∀ {n : ℕ} {i : Fin n} → cycleE' {ℕ.suc n} {Fin.suc i} {inject₁ i}
  zeroLast : ∀ {n : ℕ}             → cycleE' {ℕ.suc (ℕ.suc n)} {Fin.zero} {fromℕ (ℕ.suc n)}
  lastZero : ∀ {n : ℕ}             → cycleE' {ℕ.suc (ℕ.suc n)} {fromℕ (ℕ.suc n)} {Fin.zero}


cycleE'' : (n : ℕ) (i j : Fin n) → Set
cycleE'' (ℕ.suc ℕ.zero) Fin.zero Fin.zero = ⊥
cycleE'' (ℕ.suc (ℕ.suc n₁)) Fin.zero Fin.zero = ⊥
cycleE'' (ℕ.suc (ℕ.suc n₁)) Fin.zero (Fin.suc j)  = (j ≡ Fin.zero) ⊎ (j ≡ fromℕ n₁)
cycleE'' (ℕ.suc (ℕ.suc n₁)) (Fin.suc i) Fin.zero = (i ≡ Fin.zero) ⊎ (i ≡ fromℕ n₁)
cycleE'' (ℕ.suc (ℕ.suc n₁)) (Fin.suc i) (Fin.suc j) =
  (inject₁ i ≡ Fin.suc j) ⊎ (Fin.suc i ≡ inject₁ j)


cycleSym' : ∀ (n : ℕ) (i j : Fin (3 + n)) → cycleE n i j → cycleE n j i
cycleSym' ℕ.zero Fin.zero (Fin.suc j) (inj₁ x) = inj₂ x
cycleSym' ℕ.zero Fin.zero (Fin.suc j) (inj₂ y) = inj₁ y
cycleSym' ℕ.zero (Fin.suc i) Fin.zero (inj₁ x) = inj₂ x
cycleSym' ℕ.zero (Fin.suc i) Fin.zero (inj₂ y) = inj₁ y
cycleSym' ℕ.zero (Fin.suc i) (Fin.suc j) (inj₁ x) = inj₂ x
cycleSym' ℕ.zero (Fin.suc i) (Fin.suc j) (inj₂ y) = inj₁ y
cycleSym' (ℕ.suc n₁) Fin.zero (Fin.suc j) (inj₁ x) = inj₂ x
cycleSym' (ℕ.suc n₁) Fin.zero (Fin.suc j) (inj₂ y) = inj₁ y
cycleSym' (ℕ.suc n₁) (Fin.suc i) Fin.zero (inj₁ x) = inj₂ x
cycleSym' (ℕ.suc n₁) (Fin.suc i) Fin.zero (inj₂ y) = inj₁ y
cycleSym' (ℕ.suc n₁) (Fin.suc i) (Fin.suc j) (inj₁ x) = inj₂ x
cycleSym' (ℕ.suc n₁) (Fin.suc i) (Fin.suc j) (inj₂ y) = inj₁ y


cycleDec' : ∀ (n : ℕ) (i j : Fin (3 + n)) → Dec (cycleE n i j)
cycleDec' ℕ.zero Fin.zero Fin.zero = no (cycleIrreflexive ℕ.zero Fin.zero Fin.zero refl)
cycleDec' ℕ.zero Fin.zero (Fin.suc Fin.zero) = yes (inj₂ refl)
cycleDec' ℕ.zero Fin.zero (Fin.suc (Fin.suc j)) with (Fin.suc (Fin.suc j)) ≟ fromℕ 2
... | (yes 2+j≡n) = yes (inj₁ 2+j≡n)
... | (no 2+j≢n) = no (2+j≢n ¬-⊎ 0≢1+n)

cycleDec' ℕ.zero (Fin.suc Fin.zero) Fin.zero = yes (inj₁ refl)
cycleDec' ℕ.zero (Fin.suc (Fin.suc i)) Fin.zero with (Fin.suc (Fin.suc i)) ≟ fromℕ 2
... | (yes 2+j≡n) = yes (inj₂ 2+j≡n)
... | (no 2+j≢n) = no (0≢1+n ¬-⊎ 2+j≢n) 

cycleDec' ℕ.zero (Fin.suc i) (Fin.suc j) with (Fin.suc j ≟ inject₁ i) ⊎-dec (Fin.suc i ≟ inject₁ j)
... | 1+j≡i⊎1+i≡j = 1+j≡i⊎1+i≡j

cycleDec' (ℕ.suc n₁) Fin.zero Fin.zero = no (cycleIrreflexive (ℕ.suc n₁) Fin.zero Fin.zero refl)
cycleDec' (ℕ.suc n₁) Fin.zero (Fin.suc Fin.zero) = yes (inj₂ refl)
cycleDec' (ℕ.suc n₁) Fin.zero (Fin.suc (Fin.suc j)) with (Fin.suc (Fin.suc j)) ≟ fromℕ (3 + n₁)
... | (yes 2+j≡n) = yes (inj₁ 2+j≡n)
... | (no 2+j≢n) = no (2+j≢n ¬-⊎ 0≢1+n)

cycleDec' (ℕ.suc n₁) (Fin.suc Fin.zero) Fin.zero = yes (inj₁ refl)
cycleDec' (ℕ.suc n₁) (Fin.suc (Fin.suc i)) Fin.zero with (Fin.suc (Fin.suc i)) ≟ fromℕ (3 + n₁)
... | (yes 2+j≡n) = yes (inj₂ 2+j≡n)
... | (no 2+j≢n) = no (0≢1+n ¬-⊎ 2+j≢n)

cycleDec' (ℕ.suc n₁) (Fin.suc i) (Fin.suc j) with (Fin.suc j ≟ inject₁ i) ⊎-dec (Fin.suc i ≟ inject₁ j)
... | 1+j≡i⊎1+i≡j = 1+j≡i⊎1+i≡j
