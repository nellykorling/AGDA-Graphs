{-# OPTIONS --with-K #-}

open import Data.Nat using (ℕ; _+_)
open import Data.Nat.Properties using (1+n≢n)
open import Data.Fin using (Fin)
open import Data.Empty using (⊥)
open import Relation.Nullary using (Dec; yes; no)
open import Data.Fin.Base using (toℕ; fromℕ; inject₁)
open import Data.Fin.Properties using (toℕ-inject₁; _≟_; 0≢1+n)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂; swap)
open import Data.Product.Base using (_×_; _,_)
open import Relation.Nullary.Negation.Core using (_¬-⊎_)
open import Relation.Nullary.Decidable.Core using (_⊎-dec_)
open import Function.Base using (_∘_)
open import Graphs
open import miscLemmas using (suc≢inject₁)
open Dec
open EnumeratedFiniteGraph


module Cycles where


infix 6 _minus1

_minus1 : ∀ {n : ℕ} (i : Fin (3 + n)) → Fin (3 + n)
_minus1 {n} Fin.zero = fromℕ (2 + n)
_minus1 (Fin.suc i) = inject₁ i


cycleE : ∀ (n : ℕ) (i j : Fin (3 + n)) → Set
cycleE n i j = (j ≡ (i minus1)) ⊎ (i ≡ (j minus1))





cycleIrr : ∀ (n : ℕ) (i j : Fin (3 + n)) → i ≡ j → cycleE n i j → ⊥
cycleIrr ℕ.zero Fin.zero Fin.zero 0≡0 (inj₁ ())
cycleIrr ℕ.zero Fin.zero Fin.zero 0≡0 (inj₂ ())
cycleIrr ℕ.zero (Fin.suc i) (Fin.suc j) 1+i≡1+j (inj₁ x) = suc≢inject₁ (trans 1+i≡1+j x)
cycleIrr ℕ.zero (Fin.suc i) (Fin.suc j) 1+i≡1+j (inj₂ y) = suc≢inject₁ (trans (sym 1+i≡1+j) y)
cycleIrr (ℕ.suc n₁) Fin.zero Fin.zero 0≡0 (inj₁ ())
cycleIrr (ℕ.suc n₁) Fin.zero Fin.zero 0≡0 (inj₂ ())
cycleIrr (ℕ.suc n₁) (Fin.suc i) (Fin.suc j) 1+i≡1+j (inj₁ x) = suc≢inject₁ (trans 1+i≡1+j x)
cycleIrr (ℕ.suc n₁) (Fin.suc i) (Fin.suc j) 1+i≡1+j (inj₂ y) = suc≢inject₁ (trans (sym 1+i≡1+j) y)


cycleSym : ∀ (n : ℕ) (i j : Fin (3 + n)) → cycleE n i j → cycleE n j i
cycleSym ℕ.zero Fin.zero (Fin.suc j) (inj₁ x) = inj₂ x
cycleSym ℕ.zero Fin.zero (Fin.suc j) (inj₂ y) = inj₁ y
cycleSym ℕ.zero (Fin.suc i) Fin.zero (inj₁ x) = inj₂ x
cycleSym ℕ.zero (Fin.suc i) Fin.zero (inj₂ y) = inj₁ y
cycleSym ℕ.zero (Fin.suc i) (Fin.suc j) (inj₁ x) = inj₂ x
cycleSym ℕ.zero (Fin.suc i) (Fin.suc j) (inj₂ y) = inj₁ y
cycleSym (ℕ.suc n₁) Fin.zero (Fin.suc j) (inj₁ x) = inj₂ x
cycleSym (ℕ.suc n₁) Fin.zero (Fin.suc j) (inj₂ y) = inj₁ y
cycleSym (ℕ.suc n₁) (Fin.suc i) Fin.zero (inj₁ x) = inj₂ x
cycleSym (ℕ.suc n₁) (Fin.suc i) Fin.zero (inj₂ y) = inj₁ y
cycleSym (ℕ.suc n₁) (Fin.suc i) (Fin.suc j) (inj₁ x) = inj₂ x
cycleSym (ℕ.suc n₁) (Fin.suc i) (Fin.suc j) (inj₂ y) = inj₁ y
 

cycleSym' : ∀ (n : ℕ) (i j : Fin (3 + n)) → cycleE n i j → cycleE n j i
cycleSym' n i j = swap 


cycleDec : ∀ (n : ℕ) (i j : Fin (3 + n)) → Dec (cycleE n i j)
cycleDec ℕ.zero Fin.zero Fin.zero = no (cycleIrr ℕ.zero Fin.zero Fin.zero refl)
cycleDec ℕ.zero Fin.zero (Fin.suc Fin.zero) = yes (inj₂ refl)
cycleDec ℕ.zero Fin.zero (Fin.suc (Fin.suc j)) with (Fin.suc (Fin.suc j)) ≟ fromℕ 2
... | (yes 2+j≡n) = yes (inj₁ 2+j≡n)
... | (no 2+j≢n) = no (2+j≢n ¬-⊎ 0≢1+n)

cycleDec ℕ.zero (Fin.suc Fin.zero) Fin.zero = yes (inj₁ refl)
cycleDec ℕ.zero (Fin.suc (Fin.suc i)) Fin.zero with (Fin.suc (Fin.suc i)) ≟ fromℕ 2
... | (yes 2+j≡n) = yes (inj₂ 2+j≡n)
... | (no 2+j≢n) = no (0≢1+n ¬-⊎ 2+j≢n) 

cycleDec ℕ.zero (Fin.suc i) (Fin.suc j) with (Fin.suc j ≟ inject₁ i) ⊎-dec (Fin.suc i ≟ inject₁ j)
... | 1+j≡i⊎1+i≡j = 1+j≡i⊎1+i≡j

cycleDec (ℕ.suc n₁) Fin.zero Fin.zero = no (cycleIrr (ℕ.suc n₁) Fin.zero Fin.zero refl)
cycleDec (ℕ.suc n₁) Fin.zero (Fin.suc Fin.zero) = yes (inj₂ refl)
cycleDec (ℕ.suc n₁) Fin.zero (Fin.suc (Fin.suc j)) with (Fin.suc (Fin.suc j)) ≟ fromℕ (3 + n₁)
... | (yes 2+j≡n) = yes (inj₁ 2+j≡n)
... | (no 2+j≢n) = no (2+j≢n ¬-⊎ 0≢1+n)

cycleDec (ℕ.suc n₁) (Fin.suc Fin.zero) Fin.zero = yes (inj₁ refl)
cycleDec (ℕ.suc n₁) (Fin.suc (Fin.suc i)) Fin.zero with (Fin.suc (Fin.suc i)) ≟ fromℕ (3 + n₁)
... | (yes 2+j≡n) = yes (inj₂ 2+j≡n)
... | (no 2+j≢n) = no (0≢1+n ¬-⊎ 2+j≢n)

cycleDec (ℕ.suc n₁) (Fin.suc i) (Fin.suc j) with (Fin.suc j ≟ inject₁ i) ⊎-dec (Fin.suc i ≟ inject₁ j)
... | 1+j≡i⊎1+i≡j = 1+j≡i⊎1+i≡j


cycleDec' : ∀ (n : ℕ) (i j : Fin (3 + n)) → Dec (cycleE n i j)
cycleDec' n i j = (j ≟ (i minus1)) ⊎-dec (i ≟ (j minus1))


3+_cycle : ℕ → EnumeratedFiniteGraph
3+ n cycle = record
           { n = 3 + n
           ; FiniteE = cycleE n
           ; isIrreflexiveE = cycleIrr n _ _
           ; isSymmetricE = cycleSym' n _ _
           ; isDecidableE = cycleDec' n
           }



