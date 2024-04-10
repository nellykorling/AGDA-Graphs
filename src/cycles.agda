{-# OPTIONS --with-K #-}

open import Data.Nat using (ℕ)
open import Data.Nat.Base using (_/_; _*_; _+_; _∸_)
open import Data.Nat.Properties using (1+n≢n; 1+n≢0)
open import Data.Fin using (Fin)
open import Agda.Builtin.Bool using (Bool)
open import Data.Empty using (⊥)
open import Relation.Nullary using (Dec; yes; no)
open import Data.Fin.Base using (toℕ; fromℕ; inject₁; cast; pred)
open import Data.Fin.Properties using (toℕ-inject₁; toℕ-fromℕ; _≟_; 0≢1+n)
open import Data.Vec.Base using (Vec; tabulate; sum; allFin; count)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst; _≢_)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Product.Base using (_×_)
open import Function.Base using (id)
open import Relation.Nullary.Negation.Core using (_¬-⊎_)
open import Relation.Nullary.Decidable.Core using (_⊎-dec_)
open import Function.Bundles using (_⤖_)
open import Relation.Unary using (Pred; Decidable)
open import Level using (Level)
open import Graphs
open Dec
open EnumeratedFiniteGraph

module Cycles where


minus1 : ∀ {n : ℕ} (i : Fin (3 + n)) → Fin (3 + n)
minus1 {n} Fin.zero = fromℕ (2 + n)
minus1 (Fin.suc i) = inject₁ i



cycleE : ∀ (n : ℕ) (i j : Fin (3 + n)) → Set
cycleE n i j = (j ≡ (minus1 i)) ⊎ (i ≡ (minus1 j))



suc≢inject₁ : ∀ {n : ℕ} {i : Fin n} → Fin.suc i ≡ inject₁ i → ⊥
suc≢inject₁ i+1≡i = 1+n≢n (trans (cong toℕ (i+1≡i)) (toℕ-inject₁ _))



cycleIrr : ∀ (n : ℕ) (i j : Fin (3 + n)) → i ≡ j → cycleE n i j → ⊥
cycleIrr ℕ.zero Fin.zero Fin.zero i≡j (inj₁ ())
cycleIrr ℕ.zero Fin.zero Fin.zero i≡j (inj₂ ())
cycleIrr ℕ.zero (Fin.suc i) (Fin.suc j) i≡j (inj₁ x) = suc≢inject₁ (trans i≡j x)
cycleIrr ℕ.zero (Fin.suc i) (Fin.suc j) i≡j (inj₂ y) = suc≢inject₁ (trans (sym i≡j) y)
cycleIrr (ℕ.suc n₁) Fin.zero Fin.zero i≡j (inj₁ ())
cycleIrr (ℕ.suc n₁) Fin.zero Fin.zero i≡j (inj₂ ())
cycleIrr (ℕ.suc n₁) (Fin.suc i) (Fin.suc j) i≡j (inj₁ x) = suc≢inject₁ (trans i≡j x)
cycleIrr (ℕ.suc n₁) (Fin.suc i) (Fin.suc j) i≡j (inj₂ y) = suc≢inject₁ (trans (sym i≡j) y)



cycleSym : ∀ (n : ℕ) (i j : Fin (3 + n)) → cycleE n i j → cycleE n j i
cycleSym ℕ.zero Fin.zero (Fin.suc j) (inj₁ x) = inj₂ x
cycleSym ℕ.zero Fin.zero (Fin.suc Fin.zero) (inj₂ y) = inj₁ y
cycleSym ℕ.zero (Fin.suc Fin.zero) Fin.zero (inj₁ x) = inj₂ x
cycleSym ℕ.zero (Fin.suc i) Fin.zero (inj₂ y) = inj₁ y
cycleSym ℕ.zero (Fin.suc i) (Fin.suc j) (inj₁ x) = inj₂ x
cycleSym ℕ.zero (Fin.suc i) (Fin.suc j) (inj₂ y) = inj₁ y
cycleSym (ℕ.suc n₁) Fin.zero (Fin.suc j) (inj₁ x) = inj₂ x
cycleSym (ℕ.suc n₁) Fin.zero (Fin.suc j) (inj₂ y) = inj₁ y
cycleSym (ℕ.suc n₁) (Fin.suc i) Fin.zero (inj₁ x) = inj₂ x
cycleSym (ℕ.suc n₁) (Fin.suc i) Fin.zero (inj₂ y) = inj₁ y
cycleSym (ℕ.suc n₁) (Fin.suc i) (Fin.suc j) (inj₁ x) = inj₂ x
cycleSym (ℕ.suc n₁) (Fin.suc i) (Fin.suc j) (inj₂ y) = inj₁ y



cycleDec : ∀ (n : ℕ) (i j : Fin (3 + n)) → Dec (cycleE n i j)
cycleDec ℕ.zero Fin.zero Fin.zero = no (cycleIrr ℕ.zero Fin.zero Fin.zero refl)
cycleDec ℕ.zero Fin.zero (Fin.suc Fin.zero) = yes (inj₂ refl)
cycleDec ℕ.zero Fin.zero (Fin.suc (Fin.suc j)) with (Fin.suc (Fin.suc j)) ≟ fromℕ 2
... | (yes j≡n) = yes (inj₁ j≡n)
... | (no j≢n) = no (j≢n ¬-⊎ 0≢1+n)

cycleDec ℕ.zero (Fin.suc Fin.zero) Fin.zero = yes (inj₁ refl)
cycleDec ℕ.zero (Fin.suc (Fin.suc i)) Fin.zero with (Fin.suc (Fin.suc i)) ≟ fromℕ 2
... | (yes j≡n) = yes (inj₂ j≡n)
... | (no j≢n) = no (0≢1+n ¬-⊎ j≢n)

cycleDec ℕ.zero (Fin.suc i) (Fin.suc j) with (Fin.suc j ≟ inject₁ i) ⊎-dec (Fin.suc i ≟ inject₁ j)
... | i+1⊎j+1 = i+1⊎j+1

cycleDec (ℕ.suc n₁) Fin.zero Fin.zero = no (cycleIrr (ℕ.suc n₁) Fin.zero Fin.zero refl)
cycleDec (ℕ.suc n₁) Fin.zero (Fin.suc Fin.zero) = yes (inj₂ refl)
cycleDec (ℕ.suc n₁) Fin.zero (Fin.suc (Fin.suc j)) with (Fin.suc (Fin.suc j)) ≟ fromℕ (3 + n₁)
... | (yes j≡n) = yes (inj₁ j≡n)
... | (no j≢n) = no (j≢n ¬-⊎ 0≢1+n)

cycleDec (ℕ.suc n₁) (Fin.suc Fin.zero) Fin.zero = yes (inj₁ refl)
cycleDec (ℕ.suc n₁) (Fin.suc (Fin.suc i)) Fin.zero with (Fin.suc (Fin.suc i)) ≟ fromℕ (3 + n₁)
... | (yes j≡n) = yes (inj₂ j≡n)
... | (no j≢n) = no (0≢1+n ¬-⊎ j≢n)

cycleDec (ℕ.suc n₁) (Fin.suc i) (Fin.suc j) with (Fin.suc j ≟ inject₁ i) ⊎-dec (Fin.suc i ≟ inject₁ j)
... | i+1⊎j+1 = i+1⊎j+1



3+_cycle : ℕ → EnumeratedFiniteGraph
3+ n cycle = record
           { n = 3 + n
           ; FiniteE = cycleE n
           ; isDecidableE = cycleDec n
           ; isIrreflexiveE = cycleIrr n _ _
           ; isSymmetricE = cycleSym n _ _
           }



