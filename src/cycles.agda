{-# OPTIONS --with-K #-}

open import Data.Nat using (ℕ)
open import Data.Nat.Base using (_/_; _*_)
open import Data.Nat.Properties using (1+n≢n; 1+n≢0)
open import Data.Fin using (Fin)
open import Agda.Builtin.Bool using (Bool)
open import Data.Empty using (⊥)
open import Relation.Nullary using (Dec; yes; no)
open import Data.Fin.Base using (toℕ; fromℕ; inject₁; cast)
open import Data.Fin.Properties using (toℕ-inject₁; toℕ-fromℕ; _≟_)
open import Data.Vec.Base using (Vec; tabulate; sum; allFin; count)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Function.Base using (id)
open import Relation.Nullary.Negation.Core using (_¬-⊎_)
open import Graphs
open Dec
open EnumeratedFiniteGraph



cycleE : (n : ℕ) (i j : Fin n) → Set
cycleE (ℕ.suc ℕ.zero) Fin.zero Fin.zero = ⊥
cycleE (ℕ.suc (ℕ.suc n₁)) Fin.zero Fin.zero = ⊥
cycleE (ℕ.suc (ℕ.suc n₁)) Fin.zero (Fin.suc j)  = (j ≡ Fin.zero) ⊎ (j ≡ fromℕ n₁)
cycleE (ℕ.suc (ℕ.suc n₁)) (Fin.suc i) Fin.zero = (i ≡ Fin.zero) ⊎ (i ≡ fromℕ n₁)
cycleE (ℕ.suc (ℕ.suc n₁)) (Fin.suc i) (Fin.suc j) = (inject₁ i ≡ Fin.suc j) ⊎ (Fin.suc i ≡ inject₁ j)



cycleIrr : ∀ (n : ℕ) (i j : Fin n) → i ≡ j → cycleE n i j → ⊥
cycleIrr (ℕ.suc ℕ.zero) Fin.zero Fin.zero i≡j = id 
cycleIrr (ℕ.suc (ℕ.suc n₁)) Fin.zero Fin.zero i≡j = id
cycleIrr (ℕ.suc (ℕ.suc n₁)) (Fin.suc i) (Fin.suc j) i≡j (inj₁ x) = 1+n≢n {toℕ i} (trans (cong toℕ (trans (i≡j) (sym x))) (toℕ-inject₁ i))
cycleIrr (ℕ.suc (ℕ.suc n₁)) (Fin.suc i) (Fin.suc j) i≡j (inj₂ y) = 1+n≢n {toℕ j} (trans (cong toℕ (trans (sym i≡j) (y))) (toℕ-inject₁ j))



cycleSym : ∀ (n : ℕ) (i j : Fin n) → cycleE n i j → cycleE n j i
cycleSym (ℕ.suc ℕ.zero) Fin.zero Fin.zero ()
cycleSym (ℕ.suc ℕ.zero) Fin.zero (Fin.suc ()) e
cycleSym (ℕ.suc ℕ.zero) (Fin.suc ()) Fin.zero e
cycleSym (ℕ.suc ℕ.zero) (Fin.suc ()) (Fin.suc j) e
cycleSym (ℕ.suc (ℕ.suc n₁)) Fin.zero (Fin.suc j) e = e 
cycleSym (ℕ.suc (ℕ.suc n₁)) (Fin.suc i) Fin.zero e = e
cycleSym (ℕ.suc (ℕ.suc n₁)) (Fin.suc i) (Fin.suc j) (inj₁ x) = inj₂ (sym x)
cycleSym (ℕ.suc (ℕ.suc n₁)) (Fin.suc i) (Fin.suc j) (inj₂ y) = inj₁ (sym y)



cycleDec : ∀ (n : ℕ) (i j : Fin n) → Dec (cycleE n i j)
cycleDec (ℕ.suc ℕ.zero) Fin.zero Fin.zero = no id
cycleDec (ℕ.suc (ℕ.suc n₁)) Fin.zero Fin.zero = no id

cycleDec (ℕ.suc (ℕ.suc n₁)) Fin.zero (Fin.suc Fin.zero) = yes (inj₁ refl)
cycleDec (ℕ.suc (ℕ.suc n₁)) Fin.zero (Fin.suc (Fin.suc j)) with Fin.suc j ≟ fromℕ n₁
... | (yes j≡n) = yes (inj₂ j≡n)
... | (no j≢n) = no ((λ x → 1+n≢0 (cong toℕ x)) ¬-⊎ j≢n)

cycleDec (ℕ.suc (ℕ.suc n₁)) (Fin.suc Fin.zero) Fin.zero = yes (inj₁ refl)
cycleDec (ℕ.suc (ℕ.suc n₁)) (Fin.suc (Fin.suc i)) Fin.zero with Fin.suc i ≟ fromℕ n₁
... | (yes i≡n) = yes (inj₂ i≡n)
... | (no i≢n) = no ((λ x →  1+n≢0 (cong toℕ x)) ¬-⊎ i≢n)

cycleDec (ℕ.suc (ℕ.suc n₁)) (Fin.suc i) (Fin.suc j) with (inject₁ i ≟ Fin.suc j) | (Fin.suc i ≟ inject₁ j) 
... | (yes e) | _       = yes (inj₁ e)
... | _       | (yes f) = yes (inj₂ f)
... | (no ¬e) | (no ¬f) = no (¬e ¬-⊎ ¬f)



cycle : ℕ → EnumeratedFiniteGraph
cycle n = record
           { n = n
           ; FiniteE = cycleE n
           ; isDecidableE = cycleDec n
           ; isIrreflexiveE = cycleIrr n {!!} {!!}
           ; isSymmetricE = cycleSym n {!!} {!!}
           }



degCycleN : ∀ (n : ℕ) (u : Fin n) → deg (cycle n) u ≡ 2
degCycleN n u = {!!} 

cycle|E| : ∀ (n : ℕ) → 2|E| (cycle n) ≡ n * 2
cycle|E|  ℕ.zero    = refl        
cycle|E| (ℕ.suc n₁) = {!!} 




-- deg (cycle 5) Fin.zero 

{- deg : Fin n → ℕ
   deg u = countᵇ (FiniteEᵇ u) (allFin n)

   2|E| : ℕ
   2|E| = sum (tabulate {n} deg) -}


