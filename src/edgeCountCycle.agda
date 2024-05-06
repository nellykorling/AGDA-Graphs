{-# OPTIONS --with-K #-}

open import Data.Nat using (ℕ)
open import Data.Nat.Base using (_/_; _*_; _+_; _∸_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (+-∸-assoc; +-suc)
open import Data.Fin using (Fin)
open import Agda.Builtin.Bool using (Bool; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (Dec; yes; no)
open import Data.Fin.Base using (fromℕ; inject₁)
open import Data.Fin.Properties using (_≟_; 0≢1+n; suc-injective; fromℕ≢inject₁; inject₁-injective)
open import Data.Vec.Base using (Vec; tabulate; allFin; count)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; _≢_)
open import Data.Product.Base using (_×_; proj₁; proj₂; _,_; ∃; ∃-syntax)
open import Function.Base using (id)
open import Relation.Nullary.Decidable.Core using (_⊎-dec_; _×-dec_)
open import Relation.Unary using (Pred; Decidable; _⊆_)
open import Level using (Level)
open import Function.Base using (_∘_)
import Relation.Binary.PropositionalEquality as Eq
open Eq.≡-Reasoning
open import miscLemmas using (last≢inject₁; emptyDec)
open import Graphs using (EnumeratedFiniteGraph)
open import Cycles using (_minus1; cycleE; cycleDec'; 3+_cycle)
open import countLemmas
open Dec
open EnumeratedFiniteGraph
open Vec



degCycleN : ∀ (n : ℕ) (u : Fin (3 + n)) → deg (3+ n cycle) u ≡ 2
degCycleN n u = begin
                   deg (3+ n cycle) u
                 ≡⟨⟩
                   count (cycleDec' n u) (allFin (3 + n))
                 ≡⟨⟩
                   count (λ v → ((v ≟ (u minus1)) ⊎-dec (u ≟ (v minus1)))) (allFin (3 + n)) 
                 ≡⟨ count⊎ (λ v → (v ≟ (u minus1))) (λ v → (u ≟ (v minus1))) (allFin (3 + n))⟩
                   count (λ v → (v ≟ (u minus1))) (allFin (3 + n)) + count (λ v → (u ≟ (v minus1))) (allFin (3 + n)) ∸ count (λ v → ((v ≟ (u minus1)) ×-dec (u ≟ (v minus1)))) (allFin (3 + n))
                 ≡⟨ cong
                     (λ x →
                        x + count (λ v → u ≟ v minus1) (allFin (3 + n)) ∸
                        count (λ v → v ≟ u minus1 ×-dec u ≟ v minus1) (allFin (3 + n)))
                     (count1 (3 + n) (u minus1)) ⟩
                   1 + count (λ v → (u ≟ (v minus1))) (allFin (3 + n)) ∸ count (λ v → ((v ≟ (u minus1)) ×-dec (u ≟ (v minus1)))) (allFin (3 + n))
                 ≡⟨ cong
                     (λ x →
                        1 + x ∸
                        count (λ v → v ≟ u minus1 ×-dec u ≟ v minus1) (allFin (3 + n)))
                     (countf1' n u) ⟩
                   1 + 1 ∸ count (λ v → ((v ≟ (u minus1)) ×-dec (u ≟ (v minus1)))) (allFin (3 + n))
                 ≡⟨ cong (2 ∸_) (countExt (λ v → ((v ≟ (u minus1)) ×-dec (u ≟ (v minus1)))) (λ _ → emptyDec) ((lemma' n u _) , ⊥-elim) (allFin (3 + n)))  ⟩
                   2 ∸ count (λ _ → emptyDec) (allFin (3 + n))
                 ≡⟨ cong (2 ∸_) (count0 (3 + n) (allFin (3 + n))) ⟩     
                   2
                 ∎





cycle|E| : ∀ (n : ℕ) → 2|E| (3+ n cycle) ≡ (3 + n) * 2
cycle|E| n = {!!}


{- deg : Fin n → ℕ
  deg u = count (isDecidableE u) (allFin n)

  2|E| : ℕ
  2|E| = sum (tabulate {n} deg) -}
