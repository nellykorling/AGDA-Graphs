{-# OPTIONS --with-K #-}

open import Data.Nat using (ℕ)
open import Data.Nat.Base using (_+_; _∸_; _*_; _/_)
open import Data.Nat.DivMod using (m*n/n≡m)
open import Data.Fin using (Fin)
open import Data.Fin.Properties using (_≟_)
open import Data.Vec.Base using (tabulate; allFin; count; sum; replicate)
open import Relation.Nullary.Decidable.Core using (_⊎-dec_; _×-dec_)
open import Relation.Binary.PropositionalEquality using (_≡_; cong)
open Relation.Binary.PropositionalEquality.≡-Reasoning
open import Graphs using (EnumeratedFiniteGraph)
open import Cycles using (_minus1; cycleDecidable; 3+_cycle; ¬j≡i-1×i≡j-1)
open import countLemmas using (∀x⊥-count0; count1; countf1; count⊎)
open import MiscLemmas using (sumReplicate; tabulate-replicate)
open EnumeratedFiniteGraph


degCycleN : ∀ {n : ℕ} (u : Fin (3 + n)) → deg (3+ n cycle) u ≡ 2
degCycleN {n} u = let P = λ v → (v ≟ (u minus1)) in
                let Q = λ v → (u ≟ (v minus1)) in
                let P⊎Q = λ v → ((v ≟ u minus1) ⊎-dec (u ≟ v minus1)) in
                let P×Q = λ v → ((v ≟ u minus1) ×-dec (u ≟ v minus1)) in
                let allFin = allFin (3 + n) in
                 begin
                   deg (3+ n cycle) u
                 ≡⟨⟩
                   count (cycleDecidable n u) allFin
                 ≡⟨⟩
                   count P⊎Q allFin
                 ≡⟨ count⊎ P Q allFin ⟩
                   count P allFin + count Q allFin ∸ count P×Q allFin
                 ≡⟨ cong (λ x → x + count Q allFin ∸ count P×Q allFin) (count1 (3 + n) (u minus1)) ⟩
                   1 + count Q allFin ∸ count P×Q allFin
                 ≡⟨ cong (λ x → 1 + x ∸ count P×Q allFin) (countf1 n u) ⟩
                   1 + 1 ∸ count P×Q allFin
                 ≡⟨ cong (2 ∸_) (∀x⊥-count0 P×Q allFin (¬j≡i-1×i≡j-1 n u)) ⟩ 
                   2 
                 ∎


cycle2|E| : ∀ (n : ℕ) → 2|E| (3+ n cycle) ≡ (3 + n) * 2
cycle2|E| n = begin
               2|E| (3+ n cycle)
             ≡⟨⟩
               sum (tabulate (deg (3+ n cycle)))
             ≡⟨ cong sum (tabulate-replicate (3 + n) 2 (deg (3+ n cycle)) degCycleN) ⟩
               sum (replicate (3 + n) 2)
             ≡⟨ sumReplicate (3 + n) 2 ⟩ 
               (3 + n) * 2
             ∎


cycle|E| : ∀ (n : ℕ) → |E| (3+ n cycle) ≡ (3 + n)
cycle|E| n = begin
                |E| (3+ n cycle)
              ≡⟨⟩
                2|E| (3+ n cycle) / 2
              ≡⟨ cong (_/ 2) (cycle2|E| n) ⟩
                (3 + n) * 2 / 2
              ≡⟨ m*n/n≡m (3 + n) 2 ⟩
                3 + n
              ∎
