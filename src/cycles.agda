{-# OPTIONS --with-K #-}


open import Data.Nat using (ℕ; _+_)
open import Data.Fin using (Fin)
open import Data.Fin.Base using (fromℕ; inject₁)
open import Data.Fin.Properties using (_≟_; 0≢1+n)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂; swap)
open import Data.Product.Base using (_×_; _,_)
open import Relation.Nullary using (Dec; ¬_; Irrelevant)
open import Relation.Nullary.Decidable.Core using (_⊎-dec_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)
open import Axiom.UniquenessOfIdentityProofs
open import Graphs using (EnumeratedFiniteGraph)
open import MiscLemmas using (suc≢inject₁; sucsuc≢inject₁inject₁)


module Cycles where


infix 6 _minus1

_minus1 : ∀ {n : ℕ} (i : Fin (3 + n)) → Fin (3 + n)
_minus1 {n} Fin.zero = fromℕ (2 + n)
_minus1 (Fin.suc i) = inject₁ i


cycleE : ∀ (n : ℕ) (i j : Fin (3 + n)) → Set
cycleE n i j = (j ≡ (i minus1)) ⊎ (i ≡ (j minus1))


¬j≡i-1×i≡j-1 : ∀ (n : ℕ) (i j : Fin (3 + n)) → (j ≡ (i minus1) × i ≡ (j minus1)) → ⊥
¬j≡i-1×i≡j-1 ℕ.zero Fin.zero (Fin.suc .(fromℕ 1)) (refl , ())
¬j≡i-1×i≡j-1 ℕ.zero (Fin.suc .(fromℕ 1)) Fin.zero (() , refl)
¬j≡i-1×i≡j-1 ℕ.zero (Fin.suc (Fin.suc i)) (Fin.suc .(inject₁ i)) (refl , snd) = sucsuc≢inject₁inject₁ snd
¬j≡i-1×i≡j-1 (ℕ.suc n₁) Fin.zero (Fin.suc .(fromℕ (ℕ.suc (ℕ.suc n₁)))) (refl , ())
¬j≡i-1×i≡j-1 (ℕ.suc n₁) (Fin.suc .(fromℕ (ℕ.suc (ℕ.suc n₁)))) Fin.zero (() , refl)
¬j≡i-1×i≡j-1 (ℕ.suc n₁) (Fin.suc (Fin.suc i)) (Fin.suc .(inject₁ i)) (refl , snd) = sucsuc≢inject₁inject₁ snd


cycleIrreflexive : ∀ (n : ℕ) (i j : Fin (3 + n)) → i ≡ j → cycleE n i j → ⊥
cycleIrreflexive ℕ.zero Fin.zero Fin.zero 0≡0 (inj₁ ())
cycleIrreflexive ℕ.zero Fin.zero Fin.zero 0≡0 (inj₂ ())
cycleIrreflexive ℕ.zero (Fin.suc i) (Fin.suc j) 1+i≡1+j (inj₁ x) = suc≢inject₁ (trans 1+i≡1+j x)
cycleIrreflexive ℕ.zero (Fin.suc i) (Fin.suc j) 1+i≡1+j (inj₂ y) = suc≢inject₁ (trans (sym 1+i≡1+j) y)
cycleIrreflexive (ℕ.suc n₁) Fin.zero Fin.zero 0≡0 (inj₁ ())
cycleIrreflexive (ℕ.suc n₁) Fin.zero Fin.zero 0≡0 (inj₂ ())
cycleIrreflexive (ℕ.suc n₁) (Fin.suc i) (Fin.suc j) 1+i≡1+j (inj₁ x) = suc≢inject₁ (trans 1+i≡1+j x)
cycleIrreflexive (ℕ.suc n₁) (Fin.suc i) (Fin.suc j) 1+i≡1+j (inj₂ y) = suc≢inject₁ (trans (sym 1+i≡1+j) y)
 

cycleSymmetry : ∀ (n : ℕ) (i j : Fin (3 + n)) → cycleE n i j → cycleE n j i
cycleSymmetry n i j = swap


cycleDecidable : ∀ (n : ℕ) (i j : Fin (3 + n)) → Dec (cycleE n i j)
cycleDecidable n i j = (j ≟ (i minus1)) ⊎-dec (i ≟ (j minus1))


⊎-exclusive-irrelevant : {A B : Set} → Irrelevant A → Irrelevant B → ¬ (A × B) → Irrelevant (A ⊎ B)
⊎-exclusive-irrelevant irrA irrB ¬A×B (inj₁ x) (inj₁ x₁) = cong inj₁ (irrA x x₁)
⊎-exclusive-irrelevant irrA irrB ¬A×B (inj₁ x) (inj₂ y) = ⊥-elim (¬A×B (x , y))
⊎-exclusive-irrelevant irrA irrB ¬A×B (inj₂ y) (inj₁ x) = ⊥-elim (¬A×B (x , y))
⊎-exclusive-irrelevant irrA irrB ¬A×B (inj₂ y) (inj₂ y₁) = cong inj₂ (irrB y y₁)


cycleIrrelevant : ∀ (n : ℕ) (i j : Fin (3 + n)) → Irrelevant (cycleE n i j)
cycleIrrelevant n i j = ⊎-exclusive-irrelevant ≡-irrelevant ≡-irrelevant (¬j≡i-1×i≡j-1 _ _ _)
  where open Decidable⇒UIP (_≟_)


3+_cycle : ℕ → EnumeratedFiniteGraph
3+ n cycle = record
           { n = 3 + n
           ; FiniteE = cycleE n
           ; isIrreflexiveE = cycleIrreflexive n _ _
           ; isSymmetricE = cycleSymmetry n _ _
           ; isDecidableE = cycleDecidable n
           ; isIrrelevant = cycleIrrelevant n _ _
           }
