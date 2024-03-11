

open import Relation.Binary using (Irreflexive; Decidable; Symmetric; Irrelevant)
open import Data.Nat using (ℕ)
open import Data.Nat.Base using (_/_)
open import Data.Fin using (Fin)
open import Relation.Binary.PropositionalEquality.Core using (_≡_)
open import Agda.Builtin.Bool using (Bool)
open import Relation.Nullary using (Dec)
open import Data.Fin.Base using (toℕ)
open import Data.Fin.Subset using (Subset)
open import Data.Vec.Base using (Vec; tabulate; sum; allFin; countᵇ)

open Dec

record Graph : Set₁ where
  field
    V : Set
    E : V → V → Set

    isDecidableE : Decidable E
    isIrreflexiveE : Irreflexive _≡_ E
    isIrrelevantE : Irrelevant E
    isSymmetricE : Symmetric E

  Eᵇ : V → V → Bool
  Eᵇ u v =  isDecidableE u v .does

open Graph

record EnumeratedFiniteGraph : Set₁ where
  field
    n : ℕ                          -- ( |V| , V : Fin n)
    FiniteE : Fin n → Fin n → Set

    isDecidableFiniteE : Decidable FiniteE
    isIrreflexiveFiniteE : Irreflexive _≡_ FiniteE
    isIrrelevantFiniteE : Irrelevant FiniteE
    isSymmetricFiniteE : Symmetric FiniteE

  FiniteEᵇ : Fin n → Fin n → Bool
  FiniteEᵇ u v =  isDecidableFiniteE u v .does

  deg : Fin n → ℕ
  deg u = countᵇ (FiniteEᵇ u) (allFin n)

  |E| : ℕ
  |E| = sum (tabulate {n} deg)
  
open EnumeratedFiniteGraph


