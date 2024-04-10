{-# OPTIONS --with-K #-}

open import Relation.Binary using (Irreflexive; Decidable; Symmetric; Irrelevant)
open import Data.Nat using (ℕ)
open import Data.Nat.Base using (_/_)
open import Data.Fin using (Fin)
open import Agda.Builtin.Bool using (Bool)
open import Relation.Nullary using (Dec)
open import Data.Fin.Base using (toℕ; fromℕ; inject₁; cast)
open import Data.Vec.Base using (Vec; tabulate; sum; allFin; count)
open import Relation.Binary.PropositionalEquality using (_≡_)

open Dec

module Graphs where

record Graph : Set₁ where
  field
    V : Set
    E : V → V → Set

    isDecidableE   : Decidable E
    isIrreflexiveE : Irreflexive _≡_ E
    isSymmetricE   : Symmetric E

  Eᵇ : V → V → Bool
  Eᵇ u v =  isDecidableE u v .does

record EnumeratedFiniteGraph : Set₁ where
  field
    n : ℕ                         -- ( |V| , V : Fin n)
    FiniteE : Fin n → Fin n → Set

    isDecidableE   : Decidable FiniteE
    isIrreflexiveE : Irreflexive _≡_ FiniteE
    isSymmetricE   : Symmetric FiniteE

  FiniteEᵇ : Fin n → Fin n → Bool
  FiniteEᵇ u v =  isDecidableE u v .does

  deg : Fin n → ℕ
  deg u = count (isDecidableE u) (allFin n)

  2|E| : ℕ
  2|E| = sum (tabulate {n} deg)

  |E| : ℕ
  |E| = 2|E| / 2



