

open import Relation.Binary using (Irreflexive; Decidable; Symmetric; Irrelevant)
open import Relation.Binary.PropositionalEquality.Core using (_≡_)

record Graph : Set₁ where
  field
    V : Set
    E : V → V → Set

    isIrreflexive : Irreflexive _≡_ E
    isDecidable : Decidable E
    isSymmetric : Symmetric E
    isIrrelevant : Irrelevant E
open Graph







{-

defined in terms of an underlying equality (use propositional identity):
Irreflexive : ∀ {a b ℓ₁ ℓ₂} {A : Set a} {B : Set b} →
              REL A B ℓ₁ → REL A B ℓ₂ → Set _
Irreflexive _≈_ _<_ = ∀ {x y} → x ≈ y → ¬ (x < y)
 

Decidable : ∀ {a b ℓ} {A : Set a} {B : Set b} → REL A B ℓ → Set _
Decidable _∼_ = ∀ x y → Dec (x ∼ y)

Sym : ∀ {a b ℓ₁ ℓ₂} {A : Set a} {B : Set b} →
      REL A B ℓ₁ → REL B A ℓ₂ → Set _
Sym P Q = P ⇒ flip Q

Symmetric : ∀ {a ℓ} {A : Set a} → Rel A ℓ → Set _
Symmetric _∼_ = Sym _∼_ _∼_

Irrelevant : ∀ {a b ℓ} {A : Set a} {B : Set b} → REL A B ℓ → Set _
Irrelevant _∼_ = ∀ {x y} (a : x ∼ y) (b : x ∼ y) → a ≡ b

-}

