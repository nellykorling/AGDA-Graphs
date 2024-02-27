

open import Relation.Binary using (Irreflexive; Decidable; Symmetric)


record Graph : Set₁ where
  field
    V : Set
    E : V → V → Set

    -- isIrreflexive : Irreflexive E
    isDecidable : Decidable E
    isSymmetric : Symmetric E
open Graph

--hi

{-

defined in terms of an underlying equality:
Irreflexive : REL A B ℓ₁ → REL A B ℓ₂ → Set _
Irreflexive _≈_ _<_ = ∀ {x y} → x ≈ y → ¬ (x < y)

Decidable : REL A B ℓ → Set _
Decidable _∼_ = ∀ x y → Dec (x ∼ y)

Symmetric : Rel A ℓ → Set _
Symmetric _∼_ = Sym _∼_ _∼_

Sym : REL A B ℓ₁ → REL B A ℓ₂ → Set _
Sym P Q = P ⇒ flip Q

-}

