{-# OPTIONS --with-K #-}

open import Data.Nat using (ℕ)
open import Data.Nat.Base using (_/_; _*_; _+_; _∸_)
open import Data.Nat.Properties using (1+n≢n; 1+n≢0)
open import Data.Fin using (Fin)
open import Agda.Builtin.Bool using (Bool; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (Dec; yes; no; map′)
open import Data.Fin.Base using (toℕ; fromℕ; inject₁; cast; pred)
open import Data.Fin.Properties using (toℕ-inject₁; toℕ-fromℕ; _≟_; 0≢1+n; suc-injective)
open import Data.Vec.Base using (Vec; tabulate; sum; allFin; count; countᵇ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst; _≢_)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Product.Base using (_×_; proj₁; proj₂; _,_)
open import Function.Base using (id)
open import Relation.Nullary.Negation.Core using (_¬-⊎_)
open import Relation.Nullary.Decidable.Core using (_⊎-dec_; _×-dec_)
open import Function.Bundles using (_⤖_; _⇔_)
open import Relation.Unary using (Pred; Decidable; _⊆_)
open import Level using (Level)
open import Function.Base using (_∘_)
import Relation.Binary.PropositionalEquality as Eq
open Eq.≡-Reasoning
open import Graphs
open import Cycles
open Dec
open EnumeratedFiniteGraph

private
  variable
    a p q ℓ₁ ℓ₂ : Level
    A B : Set a
    
_≐_ : Pred A ℓ₁ → Pred A ℓ₁ → Set _
P ≐ Q = (P ⊆ Q) × (Q ⊆ P)



countExt : {n : ℕ} {P Q : Pred A p} (P? : Decidable P) (Q? : Decidable Q) → (P ≐ Q) → ∀ (xs : Vec A n) → count P? xs ≡ count Q? xs
countExt P? Q? f Vec.[] = refl
countExt P? Q? f (x Vec.∷ xs) with P? x | Q? x
... | yes Px | yes Qx = cong ℕ.suc (countExt P? Q? f xs)
... | yes Px | no ¬Qx = ⊥-elim (¬Qx (f .proj₁ Px)) 
... | no ¬Px | yes Qx = ⊥-elim (¬Px (f .proj₂ Qx)) 
... | no ¬Px | no ¬Qx = countExt P? Q? f xs


emptyDec : Dec (⊥)
emptyDec = no (λ x → x)


count0 : ∀ (n : ℕ) (xs : Vec A n) → count (λ _ → emptyDec) xs ≡ 0 
count0 ℕ.zero Vec.[] = refl
count0 (ℕ.suc n₁) (x Vec.∷ xs) = count0 n₁ xs


compLemma : {P : Pred B p} (P? : Decidable P) (f : A → B) {n : ℕ} (g : Fin n → A) → count P? (tabulate (f ∘ g)) ≡ count (P? ∘ f) (tabulate g)
compLemma P? f {ℕ.zero} g = refl
compLemma P? f {ℕ.suc n₁} g with P? (f (g Fin.zero))
... | yes Pfg0 = cong ℕ.suc (compLemma P? f (g ∘ Fin.suc))
... | no ¬Pfg0 = compLemma P? f (g ∘ Fin.suc)


count1 : (n : ℕ) (i : Fin n) → count (_≟ i) (allFin n) ≡ 1
count1 (ℕ.suc n₁) Fin.zero = cong ℕ.suc (begin
                                           count {n = n₁} (_≟ Fin.zero) (tabulate Fin.suc)
                                         ≡⟨ compLemma (λ (i : Fin (ℕ.suc n₁)) → i ≟ Fin.zero) Fin.suc id ⟩
                                           count (λ i → Fin.suc i ≟ Fin.zero) (allFin n₁)
                                         ≡⟨ countExt (λ i → Fin.suc i ≟ Fin.zero) (λ _ → emptyDec) ((λ 1+n≡0 → 0≢1+n (sym 1+n≡0)) , ⊥-elim) (allFin n₁) ⟩
                                           count (λ _ → emptyDec) (allFin n₁)
                                         ≡⟨ count0 n₁ (allFin n₁) ⟩
                                           0
                                         ∎)
count1 (ℕ.suc n₁) (Fin.suc i) = begin
                                   count (_≟ Fin.suc i) (tabulate Fin.suc)
                                 ≡⟨ compLemma (λ (j : Fin (ℕ.suc n₁)) → j ≟ Fin.suc i) Fin.suc id ⟩
                                   count (λ j → Fin.suc j ≟ Fin.suc i) (allFin n₁)
                                 ≡⟨ {!!} ⟩
                                   count (λ j → j ≟ i) (allFin n₁)
                                 ≡⟨ count1 n₁ i ⟩
                                   1
                                 ∎


countf1 : ∀ (n : ℕ) (i : Fin (3 + n)) → count (λ (j : Fin (3 + n))→ j minus1 ≟ i) (allFin (3 + n)) ≡ 1
countf1 ℕ.zero Fin.zero = refl
countf1 ℕ.zero (Fin.suc i) = {!!}  
countf1 (ℕ.suc n₁) Fin.zero = cong ℕ.suc {!!}
countf1 (ℕ.suc n₁) (Fin.suc i) = {!!} 


add : ∀ (n m : ℕ) → n + (ℕ.suc m) ≡ ℕ.suc (n + m)
add ℕ.zero m = refl
add (ℕ.suc n) m = cong ℕ.suc (add n m)


sub : ∀ (n m : ℕ) → ℕ.suc (n ∸ m) ≡ (ℕ.suc n) ∸ m
sub n ℕ.zero = refl 
sub ℕ.zero (ℕ.suc m) = ?
sub (ℕ.suc n₁) (ℕ.suc m) = ?



-- begin
--                     n ∸ m
--                   ≡⟨ {!!} ⟩
--                     ℕ.suc n ∸ ℕ.suc m
--                   ≡⟨ {!!} ⟩ 
--                     ℕ.suc (n ∸ ℕ.suc m)
--                   ∎

-- with ℕ.suc (n ∸ m) | sub n m
-- ... | ℕ.zero = refl
-- ... | ℕ.suc k rewrite sub n m = refl

count⊎ : ∀ {n : ℕ} {P Q : Pred A p} (P? : Decidable P) (Q? : Decidable Q) (xs : Vec A n) → count (λ x → (P? x) ⊎-dec (Q? x)) xs ≡ count P? xs + count Q? xs ∸ count (λ x → (P? x) ×-dec (Q? x)) xs  
count⊎ P? Q? Vec.[] = refl
count⊎ P? Q? (x Vec.∷ xs) with P? x | Q? x
... | yes Px | yes Qx = {!!} -- same as third case
... | yes Px | no ¬Qx = {!!} 
... | no ¬Px | yes Qx = {!!} 
... | no ¬Px | no ¬Qx = count⊎ P? Q? xs





degCycleN : ∀ (n : ℕ) (u : Fin (3 + n)) → deg (3+ n cycle) u ≡ 2
degCycleN n u = {!!}


cycle|E| : ∀ (n : ℕ) → 2|E| (3+ n cycle) ≡ (3 + n) * 2
cycle|E| ℕ.zero = refl
cycle|E| (ℕ.suc n₁) = {!!}