{-# OPTIONS --with-K #-}

open import Data.Nat using (ℕ; _+_; _*_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (1+n≢n; ≤-refl; suc-injective)
open import Data.Fin using (Fin)
open import Data.Fin.Base using (toℕ; fromℕ; inject₁)
open import Data.Fin.Properties using (toℕ-inject₁)
open import Data.Vec.Base using (Vec; tabulate; replicate; sum)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product.Base using (_×_; _,_; ∃; ∃-syntax)
open import Relation.Unary using (Pred; _⊆_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong; _≢_)
open import Level using (Level)
open import Function.Base using (_∘_)
open Relation.Binary.PropositionalEquality.≡-Reasoning
open Vec


module MiscLemmas where


private
  variable
    a ℓ₁ : Level
    A : Set a


suc≢inject₁ : ∀ {n : ℕ} {i : Fin n} → Fin.suc i ≡ inject₁ i → ⊥
suc≢inject₁ 1+i≡i = 1+n≢n (trans (cong toℕ (1+i≡i)) (toℕ-inject₁ _))


2+n≢n : ∀ {n : ℕ} → ℕ.suc (ℕ.suc n) ≢ n
2+n≢n {ℕ.suc (ℕ.suc n₁)} = 2+n≢n ∘ suc-injective


sucsuc≢inject₁inject₁ : ∀ {n : ℕ} {i : Fin n} → Fin.suc (Fin.suc i) ≡ inject₁ (inject₁ i) → ⊥
sucsuc≢inject₁inject₁ {n} {i} 2+i≡i = 2+n≢n (trans (cong toℕ (2+i≡i)) (trans (toℕ-inject₁ _) (toℕ-inject₁ _)))


last≢inject₁ : ∀ (n : ℕ) (i : Fin (1 + n)) → i ≢ fromℕ n →  ∃[ i' ] i ≡ inject₁ i'
last≢inject₁ ℕ.zero Fin.zero i≢fromℕ = ⊥-elim (i≢fromℕ refl)
last≢inject₁ (ℕ.suc n₁) Fin.zero i≢fromℕ = Fin.zero , refl
last≢inject₁ (ℕ.suc n₁) (Fin.suc i) 1+i≢1+fromℕ =
  let
  (i' , inject₁i'≡i) = last≢inject₁ n₁ i (λ p → 1+i≢1+fromℕ (cong Fin.suc p)) in Fin.suc i' , cong Fin.suc inject₁i'≡i


_≐_ : Pred A ℓ₁ → Pred A ℓ₁ → Set _
P ≐ Q = (P ⊆ Q) × (Q ⊆ P)


1+m+n≤m+1+n : ∀ (m n : ℕ) → 1 + (m + n) ≤ m + (1 + n)
1+m+n≤m+1+n ℕ.zero n = s≤s ≤-refl
1+m+n≤m+1+n (ℕ.suc m) n = s≤s (1+m+n≤m+1+n m n)


tabulate-replicate : ∀ (n k : ℕ) (f : Fin n → ℕ) → (∀ (u : Fin n) → f u ≡ k) → tabulate {n} f ≡ replicate n k
tabulate-replicate ℕ.zero k f f≡k = refl
tabulate-replicate (ℕ.suc n₁) k f f≡k = begin
                                          f Fin.zero ∷ tabulate {n₁} (λ x → f (Fin.suc x))
                                        ≡⟨ cong (_∷ tabulate {n₁} (λ x → f (Fin.suc x))) (f≡k Fin.zero) ⟩
                                          k ∷ tabulate {n₁} (λ x → f (Fin.suc x))
                                        ≡⟨ cong (k ∷_) (tabulate-replicate n₁ k (λ x → f (Fin.suc x)) (λ u → f≡k (Fin.suc u))) ⟩ 
                                          k ∷ replicate n₁ k
                                        ∎


sumReplicate : ∀ (n k : ℕ) →  sum (replicate n k) ≡ n * k
sumReplicate ℕ.zero k = refl
sumReplicate (ℕ.suc n₁) k rewrite sumReplicate n₁ k = refl
