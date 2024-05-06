open import Data.Nat using (ℕ; _+_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (1+n≢n; ≤-refl)
open import Data.Fin using (Fin)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (Dec; yes; no)
open import Data.Fin.Base using (toℕ; fromℕ; inject₁)
open import Data.Fin.Properties using (toℕ-inject₁; _≟_; 0≢1+n)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; _≢_)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂; swap)
open import Relation.Nullary.Negation.Core using (_¬-⊎_)
open import Relation.Nullary.Decidable.Core using (_⊎-dec_)
open import Data.Product.Base using (_×_; proj₁; proj₂; _,_; ∃; ∃-syntax)
open import Relation.Unary using (Pred; Decidable; _⊆_)
open import Level using (Level)
import Relation.Binary.PropositionalEquality as Eq
open Eq.≡-Reasoning


module miscLemmas where


private
  variable
    a ℓ₁ ℓ₂ : Level
    A B : Set a


suc≢inject₁ : ∀ {n : ℕ} {i : Fin n} → Fin.suc i ≡ inject₁ i → ⊥
suc≢inject₁ 1+i≡i = 1+n≢n (trans (cong toℕ (1+i≡i)) (toℕ-inject₁ _))





last≢inject₁ : ∀ (n : ℕ) (i : Fin (1 + n)) → i ≢ fromℕ n →  ∃[ i' ] i ≡ inject₁ i'
last≢inject₁ ℕ.zero Fin.zero i≢fromℕ = ⊥-elim (i≢fromℕ refl)
last≢inject₁ (ℕ.suc n₁) Fin.zero i≢fromℕ = Fin.zero , refl
last≢inject₁ (ℕ.suc n₁) (Fin.suc i) 1+i≢1+fromℕ =
  let
  (i' , inject₁i'≡i) = last≢inject₁ n₁ i (λ p → 1+i≢1+fromℕ (cong Fin.suc p)) in Fin.suc i' , cong Fin.suc inject₁i'≡i


emptyDec : Dec (⊥)
emptyDec = no (λ x → x)


_≐_ : Pred A ℓ₁ → Pred A ℓ₁ → Set _
P ≐ Q = (P ⊆ Q) × (Q ⊆ P)


1+m+n≤m+1+n : ∀ (m n : ℕ) → 1 + (m + n) ≤ m + (1 + n)
1+m+n≤m+1+n ℕ.zero n = s≤s ≤-refl
1+m+n≤m+1+n (ℕ.suc m) n = s≤s (1+m+n≤m+1+n m n)
