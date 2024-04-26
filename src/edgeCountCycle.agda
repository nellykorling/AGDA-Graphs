{-# OPTIONS --with-K #-}

open import Data.Nat using (ℕ)
open import Data.Nat.Base using (_/_; _*_; _+_; _∸_)
open import Data.Nat.Properties using (+-∸-comm)
open import Data.Fin using (Fin)
open import Agda.Builtin.Bool using (Bool; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (Dec; yes; no)
open import Data.Fin.Base using (fromℕ; inject₁)
open import Data.Fin.Properties using (_≟_; 0≢1+n; suc-injective; fromℕ≢inject₁; inject₁-injective)
open import Data.Vec.Base using (Vec; tabulate; allFin; count)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; subst; _≢_)
open import Data.Product.Base using (_×_; proj₁; proj₂; _,_; ∃; ∃-syntax)
open import Function.Base using (id)
open import Relation.Nullary.Decidable.Core using (_⊎-dec_; _×-dec_)
open import Relation.Unary using (Pred; Decidable; _⊆_)
open import Level using (Level)
open import Function.Base using (_∘_)
import Relation.Binary.PropositionalEquality as Eq
open Eq.≡-Reasoning
open import Graphs
open import Cycles
open Dec
open EnumeratedFiniteGraph
open Vec

private
  variable
    a p q ℓ₁ ℓ₂ : Level
    A B : Set a
    
_≐_ : Pred A ℓ₁ → Pred A ℓ₁ → Set _
P ≐ Q = (P ⊆ Q) × (Q ⊆ P)



countExt : {n : ℕ} {P Q : Pred A p} (P? : Decidable P) (Q? : Decidable Q) → (P ≐ Q) → ∀ (xs : Vec A n) → count P? xs ≡ count Q? xs
countExt P? Q? f [] = refl
countExt P? Q? f (x ∷ xs) with P? x | Q? x
... | yes Px | yes Qx = cong ℕ.suc (countExt P? Q? f xs)
... | yes Px | no ¬Qx = ⊥-elim (¬Qx (f .proj₁ Px)) 
... | no ¬Px | yes Qx = ⊥-elim (¬Px (f .proj₂ Qx)) 
... | no ¬Px | no ¬Qx = countExt P? Q? f xs


emptyDec : Dec (⊥)
emptyDec = no (λ x → x)


count0 : ∀ (n : ℕ) (xs : Vec A n) → count (λ _ → emptyDec) xs ≡ 0 
count0 ℕ.zero [] = refl
count0 (ℕ.suc n₁) (x ∷ xs) = count0 n₁ xs


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
                                   
                                 ≡⟨ compLemma (λ (j : Fin (1 + n₁)) → j ≟ Fin.suc i) Fin.suc id ⟩
                                 
                                   count (λ j → Fin.suc j ≟ Fin.suc i) (allFin n₁)
                                   
                                 ≡⟨ countExt (λ j → Fin.suc j ≟ Fin.suc i) (λ j → j ≟ i) ((λ sucj≡suci → suc-injective sucj≡suci) , (λ j≡i → cong Fin.suc j≡i)) (allFin n₁) ⟩
                                 
                                   count (λ j → j ≟ i) (allFin n₁)
                                   
                                 ≡⟨ count1 n₁ i ⟩
                                 
                                   1
                                   
                                 ∎


lemma : ∀ (n : ℕ) (i : Fin (1 + n)) → fromℕ n ≢ i →  ∃[ i' ] i ≡ inject₁ i'
lemma ℕ.zero Fin.zero i≢fromℕ = ⊥-elim (i≢fromℕ refl)
lemma (ℕ.suc n₁) Fin.zero i≢fromℕ = Fin.zero , refl
lemma (ℕ.suc n₁) (Fin.suc i) 1+i≢1+fromℕ =
  let
  (i' , i≡inject₁i') = lemma n₁ i (λ p → 1+i≢1+fromℕ (cong Fin.suc p)) in Fin.suc i' , cong Fin.suc i≡inject₁i'


countf1 : ∀ (n : ℕ) (i : Fin (3 + n)) → count (λ (j : Fin (3 + n)) → j minus1 ≟ i) (allFin (3 + n)) ≡ 1
countf1 n₁ Fin.zero = cong ℕ.suc (begin

                                    count {n = n₁} (λ j → j minus1 ≟ Fin.zero) (tabulate (λ x → Fin.suc (Fin.suc (Fin.suc x))))
                                    
                                 ≡⟨ sym (compLemma (λ j → j ≟ Fin.zero) _minus1 {n = n₁}  λ x → Fin.suc (Fin.suc (Fin.suc x))) ⟩
                                 
                                   count {n = n₁} (λ j → j ≟ Fin.zero) (tabulate (λ x → inject₁ (Fin.suc (Fin.suc x))))
                                   
                                 ≡⟨ compLemma (λ (j : Fin (3 + n₁)) → j ≟ Fin.zero) inject₁ (λ x → Fin.suc (Fin.suc x)) ⟩

                                   count {n = n₁} (λ j → inject₁ j ≟ Fin.zero) (tabulate (λ x → Fin.suc (Fin.suc x)))

                                 ≡⟨ compLemma (λ (j : Fin (2 + n₁)) → inject₁ j ≟ Fin.zero) Fin.suc Fin.suc ⟩
                                 
                                   count {n = n₁} (λ j → Fin.suc (inject₁ j) ≟ Fin.zero) (tabulate Fin.suc)  
                                   
                                 ≡⟨ countExt (λ (j : Fin (1 + n₁)) → Fin.suc (inject₁ j) ≟ Fin.zero) (λ _ → emptyDec) ((λ 1+n≡0 → 0≢1+n (sym 1+n≡0)) , ⊥-elim) (tabulate Fin.suc) ⟩

                                   count {n = n₁} (λ _ → emptyDec) (tabulate Fin.suc)
                                   
                                 ≡⟨ count0 n₁ (tabulate Fin.suc) ⟩
                                 
                                   0
                                   
                                 ∎)
countf1 n₁ (Fin.suc Fin.zero) = cong ℕ.suc (begin

                                              count {n = n₁} (λ j → j minus1 ≟ Fin.suc Fin.zero) (tabulate (λ x → Fin.suc (Fin.suc (Fin.suc x))))
                                              
                                            ≡⟨ sym (compLemma (_≟ Fin.suc Fin.zero) _minus1 {n = n₁} λ x → Fin.suc (Fin.suc (Fin.suc x))) ⟩
                                            
                                              count {n = n₁} (_≟ Fin.suc Fin.zero) (tabulate (λ x → inject₁ (Fin.suc (Fin.suc x))))
                                              
                                            ≡⟨ compLemma (λ (j : Fin (3 + n₁)) → j ≟ Fin.suc Fin.zero) inject₁ (λ x → Fin.suc (Fin.suc x)) ⟩
                                            
                                              count {n = n₁} (λ j → inject₁ j ≟ Fin.suc Fin.zero) (tabulate λ x → Fin.suc (Fin.suc x))
                                              
                                            ≡⟨ compLemma (λ (j : Fin (2 + n₁)) → inject₁ j ≟ Fin.suc Fin.zero) Fin.suc Fin.suc ⟩
                                            
                                              count {n = n₁} (λ j → Fin.suc (inject₁ j) ≟ Fin.suc Fin.zero) (tabulate Fin.suc)
                                              
                                            ≡⟨ countExt {n = n₁} (λ j → Fin.suc (inject₁ j) ≟ Fin.suc Fin.zero) (λ j → inject₁ j ≟ Fin.zero)
                                                                 ((λ sucj≡1 → suc-injective sucj≡1) , (λ j≡0 → cong Fin.suc j≡0)) (tabulate Fin.suc) ⟩
                                                                  
                                              count {n = n₁} (λ j → inject₁ j ≟ Fin.zero) (tabulate Fin.suc)
                                              
                                            ≡⟨ compLemma (λ (j : Fin (1 + n₁)) → inject₁ j ≟ Fin.zero) Fin.suc id ⟩
                                            
                                              count (λ j → Fin.suc (inject₁ j) ≟ Fin.zero) (allFin n₁)
                                              
                                            ≡⟨ countExt (λ j → Fin.suc (inject₁ j) ≟ Fin.zero) (λ _ → emptyDec) ((λ 1+n≡0 → 0≢1+n (sym 1+n≡0)) , ⊥-elim) (allFin n₁) ⟩
                                            
                                              count (λ _ → emptyDec) (allFin n₁)
                                              
                                            ≡⟨ count0 n₁ (allFin n₁) ⟩
                                            
                                              0
                                              
                                            ∎)
countf1 n₁ (Fin.suc (Fin.suc i)) with fromℕ n₁ ≟ i
... | yes p = cong ℕ.suc (begin

                            count {n = n₁} (λ j → j minus1 ≟ Fin.suc (Fin.suc i)) (tabulate (λ x → Fin.suc (Fin.suc (Fin.suc x))))
                            
                          ≡⟨ sym (compLemma (_≟ Fin.suc (Fin.suc i)) _minus1 (λ x → Fin.suc (Fin.suc (Fin.suc x)))) ⟩
                          
                            count (_≟ Fin.suc (Fin.suc i)) (tabulate (λ x → Fin.suc (Fin.suc (inject₁ x))))
                            
                          ≡⟨ compLemma (_≟ Fin.suc (Fin.suc i)) (λ x → Fin.suc (Fin.suc x)) inject₁ ⟩
                                                                 
                            count (λ j → Fin.suc (Fin.suc j) ≟ Fin.suc (Fin.suc i)) (tabulate inject₁)
                            
                          ≡⟨ countExt (λ j → Fin.suc (Fin.suc j) ≟ Fin.suc (Fin.suc i)) (_≟ i)
                                      ((λ 2+j≡2+i → suc-injective (suc-injective 2+j≡2+i)) , λ j≡i → cong (λ x → Fin.suc (Fin.suc x)) j≡i) (tabulate inject₁) ⟩
                                                                 
                            count (_≟ i) (tabulate inject₁)
                            
                          ≡⟨ cong (λ x → count (_≟ x) (tabulate inject₁)) (sym p) ⟩
                          
                            count (_≟ fromℕ n₁) (tabulate inject₁)
                            
                          ≡⟨ compLemma (_≟ fromℕ n₁) inject₁ id ⟩
                          
                            count (λ j → inject₁ j ≟ fromℕ n₁) (allFin n₁)
                            
                          ≡⟨ countExt (λ j → inject₁ j ≟ fromℕ n₁) (λ _ → emptyDec) ((λ j≡fromℕ → fromℕ≢inject₁ (sym j≡fromℕ)) , ⊥-elim) (allFin n₁) ⟩
                          
                            count (λ _ → emptyDec) (allFin n₁)
                            
                          ≡⟨ count0 n₁ (allFin n₁) ⟩
                          
                            0
                            
                          ∎)
... | no ¬p = let (i' , i≡inject₁i') = lemma n₁ i ¬p in
                begin
                
                  count {n = n₁} (λ j → j minus1 ≟ Fin.suc (Fin.suc i)) (tabulate (λ x → Fin.suc (Fin.suc (Fin.suc x))))
                  
                ≡⟨ sym (compLemma (_≟ Fin.suc (Fin.suc i)) _minus1 (λ x → Fin.suc (Fin.suc (Fin.suc x)))) ⟩
                          
                  count (_≟ Fin.suc (Fin.suc i)) (tabulate (λ x → Fin.suc (Fin.suc (inject₁ x))))
                            
                ≡⟨ compLemma (_≟ Fin.suc (Fin.suc i)) (λ x → Fin.suc (Fin.suc x)) inject₁ ⟩
                                                                 
                  count (λ j → Fin.suc (Fin.suc j) ≟ Fin.suc (Fin.suc i)) (tabulate inject₁)
                            
                ≡⟨ countExt (λ j → Fin.suc (Fin.suc j) ≟ Fin.suc (Fin.suc i)) (_≟ i)
                                      ((λ 2+j≡2+i → suc-injective (suc-injective 2+j≡2+i)) , λ j≡i → cong (λ x → Fin.suc (Fin.suc x)) j≡i) (tabulate inject₁) ⟩
                                      
                  count (_≟ i) (tabulate inject₁)
                  
                ≡⟨ compLemma (_≟ i) inject₁ id ⟩
                
                  count (λ j → inject₁ j ≟ i) (allFin n₁)
                  
                ≡⟨ cong (λ x → count (λ j → inject₁ j ≟ x) (allFin n₁)) i≡inject₁i' ⟩
                
                  count (λ j → inject₁ j ≟ inject₁ i') (allFin n₁)
                  
                ≡⟨ countExt (λ j → inject₁ j ≟ inject₁ i') (_≟ i')
                            ((λ inject₁j≡inject₁i → inject₁-injective inject₁j≡inject₁i) , λ j≡i  → cong inject₁ j≡i) (allFin n₁) ⟩
                
                  count (_≟ i') (allFin n₁)
                  
                ≡⟨ count1 n₁ i' ⟩
                
                  1
                  
                ∎


count⊎ : ∀ {n : ℕ} {P Q : Pred A p} (P? : Decidable P) (Q? : Decidable Q) (xs : Vec A n) → count (λ x → (P? x) ⊎-dec (Q? x)) xs ≡ count P? xs + count Q? xs ∸ count (λ x → (P? x) ×-dec (Q? x)) xs 
count⊎ P? Q? [] = refl
count⊎ P? Q? (x ∷ xs) with P? x | Q? x
... | yes Px | yes Qx = {!!} -- same as third case
... | yes Px | no ¬Qx = {!!} 
... | no ¬Px | yes Qx = {!!} 
... | no ¬Px | no ¬Qx = count⊎ P? Q? xs

-- (1 + n) - m ≡ 1 + (n - m)

degCycleN : ∀ (n : ℕ) (u : Fin (3 + n)) → deg (3+ n cycle) u ≡ 2
degCycleN n u = {!!}


cycle|E| : ∀ (n : ℕ) → 2|E| (3+ n cycle) ≡ (3 + n) * 2
cycle|E| ℕ.zero = refl
cycle|E| (ℕ.suc n₁) = {!!}
