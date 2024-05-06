{-# OPTIONS --with-K #-}

open import Data.Nat using (ℕ)
open import Data.Nat.Base using (_/_; _*_; _+_; _∸_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (+-∸-assoc; +-suc; m≤n⇒m≤1+n; ≤-trans; ≤-refl)
open import Data.Fin using (Fin)
open import Agda.Builtin.Bool using (Bool; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (Dec; yes; no)
open import Data.Fin.Base using (fromℕ; inject₁; toℕ)
open import Data.Fin.Properties using (_≟_; 0≢1+n; suc-injective; fromℕ≢inject₁; inject₁-injective; toℕ-inject₁)
open import Data.Vec.Base using (Vec; tabulate; allFin; count; sum; replicate)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; _≢_; trans)
open import Data.Product.Base using (_×_; proj₁; proj₂; _,_; ∃; ∃-syntax)
open import Function.Base using (id)
open import Relation.Nullary.Decidable.Core using (_⊎-dec_; _×-dec_)
open import Relation.Unary using (Pred; Decidable; _⊆_)
open import Level using (Level)
open import Function.Base using (_∘_)
import Relation.Binary.PropositionalEquality as Eq
open Eq.≡-Reasoning
open import miscLemmas using (suc≢inject₁; last≢inject₁; emptyDec; _≐_; 1+m+n≤m+1+n)
open import Graphs using (EnumeratedFiniteGraph)
open import Cycles using (_minus1; cycleE; 3+_cycle; cycleDec')
open Dec
open EnumeratedFiniteGraph
open Vec


module countLemmas where


private
  variable
    a p q : Level
    A B : Set a
   

2+n≢n : ∀ {n : ℕ} → ℕ.suc (ℕ.suc n) ≢ n
2+n≢n {ℕ.zero} = {!!}
2+n≢n {ℕ.suc ℕ.zero} = {!!}
2+n≢n {ℕ.suc (ℕ.suc n₁)} = 2+n≢n ∘ Data.Nat.Properties.suc-injective

{- 1+n≢n : suc n ≢ n
1+n≢n {suc n} = 1+n≢n ∘ suc-injective -}

sucsuc≢inject₁inject₁ : ∀ {n : ℕ} {i : Fin n} → Fin.suc (Fin.suc i) ≡ inject₁ (inject₁ i) → ⊥
sucsuc≢inject₁inject₁ {n} {i} 2+i≡i = 2+n≢n (trans (cong toℕ (2+i≡i)) ({!toℕ-inject₁ ?!}))


-- 1+n≢n (trans (cong toℕ (1+i≡i)) (toℕ-inject₁ _))


j≡i-1×i≡j-1 : ∀ (n : ℕ) (i j : Fin (3 + n)) → (j ≡ (i minus1) × i ≡ (j minus1)) → ⊥
j≡i-1×i≡j-1 ℕ.zero Fin.zero (Fin.suc .(fromℕ 1)) (refl , ())
j≡i-1×i≡j-1 ℕ.zero (Fin.suc .(fromℕ 1)) Fin.zero (() , refl)
j≡i-1×i≡j-1 ℕ.zero (Fin.suc (Fin.suc i)) (Fin.suc .(inject₁ i)) (refl , snd) = sucsuc≢inject₁inject₁ snd
j≡i-1×i≡j-1 (ℕ.suc n₁) Fin.zero (Fin.suc .(fromℕ (ℕ.suc (ℕ.suc n₁)))) (refl , ())
j≡i-1×i≡j-1 (ℕ.suc n₁) (Fin.suc .(fromℕ (ℕ.suc (ℕ.suc n₁)))) Fin.zero (() , refl)
j≡i-1×i≡j-1 (ℕ.suc n₁) (Fin.suc (Fin.suc i)) (Fin.suc .(inject₁ i)) (refl , snd) = sucsuc≢inject₁inject₁ snd


countExt : {n : ℕ} {P Q : Pred A p} (P? : Decidable P) (Q? : Decidable Q) → (P ≐ Q) → ∀ (xs : Vec A n) → count P? xs ≡ count Q? xs
countExt P? Q? f [] = refl
countExt P? Q? f (x ∷ xs) with P? x | Q? x
... | yes Px | yes Qx = cong ℕ.suc (countExt P? Q? f xs)
... | yes Px | no ¬Qx = ⊥-elim (¬Qx (f .proj₁ Px)) 
... | no ¬Px | yes Qx = ⊥-elim (¬Px (f .proj₂ Qx)) 
... | no ¬Px | no ¬Qx = countExt P? Q? f xs


compLemma : {P : Pred B p} (P? : Decidable P) (f : A → B) {n : ℕ} (g : Fin n → A) → count P? (tabulate (f ∘ g)) ≡ count (P? ∘ f) (tabulate g)
compLemma P? f {ℕ.zero} g = refl
compLemma P? f {ℕ.suc n₁} g with P? (f (g Fin.zero))
... | yes Pfg0 = cong ℕ.suc (compLemma P? f (g ∘ Fin.suc))
... | no ¬Pfg0 = compLemma P? f (g ∘ Fin.suc)


count0 : ∀ (n : ℕ) (xs : Vec A n) → count (λ _ → emptyDec) xs ≡ 0 
count0 ℕ.zero [] = refl
count0 (ℕ.suc n₁) (x ∷ xs) = count0 n₁ xs


∀x⊥-count0 : {P : Pred A p} (P? : Decidable P) {n : ℕ} (xs : Vec A n) → (∀ x → P x → ⊥) → count P? xs ≡ 0
∀x⊥-count0 P? [] ∀x⊥ = refl
∀x⊥-count0 P? (x ∷ xs) ∀x⊥ with P? x
... | yes Px = ⊥-elim (∀x⊥ x Px)
... | no ¬Px = ∀x⊥-count0 P? xs ∀x⊥


count1 : (n : ℕ) (i : Fin n) → count (_≟ i) (allFin n) ≡ 1
count1 (ℕ.suc n₁) Fin.zero = cong ℕ.suc (begin
                                           count {n = n₁} (_≟ Fin.zero) (tabulate Fin.suc) 
                                         ≡⟨ compLemma (λ (j : Fin (1 + n₁)) → j ≟ Fin.zero) Fin.suc id ⟩
                                           count (λ j → Fin.suc j ≟ Fin.zero) (allFin n₁)
                                         ≡⟨ ∀x⊥-count0 (λ j → Fin.suc j ≟ Fin.zero) (allFin n₁) (λ j 1+j≡0 → 0≢1+n (sym 1+j≡0)) ⟩     
                                           0                                           
                                         ∎)
count1 (ℕ.suc n₁) (Fin.suc i) = begin
                                   count (_≟ Fin.suc i) (tabulate Fin.suc)                                   
                                 ≡⟨ compLemma (λ (j : Fin (1 + n₁)) → j ≟ Fin.suc i) Fin.suc id ⟩                                 
                                   count (λ j → Fin.suc j ≟ Fin.suc i) (allFin n₁)
                                 ≡⟨ countExt (λ j → Fin.suc j ≟ Fin.suc i) (λ j → j ≟ i)
                                             ((λ 1+j≡1+i → suc-injective 1+j≡1+i) , (λ j≡i → cong Fin.suc j≡i)) (allFin n₁) ⟩                                 
                                   count (λ j → j ≟ i) (allFin n₁)                                  
                                 ≡⟨ count1 n₁ i ⟩                                
                                   1                                   
                                 ∎


countf1 : ∀ (n : ℕ) (i : Fin (3 + n)) → count (λ (j : Fin (3 + n)) → i ≟ j minus1) (allFin (3 + n)) ≡ 1
countf1 n₁ Fin.zero = cong ℕ.suc (begin
                                    count {n = n₁} (λ j → Fin.zero ≟ j minus1) (tabulate (λ x → Fin.suc (Fin.suc (Fin.suc x))))                                    
                                 ≡⟨ sym (compLemma (λ j → Fin.zero ≟ j) _minus1 {n = n₁}  λ x → Fin.suc (Fin.suc (Fin.suc x))) ⟩                                 
                                   count {n = n₁} (λ j → Fin.zero ≟ j) (tabulate (λ x → inject₁ (Fin.suc (Fin.suc x))))                                  
                                 ≡⟨ compLemma (λ (j : Fin (3 + n₁)) → Fin.zero ≟ j) inject₁ (λ x → Fin.suc (Fin.suc x)) ⟩
                                   count {n = n₁} (λ j → Fin.zero ≟ inject₁ j) (tabulate (λ x → Fin.suc (Fin.suc x)))
                                 ≡⟨ compLemma (λ (j : Fin (2 + n₁)) → Fin.zero ≟ inject₁ j) Fin.suc Fin.suc ⟩                                
                                   count {n = n₁} (λ j → Fin.zero ≟ Fin.suc (inject₁ j)) (tabulate Fin.suc)
                                 ≡⟨ ∀x⊥-count0 (λ (j : Fin (1 + n₁)) → Fin.zero ≟ Fin.suc (inject₁ j)) (tabulate Fin.suc)
                                               (λ j 0≡1+j → 0≢1+n 0≡1+j) ⟩
                                   0                                   
                                 ∎)
countf1 n₁ (Fin.suc Fin.zero) = cong ℕ.suc (begin
                                              count {n = n₁} (λ j → Fin.suc Fin.zero ≟ j minus1) (tabulate (λ x → Fin.suc (Fin.suc (Fin.suc x))))                       
                                            ≡⟨ sym (compLemma (Fin.suc Fin.zero ≟_) _minus1 {n = n₁} λ x → Fin.suc (Fin.suc (Fin.suc x))) ⟩                            
                                              count {n = n₁} (Fin.suc Fin.zero ≟_) (tabulate (λ x → inject₁ (Fin.suc (Fin.suc x))))
                                            ≡⟨ compLemma (λ (j : Fin (3 + n₁)) → Fin.suc Fin.zero ≟ j) inject₁ (λ x → Fin.suc (Fin.suc x)) ⟩
                                              count {n = n₁} (λ j → Fin.suc Fin.zero ≟ inject₁ j) (tabulate λ x → Fin.suc (Fin.suc x))
                                            ≡⟨ compLemma (λ (j : Fin (2 + n₁)) → Fin.suc Fin.zero ≟ inject₁ j) Fin.suc Fin.suc ⟩
                                              count {n = n₁} (λ j → Fin.suc Fin.zero ≟ Fin.suc (inject₁ j)) (tabulate Fin.suc)  
                                            ≡⟨ countExt {n = n₁} (λ j → Fin.suc Fin.zero ≟ Fin.suc (inject₁ j)) (λ j → Fin.zero ≟ inject₁ j)
                                                        ((λ 1≡1+j → suc-injective 1≡1+j) , (λ 0≡j → cong Fin.suc 0≡j)) (tabulate Fin.suc) ⟩                     
                                              count {n = n₁} (λ j → Fin.zero ≟ inject₁ j) (tabulate Fin.suc)   
                                            ≡⟨ compLemma (λ (j : Fin (1 + n₁)) → Fin.zero ≟ inject₁ j) Fin.suc id ⟩
                                              count (λ j → Fin.zero ≟ Fin.suc (inject₁ j)) (allFin n₁)
                                            ≡⟨ ∀x⊥-count0 (λ j → Fin.zero ≟ Fin.suc (inject₁ j)) (allFin n₁) (λ j 0≡1+j → 0≢1+n 0≡1+j) ⟩ 
                                              0                                
                                            ∎)
countf1 n₁ (Fin.suc (Fin.suc i)) with i ≟ fromℕ n₁
... | yes i≡fromℕ = cong ℕ.suc (begin
                            count {n = n₁} (λ j → Fin.suc (Fin.suc i) ≟ j minus1) (tabulate (λ x → Fin.suc (Fin.suc (Fin.suc x))))                      
                          ≡⟨ sym (compLemma (Fin.suc (Fin.suc i) ≟_) _minus1 (λ x → Fin.suc (Fin.suc (Fin.suc x)))) ⟩
                            count (Fin.suc (Fin.suc i) ≟_) (tabulate (λ x → Fin.suc (Fin.suc (inject₁ x))))  
                          ≡⟨ compLemma (Fin.suc (Fin.suc i) ≟_) (λ x → Fin.suc (Fin.suc x)) inject₁ ⟩                                       
                            count (λ j → Fin.suc (Fin.suc i) ≟ Fin.suc (Fin.suc j)) (tabulate inject₁)  
                          ≡⟨ countExt (λ j → Fin.suc (Fin.suc i) ≟ Fin.suc (Fin.suc j)) (i ≟_)
                                      ((λ 2+i≡2+j → suc-injective (suc-injective 2+i≡2+j)) , λ i≡j → cong (λ x → Fin.suc (Fin.suc x)) i≡j)
                                      (tabulate inject₁) ⟩                                       
                            count (i ≟_) (tabulate inject₁) 
                          ≡⟨ cong (λ x → count (x ≟_) (tabulate inject₁)) i≡fromℕ ⟩
                            count (fromℕ n₁ ≟_) (tabulate inject₁)  
                          ≡⟨ compLemma (fromℕ n₁ ≟_) inject₁ id ⟩
                            count (λ j → fromℕ n₁ ≟ inject₁ j) (allFin n₁)
                          ≡⟨ ∀x⊥-count0 (λ j → fromℕ n₁ ≟ inject₁ j) (allFin n₁) (λ j fromℕ≡j → fromℕ≢inject₁ fromℕ≡j) ⟩ 
                            0  
                          ∎ )
... | no ¬i≡fromℕ = let (i' , i≡inject₁i') = last≢inject₁ n₁ i ¬i≡fromℕ in
                    begin
                      count {n = n₁} (λ j → Fin.suc (Fin.suc i) ≟ j minus1) (tabulate (λ x → Fin.suc (Fin.suc (Fin.suc x))))
                    ≡⟨ sym (compLemma (Fin.suc (Fin.suc i) ≟_) _minus1 (λ x → Fin.suc (Fin.suc (Fin.suc x)))) ⟩  
                      count (Fin.suc (Fin.suc i) ≟_) (tabulate (λ x → Fin.suc (Fin.suc (inject₁ x))))   
                    ≡⟨ compLemma (Fin.suc (Fin.suc i) ≟_) (λ x → Fin.suc (Fin.suc x)) inject₁ ⟩                                           
                      count (λ j → Fin.suc (Fin.suc i) ≟ Fin.suc (Fin.suc j)) (tabulate inject₁)  
                    ≡⟨ countExt (λ j → Fin.suc (Fin.suc i) ≟ Fin.suc (Fin.suc j)) (i ≟_)
                            ((λ 2+i≡2+j → suc-injective (suc-injective 2+i≡2+j)) , λ i≡j → cong (λ x → Fin.suc (Fin.suc x)) i≡j)
                            (tabulate inject₁) ⟩           
                      count (i ≟_) (tabulate inject₁)
                    ≡⟨ compLemma (i ≟_) inject₁ id ⟩
                      count (λ j → i ≟ inject₁ j) (allFin n₁)
                    ≡⟨ cong (λ x → count (λ j → x ≟ inject₁ j) (allFin n₁)) i≡inject₁i' ⟩
                      count (λ j → inject₁ i' ≟ inject₁ j) (allFin n₁)
                    ≡⟨ countExt (λ j → inject₁ i' ≟ inject₁ j) (i' ≟_)
                            ((λ inject₁i'≡inject₁j → inject₁-injective inject₁i'≡inject₁j) , λ i≡j  → cong inject₁ i≡j) (allFin n₁) ⟩
                      count (i' ≟_) (allFin n₁)
                    ≡⟨ countExt (i' ≟_) (_≟ i') ((λ i'≡j → sym i'≡j) , λ j≡i' → sym j≡i') (allFin n₁) ⟩
                      count (_≟ i') (allFin n₁)
                    ≡⟨ count1 n₁ i' ⟩
                       1
                    ∎


+≤× : ∀ {n : ℕ} {P Q : Pred A p} (P? : Decidable P) (Q? : Decidable Q) (xs : Vec A n) → count (λ x → (P? x) ×-dec (Q? x)) xs ≤ (count P? xs + count Q? xs) 
+≤× P? Q? [] = z≤n
+≤× P? Q? (x ∷ xs) with P? x | Q? x
... | yes Px | yes Qx = s≤s (≤-trans (m≤n⇒m≤1+n (+≤× P? Q? xs)) (1+m+n≤m+1+n _ _)) 
... | yes Px | no ¬Qx = m≤n⇒m≤1+n (+≤× P? Q? xs) 
... | no ¬Px | yes Qx = ≤-trans (m≤n⇒m≤1+n (+≤× P? Q? xs)) (1+m+n≤m+1+n _ _) 
... | no ¬Px | no ¬Qx = +≤× P? Q? xs


count⊎ : ∀ {n : ℕ} {P Q : Pred A p} (P? : Decidable P) (Q? : Decidable Q) (xs : Vec A n) → count (λ x → (P? x) ⊎-dec (Q? x)) xs ≡ count P? xs + count Q? xs ∸ count (λ x → (P? x) ×-dec (Q? x)) xs 
count⊎ P? Q? [] = refl
count⊎ P? Q? (x ∷ xs) with P? x | Q? x
... | yes Px | yes Qx = begin
                           ℕ.suc (count (λ x₁ → P? x₁ ⊎-dec Q? x₁) xs)
                         ≡⟨ cong ℕ.suc (count⊎ P? Q? xs) ⟩
                           ℕ.suc (count P? xs + count Q? xs ∸ count (λ x → (P? x) ×-dec (Q? x)) xs)
                         ≡⟨ sym (+-∸-assoc 1 (+≤× P? Q? xs)) ⟩
                           ℕ.suc (count P? xs + count Q? xs) ∸ count (λ x₁ → P? x₁ ×-dec Q? x₁) xs
                         ≡⟨ cong (_∸ count (λ x₁ → P? x₁ ×-dec Q? x₁) xs) (sym (+-suc _ _)) ⟩
                           count P? xs + ℕ.suc (count Q? xs) ∸ count (λ x₁ → P? x₁ ×-dec Q? x₁) xs
                         ∎ 
... | yes Px | no ¬Qx = begin
                           ℕ.suc (count (λ x₁ → P? x₁ ⊎-dec Q? x₁) xs)
                         ≡⟨ cong ℕ.suc (count⊎ P? Q? xs) ⟩
                           ℕ.suc (count P? xs + count Q? xs ∸ count (λ x → (P? x) ×-dec (Q? x)) xs)
                         ≡⟨ sym (+-∸-assoc 1 (+≤× P? Q? xs)) ⟩
                           ℕ.suc (count P? xs + count Q? xs) ∸ count (λ x₁ → P? x₁ ×-dec Q? x₁) xs
                         ∎
... | no ¬Px | yes Qx = begin
                           ℕ.suc (count (λ x₁ → P? x₁ ⊎-dec Q? x₁) xs)
                         ≡⟨ cong ℕ.suc (count⊎ P? Q? xs) ⟩
                           ℕ.suc (count P? xs + count Q? xs ∸ count (λ x → (P? x) ×-dec (Q? x)) xs)
                         ≡⟨ sym (+-∸-assoc 1 (+≤× P? Q? xs)) ⟩
                           ℕ.suc (count P? xs + count Q? xs) ∸ count (λ x₁ → P? x₁ ×-dec Q? x₁) xs
                         ≡⟨ cong (_∸ count (λ x₁ → P? x₁ ×-dec Q? x₁) xs) (sym (+-suc _ _)) ⟩
                           count P? xs + ℕ.suc (count Q? xs) ∸ count (λ x₁ → P? x₁ ×-dec Q? x₁) xs
                         ∎
... | no ¬Px | no ¬Qx = count⊎ P? Q? xs


degCycleN : ∀ {n : ℕ} (u : Fin (3 + n)) → deg (3+ n cycle) u ≡ 2
degCycleN {n} u = let P = λ v → (v ≟ (u minus1)) in
                let Q = λ v → (u ≟ (v minus1)) in
                let P⊎Q = λ v → ((v ≟ (u minus1)) ⊎-dec (u ≟ (v minus1))) in
                let P×Q = λ v → ((v ≟ (u minus1)) ×-dec (u ≟ (v minus1))) in
                let allFin = allFin (3 + n) in
                 begin
                   deg (3+ n cycle) u
                 ≡⟨⟩
                   count (cycleDec' n u) allFin
                 ≡⟨⟩
                   count P⊎Q allFin
                 ≡⟨ count⊎ P Q allFin ⟩
                   count P allFin + count Q allFin ∸ count P×Q allFin
                 ≡⟨ cong (λ x → x + count Q allFin ∸ count P×Q allFin) (count1 (3 + n) (u minus1)) ⟩
                   1 + count Q allFin ∸ count P×Q allFin
                 ≡⟨ cong (λ x → 1 + x ∸ count P×Q allFin) (countf1 n u) ⟩
                   1 + 1 ∸ count P×Q allFin
                 ≡⟨ cong (2 ∸_) (∀x⊥-count0 P×Q allFin (j≡i-1×i≡j-1 n u)) ⟩ 
                   2
                 ∎


sumLemma : ∀ (n k : ℕ) → sum (tabulate {n} (λ _ → k)) ≡ n * k
sumLemma ℕ.zero k = refl
sumLemma (ℕ.suc n₁) k rewrite sumLemma n₁ k = refl

sumLemma1 : ∀ (n k : ℕ) → tabulate {n} (λ _ → k) ≡ replicate n k
sumLemma1 ℕ.zero k = refl
sumLemma1 (ℕ.suc n₁) k rewrite sumLemma1 n₁ k = refl


tabulate-replicate : ∀ (n k : ℕ) (f : Fin n → ℕ) → (∀ (u : Fin n) → f u ≡ k) → tabulate {n} f ≡ replicate n k
tabulate-replicate ℕ.zero k f f≡k = refl
tabulate-replicate (ℕ.suc n₁) k f f≡k = {!!}


-- begin
                                        --   f Fin.zero ∷ tabulate {n₁} (λ x → f (Fin.suc x))
                                        -- ≡⟨ {!!} ⟩
                                        --   k ∷ tabulate {n₁} (λ x → f (Fin.suc x))
                                        -- ≡⟨ {!!} ⟩ 
                                        --   k ∷ replicate n₁ k
                                        -- ∎


sumLemma2 : ∀ (n k : ℕ) →  sum (replicate n k) ≡ n * k
sumLemma2 ℕ.zero k = refl
sumLemma2 (ℕ.suc n₁) k rewrite sumLemma2 n₁ k = refl


cycle|E| : ∀ (n : ℕ) → 2|E| (3+ n cycle) ≡ (3 + n) * 2
cycle|E| n = begin
               2|E| (3+ n cycle)
             ≡⟨⟩
               sum (tabulate {3 + n} (deg (3+ n cycle)))
             ≡⟨ cong sum (tabulate-replicate (3 + n) 2 (deg (3+ n cycle)) degCycleN) ⟩
               sum (replicate (3 + n) 2)
             ≡⟨ sumLemma2 (3 + n) 2 ⟩ 
               (3 + n) * 2
             ∎
         
