{-data cycleE : {n : ℕ} {i j : Fin n} → Set where

  sucRight : ∀ {n : ℕ} {i : Fin n} → cycleE {ℕ.suc n} {inject₁ i} {Fin.suc i}
  sucLeft :  ∀ {n : ℕ} {i : Fin n} → cycleE {ℕ.suc n} {Fin.suc i} {inject₁ i}
  zeroLast : ∀ {n : ℕ}             → cycleE {ℕ.suc (ℕ.suc n)} {Fin.zero} {fromℕ (ℕ.suc n)}
  lastZero : ∀ {n : ℕ}             → cycleE {ℕ.suc (ℕ.suc n)} {fromℕ (ℕ.suc n)} {Fin.zero}



cycleE' : (n : ℕ) (i j : Fin n) → Set
cycleE' (ℕ.suc ℕ.zero) Fin.zero Fin.zero = ⊥
cycleE' (ℕ.suc (ℕ.suc n₁)) Fin.zero Fin.zero = ⊥
cycleE' (ℕ.suc (ℕ.suc n₁)) Fin.zero (Fin.suc j) = (j ≡ Fin.zero) ⊎ (j ≡ fromℕ n₁)
cycleE' (ℕ.suc (ℕ.suc n₁)) (Fin.suc i) Fin.zero = (i ≡ Fin.zero) ⊎ (i ≡ fromℕ n₁)
cycleE' (ℕ.suc (ℕ.suc n₁)) (Fin.suc i) (Fin.suc j) = (inject₁ i ≡ Fin.suc j) ⊎ (Fin.suc i ≡ inject₁ j)



cycleIrr : ∀ {n : ℕ} {i j : Fin n} → i ≡ j → cycleE {n} {i} {j} → ⊥
cycleIrr i≡j (sucRight {n₁} {i}) = 1+n≢n {toℕ i} (trans (cong toℕ (sym (i≡j))) (toℕ-inject₁ i))
cycleIrr i≡j (sucLeft {n₁} {i})  = 1+n≢n {toℕ i} (trans (cong toℕ (i≡j)) (toℕ-inject₁ i))
cycleIrr i≡j (zeroLast {n₁})     = {!!}
-- 0≢1+n {n₁}    (trans ((cong toℕ (i≡j))) (cong ℕ.suc (toℕ-fromℕ n₁)))
cycleIrr i≡j (lastZero {n₁})     = 1+n≢0 {n₁}    (trans (cong ℕ.suc (sym (toℕ-fromℕ n₁))) (cong toℕ (i≡j)))


cycleIrr' : ∀ (n : ℕ) (i j : Fin n) → i ≡ j → cycleE' n i j → ⊥
cycleIrr' (ℕ.suc ℕ.zero) Fin.zero Fin.zero i≡j = id 
cycleIrr' (ℕ.suc (ℕ.suc n₁)) Fin.zero Fin.zero i≡j = id
cycleIrr' (ℕ.suc (ℕ.suc n₁)) (Fin.suc i) (Fin.suc j) i≡j (_⊎_.inj₁ x) = 1+n≢n {toℕ i} (trans (cong toℕ (trans (i≡j) (sym x))) (toℕ-inject₁ i))
cycleIrr' (ℕ.suc (ℕ.suc n₁)) (Fin.suc i) (Fin.suc j) i≡j (_⊎_.inj₂ y) = 1+n≢n {toℕ j} (trans (cong toℕ (trans (sym i≡j) (y))) (toℕ-inject₁ j))



lastElemZeroLast : ∀ {n : ℕ} {j : Fin n} → cycleE {ℕ.suc (ℕ.suc n)} {Fin.zero} {Fin.suc (Fin.suc j)} → fromℕ n ≡ Fin.suc j
lastElemZeroLast {ℕ.suc n₁} (zeroLast) = refl

lastElemLastZero : ∀ {n : ℕ} {i : Fin n} → cycleE {ℕ.suc (ℕ.suc n)} {Fin.suc (Fin.suc i)} {Fin.zero} → fromℕ n ≡ Fin.suc i
lastElemLastZero {ℕ.suc n₁} (lastZero) = refl



lemma : ∀ (n : ℕ) (i j : Fin n) → cycleE {ℕ.suc n} {Fin.suc i} {Fin.suc j} → (inject₁ i ≡ Fin.suc j) ⊎ (Fin.suc i ≡ inject₁ j)
lemma n i j e = {!!}



increaseCycle : ∀ {n : ℕ} {i j : Fin n} → cycleE {ℕ.suc n} {Fin.suc i} {Fin.suc j} →
  cycleE {ℕ.suc (ℕ.suc n)} {Fin.suc (Fin.suc i)} {Fin.suc (Fin.suc j)}
increaseCycle {ℕ.suc ℕ.zero} {Fin.zero} {Fin.zero} ()
increaseCycle {ℕ.suc ℕ.zero} {Fin.zero} {Fin.suc ()} e
increaseCycle {ℕ.suc ℕ.zero} {Fin.suc ()} {Fin.zero} e
increaseCycle {ℕ.suc ℕ.zero} {Fin.suc ()} {Fin.suc j} e
increaseCycle {ℕ.suc (ℕ.suc n₁)} {Fin.zero} {Fin.suc Fin.zero} sucRight = {!!}
increaseCycle {ℕ.suc (ℕ.suc n₁)} {Fin.zero} {Fin.suc (Fin.suc j)} ()
increaseCycle {ℕ.suc (ℕ.suc n₁)} {Fin.suc Fin.zero} {Fin.zero} sucLeft = {!!}
increaseCycle {ℕ.suc (ℕ.suc n₁)} {Fin.suc (Fin.suc i)} {Fin.zero} ()
increaseCycle {ℕ.suc (ℕ.suc n₁)} {Fin.suc i} {Fin.suc j} e = {!!}

decreaseCycle :  ∀ {n : ℕ} {i j : Fin n} → cycleE {ℕ.suc (ℕ.suc n)} {Fin.suc (Fin.suc i)} {Fin.suc (Fin.suc j)} →
  cycleE {ℕ.suc n} {Fin.suc i} {Fin.suc j}
decreaseCycle = {!!}



cycleDec : ∀ {n : ℕ} {i j : Fin n} → Dec (cycleE {n} {i} {j})
cycleDec {ℕ.suc ℕ.zero}     {Fin.zero} {Fin.zero} = no (cycleIrr refl)
cycleDec {ℕ.suc (ℕ.suc n₁)} {Fin.zero} {Fin.zero} = no (cycleIrr refl)
cycleDec {ℕ.suc (ℕ.suc n₁)} {Fin.zero} {Fin.suc Fin.zero} = yes sucRight
cycleDec {ℕ.suc (ℕ.suc n₁)} {Fin.suc Fin.zero} {Fin.zero} = yes sucLeft

cycleDec {ℕ.suc (ℕ.suc n₁)} {Fin.zero} {Fin.suc (Fin.suc j)} with (fromℕ n₁) ≟ (Fin.suc j)
... | (yes n≡j) = yes (subst (λ x → cycleE {ℕ.suc (ℕ.suc n₁)} {Fin.zero} {x}) (cong Fin.suc n≡j) zeroLast) 
... | (no  n≢j) = no λ E0j+2 → n≢j (lastElemZeroLast E0j+2)

cycleDec {ℕ.suc (ℕ.suc n₁)} {Fin.suc (Fin.suc i)} {Fin.zero} with (fromℕ n₁) ≟ (Fin.suc i)
... | (yes n≡i) = yes (subst (λ x → cycleE {ℕ.suc (ℕ.suc n₁)} {x} {Fin.zero}) (cong Fin.suc n≡i) lastZero)
... | (no  n≢i) = no λ Ei+20 → n≢i (lastElemLastZero Ei+20)

cycleDec {ℕ.suc (ℕ.suc n₁)} {Fin.suc Fin.zero} {Fin.suc Fin.zero} = no (cycleIrr refl)

cycleDec {ℕ.suc (ℕ.suc .(ℕ.suc _))} {Fin.suc Fin.zero} {Fin.suc (Fin.suc Fin.zero)} = yes sucRight
cycleDec {ℕ.suc (ℕ.suc .(ℕ.suc _))} {Fin.suc Fin.zero} {Fin.suc (Fin.suc (Fin.suc j))} = no λ ()

cycleDec {ℕ.suc (ℕ.suc .(ℕ.suc _))} {Fin.suc (Fin.suc Fin.zero)} {Fin.suc Fin.zero} = yes sucLeft
cycleDec {ℕ.suc (ℕ.suc .(ℕ.suc _))} {Fin.suc (Fin.suc (Fin.suc i))} {Fin.suc Fin.zero} = no λ ()

cycleDec {ℕ.suc (ℕ.suc n₁)} {Fin.suc (Fin.suc i)} {Fin.suc (Fin.suc j)} with cycleDec {ℕ.suc n₁} {Fin.suc i} {Fin.suc j}
... | (yes Ei+1j+1) = yes (increaseCycle Ei+1j+1)
... | (no ¬Ei+1j+1) =  no λ Ei+2j+2 → ¬Ei+1j+1 (decreaseCycle Ei+2j+2) 



cycleSym : ∀ {n : ℕ} {i j : Fin n} → cycleE {n} {i} {j} → cycleE {n} {j} {i}
cycleSym sucRight = sucLeft
cycleSym sucLeft  = sucRight 
cycleSym zeroLast = lastZero
cycleSym lastZero = zeroLast



cycle : ℕ → EnumeratedFiniteGraph
cycle n = record
           { n = n
           ; FiniteE = {!!}
           ; isDecidableE = {!!} 
           ; isIrreflexiveE = cycleIrr 
           ; isSymmetricE = cycleSym
           }

-}
