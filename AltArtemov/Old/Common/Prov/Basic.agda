module AltArtemov.Common.Prov.Basic where

open import AltArtemov.Common.True.Basic public renaming (ᵗ⌊_⌋ to ᵗ⌊_⌋ᵀ)


data Prov (Γ : Cx) : ∀ {n} → Tm ᵍ⌊ Γ ⌋ n → Ty n → Set where
  var  : ∀ {n} {A : Ty n} (x : Var Γ A) →
           Prov Γ (VAR ⁱ⌊ x ⌋) A
  lam  : ∀ {n} {t : Tm (suc ᵍ⌊ Γ ⌋) n} {A B : Ty n} → Prov (Γ , A) t B →
           Prov Γ (LAM t) (A ⊃ B)
  app  : ∀ {n} {t₁ t₂ : Tm ᵍ⌊ Γ ⌋ n} {A B : Ty n} → Prov Γ t₁ (A ⊃ B) → Prov Γ t₂ A →
           Prov Γ (APP t₁ t₂) B
  pair : ∀ {n} {t₁ t₂ : Tm ᵍ⌊ Γ ⌋ n} {A B : Ty n} → Prov Γ t₁ A → Prov Γ t₂ B →
           Prov Γ (PAIR t₁ t₂) (A ∧ B)
  fst  : ∀ {n} {t : Tm ᵍ⌊ Γ ⌋ n} {A B : Ty n} → Prov Γ t (A ∧ B) →
           Prov Γ (FST t) A
  snd  : ∀ {n} {t : Tm ᵍ⌊ Γ ⌋ n} {A B : Ty n} → Prov Γ t (A ∧ B) →
           Prov Γ (SND t) B
  up   : ∀ {n} {t : Tm ᵍ⌊ Γ ⌋ (suc n)} {u : Tm 0 n} {A : Ty n} → Prov Γ t (u ∶ A) →
           Prov Γ (UP t) (! u ∶ u ∶ A)
  down : ∀ {n} {t : Tm ᵍ⌊ Γ ⌋ (suc n)} {u : Tm 0 n} {A : Ty n} → Prov Γ t (u ∶ A) →
           Prov Γ (DOWN t) A

ᵗ⌊_⌋ : ∀ {Γ n} {t : Tm ᵍ⌊ Γ ⌋ n} {A : Ty n} → Prov Γ t A → Tm ᵍ⌊ Γ ⌋ n
ᵗ⌊ var x ⌋      = VAR ⁱ⌊ x ⌋
ᵗ⌊ lam j ⌋      = LAM ᵗ⌊ j ⌋
ᵗ⌊ app j₁ j₂ ⌋  = APP ᵗ⌊ j₁ ⌋ ᵗ⌊ j₂ ⌋
ᵗ⌊ pair j₁ j₂ ⌋ = PAIR ᵗ⌊ j₁ ⌋ ᵗ⌊ j₂ ⌋
ᵗ⌊ fst j ⌋      = FST ᵗ⌊ j ⌋
ᵗ⌊ snd j ⌋      = SND ᵗ⌊ j ⌋
ᵗ⌊ up j ⌋       = UP ᵗ⌊ j ⌋
ᵗ⌊ down j ⌋     = DOWN ᵗ⌊ j ⌋

true⇗ : ∀ {Γ n} {A : Ty n} (j : True Γ A) → Prov Γ ᵗ⌊ j ⌋ᵀ A
true⇗ (var x)      = var x
true⇗ (lam j)      = lam (true⇗ j)
true⇗ (app j₁ j₂)  = app (true⇗ j₁) (true⇗ j₂)
true⇗ (pair j₁ j₂) = pair (true⇗ j₁) (true⇗ j₂)
true⇗ (fst j)      = fst (true⇗ j)
true⇗ (snd j)      = snd (true⇗ j)
true⇗ (up j)       = up (true⇗ j)
true⇗ (down j)     = down (true⇗ j)

true⇙ : ∀ {Γ n} {t : Tm ᵍ⌊ Γ ⌋ n} {A : Ty n} (j : Prov Γ t A) → True Γ A
true⇙ (var x)      = var x
true⇙ (lam j)      = lam (true⇙ j)
true⇙ (app j₁ j₂)  = app (true⇙ j₁) (true⇙ j₂)
true⇙ (pair j₁ j₂) = pair (true⇙ j₁) (true⇙ j₂)
true⇙ (fst j)      = fst (true⇙ j)
true⇙ (snd j)      = snd (true⇙ j)
true⇙ (up j)       = up (true⇙ j)
true⇙ (down j)     = down (true⇙ j)

true⇗⇙-id : ∀ {Γ n} {A : Ty n} (j : True Γ A) → true⇙ (true⇗ j) ≡ j
true⇗⇙-id (var x)      = refl
true⇗⇙-id (lam j)      = cong lam (true⇗⇙-id j)
true⇗⇙-id (app j₁ j₂)  = cong₂ app (true⇗⇙-id j₁) (true⇗⇙-id j₂)
true⇗⇙-id (pair j₁ j₂) = cong₂ pair (true⇗⇙-id j₁) (true⇗⇙-id j₂)
true⇗⇙-id (fst j)      = cong fst (true⇗⇙-id j)
true⇗⇙-id (snd j)      = cong snd (true⇗⇙-id j)
true⇗⇙-id (up j)       = cong up (true⇗⇙-id j)
true⇗⇙-id (down j)     = cong down (true⇗⇙-id j)

prov⇗ : ∀ {Γ n} {t : Tm ᵍ⌊ Γ ⌋ n} {A : Ty n} (j : Prov Γ t A) →
           Prov Γ (! ᵗ⌊ j ⌋) (t ∶ A)
prov⇗ (var x)      = {!var x!}
prov⇗ (lam j)      = {!!}
prov⇗ (app j₁ j₂)  = {!!}
prov⇗ (pair j₁ j₂) = {!!}
prov⇗ (fst j)      = fst {!prov⇗ j!}
prov⇗ (snd j)      = {!!}
prov⇗ (up j)       = {!!}
prov⇗ (down j)     = {!!}
