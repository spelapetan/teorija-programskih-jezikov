data Ty : Set where
    BOOL : Ty
    _⇒_ : Ty → Ty → Ty
    _×_ : Ty → Ty → Ty

data Ctx : Set where
    ∅ : Ctx
    _,_ : Ctx → Ty → Ctx

data _∈_ : Ty → Ctx → Set where
    Z : {A : Ty} {Γ : Ctx} → A ∈ (Γ , A)
    S : {A B : Ty} {Γ : Ctx} → A ∈ Γ → A ∈ (Γ , B)

mutual
    data _⊢v_ : Ctx → Ty → Set where

        VAR : {Γ : Ctx} {A : Ty} →
            A ∈ Γ →
            -----
            Γ ⊢v A

        TRUE : {Γ : Ctx} →
            --------
            Γ ⊢v BOOL

        FALSE : {Γ : Ctx} →
            --------
            Γ ⊢v BOOL

        ƛ : {Γ : Ctx} {A B : Ty} →
            (Γ , A) ⊢c B →
            -----------
            Γ ⊢v (A ⇒ B)

        ⟨_,_⟩ : {Γ : Ctx} {A B : Ty} →
            Γ ⊢v A →
            Γ ⊢v B →
            -----------
            Γ ⊢v (A × B)
        
    data _⊢c_ : Ctx → Ty → Set where

        IF_THEN_ELSE_ : {Γ : Ctx} {A : Ty} →
            Γ ⊢v BOOL →
            Γ ⊢c A →
            Γ ⊢c A →
            -----
            Γ ⊢c A

        _∙_ : {Γ : Ctx} {A B : Ty} →
            Γ ⊢v (A ⇒ B) →
            Γ ⊢v A →
            -----
            Γ ⊢c B

        FST : {Γ : Ctx} {A B : Ty} →
            Γ ⊢v (A × B) →
            -----
            Γ ⊢c A

        SND : {Γ : Ctx} {A B : Ty} →
            Γ ⊢v (A × B) →
            -----
            Γ ⊢c B
        
        RETURN : {Γ : Ctx} {A : Ty} →
            Γ ⊢v A →
            ------
            Γ ⊢c A

ext : {Γ Δ : Ctx}
  → ({A : Ty} → A ∈ Γ → A ∈ Δ)
    --------------------------------------
  → {A B : Ty} → A ∈ (Γ , B) → A ∈ (Δ , B)
ext σ Z = Z
ext σ (S x) = S (σ x)

rename-v : {Γ Δ : Ctx}
  → ({A : Ty} → A ∈ Γ → A ∈ Δ)
    ---------------------------
  → {A : Ty} → Γ ⊢v A → Δ ⊢v A
rename-c : {Γ Δ : Ctx}
  → ({A : Ty} → A ∈ Γ → A ∈ Δ)
    ---------------------------
  → {A : Ty} → Γ ⊢c A → Δ ⊢c A
rename-v σ (VAR x) = VAR (σ x)
rename-v σ TRUE = TRUE
rename-v σ FALSE = TRUE
rename-v σ (ƛ M) = ƛ (rename-c (ext σ) M)
rename-v σ ⟨ M , N ⟩ = ⟨ rename-v σ M , rename-v σ N ⟩
rename-c σ (IF M THEN N₁ ELSE N₂) = 
    IF (rename-v σ M) THEN (rename-c σ N₁) ELSE (rename-c σ N₂)
rename-c σ (M ∙ N) = rename-v σ M ∙ rename-v σ N
rename-c σ (FST M) = FST (rename-v σ M)
rename-c σ (SND M) = SND (rename-v σ M)
rename-c σ (RETURN V) = RETURN (rename-v σ V)

exts : {Γ Δ : Ctx}
  → ({A : Ty} → A ∈ Γ → Δ ⊢v A)
    ---------------------------------------
  → {A B : Ty} → A ∈ (Γ , B) → (Δ , B) ⊢v A
exts σ Z = VAR Z
exts σ (S x) = rename-v S (σ x)

subst-v : {Γ Δ : Ctx}
  → ({A : Ty} → A ∈ Γ → Δ ⊢v A)
    -------------------------
  → {A : Ty} → Γ ⊢v A → Δ ⊢v A
subst-c : {Γ Δ : Ctx}
  → ({A : Ty} → A ∈ Γ → Δ ⊢v A)
    -------------------------
  → {A : Ty} → Γ ⊢c A → Δ ⊢c A
subst-v σ (VAR x) = σ x
subst-v σ TRUE = TRUE
subst-v σ FALSE = TRUE
subst-v σ (ƛ M) = ƛ (subst-c (exts σ) M)
subst-v σ ⟨ M , N ⟩ = ⟨ subst-v σ M , subst-v σ N ⟩
subst-c σ (IF M THEN N₁ ELSE N₂) = 
    IF (subst-v σ M) THEN (subst-c σ N₁) ELSE (subst-c σ N₂)
subst-c σ (M ∙ N) = subst-v σ M ∙ subst-v σ N
subst-c σ (FST M) = FST (subst-v σ M)
subst-c σ (SND M) = SND (subst-v σ M)
subst-c σ (RETURN V) = RETURN (subst-v σ V)

_[_] : {Γ : Ctx} {A B : Ty}
  → (Γ , B) ⊢c A
  → Γ ⊢v B
    -----
  → Γ ⊢c A
_[_] {Γ} {B = B} N M = subst-c σ N
  where
  σ : ∀ {A : Ty} → A ∈ (Γ , B) → Γ ⊢v A
  σ Z = M
  σ (S x) = VAR x


data _↝_ : {A : Ty} → ∅ ⊢c A → ∅ ⊢c A → Set where
    IF-TRUE : {A : Ty} {M₁ M₂ : ∅ ⊢c A} →
        ------------------------------
        (IF TRUE THEN M₁ ELSE M₂) ↝ M₁
    IF-FALSE : {A : Ty} {M₁ M₂ : ∅ ⊢c A} →
        ------------------------------
        (IF FALSE THEN M₁ ELSE M₂) ↝ M₂
    APP-BETA : {A B : Ty} {M : (∅ , A) ⊢c B} {N : ∅ ⊢v A} →
        ------------------------------------------------
        ((ƛ M) ∙ N) ↝ ( M [ N ])
    FST-BETA : {A B : Ty} {M : ∅ ⊢v A} {N : ∅ ⊢v B} →
        ------------------------------------------------
        FST ⟨ M , N ⟩ ↝ (RETURN M)
    SND-BETA : {A B : Ty} {M : ∅ ⊢v A} {N : ∅ ⊢v B} →
        ------------------------------------------------
        SND ⟨ M , N ⟩ ↝ (RETURN N)


-- data progresses : {A : Ty} → ∅ ⊢ A → Set where
--     is-value : {A : Ty} {M : ∅ ⊢ A} →
--         value M →
--         ------------
--         progresses M
--     steps : {A : Ty} {M M' : ∅ ⊢ A} →
--         M ↝ M' →
--         ------------
--         progresses M

-- progress : {A : Ty} → (M : ∅ ⊢ A) → progresses M

-- progress TRUE = is-value value-TRUE
-- progress FALSE = is-value value-FALSE
-- progress (IF M THEN N₁ ELSE N₂) with progress M
-- ... | is-value value-TRUE = steps IF-TRUE
-- ... | is-value value-FALSE = steps IF-FALSE
-- ... | steps M↝M' = steps (IF-STEP M↝M')
-- progress (M ∙ N) with progress M
-- ... | steps M↝M' = steps (APP-STEP1 M↝M')
-- ... | is-value value-LAMBDA with progress N
-- ...     | is-value V = steps (APP-BETA V)
-- ...     | steps N↝N' = steps (APP-STEP2 value-LAMBDA N↝N')
-- progress (ƛ M) = is-value value-LAMBDA
-- progress ⟨ M , N ⟩ with progress M
-- ... | steps M↝M' = steps (PAIR-STEP1 M↝M')
-- ... | is-value V with progress N
-- ...     | is-value W = is-value (value-PAIR V W)
-- ...     | steps N↝N' = steps (PAIR-STEP2 V N↝N')
-- progress (FST M) with progress M
-- ... | is-value (value-PAIR V W) = steps (FST-BETA V W)
-- ... | steps M↝M' = steps (FST-STEP M↝M')
-- progress (SND M) with progress M
-- ... | is-value (value-PAIR V W) = steps (SND-BETA V W)
-- ... | steps M↝M' = steps (SND-STEP M↝M')
