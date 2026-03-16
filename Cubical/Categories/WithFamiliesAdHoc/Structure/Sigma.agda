module Cubical.Categories.WithFamiliesAdHoc.Structure.Sigma where

open import Cubical.Foundations.Prelude

open import Cubical.Foundations.Equiv
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Foundations.Transport
open import Cubical.Categories.Presheaf
open import Cubical.Foundations.Function

open import Cubical.Categories.WithFamiliesAdHoc.Base

record Σ-Structure-CwF {ℓ ℓ' ℓTy ℓTm : Level} {C : Category ℓ ℓ'} (cwf : CwF C ℓTy ℓTm) : Type ((ℓ-suc (ℓ-max (ℓ-max (ℓ-max ℓ ℓ') ℓTy) ℓTm))) where
  open Category C
  open CwF cwf

  field
    typeeq-subst : {Γ : Ctx} {A A' : Ty Γ} → (A ≡ A') → Tm Γ A' → Tm Γ A

  idsubst-action : {Γ : Ctx} (A : Ty Γ) → Tm Γ A → Tm Γ (A ∘Ty IdSubst)
  idsubst-action A = typeeq-subst (∘ᴾId C tyPresheaf A)

  field
    -- morally: σ ⋆ ⟨ IdSubst {Δ} , a ⟩ ≡ ⟨ IdSubst {Γ} , a [ σ ] ⟩ ⋆ ⟨ σ , A ⟩
    -- this should be provable
    ctxExtSubstSigmaSndEq : {Γ Δ : Ctx} (A : Ty Δ) (B : Ty (ctxExt Δ A)) (a : Tm Δ A) (σ : Subst Γ Δ) →
        ((B ∘Ty ctxExtSubst A IdSubst (idsubst-action A a) {-(subst⁻ (Tm Δ) (∘ᴾId C tyPresheaf A) a)-}) ∘Ty σ)
            ≡
        ((B ∘Ty ⟨ σ , A ⟩) ∘Ty ctxExtSubst (A ∘Ty σ) IdSubst (idsubst-action (A ∘Ty σ) (a [ σ ])) {-(subst⁻ (Tm Γ) (∘ᴾId C tyPresheaf (A ∘Ty σ)) (a [ σ ]))-})

  field
    sig : (Γ : Ctx) (A : Ty Γ) → Ty (ctxExt Γ A) → Ty Γ
    sig-nat : {Γ Δ : Ctx} (A : Ty Γ) (B : Ty (ctxExt Γ A)) (σ : Subst Δ Γ)
            → sig Γ A B ∘Ty σ ≡ sig Δ (A ∘Ty σ) (B ∘Ty ⟨ σ , A ⟩) 

    sig-pair : {Γ : Ctx} (A : Ty Γ) (B : Ty (ctxExt Γ A))
      → (Σ[ a ∈ Tm Γ A ] (Tm Γ (B ∘Ty ctxExtSubst A IdSubst (idsubst-action A a))))
      → (Tm Γ (sig Γ A B))
    
    sig-pair-nat : {Γ : Ctx} (A : Ty Γ) (B : Ty (ctxExt Γ A))
                  (a : Tm Γ A)
                  (b : Tm Γ (B ∘Ty ctxExtSubst A IdSubst (idsubst-action A a)))
                  {Δ : Ctx} (τ : Subst Δ Γ)
                → ((sig-pair A B (a , b)) [ τ ])
                ≡ typeeq-subst (sig-nat _ _ _) (sig-pair (A ∘Ty τ) (B ∘Ty ⟨ τ , A ⟩)
                    ((a [ τ ]) , (typeeq-subst (sym (ctxExtSubstSigmaSndEq _ _ _ _))
                    (b [ τ ]))))

    sig-pair-isEquiv : {Γ : Ctx} (A : Ty Γ) (B : Ty (ctxExt Γ A))
      → isEquiv (sig-pair A B)
    -- no sig-pair-isEquiv-nat needed since it’s a proposition
