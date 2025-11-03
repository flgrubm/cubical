module Cubical.Categories.WithFamilies.Structure.Sigma where

open import Cubical.Foundations.Prelude

open import Cubical.Foundations.Equiv
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Foundations.Transport
open import Cubical.Categories.Presheaf
open import Cubical.Foundations.Function

open import Cubical.Categories.WithFamilies.Base

record Σ-Structure-CwF {ℓ ℓ' ℓTy ℓTm : Level} {C : Category ℓ ℓ'} (cwf : CwF C ℓTy ℓTm) : Type ((ℓ-suc (ℓ-max (ℓ-max (ℓ-max ℓ ℓ') ℓTy) ℓTm))) where
  open CwF cwf

  field
    sig : (Γ : Ctx) (A : Ty Γ) → Ty (ctxExt Γ A) → Ty Γ
    sig-nat : {Γ Δ : Ctx} (A : Ty Γ) (B : Ty (ctxExt Γ A)) (σ : Subst Δ Γ)
            → sig Γ A B ∘Ty σ ≡ sig Δ (A ∘Ty σ) (B ∘Ty ⟨ σ , A ⟩) 

    sig-iso  : {Γ : Ctx} (A : Ty Γ) (B : Ty (ctxExt Γ A)) → (Tm Γ (sig Γ A B)) ≃ (Σ[ a ∈ Tm Γ A ] (Tm Γ (B ∘Ty ctxExtSubst A IdSubst (subst⁻ (Tm Γ) (∘ᴾId C tyPresheaf A) a))))
    sig-iso' : {Γ : Ctx} (A : Ty Γ) (B : Ty (ctxExt Γ A)) → (Tm Γ (sig Γ A B)) ≃ (Σ[ a ∈ Tm Γ (A ∘Ty IdSubst) ] (Tm Γ (B ∘Ty ctxExtSubst A IdSubst a)))

  
