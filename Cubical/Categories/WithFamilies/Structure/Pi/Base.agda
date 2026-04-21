module Cubical.Categories.WithFamilies.Structure.Pi.Base where

open import Cubical.Foundations.Prelude

open import Cubical.Foundations.Equiv
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Foundations.Transport
open import Cubical.Categories.Presheaf
open import Cubical.Foundations.Function

open import Cubical.Categories.WithFamilies.Base

record Π-Structure-CwF {ℓ ℓ' ℓTy ℓTm : Level} {C : Category ℓ ℓ'} (cwf : CwF C ℓTy ℓTm) : Type ((ℓ-suc (ℓ-max (ℓ-max (ℓ-max ℓ ℓ') ℓTy) ℓTm))) where
  open Category C
  open CwF cwf

  field
    pi : (Γ : Ctx) (A : Ty Γ) → Ty (ctxExt Γ A) → Ty Γ
    pi-nat : {Γ Δ : Ctx} (A : Ty Γ) (B : Ty (ctxExt Γ A)) (σ : Subst Δ Γ) → pi Γ A B ∘Ty σ ≡ pi Δ (A ∘Ty σ) (B ∘Ty ⟨ σ , A ⟩)
    pi-iso : {Γ : Ctx} (A : Ty Γ) (B : Ty (ctxExt Γ A)) → Tm Γ (pi Γ A B) ≃ Tm (ctxExt Γ A) B

    pi-iso-nat : {Γ Δ : Ctx} (A : Ty Γ) (B : Ty (ctxExt Γ A)) (σ : Subst Δ Γ) → (x : Tm Γ (pi Γ A B)) →
      pi-iso (A ∘Ty σ) (B ∘Ty ⟨ σ , A ⟩) .fst (subst (Tm Δ) (pi-nat A B σ) (x [ σ ]))
      ≡
      (pi-iso A B .fst x [ ⟨ σ , A ⟩ ])
