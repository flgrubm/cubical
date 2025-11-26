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
  open Category C
  open CwF cwf

  field
    sig : (Γ : Ctx) (A : Ty Γ) → Ty (ctxExt Γ A) → Ty Γ
    sig-nat : {Γ Δ : Ctx} (A : Ty Γ) (B : Ty (ctxExt Γ A)) (σ : Subst Δ Γ)
            → sig Γ A B ∘Ty σ ≡ sig Δ (A ∘Ty σ) (B ∘Ty ⟨ σ , A ⟩) 

    sig-iso  : {Γ : Ctx} (A : Ty Γ) (B : Ty (ctxExt Γ A)) →
        (Tm Γ (sig Γ A B)) ≃ (Σ[ a ∈ Tm Γ A ] (Tm Γ (B ∘Ty ctxExtSubst A IdSubst (subst⁻ (Tm Γ) (∘ᴾId C tyPresheaf A) a))))
    -- sig-iso' : {Γ : Ctx} (A : Ty Γ) (B : Ty (ctxExt Γ A)) →
    --     (Tm Γ (sig Γ A B)) ≃ (Σ[ a ∈ Tm Γ (A ∘Ty IdSubst) ] (Tm Γ (B ∘Ty ctxExtSubst A IdSubst a)))

  dest : {Γ : Ctx} (A : Ty Γ) (B : Ty (ctxExt Γ A)) →
        (Tm Γ (sig Γ A B)) → (Σ[ a ∈ Tm Γ A ] (Tm Γ (B ∘Ty ctxExtSubst A IdSubst (subst⁻ (Tm Γ) (∘ᴾId C tyPresheaf A) a))))
  dest {Γ} A B = sig-iso {Γ} A B .fst

  cons : {Γ : Ctx} (A : Ty Γ) (B : Ty (ctxExt Γ A)) →
         (Σ[ a ∈ Tm Γ A ] (Tm Γ (B ∘Ty ctxExtSubst A IdSubst (subst⁻ (Tm Γ) (∘ᴾId C tyPresheaf A) a)))) → (Tm Γ (sig Γ A B))
  cons {Γ} A B = invEq (sig-iso {Γ} A B)

  -- dest' : {Γ : Ctx} (A : Ty Γ) (B : Ty (ctxExt Γ A)) →
  --       (Tm Γ (sig Γ A B)) → (Σ[ a ∈ Tm Γ (A ∘Ty IdSubst) ] (Tm Γ (B ∘Ty ctxExtSubst A IdSubst a)))
  -- dest' {Γ} A B = sig-iso' {Γ} A B .fst

  -- cons' : {Γ : Ctx} (A : Ty Γ) (B : Ty (ctxExt Γ A)) →
  --       (Σ[ a ∈ Tm Γ (A ∘Ty IdSubst) ] (Tm Γ (B ∘Ty ctxExtSubst A IdSubst a))) → (Tm Γ (sig Γ A B))
  -- cons' {Γ} A B = invEq (sig-iso' {Γ} A B)

  field
    -- morally: σ ⋆ ⟨ IdSubst {Δ} , a ⟩ ≡ ⟨ IdSubst {Γ} , a [ σ ] ⟩ ⋆ ⟨ σ , A ⟩
    -- this should be provable
    ctxExtSubstSigmaSndEq : {Γ Δ : Ctx} (A : Ty Δ) (B : Ty (ctxExt Δ A)) (a : Tm Δ A) (σ : Subst Γ Δ) →
        ((B ∘Ty ctxExtSubst A IdSubst (subst⁻ (Tm Δ) (∘ᴾId C tyPresheaf A) a)) ∘Ty σ)
            ≡
        ((B ∘Ty ⟨ σ , A ⟩) ∘Ty ctxExtSubst (A ∘Ty σ) IdSubst (subst⁻ (Tm Γ) (∘ᴾId C tyPresheaf (A ∘Ty σ)) (a [ σ ])))

  Pairs : {Δ : Ctx} (A : Ty Δ) (B : Ty (ctxExt Δ A)) → Type ℓTm
  Pairs {Δ} A B = Σ[ a ∈ Tm Δ A ] Tm Δ (B ∘Ty ctxExtSubst A IdSubst (subst⁻ (Tm Δ) (∘ᴾId C tyPresheaf A) a))

  -- why can't I do copattern matching here?
  ArrowPairs : {Γ Δ : Ctx} (A : Ty Δ) (B : Ty (ctxExt Δ A)) (σ : Subst Γ Δ) → Pairs A B → Pairs (A ∘Ty σ) (B ∘Ty ⟨ σ , A ⟩)
  ArrowPairs {Γ} {Δ} A B σ pair = record {
      fst = pair .fst [ σ ];
      snd = subst (Tm Γ) (ctxExtSubstSigmaSndEq A B (pair .fst) σ) (pair .snd [ σ ])
      }

  field
    sig-iso-nat : {Γ Δ : Ctx} (A : Ty Δ) (B : Ty (ctxExt Δ A)) (x : Tm Δ (sig Δ A B)) (σ : Subst Γ Δ) →
        sig-iso (A ∘Ty σ) (B ∘Ty ⟨ σ , A ⟩) .fst (subst (Tm Γ) (sig-nat A B σ) (x [ σ ]))
            ≡
        (sig-iso A B .fst x .fst [ σ ] , subst (Tm Γ) (ctxExtSubstSigmaSndEq A B (sig-iso A B .fst x .fst) σ) (sig-iso A B .fst x .snd [ σ ]))
        -- ArrowPairs A B σ (sig-iso A B .fst x)
