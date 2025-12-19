-- {-# OPTIONS --safe #-}

module Cubical.Categories.WithFamilies.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category
open import Cubical.Categories.Limits.Terminal
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation
open import Cubical.Categories.Presheaf
open import Cubical.Categories.Functor
open import Cubical.Foundations.Univalence

import Cubical.Categories.Constructions.Elements as Els -- renaming (Covariant.∫ to ∫)
open Els.Contravariant
open import Cubical.Categories.Constructions.BinProduct

open import Cubical.Categories.Functors.HomFunctor

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Transport
-- open import Cubical.Categories.NaturalTransformation
open import Cubical.Foundations.Function

private
  variable
    ℓ ℓ' : Level

open Category
open Functor

-- TODO: try to use more PathP

-- check universe levels
record CwF (C : Category ℓ ℓ') (ℓTy ℓTm : Level) : Type (ℓ-suc (ℓ-max (ℓ-max (ℓ-max ℓ ℓ') ℓTy) ℓTm)) where

    Ctx : Type ℓ
    Ctx = C .ob

    Subst : Ctx → Ctx → Type ℓ'
    Subst = C .Hom[_,_]

    IdSubst : {Γ : Ctx} → Subst Γ Γ
    IdSubst = C .id

    field
        emptyContext : Terminal C

    ⟨⟩ : Ctx
    ⟨⟩ = emptyContext .fst

    field
        tyPresheaf : Presheaf C ℓTy

    ∫Ty : Category (ℓ-max ℓ ℓTy) (ℓ-max ℓ' ℓTy)
    ∫Ty = ∫ᴾ tyPresheaf

    Ty : Ctx → Type ℓTy
    Ty Γ = (tyPresheaf ⟅ Γ ⟆) .fst

    _∘Ty_ : {Γ Δ : Ctx} → Ty Δ → Subst Γ Δ → Ty Γ
    A ∘Ty γ = A ∘ᴾ⟨ tyPresheaf ⟩ γ

    field
        tmPresheaf : Presheaf ∫Ty ℓTm

    Tm : (Γ : Ctx) → Ty Γ → Type ℓTm
    Tm Γ A = (tmPresheaf ⟅ Γ , A ⟆) .fst

    _[_] : {Γ Δ : Ctx} {A : Ty Δ} → Tm Δ A → (σ : Subst Γ Δ) → Tm Γ (A ∘Ty σ)
    _[_] M γ = M ∘ᴾ⟨ tmPresheaf ⟩ (γ , refl)

    field
        ctxExtFunctor : Functor ∫Ty C

    ctxExt : (Γ : Ctx) → Ty Γ → Ctx
    ctxExt Γ A = ctxExtFunctor ⟅ Γ , A ⟆

    ⟨_,_⟩ : {Γ Δ : Ctx} (σ : Subst Γ Δ) (A : Ty Δ) → Subst (ctxExt Γ (A ∘Ty σ)) (ctxExt Δ A)
    ⟨_,_⟩ σ _ = ctxExtFunctor ⟪ σ , refl ⟫
    -- ⟨_,_⟩ {Γ} {Δ} σ A = ctxExtFunctor .F-hom {x = Γ , A ∘Ty σ} {y = Δ , A} (σ , refl)

    field
        ctxExtEquiv : (Γ Δ : Ctx) (A : Ty Δ) → Subst Γ (ctxExt Δ A) ≃ (Σ[ σ ∈ Subst Γ Δ ] Tm Γ (A ∘Ty σ))

    ctxExtSubst : {Γ Δ : Ctx} (A : Ty Δ) (σ : Subst Γ Δ) → Tm Γ (A ∘Ty σ) → Subst Γ (ctxExt Δ A)
    ctxExtSubst {Γ} {Δ} A σ a = invEq (ctxExtEquiv Γ Δ A) (σ , a)

    wk : {Γ : Ctx} (A : Ty Γ) → Subst (ctxExt Γ A) Γ
    wk {Γ} a = (ctxExtEquiv (ctxExt Γ a) Γ a .fst) IdSubst .fst

    q : {Γ : Ctx} (A : Ty Γ) → Tm (ctxExt Γ A) (A ∘Ty (wk A))
    q {Γ} A = (ctxExtEquiv (ctxExt Γ A) Γ A .fst) IdSubst .snd

    ctxExtSubst-n : {Γ : Ctx} (A : Ty Γ) → ctxExtSubst A (wk A) (q A) ≡ IdSubst
    ctxExtSubst-n {Γ} A = retEq (ctxExtEquiv (ctxExt Γ A) Γ A) IdSubst

    field
        -- as PathP
        ctxExtEquivNat :
            (Γ Γ' Δ : Ctx) (A : Ty Δ) (σ : Subst Γ Γ') (τ : Subst Γ' (ctxExt Δ A)) →
            (ctxExtEquiv Γ Δ A .fst (σ ⋆⟨ C ⟩ τ)) ≡
            (σ ⋆⟨ C ⟩ (ctxExtEquiv Γ' Δ A .fst τ .fst) ,
            subst⁻ (Tm Γ) (∘ᴾAssoc C tyPresheaf A (ctxExtEquiv Γ' Δ A .fst τ .fst) σ) ((ctxExtEquiv Γ' Δ A .fst τ .snd) [ σ ]))

        t1 :
            (Γ Γ' Δ : Ctx) (A : Ty Δ) (σ : Subst Γ Γ') (τ : Subst Γ' (ctxExt Δ A)) →
            ctxExtEquiv Γ Δ A .fst (σ ⋆⟨ C ⟩ τ) .fst ≡
            σ ⋆⟨ C ⟩ (ctxExtEquiv Γ' Δ A .fst τ .fst)

        -- remove t2
        t2 :
            (Γ Γ' Δ : Ctx) (A : Ty Δ) (σ : Subst Γ Γ') (τ : Subst Γ' (ctxExt Δ A)) →
            PathP (λ i → Tm Γ (A ∘Ty (t1 Γ Γ' Δ A σ τ i)))
            (ctxExtEquiv Γ Δ A .fst (σ ⋆⟨ C ⟩ τ) .snd)
            (subst⁻ (Tm Γ) (∘ᴾAssoc C tyPresheaf A (ctxExtEquiv Γ' Δ A .fst τ .fst) σ) ((ctxExtEquiv Γ' Δ A .fst τ .snd) [ σ ]))
        t3 :
            (Γ Γ' Δ : Ctx) (A : Ty Δ) (σ : Subst Γ Γ') (τ : Subst Γ' (ctxExt Δ A)) →
            PathP (λ i → Tm Γ (((λ k → A ∘Ty (t1 Γ Γ' Δ A σ τ k)) ∙ ∘ᴾAssoc C tyPresheaf A (ctxExtEquiv Γ' Δ A .fst τ .fst) σ) i))
            (ctxExtEquiv Γ Δ A .fst (σ ⋆⟨ C ⟩ τ) .snd)
            (ctxExtEquiv Γ' Δ A .fst τ .snd [ σ ])


        -- test1 : (Γ Γ' Δ : Ctx) (A : Ty Δ) (σ : Subst Γ Γ') (τ : Subst Γ' (ctxExt Δ A)) →
        --     (ctxExtEquiv Γ Δ A .fst (σ ⋆⟨ C ⟩ τ)) ≡ 
        --     subst⁻ (λ X → Σ (C .Hom[_,_] Γ Δ) (λ _ → Tm Γ X)) (∘ᴾAssoc C tyPresheaf A (ctxExtEquiv Γ' Δ A .fst τ .fst) σ) (σ ⋆⟨ C ⟩ (ctxExtEquiv Γ' Δ A .fst τ .fst) , (ctxExtEquiv Γ' Δ A .fst τ .snd [ σ ]))
        -- test :
        --     (Γ Γ' Δ : Ctx) (A : Ty Δ) (σ : Subst Γ Γ') (τ : Subst Γ' (ctxExt Δ A)) →
        --     PathP (λ i → Σ (C .Hom[_,_] Γ Δ) λ γ → Tm Γ {!∘ᴾAssoc C tyPresheaf A (ctxExtEquiv Γ' Δ A .fst τ .fst) σ (~ i)!})
        --         (ctxExtEquiv Γ Δ A .fst (σ ⋆⟨ C ⟩ τ))
        --         (σ ⋆⟨ C ⟩ (ctxExtEquiv Γ' Δ A .fst τ .fst) , ctxExtEquiv Γ' Δ A .fst τ .snd [ σ ])



    -- these should be provable
    field
        ctxExtSubstComp :{Γ Δ Δ' : Ctx} (A : Ty Δ') (a : Tm Δ' A) (τ : Subst Δ Δ') (σ : Subst Γ Δ) →
            Path (Subst Γ (ctxExt Δ' A)) (σ ⋆⟨ C ⟩ ctxExtSubst A τ (a [ τ ])) (ctxExtSubst A (σ ⋆⟨ C ⟩ τ) (a [ σ ⋆⟨ C ⟩ τ ]))
        -- σ should be something else, maybe Γ → ctxExt Δ (A ∘Ty τ)
        ctxExtComp :{Γ Δ Δ' : Ctx} (A : Ty Δ') (τ : Subst Δ Δ') (σ : Subst Γ Δ) →
          Path (Subst (ctxExt Γ (A ∘Ty (σ ⋆⟨ C ⟩ τ))) (ctxExt Δ' A))
            (subst⁻ (λ X → Subst (ctxExt Γ X) (ctxExt Δ' A)) (∘ᴾAssoc C tyPresheaf A τ σ) (⟨ σ , A ∘Ty τ ⟩ ⋆⟨ C ⟩ ⟨ τ , A ⟩))
            ⟨ σ ⋆⟨ C ⟩ τ , A ⟩
