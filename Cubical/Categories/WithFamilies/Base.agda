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

    _∘Ty_ : {Δ Γ : Ctx} (a : Ty Γ) (γ : Subst Δ Γ) → Ty Δ
    a ∘Ty γ = a ∘ᴾ⟨ tyPresheaf ⟩ γ

    field
        tmPresheaf : Presheaf ∫Ty ℓTm

    Tm : (Γ : Ctx) → Ty Γ → Type ℓTm
    Tm Γ a = (tmPresheaf ⟅ Γ , a ⟆) .fst

    _[_] : {Δ Γ : Ctx} {a : Ty Γ} (M : Tm Γ a) (γ : Subst Δ Γ) → Tm Δ (a ∘Ty γ)
    _[_] {Δ} {Γ} {a} M γ = M ∘ᴾ⟨ tmPresheaf ⟩ (γ , refl)

    field
        ctxExtFunctor : Functor ∫Ty C

    ctxExt : (Γ : Ctx) (a : Ty Γ) → Ctx
    ctxExt Γ a = ctxExtFunctor ⟅ Γ , a ⟆

    ⟨_,_⟩ : {Δ Γ : Ctx} (γ : Subst Δ Γ) (a : Ty Γ) → Subst (ctxExt Δ (a ∘Ty γ)) (ctxExt Γ a)
    ⟨_,_⟩ γ _ = ctxExtFunctor ⟪ γ , refl ⟫

    field
        ctxExtEquiv : (Δ Γ : Ctx) (a : Ty Γ) → Subst Δ (ctxExt Γ a) ≃ (Σ[ γ ∈ Subst Δ Γ ] Tm Δ (a ∘Ty γ))

    ctxExtSubst : {Δ Γ : Ctx} (a : Ty Γ) (γ : Subst Δ Γ) → Tm Δ (a ∘Ty γ) → Subst Δ (ctxExt Γ a)
    ctxExtSubst {Δ} {Γ} a γ M = invEq (ctxExtEquiv Δ Γ a) (γ , M)

    wk : {Γ : Ctx} (a : Ty Γ) → Subst (ctxExt Γ a) Γ
    wk {Γ} a = (ctxExtEquiv (ctxExt Γ a) Γ a .fst) IdSubst .fst

    q : {Γ : Ctx} (a : Ty Γ) → Tm (ctxExt Γ a) (a ∘Ty (wk a))
    q {Γ} a = (ctxExtEquiv (ctxExt Γ a) Γ a .fst) IdSubst .snd

    ctxExtSubst-n : {Γ : Ctx} (a : Ty Γ) → ctxExtSubst a (wk a) (q a) ≡ IdSubst
    ctxExtSubst-n {Γ} a = retEq (ctxExtEquiv (ctxExt Γ a) Γ a) IdSubst

    field
        -- as PathP
        ctxExtEquivNat :
            (Δ Δ' Γ : Ctx) (A : Ty Γ) (δ : Subst Δ' Δ) (γ : Subst Δ (ctxExt Γ A)) →
            (ctxExtEquiv Δ' Γ A .fst (δ ⋆⟨ C ⟩ γ)) ≡
            (δ ⋆⟨ C ⟩ (ctxExtEquiv Δ Γ A .fst γ .fst) ,
            subst⁻ (Tm Δ') (∘ᴾAssoc C tyPresheaf A _ δ) ((ctxExtEquiv Δ Γ A .fst γ .snd) [ δ ]))

    field
        ctxExtEquivNat₁ : (Δ Δ' Γ : Ctx) (A : Ty Γ) (δ : Subst Δ' Δ) (γ : Subst Δ (ctxExt Γ A)) →
            ctxExtEquiv Δ' Γ A .fst (δ ⋆⟨ C ⟩ γ) .fst ≡ δ ⋆⟨ C ⟩ (ctxExtEquiv Δ Γ A .fst γ .fst)
        

    -- field
    --     ctxExtEquivNat₂ : (Δ Δ' Γ : Ctx) (A : Ty Γ) (δ : Subst Δ' Δ) (γ : Subst Δ (ctxExt Γ A)) →
    --         PathP {!((ctxExtEquiv Δ Γ A .fst γ .snd) [ δ ])!} ((ctxExtEquiv Δ' Γ A .fst (δ ⋆⟨ C ⟩ γ)) .snd) ((ctxExtEquiv Δ Γ A .fst γ .snd) [ δ ])
-- Tm (Δ' , A ∙ (ctxExtEquiv Δ' Γ A .fst (δ ⋆⟨ C ⟩ γ) .fst)) .fst
-- Tm (Δ' , (A ∙ (ctxExtEquiv Δ Γ A .fst γ .fst))) ∙ δ) .fst

    -- hh : (Δ Δ' Γ : Ctx) (A : Ty Γ) (δ : Subst Δ' Δ) (γ : Subst Δ (ctxExt Γ A)) → tmPresheaf .F-ob
    --                                                                               (Δ' , ((A ∘Ty ctxExtEquiv Δ Γ A .fst γ .fst) ∘Ty δ))
    --                                                                               .fst
    -- hh Δ Δ' Γ A δ γ = (ctxExtEquiv Δ Γ A .fst γ .snd) [ δ ]

    -- gg : (Δ Δ' Γ : Ctx) (A : Ty Γ) (δ : Subst Δ' Δ) (γ : Subst Δ (ctxExt Γ A)) → F-ob tmPresheaf
    --                                                                               (Δ' , (A ∘Ty (δ ⋆⟨ C ⟩ ctxExtEquiv Δ Γ A .fst γ .fst)))
    --                                                                               .fst
    -- gg Δ Δ' Γ A δ γ = subst⁻ (Tm Δ') (∘ᴾAssoc C tyPresheaf A _ δ) ((ctxExtEquiv Δ Γ A .fst γ .snd) [ δ ])

    -- oo : (Δ Δ' Γ : Ctx) (A : Ty Γ) (δ : Subst Δ' Δ) (γ : Subst Δ (ctxExt Γ A)) → 
    --     Path (Type ℓTm)
    --         (Tm Δ' (A ∘Ty (δ ⋆⟨ C ⟩ ctxExtEquiv Δ Γ A .fst γ .fst)))
    --         (Tm Δ' ((A ∘Ty ctxExtEquiv Δ Γ A .fst γ .fst) ∘Ty δ))
    -- oo Δ Δ' Γ A δ γ = cong (Tm Δ') (∘ᴾAssoc C tyPresheaf A (ctxExtEquiv Δ Γ A .fst γ .fst) δ)

    -- work in progress
    -- testHom : Presheaf ((C ^op) ×C ∫Ty) ℓ'
    -- testHom = HomFunctor C ∘F ({!Id {C = C ^op}!} ×F {!ctxExtFunctor!})
