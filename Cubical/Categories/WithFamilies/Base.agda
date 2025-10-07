-- {-# OPTIONS --safe #-}

module Cubical.Categories.WithFamilies.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category
open import Cubical.Categories.Limits.Terminal
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation
open import Cubical.Categories.Presheaf
open import Cubical.Categories.Functor

import Cubical.Categories.Constructions.Elements as Els -- renaming (Covariant.∫ to ∫)
open Els.Contravariant

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
    a ∘Ty γ = a ∘ᴾ⟨ C , tyPresheaf ⟩ γ

    field
        tmPresheaf : Presheaf ∫Ty ℓTm

    Tm : (Γ : Ctx) → Ty Γ → Type ℓTm
    Tm Γ a = (tmPresheaf ⟅ Γ , a ⟆) .fst

    _[_] : {Δ Γ : Ctx} {a : Ty Γ} (M : Tm Γ a) (γ : Subst Δ Γ) → Tm Δ (a ∘Ty γ)
    _[_] {Δ} {Γ} {a} M γ = M ∘ᴾ⟨ ∫Ty , tmPresheaf ⟩ (γ , refl)

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
            (Δ Δ' Γ : Ctx) (A : Ty Γ) (δ : Subst Δ' Δ) →
            (γ : Subst Δ (ctxExt Γ A)) →
            (ctxExtEquiv Δ' Γ A .fst (δ ⋆⟨ C ⟩ γ)) ≡
            (δ ⋆⟨ C ⟩ (ctxExtEquiv Δ Γ A .fst γ .fst) ,
            subst⁻ (Tm Δ') (∘ᴾAssoc C tyPresheaf A _ δ) ((ctxExtEquiv Δ Γ A .fst γ .snd) [ δ ]))
