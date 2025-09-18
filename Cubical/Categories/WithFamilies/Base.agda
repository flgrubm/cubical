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
open Els.Covariant

open import Cubical.Foundations.Equiv
-- open import Cubical.Categories.NaturalTransformation

private
  variable
    ℓ ℓ' : Level

open Category
open Functor

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
    ∫Ty = ∫ tyPresheaf

    Ty : Ctx → Type ℓTy
    Ty Γ = (tyPresheaf ⟅ Γ ⟆) .fst

    _∙Ty_ : {Δ Γ : Ctx} (A : Ty Γ) (γ : Subst Δ Γ) → Ty Δ
    A ∙Ty γ = A ∘ᴾ⟨ C , tyPresheaf ⟩ γ

    field
        tmPresheaf : Presheaf (∫ tyPresheaf) ℓTm

    Tm : (Γ : Ctx) → Ty Γ → Type ℓTm
    Tm Γ A = (tmPresheaf ⟅ Γ , A ⟆) .fst

    _[_] : {Δ Γ : Ctx} {A : Ty Γ} (M : Tm Γ A) (γ : Subst Δ Γ) → Tm Δ (A ∙Ty γ)
    _[_] {Δ} {Γ} {A} M γ = M ∘ᴾ⟨ (∫ tyPresheaf) , tmPresheaf ⟩ {!!} , {!!} -- ({!γ!} , {!!})


    -- field
    --     tmPresheaf : Presheaf (Covariant.∫ tyPresheaf) ℓS

    --     ctxExt : Functor (Covariant.∫ tyPresheaf) C

    --     naturalEquiv : (Δ : C .ob) ((Γ , A) : (Covariant.∫ tyPresheaf) .ob) → Hom[ C , Δ ] (ctxExt .F-ob (Γ , A)) ≃ (Σ[ γ ∈ (Hom[ C , Δ ] Γ) ] tmPresheaf .F-ob (Δ , {!γ A!}) .fst)
