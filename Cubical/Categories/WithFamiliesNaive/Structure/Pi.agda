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

open import Cubical.Categories.WithFamilies.Base

module Cubical.Categories.WithFamilies.Structure.Pi where

record Π-Structure-CwF {ℓ ℓ' ℓTy ℓTm : Level} {C : Category ℓ ℓ'} (cwf : CwF C ℓTy ℓTm) : Type ((ℓ-suc (ℓ-max (ℓ-max (ℓ-max ℓ ℓ') ℓTy) ℓTm))) where
    open CwF cwf

    field
        Π : {Γ : Ctx} (A : Ty Γ) (B : Ty (ctxExt Γ A)) → Ty Γ
        Π-natural : {Δ Γ : Ctx} (A : Ty Γ) (B : Ty (ctxExt Γ A)) (σ : Subst Δ Γ) → (Π A B) ∘Ty σ ≡ Π (A ∘Ty σ) (B ∘Ty ⟨ σ , A ⟩)

        iso-Π : {Γ : Ctx} (A : Ty Γ) (B : Ty (ctxExt Γ A)) → Tm Γ (Π A B) ≃ Tm (ctxExt Γ A) B

    -- app : {Γ : Ctx} (A : Ty Γ) (B : Ty (ctxExt Γ A)) → Tm Γ (Π A B) → Tm Γ (Π A B)
    -- app A B = iso-Π A B .fst

    -- lam : {Γ : Ctx} (A : Ty Γ) (B : Ty (ctxExt Γ A)) → Tm Γ (Π A B) → Tm Γ (Π A B) 
    -- lam A B = invEq (iso-Π A B)

