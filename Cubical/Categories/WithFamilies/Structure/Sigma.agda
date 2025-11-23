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
    sig-iso' : {Γ : Ctx} (A : Ty Γ) (B : Ty (ctxExt Γ A)) →
        (Tm Γ (sig Γ A B)) ≃ (Σ[ a ∈ Tm Γ (A ∘Ty IdSubst) ] (Tm Γ (B ∘Ty ctxExtSubst A IdSubst a)))

  dest : {Γ : Ctx} (A : Ty Γ) (B : Ty (ctxExt Γ A)) →
        (Tm Γ (sig Γ A B)) → (Σ[ a ∈ Tm Γ A ] (Tm Γ (B ∘Ty ctxExtSubst A IdSubst (subst⁻ (Tm Γ) (∘ᴾId C tyPresheaf A) a))))
  dest {Γ} A B = sig-iso {Γ} A B .fst

  cons : {Γ : Ctx} (A : Ty Γ) (B : Ty (ctxExt Γ A)) →
         (Σ[ a ∈ Tm Γ A ] (Tm Γ (B ∘Ty ctxExtSubst A IdSubst (subst⁻ (Tm Γ) (∘ᴾId C tyPresheaf A) a)))) → (Tm Γ (sig Γ A B))
  cons {Γ} A B = invEq (sig-iso {Γ} A B)

  dest' : {Γ : Ctx} (A : Ty Γ) (B : Ty (ctxExt Γ A)) →
        (Tm Γ (sig Γ A B)) → (Σ[ a ∈ Tm Γ (A ∘Ty IdSubst) ] (Tm Γ (B ∘Ty ctxExtSubst A IdSubst a)))
  dest' {Γ} A B = sig-iso' {Γ} A B .fst

  cons' : {Γ : Ctx} (A : Ty Γ) (B : Ty (ctxExt Γ A)) →
        (Σ[ a ∈ Tm Γ (A ∘Ty IdSubst) ] (Tm Γ (B ∘Ty ctxExtSubst A IdSubst a))) → (Tm Γ (sig Γ A B))
  cons' {Γ} A B = invEq (sig-iso' {Γ} A B)

  private
    Σ-fun-snd-transport : {ℓA ℓB ℓC ℓD : Level} {A : Type ℓA} {B : A → Type ℓB} {B' : A → Type ℓD} {C : Type ℓC} {D : C → Type ℓD}
                        (f : A → C) (g : (a : A) → B a → B' a) → ((a : A) → B' a ≡ D (f a)) →
                        Σ A B → Σ C D
    Σ-fun-snd-transport {A = A} {B = B} {B' = B'} {C = C} {D = D} f g p x .fst = f (x .fst)
    Σ-fun-snd-transport {A = A} {B = B} {B' = B'} {C = C} {D = D} f g p x .snd = transport (p (x .fst)) (uncurry g x)

  private
    module _ where
      Pairs : Ctx → Type (ℓ-max ℓTy ℓTm)
      Pairs Δ = Σ[ A ∈ Ty Δ ] Σ[ B ∈ Ty (ctxExt Δ A) ] Σ[ a ∈ Tm Δ A ] Tm Δ (B ∘Ty ctxExtSubst A IdSubst (subst⁻ (Tm Δ) (∘ᴾId C tyPresheaf A) a))

      mapΣ : {ℓA ℓA' ℓB ℓB' : Level} {A : Type ℓA} {B : A → Type ℓB} {A' : Type ℓA'} {B' : A' → Type ℓB'} (f : A → A') → ((x : A) → B x → B' (f x)) → Σ A B → Σ A' B'
      mapΣ f g s .fst = f (s .fst)
      mapΣ f g s .snd = uncurry g s

      ArrowPairs : {Γ Δ : Ctx} (σ : Subst Γ Δ) → Pairs Δ → Pairs Γ
      ArrowPairs {Γ} {Δ} σ = mapΣ ty1 (λ A → mapΣ (ty2 A) λ B → mapΣ (tm1 A) λ a → tm2 A B a)
        where
          ty1 : Ty Δ → Ty Γ
          ty1 = _∘Ty σ

          ty2 : (A : Ty Δ) → Ty (ctxExt Δ A) → Ty (ctxExt Γ (A ∘Ty σ))
          ty2 A = _∘Ty ⟨ σ , A ⟩

          tm1 : (A : Ty Δ) → Tm Δ A → Tm Γ (A ∘Ty σ)
          tm1 A = _[ σ ]

          tm2 : (A : Ty Δ) (B : Ty (ctxExt Δ A)) (a : Tm Δ A) → Tm Δ (B ∘Ty ctxExtSubst A IdSubst (subst⁻ (Tm Δ) (∘ᴾId C tyPresheaf A) a)) →
                                                                 Tm Γ
                                                                 ((B ∘Ty ⟨ σ , A ⟩) ∘Ty
                                                                  ctxExtSubst (ty1 A) IdSubst
                                                                  (subst⁻ (Tm Γ) (∘ᴾId C tyPresheaf (ty1 A)) (tm1 A a)))
          tm2 A B a t = {!!}

          test1 : (A : Ty Δ) (B : Ty (ctxExt Δ A)) (a : Tm Δ A) → Ty Γ
          test1 A B a = B ∘Ty ctxExtSubst A σ (a [ σ ])

  private
    module _ {Γ Δ : Ctx} (σ : Subst Γ Δ) (A : Ty Δ) (a : Tm Γ (A ∘Ty σ)) where

      s1 : Subst {!!} {!!}
      s1 = (ctxExtSubst (A ∘Ty σ) (IdSubst {Γ}) (subst⁻ (Tm Γ) (∘ᴾId C tyPresheaf (A ∘Ty σ)) a)) ⋆ {!!}
    

  private
    module _ {Γ Δ : Ctx} (σ : Subst Γ Δ) (A : Ty Δ) (a : Tm Γ (A ∘Ty σ)) where

      δ : Subst Γ (ctxExt Δ A) -- Γ → Γ . (A ∘Ty σ) → Δ . A
      δ = (ctxExtSubst (A ∘Ty σ) IdSubst {!a!} {-(subst⁻ (Tm Γ) (∘ᴾId C tyPresheaf (A ∘Ty σ)) a)-}) ⋆ ⟨ σ , A ⟩

      -- δt : Σ[ γ' ∈ Subst Γ Δ ] Tm Γ (A ∘Ty γ')
      -- δt .fst = {!!}
      -- δt .snd = {!!}

      γ : Subst Γ (ctxExt Δ A)
      γ = ctxExtSubst A σ a

      γt : Σ[ γ' ∈ Subst Γ Δ ] Tm Γ (A ∘Ty γ')
      γt .fst = σ
      γt .snd = a
