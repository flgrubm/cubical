{-# OPTIONS --lossy-unification #-}

open import Cubical.Foundations.Prelude

open import Cubical.Categories.Functor.Base
open import Cubical.Foundations.HLevels
open import Cubical.Categories.Category.Base
open import Cubical.Categories.Instances.Sets
open import Cubical.Foundations.Function
open import Cubical.Categories.Constructions.Elements
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Transport
open import Cubical.Data.Sigma
open import Cubical.Functions.FunExtEquiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Path
open import Cubical.Foundations.GroupoidLaws
-- open import Cubical.Data.Equality.Conversion hiding (funExt)

open import Cubical.Data.IterativeSets.Base
open import Cubical.Data.IterativeSets.Sigma

open import Cubical.Categories.Instances.IterativeSets
open import Cubical.Categories.WithFamiliesCubical.Base
open import Cubical.Categories.WithFamiliesCubical.Structure.Sigma

open import Cubical.Categories.Presheaf
open import Cubical.Categories.Functor

import Cubical.Categories.Constructions.Elements as Els -- renaming (Covariant.∫ to ∫)
open Els.Contravariant

open Functor
module Cubical.Categories.WithFamiliesCubical.Instances.IterativeSets where

private
  variable
    ℓ : Level

open Category
open CwF

V-CwF : CwF (V {ℓ}) (ℓ-suc ℓ) (ℓ-suc ℓ)

V-CwF .emptyContext = terminal-object-V

V-CwF .tyPresheaf .F-ob Γ .fst = El⁰ Γ → V⁰
V-CwF .tyPresheaf .F-ob _ .snd = isSet→ isSetV⁰
V-CwF .tyPresheaf .F-hom f g x = g (f x)
V-CwF .tyPresheaf .F-id = refl
V-CwF .tyPresheaf .F-seq _ _ = refl

V-CwF .tmPresheaf .F-ob x .fst = Lift ((t : El⁰ (x .fst)) → El⁰ (x .snd t))
V-CwF .tmPresheaf .F-ob x .snd = isOfHLevelLift 2 (isSetΠ (λ t → isSetEl⁰ (x .snd t)))
V-CwF .tmPresheaf .F-hom f t = lift (λ x → subst El⁰ (funExt⁻ (f .snd) x) (t .lower (f .fst x)))
V-CwF .tmPresheaf .F-id = funExt (λ _ → cong lift (funExt (λ _ → transportRefl _)))
V-CwF .tmPresheaf .F-seq {x} {y} {z} f g = funExt (λ t → cong lift (funExt (λ s →
    let
        C = (∫ᴾ V-CwF .tyPresheaf) ^op

        mm : t .lower (seq' C {x} {y} {z} f g .fst s) ≡ t .lower (f .fst (g .fst s)) 
        mm = refl

        p : Path V⁰ (x .snd (f .fst (g .fst s))) (z .snd s)
        p = funExt⁻ (seq' C {x} {y} {z} f g .snd) s

        q : Path V⁰ (y .snd (g .fst s)) (z .snd s)
        q = funExt⁻ (g .snd) s

        r : Path V⁰ (x .snd (f .fst (g .fst s))) (y .snd (g .fst s))
        r = funExt⁻ (f .snd) (g .fst s)

        p≡r∙q : p ≡ r ∙ q
        p≡r∙q = isSetV⁰ _ _ p (r ∙ q)

        goal : Path (El⁰ (z .snd s))
                (subst El⁰ (funExt⁻ (seq' C {x} {y} {z} f g .snd) s)
                 (t .lower (f .fst (g .fst s))))
                (subst El⁰ (funExt⁻ (g .snd) s)
                 (subst El⁰ (funExt⁻ (f .snd) (g .fst s)) (t .lower (f .fst (g .fst s)))))
        goal = cong (λ a → subst El⁰ a (t .lower (f .fst (g .fst s)))) p≡r∙q ∙ substComposite El⁰ r q (t .lower (f .fst (g .fst s)))

    in goal)))

V-CwF .ctxExtFunctor .F-ob X = Σ⁰ (X .fst) (X .snd)
V-CwF .ctxExtFunctor .F-hom {x} {y} f t .fst = f .fst (t .fst)
V-CwF .ctxExtFunctor .F-hom {x} {y} f t .snd = subst⁻ El⁰ (funExt⁻ (f .snd) (t .fst)) (t .snd)
V-CwF .ctxExtFunctor .F-id = funExt (λ x → ΣPathP (refl , (transportRefl (x .snd))))
V-CwF .ctxExtFunctor .F-seq {x} {y} {z} f g = funExt (λ t → ΣPathP (refl ,
    let 
        C = ∫ᴾ V-CwF .tyPresheaf

        p : Path V⁰ (x .snd (t .fst)) (z .snd (g .fst (f .fst (t .fst))))
        p i = seq' C {x} {y} {z} f g .snd (~ i) (t .fst)

        q : Path V⁰ (y .snd (f .fst (t .fst))) (z .snd (g .fst (f .fst (t .fst))))
        q i = g .snd (~ i) (f .fst (t .fst))

        r : Path V⁰ (x .snd (t .fst)) (y .snd (f .fst (t .fst)))
        r i = f .snd (~ i) (t .fst)

        p≡r∙q : p ≡ r ∙ q
        p≡r∙q = isSetV⁰ _ _ p (r ∙ q)

        goal : subst El⁰ p (t .snd) ≡ subst El⁰ q (subst El⁰ r (t .snd))
        goal = cong (λ a → subst El⁰ a (t .snd)) p≡r∙q ∙ substComposite El⁰ r q (t .snd)
    in goal))

V-CwF .ctxExtEquiv Γ Δ a = isoToEquiv isom
    where
        isom : Iso _ _
        isom .Iso.fun f = (λ x → fst (f x)) , lift (λ x → snd (f x))
        isom .Iso.inv f A .fst = f .fst A
        isom .Iso.inv f A .snd = f .snd .lower A
        isom .Iso.rightInv _ = refl
        isom .Iso.leftInv _ = refl

V-CwF .ctxExtNat₁ _ _ _ _ _ _ = refl

V-CwF .ctxExtNat₂ Γ Γ' Δ A σ τ = 
    let
        q : PathP (λ i → refl i) (V-CwF .ctxExtEquiv Γ Δ A .fst ((V ⋆ σ) τ) .snd) (action (V-CwF .tmPresheaf) (σ , refl) (V-CwF .ctxExtEquiv Γ' Δ A .fst τ .snd))
        q = cong lift (funExt λ x → sym (substRefl {B = El⁰} (τ (σ x) .snd)))

        goal : PathP (λ i → F-ob (V-CwF .tmPresheaf) (Γ , (refl ∙ refl) i) .fst)
            (V-CwF .ctxExtEquiv Γ Δ A .fst (σ ⋆⟨ V ⟩ τ) .snd)
            (_[_] V-CwF (V-CwF .ctxExtEquiv Γ' Δ A .fst τ .snd) σ)
        goal = subst (λ m → PathP (λ i → V-CwF .tmPresheaf .F-ob (Γ , (m i)) .fst) (V-CwF .ctxExtEquiv Γ Δ A .fst ((V ⋆ σ) τ) .snd) (action (V-CwF .tmPresheaf) (σ , refl) (V-CwF .ctxExtEquiv Γ' Δ A .fst τ .snd))) compPathRefl q
    in goal

open Σ-Structure-CwF

V-Σ-Structure : {ℓ : Level} → Σ-Structure-CwF (V-CwF {ℓ})
V-Σ-Structure .sig Γ A B x = Σ⁰ (A x) (λ a → B (x , a))
V-Σ-Structure .sig-nat A B σ = funExt (λ x →
    cong (Σ⁰ (A (σ x)))
        (funExt (λ a → cong (λ t → B (σ x , t)) (sym (substRefl {B = El⁰} a)))))
V-Σ-Structure {ℓ} .sig-iso {Δ} A B = isoToEquiv isom
  where
    isom : Iso (Tm V-CwF Δ (V-Σ-Structure .sig Δ A B))
               (Σ-syntax (Tm V-CwF Δ A) (λ a → Tm V-CwF Δ ((V-CwF ∘Ty B) (ctxExtSubst V-CwF A (IdSubst V-CwF) (subst⁻ (Tm V-CwF Δ) (∘ᴾId V (tyPresheaf V-CwF) A) a)))))

    isom .Iso.fun t .fst .lower x = t .lower x .fst
    isom .Iso.fun t .snd .lower x = subst⁻ (λ m → El⁰ (B (x , m .lower x))) (substRefl {B = Tm V-CwF Δ} {x = A} (lift (λ y → t .lower y .fst)) ) (t .lower x .snd)

    isom .Iso.inv t .lower x .fst = t .fst .lower x
    isom .Iso.inv t .lower x .snd = subst (λ m → El⁰ (B (x , m .lower x))) (substRefl {B = Tm V-CwF Δ} (t .fst)) (t .snd .lower x)

    isom .Iso.rightInv t = ΣPathP (refl , cong lift (funExt (λ x → subst⁻Subst (λ m → El⁰ (B (x , m .lower x))) (substRefl {B = Tm V-CwF Δ} (t .fst)) (t .snd .lower x))))
    isom .Iso.leftInv t = cong lift (funExt (λ x → ΣPathP (refl , (substSubst⁻ (λ m → El⁰ (B (x , m .lower x))) (substRefl {B = Tm V-CwF Δ} {x = A} (lift (λ y → t .lower y .fst))) (snd (t .lower x))))))

V-Σ-Structure .ctxExtSubstSigmaSndEq {Γ} {Δ} A B a σ = funExt (λ x → 
    let
        goal' : B (σ x , a .lower (σ x))
                   ≡
                B (σ x , subst⁻ El⁰ refl (subst⁻ El⁰ refl (a .lower (σ x))))
        goal' = cong (λ m → B (σ x , m)) (sym (substRefl {B = El⁰} (a .lower (σ x))) ∙ cong (subst⁻ El⁰ refl) (sym (substRefl {B = El⁰} (a .lower (σ x)))))
        
        goal :
                B (ctxExtSubst V-CwF A (IdSubst V-CwF) (subst⁻ (Tm V-CwF Δ) refl a) (σ x))
                  ≡
                B (⟨_,_⟩ V-CwF σ A (ctxExtSubst V-CwF ((V-CwF ∘Ty A) σ) (IdSubst V-CwF) (subst⁻ (Tm V-CwF Γ) refl (_[_] V-CwF a σ)) x))
        goal = cong (λ t → B (ctxExtSubst V-CwF A (IdSubst V-CwF) t (σ x))) (substRefl {B = Tm V-CwF Δ} a) ∙∙ goal' ∙∙ cong (λ s → B (⟨_,_⟩ V-CwF σ A (ctxExtSubst V-CwF ((V-CwF ∘Ty A) σ) (IdSubst V-CwF) s x))) (sym (substRefl {B = Tm V-CwF Γ} (_[_] V-CwF a σ)))
    in goal)

V-Σ-Structure .sig-iso-nat {Γ} {Δ} A B a σ = ΣPathP (
    let
        h : (fst
              (V-Σ-Structure .sig-iso ((V-CwF ∘Ty A) σ)
               ((V-CwF ∘Ty B) (⟨ V-CwF , σ ⟩ A)) .fst
               (subst (Tm V-CwF Γ) (V-Σ-Structure .sig-nat A B σ)
                ((V-CwF [ a ]) σ))))
            ≡
            lift (λ x → subst (Tm V-CwF Γ) refl ((V-CwF [ a ]) σ) .lower x .fst) 
        h = refl

        g : lift (λ x → subst El⁰ refl (a .lower (σ x) .fst)) ≡ ((V-CwF [ V-Σ-Structure .sig-iso A B .fst a .fst ]) σ)
        g = refl

        p : lift (λ x → subst (Tm V-CwF Γ) refl ((V-CwF [ a ]) σ) .lower x .fst) ≡ lift (λ x → subst El⁰ refl (a .lower (σ x) .fst))
        p = cong lift (funExt (λ x → cong (λ M → M .lower x .fst) (substRefl {B = Tm V-CwF Γ} ((V-CwF [ a ]) σ))))

        q : {!!}
        q = {!!}
    in p , q)

-- Fully normalized goal:
-- Goal: PathP
--       (λ i →
--          Lift
--          ((t : Cubical.Data.W.W.nodes (fst Γ)) →
--           Cubical.Data.W.W.nodes
--           (fst
--            (B
--             (F-hom (ctxExtFunctor V-CwF) (σ , (λ _ x → A (σ x)))
--              (Iso.inv
--               (Cubical.Categories.WithFamiliesCubical.Instances.IterativeSets.isom
--                Γ Γ (λ x → A (σ x)))
--               ((λ x → x) ,
--                transp
--                (λ i₁ →
--                   Lift
--                   ((t₁ : Cubical.Data.W.W.nodes (fst Γ)) →
--                    Cubical.Data.W.W.nodes (fst (A (σ t₁)))))
--                i0
--                (lift
--                 (λ x →
--                    transp
--                    (λ i₁ →
--                       Cubical.Data.W.W.nodes
--                       (fst
--                        (A
--                         (σ (transp (λ j → Cubical.Data.W.W.nodes (fst Γ)) (i ∨ i₁) x)))))
--                    i
--                    (transp
--                     (λ i₁ →
--                        Cubical.Data.W.W.nodes
--                        (fst (A (σ (transp (λ j → Cubical.Data.W.W.nodes (fst Γ)) i x)))))
--                     i0
--                     (a .lower (σ (transp (λ j → Cubical.Data.W.W.nodes (fst Γ)) i x))
--                      .fst)))))
--               t))))))
--       (Iso.fun
--        (Cubical.Categories.WithFamiliesCubical.Instances.IterativeSets.isom
--         (λ x → A (σ x))
--         (λ x →
--            B (F-hom (ctxExtFunctor V-CwF) (σ , (λ _ x₁ → A (σ x₁))) x)))
--        (transp
--         (λ i →
--            Lift
--            ((t : Cubical.Data.W.W.nodes (fst Γ)) →
--             Σ (Cubical.Data.W.W.nodes (fst (A (σ t))))
--             (λ a₁ →
--                Cubical.Data.W.W.nodes
--                (fst
--                 (B
--                  (σ t ,
--                   transp (λ _ → Cubical.Data.W.W.nodes (fst (A (σ t)))) (~ i)
--                   a₁))))))
--         i0
--         (lift
--          (λ x →
--             transp
--             (λ i →
--                Σ (Cubical.Data.W.W.nodes (fst (A (σ x))))
--                (λ a₁ → Cubical.Data.W.W.nodes (fst (B (σ x , a₁)))))
--             i0 (a .lower (σ x)))))
--        .snd)
--       (transp
--        (λ i →
--           Lift
--           ((t : Cubical.Data.W.W.nodes (fst Γ)) →
--            Cubical.Data.W.W.nodes
--            (hcomp
--             (λ i₁ .o →
--                Cubical.Data.W.W.transpW (λ i₂ → Type ℓ) (λ i₂ x → x) i₁
--                (doubleComp-faces
--                 (λ i₂ →
--                    B
--                    (Iso.inv
--                     (Cubical.Categories.WithFamiliesCubical.Instances.IterativeSets.isom
--                      Δ Δ A)
--                     ((λ x → x) ,
--                      transp
--                      (λ _ →
--                         Lift
--                         ((t₁ : Cubical.Data.W.W.nodes (fst Δ)) →
--                          Cubical.Data.W.W.nodes (fst (A t₁))))
--                      i₂
--                      (Iso.fun
--                       (Cubical.Categories.WithFamiliesCubical.Instances.IterativeSets.isom
--                        A B)
--                       a .fst))
--                     (σ t)))
--                 (λ i₂ →
--                    B
--                    (F-hom (ctxExtFunctor V-CwF) (σ , (λ _ x → A (σ x)))
--                     (Iso.inv
--                      (Cubical.Categories.WithFamiliesCubical.Instances.IterativeSets.isom
--                       Γ Γ (λ x → A (σ x)))
--                      ((λ x → x) ,
--                       transp
--                       (λ _ →
--                          Lift
--                          ((t₁ : Cubical.Data.W.W.nodes (fst Γ)) →
--                           Cubical.Data.W.W.nodes (fst (A (σ t₁)))))
--                       (~ i₂)
--                       (lift
--                        (λ x →
--                           transp (λ i₃ → Cubical.Data.W.W.nodes (fst (A (σ x)))) i0
--                           (a .lower (σ x) .fst))))
--                      t)))
--                 i i₁ _ .fst))
--             (Cubical.Data.W.W.transpW (λ i₁ → Type ℓ) (λ i₁ x → x) i0
--              (B
--               (σ t ,
--                hcomp
--                (doubleComp-faces (λ _ → a .lower (σ t) .fst)
--                 (λ i₁ →
--                    transp (λ i₂ → Cubical.Data.W.W.nodes (fst (A (σ t)))) i0
--                    (transp (λ _ → Cubical.Data.W.W.nodes (fst (A (σ t)))) (~ i₁)
--                     (a .lower (σ t) .fst)))
--                 i)
--                (transp (λ _ → Cubical.Data.W.W.nodes (fst (A (σ t)))) (~ i)
--                 (a .lower (σ t) .fst)))
--               .fst)))))
--        i0
--        (lift
--         (λ x →
--            transp
--            (λ i →
--               Cubical.Data.W.W.nodes
--               (fst
--                (B
--                 (Iso.inv
--                  (Cubical.Categories.WithFamiliesCubical.Instances.IterativeSets.isom
--                   Δ Δ A)
--                  ((λ x₁ → x₁) ,
--                   transp
--                   (λ i₁ →
--                      Lift
--                      ((t : Cubical.Data.W.W.nodes (fst Δ)) →
--                       Cubical.Data.W.W.nodes (fst (A t))))
--                   i0
--                   (Iso.fun
--                    (Cubical.Categories.WithFamiliesCubical.Instances.IterativeSets.isom
--                     A B)
--                    a .fst))
--                  (σ x)))))
--            i0
--            (transp
--             (λ i →
--                Cubical.Data.W.W.nodes
--                (fst
--                 (B
--                  (σ x ,
--                   transp
--                   (λ i₁ →
--                      Cubical.Data.W.W.nodes
--                      (fst
--                       (A
--                        (transp (λ j → Cubical.Data.W.W.nodes (fst Δ)) (~ i ∨ i₁) (σ x)))))
--                   (~ i)
--                   (a .lower
--                    (transp (λ j → Cubical.Data.W.W.nodes (fst Δ)) (~ i) (σ x))
--                    .fst)))))
--             i0 (a .lower (σ x) .snd)))))
