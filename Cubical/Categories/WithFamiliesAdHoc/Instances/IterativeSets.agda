{-# OPTIONS --lossy-unification #-}

open import Cubical.Core.Everything
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
-- open import Cubical.Data.IterativeSets.Pi
open import Cubical.Data.IterativeSets.Sigma
open import Cubical.Categories.Instances.IterativeSets
open import Cubical.Categories.NewWithFamilies.Base
-- open import Cubical.Categories.WithFamilies.Structure.Pi
open import Cubical.Categories.NewWithFamilies.Structure.Sigma

open import Cubical.Categories.Presheaf
open import Cubical.Categories.Functor

import Cubical.Categories.Constructions.Elements as Els -- renaming (Covariant.∫ to ∫)
open Els.Contravariant

open Functor
module Cubical.Categories.NewWithFamilies.Instances.IterativeSets where

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

V-CwF .ctxExtEquiv _ _ _ = isoToEquiv isom1
    where
        isom1 : Iso _ (Σ _ _)
        isom1 .Iso.fun f .fst x = fst (f x)
        isom1 .Iso.fun f .snd = lift (λ x → f x .snd)
        isom1 .Iso.inv f A .fst = f .fst A
        isom1 .Iso.inv f A .snd = f .snd .lower A
        isom1 .Iso.rightInv _ = refl
        isom1 .Iso.leftInv _ = refl

V-CwF .special-ty-rev-assoc-proof _ _ _ _ _ _ x = x
V-CwF .ctxExtEquivNat Γ Γ' _ A σ τ = ΣPathP (refl , 
    let
       goal : lift (λ x → (τ (σ x)) .snd) ≡ action (V-CwF .tmPresheaf) (σ , refl) (lift (λ x → snd (τ x)))
       goal = cong lift (funExt (λ x → sym (substRefl {B = El⁰} (τ (σ x) .snd))))
    in goal)


open Σ-Structure-CwF

V-Σ-Structure : {ℓ : Level} → Σ-Structure-CwF (V-CwF {ℓ})
V-Σ-Structure {ℓ} .idsubst-action _ x = x
V-Σ-Structure {ℓ} .sig Γ A B x = Σ⁰ (A x) (λ a → B (x , a))
V-Σ-Structure {ℓ} .sig-nat A B σ = funExt (λ x → cong (Σ⁰ (A (σ x))) (funExt (λ a → cong (λ t → B (σ x , t)) (sym (substRefl {B = El⁰} a)))))
V-Σ-Structure {ℓ} .sig-iso {Γ} A B = isoToEquiv isom2
    where
        isom2 : Iso (Tm V-CwF Γ (V-Σ-Structure .sig Γ A B))
                   (Σ[ a ∈ Tm V-CwF Γ A ] Tm V-CwF Γ ((V-CwF ∘Ty B) (ctxExtSubst V-CwF A (IdSubst V-CwF) (V-Σ-Structure .idsubst-action A a))))
        isom2 .Iso.fun t .fst .lower x = t .lower x .fst
        isom2 .Iso.fun t .snd .lower x = t .lower x .snd
        isom2 .Iso.inv t .lower x .fst = t .fst .lower x
        isom2 .Iso.inv t .lower x .snd = t .snd .lower x
        isom2 .Iso.rightInv _ = refl
        isom2 .Iso.leftInv _ = refl
V-Σ-Structure {ℓ} .ctxExtSubstSigmaSndEq {Γ} A B a σ = funExt (λ x → 
    let
       p : B (σ x , a .lower (σ x)) ≡ B (σ x , subst⁻ El⁰ (refl {x = A (σ x)}) (a .lower (σ x)))
       p i = B (σ x , substRefl {B = El⁰} {x = A (σ x)} (a .lower (σ x)) (~ i))
       
       q : B (σ x , subst⁻ El⁰ (refl {x = A (σ x)}) (a .lower (σ x)))
            ≡
           B (σ x , subst⁻ El⁰ (refl {x = A (σ x)}) (subst⁻ El⁰ (refl {x = A (σ x)}) (a .lower (σ x))))
       q i = B (σ x , subst⁻ El⁰ (refl {x = A (σ x)}) (substRefl {B = El⁰} {x = A (σ x)} (a .lower (σ x)) (~ i)))
    in p ∙ q)

V-Σ-Structure {ℓ} .sig-iso-nat {Γ} A B a σ =
    let

        -- p' : (x : El⁰ Γ) → subst (Tm V-CwF Γ) (funExt (λ x₁ i → Σ⁰ (A (σ x₁)) (funExt (λ a₁ i₁ → B (σ x₁ , substRefl a₁ (~ i₁))) i))) ((V-CwF [ a ]) σ) .lower x .fst ≡ subst El⁰ (refl {x = A (σ x)}) (a .lower (σ x) .fst)
        p' : (x : El⁰ Γ) → subst (Tm V-CwF Γ) (λ i x → Σ⁰ (A (σ x)) (λ a₁ → B (σ x , substRefl a₁ (~ i)))) (_[_] V-CwF a σ) .lower x .fst ≡ subst El⁰ (refl {x = A (σ x)}) (a .lower (σ x) .fst)
        p' x = cong (λ M → M .lower x .fst) (substRefl {B = Tm V-CwF Γ} ((V-CwF [ a ]) σ))
        
        hhhh : Path
            (Lift ((t : El⁰ Γ) → El⁰ ((V-CwF ∘Ty (λ z → V-Σ-Structure .sig _ A B z)) σ t)))
            (_[_] V-CwF a σ)
            (lift (λ x → subst El⁰ (refl {x = Σ⁰ (A (σ x)) (λ a₁ → B (σ x , a₁))}) (a .lower (σ x))))
        hhhh = refl

        p : Path (Tm V-CwF Γ (_∘Ty_ V-CwF A σ))
             (lift
                (λ x → subst (Tm V-CwF Γ) refl (lift (λ x → subst El⁰ (refl {x = Σ⁰ (A (σ x)) (λ a₁ → B (σ x , a₁))}) (a .lower (σ x)))) .lower x .fst))
             (lift
                (λ x → subst El⁰ refl (a .lower (σ x) .fst)))
             -- (lift (λ x → subst El⁰ refl (a .lower (σ x) .fst)))
        p i = lift (λ x → substRefl {B = Tm V-CwF Γ} (_[_] V-CwF a σ) i .lower x .fst)
        -- p i = lift (λ x → substRefl {B = Tm V-CwF Γ} (lift (λ x → subst El⁰ (refl {x = Σ⁰ (A (σ x)) (λ a₁ → B (σ x , a₁))}) (a .lower (σ x)))) i .lower x .fst)
        -- cong lift (funExt p')
{-
Goal: transport
      (λ i →
         Tm V-CwF Γ
         ((V-CwF ∘Ty (V-CwF ∘Ty B) (⟨ V-CwF , σ ⟩ A))
          (ctxExtSubst V-CwF ((V-CwF ∘Ty A) σ) (IdSubst V-CwF)
           (lift
            (funExt (λ x i₁ → substRefl ((V-CwF [ a ]) σ) i₁ .lower x .fst)
             i)))))
      (Iso.fun
       (Cubical.Categories.NewWithFamilies.Instances.IterativeSets.isom2
        ((V-CwF ∘Ty A) σ) ((V-CwF ∘Ty B) (⟨ V-CwF , σ ⟩ A)))
       (subst (Tm V-CwF Γ)
        (funExt
         (λ x i →
            Σ⁰ (A (σ x)) (funExt (λ a₁ i₁ → B (σ x , substRefl a₁ (~ i₁))) i)))
        ((V-CwF [ a ]) σ))
       .snd)
      ≡
      subst (Tm V-CwF Γ)
      (funExt
       (λ x →
          (λ i → B (σ x , substRefl (a .lower (σ x) .fst) (~ i))) ∙
          (λ i →
             B
             (σ x ,
              subst⁻ El⁰ (λ _ → A (σ x))
              (substRefl (a .lower (σ x) .fst) (~ i))))))
      ((V-CwF [
        Iso.fun
        (Cubical.Categories.NewWithFamilies.Instances.IterativeSets.isom2 A
         B)
        a .snd
        ])
       σ)
       p
-}
        rr : _[_] (V-CwF {ℓ}) a σ ≡ lift (λ x → subst El⁰ (refl {x = Σ⁰ (A (σ x)) (λ a₁ → B (σ x , a₁))}) (a .lower (σ x)))
        rr = refl
        
        q' :
            subst (Tm V-CwF Γ)
            (λ i x → B (σ x , subst El⁰ refl (p' x i)))
            (lift (λ x → subst (Tm V-CwF Γ)
               (λ i x →
                    Σ⁰ (A (σ x)) ((λ a₁ → B (σ x , substRefl a₁ (~ i)))))
              (lift (λ x → subst El⁰ (refl {x = Σ⁰ (A (σ x)) (λ a₁ → B (σ x , a₁))}) (a .lower (σ x)))) .lower x .snd))
            ≡
            subst (Tm V-CwF Γ)
            (V-Σ-Structure {ℓ} .ctxExtSubstSigmaSndEq A B (lift (λ x → a .lower x .fst)) σ)
            (lift (λ x → subst El⁰ refl (a .lower (σ x) .snd)))
        q' = {!!}
        
        -- q : PathP (λ i → Tm V-CwF Γ {!!}) {!!} (subst (Tm V-CwF Γ) (V-Σ-Structure .ctxExtSubstSigmaSndEq A B (V-Σ-Structure .sig-iso A B .fst a .fst) σ) ((V-CwF [ V-Σ-Structure .sig-iso A B .fst a .snd ]) σ))
        -- q = toPathP q'
        -- {!subst (Tm V-CwF Γ) (V-Σ-Structure .ctxExtSubstSigmaSndEq A B (V-Σ-Structure .sig-iso A B .fst a .fst) σ) ((V-CwF [ V-Σ-Structure .sig-iso A B .fst a .snd ]) σ)!}
    in ΣPathP (p , toPathP q')
