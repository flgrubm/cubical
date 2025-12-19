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
open import Cubical.Categories.WithFamilies.Base
-- open import Cubical.Categories.WithFamilies.Structure.Pi
open import Cubical.Categories.WithFamilies.Structure.Sigma

open import Cubical.Categories.Presheaf
open import Cubical.Categories.Functor

import Cubical.Categories.Constructions.Elements as Els -- renaming (Covariant.∫ to ∫)
open Els.Contravariant

open Functor
module Cubical.Categories.WithFamilies.Instances.IterativeSets where

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

V-CwF .ctxExtEquivNat Γ Γ' _ A σ τ = ΣPathP (refl , cong lift (funExt (λ x → sym
    let
        p : transport
             (λ i → El⁰ (A (τ (σ (transp (λ j → El⁰ Γ) (i ∨ i0) x)) .fst)))
             (V-CwF .tmPresheaf .F-hom {Γ' , λ z → A (τ z .fst)} (σ , refl)
              (lift (λ y → τ y .snd)) .lower (transp (λ j → El⁰ Γ) i0 x))
             ≡
            transport
             (λ i → El⁰ (A (τ (σ (transp (λ j → El⁰ Γ) (i ∨ i1) x)) .fst)))
             (V-CwF .tmPresheaf .F-hom {Γ' , λ z → A (τ z .fst)} (σ , refl)
              (lift (λ y → τ y .snd)) .lower (transp (λ j → El⁰ Γ) i1 x))
        p k =
            transport
             (λ i → El⁰ (A (τ (σ (transp (λ j → El⁰ Γ) (i ∨ k) x)) .fst)))
             (V-CwF .tmPresheaf .F-hom {Γ' , λ z → A (τ z .fst)} (σ , refl)
              (lift (λ y → τ y .snd)) .lower (transp (λ j → El⁰ Γ) k x))
    in p ∙ transportRefl _ ∙ transportRefl _)))


V-CwF .t1 _ _ _ _ _ _ = refl

V-CwF .t2 Γ Γ' Δ A σ τ = cong snd (V-CwF .ctxExtEquivNat Γ Γ' Δ A σ τ)

V-CwF .t3 Γ Γ' Δ A σ τ = 
    let
        q : PathP (λ i → refl i) (V-CwF .ctxExtEquiv Γ Δ A .fst ((V ⋆ σ) τ) .snd) (action (V-CwF .tmPresheaf) (σ , refl) (V-CwF .ctxExtEquiv Γ' Δ A .fst τ .snd))
        q = cong lift (funExt λ x → sym (substRefl {B = El⁰} (τ (σ x) .snd)))

        goal : PathP
                (λ i → F-ob (V-CwF .tmPresheaf) (Γ , ((λ k → action (V-CwF .tyPresheaf) (V-CwF .t1 Γ Γ' Δ A σ τ k) A) ∙ ∘ᴾAssoc V (V-CwF .tyPresheaf) A (V-CwF .ctxExtEquiv Γ' Δ A .fst τ .fst) σ) i) .fst)
                (V-CwF .ctxExtEquiv Γ Δ A .fst ((V ⋆ σ) τ) .snd)
                (action (V-CwF .tmPresheaf) (σ , refl)
                 (V-CwF .ctxExtEquiv Γ' Δ A .fst τ .snd))
        goal = subst (λ m → PathP (λ i → V-CwF .tmPresheaf .F-ob (Γ , (m i)) .fst) (V-CwF .ctxExtEquiv Γ Δ A .fst ((V ⋆ σ) τ) .snd) (action (V-CwF .tmPresheaf) (σ , refl) (V-CwF .ctxExtEquiv Γ' Δ A .fst τ .snd))) compPathRefl q
    in goal

V-CwF .ctxExtSubstComp _ _ _ _ = refl

V-CwF .ctxExtComp {Γ} {Δ} {Δ'} A τ σ =
    substRefl {B = λ X → V .Hom[_,_] (V-CwF .ctxExtFunctor .F-ob (Γ , X)) (V-CwF .ctxExtFunctor .F-ob (Δ' , A))} _
        ∙ funExt (λ x → ΣPathP (refl ,
                                (substRefl {B = El⁰} _ ∙ substRefl {B = El⁰} _
                                 ∙ sym (substRefl {B = El⁰} _))))

-- V-Π-Structure : {ℓ : Level} → Π-Structure-CwF (V-CwF {ℓ})
-- V-Π-Structure .Π-Structure-CwF.Π {Γ} A B x = Π⁰ (A x) (λ a → B (x , a))
-- V-Π-Structure .Π-Structure-CwF.Π-natural A B σ = funExt (λ x → cong sup⁰ (cong (λ s → s , graph⁰) {!!})) -- funExt (λ x → {!!})
-- V-Π-Structure .Π-Structure-CwF.iso-Π = {!!}

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

-- V-Σ-Structure .sig-iso' = {!!}
V-Σ-Structure .ctxExtSubstSigmaSndEq {Γ} {Δ} A B a σ = funExt (λ x → 
    let
        goal' : B (σ x , a .lower (σ x))
                   ≡
                B (σ x , subst⁻ El⁰ refl (subst⁻ El⁰ refl (a .lower (σ x))))
        goal' = cong (λ m → B (σ x , m)) (sym (substRefl {B = El⁰} (a .lower (σ x))) ∙ cong (subst⁻ El⁰ refl) (sym (substRefl {B = El⁰} (a .lower (σ x)))))
        
        goal :
                -- ((V-CwF .tyPresheaf ⟪ ctxExtSubst V-CwF A (IdSubst V-CwF) (subst⁻ (Tm V-CwF Δ) refl a) ⟫) B) (σ x)
                B (ctxExtSubst V-CwF A (IdSubst V-CwF) (subst⁻ (Tm V-CwF Δ) refl a) (σ x))
                  ≡
                B (⟨_,_⟩ V-CwF σ A (ctxExtSubst V-CwF ((V-CwF ∘Ty A) σ) (IdSubst V-CwF) (subst⁻ (Tm V-CwF Γ) refl (_[_] V-CwF a σ)) x))
                -- ((V-CwF ∘Ty (V-CwF ∘Ty B) (⟨_,_⟩ V-CwF σ A)) (ctxExtSubst V-CwF ((V-CwF ∘Ty A) σ) (IdSubst V-CwF) (subst⁻ (Tm V-CwF Γ) refl (_[_] V-CwF a σ))) x)
        goal = cong (λ t → B (ctxExtSubst V-CwF A (IdSubst V-CwF) t (σ x))) (substRefl {B = Tm V-CwF Δ} a) ∙ goal' ∙ cong (λ s → B (⟨_,_⟩ V-CwF σ A (ctxExtSubst V-CwF ((V-CwF ∘Ty A) σ) (IdSubst V-CwF) s x))) (sym (substRefl {B = Tm V-CwF Γ} (_[_] V-CwF a σ)))

        -- p : B (σ x , subst⁻ (Tm V-CwF Δ) refl a .lower (σ x))
        --        ≡
        --     B (σ x , subst⁻ El⁰ refl (_[_] V-CwF a σ .lower x))
        -- p = cong (λ m → B (σ x , m)) (cong (λ n → n .lower (σ x)) (substRefl {B = Tm V-CwF Δ} a)
        --                                                             ∙ {!!} ∙ sym (substRefl {B = El⁰} (_[_] V-CwF a σ .lower x)))
        
        -- q :
        --         -- B (ctxExtSubst V-CwF A (IdSubst V-CwF) (subst⁻ (Tm V-CwF Δ) refl a) (σ x))
        --         -- B (σ x , subst⁻ (Tm V-CwF Δ) refl a .lower (σ x))
        --         -- B (σ x , (F-hom (ctxExtFunctor V-CwF)
        --         --             (σ , (λ _ → V-CwF .tyPresheaf .F-hom σ A))
        --         --             (x , (V-CwF [ a ]) σ .lower x) .snd))
        --         B (σ x , subst⁻ El⁰ refl (_[_] V-CwF a σ .lower x))
        --           ≡
        --         B (⟨ V-CwF , σ ⟩ A (x , subst⁻ (Tm V-CwF Γ) refl (_[_] V-CwF a σ) .lower x))
        -- q = cong (λ m → B (⟨ V-CwF , σ ⟩ A (x , m .lower x))) (sym (substRefl {B = Tm V-CwF Γ} (_[_] V-CwF a σ)))
    in goal)
-- subst (Tm V-CwF Γ) (funExt (λ x₁ i → Σ⁰ (A (σ x₁)) (funExt (λ a₁ i₁ → B (σ x₁ , substRefl a₁ (~ i₁))) i))) ((V-CwF [ a ]) σ) .lower x .fst
--       ≡ a .lower (σ x) .fst
    -- subst (Tm V-CwF Γ) (funExt (λ x₁ i → Σ⁰ (A (σ x₁)) (funExt (λ a₁ i₁ → B (σ x₁ , a₁)) i))) ((V-CwF [ a ]) σ) .lower x .fst
    --   ≡⟨⟩
    -- subst (Tm V-CwF Γ) (funExt (λ x₁ i → Σ⁰ (A (σ x₁)) (funExt (λ a → refl {x = B (σ x₁ , a)}) i))) ((V-CwF [ a ]) σ) .lower x .fst
    --   ≡⟨⟩ --  (λ j → subst (Tm V-CwF Γ) (funExt (λ x₁ i → Σ⁰ (A (σ x₁)) (funExtRefl' {f = λ a → B (σ x₁ , a)} j i))) ((V-CwF [ a ]) σ) .lower x .fst) ⟩
    -- subst (Tm V-CwF Γ) (funExt (λ x₁ i → Σ⁰ (A (σ x₁)) (refl {x = λ a → B (σ x₁ , a)} i))) ((V-CwF [ a ]) σ) .lower x .fst
    --   ≡⟨⟩
    -- subst (Tm V-CwF Γ) (funExt (λ x₁ i → Σ⁰ (A (σ x₁)) (λ a → B (σ x₁ , a)))) ((V-CwF [ a ]) σ) .lower x .fst
    --   ≡⟨⟩ --  cong (λ M → subst (Tm V-CwF Γ) M ((V-CwF [ a ]) σ) .lower x .fst) (funExtRefl' {f = λ x → Σ⁰ (A (σ x)) (λ a → B (σ x , a))}) ⟩
    -- subst (Tm V-CwF Γ) (refl {x = λ x₁ → Σ⁰ (A (σ x₁)) (λ a → B (σ x₁ , a))}) ((V-CwF [ a ]) σ) .lower x .fst
    --   ≡⟨ cong (λ M → M .lower x .fst) (substRefl {B = Tm V-CwF Γ} ((V-CwF [ a ]) σ)) ⟩
    -- (V-CwF [ a ]) σ .lower x .fst
    --   ≡⟨ transportRefl (a .lower (σ x) .fst) ⟩
    -- a .lower (σ x) .fst
    --   ∎
V-Σ-Structure .sig-iso-nat {Γ} {Δ} A B a σ = ΣPathP (cong lift (funExt (λ x → cong (λ M → M .lower x .fst)
      (substRefl {B = Tm V-CwF Γ} ((V-CwF [ a ]) σ))
        ∙∙ transportRefl (a .lower (σ x) .fst)
        ∙∙ sym (substRefl {B = El⁰} (V-Σ-Structure .sig-iso A B .fst a .fst .lower (σ x)))))
      , cong lift (funExt (λ (x : El⁰ Γ) → 
          let
-- Goal: subst⁻
--       (λ m → El⁰ ((V-CwF ∘Ty B) (⟨ V-CwF , σ ⟩ A) (x , m .lower x)))
--       (substRefl
--        (lift
--         (λ y →
--            subst (Tm V-CwF Γ)
--            (funExt
--             (λ x₁ i →
--                Σ⁰ (A (σ x₁))
--                (funExt (λ a₁ i₁ → B (σ x₁ , substRefl a₁ (~ i₁))) i)))
--            ((V-CwF [ a ]) σ) .lower y .fst)))
--       (subst (Tm V-CwF Γ)
--        (funExt
--         (λ x₁ i →
--            Σ⁰ (A (σ x₁))
--            (funExt (λ a₁ i₁ → B (σ x₁ , substRefl a₁ (~ i₁))) i)))
--        ((V-CwF [ a ]) σ) .lower x .snd)
--       ≡
--       transp
--       (λ i →
--          El⁰
--          (funExt
--           (λ x₁ →
--              (λ i₁ →
--                 B
--                 (ctxExtSubst V-CwF A (IdSubst V-CwF)
--                  (substRefl
--                   (Iso.fun
--                    (Cubical.Categories.WithFamilies.Instances.IterativeSets.isom A B)
--                    a .fst)
--                   i₁)
--                  (σ x₁)))
--              ∙
--              (λ i₁ →
--                 B
--                 (σ x₁ ,
--                  ((λ i₂ → substRefl (a .lower (σ x₁) .fst) (~ i₂)) ∙
--                   (λ i₂ →
--                      subst⁻ El⁰ (λ _ → A (σ x₁))
--                      (substRefl (a .lower (σ x₁) .fst) (~ i₂))))
--                  i₁))
--              ∙
--              (λ i₁ →
--                 B
--                 (⟨ V-CwF , σ ⟩ A
--                  (ctxExtSubst V-CwF ((V-CwF ∘Ty A) σ) (IdSubst V-CwF)
--                   (substRefl
--                    ((V-CwF [
--                      Iso.fun
--                      (Cubical.Categories.WithFamilies.Instances.IterativeSets.isom A B)
--                      a .fst
--                      ])
--                     σ)
--                    (~ i₁))
--                   x₁))))
--           i (transp (λ j → El⁰ Γ) i x)))
--       i0
--       ((V-CwF [
--         Iso.fun
--         (Cubical.Categories.WithFamilies.Instances.IterativeSets.isom A B)
--         a .snd
--         ])
--        σ .lower (transp (λ j → El⁰ Γ) i0 x))

    -- isom .Iso.fun t .fst .lower x = t .lower x .fst
    -- isom .Iso.fun t .snd .lower x = subst⁻ (λ m → El⁰ (B (x , m .lower x))) (substRefl {B = Tm V-CwF Δ} {x = A} (lift (λ y → t .lower y .fst)) ) (t .lower x .snd)
    -- arguments are A and B
                 {-
                 Iso.fun
                   (Cubical.Categories.WithFamilies.Instances.IterativeSets.isom
                    ((V-CwF ∘Ty A) σ) ((V-CwF ∘Ty B) (⟨ V-CwF , σ ⟩ A)))
                   (subst (Tm V-CwF Γ) (V-Σ-Structure .sig-nat A B σ) ((V-CwF [ a ]) σ))
                   .snd .lower
                  -}
              goal : {!!}
              goal =
                {!subst⁻ (λ m → El⁰ ((V-CwF ∘Ty B) (⟨ V-CwF , σ ⟩ A) (x , m .lower x))) (substRefl {B = Tm V-CwF Δ} {x = (V-CwF ∘Ty A) σ} (lift (λ y → (subst (Tm V-CwF Γ) (V-Σ-Structure .sig-nat A B σ) ((V-CwF [ a ]) σ))  .lower y .fst)) ) ((subst (Tm V-CwF Γ) (V-Σ-Structure .sig-nat A B σ) ((V-CwF [ a ]) σ)) .lower x .snd)!}
                    ≡⟨ {!!} ⟩
                {!!}
                    ∎
        in goal)))
      -- cong lift (funExt (λ x → 
      --   let
      --       goal : {!!} -- Path {!!} {!!} {!!}
      --       goal = {!!}
      --   in goal)))
