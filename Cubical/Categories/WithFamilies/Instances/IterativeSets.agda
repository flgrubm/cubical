module Cubical.Categories.WithFamilies.Instances.IterativeSets where

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude

open import Cubical.Categories.WithFamilies.Base
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


open import Cubical.Data.IterativeSets.Base
open import Cubical.Data.IterativeSets.Pi
open import Cubical.Data.IterativeSets.Sigma
open import Cubical.Categories.Instances.IterativeSets

open import Cubical.Categories.Presheaf
open import Cubical.Categories.Functor

import Cubical.Categories.Constructions.Elements as Els -- renaming (Covariant.∫ to ∫)
open Els.Contravariant

open Category
open CwF
open Functor

V-CwF : {ℓ : Level} → CwF (V {ℓ}) (ℓ-suc ℓ) (ℓ-suc ℓ)

V-CwF .emptyContext = terminal-object-V

V-CwF .tyPresheaf .F-ob Γ .fst = El⁰ Γ → V⁰
V-CwF .tyPresheaf .F-ob _ .snd = isSet→ thm12
V-CwF .tyPresheaf .F-hom f g x = g (f x)
V-CwF .tyPresheaf .F-id = refl
V-CwF .tyPresheaf .F-seq _ _ = refl

V-CwF .tmPresheaf .F-ob x .fst = Lift ((t : El⁰ (x .fst)) → El⁰ (x .snd t))
V-CwF .tmPresheaf .F-ob x .snd = isOfHLevelLift 2 (isSetΠ (λ t → thm17 (x .snd t)))
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
        p≡r∙q = thm12 _ _ p (r ∙ q)

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
        p≡r∙q = thm12 _ _ p (r ∙ q)

        goal : subst El⁰ p (t .snd) ≡ subst El⁰ q (subst El⁰ r (t .snd))
        goal = cong (λ a → subst El⁰ a (t .snd)) p≡r∙q ∙ substComposite El⁰ r q (t .snd)
    in goal))

V-CwF .ctxExtEquiv Γ Δ a = isoToEquiv isom
    where
        isom : Iso _ _
        isom .Iso.fun f = (λ x → fst (f x)) , lift (λ x → snd (f x))
        -- the following doesn't work for some reason
        -- isom .Iso.fun f .fst = (λ x → fst (f x))
        -- isom .Iso.fun f .snd = lift (λ x → snd (f x))
        isom .Iso.inv (f , g) A .fst = f A
        isom .Iso.inv (f , g) A .snd = g .lower A
        isom .Iso.rightInv (f , g) = refl
        isom .Iso.leftInv f = refl

V-CwF .ctxExtEquivNat Δ Δ' Γ A δ γ = ΣPathP (refl , {!!})
-- subst⁻ (λ a → Lift ((x : El⁰ Δ') → El⁰ (a x))) (∘ᴾAssoc V (V-CwF .tyPresheaf) A (λ x → fst (γ x)) δ) (action (∫ᴾ V-CwF .tyPresheaf) (V-CwF .tmPresheaf) (δ , refl) (lift (λ x → snd (γ x))))
