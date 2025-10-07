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
open import Cubical.Foundations.Transport
open import Cubical.Data.Sigma

open import Cubical.Data.IterativeSets.Base
open import Cubical.Data.IterativeSets.Pi
open import Cubical.Data.IterativeSets.Sigma
open import Cubical.Categories.Instances.IterativeSets

open Category V
open CwF
open Functor

V-CwF : {ℓ : Level} → CwF (V {ℓ}) (ℓ-suc ℓ) (ℓ-suc ℓ)

V-CwF .emptyContext = terminal-object-V

V-CwF .tyPresheaf .F-ob Γ .fst = El⁰ Γ → V⁰
V-CwF .tyPresheaf .F-ob _ .snd = isSet→ thm12
V-CwF .tyPresheaf .F-hom f g x = g (f x)
V-CwF .tyPresheaf .F-id = refl
V-CwF .tyPresheaf .F-seq _ _ = refl

-- use PathP more!
V-CwF .tmPresheaf .F-ob (Γ , A) .fst = Lift ((x : El⁰ Γ) → El⁰ (A x))
V-CwF .tmPresheaf .F-ob (_ , A) .snd = isOfHLevelLift 2 (isSetΠ (λ x → thm17 (A x)))
V-CwF .tmPresheaf .F-hom h x = lift (λ y → transport (cong El⁰ (funExt⁻ (h .snd) y)) (x .lower (h .fst y))) -- h : (Γ , A) → (Δ , B), x : (Lift …Γ…), y : El⁰ Δ
V-CwF .tmPresheaf .F-id = funExt (λ _ → cong lift (funExt (λ _ → transportRefl _)))
V-CwF .tmPresheaf .F-seq {Γ , A} {Δ , B} {Ε , D} (γ , p) (σ , q) = funExt (λ x → {!!}) -- J2 {!!} {!!} q p -- σ : El⁰ Ε → El⁰ Δ, γ : El⁰ Δ → El⁰ Γ

V-CwF .ctxExtFunctor .F-ob (Γ , A) = Σ⁰ Γ A
V-CwF .ctxExtFunctor .F-hom {Γ , A} {Δ , B} (γ , p) (x , a) .fst = γ x
V-CwF .ctxExtFunctor .F-hom {Γ , A} {Δ , B} (γ , p) (x , a) .snd = transport (cong El⁰ (funExt⁻ (sym p) x)) a
V-CwF .ctxExtFunctor .F-id {Γ , A} = funExt (λ (x , a) → ΣPathP (refl , (transportRefl a)))
V-CwF .ctxExtFunctor .F-seq {Γ , A} {Δ , B} {Ε , D} (γ , p) (σ , q) = funExt (λ (x , a) → ΣPathP (refl , transportComposite {!!} {!!} a)) -- {!transportComposite ? (cong El⁰ (funExt⁻ (sym p) x)) a!})) -- transportComposite {!!} {!!} a))

V-CwF .ctxExtEquiv = {!!}
V-CwF .ctxExtEquivNat = {!!}

-- V-CwF .ctxExt .F-ob (Γ , A) = Σ⁰ Γ A
-- V-CwF .ctxExt .F-hom = {!!}
-- V-CwF .ctxExt .F-id = {!!}
-- V-CwF .ctxExt .F-seq = {!!}
