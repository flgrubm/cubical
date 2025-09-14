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

open import Cubical.Data.IterativeSets.Base
open import Cubical.Data.IterativeSets.Pi
open import Cubical.Data.IterativeSets.Sigma
open import Cubical.Categories.Instances.IterativeSets

open CwF
open Functor

V-CwF : {ℓ : Level} → CwF (V {ℓ}) (ℓ-suc ℓ)
V-CwF .emptyContext = terminal-object-V

V-CwF .tyPresheaf .F-ob Γ .fst = El⁰ Γ → V⁰
V-CwF .tyPresheaf .F-ob _ .snd = isSet→ thm12
V-CwF .tyPresheaf .F-hom f = _∘ f
V-CwF .tyPresheaf .F-id = refl
V-CwF .tyPresheaf .F-seq _ _ = refl

V-CwF .tmPresheaf .F-ob (Γ , A) .fst = Lift ((x : El⁰ Γ) → El⁰ (A x))
V-CwF .tmPresheaf .F-ob (Γ , A) .snd = isOfHLevelLift 2 (isSetΠ (λ x → thm17 (A x)))
V-CwF .tmPresheaf .F-hom {Γ₁ , A₁} {Γ₂ , A₂} h = {!!}
V-CwF .tmPresheaf .F-id = {!!}
V-CwF .tmPresheaf .F-seq = {!!}

V-CwF .ctxExt .F-ob (Γ , A) = Σ⁰ Γ A
V-CwF .ctxExt .F-hom = {!!}
V-CwF .ctxExt .F-id = {!!}
V-CwF .ctxExt .F-seq = {!!}
