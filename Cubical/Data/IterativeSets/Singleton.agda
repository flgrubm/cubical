module Cubical.Data.IterativeSets.Singleton where

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Unit

open import Cubical.Data.IterativeSets.Base

private
  variable
    ℓ : Level
    x : V⁰ {ℓ}

singleton⁰ : V⁰ {ℓ} → V⁰ {ℓ}
singleton⁰ x = sup⁰ (Unit* , (λ _ → x) , isEmbeddingFunctionFromIsPropToIsSet _ isPropUnit* thm12)

El⁰singleton⁰IsUnit* : El⁰ (singleton⁰ x) ≡ Unit*
El⁰singleton⁰IsUnit* = refl

singleton⁰-is-singleton : {x z : V⁰ {ℓ}} → ((z ∈⁰ (singleton⁰ x)) ≃ (x ≡ z))
singleton⁰-is-singleton {x = x} {z = z} = isoToEquiv (iso f g sec ret)
    where
        f : z ∈⁰ singleton⁰ x → x ≡ z
        f (_ , p) = p
        g : x ≡ z → z ∈⁰ singleton⁰ x
        g p .fst = _
        g p .snd = p
        sec : section f g
        sec _ = refl
        ret : retract f g
        ret _ = refl
