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

singleton⁰-is-singleton-sym : {x z : V⁰ {ℓ}} → ((z ∈⁰ (singleton⁰ x)) ≃ (z ≡ x))
singleton⁰-is-singleton-sym {x = x} {z = z} = isoToEquiv (iso f g sec ret)
    where
        f : z ∈⁰ singleton⁰ x → z ≡ x
        f (_ , p) = sym p
        g : z ≡ x → z ∈⁰ singleton⁰ x
        g p .fst = _
        g p .snd = sym p
        sec : section f g
        sec _ = refl
        ret : retract f g
        ret _ = refl

singleton⁰≡singleton⁰ : {x y : V⁰ {ℓ}} → ((x ≡ y) ≃ (singleton⁰ x ≡ singleton⁰ y))
singleton⁰≡singleton⁰ {ℓ} {x} {y} = propBiimpl→Equiv (thm12 _ _) (thm12 _ _) (cong singleton⁰) g
    where
        thm4'-singleton⁰ : (singleton⁰ x ≡ singleton⁰ y) ≃ ((z : V⁰) → (z ≡ x) ≃ (z ≡ y))
        thm4'-singleton⁰ = compEquiv thm4' (equivΠCod (λ z → equivComp singleton⁰-is-singleton-sym singleton⁰-is-singleton-sym))
        g : singleton⁰ x ≡ singleton⁰ y → x ≡ y
        g p = thm4'-singleton⁰ .fst p x .fst refl
