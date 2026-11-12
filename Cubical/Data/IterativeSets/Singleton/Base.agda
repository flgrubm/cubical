-- This module provides singletons {x} of iterative sets

module Cubical.Data.IterativeSets.Singleton.Base where

open import Cubical.Foundations.Prelude

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Path
open import Cubical.Data.Unit
open import Cubical.Functions.Embedding

open import Cubical.Data.IterativeSets.Base

private
  variable
    ℓ : Level
    x : V⁰ {ℓ}

-- opaque (here and for the other codes), as unfolding this proof is very expensive
private
  opaque
    isEmbedding-const : (x : V⁰ {ℓ}) → isEmbedding (λ (_ : Unit* {ℓ}) → x)
    isEmbedding-const x = isEmbedding-isProp→isSet isPropUnit* isSetV⁰ _

singleton⁰ : V⁰ {ℓ} → V⁰ {ℓ}
singleton⁰ {ℓ} x = fromEmb E
  where
    E : Embedding (V⁰ {ℓ}) ℓ
    E .fst = Unit*
    E .snd .fst _ = x
    E .snd .snd = isEmbedding-const x

El⁰singleton⁰IsUnit* : El⁰ (singleton⁰ x) ≡ Unit*
El⁰singleton⁰IsUnit* = refl

singleton⁰-is-singleton : {x z : V⁰ {ℓ}} → ((z ∈⁰ (singleton⁰ x)) ≃ (x ≡ z))
singleton⁰-is-singleton {x = x} {z = z} = isoToEquiv isom
  where
    isom : Iso (z ∈⁰ singleton⁰ x) (x ≡ z)
    isom .Iso.fun = snd
    isom .Iso.inv _ .fst = tt*
    isom .Iso.inv p .snd = p
    isom .Iso.ret _ = refl
    isom .Iso.sec _ = refl

singleton⁰-is-singleton-sym : {x z : V⁰ {ℓ}} → ((z ∈⁰ (singleton⁰ x)) ≃ (z ≡ x))
singleton⁰-is-singleton-sym = compEquiv singleton⁰-is-singleton (isoToEquiv symIso)

singleton⁰≡singleton⁰ : {x y : V⁰ {ℓ}} → ((x ≡ y) ≃ (singleton⁰ x ≡ singleton⁰ y))
singleton⁰≡singleton⁰ {ℓ} {x} {y} = propBiimpl→Equiv (isSetV⁰ x y)
                                                     (isSetV⁰ (singleton⁰ x) (singleton⁰ y))
                                                     (cong singleton⁰)
                                                     inv
  where
    inv : singleton⁰ x ≡ singleton⁰ y → x ≡ y
    inv p = singleton⁰-is-singleton {x = x} {z = y} .fst
              (≡V⁰-≃-≃V⁰ {x = singleton⁰ x} {y = singleton⁰ y} .fst p .snd y (tt* , refl))
