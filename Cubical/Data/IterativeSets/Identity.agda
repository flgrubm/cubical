-- This module provides identity types of iterative sets. Every proof of a ≡ b is encoded by ∅,
-- so that a ≡ b is encoded by a set with at most one element

module Cubical.Data.IterativeSets.Identity where

open import Cubical.Foundations.Prelude

open import Cubical.Functions.Embedding

open import Cubical.Data.IterativeSets.Base
open import Cubical.Data.IterativeSets.Empty

private
    variable
        ℓ : Level

private
  opaque
    isEmbedding-const : (x : V⁰ {ℓ}) (a b : El⁰ x) → isEmbedding (λ (_ : a ≡ b) → empty⁰ {ℓ})
    isEmbedding-const x a b = isEmbedding-isProp→isSet (isSetEl⁰ x a b) isSetV⁰ _

Id⁰ : (x : V⁰ {ℓ}) (a b : El⁰ x) → V⁰ {ℓ}
Id⁰ x a b = fromEmb E
  where
    E : Embedding V⁰ _
    E .fst = a ≡ b
    E .snd .fst _ = empty⁰
    E .snd .snd = isEmbedding-const x a b

El⁰Id⁰IsId : {x : V⁰ {ℓ}} {a b : El⁰ x} → El⁰ (Id⁰ x a b) ≡ (a ≡ b)
El⁰Id⁰IsId = refl
