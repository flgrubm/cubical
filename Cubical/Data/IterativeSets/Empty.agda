module Cubical.Data.IterativeSets.Empty where

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude

open import Cubical.Data.Empty renaming (elim* to ⊥*-elim ; elim to ⊥-elim)
open import Cubical.Functions.Embedding

open import Cubical.Data.IterativeMultisets.Base
open import Cubical.Data.IterativeSets.Base

private
  variable
    ℓ : Level
    x : V⁰ {ℓ}

private
  module _ where
    ¬_ : Type ℓ → Type ℓ
    ¬ A = A → ⊥

empty⁰ : V⁰ {ℓ}
empty⁰ .fst = emptySet-∞
empty⁰ .snd .fst ()
empty⁰ .snd .snd ()

empty⁰' : V⁰ {ℓ}
empty⁰' {ℓ} = sup⁰ e
    where
        e : Σ[ A ∈ Type ℓ ] A ↪ V⁰ {ℓ}
        e .fst = ⊥*
        e .snd .fst ()
        e .snd .snd ()

El⁰empty⁰Is⊥* : El⁰ {ℓ} empty⁰ ≡ ⊥* {ℓ}
El⁰empty⁰Is⊥* = refl

empty⁰-is-empty : ¬ (x ∈⁰ empty⁰)
empty⁰-is-empty (⊥-inh , _) = ⊥*-elim ⊥-inh
