module Cubical.Data.IterativeSets.Bool where

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude

open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Functions.Embedding
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma

-- TODO: remove ⊥*-elim, Data.Unit, Data.SumFin once the statements that need them have found their way to a better place
open import Cubical.Data.Empty renaming (elim* to ⊥*-elim ; elim to ⊥-elim)
open import Cubical.Data.Bool
open import Cubical.Data.SumFin

open import Cubical.Data.IterativeSets.Base
open import Cubical.Data.IterativeSets.UnorderedPair
open import Cubical.Data.IterativeSets.Empty
open import Cubical.Data.IterativeSets.Unit

private
  variable
    ℓ : Level

private
  module _ where
    ¬_ : Type ℓ → Type ℓ
    ¬ A = A → ⊥

bool⁰ : V⁰ {ℓ}
bool⁰ {ℓ} = unorderedPair⁰ empty⁰ unit⁰ empty⁰≢unit⁰

bool⁰IsBool : El⁰ {ℓ} bool⁰ ≡ Bool* {ℓ}
bool⁰IsBool = refl

empty⁰≢unit⁰ : (empty⁰ {ℓ} ≡ unit⁰ {ℓ}) → ⊥
empty⁰≢unit⁰ {ℓ} p = ⊥*≢Unit* (sym El⁰empty⁰Is⊥* ∙ (cong El⁰ p) ∙ El⁰unit⁰IsUnit*)

unit⁰≢empty⁰ : (unit⁰ {ℓ} ≡ empty⁰ {ℓ}) → ⊥
unit⁰≢empty⁰ {ℓ} p = Unit*≢⊥* (sym El⁰unit⁰IsUnit* ∙ (cong El⁰ p) ∙ El⁰empty⁰Is⊥*)
