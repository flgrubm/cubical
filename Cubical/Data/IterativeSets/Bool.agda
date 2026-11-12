module Cubical.Data.IterativeSets.Bool where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Bool

open import Cubical.Data.IterativeSets.Base
open import Cubical.Data.IterativeSets.UnorderedPair.Base
open import Cubical.Data.IterativeSets.Empty
open import Cubical.Data.IterativeSets.Unit
open import Cubical.Data.IterativeSets.Singleton.Properties

private
  variable
    ℓ : Level

bool⁰ : V⁰ {ℓ}
bool⁰ {ℓ} = unorderedPair⁰ empty⁰ unit⁰ empty⁰≢unit⁰

El⁰bool⁰IsBool* : El⁰ {ℓ} bool⁰ ≡ Bool* {ℓ}
El⁰bool⁰IsBool* = refl
