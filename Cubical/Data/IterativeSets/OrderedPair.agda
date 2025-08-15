module Cubical.Data.IterativeSets.OrderedPair where

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude

open import Cubical.Functions.Embedding
open import Cubical.Data.Sigma

open import Cubical.Data.IterativeSets.Base

private
  variable
    ℓ : Level

postulate orderedPair : (V⁰ {ℓ} × V⁰ {ℓ}) → V⁰ {ℓ}

⟨_,_⟩ : V⁰ {ℓ} → V⁰ {ℓ} → V⁰ {ℓ}
⟨ x , y ⟩ = orderedPair (x , y)

postulate isEmbOrderedPair' : (V⁰ {ℓ} × V⁰ {ℓ}) ↪ V⁰ {ℓ}

-- ⟨ x , y ⟩ = orderedPair .fst (x , y)

