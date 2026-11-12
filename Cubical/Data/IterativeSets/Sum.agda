-- This module provides binary sums of iterative sets. The elements of the two summands are
-- tagged with ∅ and {∅}, i.e. inl a is encoded by ⟨ ∅ , a ⟩ and inr b by ⟨ {∅} , b ⟩

module Cubical.Data.IterativeSets.Sum where

open import Cubical.Foundations.Prelude

open import Cubical.Functions.Embedding
open import Cubical.Data.Sum as ⊎
open import Cubical.Relation.Nullary using (¬_)

open import Cubical.Data.IterativeSets.Base
open import Cubical.Data.IterativeSets.Empty
open import Cubical.Data.IterativeSets.Unit
open import Cubical.Data.IterativeSets.Singleton.Properties
open import Cubical.Data.IterativeSets.OrderedPair

private
    variable
        ℓ : Level

private
    module _ {x y : V⁰ {ℓ}} where
        fl : El⁰ x → V⁰ {ℓ}
        fl a = ⟨ empty⁰ , elements x a ⟩⁰

        fr : El⁰ y → V⁰ {ℓ}
        fr b = ⟨ unit⁰ , elements y b ⟩⁰

        f : El⁰ x ⊎ El⁰ y → V⁰ {ℓ}
        f = ⊎.rec fl fr

        embfl : isEmbedding fl
        embfl = isEmbedding-∘
                  (Embedding-×-fst-const isSetV⁰ empty⁰ orderedPair⁰ isEmbOrderedPair⁰)
                  (isEmbedding-elements x)

        embfr : isEmbedding fr
        embfr = isEmbedding-∘
                  (Embedding-×-fst-const isSetV⁰ unit⁰ orderedPair⁰ isEmbOrderedPair⁰)
                  (isEmbedding-elements y)

        fla≢frb : (a : El⁰ x) (b : El⁰ y) → ¬ fl a ≡ fr b
        fla≢frb a b fla≡frb = empty⁰≢unit⁰ (orderedPair⁰≡orderedPair⁰ .fst fla≡frb .fst)

        opaque
            femb : isEmbedding f
            femb = isEmbeddingPair fl fr embfl embfr fla≢frb

_+⁰_ : V⁰ {ℓ} → V⁰ {ℓ} → V⁰ {ℓ}
_+⁰_ {ℓ} x y = fromEmb E
  where
    E : Embedding (V⁰ {ℓ}) ℓ
    E .fst = El⁰ x ⊎ El⁰ y
    E .snd .fst = f {x = x} {y = y}
    E .snd .snd = femb {x = x} {y = y}

El⁰+⁰Is⊎ : {x y : V⁰ {ℓ}} → El⁰ (x +⁰ y) ≡ El⁰ x ⊎ El⁰ y
El⁰+⁰Is⊎ = refl
