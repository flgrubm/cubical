module Cubical.Data.IterativeSets.Identity where

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude

open import Cubical.Functions.Embedding

open import Cubical.Data.IterativeSets.Base
open import Cubical.Data.IterativeSets.Empty

private
    variable
        ℓ : Level
        
private
    function-from-isProp-to-isSet→isEmbedding : {ℓ ℓ' : Level} {A : Type ℓ} {B : Type ℓ'} (f : A → B) → isProp A → isSet B → isEmbedding f
    function-from-isProp-to-isSet→isEmbedding f propA setB = injEmbedding setB (λ {w} {x} _ → propA w x)

private
    module _ {x : V⁰ {ℓ}} {a b : El⁰ x} where
        f : a ≡ b → V⁰ {ℓ}
        f _ = empty⁰

        femb : isEmbedding f
        femb = function-from-isProp-to-isSet→isEmbedding f (thm17 x a b) thm12

Id⁰ : (x : V⁰ {ℓ}) (a b : El⁰ x) → V⁰ {ℓ}
Id⁰ x a b = sup⁰ ((a ≡ b) , (f {x = x} , femb {x = x}))

El⁰Id⁰IsId : {x : V⁰ {ℓ}} {a b : El⁰ x} → El⁰ (Id⁰ x a b) ≡ (a ≡ b)
El⁰Id⁰IsId = refl
