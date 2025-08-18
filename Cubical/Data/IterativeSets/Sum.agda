module Cubical.Data.IterativeSets.Sum where

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude

open import Cubical.Data.Sigma
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Functions.Embedding
open import Cubical.Data.Sum renaming (rec to ⊎-rec)
open import Cubical.Relation.Nullary using (¬_)

open import Cubical.Data.IterativeSets.Base
open import Cubical.Data.IterativeSets.Empty
open import Cubical.Data.IterativeSets.Unit

private
    variable
        ℓ : Level
        
-- TODO: remove private module once the performance issues with ordered and unordered pairs have been resolved
private
    module _ where
        postulate ⟨_,_⟩⁰ : V⁰ {ℓ} → V⁰ {ℓ} → V⁰ {ℓ}

        orderedPair⁰ : (V⁰ {ℓ} × V⁰ {ℓ}) → V⁰ {ℓ}
        orderedPair⁰ = uncurry ⟨_,_⟩⁰

        postulate isEmbOrderedPair⁰ : isEmbedding (orderedPair⁰ {ℓ})

        postulate orderedPair⁰≡orderedPair⁰ : {x y a b : V⁰ {ℓ}} → ((⟨ x , y ⟩⁰ ≡ ⟨ a , b ⟩⁰) ≃ ((x ≡ a) × (y ≡ b)))

private
    module _ where
        empty⁰≢unit⁰ : ¬ empty⁰ {ℓ} ≡ unit⁰ {ℓ}
        empty⁰≢unit⁰ {ℓ} p = ⊥*≢Unit* (cong El⁰ p)

private
    module _ {x y : V⁰ {ℓ}} where
        fl : El⁰ x → V⁰ {ℓ}
        fl a = ⟨ empty⁰ , tilde-0' x a ⟩⁰

        fr : El⁰ y → V⁰ {ℓ}
        fr b = ⟨ unit⁰ , tilde-0' y b ⟩⁰
        
        f : El⁰ x ⊎ El⁰ y → V⁰ {ℓ}
        f = ⊎-rec fl fr

        embfl : isEmbedding fl
        embfl = compEmbedding ((curry orderedPair⁰ empty⁰) , (lem26 thm12 empty⁰ orderedPair⁰ isEmbOrderedPair⁰)) ((tilde-0' x) , (isEmbedding-tilde-0 x)) .snd

        embfr : isEmbedding fr
        embfr = compEmbedding ((curry orderedPair⁰ unit⁰) , (lem26 thm12 unit⁰ orderedPair⁰ isEmbOrderedPair⁰)) ((tilde-0' y) , (isEmbedding-tilde-0 y)) .snd

        fla≢frb : (a : El⁰ x) (b : El⁰ y) → ¬ fl a ≡ fr b
        fla≢frb a b fla≡frb = empty⁰≢unit⁰ (orderedPair⁰≡orderedPair⁰ .fst fla≡frb .fst)

        femb : isEmbedding f
        femb = lem27 fl fr embfl embfr fla≢frb

_+⁰_ : V⁰ {ℓ} → V⁰ {ℓ} → V⁰ {ℓ}
x +⁰ y = sup⁰ ((El⁰ x ⊎ El⁰ y) , ((f {x = x} {y = y} , femb {x = x} {y = y})))

El⁰+⁰Is⊎ : {x y : V⁰ {ℓ}} → El⁰ (x +⁰ y) ≡ El⁰ x ⊎ El⁰ y
El⁰+⁰Is⊎ = refl
