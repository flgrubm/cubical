-- This module provides the Von-Neumann encoding of the natural numbers
-- i.e. 0 = ∅, suc n = n ⊎ {n}

module Cubical.Data.IterativeSets.Nat where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Functions.Embedding
open import Cubical.Data.Empty using (uninhabEquiv)
open import Cubical.Data.Unit
open import Cubical.Data.Nat
open import Cubical.Data.Fin as Fin
open import Cubical.Data.Sum as ⊎ using (_⊎_ ; isEmbeddingPair ; ⊎-equiv ; ⊎-swap-≃)

open import Cubical.Data.IterativeSets.Base
open import Cubical.Data.IterativeSets.Empty

private
  variable
    ℓ : Level

private
  opaque
    isEmbedding-suc⁰ : (x : V⁰ {ℓ})
                     → isEmbedding (⊎.rec (elements x) (λ (_ : Unit* {ℓ}) → x))
    isEmbedding-suc⁰ x = isEmbeddingPair (elements x) (λ _ → x)
                           (isEmbedding-elements x)
                           (isEmbedding-isProp→isSet isPropUnit* isSetV⁰ (λ _ → x))
                           (λ a _ p → ∈⁰-irrefl (a , p))

-- suc x = x ⊎ {x}
suc⁰ : {ℓ : Level} → V⁰ {ℓ} → V⁰ {ℓ}
suc⁰ {ℓ} x = fromEmb E
  where
    E : Embedding (V⁰ {ℓ}) ℓ
    E .fst = El⁰ x ⊎ Unit* {ℓ}
    E .snd .fst = ⊎.rec (elements x) (λ _ → x)
    E .snd .snd = isEmbedding-suc⁰ x

vonNeumannEncoding : ℕ* {ℓ} → V⁰ {ℓ}
vonNeumannEncoding (lift zero) = empty⁰
vonNeumannEncoding (lift (suc x)) = suc⁰ (vonNeumannEncoding (lift x))

El⁰-suc⁰≡El⁰⊎Unit* : {x : V⁰ {ℓ}} → El⁰ {ℓ} (suc⁰ x) ≡ (El⁰ x ⊎ Unit* {ℓ})
El⁰-suc⁰≡El⁰⊎Unit* = refl

El⁰-vNE-suc≡El⁰-vNE⊎Unit* : (n : ℕ) → El⁰ {ℓ} (vonNeumannEncoding (lift (suc n)))
                                      ≡ (El⁰ {ℓ} (vonNeumannEncoding (lift n))) ⊎ Unit* {ℓ}
El⁰-vNE-suc≡El⁰-vNE⊎Unit* n = El⁰-suc⁰≡El⁰⊎Unit* {x = vonNeumannEncoding (lift n)}

El⁰-vNE-suc≃El⁰-vNE⊎Unit* : (n : ℕ) → El⁰ {ℓ} (vonNeumannEncoding (lift (suc n)))
                                      ≃ (El⁰ {ℓ} (vonNeumannEncoding (lift n))) ⊎ Unit* {ℓ}
El⁰-vNE-suc≃El⁰-vNE⊎Unit* = pathToEquiv ∘ El⁰-vNE-suc≡El⁰-vNE⊎Unit*

-- the von-Neumann encoding of `n` is precisely a finite set with `n` elements
vonNeumannindex≃Fin : (n : ℕ) → (El⁰ (vonNeumannEncoding {ℓ} (lift n)) ≃ Fin n)
vonNeumannindex≃Fin zero = uninhabEquiv (λ ()) ¬Fin0
vonNeumannindex≃Fin {ℓ} (suc n) =
  El⁰ (vonNeumannEncoding (lift (suc n)))
    ≃⟨ El⁰-vNE-suc≃El⁰-vNE⊎Unit* n ⟩
  El⁰ (vonNeumannEncoding (lift n)) ⊎ Unit* {ℓ}
    ≃⟨ ⊎-equiv (vonNeumannindex≃Fin n) (compEquiv (invEquiv LiftEquiv) Unit≃Fin1) ⟩
  Fin n ⊎ Fin 1
    ≃⟨ ⊎-swap-≃ ⟩
  Fin 1 ⊎ Fin n
    ≃⟨ isoToEquiv Iso-Fin1⊎Fin-FinSuc ⟩
  Fin (suc n) ■

private
  opaque
    isEmbedding-vonNeumannEncoding : isEmbedding (vonNeumannEncoding {ℓ})
    isEmbedding-vonNeumannEncoding {ℓ} = injEmbedding isSetV⁰ (λ {w} {x} → isinj w x)
      where
        isinj : (w x : ℕ* {ℓ}) → vonNeumannEncoding w ≡ vonNeumannEncoding x → w ≡ x
        isinj (lift n) (lift m) p =
          liftExt (Fin-inj n m (ua (compEquiv (invEquiv (vonNeumannindex≃Fin n))
                                              (compEquiv (pathToEquiv (cong index p))
                                                         (vonNeumannindex≃Fin m)))))

ℕ⁰ : V⁰ {ℓ}
ℕ⁰ {ℓ} = fromEmb E
  where
    E : Embedding (V⁰ {ℓ}) ℓ
    E .fst = ℕ* {ℓ}
    E .snd .fst = vonNeumannEncoding {ℓ}
    E .snd .snd = isEmbedding-vonNeumannEncoding

El⁰ℕ⁰Isℕ* : El⁰ (ℕ⁰ {ℓ}) ≡ ℕ* {ℓ}
El⁰ℕ⁰Isℕ* = refl
