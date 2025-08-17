module Cubical.Data.IterativeSets.Sigma where

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Functions.Embedding
open import Cubical.Foundations.Equiv

open import Cubical.Data.Sigma

open import Cubical.Data.IterativeSets.Base

private
  variable
    ℓ : Level
    x : V⁰ {ℓ}
    y : El⁰ x → V⁰ {ℓ}

-- TODO: remove private module once the performance issues have been resolved
private
    module _ where
        postulate ⟨_,_⟩⁰ : V⁰ {ℓ} → V⁰ {ℓ} → V⁰ {ℓ}

        orderedPair⁰ : (V⁰ {ℓ} × V⁰ {ℓ}) → V⁰ {ℓ}
        orderedPair⁰ = uncurry ⟨_,_⟩⁰

        postulate isEmbOrderedPair⁰ : isEmbedding (orderedPair⁰ {ℓ})

        postulate orderedPair⁰≡orderedPair⁰ : {x y a b : V⁰ {ℓ}} → ((⟨ x , y ⟩⁰ ≡ ⟨ a , b ⟩⁰) ≃ ((x ≡ a) × (y ≡ b)))

module _ {ℓA ℓB ℓC ℓD : Level} {A : Type ℓA} {B : A → Type ℓB} {C : Type ℓC} {D : C → Type ℓD} {f : A → C} {g : (a : A) → B a → D (f a)} where
    Σfg : Σ A B → Σ C D
    Σfg (a , _) .fst = f a
    Σfg (a , b) .snd = g a b
    postulate isEmbeddingΣ : isEmbedding f → ((a : A) → isEmbedding (g a)) → isEmbedding Σfg

private
    module _ {ℓ : Level} (x : V⁰ {ℓ}) (y : El⁰ x → V⁰ {ℓ}) where
        emb : (Σ[ a ∈ El⁰ x ] El⁰ (y a)) ↪ V⁰ {ℓ}
        emb .fst (a , b) = ⟨ (tilde-0' x a) , (tilde-0' (y a) b) ⟩⁰
        emb .snd = isEmbedding-∘ isEmbOrderedPair⁰ (isEmbeddingΣ (isEmbedding-tilde-0 x) λ a → isEmbedding-tilde-0 (y a))
        
Σ⁰ : (x : V⁰ {ℓ}) → (El⁰ x → V⁰ {ℓ}) → V⁰ {ℓ}
Σ⁰ {ℓ = ℓ} x y = sup⁰ ((Σ[ a ∈ El⁰ {ℓ} x ] El⁰ {ℓ} (y a)) , emb x y)

El⁰Σ⁰IsΣ : {x : V⁰ {ℓ}} {y : El⁰ x → V⁰ {ℓ}} → El⁰ (Σ⁰ x y) ≡ (Σ (El⁰ x) (λ a → El⁰ (y a)))
El⁰Σ⁰IsΣ = refl

-- Corollary 25
_×⁰_ : V⁰ {ℓ} → V⁰ {ℓ} → V⁰ {ℓ}
x ×⁰ y = Σ⁰ x (λ _ → y)

El⁰×⁰Is× : {x y : V⁰ {ℓ}} → El⁰ (x ×⁰ y) ≡ ((El⁰ x) × (El⁰ y))
El⁰×⁰Is× = refl
