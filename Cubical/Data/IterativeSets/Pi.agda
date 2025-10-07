{-# OPTIONS --lossy-unification #-}
{-# OPTIONS --allow-unsolved-metas #-}


module Cubical.Data.IterativeSets.Pi where

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Data.Sigma
open import Cubical.Functions.Embedding
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Homotopy.Base

open import Cubical.Data.IterativeMultisets.Base
open import Cubical.Data.IterativeSets.Base
open import Cubical.Data.IterativeSets.OrderedPair


private
  variable
    ℓ : Level
    x : V⁰ {ℓ}
    y : El⁰ x → V⁰ {ℓ}

-- maybe require isSet or so
private
    module _ {ℓ ℓ' : Level} {A : Type ℓ} {B : Type ℓ'} {f g : A → B} (fibeq : (z : B) → fiber f z ≡ fiber g z) where
        t : (a : A) → Σ[ a' ∈ A ] g a' ≡ f a
        t a = transport (fibeq (f a)) (a , refl)

        q : (a : A) → PathP (λ i → fibeq (f a) i) (a , refl) (t a)
        q a = transport-filler (fibeq (f a)) (a , refl)

        -- s : (a : A) → {!!}
        -- s a = PathPΣ (q a)

        helper : (a : A) → f a ≡ g a
        helper a = {!!}

        fiberwise≡→≡ : f ≡ g
        fiberwise≡→≡ = funExt helper

module _ {x : V⁰ {ℓ}} {y : El⁰ x → V⁰ {ℓ}} where
    private
        module _ where
            emb : ((a : El⁰ x) → El⁰ (y a)) → (El⁰ x ↪ V⁰ {ℓ})
            emb ϕ .fst a = ⟨ tilde-0' x a , tilde-0' (y a) (ϕ a) ⟩⁰
            emb ϕ .snd = injEmbedding thm12 f
                where
                    f : {v w : El⁰ x} → emb ϕ .fst v ≡ emb ϕ .fst w → v ≡ w
                    f {v} {w} p = isEmbedding→Inj (isEmbedding-tilde-0 x) _ _ (orderedPair⁰≡orderedPair⁰ .fst p .fst)

            elem : ((a : El⁰ x) → El⁰ (y a)) → Σ[ A ∈ Type ℓ ] A ↪ V⁰ {ℓ}
            elem ϕ .fst = El⁰ x
            elem ϕ .snd = emb ϕ

    graph⁰ : ((a : El⁰ x) → El⁰ (y a)) ↪ V⁰ {ℓ}
    graph⁰ .fst ϕ = sup⁰ (elem ϕ)
    graph⁰ .snd = injEmbedding thm12 (h)
        where
            postulate h : {ϕ ψ : (a : El⁰ x) → El⁰ (y a)} → graph⁰ .fst ϕ ≡ graph⁰ .fst ψ → ϕ ≡ ψ
            -- h {ϕ = ϕ} {ψ = ψ} p = funExt (λ a → {!!})

    _ : (ϕ : (a : El⁰ x) → El⁰ (y a)) → cor11 .fst (sup⁰ (elem ϕ)) ≡ (sup-∞ (El⁰ x) (λ a → ⟨ tilde-0' x a , tilde-0' (y a) (ϕ a) ⟩⁰ .fst))
    _ = λ ϕ → refl

Π⁰ : (x : V⁰ {ℓ}) → (El⁰ x → V⁰ {ℓ}) → V⁰ {ℓ}
Π⁰ x y = sup⁰ (((a : El⁰ x) → El⁰ (y a)) , graph⁰ {x = x} {y = y})

El⁰Π⁰IsΠ : {x : V⁰ {ℓ}} {y : El⁰ x → V⁰ {ℓ}} → El⁰ (Π⁰ x y) ≡ ((a : El⁰ x) → El⁰ (y a))
El⁰Π⁰IsΠ = refl

-- Corollary 23
_→⁰_ : V⁰ {ℓ} → V⁰ {ℓ} → V⁰ {ℓ}
x →⁰ y = Π⁰ x (λ _ → y)

El⁰→⁰Is→ : {x y : V⁰ {ℓ}} → El⁰ (x →⁰ y) ≡ (El⁰ x → El⁰ y)
El⁰→⁰Is→ = refl
