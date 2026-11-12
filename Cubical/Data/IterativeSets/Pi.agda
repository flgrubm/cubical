-- This module provides Π-types of iterative sets. A dependent function Φ is encoded by its
-- graph, i.e. by the set of the ordered pairs ⟨ a , Φ a ⟩

module Cubical.Data.IterativeSets.Pi where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Functions.Embedding

open import Cubical.Data.IterativeSets.Base
open import Cubical.Data.IterativeSets.OrderedPair

module GraphElements {ℓ : Level} {x : V⁰ {ℓ}} {y : El⁰ {ℓ} x → V⁰ {ℓ}} where
  graphEl⁰ : ((a : El⁰ {ℓ} x) → El⁰ {ℓ} (y a)) → El⁰ x → V⁰ {ℓ}
  graphEl⁰ Φ a = ⟨ elements x a , elements (y a) (Φ a) ⟩⁰

  module FstConst (Φ : (a : El⁰ {ℓ} x) → El⁰ {ℓ} (y a)) where
    inj : {a b : El⁰ x} → graphEl⁰ Φ a ≡ graphEl⁰ Φ b → a ≡ b
    inj {a} {b} p = isEmbedding→Inj (isEmbedding-elements x) a b
                      (orderedPair⁰≡orderedPair⁰ .fst p .fst)

    emb : isEmbedding (graphEl⁰ Φ)
    emb = injEmbedding isSetV⁰ inj

  graphEl⁰-inj' : (Φ Ψ : (a : El⁰ {ℓ} x) → El⁰ {ℓ} (y a)) (a : El⁰ x)
                   → graphEl⁰ Φ ≡ graphEl⁰ Ψ → Φ a ≡ Ψ a
  graphEl⁰-inj' Φ Ψ a p = isEmbedding→Inj (isEmbedding-elements (y a)) (Φ a) (Ψ a)
                            (orderedPair⁰≡orderedPair⁰ .fst (funExt⁻ p a) .snd)

  graphEl⁰-inj : {Φ Ψ : (a : El⁰ x) → El⁰ (y a)} → graphEl⁰ Φ ≡ graphEl⁰ Ψ → Φ ≡ Ψ
  graphEl⁰-inj {Φ} {Ψ} p = funExt λ a → graphEl⁰-inj' Φ Ψ a p

  graphEl⁰-emb : isEmbedding graphEl⁰
  graphEl⁰-emb = injEmbedding (isSet→ isSetV⁰) graphEl⁰-inj

module Graph {ℓ : Level} {x : V⁰ {ℓ}} {y : El⁰ {ℓ} x → V⁰ {ℓ}} where
  open GraphElements {ℓ} {x} {y}

  graph⁰ : ((a : El⁰ {ℓ} x) → El⁰ {ℓ} (y a)) → V⁰ {ℓ}
  graph⁰ Φ = fromEmb E
    where
      E : Embedding V⁰ ℓ
      E .fst = El⁰ x
      E .snd .fst = graphEl⁰ Φ
      E .snd .snd = FstConst.emb Φ

  graph⁰-inj : {Φ Ψ : (a : El⁰ x) → El⁰ (y a)} → graph⁰ Φ ≡ graph⁰ Ψ → Φ ≡ Ψ
  graph⁰-inj {Φ} {Ψ} p =
    graphEl⁰-inj (funExt λ a → pointwise a (Ψ⊆Φ (graphEl⁰ Ψ a) (a , refl)))
    where
      Ψ⊆Φ : (z : V⁰) → z ∈⁰ graph⁰ Ψ → z ∈⁰ graph⁰ Φ
      Ψ⊆Φ = ≡V⁰-≃-≃V⁰ .fst p .snd

      -- matching on the membership proof typechecks much faster than projecting from it
      pointwise : (a : El⁰ x) → graphEl⁰ Ψ a ∈⁰ graph⁰ Φ → graphEl⁰ Φ a ≡ graphEl⁰ Ψ a
      pointwise a (a' , q) = subst (λ b → graphEl⁰ Φ b ≡ graphEl⁰ Ψ a) a'≡a q
        where
          a'≡a : a' ≡ a
          a'≡a = isEmbedding→Inj (isEmbedding-elements x) a' a
                   (orderedPair⁰≡orderedPair⁰ .fst q .fst)

  graph⁰-emb : isEmbedding graph⁰
  graph⁰-emb = injEmbedding isSetV⁰ graph⁰-inj

private
  variable
    ℓ : Level

Π⁰ : (x : V⁰ {ℓ}) → (El⁰ x → V⁰ {ℓ}) → V⁰ {ℓ}
Π⁰ {ℓ} x y = fromEmb E
  where
    E : Embedding V⁰ ℓ
    E .fst = (a : El⁰ x) → El⁰ (y a)
    E .snd .fst = Graph.graph⁰ {ℓ} {x} {y}
    E .snd .snd = Graph.graph⁰-emb {ℓ} {x} {y}

El⁰Π⁰IsΠ : {x : V⁰ {ℓ}} {y : El⁰ x → V⁰ {ℓ}} → El⁰ (Π⁰ x y) ≡ ((a : El⁰ x) → El⁰ (y a))
El⁰Π⁰IsΠ = refl

_→⁰_ : V⁰ {ℓ} → V⁰ {ℓ} → V⁰ {ℓ}
x →⁰ y = Π⁰ x (λ _ → y)

El⁰→⁰Is→ : {x y : V⁰ {ℓ}} → El⁰ (x →⁰ y) ≡ (El⁰ x → El⁰ y)
El⁰→⁰Is→ = refl
