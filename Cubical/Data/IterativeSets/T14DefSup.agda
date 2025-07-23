module Cubical.Data.IterativeSets.T14DefSup where
-- definitions in Base
-- properties in Properties

open import Cubical.Core.Everything

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Fiberwise
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Univalence
open import Cubical.Functions.Fibration
open import Cubical.Functions.Embedding
open import Cubical.Data.Empty renaming (elim to ⊥-elim)
open import Cubical.Data.Unit
open import Cubical.Data.Bool
open import Cubical.Functions.FunExtEquiv
open import Cubical.Foundations.HLevels
open import Cubical.Data.Nat
open import Cubical.Data.SumFin

open import Cubical.Data.Sigma

-- open import Cubical.

open import Cubical.Homotopy.Base

open import Cubical.Data.W.W

open import Cubical.Data.IterativeSets.Base

private
  variable
    ℓ ℓ' ℓ'' : Level
    A A' : Type ℓ
    B B' : A → Type ℓ

isEmbeddingΣ→isEmbeddingFst : {ℓ ℓ' ℓ'' : Level} → {A : Type ℓ} → {B : A → Type ℓ'} → {X : Type ℓ''} → (f : X → Σ[ x ∈ A ] B x) → isEmbedding f → isEmbedding (fst ∘ f)
isEmbeddingΣ→isEmbeddingFst {ℓ} {ℓ'} {ℓ''} {A} {B} {X} f isemb = hasPropFibers→isEmbedding hpf-fst∘f
  where
    hpf-f : hasPropFibers f
    hpf-f = isEmbedding→hasPropFibers isemb
    postulate hpf-fst∘f : (z : A) → isProp (fiber (fst ∘ f) z) -- hasPropFibers (fst ∘ f)
    -- hpf-fst∘f z (x , px) (y , py) i = {!!}

sup⁰' : {ℓ : Level} → (Σ[ A ∈ Type ℓ ] A ↪ V⁰ {ℓ}) → V⁰ {ℓ}
sup⁰' {ℓ} (A , f) .fst = sup-∞ A (fst ∘ (f .fst)) -- (λ z → f .fst z .fst)
sup⁰' {ℓ} (A , f) .snd .fst = isEmbeddingΣ→isEmbeddingFst (f .fst) (f .snd)
sup⁰' {ℓ} (A , f) .snd .snd = snd ∘ (f .fst) -- λ a → f .fst a .snd

