module Cubical.Data.IterativeSets.T15DefDesup where
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

-- maybe interesting to add to the library?
isEquivEquiv : {A : Type ℓ} {B : Type ℓ'} {f : A → B} → isEquiv f → A ≃ B
isEquivEquiv {f = f} iseq = f , iseq

firstInIsEmbeddingCompIsEmbedding : {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''} → (f : A → B) → (g : B → C) → isEmbedding g → isEmbedding (g ∘ f) → isEmbedding f
firstInIsEmbeddingCompIsEmbedding {A = A} {B = B} {C = C} f g embg emb∘ = hasPropFibers→isEmbedding hpff
  where
    postulate hpff : hasPropFibers f
    -- hpff b (x , pxg) (y , pyg) = ΣPathP (p .fst , λ i → cong (invIsEq {!embg!}) (p .snd i))
      -- where
      --   p : Σ[ q ∈ x ≡ y ] PathP _ (cong g pxg) (cong g pyg)
      --   p = PathPΣ (isEmbedding→hasPropFibers emb∘ (g b) (x , cong g pxg) (y , cong g pyg))

-- firstInIsEmbeddingCompIsEmbedding f g embg emb∘ w x = equivIsEquiv (compEquiv (isEquivEquiv (emb∘ w x)) (invEquiv (isEquivEquiv {!embg (f w) (f x)!})))

firstInInjCompIsInj : {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''} → (f : A → B) → (g : B → C) → ((w x : A) → g (f w) ≡ g (f x) → w ≡ x) → {w x : A} → f w ≡ f x → w ≡ x
firstInInjCompIsInj f g inj∘ {w} {x} p = inj∘ w x (cong g p)

desup⁰' : {ℓ : Level} → V⁰ {ℓ} → (Σ[ A ∈ Type ℓ ] A ↪ V⁰ {ℓ})
desup⁰' (sup-W A f , isitset) .fst = A
desup⁰' (sup-W A f , isitset) .snd .fst x .fst = f x
desup⁰' (sup-W A f , isitset) .snd .fst x .snd = isitset .snd x
desup⁰' (sup-W A f , isitset) .snd .snd = injEmbedding thm12 (firstInInjCompIsInj _ (cor11 .fst) (isEmbedding→Inj (isEmbedding-tilde-∞ (sup-W A f , isitset))))
-- desup⁰' (sup-W A f , isitset) .snd .snd = firstInIsEmbeddingCompIsEmbedding (desup⁰' (sup-W A f , isitset) .snd .fst) (cor11 .fst) (cor11 .snd) (isEmbedding-tilde-∞ (sup-W A f , isitset))
