module Cubical.Data.IterativeSets.UnorderedPair where
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
open import Cubical.Data.Empty renaming (elim* to ⊥*-elim ; elim to ⊥-elim)
open import Cubical.Data.Unit
open import Cubical.Data.Bool
open import Cubical.Functions.FunExtEquiv
open import Cubical.Foundations.HLevels
open import Cubical.Data.Nat
open import Cubical.Data.SumFin

open import Cubical.Data.Sigma

open import Cubical.Homotopy.Base

open import Cubical.Data.W.W

open import Cubical.Data.IterativeSets.Base

private
  variable
    ℓ ℓ' ℓ'' : Level
    A A' : Type ℓ
    B B' : A → Type ℓ'

injective : {A : Type ℓ} {B : Type ℓ'} (f : A → B) → Type (ℓ-max ℓ ℓ')
injective {A = A} f = (x y : A) → f x ≡ f y → x ≡ y

injectiveNeg : {A : Type ℓ} {B : Type ℓ'} (f : A → B) → Type (ℓ-max ℓ ℓ')
injectiveNeg {A = A} f = (x y : A) → (x ≡ y → ⊥) → (f x ≡ f y → ⊥)

injectiveNeg→injective : {A : Type ℓ} {B : Type ℓ'} (f : A → B) → injectiveNeg f → injective f
injectiveNeg→injective f injNeg x y = {!!}

-- test : {A : Type ℓ} {B : Type ℓ'} (f : A → B) → ((x y : A) → (x ≡ y → ⊥) → (f x ≡ f y → ⊥)) → isEmbedding f
-- test {A = A} {B = B} f prf = hasPropFibers→isEmbedding (λ z x y → {!!})

-- unorderedPair⁰ : (x y : V⁰ {ℓ}) → ((x ≡ y) → ⊥) → V⁰ {ℓ}
-- unorderedPair⁰ {ℓ} x y x≢y = sup⁰ (Bool* , {!!})
