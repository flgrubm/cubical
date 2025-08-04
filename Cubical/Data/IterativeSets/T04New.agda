module Cubical.Data.IterativeSets.T04New where
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

fun4 : {ℓ : Level} → {x y : V∞ {ℓ}} → x ≡ y → (z : V∞) → fiber (tilde-∞ x) z ≃ fiber (tilde-∞ y) z
fun4 {ℓ = ℓ} {x = x} {y = y} p z = pathToEquiv (λ i → fiber (tilde-∞ (p i)) z)

_≡V_ : {ℓ : Level} → (x y : V∞ {ℓ}) → Type (ℓ-suc ℓ)
_≡V_ {ℓ = ℓ} x y = (z : V∞ {ℓ}) → (fiber (tilde-∞ x) z ≃ fiber (tilde-∞ y) z)

thm : {ℓ : Level} (x y : V∞ {ℓ}) → ((x ≡ y) ≃ (x ≡V y))
thm {ℓ = ℓ} = fundamentalTheoremOfId _≡V_ ref con
    where
        ref : (x : V∞ {ℓ}) → x ≡V x
        ref x z = idEquiv (fiber (tilde-∞ x) z)

        con : (x : V∞ {ℓ}) → isContr (Σ[ y ∈ V∞ {ℓ} ] x ≡V y)
        con x .fst .fst = x
        con x .fst .snd = ref x
        con x .snd (y , p) = {!!}
