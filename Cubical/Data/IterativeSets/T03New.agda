module Cubical.Data.IterativeSets.T03New where
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

open import Cubical.Foundations.CartesianKanOps

private
  variable
    ℓ ℓ' ℓ'' : Level
    A A' : Type ℓ
    B B' : A → Type ℓ'

try : {x y : V∞ {ℓ}} → x ≡ y → Σ[ e ∈ overline-∞ x ≡ overline-∞ y ] tilde-∞ x ∼ (tilde-∞ y ∘ transport e)
try {x = x} {y = y} = J (λ z p → Σ[ e ∈ overline-∞ x ≡ overline-∞ z ] tilde-∞ x ∼ (tilde-∞ z ∘ transport e)) (refl , λ a → sym (cong (λ b → tilde-∞ x b) (transportRefl a)))

tryInv : {x y : V∞ {ℓ}} → (Σ[ e ∈ overline-∞ x ≡ overline-∞ y ] tilde-∞ x ≡ (tilde-∞ y ∘ transport e)) → x ≡ y
tryInv {ℓ = ℓ} {x = sup-∞ A f} {y = sup-∞ B g} (P , H) = J2 fam refl P H 
    where
        fam : (C : Type ℓ) → A ≡ C → (h : A → V∞ {ℓ}) → f ≡ h → Type (ℓ-suc ℓ)
        fam C p h p' = (sup-∞ A f) ≡ sup-∞ C {!h!}

