module Cubical.Data.IterativeSets.T04Combined where
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
    B B' : A → Type ℓ'

_≡W_ : {ℓ ℓ' : Level} {A : Type ℓ} {B : A → Type ℓ'} → W A B → W A B → Type (ℓ-suc (ℓ-max ℓ ℓ'))
_≡W_ {B = B} (sup-W x α) (sup-W y β)  = Σ[ p ∈ x ≡ y ] ((z : B x) → ((α z) ≡W (β (transport (cong B p) z))))

≡WRefl : (x : W A B) → x ≡W x
≡WRefl (sup-∞ x α) .fst = refl
≡WRefl {ℓ} {ℓ'} {A} {B} (sup-∞ x α) .snd z = transport (sym (
    (α z ≡W α (transport (cong B refl) z))
        ≡⟨⟩
    (α z ≡W α (transport refl z))
        ≡⟨ cong (λ x → α z ≡W α x) (transportRefl z) ⟩
    (α z ≡W α z)
        ∎)) (≡WRefl {ℓ} {ℓ'} {A} {B} (α z))

≡WCenterTotal : (x : W A B) → Σ[ w ∈ W A B ] x ≡W w
≡WCenterTotal x .fst = x
≡WCenterTotal x .snd = ≡WRefl x
