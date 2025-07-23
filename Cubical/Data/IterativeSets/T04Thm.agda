module Cubical.Data.IterativeSets.T04Thm where
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

thm4-fun : {ℓ : Level} → {x y : V∞ {ℓ}} → x ≡ y → (z : V∞) → fiber (tilde-∞ x) z ≡ fiber (tilde-∞ y) z
thm4-fun {ℓ = ℓ} {x = x} {y = y} p z i = fiber (tilde-∞ (p i)) z

thm4-fun' : {ℓ : Level} → {x y : V∞ {ℓ}} → x ≡ y → (z : V∞) → fiber (tilde-∞ x) z ≃ fiber (tilde-∞ y) z
thm4-fun' {ℓ = ℓ} {x = x} {y = y} p z = pathToEquiv (λ i → fiber (tilde-∞ (p i)) z)

-- J rule

postulate thm4-inv : {ℓ : Level} → {x y : V∞ {ℓ}} → ((z : V∞) → fiber (tilde-∞ x) z ≡ fiber (tilde-∞ y) z) → x ≡ y
-- thm4-inv {ℓ = ℓ} {x = sup-W A f} {y = sup-W B g} h i = sup-W A→Bi f→gi where
--   A→Bi = {!!}
--   f→gi : A→Bi → V∞
--   f→gi = {!!}
-- plug in x or y for z???
-- equality of sigma type as equality (ΣPathP, PathPΣ or so?)

postulate thm4-rightInv : {ℓ : Level} → {x y : V∞ {ℓ}} → section (thm4-fun {ℓ} {x} {y}) (thm4-inv {ℓ} {x} {y})

postulate thm4-leftInv : {ℓ : Level} → {x y : V∞ {ℓ}} → retract (thm4-fun {ℓ} {x} {y}) (thm4-inv {ℓ} {x} {y})

thm4' : {ℓ : Level} → {x y : V∞ {ℓ}} → ((x ≡ y) ≃ ((z : V∞) → fiber (tilde-∞ x) z ≡ fiber (tilde-∞ y) z))
thm4' {ℓ = ℓ} {x = x} {y = y} = isoToEquiv (iso (thm4-fun {ℓ} {x} {y}) (thm4-inv {ℓ} {x} {y}) (thm4-rightInv {ℓ} {x} {y}) (thm4-leftInv {ℓ} {x} {y}))

thm4'' : {ℓ : Level} → {x y : V∞ {ℓ}} → ((x ≡ y) ≃ ((z : V∞) → fiber (tilde-∞ x) z ≃ fiber (tilde-∞ y) z))
thm4'' {ℓ = ℓ} {x = x} {y = y} = isoToEquiv (iso f finv sect retr) where
  f : x ≡ y → (z : V∞) → fiber (tilde-∞ x) z ≃ fiber (tilde-∞ y) z
  f p z = pathToEquiv (thm4-fun p z)
  finv : ((z : V∞) → fiber (tilde-∞ x) z ≃ fiber (tilde-∞ y) z) → x ≡ y
  finv h = thm4-inv λ z → ua (h z)
  postulate sect : section f  finv
  postulate retr : retract f finv

-- maybe not
-- thm4' : {x y : V∞} → ((z : V∞) → fiber (tilde-∞ x) z ≡ fiber (tilde-∞ y) z) → x ≡ y
-- thm4' {x = (sup-W A f)} {y = (sup-W B g)} h i = sup-W {!!} {! !}

