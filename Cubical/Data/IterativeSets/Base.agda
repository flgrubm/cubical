-- {-# OPTIONS --safe #-}
module Cubical.Data.IterativeSets.Base where
-- maybe move to Cubical.Data.IterativeSets
-- definitions in Base
-- properties in Properties

open import Cubical.Core.Everything

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
-- open import Cubical.

open import Cubical.Homotopy.Base

open import Cubical.Data.W.W

private
  variable
    ℓ ℓ' ℓ'' : Level

V∞ : {ℓ : Level} → Type (ℓ-suc ℓ)
V∞ {ℓ = ℓ} = W (Type ℓ) (λ x → x)

-- TODO: definitions of overline and tilde

-- it's not really possible to use sup-∞ as a constructor, is it still helpful to have it?
sup-∞ : (A : Type ℓ) → (A → V∞) → V∞
sup-∞ = sup-W

overline-∞ : V∞ {ℓ} → Type ℓ
overline-∞ (sup-W A f) = A

tilde-∞ : (A : V∞ {ℓ}) → overline-∞ A → V∞ {ℓ}
tilde-∞ (sup-W A f) = f

thm3 : {x y : V∞ {ℓ}} → x ≡ y → Σ[ e ∈ overline-∞ x ≃ overline-∞ y ] tilde-∞ x ∼ (tilde-∞ y ∘ e .fst)
thm3 p = {!!}

thm4 : {x y : V∞} → x ≡ y → (z : V∞) → fiber (tilde-∞ x) z ≃ fiber (tilde-∞ y) z
thm4 p z = {!!} , {! !}

-- desup in the future (for V = V⁰)

-- Definition 5 (element V∞)
-- theorem 3 + 4
-- Definition 6 (somewhere in the library)
-- same lemma 7
-- Definition 8 important
-- Definition 9
-- ... theorem 12
