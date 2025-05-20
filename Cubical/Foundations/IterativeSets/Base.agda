{-# OPTIONS --safe #-}
module Cubical.Foundations.IterativeSets.Base where
-- maybe move to Cubical.Data.IterativeSets
-- definitions in Base
-- properties in Properties

open import Cubical.Foundations.Prelude
open import Cubical.Data.W.W
open import Cubical.Foundations.Function
open import Cubical.Homotopy.Base

private
  variable
    ℓ : Level

V∞ : {ℓ : Level} → Type (ℓ-suc ℓ)
V∞ {ℓ = ℓ} = W (Type ℓ) (λ x → x)

-- TODO: definitions of overline and tilde

-- it's not really possible to use sup-∞ as a constructor, is it still helpful to have it?
sup-∞ : (A : Type ℓ) → (A → V∞) → V∞
sup-∞ = sup-W

overline-∞ : V∞ → Type ℓ
overline-∞ (sup-W A f) = A

tilde-∞ : (A : V∞ {ℓ}) → overline-∞ A → V∞ {ℓ}
tilde-∞ (sup-W A f) = f

-- desup in the future (for V = V⁰)

-- Definition 5 (element V∞)
-- theorem 3 + 4
-- Definition 6 (somewhere in the library)
-- same lemma 7
-- Definition 8 important
-- Definition 9
-- ... theorem 12
