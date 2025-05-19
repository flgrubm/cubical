{-# OPTIONS --safe #-}
module Cubical.Foundations.IterativeSets.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Data.W.W

-- private
--   variable
--     ℓ : Level

V∞ : {ℓ : Level} → Type (ℓ-suc ℓ)
V∞ {ℓ = ℓ} = W (Type ℓ) (λ x → x)

-- TODO: definitions of overline and tilde
