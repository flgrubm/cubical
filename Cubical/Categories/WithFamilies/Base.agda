-- {-# OPTIONS --safe #-}

module Cubical.Categories.WithFamilies.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category
open import Cubical.Categories.Limits.Terminal
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation
open import Cubical.Categories.Presheaf
open import Cubical.Categories.Constructions.Elements

private
  variable
    ℓ ℓ' : Level

-- deal with this once I figure out how to use it
-- how do I avoid typing all this `Cubical.Categories.Category.Category` boilerplate?
-- otherwise make them private somehow, maybe `module _ where`?
-- isTerminal : (C : Category ℓ ℓ') → (x : Cubical.Categories.Category.Category.ob C) → Type (ℓ-max ℓ ℓ')
-- isTerminal C x = ∀ (y : Cubical.Categories.Category.Category.ob C) → isContr (C [ y , x ])
--
-- hasTerminal : (C : Category ℓ ℓ') → Type (ℓ-max ℓ ℓ')
-- hasTerminal C = Σ[ x ∈ Cubical.Categories.Category.Category.ob C ] isTerminal C x

-- hasTerminal : (C : Category  ℓ ℓ') → Type (ℓ-max ℓ ℓ')
-- hasTerminal C = ∥ Terminal C ∥₁

-- check universe levels
record CwF (C : Category ℓ ℓ') (ℓS : Level) : Type (ℓ-suc (ℓ-max (ℓ-max ℓ ℓ') ℓS)) where
  field
    -- very much inspired by `Cubical.Categories.Limits.Terminal`, but I don't know how to import it from there.
    -- emptyContext : ∥ hasTerminal C ∥₁ -- do I need truncation here?
    emptyContext : Terminal C

    tyPresheaf : Presheaf C ℓS -- (ℓ-max ℓ ℓ')
    -- ∫_ : ∀ {ℓS} → Functor C (SET ℓS) → Category (ℓ-max ℓ ℓS) (ℓ-max ℓ' ℓS)
    tmPresheaf : Presheaf (Covariant.∫ tyPresheaf) ℓS
