module Cubical.Data.IterativeSets.OrderedPair where

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude

open import Cubical.Functions.Embedding
open import Cubical.Foundations.Equiv
open import Cubical.Data.Sigma
open import Cubical.Data.Empty renaming (elim to ⊥-elim)
open import Cubical.Data.Sum

open import Cubical.Data.IterativeSets.Base
open import Cubical.Data.IterativeSets.Empty
open import Cubical.Data.IterativeSets.Singleton

-- TODO: Deal with the following after efficiency gain
open import Cubical.Data.IterativeSets.UnorderedPair

private
  variable
    ℓ : Level
    x y z : V⁰ {ℓ}

private
  module _ where
    ¬_ : Type ℓ → Type ℓ
    ¬ A = A → ⊥
    {-# INLINE ¬_ #-}

private
  variable
    x≢y : ¬ (x ≡ y)

-- TODO: maybe move to some better place together with empty⁰≢unit⁰
empty⁰≢singleton⁰ : ¬ (empty⁰ {ℓ} ≡ singleton⁰ x)
empty⁰≢singleton⁰ p = ⊥*≢Unit* (cong El⁰ p)

singleton⁰≢empty⁰ : ¬ (singleton⁰ x ≡ empty⁰ {ℓ})
singleton⁰≢empty⁰ p = Unit*≢⊥* (cong El⁰ p)

singleton⁰≢unorderedPair⁰ : ¬ (singleton⁰ z ≡ unorderedPair⁰ x y x≢y)
singleton⁰≢unorderedPair⁰ p = Unit*≢Bool* (cong El⁰ p)

unorderedPair⁰≢singleton⁰ : ¬ (unorderedPair⁰ x y x≢y ≡ singleton⁰ z)
unorderedPair⁰≢singleton⁰ p = Bool*≢Unit* (cong El⁰ p)


-- Norbert Wiener encoding
⟨_,_⟩⁰ : V⁰ {ℓ} → V⁰ {ℓ} → V⁰ {ℓ}
⟨ x , y ⟩⁰ = unorderedPair⁰ (unorderedPair⁰ (singleton⁰ x) empty⁰ singleton⁰≢empty⁰) (singleton⁰ (singleton⁰ y)) unorderedPair⁰≢singleton⁰

orderedPair⁰ : (V⁰ {ℓ} × V⁰ {ℓ}) → V⁰ {ℓ}
orderedPair⁰ (x , y) = ⟨ x , y ⟩⁰

isEmbOrderedPair⁰ : isEmbedding (orderedPair⁰ {ℓ})
isEmbOrderedPair⁰ {ℓ} = injEmbedding thm12 inj
    where
        inj : {s t : V⁰ {ℓ} × V⁰ {ℓ}} → orderedPair⁰ s ≡ orderedPair⁰ t → s ≡ t
        inj {s = x , y} {t = a , b} p = {!!}
            where
                helper : ((unorderedPair⁰ (singleton⁰ x) empty⁰ singleton⁰≢empty⁰ ≡ unorderedPair⁰ (singleton⁰ a) empty⁰ singleton⁰≢empty⁰) × (singleton⁰ (singleton⁰ y) ≡ singleton⁰ (singleton⁰ b))) ⊎ ((unorderedPair⁰ (singleton⁰ x) empty⁰ singleton⁰≢empty⁰ ≡ singleton⁰ (singleton⁰ b)) × (singleton⁰ (singleton⁰ y) ≡ unorderedPair⁰ (singleton⁰ a) empty⁰ singleton⁰≢empty⁰)) → (((unorderedPair⁰ (singleton⁰ x) empty⁰ singleton⁰≢empty⁰ ≡ unorderedPair⁰ (singleton⁰ a) empty⁰ singleton⁰≢empty⁰)) × ((singleton⁰ (singleton⁰ y) ≡ singleton⁰ (singleton⁰ b))))
                helper (inl x) = x
                helper (inr (p , _)) = ⊥-elim (unorderedPair⁰≢singleton⁰ p) -- impossible case (unorderedPair⁰≢singleton⁰)
                -- unorderedPair⁰≡unorderedPair⁰ {x = unorderedPair⁰ (singleton⁰ x) empty⁰ singleton⁰≢empty⁰} {y = singleton⁰ (singleton⁰ y)} {a = unorderedPair⁰ (singleton⁰ a) empty⁰ singleton⁰≢empty⁰} {b = singleton⁰ (singleton⁰ b)} .fst p
