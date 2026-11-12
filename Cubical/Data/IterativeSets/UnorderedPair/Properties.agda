module Cubical.Data.IterativeSets.UnorderedPair.Properties where

open import Cubical.Foundations.Prelude

open import Cubical.Relation.Nullary
open import Cubical.Data.Bool.Properties

open import Cubical.Data.IterativeSets.Base
open import Cubical.Data.IterativeSets.Empty
open import Cubical.Data.IterativeSets.Singleton.Base
open import Cubical.Data.IterativeSets.UnorderedPair.Base
open import Cubical.Data.IterativeSets.Unit
open import Cubical.Data.IterativeSets.Bool

private
  variable
    ℓ : Level
    x y z : V⁰ {ℓ}

empty⁰≢unorderedPair⁰ : {x≢y : ¬ x ≡ y} → ¬ empty⁰ ≡ unorderedPair⁰ x y x≢y
empty⁰≢unorderedPair⁰ p = ⊥*≢Bool* (cong El⁰ p)

unorderedPair⁰≢empty⁰ : {x≢y : ¬ x ≡ y} → ¬ unorderedPair⁰ x y x≢y ≡ empty⁰
unorderedPair⁰≢empty⁰ p = Bool*≢⊥* (cong El⁰ p)

empty⁰≢bool⁰ : ¬ empty⁰ {ℓ} ≡ bool⁰ {ℓ}
empty⁰≢bool⁰ = empty⁰≢unorderedPair⁰

bool⁰≢empty⁰ : ¬ bool⁰ {ℓ} ≡ empty⁰ {ℓ}
bool⁰≢empty⁰ = unorderedPair⁰≢empty⁰

singleton⁰≢unorderedPair⁰ : {x≢y : ¬ x ≡ y} → ¬ singleton⁰ z ≡ unorderedPair⁰ x y x≢y
singleton⁰≢unorderedPair⁰ p = Unit*≢Bool* (cong El⁰ p)

unorderedPair⁰≢singleton⁰ : {x≢y : ¬ x ≡ y} → ¬ unorderedPair⁰ x y x≢y ≡ singleton⁰ z
unorderedPair⁰≢singleton⁰ p = Bool*≢Unit* (cong El⁰ p)

unit⁰≢bool⁰ : ¬ unit⁰ {ℓ} ≡ bool⁰ {ℓ}
unit⁰≢bool⁰ = singleton⁰≢unorderedPair⁰ {x = empty⁰} {y = unit⁰} {z = empty⁰}

bool⁰≢unit⁰ : ¬ bool⁰ {ℓ} ≡ unit⁰ {ℓ}
bool⁰≢unit⁰ = unorderedPair⁰≢singleton⁰ {x = empty⁰} {y = unit⁰} {z = empty⁰}
