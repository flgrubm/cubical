module Cubical.Data.IterativeSets.T22Lem where
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
open import Cubical.Data.Empty renaming (elim* to ⊥*-elim ; elim to ⊥-elim)
open import Cubical.Data.Unit
open import Cubical.Data.Bool
open import Cubical.Functions.FunExtEquiv
open import Cubical.Foundations.HLevels
open import Cubical.Data.Nat
open import Cubical.Data.SumFin

open import Cubical.Data.Sigma

open import Cubical.Homotopy.Base

open import Cubical.Data.W.W
open import Cubical.Data.IterativeSets.Base

private
  variable
    ℓ ℓ' ℓ'' : Level
    A A' : Type ℓ
    B B' : A → Type ℓ'

graph⁰ : {ℓ : Level} (x : V⁰ {ℓ}) (y : El⁰ x → V⁰ {ℓ}) → (((a : El⁰ x) → El⁰ (y a)) ↪ V⁰ {ℓ})
graph⁰ x y .fst ϕ = sup⁰ (El⁰ x , (λ a → ⟨ tilde-0' x a , tilde-0' (y a) (ϕ a) ⟩) , {!!})
graph⁰ x y .snd = {!!}

Π⁰' : {ℓ : Level} (x : V⁰ {ℓ}) (y : El⁰ x → V⁰ {ℓ}) → V⁰ {ℓ}
Π⁰' x y = sup⁰ (((a : El⁰ x) → El⁰ (y a)) , (graph⁰ x y))

Π⁰IsΠ' : {ℓ : Level} {x : V⁰ {ℓ}} {y : El⁰ x → V⁰ {ℓ}} → El⁰ (Π⁰' x y) ≡ ((a : El⁰ x) → El⁰ (y a))
Π⁰IsΠ' = refl
