module Cubical.Data.IterativeSets.T17Thm where
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

-- don't need the following
embeddingIntoIsSet→isSet : {A : Type ℓ} {B : Type ℓ'} → A ↪ B → isSet B → isSet A
embeddingIntoIsSet→isSet = Embedding-into-isSet→isSet

-- Embedding-into-isSet→isSet

thm17' : {ℓ : Level} → (x : V⁰ {ℓ}) → isSet (El⁰ x)
thm17' {ℓ = ℓ} (x , (xemb , elsit)) = Embedding-into-isSet→isSet {A = El⁰ {ℓ = ℓ} (x , (xemb , elsit))} {B = V⁰ {ℓ}} ((λ y → tilde-0 (x , (xemb , elsit)) y , {!isit .snd!}) , {!!}) (thm12 {ℓ})
-- thm17' {ℓ = ℓ} x = Embedding-into-isSet→isSet {A = El⁰ {ℓ = ℓ} x} {B = V⁰ {ℓ}} {!!} (thm12 {ℓ})


