module Cubical.Data.IterativeSets.T20Pro where
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

suc⁰ : {ℓ : Level} → V⁰ {ℓ} → V⁰ {ℓ}
suc⁰ x = sup⁰ (overline-0 x ⊎ Unit , ϕₓ , ϕₓemb)
  where
    ϕₓ : (overline-0 x ⊎ Unit) → V⁰ {{!!}}
    ϕₓ (inl a) = (tilde-0 x a) , {!x .snd!}
    ϕₓ (fsuc a) = x

    ϕₓemb : {!!}
    ϕₓemb = {!!}
    
