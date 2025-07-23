module Cubical.Data.IterativeSets.T19Pro where
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

-- isProp-isSet→isEmbedding : {ℓ ℓ' : Level} → {A : Type ℓ} → {B : Type ℓ'} → (f : A → B) → isProp A → isSet B → isEmbedding f
-- isProp-isSet→isEmbedding {A = A} {B = B} f isp iss = {!!}

postulate functionFromIsProp→isEmbedding : {ℓ ℓ' : Level} → {A : Type ℓ} → {B : Type ℓ'} → (f : A → B) → isProp A → isEmbedding f
-- functionFromIsProp→isEmbedding f isprop = hasPropFibers→isEmbedding λ z x y i → (isprop (x .fst) (y .fst)) i , {!!} -- ((cong f (isprop (isprop (x .fst) (y .fst)) x)) ∙ (x .snd))

unit⁰' : V⁰ {ℓ-zero}
unit⁰' = singleton emptySet-∞ , isemb , isiterative
  where
    isemb : isEmbedding (λ _ → emptySet-∞)
    isemb = functionFromIsProp→isEmbedding (λ _ → emptySet-∞) isPropUnit

    isiterative : (a : Unit) → isIterativeSet emptySet-∞
    isiterative _ = empty⁰ .snd

bool⁰' : V⁰ {ℓ-zero}
bool⁰' = unorderedPair (empty⁰ .fst) (unit⁰' .fst) , isemb , isiterative
  where
    postulate isemb : isEmbedding (λ b → if b then empty⁰ .fst else unit⁰' .fst)
    -- isemb = {!!} -- idea: empty⁰ /= unit⁰

    isiterative : (b : Bool) → isIterativeSet (if b then empty⁰ .fst else unit⁰' .fst)
    isiterative false = unit⁰' .snd
    isiterative true = empty⁰ .snd

unit⁰IsUnit' : El⁰ unit⁰' ≡ Unit
unit⁰IsUnit' = refl

bool⁰IsBool' : El⁰ bool⁰' ≡ Bool
bool⁰IsBool' = refl
