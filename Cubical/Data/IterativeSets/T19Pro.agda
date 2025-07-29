module Cubical.Data.IterativeSets.T19Pro where

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
open import Cubical.Data.Empty renaming (elim* to ⊥*-elim)
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
-- functionFromIsProp→isEmbedding {A = A} {B = B} f propA w x = {!!}
-- functionFromIsProp→isEmbedding f isprop = hasPropFibers→isEmbedding λ z x y i → (isprop (x .fst) (y .fst)) i , {!!} -- ((cong f (isprop (isprop (x .fst) (y .fst)) x)) ∙ (x .snd))

unit⁰' : V⁰ {ℓ}
unit⁰' {ℓ = ℓ} = sup⁰ (Unit* , f , isemb)
    where
        f : Unit* → V⁰ {ℓ}
        f _ = empty⁰
        isemb : isEmbedding f
        isemb = functionFromIsProp→isEmbedding f isPropUnit*

unit⁰IsUnit' : El⁰ {ℓ} unit⁰' ≡ Unit* {ℓ}
unit⁰IsUnit' = refl


isEmpty : {ℓ : Level} (A : Type ℓ) → Type ℓ
isEmpty {ℓ} A = (a : A) → ⊥* {ℓ}

isEmpty-elim : {ℓ ℓ' : Level} {A : Type ℓ} {B : Type ℓ'} → isEmpty A → A → B
isEmpty-elim emptyA = (⊥*-elim ∘ emptyA)

isEmptyIsEquiv : {A : Type ℓ} {B : Type ℓ'} → (f : A → B) → isEmpty {ℓ} A → isEmpty {ℓ'} B → isEquiv f
isEmptyIsEquiv {ℓ} {ℓ'} {A} {B} f emptyA emptyB = isoToIsEquiv (iso f g sec ret)
    where
        g : B → A
        g = isEmpty-elim emptyB
        sec : section f g
        sec b = isEmpty-elim emptyB b
        ret : retract f g
        ret a = isEmpty-elim emptyA a

false≢true* : (lift false :> Bool* {ℓ}) ≡ (lift true :> Bool* {ℓ}) → ⊥* {ℓ}
false≢true* {ℓ = ℓ} p = subst ((λ {(lift false) → Unit* {ℓ} ; (lift true) → ⊥* {ℓ}})) p (lift tt)

true≢false* : (lift true :> Bool* {ℓ}) ≡ (lift false :> Bool* {ℓ}) → ⊥* {ℓ}
true≢false* {ℓ = ℓ} p = subst (λ {(lift true) → Unit* {ℓ} ; (lift false) → ⊥* {ℓ}}) p (lift tt)

⊥*≢Unit* : ((⊥* {ℓ} :> Type ℓ) ≡ (Unit* {ℓ} :> Type ℓ)) → ⊥* {ℓ}
⊥*≢Unit* p = pathToEquiv (sym p) .fst (lift tt)

Unit*≢⊥* : ((Unit* {ℓ} :> Type ℓ) ≡ (⊥* {ℓ} :> Type ℓ)) → ⊥* {ℓ}
Unit*≢⊥* p = pathToEquiv p .fst (lift tt)

empty⁰≢unit⁰ : (empty⁰ {ℓ} ≡ unit⁰ {ℓ}) → ⊥* {ℓ}
empty⁰≢unit⁰ {ℓ} p = ⊥*≢Unit* (sym empty⁰Is⊥* ∙ (cong El⁰ p) ∙ unit⁰IsUnit*)

unit⁰≢empty⁰ : (unit⁰ {ℓ} ≡ empty⁰ {ℓ}) → ⊥* {ℓ}
unit⁰≢empty⁰ {ℓ} p = Unit*≢⊥* (sym unit⁰IsUnit* ∙ (cong El⁰ p) ∙ empty⁰Is⊥*)

bool⁰' : V⁰ {ℓ}
bool⁰' {ℓ} = sup⁰ (Bool* {ℓ} , f , isemb)
    where
        f : Bool* {ℓ} → V⁰ {ℓ}
        f (lift false) = empty⁰
        f (lift true) = unit⁰

        isemb : isEmbedding f
        isemb (lift false) (lift true) = isEmptyIsEquiv _ false≢true* {!empty⁰≢unit⁰ {ℓ}!} -- why does this not work?
        isemb (lift true) (lift false) = isEmptyIsEquiv _ true≢false* {!unit⁰≢empty⁰ {ℓ}!}
        -- for the other cases use that El⁰ unit⁰ is a proposition (even contractible)
        isemb x y = {!!}

bool⁰IsBool' : El⁰ {ℓ} bool⁰' ≡ Bool* {ℓ}
bool⁰IsBool' = refl
