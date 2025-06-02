-- {-# OPTIONS --safe #-}
module Cubical.Data.IterativeSets.Base where
-- definitions in Base
-- properties in Properties

open import Cubical.Core.Everything

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
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

open import Cubical.Data.Sigma

-- open import Cubical.

open import Cubical.Homotopy.Base

open import Cubical.Data.W.W

private
  variable
    ℓ ℓ' ℓ'' : Level

V∞ : {ℓ : Level} → Type (ℓ-suc ℓ)
V∞ {ℓ = ℓ} = W (Type ℓ) (λ x → x)

-- TODO: definitions of overline and tilde

-- it's not really possible to use sup-∞ as a constructor, is it still helpful to have it?
sup-∞ : (A : Type ℓ) → (A → V∞) → V∞
sup-∞ = sup-W

overline-∞ : V∞ {ℓ} → Type ℓ
overline-∞ (sup-W A f) = A

tilde-∞ : (A : V∞ {ℓ}) → overline-∞ A → V∞ {ℓ}
tilde-∞ (sup-W B f) = f

-- theorem 3 + 4
thm3-fun : {ℓ : Level} → {x y : V∞ {ℓ}} → x ≡ y → Σ[ e ∈ overline-∞ x ≃ overline-∞ y ] tilde-∞ x ∼ (tilde-∞ y ∘ e .fst)
thm3-fun {ℓ = ℓ} {x = x} {y = y} p = e , h where
  e = pathToEquiv (λ i → overline-∞ (p i))
  h : (z : overline-∞ x) → tilde-∞ x z ≡ (tilde-∞ y (e .fst z))
  h z i = tilde-∞ (p i) (transport-filler (cong overline-∞ p) z i)

-- helper : {A : Type ℓ} {B : Type ℓ'} {C : I → Type ℓ''} → (P : PathP (λ i → C i) A B) → (x : A) → (y : B) →

-- postulate helper : {C : I → Type ℓ} → (P Q : PathP (λ i → C i) (Type ℓ) (Type ℓ)) → P ≡ Q → (x : C i0) → transport P x ≡ transport Q x

postulate thm3-inv : {ℓ : Level} → {x y : V∞ {ℓ}} → (Σ[ e ∈ overline-∞ x ≃ overline-∞ y ] tilde-∞ x ∼ (tilde-∞ y ∘ e .fst)) → x ≡ y
-- thm3-inv {ℓ = ℓ} {x = sup-W A f} {y = sup-W B g} (e , h) i = sup-W (A→B i) (f→g i) where
--   A→B = ua e
--   f→g : (j : I) → (A→B j) → V∞
--   f→g j = funExtNonDep {ℓ} {ℓ-suc ℓ} {λ i → A→B i} {λ _ → V∞} {f} {g} (λ {z₀} {z₁} p → h z₀ ∙ {! !}) j

postulate thm3-rightInv : {ℓ : Level} → {x y : V∞ {ℓ}} → section (thm3-fun {ℓ} {x} {y}) (thm3-inv {ℓ} {x} {y})

postulate thm3-leftInv : {ℓ : Level} → {x y : V∞ {ℓ}} → retract (thm3-fun {ℓ} {x} {y}) (thm3-inv {ℓ} {x} {y})


thm3 : {ℓ : Level} → {x y : V∞ {ℓ}} → ((x ≡ y) ≃ (Σ[ e ∈ overline-∞ x ≃ overline-∞ y ] tilde-∞ x ∼ (tilde-∞ y ∘ e .fst)))
thm3 {ℓ = ℓ} {x = x} {y = y} = isoToEquiv (iso (thm3-fun {ℓ} {x} {y}) (thm3-inv {ℓ} {x} {y}) (thm3-rightInv {ℓ} {x} {y}) (thm3-leftInv {ℓ} {x} {y}))

thm4-fun : {ℓ : Level} → {x y : V∞ {ℓ}} → x ≡ y → (z : V∞) → fiber (tilde-∞ x) z ≡ fiber (tilde-∞ y) z
thm4-fun {ℓ = ℓ} {x = x} {y = y} p z i = fiber (tilde-∞ (p i)) z

postulate thm4-inv : {ℓ : Level} → {x y : V∞ {ℓ}} → ((z : V∞) → fiber (tilde-∞ x) z ≡ fiber (tilde-∞ y) z) → x ≡ y
-- thm4-inv {ℓ = ℓ} {x = sup-W A f} {y = sup-W B g} h i = sup-W A→Bi f→gi where
--   A→Bi = {!!}
--   f→gi : A→Bi → V∞
--   f→gi = {!!}

postulate thm4-rightInv : {ℓ : Level} → {x y : V∞ {ℓ}} → section (thm4-fun {ℓ} {x} {y}) (thm4-inv {ℓ} {x} {y})

postulate thm4-leftInv : {ℓ : Level} → {x y : V∞ {ℓ}} → retract (thm4-fun {ℓ} {x} {y}) (thm4-inv {ℓ} {x} {y})

thm4' : {ℓ : Level} → {x y : V∞ {ℓ}} → ((x ≡ y) ≃ ((z : V∞) → fiber (tilde-∞ x) z ≡ fiber (tilde-∞ y) z))
thm4' {ℓ = ℓ} {x = x} {y = y} = isoToEquiv (iso (thm4-fun {ℓ} {x} {y}) (thm4-inv {ℓ} {x} {y}) (thm4-rightInv {ℓ} {x} {y}) (thm4-leftInv {ℓ} {x} {y}))

thm4 : {ℓ : Level} → {x y : V∞ {ℓ}} → ((x ≡ y) ≃ ((z : V∞) → fiber (tilde-∞ x) z ≃ fiber (tilde-∞ y) z))
thm4 {ℓ = ℓ} {x = x} {y = y} = isoToEquiv (iso f finv sect retr) where
  f : x ≡ y → (z : V∞) → fiber (tilde-∞ x) z ≃ fiber (tilde-∞ y) z
  f p z = pathToEquiv (thm4-fun p z)
  finv : ((z : V∞) → fiber (tilde-∞ x) z ≃ fiber (tilde-∞ y) z) → x ≡ y
  finv h = thm4-inv λ z → ua (h z)
  postulate sect : section f  finv
  postulate retr : retract f finv

-- maybe not
-- thm4' : {x y : V∞} → ((z : V∞) → fiber (tilde-∞ x) z ≡ fiber (tilde-∞ y) z) → x ≡ y
-- thm4' {x = (sup-W A f)} {y = (sup-W B g)} h i = sup-W {!!} {! !}


_∈∞_ : V∞ {ℓ} → V∞ {ℓ} → Type (ℓ-suc ℓ)
x ∈∞ y = fiber (tilde-∞ y) x

-- examples
emptySet-∞ : V∞ {ℓ-zero}
emptySet-∞ = sup-∞ ⊥ ⊥-elim

singleton : V∞ → V∞
singleton x = sup-∞ Unit λ _ → x

unorderedPair : V∞ → V∞ → V∞
unorderedPair x y = sup-∞ Bool (λ b → if b then x else y)

-- iterative sets
isIterativeSet : V∞ {ℓ} → Type (ℓ-suc ℓ)
isIterativeSet (sup-W A f) = (isEmbedding f) × ((a : A) → isIterativeSet (f a))

V⁰ : {ℓ : Level} → Type (ℓ-suc ℓ)
V⁰ {ℓ = ℓ} = Σ[ x ∈ V∞ {ℓ} ] isIterativeSet x

overline-0 : V⁰ {ℓ} → Type ℓ
overline-0 (sup-W A f , p) = A

tilde-0 : (A : V⁰ {ℓ}) → overline-0 A → V∞ {ℓ}
tilde-0 (sup-W B f , p) = f

lem10 : {ℓ : Level} → (x : V∞ {ℓ}) → isProp (isIterativeSet x)
lem10 {ℓ = ℓ} (sup-W A f) = isProp× (isPropIsEmbedding) helper where
  helper : isProp ((a : A) → isIterativeSet (f a))
  helper g h i x = lem10 (f x) (g x) (h x) i

cor11 : {ℓ : Level} → V⁰ {ℓ} ↪ V∞ {ℓ}
cor11 {ℓ = ℓ} = EmbeddingΣProp lem10

-- maybe this is somthing for Cubical.Functions.Embedding?
embeddingToEquivOfPath : {ℓ ℓ' : Level} → {A : Type ℓ} → {B : Type ℓ'} → {f : A → B} → isEmbedding f → (x y : A) → (x ≡ y) ≃ (f x ≡ f y)
embeddingToEquivOfPath {ℓ = ℓ} {ℓ' = ℓ'} {A = A} {B = B} {f = f} isemb x y = cong f , isemb x y

cor11-1 : {ℓ : Level} → {x y : V⁰ {ℓ}} → (x ≡ y) ≃ (x .fst ≡ y .fst)
cor11-1 {ℓ = ℓ} {x = x} {y = y} = embeddingToEquivOfPath (cor11 .snd) x y

infixr 15 _∘e_

_∘e_ : {ℓ ℓ' ℓ'' : Level} → {A : Type ℓ} → {B : Type ℓ'} → {C : Type ℓ''} → B ≃ C → A ≃ B → A ≃ C
_∘e_ {A = A} {B = B} {C = C} (l₁ , l₂) (r₁ , r₂) = eqfun , equivprf where
  eqfun = l₁ ∘ r₁
  equivprf : isEquiv eqfun
  equivprf .equiv-proof c = inh , contrprf where
    inh : fiber eqfun c
    inh .fst = r₂ .equiv-proof (l₂ .equiv-proof c .fst .fst) .fst .fst
    inh .snd = cong l₁ (rr (l₂ .equiv-proof c .fst .fst)) ∙ ll c where
      ll : (c' : C) → l₁ (l₂ .equiv-proof c' .fst .fst) ≡ c'
      ll c' = l₂ .equiv-proof c' .fst .snd
      rr : (b' : B) → r₁ (r₂ .equiv-proof b' .fst .fst) ≡ b'
      rr b' = r₂ .equiv-proof b' .fst .snd
    contrprf : (d : fiber eqfun c) → inh ≡ d
    contrprf (a , p) = {!!}

-- ... theorem 12

thm12-help : {ℓ : Level} → {x y : V⁰ {ℓ}} → ((x ≡ y) ≃ ((z : V∞) → fiber (tilde-∞ (x .fst)) z ≃ fiber (tilde-∞ (y .fst)) z))
thm12-help = thm4 ∘e cor11-1

thm12 : {ℓ : Level} → isSet (V⁰ {ℓ})
thm12 x y x₁ y₁ = {!!}
