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

open import Cubical.Data.Prod

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

-- t : {ℓ : Level} {A B : Type ℓ} → A ≡ B → A → B
-- t = transport

-- theorem 3 + 4
thm3-fun : {ℓ : Level} → {x y : V∞ {ℓ}} → x ≡ y → Σ[ e ∈ overline-∞ x ≃ overline-∞ y ] tilde-∞ x ∼ (tilde-∞ y ∘ e .fst)
thm3-fun {ℓ = ℓ} {x = x} {y = y} p = e , h where
  e = pathToEquiv (λ i → overline-∞ (p i))
  h : (z : overline-∞ x) → tilde-∞ x z ≡ (tilde-∞ y (e .fst z))
  h z i = tilde-∞ (p i) (transport-filler (cong overline-∞ p) z i)

thm3-inv : {ℓ : Level} → {x y : V∞ {ℓ}} → (Σ[ e ∈ overline-∞ x ≃ overline-∞ y ] tilde-∞ x ∼ (tilde-∞ y ∘ e .fst)) → x ≡ y
thm3-inv {ℓ = ℓ} {x = sup-W A f} {y = sup-W B g} (e , h) i = sup-W A→Bi f→gi where
  A→Bi = ua e i
  f→gi : A→Bi → V∞
  f→gi z = {!!} -- funExtNonDep (λ {z₀} {z₁} p → {! !}) i

postulate thm3-rightInv : {ℓ : Level} → {x y : V∞ {ℓ}} → section (thm3-fun {ℓ} {x} {y}) (thm3-inv {ℓ} {x} {y})

postulate thm3-leftInv : {ℓ : Level} → {x y : V∞ {ℓ}} → retract (thm3-fun {ℓ} {x} {y}) (thm3-inv {ℓ} {x} {y})


thm3 : {ℓ : Level} → {x y : V∞ {ℓ}} → ((x ≡ y) ≃ (Σ[ e ∈ overline-∞ x ≃ overline-∞ y ] tilde-∞ x ∼ (tilde-∞ y ∘ e .fst)))
thm3 {ℓ = ℓ} {x = x} {y = y} = isoToEquiv (iso (thm3-fun {ℓ} {x} {y}) (thm3-inv {ℓ} {x} {y}) (thm3-rightInv {ℓ} {x} {y}) (thm3-leftInv {ℓ} {x} {y}))

thm4-fun : {ℓ : Level} → {x y : V∞ {ℓ}} → x ≡ y → (z : V∞) → fiber (tilde-∞ x) z ≡ fiber (tilde-∞ y) z
thm4-fun {ℓ = ℓ} {x = x} {y = y} p z i = fiber (tilde-∞ (p i)) z

postulate thm4-inv : {ℓ : Level} → {x y : V∞ {ℓ}} → ((z : V∞) → fiber (tilde-∞ x) z ≡ fiber (tilde-∞ y) z) → x ≡ y

postulate thm4-rightInv : {ℓ : Level} → {x y : V∞ {ℓ}} → section (thm4-fun {ℓ} {x} {y}) (thm4-inv {ℓ} {x} {y})

postulate thm4-leftInv : {ℓ : Level} → {x y : V∞ {ℓ}} → retract (thm4-fun {ℓ} {x} {y}) (thm4-inv {ℓ} {x} {y})

thm4 : {ℓ : Level} → {x y : V∞ {ℓ}} → ((x ≡ y) ≃ ((z : V∞) → fiber (tilde-∞ x) z ≡ fiber (tilde-∞ y) z))
thm4 {ℓ = ℓ} {x = x} {y = y} = isoToEquiv (iso (thm4-fun {ℓ} {x} {y}) (thm4-inv {ℓ} {x} {y}) (thm4-rightInv {ℓ} {x} {y}) (thm4-leftInv {ℓ} {x} {y}))

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

-- Definition 6 (somewhere in the library)
-- same lemma 7
-- Definition 8 important
-- Definition 9
-- ... theorem 12
