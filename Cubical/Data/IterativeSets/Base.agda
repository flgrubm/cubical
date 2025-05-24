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
tilde-∞ (sup-W A f) = f

t : {ℓ : Level} {A B : Type ℓ} → A ≡ B → A → B
t = transport

thm3 : {x y : V∞ {ℓ}} → x ≡ y → Σ[ e ∈ overline-∞ x ≃ overline-∞ y ] tilde-∞ x ∼ (tilde-∞ y ∘ e .fst)
thm3 {x = x} {y = y} p = pathToEquiv (λ i → overline-∞ (p i)) , λ z → λ i → tilde-∞ (p i) (transp (λ j → overline-∞ (p {! !})) i0 z)
-- thm3 {x = x} {y = y} p = pathToEquiv (λ i → overline-∞ (p i)) , λ z → λ i → tilde-∞ (p i) (transport (λ j → overline-∞ (p {! !})) z)

-- thm4 : {x y : V∞} → x ≡ y → (z : V∞) → fiber (tilde-∞ x) z ≃ fiber (tilde-∞ y) z
-- thm4 {x = x} {y = y} p z = transport (λ i → fiber (tilde-∞ (p i)) z) , record { equiv-proof = λ a → ({!!} , {! !}) , {! !} }

-- desup in the future (for V = V⁰)

-- Definition 5 (element V∞)

_∈∞_ : V∞ {ℓ} → V∞ {ℓ} → Type (ℓ-suc ℓ)
x ∈∞ y = fiber (tilde-∞ y) x

isIterativeSet : V∞ {ℓ} → Type (ℓ-suc ℓ)
isIterativeSet (sup-W A f) = (isEmbedding f) × ((a : A) → isIterativeSet (f a))

V⁰ : {ℓ : Level} → Type (ℓ-suc ℓ)
V⁰ {ℓ = ℓ} = Σ[ x ∈ V∞ {ℓ} ] isIterativeSet x

-- theorem 3 + 4
-- Definition 6 (somewhere in the library)
-- same lemma 7
-- Definition 8 important
-- Definition 9
-- ... theorem 12
