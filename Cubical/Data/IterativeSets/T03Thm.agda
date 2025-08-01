module Cubical.Data.IterativeSets.T03Thm where
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

open import Cubical.Foundations.CartesianKanOps

private
  variable
    ℓ ℓ' ℓ'' : Level
    A A' : Type ℓ
    B B' : A → Type ℓ
 
-- module _ (P : ∀ y → x ≡ y → Type ℓ') (d : P x refl) where

--   J : (p : x ≡ y) → P y p
--   J p = transport (λ i → P (p i) (λ j → p (i ∧ j))) d

--   JRefl : J refl ≡ d
--   JRefl = transportRefl d

-- try to first define the function out of x ≡ y?? maybe not
-- module _ {A : Type ℓ} {B : Type ℓ'} {F : A → B} {x y : A} (P : (z : A) → F x ≡ F z → Type ℓ'') (d : P x refl) where
--     J' : (p : F x ≡ F y) → P y p
--     J' p = transport {!!} d

help : (x : V∞ {ℓ}) → (y₁ : Type ℓ) → (p : overline-∞ x ≡ y₁) → Σ[ y₂ ∈ (y₁ → V∞ {ℓ}) ] PathP (λ i → (p i) → V∞ {ℓ}) (tilde-∞ x) y₂
help x y₁ p .fst w = tilde-∞ x (transport (sym p) w)
help x y₁ p .snd i w = tilde-∞ x (transport (λ j → {!p (i ∧ ~ j)!}) w)


thm3-fun' : {ℓ : Level} → {x y : V∞ {ℓ}} → x ≡ y → Σ[ e ∈ overline-∞ x ≃ overline-∞ y ] tilde-∞ x ∼ (tilde-∞ y ∘ e .fst)
thm3-fun' {ℓ} {x} {y} = J (λ z p → Σ[ e ∈ overline-∞ x ≃ overline-∞ z ] tilde-∞ x ∼ (tilde-∞ z ∘ e .fst)) (idEquiv (overline-∞ x) , λ a → refl)

-- helper : {ℓ : Level} → {x y : V∞ {ℓ}} → (e : overline-∞ x ≡ overline-∞ y) → (tilde-∞ x ∼ (tilde-∞ y ∘ transport e)) → x ≡ y
-- helper {ℓ} {x} {y} e h = J (λ z e' → {!((tilde-∞ x ∼ (tilde-∞ z ∘ transport e)) → x ≡ z)!}) (J {!!} {!!} {!!}) e

postulate thm3-inv' : {ℓ : Level} → {x y : V∞ {ℓ}} → (Σ[ e ∈ overline-∞ x ≃ overline-∞ y ] tilde-∞ x ∼ (tilde-∞ y ∘ e .fst)) → x ≡ y
-- thm3-inv' = {!!}

-- (λ z →
--                                Σ-syntax (overline-∞ x ≃ overline-∞ z)
--                                λ e → tilde-∞ x (tilde-∞ z ∘ e .fst))
--                             {!!}) {!!}


-- old part

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
--   f→g j = {!!} -- funExtNonDep {ℓ} {ℓ-suc ℓ} {λ i → A→B i} {λ _ → V∞} {f} {g} (λ {z₀} {z₁} p → h z₀ ∙ {! !}) j

postulate thm3-rightInv : {ℓ : Level} → {x y : V∞ {ℓ}} → section (thm3-fun {ℓ} {x} {y}) (thm3-inv {ℓ} {x} {y})

postulate thm3-leftInv : {ℓ : Level} → {x y : V∞ {ℓ}} → retract (thm3-fun {ℓ} {x} {y}) (thm3-inv {ℓ} {x} {y})


thm3' : {ℓ : Level} → {x y : V∞ {ℓ}} → ((x ≡ y) ≃ (Σ[ e ∈ overline-∞ x ≃ overline-∞ y ] tilde-∞ x ∼ (tilde-∞ y ∘ e .fst)))
thm3' {ℓ = ℓ} {x = x} {y = y} = isoToEquiv (iso (thm3-fun {ℓ} {x} {y}) (thm3-inv {ℓ} {x} {y}) (thm3-rightInv {ℓ} {x} {y}) (thm3-leftInv {ℓ} {x} {y}))

