-- {-# OPTIONS --safe #-}
module Cubical.Data.IterativeSets.Test where
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

open import Cubical.Data.IterativeSets.Base

-- open import Cubical.

open import Cubical.Homotopy.Base

open import Cubical.Data.W.W


-- try something

_≡W'_ : {ℓ ℓ' : Level} → {A : Type ℓ} → {B : A → Type ℓ'} → W A B → W A B → Type (ℓ-max ℓ ℓ')
_≡W'_ {B = B} (sup-W x α) (sup-W y β) = Σ[ p ∈ x ≡ y ] ((z : B x) → (α z ≡W' β (subst B p z)))

_≡W_ : {ℓ ℓ' : Level} → {A : Type ℓ} → {B : A → Type ℓ'} → W A B → W A B → Type (ℓ-max ℓ ℓ')
v ≡W w = (sup-W (overline-W v) (tilde-W v)) ≡W' (sup-W (overline-W w) (tilde-W w))

postulate ≡W-comp : {u v w : W A B} → (u ≡W v) → (v ≡W w) → (u ≡W w)
-- ≡W-comp p q .fst = (p .fst) ∙ (q .fst)
-- ≡W-comp p q .snd z = {!!}

postulate ≡W-refl : (w : W A B) → w ≡W' w
-- ≡W-refl (sup-W _ _) .fst = refl
-- ≡W-refl (sup-W _ α) .snd z = {!!}


-- maybe try to follow https://elisabeth.stenholm.one/category-of-iterative-sets/trees.w-types.html#3487 in order
-- ≡-equiv-≡W : {v w : W A B} → ((v ≡ w) ≃ (v ≡W w))
-- ≡-equiv-≡W {v = v} {w = w} = isoToEquiv (iso to {!!} {!!} {!!})
--   where
--     to : (v ≡ w) → (v ≡W' w)
--     to p = (λ i → overline-W (p i)) , λ z → {!to!}

-- from Gylterud's article

-- mapΣ : {ℓA ℓB ℓC ℓD : Level} → {A : Type ℓA} → {B : Type ℓB} → {C : A → Type ℓC} → {D : B → Type ℓD} → (f : A → B) → (g : (x : A) → C x → D (f x)) → (Σ[ x ∈ A ] C x) → (Σ[ x ∈ B ] D x)
-- mapΣ f g t .fst = f (t .fst)
-- mapΣ f g t .snd = g (t .fst) (t .snd)

equivΣ : {ℓA ℓB ℓC ℓD : Level} → {A : Type ℓA} → {B : Type ℓB} → {C : A → Type ℓC} → {D : B → Type ℓD} → (e : A ≃ B) → ((x : A) → C x ≃ D (e .fst x)) → (Σ[ x ∈ A ] C x) ≃ (Σ[ x ∈ B ] D x)
equivΣ = Σ-cong-equiv

-- lem1 : {ℓ ℓ' : Level} → {A : Type ℓ} → {B : A → Type ℓ'} → {x y : W A B} → ((x ≡ y) ≃ (Σ[ α ∈ overline-W x ≡ overline-W y ] tilde-W x ≡ (tilde-W y ∘ transport (cong B α))))
-- lem1 = {!!}

-- this probably won't work
postulate lem1'' : {ℓ ℓ' : Level} → {A : Type ℓ} → {B : A → Type ℓ'} → {x y : W A B} → ((x ≡ y) ≃ (Σ[ α ∈ overline-W x ≡ overline-W y ] tilde-W x ≡ (tilde-W y ∘ transport (cong B α))))
-- lem1'' {B = B} {x = x} {y = y} = fundamentalTheoremOfId (λ z₁ z₂ → Σ[ α ∈ overline-W z₁ ≡ overline-W z₂ ] (tilde-W z₁ ≡ (tilde-W z₂ ∘ transport (cong B α)))) (λ z → refl , funExt (λ a → cong (tilde-W z) (sym (transportRefl a)))) {!!} x y

-- ∙reflIsId : {A : Type ℓ} → {x y : A} → (p : x ≡ y) → p ∙ refl ≡ p
-- ∙reflIsId p = {!!}

lem1' : {ℓ ℓ' : Level} → {A : Type ℓ} → {B : A → Type ℓ'} → {x y : W A B} → ((x ≡ y) ≃ (Σ[ α ∈ overline-W x ≡ overline-W y ] tilde-W x ≡ (tilde-W y ∘ transport (cong B α))))
lem1' {ℓ} {ℓ'} {A} {B} {x = sup-W a f} {y = sup-W b g} = isoToEquiv (iso to from sec ret) where
  postulate to : sup-W a f ≡ sup-W b g → Σ[ α ∈ a ≡ b ] f ≡ (g ∘ transport (cong B α))
  -- to = J {!!} (refl {x = a} , {!!})

  postulate from : (Σ[ α ∈ a ≡ b ] f ≡ (g ∘ transport (cong B α))) → sup-W a f ≡ sup-W b g
  -- from = {!!}

  postulate sec : section to from
  -- sec = {!!}

  postulate ret : retract to from
  -- ret = {!!}
