module Cubical.Data.IterativeSets.T03New where
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
open import Cubical.Foundations.Path

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
    B B' : A → Type ℓ'

-- try : {x y : V∞ {ℓ}} → x ≡ y → Σ[ e ∈ overline-∞ x ≡ overline-∞ y ] tilde-∞ x ∼ (tilde-∞ y ∘ transport e)
-- try {x = x} {y = y} = J (λ z p → Σ[ e ∈ overline-∞ x ≡ overline-∞ z ] tilde-∞ x ∼ (tilde-∞ z ∘ transport e)) (refl , λ a → sym (cong (tilde-∞ x) (transportRefl a)))

-- tryInv : {x y : V∞ {ℓ}} → (Σ[ e ∈ overline-∞ x ≡ overline-∞ y ] tilde-∞ x ≡ (tilde-∞ y ∘ transport e)) → x ≡ y
-- tryInv {ℓ = ℓ} {x = sup-∞ A f} {y = sup-∞ B g} (P , H) = J2 fam refl P H 
--     where
--         fam : (C : Type ℓ) → A ≡ C → (h : A → V∞ {ℓ}) → f ≡ h → Type (ℓ-suc ℓ)
--         fam C p h p' = (sup-∞ A f) ≡ sup-∞ C {!h!}

-- this should really be in the library, but I haven't found it there?

refl∙refl≡refl : {A : Type ℓ} {x : A} → refl ∙ refl ≡ refl {x = x}
refl∙refl≡refl = sym (compPath-filler refl refl)

∙refl-is-identity : {A B : Type ℓ} (p : A ≡ B) → p ∙ refl ≡ p
∙refl-is-identity p = sym (compPath-filler p refl)

∙refl-is-identity' : {A B : Type ℓ} (p : A ≡ B) → p ∙ refl ≡ p
∙refl-is-identity' = J (λ C q → q ∙ refl ≡ q) refl∙refl≡refl

refl∙-is-identity : {A B : Type ℓ} (p : A ≡ B) → refl ∙ p ≡ p
refl∙-is-identity = J (λ C q → refl ∙ q ≡ q) refl∙refl≡refl

compTransport-is-transportComp : {A B C : Type ℓ} (x : A) (p : A ≡ B) (q : B ≡ C) → transport q (transport p x) ≡ transport (p ∙ q) x
compTransport-is-transportComp x p q = J (λ y q' → transport q' (transport p x) ≡ transport (p ∙ q') x) (transportRefl (transport p x) ∙ cong (λ r → transport r x) (sym (∙refl-is-identity p))) q

Path∙symPath-cancel : {A B : Type ℓ} (p : A ≡ B) → p ∙ (sym p) ≡ refl
Path∙symPath-cancel p = cong (λ r → p ∙ r) (sym (∙refl-is-identity (sym p))) ∙ compPathl-cancel p refl

symPath∙Path-cancel : {A B : Type ℓ} (p : A ≡ B) → (sym p) ∙ p ≡ refl
symPath∙Path-cancel p = cong (λ r → r ∙ p) (sym (refl∙-is-identity (sym p))) ∙ compPathr-cancel p refl

fun' : {x y : V∞ {ℓ}} → (Σ[ p ∈ (overline-∞ x ≡ overline-∞ y) ] (tilde-∞ x ≡ (tilde-∞ y ∘ (transport p)))) → (x ≡ y)
fun' {ℓ} {x = sup-∞ A f} {y = sup-∞ B g} (p , q) i = sup-W (p i) (k' i)
    where
        -- k : (j : I) → p j → V∞ {ℓ}
        k : PathP (λ j → p j → V∞ {ℓ}) (f ∘ (transport refl)) (g ∘ (transport p) ∘ (transport (sym p)))
        k j z = q j (transport (λ k → p (j ∧ ~ k)) z)

        k' : PathP (λ j → p j → V∞ {ℓ}) f g
        k' = funExt fpart ◁ k ▷ funExt gpart
            where
                fpart : (a : A) → f a ≡ f (transport refl a)
                fpart a = cong f (sym (transportRefl a))
                gpart : (b : B) → g (transport p (transport (sym p) b)) ≡ g b
                gpart b = cong g (compTransport-is-transportComp b (sym p) p ∙ cong (λ r → transport r b) (symPath∙Path-cancel p) ∙ transportRefl b)
