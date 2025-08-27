module Cubical.Data.IterativeMultisets.Base where

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude

open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Homotopy.Base
open import Cubical.Data.Empty renaming (elim* to ⊥*-elim ; elim to ⊥-elim)
open import Cubical.Data.Unit
open import Cubical.Data.Bool
open import Cubical.Relation.Nullary using (¬_)

open import Cubical.Data.W.W

-- probably move to module Cubical.Data.W (or the corresponding .Properties)

module _ where
    private
        variable
            ℓ ℓ' : Level
            A : Type ℓ
            B : A → Type ℓ'
            x y : W A B

    overline-W : (x : W A B) → A
    overline-W (sup-W a _) = a

    tilde-W : (x : W A B) → B (overline-W x) → W A B
    tilde-W (sup-W _ f) = f

    _∈W_ : {A : Type ℓ} {B : A → Type ℓ'} (x y : W A B) → Type (ℓ-max ℓ ℓ')
    x ∈W y = fiber (tilde-W y) x

    ∈W-irrefl : {x : W A B} → ¬ x ∈W x
    ∈W-irrefl {A = A} {B = B} {x = x} = WInd A B (λ y → ¬ y ∈W y) step x
        where
            step : {s : A} {f : B s → W A B} → ((p : B s) → ¬ f p ∈W f p) → ¬ sup-W s f ∈W sup-W s f
            step indHyp (b , p) = indHyp b (transport (cong (λ r → r ∈W r) (sym p)) (b , p))

    _≡W_ : {ℓ ℓ' : Level} {A : Type ℓ} {B : A → Type ℓ'} → W A B → W A B → Type (ℓ-max ℓ ℓ')
    _≡W_ {A = A} {B = B} x y = Σ[ p ∈ overline-W x ≡ overline-W y ]
                                PathP (λ i → B (p i) → W A B) (tilde-W x) (tilde-W y)

    ≡≃≡W : (x ≡ y) ≃ (x ≡W y)
    ≡≃≡W {x = x} {y = y} = isoToEquiv (iso (f x y) (g x y) (sec x y) (ret x y))
        where
            f : (u v : W A B) → u ≡ v → u ≡W v
            f _ _ p .fst = cong overline-W p
            f _ _ p .snd = cong tilde-W p

            g : (u v : W A B) → u ≡W v → u ≡ v
            g (sup-W _ _) (sup-W _ _) (p , q) = cong₂ sup-W p q

            sec : (u v : W A B) → section (f u v) (g u v)
            sec (sup-W _ _) (sup-W _ _) _ = refl

            ret : (u v : W A B) → retract (f u v) (g u v)
            ret (sup-W _ _) = J> refl

-- V∞ specific

private
  variable
    ℓ ℓ' : Level

V∞ : Type (ℓ-suc ℓ)
V∞ {ℓ} = W (Type ℓ) (λ x → x)

private
  variable
    x y : V∞ {ℓ}

pattern sup-∞ A f = (sup-W A f)

overline-∞ : V∞ {ℓ} → Type ℓ
overline-∞ = overline-W

tilde-∞ : (A : V∞ {ℓ}) → overline-∞ A → V∞ {ℓ}
tilde-∞ = tilde-W

_∈∞_ : V∞ {ℓ} → V∞ {ℓ} → Type (ℓ-suc ℓ)
x ∈∞ y = fiber (tilde-∞ y) x

∈∞-irrefl : ¬ x ∈∞ x
∈∞-irrefl = ∈W-irrefl

postulate thm3 : ((x ≡ y) ≃ (Σ[ e ∈ overline-∞ x ≃ overline-∞ y ] tilde-∞ x ∼ (tilde-∞ y ∘ e .fst)))

postulate thm4 : ((x ≡ y) ≃ ((z : V∞) → fiber (tilde-∞ x) z ≃ fiber (tilde-∞ y) z))

-- examples
emptySet-∞ : V∞ {ℓ}
emptySet-∞ = sup-∞ ⊥* ⊥*-elim

singleton-∞ : V∞ {ℓ} → V∞ {ℓ}
singleton-∞ x = sup-∞ Unit* λ _ → x

unorderedPair-∞ : V∞ → V∞ → V∞
unorderedPair-∞ x y = sup-∞ Bool (λ b → if b then x else y)
