module Cubical.Data.IterativeMultisets.Base where

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude

open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Relation.Nullary using (¬_)
open import Cubical.Data.Sigma
open import Cubical.Functions.Fibration
open import Cubical.Functions.Embedding
open import Cubical.Foundations.Univalence

open import Cubical.Data.Empty renaming (elim* to ⊥*-elim ; elim to ⊥-elim)
open import Cubical.Data.Unit
open import Cubical.Data.Bool

open import Cubical.Data.W.W

private
  variable
    ℓ ℓ' : Level

V∞ : Type (ℓ-suc ℓ)
V∞ {ℓ} = W (Type ℓ) (λ x → x)

open Cubical.Data.W.W.W renaming (sup-W to sup-∞) public

private
  variable
    x y : V∞ {ℓ}


overline = nodes

tilde : (A : V∞ {ℓ}) → overline A → V∞ {ℓ}
tilde = arities

V∞-overline-tilde : x ≡ sup-∞ (overline x) (tilde x)
V∞-overline-tilde = W-nodes-arities

_∈∞_ : V∞ {ℓ} → V∞ {ℓ} → Type (ℓ-suc ℓ)
x ∈∞ y = fiber (tilde y) x

∈∞-irrefl : ¬ x ∈∞ x
∈∞-irrefl = ∈W-irrefl

toFib : V∞ {ℓ} → Fibration (V∞ {ℓ}) ℓ
toFib x .fst = overline x
toFib x .snd = tilde x

fromFib : Fibration (V∞ {ℓ}) ℓ → V∞ {ℓ}
fromFib fib = sup-∞ (fib .fst) (fib .snd)

retFib : retract (toFib {ℓ}) (fromFib {ℓ})
retFib (sup-∞ _ _) = refl

secFib : section (toFib {ℓ}) (fromFib {ℓ})
secFib _ = refl

Iso-V∞-Fib : Iso (V∞ {ℓ}) (Fibration (V∞ {ℓ}) ℓ)
Iso-V∞-Fib .Iso.fun = toFib
Iso-V∞-Fib .Iso.inv = fromFib
Iso-V∞-Fib .Iso.rightInv = secFib
Iso-V∞-Fib .Iso.leftInv = retFib

V∞≃Fib : V∞ {ℓ} ≃ Fibration (V∞ {ℓ}) ℓ
V∞≃Fib = isoToEquiv Iso-V∞-Fib

≡V∞-≃-≡Fib : {ℓ : Level} {x y : V∞ {ℓ}} → (x ≡ y) ≃ (toFib x ≡ toFib y)
≡V∞-≃-≡Fib {x = x} {y = y} .fst = cong toFib
≡V∞-≃-≡Fib {x = x} {y = y} .snd = iso→isEmbedding Iso-V∞-Fib x y

-- explicitly writing down the isomorphism
Iso-≡V∞-≡Fib' : Iso (x ≡ y) (Path (Fibration (V∞ {ℓ}) ℓ) (overline x , tilde x) (overline y , tilde y))
Iso-≡V∞-≡Fib' {x = sup-∞ x α} {y = sup-∞ y β} .Iso.fun = cong (λ s → overline s , tilde s)
Iso-≡V∞-≡Fib' {x = sup-∞ x α} {y = sup-∞ y β} .Iso.inv = cong (λ s → sup-∞ (s .fst) (s .snd))
Iso-≡V∞-≡Fib' {x = sup-∞ x α} {y = sup-∞ y β} .Iso.rightInv _ = refl
Iso-≡V∞-≡Fib' {x = sup-∞ x α} {y = sup-∞ y β} .Iso.leftInv p = cong (λ s → cong s p) (funExt (λ s → sym (V∞-overline-tilde {x = s})))

≡V∞-≃-≡Fib' : (x ≡ y) ≃ Path (Fibration (V∞ {ℓ}) ℓ) (overline x , tilde x) (overline y , tilde y)
≡V∞-≃-≡Fib' = isoToEquiv Iso-≡V∞-≡Fib'

≡V∞-≃-≃Fib : (x ≡ y) ≃ ((overline x , tilde x) ≃Fib (overline y , tilde y))
≡V∞-≃-≃Fib = compEquiv ≡V∞-≃-≡Fib (invEquiv (FibrationIP _ _))

-- TODO: move this to a better place
private
  transport→≡∘ : {ℓ ℓ' : Level} {A B : Type ℓ} {C : Type ℓ'}
                 (f : A → C) (g : B → C) (p : A ≡ B) →
                 (transport (λ i → p i → C) f ≡ g) ≡ (f ≡ g ∘ (transport p))
  transport→≡∘ {C = C} f g p = q ∙∙ r ∙∙ s
        where
            q : (transport (λ i → p i → C) f ≡ g) ≡ (transport (λ i → p i → C) f ≡ g ∘ (transport refl))
            q = cong (λ t → (transport (λ i → p i → C) f ≡ g ∘ t)) (funExt (λ x → sym (transportRefl x)))

            r : (transport (λ i → p i → C) f ≡ g ∘ (transport refl)) ≡ (transport refl f ≡ g ∘ (transport p))
            r i = transport (λ j → p (j ∧ (~ i)) → C) f ≡ g ∘ (transport λ j → p (j ∨ ~ i))

            s : (transport refl f ≡ g ∘ (transport p)) ≡ (f ≡ g ∘ (transport p))
            s = cong (λ t → t ≡ g ∘ transport p) (transportRefl f)

≡V∞-≃-transport≡ : {ℓ : Level} {x y : V∞ {ℓ}} →
                   (x ≡ y) ≃ (Σ[ p ∈ overline x ≡ overline y ] (tilde x ≡ tilde y ∘ transport p))
≡V∞-≃-transport≡ {ℓ} {x} {y} = compEquiv (compEquiv ≡V∞-≃-≡Fib (invEquiv (ΣPathTransport≃PathΣ _ _)))
                                         (pathToEquiv (Σ-cong-snd (λ p → transport→≡∘ (tilde x) (tilde y) p)))

≡V∞-≃-transport≃ : (x ≡ y) ≃ (Σ[ e ∈ overline x ≃ overline y ] tilde x ≡ (tilde y ∘ e .fst))
≡V∞-≃-transport≃ = compEquiv ≡V∞-≃-transport≡ (Σ-cong-equiv-fst univalence)


-- examples

emptySet-∞ : V∞ {ℓ}
emptySet-∞ = sup-∞ ⊥* ⊥*-elim

singleton-∞ : V∞ {ℓ} → V∞ {ℓ}
singleton-∞ x = sup-∞ Unit* λ _ → x

unorderedPair-∞ : V∞ → V∞ → V∞
unorderedPair-∞ x y = sup-∞ Bool (λ b → if b then x else y)


-- TODO: Remove

thm3-help1 : (x ≡ y) ≃ Path (Σ[ A ∈ Type ℓ ] (A → V∞ {ℓ})) (overline x , tilde x) (overline y , tilde y)
thm3-help1 = ≡V∞-≃-≡Fib
{-# WARNING_ON_USAGE thm3-help1 "Deprecated: use ≡V∞-≃-≡Fib" #-}

thm3-help2 : (x ≡ y) ≃ (Σ[ p ∈ overline x ≡ overline y ] transport (λ i → p i → V∞) (tilde x) ≡ tilde y)
thm3-help2 = compEquiv ≡V∞-≃-≡Fib (invEquiv (ΣPathTransport≃PathΣ _ _))
{-# WARNING_ON_USAGE thm3-help2 "Deprecated: use inlined" #-}

thm3-help3 : {ℓ ℓ' : Level} {A B : Type ℓ} {C : Type ℓ'} (f : A → C) (g : B → C) (p : A ≡ B) → (transport (λ i → p i → C) f ≡ g) ≡ (f ≡ g ∘ (transport p))
thm3-help3 = transport→≡∘
{-# WARNING_ON_USAGE thm3-help3 "Deprecated: use transport→≡∘" #-}

thm3 : (x ≡ y) ≃ (Σ[ e ∈ overline x ≃ overline y ] tilde x ≡ (tilde y ∘ e .fst))
thm3 = ≡V∞-≃-transport≃
{-# WARNING_ON_USAGE thm3 "Deprecated: use ≡V∞-≃-transport≃" #-}

thm4 : ((x ≡ y) ≃ ((z : V∞) → fiber (tilde x) z ≃ fiber (tilde y) z))
thm4 = ≡V∞-≃-≃Fib
{-# WARNING_ON_USAGE thm3 "Deprecated: use ≡V∞-≃-≃Fib" #-}
