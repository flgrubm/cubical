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
open import Cubical.Data.Sigma
open import Cubical.Foundations.Transport
open import Cubical.Foundations.GroupoidLaws

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

V∞≡sup : x ≡ sup-∞ (overline-∞ x) (tilde-∞ x)
V∞≡sup {x = sup-∞ x α} = refl

thm3-help1 : (x ≡ y) ≃ Path (Σ[ A ∈ Type ℓ ] (A → V∞ {ℓ})) (overline-∞ x , tilde-∞ x) (overline-∞ y , tilde-∞ y)
thm3-help1 {ℓ} {x = sup-∞ x α} {y = sup-∞ y β} = isoToEquiv isom
    where
        isom : Iso (sup-∞ x α ≡ sup-∞ y β)
                   (Path (Σ[ A ∈ Type ℓ ] (A → V∞)) (x , α) (y , β))
        isom .Iso.fun = cong (λ s → overline-∞ s , tilde-∞ s)
        isom .Iso.inv = cong (λ s → sup-∞ (s .fst) (s .snd))
        isom .Iso.rightInv _ = refl
        isom .Iso.leftInv p = cong (λ s → cong s p) (funExt (λ s → sym (V∞≡sup {x = s})))
            -- cong (λ s → sup-∞ (overline-∞ s) (tilde-∞ s)) p
            --     ≡⟨ cong (λ s → cong s p) (funExt (λ s → sym (V∞≡sup {x = s}))) ⟩
            -- cong (λ s → s) p
            --     ∎

thm3-help2 : (x ≡ y) ≃ (Σ[ p ∈ overline-∞ x ≡ overline-∞ y ] transport (λ i → p i → V∞) (tilde-∞ x) ≡ tilde-∞ y)
thm3-help2 = compEquiv thm3-help1 (invEquiv (ΣPathTransport≃PathΣ _ _))

thm3-help3 : {ℓ ℓ' ℓ'' : Level} {A B : Type ℓ} {C : Type ℓ''} (f : A → C) (g : B → C) (p : A ≡ B) → (transport (λ i → p i → C) f ≡ g) ≡ (f ≡ g ∘ (transport p))
thm3-help3 {C = C} f g p = q ∙∙ r ∙∙ s
    where
        q : (transport (λ i → p i → C) f ≡ g) ≡ (transport (λ i → p i → C) f ≡ g ∘ (transport refl))
        q = cong (λ t → (transport (λ i → p i → C) f ≡ g ∘ t)) (funExt (λ x → sym (transportRefl x)))

        r : (transport (λ i → p i → C) f ≡ g ∘ (transport refl)) ≡ (transport refl f ≡ g ∘ (transport p))
        r i = transport (λ j → p (j ∧ (~ i)) → C) f ≡ g ∘ (transport λ j → p (j ∨ ~ i))

        s : (transport refl f ≡ g ∘ (transport p)) ≡ (f ≡ g ∘ (transport p))
        s = cong (λ t → t ≡ g ∘ transport p) (transportRefl f)

thm3' : {ℓ : Level} {x y : V∞ {ℓ}} → (x ≡ y) ≃ (Σ[ p ∈ overline-∞ x ≡ overline-∞ y ] (tilde-∞ x ≡ tilde-∞ y ∘ transport p))
thm3' {ℓ} {x} {y} = compEquiv thm3-help2 (pathToEquiv (Σ-cong-snd (λ p → thm3-help3 {ℓ' = ℓ} (tilde-∞ x) (tilde-∞ y) p)))

thm3 : (x ≡ y) ≃ (Σ[ e ∈ overline-∞ x ≃ overline-∞ y ] tilde-∞ x ≡ (tilde-∞ y ∘ e .fst))
thm3 = compEquiv thm3' (Σ-cong-equiv-fst univalence)

-- thm4-help1 : {ℓ : Level} {x y : V∞ {ℓ}} → Path (Σ[ A ∈ Type ℓ ] (A → V∞ {ℓ})) (overline-∞ x , tilde-∞ x) (overline-∞ y , tilde-∞ y) ≃ ((z : V∞) → fiber (tilde-∞ x) z ≡ fiber (tilde-∞ y) z)
-- thm4-help1 {ℓ} {x} {y} = isoToEquiv isom
--     where
--         isom : Iso
--                 (Path (Σ[ A ∈ Type ℓ ] (A → V∞ {ℓ})) (overline-∞ x , tilde-∞ x) (overline-∞ y , tilde-∞ y))
--                 ((z : V∞) → fiber (tilde-∞ x) z ≡ fiber (tilde-∞ y) z)
--         isom .Iso.fun p z i = Σ[ a ∈ PathPΣ p .fst i ] PathPΣ p .snd i a ≡ z
--         isom .Iso.inv H = ΣPathP (record {
--             fst = ua (isoToEquiv iso1);
--             snd = {!!}})
--                 where
--                     iso1 : Iso (overline-∞ x) (overline-∞ y)
--                     iso1 .Iso.fun a = transport (H (tilde-∞ x a)) (a , refl) .fst
--                     iso1 .Iso.inv a = transport⁻ (H (tilde-∞ y a)) (a , refl) .fst
--                     iso1 .Iso.rightInv a = {!!}
--                     iso1 .Iso.leftInv = {!!}
--         isom .Iso.rightInv = {!!}
--         isom .Iso.leftInv = {!!}
-- thm4-help1 : {ℓ : Level} {x y : V∞ {ℓ}} → Path (Σ[ A ∈ Type ℓ ] (A → V∞ {ℓ})) (overline-∞ x , tilde-∞ x) (overline-∞ y , tilde-∞ y) ≃ ((z : V∞) → fiber (tilde-∞ x) z ≃ fiber (tilde-∞ y) z)
-- thm4-help1 {ℓ} {x} {y} = isoToEquiv isom
--     where
--         isom : Iso
--                 (Path (Σ[ A ∈ Type ℓ ] (A → V∞ {ℓ})) (overline-∞ x , tilde-∞ x) (overline-∞ y , tilde-∞ y))
--                 ((z : V∞) → fiber (tilde-∞ x) z ≃ fiber (tilde-∞ y) z)
--         isom .Iso.fun p z = isoToEquiv isoFun
--             where
--                 isoFun : Iso (fiber (tilde-∞ x) z) (fiber (tilde-∞ y) z)
--                 isoFun .Iso.fun fib .fst = transport (PathPΣ p .fst) (fib .fst)
--                 isoFun .Iso.fun fib .snd = {!!}
--                 isoFun .Iso.inv = {!!}
--                 isoFun .Iso.rightInv = {!!}
--                 isoFun .Iso.leftInv = {!!}
--         isom .Iso.inv = {!!}
--         isom .Iso.rightInv = {!!}
--         isom .Iso.leftInv = {!!}
        
thm4-help2 : {ℓ : Level} {x y : V∞ {ℓ}} → (Σ[ e ∈ overline-∞ x ≃ overline-∞ y ] tilde-∞ x ≡ (tilde-∞ y ∘ e .fst)) ≃ ((z : V∞) → fiber (tilde-∞ x) z ≃ fiber (tilde-∞ y) z)
thm4-help2 {ℓ} {x} {y} = isoToEquiv isom
    where
        isom : Iso
                (Σ[ e ∈ overline-∞ x ≃ overline-∞ y ] (tilde-∞ x ≡ tilde-∞ y ∘ e .fst))
                ((z : V∞) → fiber (tilde-∞ x) z ≃ fiber (tilde-∞ y) z)
        isom .Iso.fun s z = {!!}
        isom .Iso.inv = {!!}
        isom .Iso.rightInv = {!!}
        isom .Iso.leftInv = {!!}

postulate thm4 : ((x ≡ y) ≃ ((z : V∞) → fiber (tilde-∞ x) z ≃ fiber (tilde-∞ y) z))

-- examples
emptySet-∞ : V∞ {ℓ}
emptySet-∞ = sup-∞ ⊥* ⊥*-elim

singleton-∞ : V∞ {ℓ} → V∞ {ℓ}
singleton-∞ x = sup-∞ Unit* λ _ → x

unorderedPair-∞ : V∞ → V∞ → V∞
unorderedPair-∞ x y = sup-∞ Bool (λ b → if b then x else y)
