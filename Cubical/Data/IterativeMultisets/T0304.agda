module Cubical.Data.IterativeMultisets.T0304 where

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
open import Cubical.Data.IterativeMultisets.Base

-- probably move to module Cubical.Data.W (or the corresponding .Properties)

module _ where
    -- first define substP
    postulate substCompositeP : ∀ {ℓ ℓ'} {A : Type ℓ} → (B : A → Type ℓ') → {x y z : A} (p : x ≡ y) (q : y ≡ z) (u : B x) → subst B (p ∙ q) u ≡ subst B q (subst B p u)

module _ where
    private
        variable
            ℓ ℓ' : Level
            A : Type ℓ
            B : A → Type ℓ'
            x y : W A B

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

    _≡fib∞_ : {ℓ : Level} → V∞ {ℓ} → V∞ {ℓ} → Type (ℓ-suc ℓ)
    x ≡fib∞ y = (z : V∞) → (fiber (tilde-W x) z) ≃ (fiber (tilde-W y) z) 

    open Iso
    
    ≡≃≡fib∞ : {ℓ : Level} {x y : V∞ {ℓ}} → (x ≡W y) ≃ (x ≡fib∞ y)
    ≡≃≡fib∞ {ℓ} {x} {y} = isoToEquiv (iso (f x y) (g x y) (sec x y) (ret x y))
        where
            f : (u v : V∞ {ℓ}) → u ≡W v → u ≡fib∞ v
            f u v (p , q) z = isoToEquiv isom
                where
                    postulate isom : Iso (fiber (tilde-W u) z) (fiber (tilde-W v) z)
                    -- isom .fun (au , _) .fst = transport p au
                    -- isom .fun (au , su) .snd = subst (_≡ z) (λ i → q i (transport-filler p au i)) su
                    -- isom .inv (av , sv) .fst = transport (sym p) av
                    -- isom .inv (av , sv) .snd = subst (_≡ z) (λ i → q (~ i) (transport-filler (sym p) av i)) sv
                    -- isom .rightInv (av , sv) = ΣPathP ((
                    --     transport p (transport (sym p) av) ≡⟨ sym (transportComposite (sym p) p av) ⟩
                    --     transport (sym p ∙ p) av ≡⟨ cong (flip transport av) (lCancel p) ⟩
                    --     transport refl av ≡⟨ transportRefl av ⟩
                    --     av ∎) , {!!})
                    -- -- basically same as rightInv
                    -- isom .leftInv = {!!}
            g : (u v : V∞ {ℓ}) → u ≡fib∞ v → u ≡W v
            g u v F .fst = ua (isoToEquiv isom)
                where
                    isom : Iso (overline-W u) (overline-W v)
                    isom .fun a = F (tilde-∞ u a) .fst (a , refl) .fst
                    isom .inv = {!!}
                    isom .rightInv = {!!}
                    isom .leftInv = {!!}
            g u v F .snd = {!!}
            postulate sec : (u v : V∞ {ℓ}) → section (f u v) (g u v)
            postulate ret : (u v : V∞ {ℓ}) → retract (f u v) (g u v)
