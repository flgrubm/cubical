module Cubical.Data.IterativeSets.Sigma where

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Functions.Embedding
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Fiberwise
open import Cubical.Homotopy.Base
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Path

open import Cubical.Data.Sigma

open import Cubical.Data.IterativeSets.Base

private
  variable
    ℓ : Level
    x : V⁰ {ℓ}
    y : El⁰ x → V⁰ {ℓ}

-- TODO: remove private module once the performance issues with ordered and unordered pairs have been resolved
private
    module _ where
        postulate ⟨_,_⟩⁰ : V⁰ {ℓ} → V⁰ {ℓ} → V⁰ {ℓ}

        orderedPair⁰ : (V⁰ {ℓ} × V⁰ {ℓ}) → V⁰ {ℓ}
        orderedPair⁰ = uncurry ⟨_,_⟩⁰

        postulate isEmbOrderedPair⁰ : isEmbedding (orderedPair⁰ {ℓ})

        postulate orderedPair⁰≡orderedPair⁰ : {x y a b : V⁰ {ℓ}} → ((⟨ x , y ⟩⁰ ≡ ⟨ a , b ⟩⁰) ≃ ((x ≡ a) × (y ≡ b)))

-- TODO: move somewhere else
private
    module _ where
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

-- TODO: this should go somewhere in the library
private
    module _ where
        module _ {ℓA ℓB ℓC : Level} {A : Type ℓA} {B : Type ℓB} {C : Type ℓC} (f : A → B) (g : B → C) (h : A → C) where
            isEmbedding-triangle : isEmbedding f → isEmbedding g → (h ≡ (g ∘ f)) → isEmbedding h
            isEmbedding-triangle embf embg p = transport (cong isEmbedding (sym p)) (isEmbedding-∘ embg embf)
        
        module _ {ℓA ℓB ℓD : Level} {A : Type ℓA} {B : A → Type ℓB} {D : A → Type ℓD} (f : (x : A) → B x → D x) where
            total : Σ A B → Σ A D
            total t .fst = t .fst
            total t .snd = uncurry f t

            isEmbedding-total : ((a : A) → isEmbedding (f a)) → isEmbedding total
            isEmbedding-total H = hasPropFibers→isEmbedding λ z → isOfHLevelRespectEquiv 1 (invEquiv (isoToEquiv (fibers-total B D f))) (isEmbedding→hasPropFibers (H (z .fst)) (z .snd))

        module _ {ℓA ℓC ℓD : Level} {A : Type ℓA} {C : Type ℓC} (f : A → C) (D : C → Type ℓD) where
            Σfun-base : Σ A (λ a → D (f a)) → Σ C D
            Σfun-base s .fst = f (s .fst)
            Σfun-base s .snd = s .snd

            -- might need J rule again...
            fiber≃Σfun-base-fiber : (t : Σ C D) → fiber f (t .fst) ≃ fiber Σfun-base t
            fiber≃Σfun-base-fiber (c , d) = isoToEquiv isom
                where
                    isom : Iso (fiber f c) (fiber Σfun-base (c , d))
                    isom .Iso.fun (a , p) = subst (fiber Σfun-base) sigmaPath {!!} -- J (λ c' q → fiber Σfun-base (c' , subst D (sym p ∙ q) d)) {!cong (transport-refl!} p
                        where
                            sigmaPath : (f a , subst D (sym p) d) ≡ (c , d)
                            sigmaPath = (λ i → (p i , subst-filler D p (subst D (sym p) d) i )) ∙ λ i → (c , {!compTransport-is-transportComp d (cong D p)!}) -- (λ i → (c , transportRefl d i))
                    isom .Iso.inv = {!!}
                    isom .Iso.rightInv = {!!}
                    isom .Iso.leftInv = {!!}

            isEmbedding-Σfun-base : isEmbedding f → isEmbedding Σfun-base
            isEmbedding-Σfun-base embf = hasPropFibers→isEmbedding (λ z → isOfHLevelRespectEquiv 1 (fiber≃Σfun-base-fiber z) (isEmbedding→hasPropFibers embf (z .fst)))
        
        module _ {ℓA ℓB ℓC ℓD : Level} {A : Type ℓA} {B : A → Type ℓB} {C : Type ℓC} {D : C → Type ℓD} (f : A → C) (g : (a : A) → B a → D (f a)) where
            Σfun : Σ A B → Σ C D
            Σfun (a , _) .fst = f a
            Σfun (a , b) .snd = g a b

            Σfun-triangle : Σfun ≡ (Σfun-base f D ∘ total g)
            Σfun-triangle = funExt λ t → refl

            isEmbeddingΣ : isEmbedding f → ((a : A) → isEmbedding (g a)) → isEmbedding Σfun
            isEmbeddingΣ embf embga = isEmbedding-triangle (total g) (Σfun-base f D) Σfun (isEmbedding-total g embga) (isEmbedding-Σfun-base f D embf) Σfun-triangle

private
    module _ {ℓ : Level} (x : V⁰ {ℓ}) (y : El⁰ x → V⁰ {ℓ}) where
        emb : (Σ[ a ∈ El⁰ x ] El⁰ (y a)) ↪ V⁰ {ℓ}
        emb .fst (a , b) = ⟨ (tilde-0' x a) , (tilde-0' (y a) b) ⟩⁰
        emb .snd = isEmbedding-∘ isEmbOrderedPair⁰ (isEmbeddingΣ _ _ (isEmbedding-tilde-0 x) λ a → isEmbedding-tilde-0 (y a))
        
Σ⁰ : (x : V⁰ {ℓ}) → (El⁰ x → V⁰ {ℓ}) → V⁰ {ℓ}
Σ⁰ {ℓ = ℓ} x y = sup⁰ ((Σ[ a ∈ El⁰ {ℓ} x ] El⁰ {ℓ} (y a)) , emb x y)

El⁰Σ⁰IsΣ : {x : V⁰ {ℓ}} {y : El⁰ x → V⁰ {ℓ}} → El⁰ (Σ⁰ x y) ≡ (Σ (El⁰ x) (λ a → El⁰ (y a)))
El⁰Σ⁰IsΣ = refl

-- Corollary 25
_×⁰_ : V⁰ {ℓ} → V⁰ {ℓ} → V⁰ {ℓ}
x ×⁰ y = Σ⁰ x (λ _ → y)

El⁰×⁰Is× : {x y : V⁰ {ℓ}} → El⁰ (x ×⁰ y) ≡ ((El⁰ x) × (El⁰ y))
El⁰×⁰Is× = refl
