{-# OPTIONS --lossy-unification #-}
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
open import Cubical.Foundations.Transport

open import Cubical.Data.Sigma

open import Cubical.Data.IterativeSets.Base
open import Cubical.Data.IterativeSets.OrderedPair

private
  variable
    ℓ : Level
    x : V⁰ {ℓ}
    y : El⁰ x → V⁰ {ℓ}


-- -- TODO: move somewhere else
-- private
--     module _ where
--         refl∙refl≡refl : {A : Type ℓ} {x : A} → refl ∙ refl ≡ refl {x = x}
--         refl∙refl≡refl = sym (compPath-filler refl refl)

--         ∙refl-is-identity : {A B : Type ℓ} (p : A ≡ B) → p ∙ refl ≡ p
--         ∙refl-is-identity p = sym (compPath-filler p refl)

--         ∙refl-is-identity' : {A B : Type ℓ} (p : A ≡ B) → p ∙ refl ≡ p
--         ∙refl-is-identity' = J (λ C q → q ∙ refl ≡ q) refl∙refl≡refl

--         refl∙-is-identity : {A B : Type ℓ} (p : A ≡ B) → refl ∙ p ≡ p
--         refl∙-is-identity = J (λ C q → refl ∙ q ≡ q) refl∙refl≡refl

--         compTransport-is-transportComp : {A B C : Type ℓ} (x : A) (p : A ≡ B) (q : B ≡ C) → transport q (transport p x) ≡ transport (p ∙ q) x
--         compTransport-is-transportComp x p q = J (λ y q' → transport q' (transport p x) ≡ transport (p ∙ q') x) (transportRefl (transport p x) ∙ cong (λ r → transport r x) (sym (∙refl-is-identity p))) q

--         Path∙symPath-cancel : {A B : Type ℓ} (p : A ≡ B) → p ∙ (sym p) ≡ refl
--         Path∙symPath-cancel p = cong (λ r → p ∙ r) (sym (∙refl-is-identity (sym p))) ∙ compPathl-cancel p refl

--         symPath∙Path-cancel : {A B : Type ℓ} (p : A ≡ B) → (sym p) ∙ p ≡ refl
--         symPath∙Path-cancel p = cong (λ r → r ∙ p) (sym (refl∙-is-identity (sym p))) ∙ compPathr-cancel p refl

-- -- TODO: this should go somewhere in the library
-- private
--     module _ where
--         module _ {ℓA ℓB ℓC : Level} {A : Type ℓA} {B : Type ℓB} {C : Type ℓC} (f : A → B) (g : B → C) (h : A → C) where
--             isEmbedding-triangle : isEmbedding f → isEmbedding g → (h ≡ (g ∘ f)) → isEmbedding h
--             isEmbedding-triangle embf embg p = transport (cong isEmbedding (sym p)) (isEmbedding-∘ embg embf)
        
--         module _ {ℓA ℓB ℓD : Level} {A : Type ℓA} {B : A → Type ℓB} {D : A → Type ℓD} (f : (x : A) → B x → D x) where
--             total : Σ A B → Σ A D
--             total t .fst = t .fst
--             total t .snd = uncurry f t

--             isEmbedding-total : ((a : A) → isEmbedding (f a)) → isEmbedding total
--             isEmbedding-total H = hasPropFibers→isEmbedding λ z → isOfHLevelRespectEquiv 1 (invEquiv (isoToEquiv (fibers-total B D f))) (isEmbedding→hasPropFibers (H (z .fst)) (z .snd))

--         module _ {ℓA ℓC ℓD : Level} {A : Type ℓA} {C : Type ℓC} (f : A → C) (D : C → Type ℓD) where
--             Σfun-base : Σ A (λ a → D (f a)) → Σ C D
--             Σfun-base s .fst = f (s .fst)
--             Σfun-base s .snd = s .snd

--             -- might need J rule again...
--             fiber≃Σfun-base-fiber : (t : Σ C D) → fiber f (t .fst) ≃ fiber Σfun-base t
--             fiber≃Σfun-base-fiber (c , d) = isoToEquiv (iso to from sec ret)
--                 where
--                     to : fiber f c → fiber Σfun-base (c , d)
--                     to (a , p) .fst .fst = a
--                     to (a , p) .fst .snd = subst D (sym p) d
--                     to (a , p) .snd i .fst = p i
--                     to (a , p) .snd i .snd = subst-filler D (sym p) d (~ i)
--                     -- to (a , p) .snd = ΣPathP (p , λ i → subst-filler D (sym p) d (~ i))
--                     from : fiber Σfun-base (c , d) → fiber f c
--                     from ((a , d') , p) .fst = a
--                     from ((a , d') , p) .snd i = p i .fst
--                     postulate sec : section to from
--                     -- sec ((a , d') , p) =
--                     --     to (from ((a , d') , p))
--                     --         ≡⟨⟩
--                     --     to (a , λ i → p i .fst)
--                     --         ≡⟨⟩
--                     --     -- (a , subst D _ d) , λ i → (p i , subst-filler D _ d (~ i))
--                     --     {!!}
--                     --         ≡⟨ {!!} ⟩
--                     --     (a , d') , p
--                     --         ∎
--                     postulate ret : retract to from

--             postulate fiber≃Σfun-base-fiber' : (t : Σ C D) → fiber f (t .fst) ≃ fiber Σfun-base t
--             -- fiber≃Σfun-base-fiber' t = isoToEquiv (iso (to t) (from t) {!!} {!!})
--             --     where
--             --         to : (t' : Σ C D) → fiber f (t' .fst) → fiber Σfun-base t'
--             --         to (c , d) (a , p) .fst .fst = a
--             --         to (c , d) (a , p) .fst .snd = subst D (sym p) d
--             --         to (c , d) (a , p) .snd i .fst = p i
--             --         to (c , d) (a , p) .snd i .snd = subst-filler D (sym p) d (~ i)
--             --         from : (t' : Σ C D) → fiber Σfun-base t → fiber f (t .fst)
--             --         from (c , d) ((a , d') , p) .fst = a
--             --         from (c , d) ((a , d') , p) .snd = cong fst p
            

--             isEmbedding-Σfun-base : isEmbedding f → isEmbedding Σfun-base
--             isEmbedding-Σfun-base embf = hasPropFibers→isEmbedding (λ z → isOfHLevelRespectEquiv 1 (fiber≃Σfun-base-fiber z) (isEmbedding→hasPropFibers embf (z .fst)))
        
--         module abc {ℓA ℓB ℓC ℓD : Level} {A : Type ℓA} {B : A → Type ℓB} {C : Type ℓC} {D : C → Type ℓD} (f : A → C) (g : (a : A) → B a → D (f a)) where
--             Σfun : Σ A B → Σ C D
--             Σfun (a , _) .fst = f a
--             Σfun (a , b) .snd = g a b

--             Σfun-triangle : Σfun ≡ (Σfun-base f D ∘ total g)
--             Σfun-triangle = funExt λ t → refl

--             isEmbeddingΣ : isEmbedding f → ((a : A) → isEmbedding (g a)) → isEmbedding Σfun
--             isEmbeddingΣ embf embga = isEmbedding-triangle (total g) (Σfun-base f D) Σfun (isEmbedding-total g embga) (isEmbedding-Σfun-base f D embf) Σfun-triangle

-- private
--     module _ {ℓA ℓB ℓC : Level} {A : Type ℓA} {B : Type ℓB} {C : Type ℓC} (f : A → B) (g : A → C) where
--       f×g : A → B × C
--       f×g a .fst = f a
--       f×g a .snd = g a

--       Δ : A → A × A
--       Δ x .fst = x
--       Δ x .snd = x
      
--       emb-Δ : isSet A → isEmbedding Δ
--       emb-Δ setA x y = propBiimpl→Equiv (setA x y) (isSet× setA setA (x , x) (y , y)) (cong Δ) (cong fst) .snd

--       isEmbedding-× : isSet B → isSet C → isEmbedding f → isEmbedding f×g
--       isEmbedding-× setB setC embf = injEmbedding (isSet× setB setC) λ {x} {y} p → isEmbedding→Inj embf x y (cong fst p)


module _ {ℓA ℓA' ℓB ℓB' : Level} {A : Type ℓA} {B : A → Type ℓB} {A' : Type ℓA'} {B' : A' → Type ℓB'} (f : A → A') (g : (a : A) → B a → B' (f a)) where
    Σfun : Σ A B → Σ A' B'
    Σfun (a , _) .fst = f a
    Σfun (a , b) .snd = g a b

    private
        module _ {ℓ ℓ' : Level} {M : Type ℓ} {N : Type ℓ'} (h : M → N) where
            Inj : Type (ℓ-max ℓ ℓ')
            Inj = {x y : M} → h x ≡ h y → x ≡ y

    Inj-Σfun : isEmbedding f → ((a : A) → isEmbedding (g a)) → Inj Σfun
    Inj-Σfun embf embg {a , b} {a' , b'} p = ΣPathP (q₁ , q₂)
        where
            ΣP₁ : Σ[ q ∈ f a ≡ f a' ] subst B' q (g a b) ≡ (g a' b')
            ΣP₁ = PathΣ→ΣPathTransport _ _ p

            ΣP₂ : Σ[ q ∈ a ≡ a' ] subst (λ a → B' (f a)) q (g a b) ≡ (g a' b')
            ΣP₂ = invEq (Σ-cong-equiv-fst {B = λ q → subst B' q (g a b) ≡ (g a' b')} ((cong f :> (a ≡ a' → f a ≡ f a')), embf a a')) ΣP₁

            q₁ : a ≡ a'
            q₁ = ΣP₂ .fst
            
            Pg₁ : g a' (subst B q₁ b) ≡ subst (λ a → B' (f a)) q₁ (g a b)
            Pg₁ = sym (substCommSlice B (λ a → B' (f a)) g {a} {a'} q₁ b)

            Pg₂ : g a' (subst B q₁ b) ≡ g a' b'
            Pg₂ = Pg₁ ∙ ΣP₂ .snd

            P : subst B q₁ b ≡ b'
            P = isEmbedding→Inj (embg a') (subst B q₁ b) b' Pg₂

            q₂ : PathP (λ i → B (q₁ i)) b b'
            q₂ = toPathP P

    Emb-Σfun : isSet (Σ A' B') → isEmbedding f → ((a : A) → isEmbedding (g a)) → isEmbedding Σfun
    Emb-Σfun setΣ embf embg = injEmbedding setΣ (Inj-Σfun embf embg)

Σ⁰ : (x : V⁰ {ℓ}) → (El⁰ x → V⁰ {ℓ}) → V⁰ {ℓ}
Σ⁰ {ℓ = ℓ} x y = fromEmb E
  where
    E : Embedding (V⁰ {ℓ}) ℓ
    E .fst = (Σ[ a ∈ El⁰ {ℓ} x ] El⁰ {ℓ} (y a))
    E .snd .fst (a , b) = ⟨ (tilde x a) , (tilde (y a) b) ⟩⁰
    E .snd .snd = isEmbedding-∘ isEmbOrderedPair⁰ (Emb-Σfun _ _ (isSetΣ isSetV⁰ (λ _ → isSetV⁰)) (isEmbedding-tilde x) λ a → isEmbedding-tilde (y a))

El⁰Σ⁰IsΣ : {x : V⁰ {ℓ}} {y : El⁰ x → V⁰ {ℓ}} → El⁰ (Σ⁰ x y) ≡ (Σ (El⁰ x) (λ a → El⁰ (y a)))
El⁰Σ⁰IsΣ = refl

-- Corollary 25
_×⁰_ : V⁰ {ℓ} → V⁰ {ℓ} → V⁰ {ℓ}
x ×⁰ y = Σ⁰ x (λ _ → y)

El⁰×⁰Is× : {x y : V⁰ {ℓ}} → El⁰ (x ×⁰ y) ≡ ((El⁰ x) × (El⁰ y))
El⁰×⁰Is× = refl
