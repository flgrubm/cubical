{-# OPTIONS --lossy-unification #-}
{-# OPTIONS --allow-unsolved-metas #-}


module Cubical.Data.IterativeSets.Pi where

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Data.Sigma
open import Cubical.Functions.Embedding
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Homotopy.Base
open import Cubical.Foundations.Transport

open import Cubical.Data.IterativeMultisets.Base
open import Cubical.Data.IterativeSets.Base
open import Cubical.Data.IterativeSets.OrderedPair


private
  variable
    ℓ : Level
    x : V⁰ {ℓ}
    y : El⁰ x → V⁰ {ℓ}

module _ {ℓ ℓ' ℓ'' : Level} {A : Type ℓ} {B : A → Type ℓ'} {X : Type ℓ''} (setA : isSet A) (propB : (a : A) → isProp (B a)) (f : X → Σ A B) where
    f₁ : X → A
    f₁ x = f x .fst

    isEmbeddingFstIsEmbedding : isEmbedding f₁ → isEmbedding f
    isEmbeddingFstIsEmbedding embf₁ = hasPropFibers→isEmbedding
        (λ z → isPropRetract (λ x → x .fst , cong fst (x .snd))
                             (λ x → (x .fst) , (Σ≡Prop propB (x .snd)))
                             (λ fib → cong (fib .fst ,_) (isSetΣ setA (λ x → isProp→isSet (propB x)) _ _ _ _))
                             (isEmbedding→hasPropFibers embf₁ (z .fst)))
    
module _ {ℓ ℓ' ℓ'' : Level} {A : Type ℓ} {B : A → Type ℓ'} {a₀ : A} {X : Type ℓ''} (f : X ↪ B a₀) where
    g : X → Σ A B
    g x .fst = a₀
    g x .snd = f .fst x

    isEmbeddingSndIsEmbedding : isEmbedding g
    isEmbeddingSndIsEmbedding x y = isoToIsEquiv isom
         where
             isom : Iso (x ≡ y) (g x ≡ g y)
             isom .Iso.fun = _
             isom .Iso.inv p = {!cong snd p!}
             isom .Iso.rightInv = {!!}
             isom .Iso.leftInv = {!!}
    -- hasPropFibers→isEmbedding (λ z → isPropRetract {B = Σ[ p ∈ a₀ ≡ z .fst ] fiber (f .fst) (subst⁻ B p (z .snd))} (λ x → cong fst (x .snd) , ((x .fst) , {!!} ∙ {!!})) {!!} {!!} {!!})
    -- isEmbeddingSndIsEmbedding = hasPropFibers→isEmbedding (λ z → isPropRetract {!!} {!!} {!!} (isEmbedding→hasPropFibers (f .snd) {!z .fst!}))
    

-- module _ {x : V⁰ {ℓ}} {y : El⁰ x → V⁰ {ℓ}} where
--     private
--         module _ where
--             emb : ((a : El⁰ x) → El⁰ (y a)) → (El⁰ x ↪ V⁰ {ℓ})
--             emb ϕ .fst a = ⟨ tilde-0' x a , tilde-0' (y a) (ϕ a) ⟩⁰
--             emb ϕ .snd = injEmbedding thm12 f
--                 where
--                     f : {v w : El⁰ x} → emb ϕ .fst v ≡ emb ϕ .fst w → v ≡ w
--                     f {v} {w} p = isEmbedding→Inj (isEmbedding-tilde-0 x) _ _ (orderedPair⁰≡orderedPair⁰ .fst p .fst)

--             elem : ((a : El⁰ x) → El⁰ (y a)) → Σ[ A ∈ Type ℓ ] A ↪ V⁰ {ℓ}
--             elem ϕ .fst = El⁰ x
--             elem ϕ .snd = emb ϕ

--             emb-emb : isEmbedding emb
--             emb-emb = isEmbeddingFstIsEmbedding (isSetΠ λ _ → thm12) (λ _ → isPropIsEmbedding) emb (injEmbedding (isSetΠ (λ _ → thm12)) inj)
--                 where
--                     inj : {ϕ ψ : (a : El⁰ x) → El⁰ (y a)} → emb ϕ .fst ≡ emb ψ .fst → ϕ ≡ ψ
--                     inj {ϕ} {ψ} p = funExt (λ a →
--                         let
--                             h : (tilde-0' x a ≡ tilde-0' x a) × (tilde-0' (y a) (ϕ a) ≡ tilde-0' (y a) (ψ a))
--                             h = orderedPair⁰≡orderedPair⁰ .fst (funExt⁻ p a)

--                             hh : tilde-0' (y a) (ϕ a) ≡ tilde-0' (y a) (ψ a)
--                             hh = h .snd

--                             hhh : ϕ a ≡ ψ a
--                             hhh = isEmbedding→Inj (isEmbedding-tilde-0 (y a)) _ _ hh
--                         in hhh)
            
--             emb-elem : isEmbedding elem
--             emb-elem = isEmbeddingSndIsEmbedding (emb , emb-emb)

--     graph⁰ : ((a : El⁰ x) → El⁰ (y a)) ↪ V⁰ {ℓ}
--     graph⁰ = compEmbedding (Equiv→Embedding (invEquiv (sup⁰desup⁰≃))) (elem , emb-elem)

--     -- _ : (ϕ : (a : El⁰ x) → El⁰ (y a)) → cor11 .fst (sup⁰ (elem ϕ)) ≡ (sup-∞ (El⁰ x) (λ a → ⟨ tilde-0' x a , tilde-0' (y a) (ϕ a) ⟩⁰ .fst))
--     -- _ = λ ϕ → refl

-- Π⁰ : (x : V⁰ {ℓ}) → (El⁰ x → V⁰ {ℓ}) → V⁰ {ℓ}
-- Π⁰ x y = sup⁰ (((a : El⁰ x) → El⁰ (y a)) , graph⁰ {x = x} {y = y})

-- El⁰Π⁰IsΠ : {x : V⁰ {ℓ}} {y : El⁰ x → V⁰ {ℓ}} → El⁰ (Π⁰ x y) ≡ ((a : El⁰ x) → El⁰ (y a))
-- El⁰Π⁰IsΠ = refl

-- -- Corollary 23
-- _→⁰_ : V⁰ {ℓ} → V⁰ {ℓ} → V⁰ {ℓ}
-- x →⁰ y = Π⁰ x (λ _ → y)

-- El⁰→⁰Is→ : {x y : V⁰ {ℓ}} → El⁰ (x →⁰ y) ≡ (El⁰ x → El⁰ y)
-- El⁰→⁰Is→ = refl
