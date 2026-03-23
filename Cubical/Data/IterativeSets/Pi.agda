{-# OPTIONS --lossy-unification #-}

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

open import Cubical.Data.IterativeMultisets.Base renaming (overline to overline-V∞ ; tilde to tilde-V∞)
open import Cubical.Data.IterativeSets.Base
open import Cubical.Data.IterativeSets.OrderedPair


private
  variable
    ℓ : Level
    x : V⁰ {ℓ}
    y : El⁰ x → V⁰ {ℓ}

private
    module _ {ℓ ℓ' : Level} {A : Type ℓ} {B : Type ℓ'} (f : A → B) where
        Inj : Type (ℓ-max ℓ ℓ')
        Inj = {x y : A} → f x ≡ f y → x ≡ y

private
  module _ {ℓA ℓA' ℓB : Level} {A : Type ℓA} {A' : Type ℓA'} {B : A' → Type ℓB} (f : A → A') (g : (x : A) → B (f x)) where
    Σfun : A → Σ A' B
    Σfun x .fst = f x
    Σfun x .snd = g x

    InjFstInj : Inj f → Inj Σfun
    InjFstInj injf p = injf (cong fst p)

private
  module _ {ℓA ℓA' ℓB : Level} {A : Type ℓA} {A' : Type ℓA'} {B : A' → Type ℓB} where


private
  module _ {ℓA ℓA' ℓB ℓB' : Level} {A : Type ℓA} {A' : Type ℓA'} {B : A → Type ℓB} {B' : A' → Type ℓB'} (setA' : isSet A') (f : A → A') (g : (x : A) → B x → B' (f x)) where
      Σfun' : Σ A B → Σ A' B'
      Σfun' pair .fst = f (pair .fst)
      Σfun' pair .snd = uncurry g pair

      InjΣInj : Inj f → ((x : A) → Inj (g x)) → Inj Σfun'
      InjΣInj injf injg {a , b} {c , d} p = ΣPathTransport→PathΣ (a , b) (c , d) (q1 , q2)
        where
          s : Σ[ p1 ∈ f a ≡ f c ] subst B' p1 (g a b) ≡ g c d
          s = PathΣ→ΣPathTransport _ _ p

          q1 : a ≡ c
          q1 = injf (s .fst)

          p1' : f a ≡ f c
          p1' = cong f q1

          s1≡p1' : (s .fst) ≡ (cong f q1)
          s1≡p1' = setA' (f a) (f c) (s .fst) (cong f q1)

          p1'≡s1 : (cong f q1) ≡ s .fst
          p1'≡s1 = setA' (f a) (f c) (cong f q1) (s .fst)

          h : subst (λ z → B' (f z)) q1 (g a b) ≡ g c (subst B q1 b)
          h = substCommSlice (λ z → B z) (λ z → B' (f z)) g (injf (s .fst)) b

          ii : subst (λ z → B' (f z)) q1 (g a b) ≡ subst B' (s .fst) (g a b)
          ii = cong (λ m → subst B' m (g a b)) p1'≡s1

          p2 : g c (subst B q1 b) ≡ g c d
          p2 = sym h ∙ ii ∙ s .snd

          q2 : subst B q1 b ≡ d
          q2 = injg c p2

graph⁰ : ((a : El⁰ {ℓ} x) → El⁰ {ℓ} (y a)) → V⁰ {ℓ}
graph⁰ {ℓ = ℓ} {x = x} {y = y} f = fromEmb E
  where
    E : Embedding (V⁰ {ℓ}) ℓ
    E .fst = El⁰ x
    E .snd .fst a = orderedPair⁰ (tilde x a , tilde (y a) (f a))
    E .snd .snd = injEmbedding isSetV⁰ (λ {v} {w} p → isEmbedding→Inj {f = tilde x} (isEmbedding-tilde x) v w (orderedPair⁰≡orderedPair⁰ .fst p .fst))

Π⁰ : (x : V⁰ {ℓ}) → ((a : El⁰ x) → V⁰ {ℓ}) → V⁰ {ℓ}
Π⁰ {ℓ} x y = fromEmb E
  where
    In : {f g : (a : El⁰ {ℓ} x) → El⁰ {ℓ} (y a)} → graph⁰ {x = x} {y = y} f ≡ graph⁰ {x = x} {y = y} g → (a : El⁰ x) → f a ≡ g a
    In {f} {g} p a = 
      let
        qqq : ((z : V⁰) → z ∈⁰ graph⁰ f → z ∈⁰ graph⁰ g)
        qqq = ≡V⁰-≃-≃V⁰ .fst p .fst
        -- ppp : Σ (overline (graph⁰ g))
        --        (λ x₁ →
        --           tilde (graph⁰ g) x₁ ≡ orderedPair⁰ (tilde x a , tilde (y a) (f a)))
        ppp : Σ[ a' ∈ El⁰ x ] orderedPair⁰ ((tilde x a') , (tilde (y a') (g a'))) ≡ orderedPair⁰ ((tilde x a) , (tilde (y a) (f a)))
        ppp = qqq (orderedPair⁰ ((tilde x a) , (tilde (y a) (f a)))) (a , refl)

        a' : El⁰ x
        a' = ppp .fst

        ttt : orderedPair⁰ ((tilde x a') , (tilde (y a') (g a'))) ≡ orderedPair⁰ ((tilde x a) , (tilde (y a) (f a)))
        ttt = ppp .snd

        qqq : tilde x a' ≡ tilde x a
        qqq = orderedPair⁰≡orderedPair⁰ .fst ttt .fst

        pp : a' ≡ a
        pp = isEmbedding→Inj {f = tilde x} (isEmbedding-tilde x) a' a qqq

        sss : tilde (y a') (g a') ≡ tilde (y a) (f a)
        sss = orderedPair⁰≡orderedPair⁰ .fst ttt .snd
        
        pppp : tilde (y a) (g a) ≡ tilde (y a') (g a')
        pppp i = tilde (y (pp (~ i))) (g (pp (~ i)))

        s : f a ≡ g a
        s = isEmbedding→Inj {f = tilde (y a)} (isEmbedding-tilde (y a)) (f a) (g a) (sym (pppp ∙ sss))
      in s
       
    
    In' : {f g : (a : El⁰ {ℓ} x) → El⁰ {ℓ} (y a)} → graph⁰ {x = x} {y = y} f ≡ graph⁰ {x = x} {y = y} g → f ≡ g
    In' p = funExt (In p)

    E : Embedding (V⁰ {ℓ}) ℓ
    E .fst = (a : El⁰ x) → El⁰ (y a)
    E .snd .fst f = graph⁰ {x = x} {y = y} f
    E .snd .snd = injEmbedding isSetV⁰ In'
