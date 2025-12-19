{-# OPTIONS --lossy-unification #-}

module Cubical.Data.IterativeSets.PiTest where

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

          


Ψ : {ℓ : Level} {x : V⁰ {ℓ}} {y : El⁰ x → V⁰ {ℓ}} → ((a : El⁰ x) → El⁰ (y a)) → El⁰ x ↪ V⁰ {ℓ}
Ψ {ℓ} {x} {y} ϕ = compEmbedding (orderedPair⁰ , isEmbOrderedPair⁰) emb
  where
    emb : El⁰ x ↪ (V⁰ × V⁰)
    emb .fst a .fst = tilde x a
    emb .fst a .snd = tilde (y a) (ϕ a)
    emb .snd = injEmbedding (isSet× isSetV⁰ isSetV⁰) (λ p → isEmbedding→Inj (isEmbedding-tilde x) _ _ (cong fst p))

graph⁰ : {ℓ : Level} {x : V⁰ {ℓ}} {y : El⁰ x → V⁰ {ℓ}} → ((a : El⁰ x) → El⁰ (y a)) ↪ V⁰ {ℓ}
graph⁰ {ℓ} {x} {y} = compEmbedding (Iso→Embedding (invIso Iso-V⁰-Emb)) ee
  where
    ee : ((a : El⁰ x) → El⁰ (y a)) ↪ Embedding V⁰ ℓ
    ee .fst ϕ .fst = El⁰ x
    ee .fst ϕ .snd = Ψ ϕ
    ee .snd = injEmbedding isSetEmbedding help
      where
        help : {ϕ θ : (a : El⁰ x) → El⁰ (y a)} → ee .fst ϕ ≡ ee .fst θ → ϕ ≡ θ
        help {ϕ} {θ} p = {!!}
          where
            q : (El⁰ x , Ψ ϕ .fst) ≡ (El⁰ x , Ψ θ .fst)
            q = cong EmbeddingIdentityPrinciple.toFibr p

            qq : Σ[ p ∈ El⁰ x ≡ El⁰ x ] subst (λ m → m → V⁰) p (Ψ ϕ .fst) ≡ Ψ θ .fst
            qq = PathΣ→ΣPathTransport (El⁰ x , Ψ ϕ .fst) (El⁰ x , Ψ θ .fst) q

            qq1 : El⁰ x ≡ El⁰ x
            qq1 = qq .fst

            qq2 : subst (λ m → m → V⁰) (qq .fst) (Ψ ϕ .fst) ≡ Ψ θ .fst
            qq2 = qq .snd

            qqq : Σ[ p ∈ El⁰ x ≡ El⁰ x ] PathP (λ i → p i → V⁰) (Ψ ϕ .fst) (Ψ θ .fst)
            qqq = PathPΣ q

            qqq1 : El⁰ x ≡ El⁰ x
            qqq1 = qqq .fst

            qqq2 : PathP (λ i → qqq1 i → V⁰) (Ψ ϕ .fst) (Ψ θ .fst)
            qqq2 = qqq .snd

            qqqq : (a : (i : I) → qqq1 i) → Ψ ϕ .fst (a i0) ≡ Ψ θ .fst (a i1)
            qqqq a i = qqq2 i (a i)

            ggg : (a : El⁰ x) → PathP (λ i → qqq1 i) a (transport qqq1 a)
            ggg a = transport-filler qqq1 a

            qqqqq : (a : El⁰ x) → Ψ ϕ .fst a ≡ Ψ θ .fst (transport qqq1 a)
            qqqqq a = qqqq (λ i → transport-filler qqq1 a i)

            hhh : (a : El⁰ x) → transport refl (Ψ ϕ .fst a) ≡ Ψ θ .fst (transport qqq1 a)
            hhh a = fromPathP (qqqqq a)

graph⁰' : {ℓ : Level} {x : V⁰ {ℓ}} {y : El⁰ x → V⁰ {ℓ}} → ((a : El⁰ x) → El⁰ (y a)) ↪ V⁰ {ℓ}
graph⁰' {ℓ} {x} {y} = compEmbedding (Iso→Embedding (invIso Iso-V⁰-Emb)) ee
  where
    ee : ((a : El⁰ x) → El⁰ (y a)) ↪ Embedding V⁰ ℓ
    ee .fst ϕ .fst = El⁰ x
    ee .fst ϕ .snd = Ψ ϕ
    ee .snd = injEmbedding isSetEmbedding help
      where
        help : {ϕ θ : (a : El⁰ x) → El⁰ (y a)} → ee .fst ϕ ≡ ee .fst θ → ϕ ≡ θ
        help {ϕ} {θ} p = {!!}
        -- (J> isEmbedding→Inj {!Ψ ϕ .snd!} {!!}) (ee .fst θ)
-- graph⁰ : {ℓ : Level} {x : V⁰ {ℓ}} {y : El⁰ x → V⁰ {ℓ}} → ((a : El⁰ x) → El⁰ (y a)) ↪ V⁰ {ℓ}
-- graph⁰ {ℓ} {x} {y} .fst ϕ = fromEmb (El⁰ x , Ψ ϕ)
-- graph⁰ {ℓ} {x} {y} .snd = injEmbedding isSetV⁰ (λ {ϕ} {θ} p → funExt (λ a → 
--     let
--       h : fromEmb (El⁰ x , Ψ {ℓ} {x} {y} ϕ) .fst ≡ sup-∞ (El⁰ x) (λ a → orderedPair⁰ (tilde x a , tilde (y a) (ϕ a)) .fst)
--       h = refl

--       -- hh : fromEmb (El⁰ x , Ψ {ℓ} {x} {y} ϕ) ≡ (sup-∞ (El⁰ x) (λ a → orderedPair⁰ (tilde x a , tilde (y a) (ϕ a)) .fst) , _)
--       -- hh = Σ≡Prop isPropIsIterativeSet {!!}

--       j : fromEmb (El⁰ x , Ψ {ℓ} {x} {y} θ) .fst ≡ sup-∞ (El⁰ x) (λ a → orderedPair⁰ (tilde x a , tilde (y a) (θ a)) .fst)
--       j = refl

--       k : sup-∞ (El⁰ x) (λ a → orderedPair⁰ (tilde x a , tilde (y a) (ϕ a)) .fst) ≡ sup-∞ (El⁰ x) (λ a → orderedPair⁰ (tilde x a , tilde (y a) (θ a)) .fst)
--       k = cong fst p

--       kk : fromEmb (El⁰ x , Ψ {ℓ} {x} {y} ϕ) ≃V⁰ fromEmb (El⁰ x , Ψ {ℓ} {x} {y} θ)
--       kk = ≡V⁰-≃-≃V⁰ .fst p

--       kkk : fromEmb (El⁰ x , Ψ {ℓ} {x} {y} ϕ) ≃V⁰' fromEmb (El⁰ x , Ψ {ℓ} {x} {y} θ)
--       kkk = ≡V⁰-≃-≃V⁰' .fst p

--       goal : tilde (y a) (ϕ a) ≡ tilde (y a) (θ a)
--       goal = {!!}
--     in isEmbedding→Inj (isEmbedding-tilde (y a)) (ϕ a) (θ a) goal))

-- Π⁰ : (x : V⁰ {ℓ}) → (El⁰ x → V⁰ {ℓ}) → V⁰ {ℓ}
-- Π⁰ x y = sup⁰ (((a : El⁰ x) → El⁰ (y a)) , graph⁰ {x = x} {y = y})

-- El⁰Π⁰IsΠ : {x : V⁰ {ℓ}} {y : El⁰ x → V⁰ {ℓ}} → El⁰ (Π⁰ x y) ≡ ((a : El⁰ x) → El⁰ (y a))
-- El⁰Π⁰IsΠ = refl

-- -- Corollary 23
-- _→⁰_ : V⁰ {ℓ} → V⁰ {ℓ} → V⁰ {ℓ}
-- x →⁰ y = Π⁰ x (λ _ → y)

-- El⁰→⁰Is→ : {x y : V⁰ {ℓ}} → El⁰ (x →⁰ y) ≡ (El⁰ x → El⁰ y)
-- El⁰→⁰Is→ = refl
