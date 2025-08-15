module Cubical.Data.IterativeSets.UnorderedPair where

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Functions.Embedding
open import Cubical.Data.SumFin
open import Cubical.Data.Bool
open import Cubical.Data.Sigma
open import Cubical.Data.Empty renaming (elim to ⊥-elim)

open import Cubical.Data.IterativeSets.Base

private
  variable
    ℓ : Level

private
  module _ where
    ¬_ : Type ℓ → Type ℓ
    ¬ A = A → ⊥

unorderedPair⁰ : (x y : V⁰ {ℓ}) → ¬ (x ≡ y) → V⁰ {ℓ}
unorderedPair⁰ {ℓ} x y x≢y = sup⁰ emb
    where
        emb : Σ[ A ∈ Type ℓ ] A ↪ V⁰
        emb .fst = Bool* {ℓ}
        emb .snd .fst (lift false) = x
        emb .snd .fst (lift true) = y
        emb .snd .snd = injEmbedding thm12 inj
            where
                inj : {w x : _} → emb .snd .fst w ≡ emb .snd .fst x → w ≡ x
                inj {lift false} {lift true} p = ⊥-elim (x≢y p)
                inj {lift true} {lift false} p = ⊥-elim (x≢y (sym p))
                inj {lift false} {lift false} _ = refl
                inj {lift true} {lift true} _ = refl

-- {x , y} ≡ {y , x}
unorderedUnorderedPair⁰ : {x y : V⁰ {ℓ}} {p : ¬ (x ≡ y)} {q : ¬ (y ≡ x)} → unorderedPair⁰ x y p ≡ unorderedPair⁰ y x q
unorderedUnorderedPair⁰ {ℓ} {x} {y} {p} {q} = invEq thm4' fibEq
    where
        fibEq : (z : V⁰ {ℓ}) → (z ∈⁰ unorderedPair⁰ x y p) ≃ (z ∈⁰ unorderedPair⁰ y x q)
        fibEq z = propBiimpl→Equiv (isProp∈⁰ {x = unorderedPair⁰ x y p} {z = z}) (isProp∈⁰ {x = unorderedPair⁰ y x q} {z = z}) f g
            where
                f : z ∈⁰ unorderedPair⁰ x y p → z ∈⁰ unorderedPair⁰ y x q
                f (lift false , prf) .fst = lift true
                f (lift false , prf) .snd = prf
                f (lift true , prf) .fst = lift false
                f (lift true , prf) .snd = prf
                g : z ∈⁰ unorderedPair⁰ y x q → z ∈⁰ unorderedPair⁰ x y p
                g (lift false , prf) .fst = lift true
                g (lift false , prf) .snd = prf
                g (lift true , prf) .fst = lift false
                g (lift true , prf) .snd = prf

-- {x , y} ≡ {y , x} where for the sake of convenience the proof q : ¬ (y ≡ x) is simply the reversed version of p (which is irrelevant since V⁰ is a set)
unorderedUnorderedPair⁰' : {x y : V⁰ {ℓ}} {p : ¬ (x ≡ y)} → unorderedPair⁰ x y p ≡ unorderedPair⁰ y x λ p' → p (sym p')
unorderedUnorderedPair⁰' {ℓ} {x} {y} {p} = unorderedUnorderedPair⁰

unorderedPair⁰-is-unordered-pair : {x y z : V⁰ {ℓ}} {p : ¬ (x ≡ y)} → ((z ∈⁰ (unorderedPair⁰ x y p)) ≃ ((x ≡ z) ⊎ (y ≡ z)))
unorderedPair⁰-is-unordered-pair {x = x} {y = y} {z = z} = isoToEquiv (iso f g sec ret)
    where
        f : z ∈⁰ unorderedPair⁰ x y _ → (x ≡ z) ⊎ (y ≡ z)
        f (lift false , q) = inl q
        f (lift true , q) = inr q
        g : (x ≡ z) ⊎ (y ≡ z) → z ∈⁰ unorderedPair⁰ x y _
        g (inl _) .fst = lift false
        g (inl q) .snd = q
        g (inr _) .fst = lift true
        g (inr q) .snd = q
        sec : section f g
        sec (inl _) = refl
        sec (inr _) = refl
        ret : retract f g
        ret (lift false , _) = refl
        ret (lift true , _) = refl

test : {ℓ : Level} {A : Type ℓ} {x y : A} (p : x ≡ y) (i : I) → x ≡ p i
test p i = λ j → p (i ∧ j)

test' : {ℓ : Level} {A : Type ℓ} {x y a b : A} (p : x ≡ a) (q : y ≡ b) (i : I) → p i ≡ q i → x ≡ y
test' p q i eq = test p i ∙ eq ∙ sym (test q i)

test'' : {ℓ : Level} {A : Type ℓ} {x y a b : A} (p : x ≡ a) (q : y ≡ b) (x≢y : ¬ (x ≡ y)) (i : I) → ¬ (p i ≡ q i)
test'' p q x≢y i pi≡qi = x≢y (test' p q i pi≡qi)

test''' : {x y : V⁰ {ℓ}} (p q : ¬ (x ≡ y)) → unorderedPair⁰ x y p ≡ unorderedPair⁰ x y q
test''' {x = x} {y = y} p q = cong (unorderedPair⁰ x y) p≡q
    where
        p≡q : p ≡ q
        p≡q = isProp→ (λ ()) p q

unorderedPair⁰≡unorderedPair⁰ : {x y a b : V⁰ {ℓ}} {p : ¬ (x ≡ y)} {q : ¬ (a ≡ b)} → ((unorderedPair⁰ x y p ≡ unorderedPair⁰ a b q) ≃ (((x ≡ a) × (y ≡ b)) ⊎ ((x ≡ b) × (y ≡ a))))
unorderedPair⁰≡unorderedPair⁰ {ℓ = ℓ} {x = x} {y = y} {a = a} {b = b} {p = p} {q = q} = isoToEquiv (iso f g sec ret)
    where
        postulate f : unorderedPair⁰ x y p ≡ unorderedPair⁰ a b q → ((x ≡ a) × (y ≡ b)) ⊎ ((x ≡ b) × (y ≡ a))
        g : ((x ≡ a) × (y ≡ b)) ⊎ ((x ≡ b) × (y ≡ a)) → unorderedPair⁰ x y p ≡ unorderedPair⁰ a b q
        g (inl (x≡a , y≡b)) = xy≡ab
            where
                h : unorderedPair⁰ x y (test'' x≡a y≡b p i0) ≡ unorderedPair⁰ a b (test'' x≡a y≡b p i1)
                h i = unorderedPair⁰ (x≡a i) (y≡b i) (test'' x≡a y≡b p i)
                xy≡ab : unorderedPair⁰ x y p ≡ unorderedPair⁰ a b q
                xy≡ab = test''' p (test'' x≡a y≡b p i0) ◁ h ▷ test''' (test'' x≡a y≡b p i1) q
        g (inr (x≡b , y≡a)) = xy≡ba ∙ unorderedUnorderedPair⁰
            where
                h : unorderedPair⁰ x y (test'' x≡b y≡a p i0) ≡ unorderedPair⁰ b a (test'' x≡b y≡a p i1)
                h i = unorderedPair⁰ (x≡b i) (y≡a i) (test'' x≡b y≡a p i)
                xy≡ba : unorderedPair⁰ x y p ≡ unorderedPair⁰ b a (λ eq → q (sym eq))
                xy≡ba = test''' p (test'' x≡b y≡a p i0) ◁ h ▷ test''' (test'' x≡b y≡a p i1) (λ eq → q (sym eq))
        postulate sec : section f g
        postulate ret : retract f g
