module Cubical.Data.IterativeSets.UnorderedPair where

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function
open import Cubical.Functions.Embedding
open import Cubical.Data.Sum
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
    {-# INLINE ¬_ #-}

-- TODO: (possibly) rename and move
-- TODO: maybe remove inlining
private
    module _ where
        path-filler : {ℓ : Level} {A : Type ℓ} {x y : A} (p : x ≡ y) (i : I) → x ≡ p i
        path-filler p i j = p (i ∧ j)
        {-# INLINE path-filler #-}

        path-reverse-filler : {ℓ : Level} {A : Type ℓ} {x y : A} (p : x ≡ y) (i : I) → p i ≡ y
        path-reverse-filler p i j = p (i ∨ j)
        {-# INLINE path-reverse-filler #-}

        path-move-i→i0 : {ℓ : Level} {A : Type ℓ} {x y a b : A} (p : x ≡ a) (q : y ≡ b) (i : I) → p i ≡ q i → x ≡ y
        path-move-i→i0 p q i eq = path-filler p i ∙∙ eq ∙∙ sym (path-filler q i)

        path-move-i0→i : {ℓ : Level} {A : Type ℓ} {x y a b : A} (p : x ≡ a) (q : y ≡ b) (i : I) → x ≡ y → p i ≡ q i
        path-move-i0→i p q i eq = sym (path-filler p i) ∙∙ eq ∙∙ path-filler q i

        path-move-i→i1 : {ℓ : Level} {A : Type ℓ} {x y a b : A} (p : x ≡ a) (q : y ≡ b) (i : I) → p i ≡ q i → a ≡ b
        path-move-i→i1 p q i eq = sym (path-reverse-filler p i) ∙∙ eq ∙∙ path-reverse-filler q i

        path-move-i1→i : {ℓ : Level} {A : Type ℓ} {x y a b : A} (p : x ≡ a) (q : y ≡ b) (i : I) → a ≡ b → p i ≡ q i
        path-move-i1→i p q i eq = path-reverse-filler p  i ∙∙ eq ∙∙ sym (path-reverse-filler q i)

        ≢-move-i→i0 : {ℓ : Level} {A : Type ℓ} {x y a b : A} (p : x ≡ a) (q : y ≡ b) (i : I) → ¬ (p i ≡ q i) → ¬ (x ≡ y)
        ≢-move-i→i0 p q i pi≢qi x≡y = pi≢qi (path-move-i0→i p q i x≡y)

        ≢-move-i0→i : {ℓ : Level} {A : Type ℓ} {x y a b : A} (p : x ≡ a) (q : y ≡ b) (i : I) → ¬ (x ≡ y) → ¬ (p i ≡ q i)
        ≢-move-i0→i p q i x≢y pi≡qi = x≢y (path-move-i→i0 p q i pi≡qi)

        ≢-move-i→i1 : {ℓ : Level} {A : Type ℓ} {x y a b : A} (p : x ≡ a) (q : y ≡ b) (i : I) → ¬ (p i ≡ q i) → ¬ (a ≡ b)
        ≢-move-i→i1 p q i pi≢qi a≡b = pi≢qi (path-move-i1→i p q i a≡b)

        ≢-move-i1→i : {ℓ : Level} {A : Type ℓ} {x y a b : A} (p : x ≡ a) (q : y ≡ b) (i : I) → ¬ (a ≡ b) → ¬ (p i ≡ q i)
        ≢-move-i1→i p q i a≢b pi≡qi = a≢b (path-move-i→i1 p q i pi≡qi)

        -- TODO: find out why this doesn't work, whenever I try to use it, Agda complains about Levels
        ≢-sym : {ℓ : Level} {A : Type} {x y : A} → ¬ (x ≡ y) → ¬ (y ≡ x)
        ≢-sym x≢y y≡x = x≢y (sym y≡x)

unorderedPair⁰ : (x y : V⁰ {ℓ}) → ¬ (x ≡ y) → V⁰ {ℓ}
unorderedPair⁰ {ℓ} x y x≢y = sup⁰ emb
    where
        emb : Σ[ A ∈ Type ℓ ] A ↪ V⁰
        emb .fst = Bool* {ℓ}
        emb .snd .fst (lift false) = x
        emb .snd .fst (lift true) = y
        emb .snd .snd = injEmbedding thm12 inj
            where
                inj : {a b : _} → emb .snd .fst a ≡ emb .snd .fst b → a ≡ b
                inj {lift false} {lift true} x≡y = ⊥-elim (x≢y x≡y)
                inj {lift true} {lift false} y≡x = ⊥-elim (x≢y (sym y≡x))
                inj {lift false} {lift false} _ = refl
                inj {lift true} {lift true} _ = refl

-- {x , y} ≡ {y , x}
unorderedUnorderedPair⁰ : {x y : V⁰ {ℓ}} {x≢y : ¬ (x ≡ y)} {y≢x : ¬ (y ≡ x)} → unorderedPair⁰ x y x≢y ≡ unorderedPair⁰ y x y≢x
unorderedUnorderedPair⁰ {x = x} {y = y} = invEq thm4' fibEq
    where
        fibEq : (z : V⁰) → (z ∈⁰ unorderedPair⁰ x y _) ≃ (z ∈⁰ unorderedPair⁰ y x _)
        fibEq z = propBiimpl→Equiv (isProp∈⁰ {x = unorderedPair⁰ x y _} {z = z}) (isProp∈⁰ {x = unorderedPair⁰ y x _} {z = z}) f g
            where
                f : z ∈⁰ unorderedPair⁰ x y _ → z ∈⁰ unorderedPair⁰ y x _
                f (lift false , prf) .fst = lift true
                f (lift false , prf) .snd = prf
                f (lift true , prf) .fst = lift false
                f (lift true , prf) .snd = prf
                g : z ∈⁰ unorderedPair⁰ y x _ → z ∈⁰ unorderedPair⁰ x y _
                g (lift false , prf) .fst = lift true
                g (lift false , prf) .snd = prf
                g (lift true , prf) .fst = lift false
                g (lift true , prf) .snd = prf

-- {x , y} ≡ {y , x} where for the sake of convenience the proof q : ¬ (y ≡ x) is simply the reversed version of p (which is irrelevant since V⁰ is a set)
unorderedUnorderedPair⁰' : {x y : V⁰ {ℓ}} {x≢y : ¬ (x ≡ y)} → unorderedPair⁰ x y x≢y ≡ unorderedPair⁰ y x λ y≡x → x≢y (sym y≡x)
unorderedUnorderedPair⁰' = unorderedUnorderedPair⁰

unorderedPair⁰-is-unordered-pair : {x y z : V⁰ {ℓ}} {x≢y : ¬ (x ≡ y)} → ((z ∈⁰ (unorderedPair⁰ x y x≢y)) ≃ ((x ≡ z) ⊎ (y ≡ z)))
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

unorderedPair⁰-is-unordered-pair-sym : {x y z : V⁰ {ℓ}} {x≢y : ¬ (x ≡ y)} → ((z ∈⁰ (unorderedPair⁰ x y x≢y)) ≃ ((z ≡ x) ⊎ (z ≡ y)))
unorderedPair⁰-is-unordered-pair-sym {x = x} {y = y} {z = z} = isoToEquiv (iso f g sec ret)
    where
        f : z ∈⁰ unorderedPair⁰ x y _ → (z ≡ x) ⊎ (z ≡ y)
        f (lift false , q) = inl (sym q)
        f (lift true , q) = inr (sym q)
        g : (z ≡ x) ⊎ (z ≡ y) → z ∈⁰ unorderedPair⁰ x y _
        g (inl _) .fst = lift false
        g (inl q) .snd = sym q
        g (inr _) .fst = lift true
        g (inr q) .snd = sym q
        sec : section f g
        sec (inl _) = refl
        sec (inr _) = refl
        ret : retract f g
        ret (lift false , _) = refl
        ret (lift true , _) = refl

unorderedPair⁰-≢-witness-agnostic : {x y : V⁰ {ℓ}} (x≢y₁ x≢y₂ : ¬ (x ≡ y)) → unorderedPair⁰ x y x≢y₁ ≡ unorderedPair⁰ x y x≢y₂
unorderedPair⁰-≢-witness-agnostic {x = x} {y = y} x≢y₁ x≢y₂ = cong (unorderedPair⁰ x y) x≢y₁≡x≢y₂
    where
        x≢y₁≡x≢y₂ : x≢y₁ ≡ x≢y₂
        x≢y₁≡x≢y₂ = isProp→ (λ ()) x≢y₁ x≢y₂

unorderedPair⁰≡unorderedPair⁰ : {x y a b : V⁰ {ℓ}} {x≢y : ¬ (x ≡ y)} {a≢b : ¬ (a ≡ b)} → ((unorderedPair⁰ x y x≢y ≡ unorderedPair⁰ a b a≢b) ≃ (((x ≡ a) × (y ≡ b)) ⊎ ((x ≡ b) × (y ≡ a))))
unorderedPair⁰≡unorderedPair⁰ {x = x} {y = y} {a = a} {b = b} {x≢y = x≢y} {a≢b = a≢b} = propBiimpl→Equiv (thm12 _ _) isPropRHS f g
    where
       isPropRHS : isProp (((x ≡ a) × (y ≡ b)) ⊎ ((x ≡ b) × (y ≡ a)))
       isPropRHS = isProp⊎ (isProp× (thm12 _ _) (thm12 _ _)) (isProp× (thm12 _ _) (thm12 _ _)) (λ (x≡a , _) (_ , y≡a) → x≢y (x≡a ∙ (sym y≡a)))

       thm4'-unorderedPair⁰ : (unorderedPair⁰ x y _ ≡ unorderedPair⁰ a b _) ≃ ((z : V⁰) → ((z ≡ x) ⊎ (z ≡ y)) ≃ ((z ≡ a) ⊎ (z ≡ b)))
       thm4'-unorderedPair⁰ = compEquiv thm4' (equivΠCod (λ z → equivComp unorderedPair⁰-is-unordered-pair-sym unorderedPair⁰-is-unordered-pair-sym))

       destruct : (unorderedPair⁰ x y _ ≡ unorderedPair⁰ a b _) → ((x ≡ a) ⊎ (x ≡ b)) × ((y ≡ a) ⊎ (y ≡ b))
       destruct p .fst = thm4'-unorderedPair⁰ .fst p x .fst (inl refl)
       destruct p .snd = thm4'-unorderedPair⁰ .fst p y .fst (inr refl)

       filter : ((x ≡ a) ⊎ (x ≡ b)) × ((y ≡ a) ⊎ (y ≡ b)) → ((x ≡ a) × (y ≡ b)) ⊎ ((x ≡ b) × (y ≡ a))
       filter (inl x≡a , inl y≡a) = ⊥-elim (x≢y (x≡a ∙ (sym y≡a)))
       filter (inl x≡a , inr y≡b) = inl (x≡a , y≡b)
       filter (inr x≡b , inl y≡a) = inr (x≡b , y≡a)
       filter (inr x≡b , inr y≡b) = ⊥-elim (x≢y (x≡b ∙ (sym y≡b)))

       f : unorderedPair⁰ x y _ ≡ unorderedPair⁰ a b _ → ((x ≡ a) × (y ≡ b)) ⊎ ((x ≡ b) × (y ≡ a))
       f = filter ∘ destruct

       g : ((x ≡ a) × (y ≡ b)) ⊎ ((x ≡ b) × (y ≡ a)) → unorderedPair⁰ x y _ ≡ unorderedPair⁰ a b _
       g (inl (x≡a , y≡b)) = unorderedPair⁰-≢-witness-agnostic x≢y _ ∙∙ (λ i → unorderedPair⁰ (x≡a i) (y≡b i) (≢-move-i0→i x≡a y≡b i x≢y)) ∙∙ unorderedPair⁰-≢-witness-agnostic _ a≢b
       g (inr (x≡b , y≡a)) = (unorderedPair⁰-≢-witness-agnostic x≢y _ ∙∙ (λ i → unorderedPair⁰ (x≡b i) (y≡a i) (≢-move-i0→i x≡b y≡a i x≢y)) ∙∙ unorderedPair⁰-≢-witness-agnostic _ (λ b≡a → a≢b (sym b≡a)) :> unorderedPair⁰ x y _ ≡ unorderedPair⁰ b a _) ∙ unorderedUnorderedPair⁰
