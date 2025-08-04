module Cubical.Data.IterativeSets.T20Pro where
-- definitions in Base
-- properties in Properties

open import Cubical.Core.Everything

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Fiberwise
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Univalence
open import Cubical.Functions.Fibration
open import Cubical.Functions.Embedding
open import Cubical.Data.Empty renaming (elim to ⊥-elim ; elim* to ⊥*-elim)
open import Cubical.Data.Unit
open import Cubical.Data.Bool
open import Cubical.Functions.FunExtEquiv
open import Cubical.Foundations.HLevels
open import Cubical.Data.Nat
open import Cubical.Data.SumFin
open import Cubical.Data.Fin as Fin

open import Cubical.Data.Sigma

-- open import Cubical.

open import Cubical.Homotopy.Base

open import Cubical.Data.W.W

open import Cubical.Data.IterativeSets.Base

private
  variable
    ℓ ℓ' ℓ'' : Level
    A A' : Type ℓ
    B B' : A → Type ℓ

isPropIsPropDisjointSum : {A : Type ℓ} {B : Type ℓ} → isProp A → isProp B → (A × B → ⊥) → isProp (A ⊎ B)
isPropIsPropDisjointSum propA propB disj (inl a₁) (inl a₂) = cong inl (propA a₁ a₂)
isPropIsPropDisjointSum propA propB disj (inr b₁) (inr b₂) = cong inr (propB b₁ b₂)
isPropIsPropDisjointSum propA propB disj (inl a) (inr b) = ⊥-elim (disj (a , b))
isPropIsPropDisjointSum propA propB disj (inr b) (inl a) = ⊥-elim (disj (a , b))


EquivToIsProp→isProp : {A : Type ℓ} {B : Type ℓ} → isProp A → (A ≃ B) → isProp B
EquivToIsProp→isProp propA equiv = Embedding-into-isProp→isProp (Equiv→Embedding (invEquiv equiv)) propA

-- EquivToIsProp→isProp' : {A : Type ℓ} {B : Type ℓ} → isProp A → (A ≃ B) → isProp B
-- EquivToIsProp→isProp' propA (f , isequiv) w x =
--         w
--             ≡⟨ sym (secIsEq isequiv w) ⟩
--         f (invIsEq isequiv w)
--             ≡⟨ cong f (propA (invIsEq isequiv w) (invIsEq isequiv x)) ⟩
--         f (invIsEq isequiv x)
--             ≡⟨ secIsEq isequiv x ⟩
--         x
--             ∎

-- _∈∞_ : V∞ {ℓ} → V∞ {ℓ} → Type (ℓ-suc ℓ)
-- x ∈∞ y = fiber (tilde-∞ y) x
_∈⁰_ : V⁰ {ℓ} → V⁰ {ℓ} → Type (ℓ-suc ℓ)
x ∈⁰ y = fiber (tilde-0 y) (x .fst)

-- new tilde-0 that maps to V⁰ instead of V∞?

suc⁰ : {ℓ : Level} → V⁰ {ℓ} → V⁰ {ℓ}
suc⁰ {ℓ} (sup-∞ A f , isitsetAf) = sup⁰ ((overline-0 (sup-∞ A f , isitsetAf) ⊎ Unit* {ℓ}) , ϕₓ , isemb)
    where
        ϕₓ : (overline-0 (sup-∞ A f , isitsetAf) ⊎ Unit* {ℓ}) → V⁰ {ℓ}
        ϕₓ (inl a) = f a , isitsetAf .snd a
        ϕₓ (inr _) = (sup-∞ A f , isitsetAf)

        eqFib : (z : V⁰ {ℓ}) → (fiber ϕₓ z ≃ ((z ∈⁰ (sup-∞ A f , isitsetAf)) ⊎ ((sup-∞ A f , isitsetAf) ≡ z)))
        eqFib (sup-∞ B g , isitsetBg) = isoToEquiv (iso to from {!!} {!!})
            where
                to : fiber ϕₓ (sup-∞ B g , isitsetBg) → ((sup-∞ B g , isitsetBg) ∈⁰ (sup-∞ A f , isitsetAf)) ⊎ ((sup-∞ A f , isitsetAf) ≡ (sup-∞ B g , isitsetBg))
                to = {!!}
                -- to (inl a , snd) = inl (a , PathPΣ snd .fst)
                -- to (inr _ , p) = inr p
                from : ((sup-∞ B g , isitsetBg) ∈⁰ (sup-∞ A f , isitsetAf)) ⊎ ((sup-∞ A f , isitsetAf) ≡ (sup-∞ B g , isitsetBg)) → fiber ϕₓ (sup-∞ B g , isitsetBg)
                from (inl (a , p)) = inl a , {!p!}
                from (inr p) = inr _ , p

        postulate isemb : isEmbedding ϕₓ
        -- isemb = hasPropFibers→isEmbedding λ z → EquivToIsProp→isProp (isPropIsPropDisjointSum {!!} (thm12 _ _) {!!}) (invEquiv (eqFib z))

ℕ* : Type ℓ
ℕ* = Lift ℕ

vonNeumannEncoding : ℕ* {ℓ} → V⁰ {ℓ}
vonNeumannEncoding (lift zero) = empty⁰
vonNeumannEncoding (lift (suc x)) = suc⁰ (vonNeumannEncoding (lift x))

vonNeumannOverline≃Fin : (n : ℕ) → (overline-0 (vonNeumannEncoding {ℓ} (lift n)) ≃ Fin.Fin n)
vonNeumannOverline≃Fin {ℓ} zero = isoToEquiv (iso f g sec ret)
    where
        f : overline-0 (vonNeumannEncoding (lift zero)) → Fin.Fin zero
        f ()
        g : Fin.Fin zero → overline-0 (vonNeumannEncoding (lift zero))
        g = ⊥-elim {A = λ _ → overline-0 (vonNeumannEncoding (lift zero))} ∘ ¬Fin0

        postulate sec : section f g
        -- sec a = ⊥-elim {ℓ-zero} {A = λ _ → {!section f g!}} (¬Fin0 a)
        postulate ret : retract f g
vonNeumannOverline≃Fin (suc n) = placeholder
    where
        postulate placeholder : (overline-0 (vonNeumannEncoding {ℓ} (lift (suc n))) ≃ Fin.Fin (suc n))

ℕ⁰' : V⁰ {ℓ}
ℕ⁰' {ℓ} = sup⁰ (ℕ* {ℓ} , vonNeumannEncoding {ℓ} , isemb)
    where
        isinj : (w x : ℕ* {ℓ}) → vonNeumannEncoding w ≡ vonNeumannEncoding x → w ≡ x
        isinj (lift n) (lift m) p = liftExt (Fin-inj n m (ua (compEquiv (invEquiv (vonNeumannOverline≃Fin n)) (compEquiv (pathToEquiv (cong overline-0 p)) (vonNeumannOverline≃Fin m)))))
        isemb : isEmbedding (vonNeumannEncoding {ℓ})
        isemb = injEmbedding thm12 λ {w} {x} → isinj w x

ℕ⁰Isℕ*' : El⁰ (ℕ⁰' {ℓ}) ≡ ℕ* {ℓ}
ℕ⁰Isℕ*' = refl
