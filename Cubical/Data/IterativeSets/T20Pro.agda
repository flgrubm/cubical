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
open import Cubical.Data.Nat.Order

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

-- this might be something for the library?

_∈W_ : {ℓ ℓ' : Level} {A : Type ℓ} {B : A → Type ℓ'} (x y : W A B) → Type (ℓ-max ℓ ℓ')
x ∈W y = fiber (tilde-W y) x

∈W-irrefl : {ℓ ℓ' : Level} {A : Type ℓ} {B : A → Type ℓ'} (x : W A B) → (x ∈W x) → ⊥
∈W-irrefl {A = A} {B = B} = WInd A B _ step
    where
        step : {s : A} {f : B s → W A B} → ((p : B s) → f p ∈W f p → ⊥) → sup-∞ s f ∈W sup-∞ s f → ⊥
        step {s = s} {f = f} ih (b , p) = ih b (transport (cong (λ r → r ∈W r) (sym p)) (b , p))


∈∞-irrefl : {ℓ : Level} (x : V∞ {ℓ}) → (x ∈∞ x) → ⊥
∈∞-irrefl = ∈W-irrefl

_∈⁰_ : V⁰ {ℓ} → V⁰ {ℓ} → Type (ℓ-suc ℓ)
x ∈⁰ y = fiber (tilde-0' y) (x)

∈⁰-irrefl : {ℓ : Level} (x : V⁰ {ℓ}) → (x ∈⁰ x) → ⊥
∈⁰-irrefl (sup-∞ A f , isitset) (a , p) = ∈∞-irrefl (sup-∞ A f) (a , cong fst p)


SumInl≢Inr : {ℓ ℓ' ℓ'' : Level} {A : Type ℓ} {B : Type ℓ'} (a : A) (b : B) → inl a ≡ (inr b :> A ⊎ B) → ⊥
SumInl≢Inr {ℓ'' = ℓ''} {A = A} {B = B} a b p = transport (cong helper p) _
    where
        helper : A ⊎ B → Type ℓ-zero
        helper (inl x) = Unit
        helper (inr y) = ⊥


suc⁰ : {ℓ : Level} → V⁰ {ℓ} → V⁰ {ℓ}
suc⁰ {ℓ} (sup-∞ A f , isitsetAf) = sup⁰ (A ⊎ Unit* {ℓ} , ϕₓ , hasPropFibers→isEmbedding hpf)
    where
        ϕₓ : (overline-0 (sup-∞ A f , isitsetAf) ⊎ Unit* {ℓ}) → V⁰ {ℓ}
        ϕₓ (inl a) = f a , isitsetAf .snd a
        ϕₓ (inr _) = (sup-∞ A f , isitsetAf)

        eqFib : (z : V⁰ {ℓ}) → (fiber ϕₓ z ≃ ((z ∈⁰ (sup-∞ A f , isitsetAf)) ⊎ ((sup-∞ A f , isitsetAf) ≡ z)))
        eqFib (sup-∞ B g , isitsetBg) = isoToEquiv (iso to fro sec ret)
            where
                to : fiber ϕₓ (sup-∞ B g , isitsetBg) → ((sup-∞ B g , isitsetBg) ∈⁰ (sup-∞ A f , isitsetAf)) ⊎ ((sup-∞ A f , isitsetAf) ≡ (sup-∞ B g , isitsetBg))
                to (inl a , p) = inl (a , p)
                to (inr _ , p) = inr p
                fro : ((sup-∞ B g , isitsetBg) ∈⁰ (sup-∞ A f , isitsetAf)) ⊎ ((sup-∞ A f , isitsetAf) ≡ (sup-∞ B g , isitsetBg)) → fiber ϕₓ (sup-∞ B g , isitsetBg)
                fro (inl (a , p)) = inl a , p
                fro (inr p) = inr _ , p
                sec : section to fro
                sec (inl _) = refl
                sec (inr _) = refl
                ret : retract to fro
                ret (inl _ , _) = refl
                ret (inr _ , _) = refl

        hpf : hasPropFibers ϕₓ
        hpf (sup-∞ B g , isitsetBg) = EquivToIsProp→isProp (isPropIsPropDisjointSum (isEmbedding→hasPropFibers (isEmbedding-tilde-0 (sup-∞ A f , isitsetAf)) (sup-∞ B g , isitsetBg)) (thm12 _ _) ∈⁰×≡→⊥) (invEquiv (eqFib (sup-∞ B g , isitsetBg)))
            where
                ∈⁰×≡→⊥ : ((sup-∞ B g , isitsetBg) ∈⁰ (sup-∞ A f , isitsetAf)) × ((sup-∞ A f , isitsetAf) ≡ (sup-∞ B g , isitsetBg)) → ⊥
                ∈⁰×≡→⊥ ((a , pa) , p) = ∈⁰-irrefl (sup-∞ B g , isitsetBg) (transport (cong (λ r → ((sup-∞ B g , isitsetBg) ∈⁰ r)) p) (a , pa))

ℕ* : Type ℓ
ℕ* = Lift ℕ

vonNeumannEncoding : ℕ* {ℓ} → V⁰ {ℓ}
vonNeumannEncoding (lift zero) = empty⁰
vonNeumannEncoding (lift (suc x)) = suc⁰ (vonNeumannEncoding (lift x))

_ : overline-0 {ℓ} (vonNeumannEncoding (lift zero)) ≡ ⊥*
_ = refl

_ : overline-0 {ℓ} (vonNeumannEncoding (lift (suc zero))) ≡ ⊥* ⊎ Unit*
_ = refl

_ : overline-0 {ℓ} (vonNeumannEncoding (lift (suc (suc zero)))) ≡ (⊥* ⊎ Unit*) ⊎ Unit*
_ = refl

overline-0-suc⁰≡overline-0⊎Unit* : {x : V⁰ {ℓ}} → overline-0 {ℓ} (suc⁰ x) ≡ (overline-0 x ⊎ Unit* {ℓ})
-- overline-0-suc⁰≡overline-0⊎Unit* = refl -- doesn't work
overline-0-suc⁰≡overline-0⊎Unit* {x = (sup-∞ _ _ , _)} = refl

overline-0-vNE-suc≡overline-0-vNE⊎Unit* : (n : ℕ) → overline-0 {ℓ} (vonNeumannEncoding (lift (suc n))) ≡ (overline-0 {ℓ} (vonNeumannEncoding (lift n))) ⊎ Unit* {ℓ}
-- overline-0-vNE-suc≡overline-0-vNE⊎Unit* _ = refl -- doesn't work
overline-0-vNE-suc≡overline-0-vNE⊎Unit* n = overline-0-suc⁰≡overline-0⊎Unit* {x = vonNeumannEncoding (lift n)}

vonNeumannOverline≃Fin : (n : ℕ) → (overline-0 (vonNeumannEncoding {ℓ} (lift n)) ≃ Fin.Fin n)
vonNeumannOverline≃Fin {ℓ} zero = isoToEquiv (iso f g sec ret)
    where
        f : overline-0 (vonNeumannEncoding (lift zero)) → Fin.Fin zero
        f ()
        g : Fin.Fin zero → overline-0 (vonNeumannEncoding (lift zero))
        g = ⊥-elim {A = λ _ → overline-0 (vonNeumannEncoding (lift zero))} ∘ ¬Fin0
        sec : section f g
        sec a = ⊥-elim {A = λ _ → f (g a) ≡ a} (¬Fin0 a)
        ret : retract f g
        ret ()
vonNeumannOverline≃Fin {ℓ} (suc n) = isoToEquiv (iso f g sec ret)
    where
        postulate f : overline-0 (vonNeumannEncoding (lift (suc n))) → Fin.Fin (suc n)
        -- f n = {!!}
        postulate g : Fin.Fin (suc n) → overline-0 (vonNeumannEncoding (lift (suc n)))
        -- g (zero , _) = {!inr tt*!}
        -- g (suc m , sucm<sucn) = {!inl (g (m , pred-≤-pred sucm<sucn))!} -- actually this should be something like `invEq (vonNeumannOverline≃Fin n)` and mapping m into Fin n
        postulate sec : section f g
        postulate ret : retract f g
        
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
