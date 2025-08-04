module Cubical.Data.IterativeSets.T03WithoutJ where
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
open import Cubical.Data.Empty renaming (elim to ⊥-elim)
open import Cubical.Data.Unit
open import Cubical.Data.Bool
open import Cubical.Functions.FunExtEquiv
open import Cubical.Foundations.HLevels
open import Cubical.Data.Nat
open import Cubical.Data.SumFin

open import Cubical.Data.Sigma

-- open import Cubical.

open import Cubical.Homotopy.Base

open import Cubical.Data.W.W

open import Cubical.Data.IterativeSets.Base

open import Cubical.Foundations.CartesianKanOps

private
  variable
    ℓ ℓ' ℓ'' : Level
    A A' : Type ℓ
    B B' : A → Type ℓ'
 
thm3-fun' : {ℓ : Level} → {x y : V∞ {ℓ}} → x ≡ y → Σ[ e ∈ overline-∞ x ≃ overline-∞ y ] tilde-∞ x ∼ (tilde-∞ y ∘ e .fst)
thm3-fun' {x = x} = J (λ z p → Σ[ e ∈ overline-∞ x ≃ overline-∞ z ] tilde-∞ x ∼ (tilde-∞ z ∘ e .fst)) (idEquiv (overline-∞ x) , λ a → refl)

-- thm3-fun'' : {ℓ : Level} → {x y : V∞ {ℓ}} → x ≡ y → Σ[ e ∈ overline-∞ x ≃ overline-∞ y ] tilde-∞ x ∼ (tilde-∞ y ∘ e .fst)
-- thm3-fun'' {ℓ} {sup-∞ A f} {sup-∞ B g} p .fst = pathToEquiv (cong overline-∞ p) -- λ i → overline-∞ (p i)
-- thm3-fun'' {ℓ} {sup-∞ A f} {sup-∞ B g} p .snd z =
--     f z
--         ≡⟨ cong f (sym (retEq (thm3-fun'' p .fst) z)) ⟩
--     f (invEq (thm3-fun'' p .fst) (thm3-fun'' p .fst .fst z))
--         ≡⟨ {!!} ⟩
--     g (thm3-fun'' p .fst .fst z)
--         ∎

-- helper : {ℓ : Level} → {x y : V∞ {ℓ}} → (e : overline-∞ x ≡ overline-∞ y) → (tilde-∞ x ∼ (tilde-∞ y ∘ transport e)) → x ≡ y
-- helper {ℓ} {x} {y} e h = J (λ z e' → {!((tilde-∞ x ∼ (tilde-∞ z ∘ transport e)) → x ≡ z)!}) (J {!!} {!!} {!!}) e

-- WPathP : {x y : W A B} → Σ[ p ∈ overline-W x ≡ overline-W y ] PathP (λ i → p i → B (p i)) (tilde-W x) (tilde-W y) → x ≡ y
-- WPathP = ?

-- PathPV∞ : {x y : V∞ {ℓ}} → (x ≡ y) → Σ[ p ∈ overline-∞ x ≡ overline-∞ y ] PathP (λ i → (p i → V∞ {ℓ})) (tilde-∞ x) (tilde-∞ y)
-- PathPV∞ p .fst i = overline-∞ (p i)
-- PathPV∞ p .snd i z = {!!}

-- thm3-inv' : {ℓ : Level} → {x y : V∞ {ℓ}} → Σ[ e ∈ overline-∞ x ≃ overline-∞ y ] ((z : overline-∞ x) → tilde-∞ x z ≡ tilde-∞ y (e .fst z)) → x ≡ y
-- thm3-inv' {ℓ} {x = sup-∞ A f} {y = sup-∞ B g} (e , p) i = sup-∞ (ua e i) (h i)
--     where
--         h : PathP (λ j → ua e j → V∞ {ℓ}) f g
--         h = {!!}

_≡V∞_ : {ℓ : Level} → (x y : V∞ {ℓ}) → Type (ℓ-suc ℓ)
(sup-W A f) ≡V∞ (sup-W B g) = Σ[ e ∈ A ≃ B ] ((z : A) → f z ≡ g (e .fst z))

fun3 : {ℓ : Level} → {x y : V∞ {ℓ}} → (x ≡ y) → (x ≡V∞ y)
fun3 {ℓ = ℓ} {x = sup-∞ x α} {y = sup-∞ y β} p .fst = pathToEquiv (cong overline-∞ p)
fun3 {ℓ = ℓ} {x = sup-∞ x α} {y = sup-∞ y β} p .snd z =
    α z
        ≡⟨ cong α (sym (retEq (fun3 p .fst) z)) ⟩
    α (invEq (fun3 p .fst) (fun3 p .fst .fst z))
        ≡⟨ s (fun3 p .fst .fst z) ⟩
    β (fun3 p .fst .fst z)
        ∎
    where
        postulate s : (n : y) → α (invEq (fun3 p .fst) n) ≡ β n
fun3Inv : {ℓ : Level} {x y : V∞ {ℓ}} → (x ≡V∞ y) → (x ≡ y)
fun3Inv {ℓ = ℓ} {x = sup-∞ x α} {y = sup-∞ y β} (e , p) i = sup-∞ (ua e i) (h i)
    where
        postulate h : PathP (λ j → ua e j → V∞ {ℓ}) α β
        -- h = {!p!}
        -- h j z = {!α (coei→0 (λ k → ua e k) j z)!}

thm3-FTI : {ℓ : Level} (x y : V∞ {ℓ}) → (x ≡ y) ≃ (x ≡V∞ y)
thm3-FTI {ℓ} = fundamentalTheoremOfId _≡V∞_ reflexivity contr
    where
        reflexivity : (x : V∞ {ℓ}) → x ≡V∞ x
        reflexivity (sup-∞ A f) .fst = idEquiv A
        reflexivity (sup-∞ A f) .snd z = refl

        postulate contr : (x : V∞ {ℓ}) → isContr (Σ[ y ∈ V∞ {ℓ} ] x ≡V∞ y)
        -- contr (sup-∞ A f) .fst .fst = sup-∞ A f
        -- contr (sup-∞ A f) .fst .snd = reflexivity (sup-∞ A f)
        -- contr (sup-∞ A f) .snd (sup-∞ B g , p) = ΣPathP ({!!} , {!!})

_≡V∞'_ : {ℓ : Level} → (x y : V∞ {ℓ}) → Type (ℓ-suc ℓ)
(sup-W A f) ≡V∞' (sup-W B g) = Σ[ e ∈ A ≡ B ] ((z : A) → f z ≡ g (transport e z))

fun3' : {ℓ : Level} → {x y : V∞ {ℓ}} → (x ≡ y) → (x ≡V∞' y)
fun3' {ℓ = ℓ} {x = sup-∞ x α} {y = sup-∞ y β} = J fam (refl , λ z → cong α (sym (transportRefl z)))
    where
        fam : (z : V∞ {ℓ}) → (sup-∞ x α) ≡ z → Type (ℓ-suc ℓ)
        fam (sup-∞ z γ) _ = (sup-∞ x α) ≡V∞' (sup-∞ z γ)

-- thm3-fun' : {ℓ : Level} → {x y : V∞ {ℓ}} → x ≡ y → Σ[ e ∈ overline-∞ x ≃ overline-∞ y ] tilde-∞ x ∼ (tilde-∞ y ∘ e .fst)

fun3Inv' : {ℓ : Level} {x y : V∞ {ℓ}} → (x ≡V∞' y) → (x ≡ y)
fun3Inv' {ℓ = ℓ} {x = sup-∞ x α} {y = sup-∞ y β} (p , h) = J2 fam {!!} p {!!}
    where
        fam : {!!}
        fam = {!!}
