-- {-# OPTIONS --no-termination-check #-}
{-# OPTIONS --termination-depth 2 #-}
module Cubical.Data.IterativeSets.Nat where
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
open import Cubical.Data.Fin as Fin
open import Cubical.Relation.Nullary using (¬_)

open import Cubical.Data.Sigma
open import Cubical.Data.Nat.Order
open import Cubical.Data.Sum using (_⊎_; inl; inr; ⊎-IdL-⊥*-≃) public

open import Cubical.Homotopy.Base

open import Cubical.Data.IterativeMultisets.Base renaming (overline to overline-∞ ; tilde to tilde-V∞)
open import Cubical.Data.IterativeSets.Base
open import Cubical.Data.IterativeSets.Empty

-- TODO: think about whether to switch to using Data.SumFin

private
  variable
    ℓ ℓ' ℓ'' : Level
    A A' : Type ℓ
    B B' : A → Type ℓ

⊥*∼⊥ : ⊥* {ℓ} ≃ ⊥
⊥*∼⊥ = isoToEquiv (iso (λ ()) (λ ()) (λ ()) λ ())

Unit*≃Unit : Unit* {ℓ} ≃ Unit
Unit*≃Unit = isoToEquiv (iso (λ {(lift _) → _}) (λ _ → lift _) (λ _ → refl) λ {(lift _) → refl})

isPropIsPropDisjointSum : {A : Type ℓ} {B : Type ℓ} → isProp A → isProp B → ¬ A × B → isProp (A ⊎ B)
isPropIsPropDisjointSum propA propB disj (inl a₁) (inl a₂) = cong inl (propA a₁ a₂)
isPropIsPropDisjointSum propA propB disj (inr b₁) (inr b₂) = cong inr (propB b₁ b₂)
isPropIsPropDisjointSum propA propB disj (inl a) (inr b) = ⊥-elim (disj (a , b))
isPropIsPropDisjointSum propA propB disj (inr b) (inl a) = ⊥-elim (disj (a , b))


suc⁰ : {ℓ : Level} → V⁰ {ℓ} → V⁰ {ℓ}
suc⁰ {ℓ} (sup-∞ A f , isitsetAf) = fromEmb E
    where
        ϕₓ : (overline (sup-∞ A f , isitsetAf) ⊎ Unit* {ℓ}) → V⁰ {ℓ}
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
        hpf (sup-∞ B g , isitsetBg) = isOfHLevelRespectEquiv 1 (invEquiv (eqFib (sup-∞ B g , isitsetBg))) (isPropIsPropDisjointSum (isEmbedding→hasPropFibers (isEmbedding-tilde (sup-∞ A f , isitsetAf)) (sup-∞ B g , isitsetBg)) (isSetV⁰ _ _) ∈⁰×≡→⊥)
            where
                ∈⁰×≡→⊥ : ((sup-∞ B g , isitsetBg) ∈⁰ (sup-∞ A f , isitsetAf)) × ((sup-∞ A f , isitsetAf) ≡ (sup-∞ B g , isitsetBg)) → ⊥
                ∈⁰×≡→⊥ ((a , pa) , p) = ∈⁰-irrefl {x = (sup-∞ B g , isitsetBg)} (transport (cong (λ r → ((sup-∞ B g , isitsetBg) ∈⁰ r)) p) (a , pa))

        E : Embedding (V⁰ {ℓ}) ℓ
        E .fst = A ⊎ Unit* {ℓ}
        E .snd .fst = ϕₓ
        E .snd .snd = hasPropFibers→isEmbedding hpf

ℕ* : Type ℓ
ℕ* = Lift ℕ

vonNeumannEncoding : ℕ* {ℓ} → V⁰ {ℓ}
vonNeumannEncoding (lift zero) = empty⁰
vonNeumannEncoding (lift (suc x)) = suc⁰ (vonNeumannEncoding (lift x))

El⁰-suc⁰≡El⁰⊎Unit* : {x : V⁰ {ℓ}} → El⁰ {ℓ} (suc⁰ x) ≡ (El⁰ x ⊎ Unit* {ℓ})
-- El⁰-suc⁰≡El⁰⊎Unit* = refl -- doesn't work
El⁰-suc⁰≡El⁰⊎Unit* {x = (sup-∞ _ _ , _)} = refl

El⁰-vNE-suc≡El⁰-vNE⊎Unit* : (n : ℕ) → El⁰ {ℓ} (vonNeumannEncoding (lift (suc n))) ≡ (El⁰ {ℓ} (vonNeumannEncoding (lift n))) ⊎ Unit* {ℓ}
-- El⁰-vNE-suc≡El⁰-vNE⊎Unit* _ = refl -- doesn't work
El⁰-vNE-suc≡El⁰-vNE⊎Unit* n = El⁰-suc⁰≡El⁰⊎Unit* {x = vonNeumannEncoding (lift n)}

El⁰-vNE-suc≃El⁰-vNE⊎Unit* : (n : ℕ) → El⁰ {ℓ} (vonNeumannEncoding (lift (suc n))) ≃ (El⁰ {ℓ} (vonNeumannEncoding (lift n))) ⊎ Unit* {ℓ}
El⁰-vNE-suc≃El⁰-vNE⊎Unit* = pathToEquiv ∘ El⁰-vNE-suc≡El⁰-vNE⊎Unit*

+1≡suc : (n : ℕ) → (n + 1 ≡ suc n)
+1≡suc n = +-comm n 1

finj' : {n : ℕ} → Fin n → Fin (suc n)
finj' (m , _) .fst = m
finj' (_ , k , _) .snd .fst = suc k
finj' (_ , _ , prf) .snd .snd = cong suc prf

finj'-ret : {n : ℕ} → Fin (suc (suc n)) → Fin (suc n)
finj'-ret (zero , _) = fzero
finj'-ret (suc m , zero , _) .fst = m
finj'-ret (suc _ , zero , prf) .snd = pred-≤-pred (zero , prf)
finj'-ret (suc m , suc _ , _) .fst = suc m
finj'-ret (suc _ , suc k , _) .snd .fst = k
finj'-ret (suc _ , suc _ , prf) .snd .snd = injSuc prf

ret-finj' : {n : ℕ} → retract (finj' {n = suc n}) (finj'-ret {n = n})
ret-finj' {n} (zero , _) = Fin-fst-≡ refl
ret-finj' {n} (suc m , k , prf) = Fin-fst-≡ refl

vonNeumannOverline≃Fin : (n : ℕ) → (El⁰ (vonNeumannEncoding {ℓ} (lift n)) ≃ Fin n)
vonNeumannOverline≃Fin {ℓ} = elim+2 case0 case1 caseSuc
    where
        case0 : El⁰ (vonNeumannEncoding (lift 0)) ≃ Fin 0
        case0 = uninhabEquiv (λ ()) ¬Fin0
        case1 : El⁰ (vonNeumannEncoding (lift 1)) ≃ Fin 1
        case1 = compEquiv (compEquiv ⊎-IdL-⊥*-≃ Unit*≃Unit) Unit≃Fin1 
        caseSuc : (n : ℕ) → El⁰ (vonNeumannEncoding (lift (suc n))) ≃ Fin (suc n) → El⁰ (vonNeumannEncoding (lift (suc (suc n)))) ≃ Fin (suc (suc n))
        caseSuc n indHyp = compEquiv (El⁰-vNE-suc≃El⁰-vNE⊎Unit* (suc n)) (isoToEquiv (iso f g sec ret))
            where
                f : El⁰ (vonNeumannEncoding (lift (suc n))) ⊎ Unit* → Fin (suc (suc n))
                f (inr _) .fst = suc n
                f (inr _) .snd = ≤-refl
                f (inl x) = finj' (indHyp .fst x)
                g : Fin (suc (suc n)) → El⁰ (vonNeumannEncoding (lift (suc n))) ⊎ Unit*
                g (l , zero , sucl≡susucn) = inr _
                g (l , suc k , suck+sucl≡sucsucn) = inl (invEq indHyp (finj'-ret (l , suc k , suck+sucl≡sucsucn)))
                sec : section f g
                sec (suc l , zero , sucsucl≡sucsucn) = Fin-fst-≡ (sym (injSuc sucsucl≡sucsucn))
                sec (zero , zero , prf) = ⊥-elim {A = λ _ → f (g (zero , zero , prf)) ≡ (zero , zero , prf)} (znots (injSuc prf))
                sec (zero , suc k , prf) = Fin-fst-≡ (cong (fst ∘ finj') (secEq indHyp fzero))
                sec (suc l , suc k , prf) = Fin-fst-≡ (cong (fst ∘ finj') (secEq indHyp (suc l , k , injSuc prf)))
                ret : retract f g
                ret (inr _) = refl
                ret (inl x) = cong (inl ∘ (invEq indHyp)) (ret-finj' (indHyp .fst x)) ∙
                                cong inl (retEq indHyp x)

-- for some reason the following doesn't termination check
-- it does with termination depth > 1
vonNeumannOverline≃Fin' : (n : ℕ) → (El⁰ (vonNeumannEncoding {ℓ} (lift n)) ≃ Fin n)
vonNeumannOverline≃Fin' {ℓ} zero = uninhabEquiv (λ ()) ¬Fin0
vonNeumannOverline≃Fin' {ℓ} (suc zero) = compEquiv (compEquiv ⊎-IdL-⊥*-≃ Unit*≃Unit) Unit≃Fin1 
vonNeumannOverline≃Fin' {ℓ} (suc (suc n)) = compEquiv (El⁰-vNE-suc≃El⁰-vNE⊎Unit* (suc n)) (isoToEquiv (iso f g sec ret))
    where
        f : El⁰ (vonNeumannEncoding (lift (suc n))) ⊎ Unit* → Fin (suc (suc n))
        f (inr _) .fst = suc n
        f (inr _) .snd = ≤-refl
        f (inl x) = finj' (vonNeumannOverline≃Fin' {ℓ = ℓ} (suc n) .fst x)

        g : Fin (suc (suc n)) → El⁰ (vonNeumannEncoding (lift (suc n))) ⊎ Unit*
        g (l , zero , sucl≡susucn) = inr _
        g (l , suc k , suck+sucl≡sucsucn) = inl (invEq (vonNeumannOverline≃Fin' {ℓ = ℓ} (suc n)) (finj'-ret (l , suc k , suck+sucl≡sucsucn)))

        sec : section f g
        sec (suc l , zero , sucsucl≡sucsucn) = Fin-fst-≡ (sym (injSuc sucsucl≡sucsucn))
        sec (zero , zero , prf) = ⊥-elim {A = λ _ → f (g (zero , zero , prf)) ≡ (zero , zero , prf)} (znots (injSuc prf))
        sec (zero , suc k , prf) = Fin-fst-≡ (cong (fst ∘ finj') (secEq (vonNeumannOverline≃Fin' {ℓ = ℓ} (suc n)) fzero))
        sec (suc l , suc k , prf) = Fin-fst-≡ (cong (fst ∘ finj') (secEq (vonNeumannOverline≃Fin' {ℓ = ℓ} (suc n)) (suc l , k , injSuc prf)))

        ret : retract f g
        ret (inr _) = refl
        ret (inl x) = cong (inl ∘ (invEq (vonNeumannOverline≃Fin' {ℓ = ℓ} (suc n)))) (ret-finj' (vonNeumannOverline≃Fin' {ℓ = ℓ} (suc n) .fst x)) ∙
                        cong inl (retEq (vonNeumannOverline≃Fin' {ℓ = ℓ} (suc n)) x)
        
ℕ⁰ : V⁰ {ℓ}
ℕ⁰ {ℓ} = fromEmb E
    where
        isinj : (w x : ℕ* {ℓ}) → vonNeumannEncoding w ≡ vonNeumannEncoding x → w ≡ x
        isinj (lift n) (lift m) p = liftExt (Fin-inj n m (ua (compEquiv (invEquiv (vonNeumannOverline≃Fin n)) (compEquiv (pathToEquiv (cong overline p)) (vonNeumannOverline≃Fin m)))))
        E : Embedding (V⁰ {ℓ}) ℓ
        E .fst = ℕ* {ℓ}
        E .snd .fst = vonNeumannEncoding {ℓ}
        E .snd .snd = injEmbedding isSetV⁰ (λ {w} {x} → isinj w x)

ℕ⁰Isℕ* : El⁰ (ℕ⁰ {ℓ}) ≡ ℕ* {ℓ}
ℕ⁰Isℕ* = refl

-- TODO: remove or add somewhere else
ℕ-≢0→is-suc : (n : ℕ) → (n ≡ 0 → ⊥) → Σ[ m ∈ ℕ ] n ≡ suc m
ℕ-≢0→is-suc zero n≢0 = ⊥-elim (n≢0 refl)
ℕ-≢0→is-suc (suc m) _ .fst = m
ℕ-≢0→is-suc (suc _) _ .snd = refl
