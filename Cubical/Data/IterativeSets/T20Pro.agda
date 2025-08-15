-- {-# OPTIONS --no-termination-check #-}
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
open import Cubical.Data.Fin as Fin

open import Cubical.Data.Sigma
open import Cubical.Data.Nat.Order
open import Cubical.Data.Sum using (_⊎_; inl; inr; ⊎-IdL-⊥*-≃) public

-- open import Cubical.

open import Cubical.Homotopy.Base

open import Cubical.Data.W.W

open import Cubical.Data.IterativeSets.Base

private
  variable
    ℓ ℓ' ℓ'' : Level
    A A' : Type ℓ
    B B' : A → Type ℓ

⊥*∼⊥ : ⊥* {ℓ} ≃ ⊥
⊥*∼⊥ = isoToEquiv (iso (λ ()) (λ ()) (λ ()) λ ())

Unit*≃Unit : Unit* {ℓ} ≃ Unit
Unit*≃Unit = isoToEquiv (iso (λ {(lift _) → _}) (λ _ → lift _) (λ _ → refl) λ {(lift _) → refl})

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

_ : El⁰ {ℓ} (vonNeumannEncoding (lift zero)) ≡ ⊥*
_ = refl

_ : El⁰ {ℓ} (vonNeumannEncoding (lift (suc zero))) ≡ ⊥* ⊎ Unit*
_ = refl

_ : El⁰ {ℓ} (vonNeumannEncoding (lift (suc (suc zero)))) ≡ (⊥* ⊎ Unit*) ⊎ Unit*
_ = refl

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

vonNeumannOverline≃Fin : (n : ℕ) → (El⁰ (vonNeumannEncoding {ℓ} (lift n)) ≃ Fin.Fin n)
vonNeumannOverline≃Fin {ℓ} zero = uninhabEquiv (λ ()) ¬Fin0
vonNeumannOverline≃Fin {ℓ} (suc zero) = compEquiv (compEquiv ⊎-IdL-⊥*-≃ Unit*≃Unit) Unit≃Fin1 
vonNeumannOverline≃Fin {ℓ} (suc (suc n)) = compEquiv (El⁰-vNE-suc≃El⁰-vNE⊎Unit* (suc n)) (isoToEquiv (iso f g sec ret))
    where
        f : El⁰ (vonNeumannEncoding (lift (suc n))) ⊎ Unit* → Fin (suc (suc n))
        f (inr _) .fst = suc n
        f (inr _) .snd = ≤-refl
        f (inl x) = finj' (vonNeumannOverline≃Fin {ℓ = ℓ} (suc n) .fst x)

        g : Fin (suc (suc n)) → El⁰ (vonNeumannEncoding (lift (suc n))) ⊎ Unit*
        g (l , zero , sucl≡susucn) = inr _
        g (l , suc k , suck+sucl≡sucsucn) = inl (invEq (vonNeumannOverline≃Fin {ℓ = ℓ} (suc n)) (finj'-ret (l , suc k , suck+sucl≡sucsucn)))

        sec : section f g
        sec (suc l , zero , sucsucl≡sucsucn) = Fin-fst-≡ (sym (injSuc sucsucl≡sucsucn))
        sec (zero , zero , prf) = ⊥-elim {A = λ _ → f (g (zero , zero , prf)) ≡ (zero , zero , prf)} (znots (injSuc prf))
        sec (zero , suc k , prf) = Fin-fst-≡ (cong (fst ∘ finj') (secEq (vonNeumannOverline≃Fin (suc n)) fzero))
        sec (suc l , suc k , prf) = Fin-fst-≡ (cong (fst ∘ finj') (secEq (vonNeumannOverline≃Fin {ℓ = ℓ} (suc n)) (suc l , k , injSuc prf)))

        ret : retract f g
        ret (inr _) = refl
        ret (inl x) = cong (inl ∘ (invEq (vonNeumannOverline≃Fin (suc n)))) (ret-finj' (vonNeumannOverline≃Fin {ℓ = ℓ} (suc n) .fst x)) ∙
                        cong inl (retEq (vonNeumannOverline≃Fin (suc n)) x)

--             g (f (inl x))
--                 ≡⟨⟩
--             g (finj' (vonNeumannOverline≃Fin (suc n) .fst x))
--                 ≡⟨⟩
--             inl (invEq (vonNeumannOverline≃Fin (suc n)) (finj'-ret (finj' (vonNeumannOverline≃Fin (suc n) .fst x))))
--                 ≡⟨ cong (inl ∘ (invEq (vonNeumannOverline≃Fin (suc n)))) (ret-finj' (vonNeumannOverline≃Fin (suc n) .fst x)) ⟩
--             inl (invEq (vonNeumannOverline≃Fin (suc n)) (vonNeumannOverline≃Fin (suc n) .fst x))
--                 ≡⟨ cong inl (retEq (vonNeumannOverline≃Fin (suc n)) x) ⟩
--             inl x
--                 ∎
-- -- ...                                 | zero = compEquiv (compEquiv ⊎-IdL-⊥*-≃ Unit*≃Unit) Unit≃Fin1
-- ...                                 | suc m = compEquiv (El⁰-vNE-suc≃El⁰-vNE⊎Unit* (suc m)) (isoToEquiv (iso f g sec ret))
--     where
--         f : El⁰ (vonNeumannEncoding (lift (suc m))) ⊎ Unit* → Fin.Fin (suc (suc m))
--         f (inr _) .fst = suc m
--         f (inr _) .snd = ≤-refl
--         f (inl x) = finj' (vonNeumannOverline≃Fin (suc m) .fst x)

--         g : Fin.Fin (suc (suc m)) → El⁰ (vonNeumannEncoding (lift (suc m))) ⊎ Unit*
--         g (l , zero , sucl≡sucsucm) = inr _
--         g (l , suc k , suck+sucl≡sucsucm) = inl (invEq (vonNeumannOverline≃Fin (suc m)) (finj'-ret (l , suc k , suck+sucl≡sucsucm)))

--         sec : section f g
--         sec (l , zero , sucl≡sucsucm) = Fin-fst-≡ (sym (injSuc sucl≡sucsucm))
--         sec (l , suc k , suck+sucl≡sucsucm) = Fin-fst-≡ (cong (fst ∘ finj') (secEq {!vonNeumannOverline≃Fin (suc m)!} (l , k , injSuc suck+sucl≡sucsucm)))
            -- f (g (l , suc k , suck+sucl≡sucsucm)) .fst
            --     ≡⟨⟩
            -- f (inl (invEq (vonNeumannOverline≃Fin (suc m)) (finj'-ret (l , suc k , suck+sucl≡sucsucm)))) .fst
            --     ≡⟨⟩
            -- finj' (vonNeumannOverline≃Fin (suc m) .fst (invEq (vonNeumannOverline≃Fin (suc m)) (finj'-ret (l , suc k , suck+sucl≡sucsucm)))) .fst
            --     ≡⟨⟩
            -- finj' (vonNeumannOverline≃Fin (suc m) .fst (invEq (vonNeumannOverline≃Fin (suc m)) (l , k , injSuc suck+sucl≡sucsucm))) .fst
            --     ≡⟨ cong finj'  ⟩
            -- finj' (l , k , injSuc suck+sucl≡sucsucm) .fst
            --     ≡⟨ {!!} ⟩
            -- l
            --     ∎)

        -- postulate ret : retract f g
-- vonNeumannOverline≃Fin {ℓ} (suc zero) = compEquiv (compEquiv ⊎-IdL-⊥*-≃ Unit*≃Unit) Unit≃Fin1
-- vonNeumannOverline≃Fin {ℓ} (suc (suc n)) = {!!} -- compEquiv (El⁰-vNE-suc≃El⁰-vNE⊎Unit* (suc n)) (isoToEquiv (iso f g sec ret))
    -- where
    --     f : El⁰ (vonNeumannEncoding (lift (suc n))) ⊎ Unit* → Fin.Fin (suc (suc n))
    --     f (inr _) .fst = suc n
    --     f (inr _) .snd = ≤-refl
    --     f (inl x) = Fin.finj (vonNeumannOverline≃Fin (suc n) .fst x)
    --     g : Fin.Fin (suc (suc n)) → El⁰ (vonNeumannEncoding (lift (suc n))) ⊎ Unit*
    --     g (m , zero , sucm≡sucsucn) = inr _
    --     g (m , suc k , suc+sucm≡sucsucn) = inl (invEq (vonNeumannOverline≃Fin (suc n)) {!!})
    --     postulate sec : section f g
    --     postulate ret : retract f g
        -- the following commented out stuff is correct (just replace n with suc n), I just need to figure out how to make Agda realize that the above terminates
-- vonNeumannOverline≃Fin {ℓ} (suc n) = compEquiv (El⁰-vNE-suc≃El⁰-vNE⊎Unit* n) (isoToEquiv (iso f g sec ret))
--     where
--         f : El⁰ (vonNeumannEncoding (lift n)) ⊎ Unit* → Fin.Fin (suc n)
--         f (inr _) .fst = n
--         f (inr _) .snd = ≤-refl
--         f (inl x) = Fin.finj (vonNeumannOverline≃Fin n .fst x)

--         g : Fin.Fin (suc n) → El⁰ (vonNeumannEncoding (lift n)) ⊎ Unit*
--         g (m , zero , sucm≡sucn) = inr _
--         g (m , suc k , suck+sucm≡sucn) = inl (invEq (vonNeumannOverline≃Fin n) (record {fst = m; snd = record {fst = k; snd = injSuc suck+sucm≡sucn {- : k + suc m ≡ n-}}}))

--         test : (a : ℕ) → (p : zero + a ≡ a) → p ≡ refl {x = a}
--         test a p = isSetℕ a a p refl

--         predFin' : Fin.Fin (suc n) → Fin.Fin n
--         predFin' (zero , prf) = zero , {!!}
--         predFin' (suc m , prf) = {!!}

--         sec : section f g
--         sec (m , zero , sucm≡sucn) = Fin-fst-≡ (sym (injSuc sucm≡sucn))
--         sec (m , suc k , suck+sucm≡sucn) = Fin-fst-≡ (cong (λ x → fst (Fin.finj x)) (secEq (vonNeumannOverline≃Fin n) _))
        
--         ret : retract f g
--         ret (inr _) = refl
--         ret (inl x) = {!!}
--             -- g (f (inl x))
--             --     ≡⟨⟩
--             -- g (Fin.finj (vonNeumannOverline≃Fin n .fst x .fst , vonNeumannOverline≃Fin n .fst x .snd .fst , (λ i → vonNeumannOverline≃Fin n .fst x .snd .snd i)))
--             --     ≡⟨⟩
--             -- g (vonNeumannOverline≃Fin n .fst x .fst , vonNeumannOverline≃Fin n .fst x .snd .fst + 1 , _)
--             --     ≡⟨ cong (λ x → g (_ , x , _)) (+1≡suc _) ⟩
--             -- g (vonNeumannOverline≃Fin n .fst x .fst , suc (vonNeumannOverline≃Fin n .fst x .snd .fst) , _)
--             --     ≡⟨ {!!} ⟩
--             -- inl x
--             --     ∎
        
ℕ⁰' : V⁰ {ℓ}
ℕ⁰' {ℓ} = sup⁰ (ℕ* {ℓ} , vonNeumannEncoding {ℓ} , isemb)
    where
        isinj : (w x : ℕ* {ℓ}) → vonNeumannEncoding w ≡ vonNeumannEncoding x → w ≡ x
        isinj (lift n) (lift m) p = liftExt (Fin-inj n m (ua (compEquiv (invEquiv (vonNeumannOverline≃Fin n)) (compEquiv (pathToEquiv (cong overline-0 p)) (vonNeumannOverline≃Fin m)))))
        isemb : isEmbedding (vonNeumannEncoding {ℓ})
        isemb = injEmbedding thm12 λ {w} {x} → isinj w x

ℕ⁰Isℕ*' : El⁰ (ℕ⁰' {ℓ}) ≡ ℕ* {ℓ}
ℕ⁰Isℕ*' = refl

ℕ-≢0→is-suc : (n : ℕ) → (n ≡ 0 → ⊥) → Σ[ m ∈ ℕ ] n ≡ suc m
ℕ-≢0→is-suc zero n≢0 = ⊥-elim (n≢0 refl)
ℕ-≢0→is-suc (suc m) _ .fst = m
ℕ-≢0→is-suc (suc _) _ .snd = refl
