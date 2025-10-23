{-# OPTIONS --allow-unsolved-metas #-}
module Cubical.Data.IterativeSets.Base where

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude

open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Functions.Embedding
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
open import Cubical.Relation.Nullary using (¬_)
open import Cubical.Foundations.GroupoidLaws

-- TODO: remove ⊥*-elim, Data.Unit, Data.Bool Data.SumFin once the statements that need them have found their way to a better place
open import Cubical.Data.Empty renaming (elim* to ⊥*-elim ; elim to ⊥-elim)
open import Cubical.Data.Unit
open import Cubical.Data.Bool
open import Cubical.Data.Sum renaming (rec to ⊎-rec)

open import Cubical.Data.IterativeMultisets.Base

private
  variable
    ℓ : Level

-- TODO: potentially don't do pattern matching, change everywhere afterwards?
isIterativeSet : V∞ {ℓ} → Type (ℓ-suc ℓ)
isIterativeSet (sup-∞ A f) = (isEmbedding f) × ((a : A) → isIterativeSet (f a))

V⁰ : Type (ℓ-suc ℓ)
V⁰ = Σ[ x ∈ V∞ ] isIterativeSet x

private
  variable
    x y z : V⁰ {ℓ}

-- TODO: For the sake of consistency, I think it should be called overline⁰, similarly tilde⁰, or maybe even ⁻⁰, ̃⁰, idk
overline-0 : V⁰ {ℓ} → Type ℓ
-- overline-0 (sup-∞ A _ , _) = A
overline-0 = overline-∞ ∘ fst

tilde-0 : (x : V⁰ {ℓ}) → overline-0 x → V∞ {ℓ}
-- tilde-0 (sup-∞ B f , p) = f
tilde-0 = tilde-∞ ∘ fst

-- TODO: refactor so that everything that uses tilde-0 now uses tilde-0' instead; afterwards change name to tilde-0 or tilde⁰ (depending on whether the above todo is implemented)
tilde-0' : (x : V⁰ {ℓ}) → overline-0 x → V⁰ {ℓ}
-- the following doesn't work because seemingly `isIterativeSet` cannot be destructured
-- tilde-0' x a .fst = tilde-∞ (x .fst) a
-- tilde-0' x a .snd = {!x .snd .snd a!}
tilde-0' (sup-∞ _ f , _) a .fst = f a
tilde-0' (sup-∞ _ _ , isitset) a .snd = isitset .snd a


_∈⁰_ : V⁰ {ℓ} → V⁰ {ℓ} → Type (ℓ-suc ℓ)
x ∈⁰ y = fiber (tilde-0' y) (x)

∈⁰-irrefl : ¬ x ∈⁰ x
∈⁰-irrefl {x = sup-∞ A f , isitset} (a , p) = ∈∞-irrefl {x = sup-∞ A f} (a , cong fst p)

-- TODO: rename to isEmbedding-tilde-0
isEmbedding-tilde-∞ : (x : V⁰ {ℓ}) → isEmbedding (tilde-0 x)
isEmbedding-tilde-∞ (sup-∞ A f , isitset) = isitset .fst

isProp∈∞ : {z : V∞ {ℓ}} → isProp (z ∈∞ (x .fst))
isProp∈∞ {x = x} {z = z} = isEmbedding→hasPropFibers (isEmbedding-tilde-∞ x) z

lem10 : (x : V∞ {ℓ}) → isProp (isIterativeSet x)
lem10 (sup-∞ A f) = isProp× (isPropIsEmbedding) helper where
  helper : isProp ((a : A) → isIterativeSet (f a))
  helper g h i x = lem10 (f x) (g x) (h x) i

cor11 : V⁰ {ℓ} ↪ V∞ {ℓ}
cor11 = EmbeddingΣProp lem10

-- TODO: move to better place
embeddingToEquivOfPath : {ℓ ℓ' : Level} {A : Type ℓ} → {B : Type ℓ'} → {f : A → B} → isEmbedding f → (x y : A) → (x ≡ y) ≃ (f x ≡ f y)
embeddingToEquivOfPath {f = f} _ _ _ .fst = cong f
embeddingToEquivOfPath isemb x y .snd = isemb x y

cor11-1 : (x ≡ y) ≃ (x .fst ≡ y .fst)
cor11-1 = invEquiv (Σ≡PropEquiv lem10)

thm12-help1 : ((x ≡ y) ≃ ((z : V∞) → fiber (tilde-∞ (x .fst)) z ≃ fiber (tilde-∞ (y .fst)) z))
thm12-help1 = compEquiv cor11-1 thm4

-- couldn't find it in the library
isPropEquiv : {ℓ ℓ' : Level} → {A : Type ℓ} → {B : Type ℓ'} → isProp A → isProp B → isProp (A ≃ B)
isPropEquiv _ pB = isPropΣ (isPropΠ (λ _ → pB)) isPropIsEquiv

thm12-help2 : (x y : V⁰ {ℓ}) → isProp ((z : V∞) → (z ∈∞ (x .fst)) ≃ (z ∈∞ (y .fst)))
thm12-help2 x y = isPropΠ λ z → isPropEquiv (isProp∈∞ {x = x} {z = z}) (isProp∈∞ {x = y} {z = z})

thm12 : isSet (V⁰ {ℓ})
thm12 x y = isOfHLevelRespectEquiv 1 (invEquiv thm12-help1) (thm12-help2 x y)

-- if f : A → B and g : B → C are functions and g ∘ f is injective, then f is injective too
-- probably can be generalized to embeddings (potentially with assuming that g is an embedding too, but this is a WIP, see `T15DefDesup.agda`
firstInInjCompIsInj : {ℓ ℓ' ℓ'' : Level} {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''} → (f : A → B) → (g : B → C) → ((w x : A) → g (f w) ≡ g (f x) → w ≡ x) → {w x : A} → f w ≡ f x → w ≡ x
firstInInjCompIsInj f g inj∘ {w} {x} p = inj∘ w x (cong g p)

isEmbedding-tilde-0 : (x : V⁰ {ℓ}) → isEmbedding (tilde-0' x)
isEmbedding-tilde-0 (sup-∞ A f , isitset) = injEmbedding thm12 (firstInInjCompIsInj (tilde-0' (sup-∞ A f , isitset)) fst (isEmbedding→Inj (isEmbedding-tilde-∞ (sup-∞ A f , isitset))))

-- TODO: figure out why removing {x z : V⁰ {ℓ}} doesn't work (complains about z)...
isProp∈⁰ : {x z : V⁰ {ℓ}} → isProp (z ∈⁰ x)
isProp∈⁰ {x = x} {z = z} = isEmbedding→hasPropFibers (isEmbedding-tilde-0 x) z

sup⁰ : (Σ[ A ∈ Type ℓ ] A ↪ V⁰ {ℓ}) → V⁰ {ℓ}
sup⁰ (A , f) .fst = sup-∞ A (compEmbedding cor11 f .fst) -- λ x → f .fst x .fst
sup⁰ (A , f) .snd .fst = compEmbedding cor11 f .snd
sup⁰ (A , f) .snd .snd y = f .fst y .snd

desup⁰ : V⁰ {ℓ} → (Σ[ A ∈ Type ℓ ] A ↪ V⁰ {ℓ})
desup⁰ (sup-∞ A f , isitset) .fst = A
desup⁰ (sup-∞ A f , isitset) .snd .fst x .fst = f x
desup⁰ (sup-∞ A f , isitset) .snd .fst x .snd = isitset .snd x
desup⁰ (sup-∞ A f , isitset) .snd .snd = injEmbedding thm12 (firstInInjCompIsInj _ (cor11 .fst) (isEmbedding→Inj (isEmbedding-tilde-∞ (sup-∞ A f , isitset))))

sup⁰desup⁰≃ : (V⁰ {ℓ} ≃ (Σ[ A ∈ Type ℓ ] A ↪ V⁰ {ℓ}))
sup⁰desup⁰≃ {ℓ} = isoToEquiv (iso desup⁰ sup⁰ sec ret)
    where
        sec : section (desup⁰ {ℓ}) (sup⁰ {ℓ})
        sec (A , (f , embf)) = cong (λ e → (A , (f , e))) (isPropIsEmbedding {f = f} _ embf)

        ret : retract (desup⁰ {ℓ}) (sup⁰ {ℓ}) 
        ret (sup-∞ A f , isitset) = cong fun (lem10 (sup-∞ A f) _ isitset)
            where
                fun : isIterativeSet (sup-∞ A f) → V⁰ {ℓ}
                fun _ .fst = sup-∞ A f
                fun it .snd = it

-- Ch. 3

El⁰ : V⁰ {ℓ} → Type ℓ
El⁰ = overline-0

desup⁰' : (x : V⁰ {ℓ}) → (El⁰ x ↪ V⁰ {ℓ})
desup⁰' (sup-∞ A f , isitset) = desup⁰ (sup-∞ A f , isitset) .snd

thm17 : (x : V⁰ {ℓ}) → isSet (El⁰ x)
thm17 {ℓ} (sup-∞ A f , isitset) = Embedding-into-isSet→isSet {A = El⁰ {ℓ} (sup-∞ A f , isitset)} {B = V⁰ {ℓ}} (desup⁰' (sup-∞ A f , isitset)) (thm12 {ℓ})

postulate pro18 : {A : Type ℓ} → ((A ↪ V⁰ {ℓ}) ≃ (Σ[ a ∈ V⁰ {ℓ} ] El⁰ a ≡ A))

-- move this to some other place in the library
isEmbeddingFunctionFromIsPropToIsSet : {ℓ ℓ' : Level} {A : Type ℓ} {B : Type ℓ'} (f : A → B) → isProp A → isSet B → isEmbedding f
isEmbeddingFunctionFromIsPropToIsSet f propA setB = injEmbedding setB λ {w} {x} _ → propA w x

isProp-∈⁰-Equiv : (x y : V⁰ {ℓ}) → isProp ((z : V⁰) → (z ∈⁰ x) ≃ (z ∈⁰ y))
isProp-∈⁰-Equiv x y = isPropΠ λ z → isPropEquiv (isProp∈⁰ {x = x} {z = z}) (isProp∈⁰ {x = y} {z = z})

∈⁰≃∈∞ : {x z : V⁰ {ℓ}} → (z ∈⁰ x) ≃ (z .fst ∈∞ x .fst)
∈⁰≃∈∞ {x = sup-∞ x α , itsetx} {z = sup-∞ z γ , itsetz} = propBiimpl→Equiv (isProp∈⁰ {x = sup-∞ x α , itsetx} {z = sup-∞ z γ , itsetz}) (isProp∈∞ {x = sup-∞ x α , itsetx} {z = sup-∞ z γ}) f g
    where
        f : (sup-∞ z γ , itsetz) ∈⁰ (sup-∞ x α , itsetx) → sup-∞ z γ ∈∞ sup-∞ x α
        f (a , p) .fst = a
        f (a , p) .snd = cong fst p
        g : sup-∞ z γ ∈∞ sup-∞ x α → (sup-∞ z γ , itsetz) ∈⁰ (sup-∞ x α , itsetx)
        g (a , p) .fst = a
        g (a , p) .snd = Σ≡Prop lem10 p

thm4'-helper : {x y : V⁰ {ℓ}} → (((z : V∞ {ℓ}) → (z ∈∞ x .fst) ≃ (z ∈∞ y .fst)) ≃ ((z : V⁰ {ℓ}) → (z ∈⁰ x) ≃ (z ∈⁰ y)))
thm4'-helper {x = sup-∞ x α , itsetx} {y = sup-∞ y β , itsety} = propBiimpl→Equiv (thm12-help2 (sup-∞ x α , itsetx) (sup-∞ y β , itsety)) (isProp-∈⁰-Equiv (sup-∞ x α , itsetx) (sup-∞ y β , itsety)) f g
    where
       f : ((z : V∞) → (z ∈∞ sup-∞ x α) ≃ (z ∈∞ sup-∞ y β)) → (z : V⁰) → (z ∈⁰ (sup-∞ x α , itsetx)) ≃ (z ∈⁰ (sup-∞ y β , itsety))
       f fibEquiv z = compEquiv (compEquiv (∈⁰≃∈∞ {x = sup-∞ x α , itsetx} {z = z}) (fibEquiv (z .fst))) (invEquiv (∈⁰≃∈∞ {x = sup-∞ y β , itsety} {z = z}))
       g : ((z : V⁰) → (z ∈⁰ (sup-∞ x α , itsetx)) ≃ (z ∈⁰ (sup-∞ y β , itsety))) → (z : V∞) → (z ∈∞ sup-∞ x α) ≃ (z ∈∞ sup-∞ y β)
       g fibEquiv z = propBiimpl→Equiv (isProp∈∞ {x = sup-∞ x α , itsetx} {z = z}) (isProp∈∞ {x = sup-∞ y β , itsety} {z = z}) (helper {u = sup-∞ x α , itsetx} {v = sup-∞ y β , itsety} fibEquiv) (helper {u = sup-∞ y β , itsety} {v = sup-∞ x α , itsetx} λ z' → invEquiv (fibEquiv z'))
           where
               helper : {u v : V⁰} → ((z' : V⁰) → (z' ∈⁰ u) ≃ (z' ∈⁰ v)) → z ∈∞ u .fst → z ∈∞ v .fst
               helper {u = sup-∞ u δ , itsetu} {v = sup-∞ v ζ , itsetv} fE (a , p) = ∈⁰≃∈∞ {x = sup-∞ v ζ , itsetv} {z = z⁰} .fst (fE z⁰ .fst (invEq (∈⁰≃∈∞ {x = sup-∞ u δ , itsetu} {z = z⁰}) (a , p)))
                   where
                       z⁰ : V⁰
                       z⁰ .fst = z
                       z⁰ .snd = transport (cong isIterativeSet p) (itsetu .snd a)

thm4' : (x ≡ y) ≃ ((z : V⁰ {ℓ}) → (z ∈⁰ x) ≃ (z ∈⁰ y))
thm4' {x = x} {y = y} = compEquiv cor11-1 (compEquiv thm4 (thm4'-helper {x = x} {y = y}))

-- move to better place
⊥*≢Unit* : ((⊥* {ℓ} :> Type ℓ) ≡ (Unit* {ℓ} :> Type ℓ)) → ⊥
⊥*≢Unit* p = ⊥*-elim {A = λ _ → ⊥} (transport (sym p) (lift tt))

Unit*≢⊥* : ((Unit* {ℓ} :> Type ℓ) ≡ (⊥* {ℓ} :> Type ℓ)) → ⊥
Unit*≢⊥* p = ⊥*-elim {A = λ _ → ⊥} (transport p (lift tt))

-- this should be somewhere else, but I couldn't find it in the library for some reason
≡-from-isOfHLevel→isOfHLevel : {ℓ : Level} {A B : Type ℓ} {n : HLevel} → A ≡ B → isOfHLevel n A → isOfHLevel n B
≡-from-isOfHLevel→isOfHLevel {n = n} A≡B = transport (cong (isOfHLevel n) A≡B)

≡-to-isOfHLevel→isOfHLevel : {ℓ : Level} {A B : Type ℓ} {n : HLevel} → A ≡ B → isOfHLevel n B → isOfHLevel n A
≡-to-isOfHLevel→isOfHLevel {n = n} A≡B = transport (cong (isOfHLevel n) (sym A≡B))

≡-to-isContr→isContr : {ℓ : Level} {A B : Type ℓ} → A ≡ B → isContr B → isContr A
≡-to-isContr→isContr = ≡-to-isOfHLevel→isOfHLevel {n = 0}

≡-from-isContr→isContr : {ℓ : Level} {A B : Type ℓ} → A ≡ B → isContr A → isContr B
≡-from-isContr→isContr = ≡-from-isOfHLevel→isOfHLevel {n = 0}

≡-to-isProp→isProp : {ℓ : Level} {A B : Type ℓ} → A ≡ B → isProp B → isProp A
≡-to-isProp→isProp = ≡-to-isOfHLevel→isOfHLevel {n = 1}

≡-from-isProp→isProp : {ℓ : Level} {A B : Type ℓ} → A ≡ B → isProp A → isProp B
≡-from-isProp→isProp = ≡-from-isOfHLevel→isOfHLevel {n = 1}

≡-to-isSet→isSet : {ℓ : Level} {A B : Type ℓ} → A ≡ B → isSet B → isSet A
≡-to-isSet→isSet = ≡-to-isOfHLevel→isOfHLevel {n = 2}

≡-from-isSet→isSet : {ℓ : Level} {A B : Type ℓ} → A ≡ B → isSet A → isSet B
≡-from-isSet→isSet = ≡-from-isOfHLevel→isOfHLevel {n = 2}

Unit≢Bool : ¬ (Unit ≡ Bool)
Unit≢Bool p = false≢true (≡-from-isProp→isProp p isPropUnit false true)

Bool≢Unit : ¬ (Bool ≡ Unit)
Bool≢Unit p = false≢true (≡-to-isProp→isProp p isPropUnit false true)

false*≢true* : ¬ (false* {ℓ} ≡ true* {ℓ})
false*≢true* p = subst (λ b → if b .lower then Unit else ⊥) (sym p) tt

true*≢false* : ¬ (true* {ℓ} ≡ false* {ℓ})
true*≢false* p = subst (λ b → if b .lower then Unit else ⊥) p tt

Unit*≢Bool* : ¬ (Unit* {ℓ} ≡ Bool* {ℓ})
Unit*≢Bool* p = false*≢true* (≡-from-isProp→isProp p isPropUnit* false* true*)

Bool*≢Unit* : ¬ (Bool* {ℓ} ≡ Unit* {ℓ})
Bool*≢Unit* p = false*≢true* (≡-to-isProp→isProp p isPropUnit* false* true*)

-- probably also move to some better place in the library
module _ {ℓ ℓ' ℓ'' : Level} {X : Type ℓ} {Y : Type ℓ'} {Z : Type ℓ''} (setX : isSet X) (x₀ : X) (f : (X × Y) → Z) (embf : isEmbedding f) where
    f-x₀ : Y → Z
    f-x₀ = curry f x₀

    lem26 : isEmbedding f-x₀
    lem26 = hasPropFibers→isEmbedding (λ z → isPropRetract (g z) (h z) (ret z) (isPropΣ (isEmbedding→hasPropFibers embf z) λ s → setX (s .fst .fst) x₀))
        where
            g : (z : Z) → (fiber f-x₀ z) → (Σ[ s ∈ fiber f z ] (s .fst .fst) ≡ x₀)
            g z _ .fst .fst .fst = x₀
            g z fib .fst .fst .snd = fib .fst
            g z fib .fst .snd = fib .snd
            g z _ .snd = refl

            h : (z : Z) → (Σ[ s ∈ fiber f z ] (s .fst .fst) ≡ x₀) → (fiber f-x₀ z)
            -- h z (((x , y) , q) , p) .fst = y
            h z s .fst = s .fst .fst .snd
            h z s .snd = cong (λ x' → f (x' , (s .fst .fst .snd))) (sym (s .snd)) ∙ (s .fst .snd)

            ret : (z : Z) → retract (g z) (h z)
            ret z fib = cong (fib .fst ,_) (sym (lUnit _))

private
    module _ {ℓ ℓ' : Level} {A : Type ℓ} {B : Type ℓ'} (f : A → B) where
        uninhabIsEquiv : ¬ A → ¬ B → isEquiv f
        uninhabIsEquiv ¬A ¬B = isoToIsEquiv isom
            where
                open Iso
                isom : Iso A B
                isom .fun = f
                isom .inv = ⊥-elim ∘ ¬B
                isom .rightInv b = ⊥-elim {A = λ _ → f (isom .inv b) ≡ b} (¬B b)
                isom .leftInv a = ⊥-elim {A = λ _ → isom .inv (f a) ≡ a} (¬A a)

    module _ {ℓA ℓB ℓC : Level} {A : Type ℓA} {B : Type ℓB} {C : Type ℓC} (f : A → B) (g : B → C) (h : A → C) (equivf : isEquiv f) (equivh : isEquiv h) (h≡g∘f : h ≡ g ∘ f) where
        B≃C : B ≃ C
        B≃C = compEquiv (invEquiv (f , equivf)) (h , equivh)

        g' : B → C
        g' = B≃C .fst

        equivg' : isEquiv g'
        equivg' = B≃C .snd

        g'≡g : g' ≡ g
        g'≡g = funExt λ b → funExt⁻ h≡g∘f _ ∙ cong g (secIsEq equivf b)
            -- g' b
            --     ≡⟨⟩
            -- h (invIsEq equivf b)
            --     ≡⟨ funExt⁻ h≡g∘f _ ⟩
            -- g (f (invIsEq equivf b))
            --     ≡⟨ cong g (secIsEq equivf b) ⟩
            -- g b
            --     ∎
        second-in-isEquiv-comp→isEquiv : isEquiv g
        second-in-isEquiv-comp→isEquiv = transport (cong isEquiv g'≡g) equivg'

SumInl≢Inr : {ℓ ℓ' : Level} {A : Type ℓ} {B : Type ℓ'} (a : A) (b : B) → ¬ (inl a :> A ⊎ B) ≡ (inr b :> A ⊎ B)
SumInl≢Inr {A = A} {B = B} a b p = transport (cong helper p) _
    where
        helper : A ⊎ B → Type ℓ-zero
        helper (inl _) = Unit
        helper (inr _) = ⊥

module _ {ℓ ℓ' ℓ'' : Level} {X : Type ℓ} {Y : Type ℓ'} {Z : Type ℓ''} (f : X → Z) (g : Y → Z) where
    f+g : (X ⊎ Y) → Z
    f+g = ⊎-rec f g

    cong-f+g∘inl : {x x' : X} → x ≡ x' → f x ≡ f x'
    cong-f+g∘inl {x = x} {x' = x'} = cong (f+g ∘ inl)

    cong-f+g∘inr : {y y' : Y} → y ≡ y' → g y ≡ g y'
    cong-f+g∘inr {y = y} {y' = y'} = cong (f+g ∘ inr)
    
    lem27 : isEmbedding f → isEmbedding g → ((x : X) (y : Y) → ¬ f x ≡ g y) → isEmbedding f+g
    lem27 embf embg fx≢gy (inl x) (inl x') = second-in-isEquiv-comp→isEquiv (cong inl) (cong f+g) cong-f+g∘inl (isEmbedding-inl x x') (embf x x') refl
    lem27 embf embg fx≢gy (inl x) (inr y') = uninhabIsEquiv (cong f+g) (SumInl≢Inr x y') (fx≢gy x y')
    lem27 embf embg fx≢gy (inr y) (inl x') = uninhabIsEquiv (cong f+g) (λ eq → SumInl≢Inr x' y (sym eq)) λ eq → fx≢gy x' y (sym eq)
    lem27 embf embg fx≢gy (inr y) (inr y') = second-in-isEquiv-comp→isEquiv (cong inr) (cong f+g) cong-f+g∘inr (isEmbedding-inr y y') (embg y y') refl
