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
open import Cubical.Functions.Fibration
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Path

-- TODO: remove ⊥*-elim, Data.Unit, Data.Bool Data.SumFin once the statements that need them have found their way to a better place
open import Cubical.Data.Empty renaming (elim* to ⊥*-elim ; elim to ⊥-elim)
open import Cubical.Data.Unit
open import Cubical.Data.Bool
open import Cubical.Data.Sum renaming (rec to ⊎-rec)

open import Cubical.Data.IterativeMultisets.Base renaming (overline to overline-∞ ; tilde to tilde-∞ ; toFib to toFib-∞)

private
  variable
    ℓ : Level

isIterativeSet : V∞ {ℓ} → Type (ℓ-suc ℓ)
isIterativeSet (sup-∞ A f) = (isEmbedding f) × ((a : A) → isIterativeSet (f a))

isPropIsIterativeSet : (x : V∞ {ℓ}) → isProp (isIterativeSet x)
isPropIsIterativeSet (sup-∞ A f) = isProp× isPropIsEmbedding helper
  where
    helper : isProp ((a : A) → isIterativeSet (f a))
    helper g h i x = isPropIsIterativeSet (f x) (g x) (h x) i

lem10 : (x : V∞ {ℓ}) → isProp (isIterativeSet x)
lem10 = isPropIsIterativeSet
{-# WARNING_ON_USAGE lem10 "Deprecated: use isPropIsIterativeSet" #-}

V⁰ : Type (ℓ-suc ℓ)
V⁰ = Σ[ x ∈ V∞ ] isIterativeSet x

private
  variable
    x y z : V⁰ {ℓ}

-- accessing the components

-- TODO: For the sake of consistency, I think it should be called overline⁰, similarly tilde⁰, or maybe even ⁻⁰, ̃⁰, idk
overline : V⁰ {ℓ} → Type ℓ
-- overline (sup-∞ A _ , _) = A
overline = overline-∞ ∘ fst

tilde-plain : (x : V⁰ {ℓ}) → overline x → V∞ {ℓ}
-- tilde (sup-∞ B f , p) = f
tilde-plain = tilde-∞ ∘ fst

-- TODO: refactor so that everything that uses tilde now uses tilde instead; afterwards change name to tilde or tilde⁰ (depending on whether the above todo is implemented)
tilde : (x : V⁰ {ℓ}) → overline x → V⁰ {ℓ}
-- the following doesn't work because seemingly `isIterativeSet` cannot be destructured
-- tilde x a .fst = tilde-∞ (x .fst) a
-- tilde x a .snd = {!x .snd .snd a!}
tilde (sup-∞ _ f , _) a .fst = f a
tilde (sup-∞ _ _ , isitset) a .snd = isitset .snd a

V⁰↪V∞ : V⁰ {ℓ} ↪ V∞ {ℓ}
V⁰↪V∞ = EmbeddingΣProp isPropIsIterativeSet

cor11 : V⁰ {ℓ} ↪ V∞ {ℓ}
cor11 = V⁰↪V∞
{-# WARNING_ON_USAGE cor11 "Deprecated: use V⁰↪V∞" #-}

-- TODO: rename
≡V⁰-≃-≡V∞ : (x ≡ y) ≃ (x .fst ≡ y .fst)
≡V⁰-≃-≡V∞ .fst = cong fst
≡V⁰-≃-≡V∞ .snd = V⁰↪V∞ .snd _ _

cor11-1 : (x ≡ y) ≃ (x .fst ≡ y .fst)
cor11-1 = ≡V⁰-≃-≡V∞
{-# WARNING_ON_USAGE cor11-1 "Deprecated: use V⁰↪V∞" #-}
-- invEquiv (Σ≡PropEquiv isPropIsIterativeSet)

_∈⁰_ : V⁰ {ℓ} → V⁰ {ℓ} → Type (ℓ-suc ℓ)
x ∈⁰ y = fiber (tilde y) (x)

∈⁰-irrefl : ¬ x ∈⁰ x
∈⁰-irrefl {x = sup-∞ A f , _} (a , p) = ∈∞-irrefl {x = sup-∞ A f} (a , cong fst p)

Iso-V⁰-Emb : Iso (V⁰ {ℓ}) (Embedding (V⁰ {ℓ}) ℓ)
Iso-V⁰-Emb {ℓ} = compIso isom Σ-assoc-Iso
  where
    isom : Iso (V⁰ {ℓ}) (Σ[ F ∈ Fibration (V⁰ {ℓ}) ℓ ] isEmbedding (F .snd))
    isom .Iso.fun (sup-∞ A f , its) .fst .fst = A
    isom .Iso.fun (sup-∞ A f , its) .fst .snd a .fst = f a
    isom .Iso.fun (sup-∞ A f , its) .fst .snd a .snd = its .snd a
    isom .Iso.fun (sup-∞ A f , its) .snd = isEmbeddingSndΣProp isPropIsIterativeSet _ (its .fst)
    isom .Iso.inv E .fst = sup-∞ (E .fst .fst) (compEmbedding V⁰↪V∞ (E .fst .snd , E .snd) .fst)
    isom .Iso.inv E .snd .fst = compEmbedding V⁰↪V∞ (E .fst .snd , E .snd) .snd
    isom .Iso.inv E .snd .snd a = E .fst .snd a .snd
    isom .Iso.rightInv E = Σ≡Prop (λ _ → isPropIsEmbedding) refl
    isom .Iso.leftInv (sup-∞ _ _ , _) = Σ≡Prop isPropIsIterativeSet refl

toEmb : V⁰ {ℓ} → Embedding (V⁰ {ℓ}) ℓ
toEmb = Iso-V⁰-Emb .Iso.fun

fromEmb : Embedding (V⁰ {ℓ}) ℓ → V⁰ {ℓ}
fromEmb = Iso-V⁰-Emb .Iso.inv

retEmb : retract (toEmb {ℓ}) (fromEmb {ℓ})
retEmb = Iso-V⁰-Emb .Iso.leftInv

-- figure out why this one computes poorly
secEmb : section (toEmb {ℓ}) (fromEmb {ℓ})
secEmb = Iso-V⁰-Emb .Iso.rightInv

V⁰≃Emb : V⁰ {ℓ} ≃ Embedding (V⁰ {ℓ}) ℓ
V⁰≃Emb = isoToEquiv Iso-V⁰-Emb

Emb≃V⁰ : Embedding (V⁰ {ℓ}) ℓ ≃ V⁰ {ℓ}
Emb≃V⁰ = isoToEquiv (invIso Iso-V⁰-Emb)

-- x ≃V⁰ y =
--    ((z : V⁰) → (z ∈⁰ x) → (z ∈⁰ y)) ×
--    ((z : V⁰) → (z ∈⁰ y) → (z ∈⁰ x))
-- (with pattern matched x and y)
_≃V⁰_ : (x y : V⁰ {ℓ}) → Type (ℓ-suc ℓ)
x ≃V⁰ y = toEmb x ≃Emb toEmb y

≃V⁰-≃-≡V⁰ : {ℓ : Level} {x y : V⁰ {ℓ}} → (x ≃V⁰ y) ≃ (x ≡ y)
≃V⁰-≃-≡V⁰ {x = x} {y = y} = compEquiv (EmbeddingIP (toEmb x) (toEmb y)) (invEquiv (cong toEmb , iso→isEmbedding Iso-V⁰-Emb x y))

≡V⁰-≃-≃V⁰ : {ℓ : Level} {x y : V⁰ {ℓ}} → (x ≡ y) ≃ (x ≃V⁰ y)
≡V⁰-≃-≃V⁰ {x = x} {y = y} = compEquiv (cong toEmb , iso→isEmbedding Iso-V⁰-Emb x y) (invEquiv (EmbeddingIP (toEmb x) (toEmb y)))

V⁰↪Fib : (V⁰ {ℓ}) ↪ Fibration (V⁰ {ℓ}) ℓ
V⁰↪Fib {ℓ} = compEmbedding Emb↪Fib (Iso→Embedding Iso-V⁰-Emb)
  where
    open EmbeddingIdentityPrinciple
    Emb↪Fib : Embedding (V⁰ {ℓ}) ℓ ↪ Fibration (V⁰ {ℓ}) ℓ
    Emb↪Fib .fst = toFibr
    Emb↪Fib .snd = isEmbeddingToFibr

toFib : (V⁰ {ℓ}) → Fibration (V⁰ {ℓ}) ℓ
toFib = V⁰↪Fib .fst
    
-- x ≃V⁰' y =
--    ((z : V⁰) → (z ∈⁰ x) → (z ∈⁰ y)) ≃
--    ((z : V⁰) → (z ∈⁰ y) → (z ∈⁰ x))
-- (with pattern matched x and y)
_≃V⁰'_ : (x y : V⁰ {ℓ}) → Type (ℓ-suc ℓ)
x ≃V⁰' y = toFib x ≃Fib toFib y

≃V⁰'-≃-≡V⁰ : {ℓ : Level} {x y : V⁰ {ℓ}} → (x ≃V⁰' y) ≃ (x ≡ y)
≃V⁰'-≃-≡V⁰ {x = x} {y = y} = compEquiv (FibrationIP (toFib x) (toFib y)) (invEquiv (cong toFib , V⁰↪Fib .snd x y))

≡V⁰-≃-≃V⁰' : {ℓ : Level} {x y : V⁰ {ℓ}} → (x ≡ y) ≃ (x ≃V⁰' y)
≡V⁰-≃-≃V⁰' {x = x} {y = y} = compEquiv (cong toFib , V⁰↪Fib .snd x y) (invEquiv (FibrationIP (toFib x) (toFib y)))

isSetV⁰ : isSet (V⁰ {ℓ})
isSetV⁰ = isOfHLevelRespectEquiv 2 Emb≃V⁰ isSetEmbedding

-- TODO: rename to isEmbedding-tilde-plain
isEmbedding-tilde-∞ : (x : V⁰ {ℓ}) → isEmbedding (tilde-plain x)
isEmbedding-tilde-∞ (sup-∞ A f , isitset) = isitset .fst

isProp∈∞ : {z : V∞ {ℓ}} → isProp (z ∈∞ (x .fst))
isProp∈∞ {x = x} {z = z} = isEmbedding→hasPropFibers (isEmbedding-tilde-∞ x) z

-- TODO: move to better place
embeddingToEquivOfPath : {ℓ ℓ' : Level} {A : Type ℓ} → {B : Type ℓ'} → {f : A → B} → isEmbedding f → (x y : A) → (x ≡ y) ≃ (f x ≡ f y)
embeddingToEquivOfPath {f = f} _ _ _ .fst = cong f
embeddingToEquivOfPath isemb x y .snd = isemb x y

thm12-help1 : ((x ≡ y) ≃ ((z : V∞) → fiber (tilde-∞ (x .fst)) z ≃ fiber (tilde-∞ (y .fst)) z))
thm12-help1 = compEquiv ≡V⁰-≃-≡V∞ thm4

-- couldn't find it in the library
isPropEquiv : {ℓ ℓ' : Level} → {A : Type ℓ} → {B : Type ℓ'} → isProp A → isProp B → isProp (A ≃ B)
isPropEquiv _ pB = isPropΣ (isPropΠ (λ _ → pB)) isPropIsEquiv
{-# WARNING_ON_USAGE isPropEquiv "" #-}

thm12-help2 : (x y : V⁰ {ℓ}) → isProp ((z : V∞) → (z ∈∞ (x .fst)) ≃ (z ∈∞ (y .fst)))
thm12-help2 x y = isPropΠ λ z → isOfHLevel≃ 1 (isProp∈∞ {x = x} {z = z}) (isProp∈∞ {x = y} {z = z})

thm12 : isSet (V⁰ {ℓ})
thm12 = isSetV⁰ -- isOfHLevelRespectEquiv 1 (invEquiv thm12-help1) (thm12-help2 x y)
{-# WARNING_ON_USAGE thm12 "Deprecated: use isSetV⁰" #-}

-- if f : A → B and g : B → C are functions and g ∘ f is injective, then f is injective too
-- probably can be generalized to embeddings (potentially with assuming that g is an embedding too, but this is a WIP, see `T15DefDesup.agda`
firstInInjCompIsInj : {ℓ ℓ' ℓ'' : Level} {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''} → (f : A → B) → (g : B → C) → ((w x : A) → g (f w) ≡ g (f x) → w ≡ x) → {w x : A} → f w ≡ f x → w ≡ x
firstInInjCompIsInj f g inj∘ {w} {x} p = inj∘ w x (cong g p)

isEmbedding-tilde : (x : V⁰ {ℓ}) → isEmbedding (tilde x)
isEmbedding-tilde (sup-∞ A f , isitset) = isEmbeddingSndΣProp isPropIsIterativeSet _ (isitset .fst)

-- TODO: figure out why removing {x z : V⁰ {ℓ}} doesn't work (complains about z)...
isProp∈⁰ : {x z : V⁰ {ℓ}} → isProp (z ∈⁰ x)
isProp∈⁰ {x = x} {z = z} = isEmbedding→hasPropFibers (isEmbedding-tilde x) z

sup⁰ : (Σ[ A ∈ Type ℓ ] A ↪ V⁰ {ℓ}) → V⁰ {ℓ}
sup⁰ = fromEmb
-- sup⁰ (A , f) .fst = sup-∞ A (compEmbedding cor11 f .fst) -- λ x → f .fst x .fst
-- sup⁰ (A , f) .snd .fst = compEmbedding cor11 f .snd
-- sup⁰ (A , f) .snd .snd y = f .fst y .snd
-- sup⁰ s .fst = sup-∞ (s .fst) (compEmbedding cor11 (s .snd) .fst) -- λ x → f .fst x .fst
-- sup⁰ s .snd .fst = compEmbedding cor11 (s .snd) .snd
-- sup⁰ s .snd .snd y = s .snd .fst y .snd

desup⁰ : V⁰ {ℓ} → (Σ[ A ∈ Type ℓ ] A ↪ V⁰ {ℓ})
desup⁰ = toEmb
-- desup⁰ (sup-∞ A f , isitset) .fst = A
-- desup⁰ (sup-∞ A f , isitset) .snd .fst x .fst = f x
-- desup⁰ (sup-∞ A f , isitset) .snd .fst x .snd = isitset .snd x
-- desup⁰ (sup-∞ A f , isitset) .snd .snd = injEmbedding isSetV⁰ (firstInInjCompIsInj _ (cor11 .fst) (isEmbedding→Inj (isEmbedding-tilde-∞ (sup-∞ A f , isitset))))

sup⁰desup⁰≃ : (V⁰ {ℓ} ≃ (Σ[ A ∈ Type ℓ ] A ↪ V⁰ {ℓ}))
sup⁰desup⁰≃ = V⁰≃Emb
    -- isoToEquiv (iso desup⁰ sup⁰ sec ret)
    -- where
    --     sec : section (desup⁰ {ℓ}) (sup⁰ {ℓ})
    --     sec (A , (f , embf)) = cong (λ e → (A , (f , e))) (isPropIsEmbedding {f = f} _ embf)

    --     ret : retract (desup⁰ {ℓ}) (sup⁰ {ℓ}) 
    --     ret (sup-∞ A f , isitset) = cong fun (isPropIsIterativeSet (sup-∞ A f) _ isitset)
    --         where
    --             fun : isIterativeSet (sup-∞ A f) → V⁰ {ℓ}
    --             fun _ .fst = sup-∞ A f
    --             fun it .snd = it

-- Ch. 3

El⁰ : V⁰ {ℓ} → Type ℓ
El⁰ = overline

desup⁰' : (x : V⁰ {ℓ}) → (El⁰ x ↪ V⁰ {ℓ})
desup⁰' (sup-∞ A f , its) = desup⁰ (sup-∞ A f , its) .snd

thm17 : (x : V⁰ {ℓ}) → isSet (El⁰ x)
thm17 {ℓ} x = Embedding-into-isSet→isSet {A = El⁰ {ℓ} x} {B = V⁰ {ℓ}} (desup⁰' x) (isSetV⁰ {ℓ})

postulate pro18 : {A : Type ℓ} → ((A ↪ V⁰ {ℓ}) ≃ (Σ[ a ∈ V⁰ {ℓ} ] El⁰ a ≡ A))

-- pro18' : {A : Type ℓ} → Iso (A ↪ V⁰ {ℓ}) (fiber (El⁰ {ℓ}) A)
-- pro18' {A = A} .Iso.fun emb .fst = fromEmb (record {fst = A ; snd = emb})
-- pro18' .Iso.fun emb .snd = refl
-- pro18' {A = A} .Iso.inv fib = subst (λ s → s ↪ V⁰) (fib .snd) (toEmb (fib .fst) .snd)
-- -- (J> toEmb (fib .fst) .snd) A (fib .snd)
-- pro18' {A = A} .Iso.rightInv fib = {!!}
-- pro18' {ℓ = ℓ} {A = A} .Iso.leftInv emb = ΣPathP ((cong fst (substRefl (A , emb)) ∙ cong fst ({!secEmb!})) , {!!})
    -- Iso.inv pro18' (Iso.fun pro18' emb)
    --     ≡⟨⟩
    -- Iso.inv pro18' (fromEmb (record {fst = A ; snd = emb}) , refl)
    --     ≡⟨⟩
    -- subst (λ s → s ↪ V⁰) refl (toEmb (fromEmb (A , emb)) .snd)
    --     ≡⟨ substRefl (toEmb (fromEmb (record {fst = A ; snd = emb})) .snd) ⟩
    -- snd (toEmb (fromEmb (record {fst = A ; snd = emb})))
    --     ≡⟨ cong {A = Embedding (V⁰ {ℓ}) ℓ} snd {!secEmb!} ⟩
    -- record {fst = A ; snd = emb} .snd
    --     ≡⟨⟩
    -- emb
    --     ∎

-- move this to some other place in the library
isEmbeddingFunctionFromIsPropToIsSet : {ℓ ℓ' : Level} {A : Type ℓ} {B : Type ℓ'} (f : A → B) → isProp A → isSet B → isEmbedding f
isEmbeddingFunctionFromIsPropToIsSet f propA setB = injEmbedding setB λ {w} {x} _ → propA w x

isProp-∈⁰-Equiv : (x y : V⁰ {ℓ}) → isProp ((z : V⁰) → (z ∈⁰ x) ≃ (z ∈⁰ y))
isProp-∈⁰-Equiv x y = isPropΠ λ z → isOfHLevel≃ 1 (isProp∈⁰ {x = x} {z = z}) (isProp∈⁰ {x = y} {z = z})

∈⁰≃∈∞ : {x z : V⁰ {ℓ}} → (z ∈⁰ x) ≃ (z .fst ∈∞ x .fst)
∈⁰≃∈∞ {x = sup-∞ x α , itsetx} {z = sup-∞ z γ , itsetz} = propBiimpl→Equiv (isProp∈⁰ {x = sup-∞ x α , itsetx} {z = sup-∞ z γ , itsetz}) (isProp∈∞ {x = sup-∞ x α , itsetx} {z = sup-∞ z γ}) f g
    where
        f : (sup-∞ z γ , itsetz) ∈⁰ (sup-∞ x α , itsetx) → sup-∞ z γ ∈∞ sup-∞ x α
        f (a , p) .fst = a
        f (a , p) .snd = cong fst p
        g : sup-∞ z γ ∈∞ sup-∞ x α → (sup-∞ z γ , itsetz) ∈⁰ (sup-∞ x α , itsetx)
        g (a , p) .fst = a
        g (a , p) .snd = Σ≡Prop isPropIsIterativeSet p

thm4⁰-helper : {x y : V⁰ {ℓ}} → (((z : V∞ {ℓ}) → (z ∈∞ x .fst) ≃ (z ∈∞ y .fst)) ≃ ((z : V⁰ {ℓ}) → (z ∈⁰ x) ≃ (z ∈⁰ y)))
thm4⁰-helper {x = sup-∞ x α , itsetx} {y = sup-∞ y β , itsety} = propBiimpl→Equiv (thm12-help2 (sup-∞ x α , itsetx) (sup-∞ y β , itsety)) (isProp-∈⁰-Equiv (sup-∞ x α , itsetx) (sup-∞ y β , itsety)) f g
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

thm4⁰ : (x ≡ y) ≃ ((z : V⁰ {ℓ}) → (z ∈⁰ x) ≃ (z ∈⁰ y))
thm4⁰ {x = sup-∞ _ _ , _} {y = sup-∞ _ _ , _} = ≡V⁰-≃-≃V⁰'

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
