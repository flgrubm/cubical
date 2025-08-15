module Cubical.Data.IterativeSets.Base where
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
open import Cubical.Foundations.Path
open import Cubical.Functions.Fibration
open import Cubical.Functions.Embedding
open import Cubical.Data.Empty renaming (elim* to ⊥*-elim ; elim to ⊥-elim)
open import Cubical.Data.Unit
open import Cubical.Data.Bool
open import Cubical.Functions.FunExtEquiv
open import Cubical.Foundations.HLevels
open import Cubical.Data.Nat
open import Cubical.Data.SumFin

open import Cubical.Data.Sigma

open import Cubical.Homotopy.Base

open import Cubical.Data.W.W

private
  variable
    ℓ ℓ' ℓ'' : Level
    A A' : Type ℓ
    B B' : A → Type ℓ'

¬_ : Type ℓ → Type ℓ
¬ A = A → ⊥

-- probably move to Cubical.Data.W

-- due to Gylterud 2020
overline-W : (x : W A B) → A
overline-W (sup-W a _) = a

tilde-W : (x : W A B) → B (overline-W x) → W A B
tilde-W (sup-W _ f) = f
_∈W_ : {ℓ ℓ' : Level} {A : Type ℓ} {B : A → Type ℓ'} (x y : W A B) → Type (ℓ-max ℓ ℓ')
x ∈W y = fiber (tilde-W y) x

∈W-irrefl : {ℓ ℓ' : Level} {A : Type ℓ} {B : A → Type ℓ'} (x : W A B) → (x ∈W x) → ⊥
∈W-irrefl {A = A} {B = B} = WInd A B _ step
    where
        step : {s : A} {f : B s → W A B} → ((p : B s) → f p ∈W f p → ⊥) → sup-W s f ∈W sup-W s f → ⊥
        step {s = s} {f = f} ih (b , p) = ih b (transport (cong (λ r → r ∈W r) (sym p)) (b , p))

-- V∞ specific

V∞ : {ℓ : Level} → Type (ℓ-suc ℓ)
V∞ {ℓ} = W (Type ℓ) (λ x → x)


pattern sup-∞ A f = (sup-W A f)

overline-∞ : V∞ {ℓ} → Type ℓ
overline-∞ = overline-W

tilde-∞ : (A : V∞ {ℓ}) → overline-∞ A → V∞ {ℓ}
tilde-∞ = tilde-W

_∈∞_ : V∞ {ℓ} → V∞ {ℓ} → Type (ℓ-suc ℓ)
x ∈∞ y = fiber (tilde-∞ y) x

∈∞-irrefl : {ℓ : Level} (x : V∞ {ℓ}) → (x ∈∞ x) → ⊥
∈∞-irrefl = ∈W-irrefl

postulate thm3 : {ℓ : Level} → {x y : V∞ {ℓ}} → ((x ≡ y) ≃ (Σ[ e ∈ overline-∞ x ≃ overline-∞ y ] tilde-∞ x ∼ (tilde-∞ y ∘ e .fst)))

postulate thm4 : {ℓ : Level} → {x y : V∞ {ℓ}} → ((x ≡ y) ≃ ((z : V∞) → fiber (tilde-∞ x) z ≃ fiber (tilde-∞ y) z))

-- examples
emptySet-∞ : V∞ {ℓ}
emptySet-∞ = sup-∞ ⊥* ⊥*-elim

singleton-∞ : V∞ {ℓ} → V∞ {ℓ}
singleton-∞ x = sup-∞ Unit* λ _ → x

unorderedPair-∞ : V∞ → V∞ → V∞
unorderedPair-∞ x y = sup-∞ Bool (λ b → if b then x else y)

-- iterative sets
isIterativeSet : V∞ {ℓ} → Type (ℓ-suc ℓ)
isIterativeSet (sup-∞ A f) = (isEmbedding f) × ((a : A) → isIterativeSet (f a))
-- isIterativeSet (sup-W A f) = Σ (isEmbedding f) (λ _ → (a : A) → isIterativeSet (f a))
-- potentially don't do pattern matching, change everywhere afterwards?

V⁰ : {ℓ : Level} → Type (ℓ-suc ℓ)
V⁰ {ℓ = ℓ} = Σ[ x ∈ V∞ {ℓ} ] isIterativeSet x

-- For the sake of consistency, I think it should be called overline⁰, similarly tilde⁰, or maybe even ⁻⁰, ̃⁰, idk
overline-0 : V⁰ {ℓ} → Type ℓ
-- overline-0 (sup-W A f , p) = A
overline-0 = overline-∞ ∘ fst

tilde-0 : (A : V⁰ {ℓ}) → overline-0 A → V∞ {ℓ}
-- tilde-0 (sup-W B f , p) = f
tilde-0 = tilde-∞ ∘ fst

-- TODO: refactor so that everything that uses tilde-0 now uses tilde-0' instead; afterwards change name
tilde-0' : (A : V⁰ {ℓ}) → overline-0 A → V⁰ {ℓ}
tilde-0' (sup-∞ _ f , _) a .fst = f a
tilde-0' (sup-∞ _ _ , isitset) a .snd = isitset .snd a


_∈⁰_ : V⁰ {ℓ} → V⁰ {ℓ} → Type (ℓ-suc ℓ)
x ∈⁰ y = fiber (tilde-0' y) (x)

∈⁰-irrefl : {ℓ : Level} (x : V⁰ {ℓ}) → (x ∈⁰ x) → ⊥
∈⁰-irrefl (sup-∞ A f , isitset) (a , p) = ∈∞-irrefl (sup-∞ A f) (a , cong fst p)

-- TODO: rename to isEmbedding-tilde-0
isEmbedding-tilde-∞ : {ℓ : Level} → (x : V⁰ {ℓ}) → isEmbedding (tilde-0 x)
isEmbedding-tilde-∞ (sup-∞ A f , isitset) = isitset .fst

isProp∈∞ : {x : V⁰ {ℓ}} {z : V∞ {ℓ}} → isProp (z ∈∞ (x .fst))
isProp∈∞ {x = x} {z = z} = isEmbedding→hasPropFibers (isEmbedding-tilde-∞ x) z

lem10 : {ℓ : Level} → (x : V∞ {ℓ}) → isProp (isIterativeSet x)
lem10 {ℓ = ℓ} (sup-∞ A f) = isProp× (isPropIsEmbedding) helper where
  helper : isProp ((a : A) → isIterativeSet (f a))
  helper g h i x = lem10 (f x) (g x) (h x) i

cor11 : {ℓ : Level} → V⁰ {ℓ} ↪ V∞ {ℓ}
cor11 {ℓ = ℓ} = EmbeddingΣProp lem10

embeddingToEquivOfPath : {A : Type ℓ} → {B : Type ℓ'} → {f : A → B} → isEmbedding f → (x y : A) → (x ≡ y) ≃ (f x ≡ f y)
embeddingToEquivOfPath {f = f} _ _ _ .fst = cong f
embeddingToEquivOfPath isemb x y .snd = isemb x y

cor11-1 : {ℓ : Level} → {x y : V⁰ {ℓ}} → (x ≡ y) ≃ (x .fst ≡ y .fst)
cor11-1 {ℓ = ℓ} {x = x} {y = y} = invEquiv (Σ≡PropEquiv lem10)

thm12-help1 : {ℓ : Level} → {x y : V⁰ {ℓ}} → ((x ≡ y) ≃ ((z : V∞) → fiber (tilde-∞ (x .fst)) z ≃ fiber (tilde-∞ (y .fst)) z))
thm12-help1 = compEquiv cor11-1 thm4

-- couldn't find it in the library
isPropEquiv : {ℓ ℓ' : Level} → {A : Type ℓ} → {B : Type ℓ'} → isProp A → isProp B → isProp (A ≃ B)
isPropEquiv _ pB = isPropΣ (isPropΠ (λ _ → pB)) isPropIsEquiv

thm12-help2 : {ℓ : Level} → (x y : V⁰ {ℓ}) → isProp ((z : V∞) → (z ∈∞ (x .fst)) ≃ (z ∈∞ (y .fst)))
thm12-help2 x y = isPropΠ λ z → isPropEquiv (isProp∈∞ {x = x} {z = z}) (isProp∈∞ {x = y} {z = z})

thm12 : {ℓ : Level} → isSet (V⁰ {ℓ})
thm12 x y = isOfHLevelRespectEquiv 1 (invEquiv thm12-help1) (thm12-help2 x y)

-- if f : A → B and g : B → C are functions and g ∘ f is injective, then f is injective too
-- probably can be generalized to embeddings (potentially with assuming that g is an embedding too, but this is a WIP, see `T15DefDesup.agda`
firstInInjCompIsInj : {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''} → (f : A → B) → (g : B → C) → ((w x : A) → g (f w) ≡ g (f x) → w ≡ x) → {w x : A} → f w ≡ f x → w ≡ x
firstInInjCompIsInj f g inj∘ {w} {x} p = inj∘ w x (cong g p)

isEmbedding-tilde-0 : {ℓ : Level} → (x : V⁰ {ℓ}) → isEmbedding (tilde-0' x)
isEmbedding-tilde-0 (sup-∞ A f , isitset) = injEmbedding thm12 (firstInInjCompIsInj (tilde-0' (sup-∞ A f , isitset)) fst (isEmbedding→Inj (isEmbedding-tilde-∞ (sup-∞ A f , isitset))))

isProp∈⁰ : {x z : V⁰ {ℓ}} → isProp (z ∈⁰ x)
isProp∈⁰ {x = x} {z = z} = isEmbedding→hasPropFibers (isEmbedding-tilde-0 x) z

sup⁰ : {ℓ : Level} → (Σ[ A ∈ Type ℓ ] A ↪ V⁰ {ℓ}) → V⁰ {ℓ}
sup⁰ {ℓ} (A , f) .fst = sup-∞ A (compEmbedding cor11 f .fst) -- λ x → f .fst x .fst
sup⁰ {ℓ} (A , f) .snd .fst = compEmbedding cor11 f .snd
sup⁰ {ℓ} (A , f) .snd .snd y = f .fst y .snd

desup⁰ : {ℓ : Level} → V⁰ {ℓ} → (Σ[ A ∈ Type ℓ ] A ↪ V⁰ {ℓ})
desup⁰ (sup-∞ A f , isitset) .fst = A
desup⁰ (sup-∞ A f , isitset) .snd .fst x .fst = f x
desup⁰ (sup-∞ A f , isitset) .snd .fst x .snd = isitset .snd x
desup⁰ (sup-∞ A f , isitset) .snd .snd = injEmbedding thm12 (firstInInjCompIsInj _ (cor11 .fst) (isEmbedding→Inj (isEmbedding-tilde-∞ (sup-∞ A f , isitset))))

sup⁰desup⁰≃ : {ℓ : Level} → (V⁰ {ℓ} ≃ (Σ[ A ∈ Type ℓ ] A ↪ V⁰ {ℓ}))
sup⁰desup⁰≃ {ℓ = ℓ} = isoToEquiv (iso desup⁰ sup⁰ sec ret)
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

desup⁰' : {ℓ : Level} → (x : V⁰ {ℓ}) → (El⁰ x ↪ V⁰ {ℓ})
desup⁰' (sup-∞ A f , isitset) = desup⁰ (sup-∞ A f , isitset) .snd

thm17 : {ℓ : Level} → (x : V⁰ {ℓ}) → isSet (El⁰ x)
thm17 {ℓ = ℓ} (sup-∞ A f , isitset) = Embedding-into-isSet→isSet {A = El⁰ {ℓ = ℓ} (sup-∞ A f , isitset)} {B = V⁰ {ℓ}} (desup⁰' (sup-∞ A f , isitset)) (thm12 {ℓ})

postulate pro18 : {ℓ : Level} → {A : Type ℓ} → ((A ↪ V⁰ {ℓ}) ≃ (Σ[ a ∈ V⁰ {ℓ} ] El⁰ a ≡ A))

-- Proposition 19

empty⁰ : V⁰ {ℓ}
empty⁰ {ℓ = ℓ} .fst = emptySet-∞ {ℓ}
empty⁰ .snd .fst ()
empty⁰ .snd .snd ()

El⁰empty⁰Is⊥* : El⁰ {ℓ} empty⁰ ≡ ⊥* {ℓ}
El⁰empty⁰Is⊥* = refl

empty⁰-is-empty : {x : V⁰ {ℓ}} → ¬ (x ∈⁰ empty⁰)
empty⁰-is-empty (⊥-inh , _) = ⊥*-elim ⊥-inh

--

isEmbeddingFunctionFromIsPropToIsSet : {A : Type ℓ} {B : Type ℓ'} (f : A → B) → isProp A → isSet B → isEmbedding f
isEmbeddingFunctionFromIsPropToIsSet f propA setB = injEmbedding setB λ {w} {x} _ → propA w x

singleton⁰ : V⁰ {ℓ} → V⁰ {ℓ}
singleton⁰ x = sup⁰ (Unit* , (λ _ → x) , isEmbeddingFunctionFromIsPropToIsSet _ isPropUnit* thm12)

El⁰singleton⁰IsUnit* : {x : V⁰ {ℓ}} → El⁰ {ℓ} (singleton⁰ x) ≡ Unit* {ℓ}
El⁰singleton⁰IsUnit* = refl

singleton⁰-is-singleton : {x z : V⁰ {ℓ}} → ((z ∈⁰ (singleton⁰ x)) ≃ (x ≡ z))
singleton⁰-is-singleton {x = x} {z = z} = isoToEquiv (iso f g sec ret)
    where
        f : z ∈⁰ singleton⁰ x → x ≡ z
        f (_ , p) = p
        g : x ≡ z → z ∈⁰ singleton⁰ x
        g p .fst = _
        g p .snd = p
        sec : section f g
        sec _ = refl
        ret : retract f g
        ret _ = refl

unit⁰ : V⁰ {ℓ}
unit⁰ = singleton⁰ empty⁰

El⁰unit⁰IsUnit* : El⁰ {ℓ} unit⁰ ≡ Unit* {ℓ}
El⁰unit⁰IsUnit* = refl

unit⁰-is-singleton-empty⁰ : {z : V⁰ {ℓ}} → ((z ∈⁰ unit⁰) ≃ (empty⁰ ≡ z))
unit⁰-is-singleton-empty⁰ = singleton⁰-is-singleton

-- 

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

isProp-∈⁰-Equiv : {ℓ : Level} → (x y : V⁰ {ℓ}) → isProp ((z : V⁰) → (z ∈⁰ x) ≃ (z ∈⁰ y))
isProp-∈⁰-Equiv x y = isPropΠ λ z → isPropEquiv (isProp∈⁰ {x = x} {z = z}) (isProp∈⁰ {x = y} {z = z})

∈⁰≃∈∞ : {x z : V⁰ {ℓ}} → (z ∈⁰ x) ≃ (z .fst ∈∞ x .fst)
∈⁰≃∈∞ {ℓ = ℓ} {x = sup-∞ x α , itsetx} {z = sup-∞ z γ , itsetz} = propBiimpl→Equiv (isProp∈⁰ {x = sup-∞ x α , itsetx} {z = sup-∞ z γ , itsetz}) (isProp∈∞ {x = sup-∞ x α , itsetx} {z = sup-∞ z γ}) f g
    where
        f : (sup-∞ z γ , itsetz) ∈⁰ (sup-∞ x α , itsetx) → sup-∞ z γ ∈∞ sup-∞ x α
        f (a , p) .fst = a
        f (a , p) .snd = cong fst p
        g : sup-∞ z γ ∈∞ sup-∞ x α → (sup-∞ z γ , itsetz) ∈⁰ (sup-∞ x α , itsetx)
        g (a , p) .fst = a
        g (a , p) .snd = Σ≡Prop lem10 p

thm4'-helper : {ℓ : Level} {x y : V⁰ {ℓ}} → (((z : V∞ {ℓ}) → (z ∈∞ x .fst) ≃ (z ∈∞ y .fst)) ≃ ((z : V⁰ {ℓ}) → (z ∈⁰ x) ≃ (z ∈⁰ y)))
thm4'-helper {ℓ} {sup-W x α , itsetx} {sup-∞ y β , itsety} = propBiimpl→Equiv (thm12-help2 (sup-W x α , itsetx) (sup-∞ y β , itsety)) (isProp-∈⁰-Equiv (sup-W x α , itsetx) (sup-∞ y β , itsety)) f g
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

thm4' : {ℓ : Level} {x y : V⁰ {ℓ}} → ((x ≡ y) ≃ ((z : V⁰ {ℓ}) → fiber (tilde-0' x) z ≃ fiber (tilde-0' y) z))
thm4' {x = x} {y = y} = compEquiv cor11-1 (compEquiv thm4 (thm4'-helper {x = x} {y = y}))

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

-- {x , y} ≡ {y , x} where the proof q : ¬ (y ≡ x) is literally just the reversed version of p
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

⊥*≢Unit* : ((⊥* {ℓ} :> Type ℓ) ≡ (Unit* {ℓ} :> Type ℓ)) → ⊥
⊥*≢Unit* p = ⊥*-elim {A = λ _ → ⊥} (transport (sym p) (lift tt))

Unit*≢⊥* : ((Unit* {ℓ} :> Type ℓ) ≡ (⊥* {ℓ} :> Type ℓ)) → ⊥
Unit*≢⊥* p = ⊥*-elim {A = λ _ → ⊥} (transport p (lift tt))

empty⁰≢unit⁰ : (empty⁰ {ℓ} ≡ unit⁰ {ℓ}) → ⊥
empty⁰≢unit⁰ {ℓ} p = ⊥*≢Unit* (sym El⁰empty⁰Is⊥* ∙ (cong El⁰ p) ∙ El⁰unit⁰IsUnit*)

unit⁰≢empty⁰ : (unit⁰ {ℓ} ≡ empty⁰ {ℓ}) → ⊥
unit⁰≢empty⁰ {ℓ} p = Unit*≢⊥* (sym El⁰unit⁰IsUnit* ∙ (cong El⁰ p) ∙ El⁰empty⁰Is⊥*)

bool⁰ : V⁰ {ℓ}
bool⁰ {ℓ} = unorderedPair⁰ empty⁰ unit⁰ empty⁰≢unit⁰

bool⁰IsBool : El⁰ {ℓ} bool⁰ ≡ Bool* {ℓ}
bool⁰IsBool = refl

-- Proposition 20
postulate ℕ⁰ : V⁰ {ℓ}
postulate ℕ⁰Isℕ : El⁰ ℕ⁰ ≡ ℕ

-- Proposition 21

postulate orderedPair : (V⁰ {ℓ} × V⁰ {ℓ}) → V⁰ {ℓ}

⟨_,_⟩ : V⁰ {ℓ} → V⁰ {ℓ} → V⁰ {ℓ}
⟨ x , y ⟩ = orderedPair (x , y)

postulate isEmbOrderedPair' : (V⁰ {ℓ} × V⁰ {ℓ}) ↪ V⁰ {ℓ}

-- ⟨ x , y ⟩ = orderedPair .fst (x , y)

-- Proposition 22
postulate Π⁰ : (x : V⁰ {ℓ}) → (El⁰ x → V⁰ {ℓ}) → V⁰ {ℓ}
postulate Π⁰IsΠ : {x : V⁰ {ℓ}} {y : El⁰ x → V⁰ {ℓ}} → El⁰ (Π⁰ x y) ≡ ((a : El⁰ x) → El⁰ (y a))

-- Corollary 23
_→⁰_ : V⁰ {ℓ} → V⁰ {ℓ} → V⁰ {ℓ}
x →⁰ y = Π⁰ x (λ _ → y)

→⁰Is→ : {x y : V⁰ {ℓ}} → El⁰ (x →⁰ y) ≡ (El⁰ x → El⁰ y)
→⁰Is→ = Π⁰IsΠ

-- Proposition 24
postulate Σ⁰ : (x : V⁰ {ℓ}) → (El⁰ x → V⁰ {ℓ}) → V⁰ {ℓ}
postulate Σ⁰IsΣ : {x : V⁰ {ℓ}} {y : El⁰ x → V⁰ {ℓ}} → El⁰ (Σ⁰ x y) ≡ (Σ (El⁰ x) (λ a → El⁰ (y a)))

-- Corollary 25
_×⁰_ : V⁰ {ℓ} → V⁰ {ℓ} → V⁰ {ℓ}
x ×⁰ y = Σ⁰ x (λ _ → y)

×⁰Is× : {x y : V⁰ {ℓ}} → El⁰ (x ×⁰ y) ≡ ((El⁰ x) × (El⁰ y))
×⁰Is× = Σ⁰IsΣ

postulate lem26 : {X : Type ℓ} {Y : Type ℓ'} {Z : Type ℓ''} → isSet X → (x₀ : X) → (f : (X × Y) → Z) → isEmbedding f → isEmbedding (λ y → f (x₀ , y))

postulate lem27 : {X : Type ℓ} {Y : Type ℓ'} {Z : Type ℓ''} (f : X ↪ Z) → (g : Y ↪ Z) → ((x : X) (y : Y) → (f .fst x ≡ g .fst y) → ⊥) → ((X ⊎ Y) ↪ Z)
