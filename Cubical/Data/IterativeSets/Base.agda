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

V∞ : {ℓ : Level} → Type (ℓ-suc ℓ)
V∞ {ℓ} = W (Type ℓ) (λ x → x)

-- Gylterud 2020
overline-W : (x : W A B) → A
overline-W (sup-W a f) = a

tilde-W : (x : W A B) → B (overline-W x) → W A B
tilde-W (sup-W a f) = f

pattern sup-∞ A f = (sup-W A f)

overline-∞ : V∞ {ℓ} → Type ℓ
overline-∞ = overline-W

tilde-∞ : (A : V∞ {ℓ}) → overline-∞ A → V∞ {ℓ}
tilde-∞ = tilde-W

_∈∞_ : V∞ {ℓ} → V∞ {ℓ} → Type (ℓ-suc ℓ)
x ∈∞ y = fiber (tilde-∞ y) x

postulate thm3 : {ℓ : Level} → {x y : V∞ {ℓ}} → ((x ≡ y) ≃ (Σ[ e ∈ overline-∞ x ≃ overline-∞ y ] tilde-∞ x ∼ (tilde-∞ y ∘ e .fst)))

postulate thm4 : {ℓ : Level} → {x y : V∞ {ℓ}} → ((x ≡ y) ≃ ((z : V∞) → fiber (tilde-∞ x) z ≃ fiber (tilde-∞ y) z))

-- examples
emptySet-∞ : V∞ {ℓ}
emptySet-∞ = sup-∞ ⊥* ⊥*-elim

singleton : V∞ {ℓ} → V∞ {ℓ}
singleton x = sup-∞ Unit* λ _ → x

unorderedPair : V∞ → V∞ → V∞
unorderedPair x y = sup-∞ Bool (λ b → if b then x else y)

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

-- TODO: rename to isEmbedding-tilde-0
isEmbedding-tilde-∞ : {ℓ : Level} → (x : V⁰ {ℓ}) → isEmbedding (tilde-0 x)
isEmbedding-tilde-∞ (sup-∞ A f , isitset) = isitset .fst

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
cor11-1 {ℓ = ℓ} {x = x} {y = y} = embeddingToEquivOfPath (cor11 .snd) x y

thm12-help1 : {ℓ : Level} → {x y : V⁰ {ℓ}} → ((x ≡ y) ≃ ((z : V∞) → fiber (tilde-∞ (x .fst)) z ≃ fiber (tilde-∞ (y .fst)) z))
thm12-help1 = compEquiv cor11-1 thm4

-- couldn't find it in the library
isPropEquiv : {ℓ ℓ' : Level} → {A : Type ℓ} → {B : Type ℓ'} → isProp A → isProp B → isProp (A ≃ B)
isPropEquiv _ pB = isPropΣ (isPropΠ (λ _ → pB)) isPropIsEquiv

thm12-help2 : {ℓ : Level} → (x y : V⁰ {ℓ}) → isProp ((z : V∞) → (z ∈∞ (x .fst)) ≃ (z ∈∞ (y .fst)))
thm12-help2 x y = isPropΠ λ z → isPropEquiv (isEmbedding→hasPropFibers (isEmbedding-tilde-∞ x) z) (isEmbedding→hasPropFibers (isEmbedding-tilde-∞ y) z)

thm12 : {ℓ : Level} → isSet (V⁰ {ℓ})
thm12 x y = isOfHLevelRespectEquiv 1 (invEquiv thm12-help1) (thm12-help2 x y)

-- if f : A → B and g : B → C are functions and g ∘ f is injective, then f is injective too
-- probably can be generalized to embeddings (potentially with assuming that g is an embedding too, but this is a WIP, see `T15DefDesup.agda`
firstInInjCompIsInj : {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''} → (f : A → B) → (g : B → C) → ((w x : A) → g (f w) ≡ g (f x) → w ≡ x) → {w x : A} → f w ≡ f x → w ≡ x
firstInInjCompIsInj f g inj∘ {w} {x} p = inj∘ w x (cong g p)

isEmbedding-tilde-0 : {ℓ : Level} → (x : V⁰ {ℓ}) → isEmbedding (tilde-0' x)
isEmbedding-tilde-0 (sup-∞ A f , isitset) = injEmbedding thm12 (firstInInjCompIsInj (tilde-0' (sup-∞ A f , isitset)) fst (isEmbedding→Inj (isEmbedding-tilde-∞ (sup-∞ A f , isitset))))

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

empty⁰Is⊥* : El⁰ {ℓ} empty⁰ ≡ ⊥* {ℓ}
empty⁰Is⊥* = refl

--

isEmbeddingFunctionFromIsPropToIsSet : {A : Type ℓ} {B : Type ℓ'} (f : A → B) → isProp A → isSet B → isEmbedding f
isEmbeddingFunctionFromIsPropToIsSet f propA setB = injEmbedding setB λ {w} {x} _ → propA w x

unit⁰ : V⁰ {ℓ}
unit⁰ {ℓ = ℓ} = sup⁰ (Unit* {ℓ} , f , isemb)
    where
        f : Unit* {ℓ} → V⁰ {ℓ}
        f _ = empty⁰
        isemb : isEmbedding f
        isemb = isEmbeddingFunctionFromIsPropToIsSet f isPropUnit* thm12

unit⁰IsUnit* : El⁰ {ℓ} unit⁰ ≡ Unit* {ℓ}
unit⁰IsUnit* = refl

-- 

⊥*≢Unit* : ((⊥* {ℓ} :> Type ℓ) ≡ (Unit* {ℓ} :> Type ℓ)) → ⊥* {ℓ}
⊥*≢Unit* p = transport (sym p) (lift tt)

Unit*≢⊥* : ((Unit* {ℓ} :> Type ℓ) ≡ (⊥* {ℓ} :> Type ℓ)) → ⊥* {ℓ}
Unit*≢⊥* p = transport p (lift tt)

empty⁰≢unit⁰ : (empty⁰ {ℓ} ≡ unit⁰ {ℓ}) → ⊥* {ℓ}
empty⁰≢unit⁰ {ℓ} p = ⊥*≢Unit* (sym empty⁰Is⊥* ∙ (cong El⁰ p) ∙ unit⁰IsUnit*)

unit⁰≢empty⁰ : (unit⁰ {ℓ} ≡ empty⁰ {ℓ}) → ⊥* {ℓ}
unit⁰≢empty⁰ {ℓ} p = Unit*≢⊥* (sym unit⁰IsUnit* ∙ (cong El⁰ p) ∙ empty⁰Is⊥*)

bool⁰ : V⁰ {ℓ}
bool⁰ {ℓ} = sup⁰ (Bool* {ℓ} , f , isemb)
    where
        f : Bool* {ℓ} → V⁰ {ℓ}
        f (lift false) = empty⁰
        f (lift true) = unit⁰

        isinj : (w x : Bool* {ℓ}) → f w ≡ f x → w ≡ x
        isinj (lift false) (lift true) p = ⊥*-elim {ℓ} {A = λ _ → (lift false) ≡ (lift true)} (empty⁰≢unit⁰ {ℓ} p)
        isinj (lift true) (lift false) p = ⊥*-elim {ℓ} {A = λ _ → (lift true) ≡ (lift false)} (unit⁰≢empty⁰ {ℓ} p)
        isinj (lift false) (lift false) p = refl
        isinj (lift true) (lift true) p = refl

        isemb : isEmbedding f
        isemb = injEmbedding thm12 λ {w} {x} → isinj w x

bool⁰IsBool : El⁰ {ℓ} bool⁰ ≡ Bool* {ℓ}
bool⁰IsBool = refl

-- Proposition 20
postulate ℕ⁰ : V⁰ {ℓ}
postulate ℕ⁰Isℕ : El⁰ ℕ⁰ ≡ ℕ

-- Proposition 21
postulate orderedPair : (V⁰ {ℓ} × V⁰ {ℓ}) ↪ V⁰ {ℓ}

⟨_,_⟩ : V⁰ {ℓ} → V⁰ {ℓ} → V⁰ {ℓ}
⟨ x , y ⟩ = orderedPair .fst (x , y)

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
