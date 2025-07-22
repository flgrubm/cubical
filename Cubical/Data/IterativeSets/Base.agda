-- {-# OPTIONS --safe #-}
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

private
  variable
    ℓ ℓ' ℓ'' : Level
    A A' : Type ℓ
    B B' : A → Type ℓ

V∞ : {ℓ : Level} → Type (ℓ-suc ℓ)
V∞ {ℓ} = W (Type ℓ) (λ x → x)

-- Gylterud 2020
overline-W : (x : W A B) → A
overline-W (sup-W a f) = a

tilde-W : (x : W A B) → B (overline-W x) → W A B
tilde-W (sup-W a f) = f

-- it's not really possible to use sup-∞ as a constructor, is it still helpful to have it?
sup-∞ : (A : Type ℓ) → (A → V∞) → V∞
sup-∞ = sup-W

overline-∞ : V∞ {ℓ} → Type ℓ
overline-∞ = overline-W

tilde-∞ : (A : V∞ {ℓ}) → overline-∞ A → V∞ {ℓ}
tilde-∞ = tilde-W

-- theorem 3 + 4
thm3-fun : {ℓ : Level} → {x y : V∞ {ℓ}} → x ≡ y → Σ[ e ∈ overline-∞ x ≃ overline-∞ y ] tilde-∞ x ∼ (tilde-∞ y ∘ e .fst)
thm3-fun {ℓ = ℓ} {x = x} {y = y} p = e , h where
  e = pathToEquiv (λ i → overline-∞ (p i))
  h : (z : overline-∞ x) → tilde-∞ x z ≡ (tilde-∞ y (e .fst z))
  h z i = tilde-∞ (p i) (transport-filler (cong overline-∞ p) z i)

-- helper : {A : Type ℓ} {B : Type ℓ'} {C : I → Type ℓ''} → (P : PathP (λ i → C i) A B) → (x : A) → (y : B) →

-- postulate helper : {C : I → Type ℓ} → (P Q : PathP (λ i → C i) (Type ℓ) (Type ℓ)) → P ≡ Q → (x : C i0) → transport P x ≡ transport Q x

postulate thm3-inv : {ℓ : Level} → {x y : V∞ {ℓ}} → (Σ[ e ∈ overline-∞ x ≃ overline-∞ y ] tilde-∞ x ∼ (tilde-∞ y ∘ e .fst)) → x ≡ y
-- thm3-inv {ℓ = ℓ} {x = sup-W A f} {y = sup-W B g} (e , h) i = sup-W (A→B i) (f→g i) where
--   A→B = ua e
--   f→g : (j : I) → (A→B j) → V∞
--   f→g j = {!!} -- funExtNonDep {ℓ} {ℓ-suc ℓ} {λ i → A→B i} {λ _ → V∞} {f} {g} (λ {z₀} {z₁} p → h z₀ ∙ {! !}) j

postulate thm3-rightInv : {ℓ : Level} → {x y : V∞ {ℓ}} → section (thm3-fun {ℓ} {x} {y}) (thm3-inv {ℓ} {x} {y})

postulate thm3-leftInv : {ℓ : Level} → {x y : V∞ {ℓ}} → retract (thm3-fun {ℓ} {x} {y}) (thm3-inv {ℓ} {x} {y})


thm3 : {ℓ : Level} → {x y : V∞ {ℓ}} → ((x ≡ y) ≃ (Σ[ e ∈ overline-∞ x ≃ overline-∞ y ] tilde-∞ x ∼ (tilde-∞ y ∘ e .fst)))
thm3 {ℓ = ℓ} {x = x} {y = y} = isoToEquiv (iso (thm3-fun {ℓ} {x} {y}) (thm3-inv {ℓ} {x} {y}) (thm3-rightInv {ℓ} {x} {y}) (thm3-leftInv {ℓ} {x} {y}))

-- Gylterud

-- lem4 : {ℓ : Level} → {x y : V∞ {ℓ}} → ((Σ[ e ∈ overline-∞ x ≃ overline-∞ y ] tilde-∞ x ∼ (tilde-∞ y ∘ e .fst)) ≃ ((z : V∞) → fiber (tilde-∞ x) z ≃ fiber (tilde-∞ y) z))
-- lem4 {ℓ} {x} {y} = isoToEquiv (iso to {!!} {!!} {!!})
--   where
--     to : (Σ[ e ∈ overline-∞ x ≃ overline-∞ y ] tilde-∞ x ∼ (tilde-∞ y ∘ e .fst)) → ((z : V∞) → fiber (tilde-∞ x) z ≃ fiber (tilde-∞ y) z)
--     to σ z = {!!}

-- back to Gratzer et al.

thm4-fun : {ℓ : Level} → {x y : V∞ {ℓ}} → x ≡ y → (z : V∞) → fiber (tilde-∞ x) z ≡ fiber (tilde-∞ y) z
thm4-fun {ℓ = ℓ} {x = x} {y = y} p z i = fiber (tilde-∞ (p i)) z

thm4-fun' : {ℓ : Level} → {x y : V∞ {ℓ}} → x ≡ y → (z : V∞) → fiber (tilde-∞ x) z ≃ fiber (tilde-∞ y) z
thm4-fun' {ℓ = ℓ} {x = x} {y = y} p z = pathToEquiv (λ i → fiber (tilde-∞ (p i)) z)

-- J rule

postulate thm4-inv : {ℓ : Level} → {x y : V∞ {ℓ}} → ((z : V∞) → fiber (tilde-∞ x) z ≡ fiber (tilde-∞ y) z) → x ≡ y
-- thm4-inv {ℓ = ℓ} {x = sup-W A f} {y = sup-W B g} h i = sup-W A→Bi f→gi where
--   A→Bi = {!!}
--   f→gi : A→Bi → V∞
--   f→gi = {!!}
-- plug in x or y for z???
-- equality of sigma type as equality (ΣPathP, PathPΣ or so?)

postulate thm4-rightInv : {ℓ : Level} → {x y : V∞ {ℓ}} → section (thm4-fun {ℓ} {x} {y}) (thm4-inv {ℓ} {x} {y})

postulate thm4-leftInv : {ℓ : Level} → {x y : V∞ {ℓ}} → retract (thm4-fun {ℓ} {x} {y}) (thm4-inv {ℓ} {x} {y})

thm4' : {ℓ : Level} → {x y : V∞ {ℓ}} → ((x ≡ y) ≃ ((z : V∞) → fiber (tilde-∞ x) z ≡ fiber (tilde-∞ y) z))
thm4' {ℓ = ℓ} {x = x} {y = y} = isoToEquiv (iso (thm4-fun {ℓ} {x} {y}) (thm4-inv {ℓ} {x} {y}) (thm4-rightInv {ℓ} {x} {y}) (thm4-leftInv {ℓ} {x} {y}))

thm4 : {ℓ : Level} → {x y : V∞ {ℓ}} → ((x ≡ y) ≃ ((z : V∞) → fiber (tilde-∞ x) z ≃ fiber (tilde-∞ y) z))
thm4 {ℓ = ℓ} {x = x} {y = y} = isoToEquiv (iso f finv sect retr) where
  f : x ≡ y → (z : V∞) → fiber (tilde-∞ x) z ≃ fiber (tilde-∞ y) z
  f p z = pathToEquiv (thm4-fun p z)
  finv : ((z : V∞) → fiber (tilde-∞ x) z ≃ fiber (tilde-∞ y) z) → x ≡ y
  finv h = thm4-inv λ z → ua (h z)
  postulate sect : section f  finv
  postulate retr : retract f finv

-- maybe not
-- thm4' : {x y : V∞} → ((z : V∞) → fiber (tilde-∞ x) z ≡ fiber (tilde-∞ y) z) → x ≡ y
-- thm4' {x = (sup-W A f)} {y = (sup-W B g)} h i = sup-W {!!} {! !}

_∈∞_ : V∞ {ℓ} → V∞ {ℓ} → Type (ℓ-suc ℓ)
x ∈∞ y = fiber (tilde-∞ y) x

-- examples
emptySet-∞ : V∞ {ℓ-zero}
emptySet-∞ = sup-∞ ⊥ ⊥-elim

singleton : V∞ → V∞
singleton x = sup-∞ Unit λ _ → x

unorderedPair : V∞ → V∞ → V∞
unorderedPair x y = sup-∞ Bool (λ b → if b then x else y)

-- iterative sets
isIterativeSet : V∞ {ℓ} → Type (ℓ-suc ℓ)
isIterativeSet (sup-W A f) = (isEmbedding f) × ((a : A) → isIterativeSet (f a))
-- potentially don't do pattern matching, change everywhere afterwards?

V⁰ : {ℓ : Level} → Type (ℓ-suc ℓ)
V⁰ {ℓ = ℓ} = Σ[ x ∈ V∞ {ℓ} ] isIterativeSet x

overline-0 : V⁰ {ℓ} → Type ℓ
-- overline-0 (sup-W A f , p) = A
overline-0 = overline-∞ ∘ fst

tilde-0 : (A : V⁰ {ℓ}) → overline-0 A → V∞ {ℓ}
-- tilde-0 (sup-W B f , p) = f
tilde-0 = tilde-∞ ∘ fst

isEmbedding-tilde-∞ : {ℓ : Level} → (x : V⁰ {ℓ}) → isEmbedding (tilde-0 x)
isEmbedding-tilde-∞ (sup-W A f , isitset) = isitset .fst

lem10 : {ℓ : Level} → (x : V∞ {ℓ}) → isProp (isIterativeSet x)
lem10 {ℓ = ℓ} (sup-W A f) = isProp× (isPropIsEmbedding) helper where
  helper : isProp ((a : A) → isIterativeSet (f a))
  helper g h i x = lem10 (f x) (g x) (h x) i

cor11 : {ℓ : Level} → V⁰ {ℓ} ↪ V∞ {ℓ}
cor11 {ℓ = ℓ} = EmbeddingΣProp lem10

-- maybe this is somthing for Cubical.Functions.Embedding?
embeddingToEquivOfPath : {ℓ ℓ' : Level} → {A : Type ℓ} → {B : Type ℓ'} → {f : A → B} → isEmbedding f → (x y : A) → (x ≡ y) ≃ (f x ≡ f y)
embeddingToEquivOfPath {ℓ = ℓ} {ℓ' = ℓ'} {A = A} {B = B} {f = f} isemb x y = cong f , isemb x y

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

-- sup desup

isEmbeddingΣ→isEmbeddingFst : {ℓ ℓ' ℓ'' : Level} → {A : Type ℓ} → {B : A → Type ℓ'} → {X : Type ℓ''} → (f : X → Σ[ x ∈ A ] B x) → isEmbedding f → isEmbedding (fst ∘ f)
isEmbeddingΣ→isEmbeddingFst {ℓ} {ℓ'} {ℓ''} {A} {B} {X} f isemb = hasPropFibers→isEmbedding hpf-fst∘f
  where
    hpf-f : hasPropFibers f
    hpf-f = isEmbedding→hasPropFibers isemb
    postulate hpf-fst∘f : (z : A) → isProp (fiber (fst ∘ f) z) -- hasPropFibers (fst ∘ f)
    -- hpf-fst∘f z (x , px) (y , py) i = {!!}

sup⁰ : {ℓ : Level} → (Σ[ A ∈ Type ℓ ] A ↪ V⁰ {ℓ}) → V⁰ {ℓ}
sup⁰ {ℓ} (A , f) .fst = sup-∞ A (fst ∘ (f .fst)) -- (λ z → f .fst z .fst)
sup⁰ {ℓ} (A , f) .snd .fst = isEmbeddingΣ→isEmbeddingFst (f .fst) (f .snd)
sup⁰ {ℓ} (A , f) .snd .snd = snd ∘ (f .fst) -- λ a → f .fst a .snd


postulate desup⁰ : {ℓ : Level} → V⁰ {ℓ} → (Σ[ A ∈ Type ℓ ] A ↪ V⁰ {ℓ})


-- Ch. 3

El⁰ : V⁰ {ℓ} → Type ℓ
El⁰ = overline-0

postulate embeddingIntoIsSet→isSet : {A : Type ℓ} {B : Type ℓ'} → A ↪ B → isSet B → isSet A
-- embeddingIntoIsSet→isSet {A} {B} (e , isemb) issetB = {!!}

postulate thm17 : {ℓ : Level} → (x : V⁰ {ℓ}) → isSet (El⁰ x)
-- thm17 {ℓ} x = embeddingIntoIsSet→isSet {A = El⁰ x} {B = V⁰ {ℓ}} ({!!} , {!isEmbedding-tilde-∞!}) (thm12 {ℓ})

postulate thm18 : {ℓ : Level} → {A : Type ℓ} → ((A ↪ V⁰ {ℓ}) ≃ (Σ[ a ∈ V⁰ {ℓ} ] El⁰ a ≡ A))

empty⁰ : V⁰
empty⁰ = emptySet-∞ , (λ ()) , λ ()

-- isProp-isSet→isEmbedding : {ℓ ℓ' : Level} → {A : Type ℓ} → {B : Type ℓ'} → (f : A → B) → isProp A → isSet B → isEmbedding f
-- isProp-isSet→isEmbedding {A = A} {B = B} f isp iss = {!!}

postulate functionFromIsProp→isEmbedding : {ℓ ℓ' : Level} → {A : Type ℓ} → {B : Type ℓ'} → (f : A → B) → isProp A → isEmbedding f
-- functionFromIsProp→isEmbedding f isprop = hasPropFibers→isEmbedding λ z x y i → (isprop (x .fst) (y .fst)) i , {!!} -- ((cong f (isprop (isprop (x .fst) (y .fst)) x)) ∙ (x .snd))

unit⁰ : V⁰ {ℓ-zero}
unit⁰ = singleton emptySet-∞ , isemb , isiterative
  where
    isemb : isEmbedding (λ _ → emptySet-∞)
    isemb = functionFromIsProp→isEmbedding (λ _ → emptySet-∞) isPropUnit

    isiterative : (a : Unit) → isIterativeSet emptySet-∞
    isiterative _ = empty⁰ .snd

bool⁰ : V⁰ {ℓ-zero}
bool⁰ = unorderedPair (empty⁰ .fst) (unit⁰ .fst) , isemb , isiterative
  where
    postulate isemb : isEmbedding (λ b → if b then empty⁰ .fst else unit⁰ .fst)
    -- isemb = {!!} -- idea: empty⁰ /= unit⁰

    isiterative : (b : Bool) → isIterativeSet (if b then empty⁰ .fst else unit⁰ .fst)
    isiterative false = unit⁰ .snd
    isiterative true = empty⁰ .snd

empty⁰Is⊥ : El⁰ empty⁰ ≡ ⊥
empty⁰Is⊥ = refl

unit⁰IsUnit : El⁰ unit⁰ ≡ Unit
unit⁰IsUnit = refl

bool⁰IsBool : El⁰ bool⁰ ≡ Bool
bool⁰IsBool = refl


--

suc⁰ : {ℓ : Level} → V⁰ {ℓ} → V⁰ {ℓ}
suc⁰ x = sup⁰ (overline-0 x ⊎ Unit , ϕₓ , ϕₓemb)
  where
    ϕₓ : (overline-0 x ⊎ Unit) → V⁰ {{!!}}
    ϕₓ (inl a) = (tilde-0 x a) , {!x .snd!}
    ϕₓ (fsuc a) = x

    ϕₓemb : {!!}
    ϕₓemb = {!!}
    
