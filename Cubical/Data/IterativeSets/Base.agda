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

-- why does the following not work?
--pattern sup-∞ = sup-W
-- in the meantime define like this
sup-∞ : (A : Type ℓ) → (A → V∞) → V∞
sup-∞ = sup-W

overline-∞ : V∞ {ℓ} → Type ℓ
overline-∞ = overline-W

tilde-∞ : (A : V∞ {ℓ}) → overline-∞ A → V∞ {ℓ}
tilde-∞ = tilde-W

_∈∞_ : V∞ {ℓ} → V∞ {ℓ} → Type (ℓ-suc ℓ)
x ∈∞ y = fiber (tilde-∞ y) x

postulate thm3 : {ℓ : Level} → {x y : V∞ {ℓ}} → ((x ≡ y) ≃ (Σ[ e ∈ overline-∞ x ≃ overline-∞ y ] tilde-∞ x ∼ (tilde-∞ y ∘ e .fst)))

postulate thm4 : {ℓ : Level} → {x y : V∞ {ℓ}} → ((x ≡ y) ≃ ((z : V∞) → fiber (tilde-∞ x) z ≃ fiber (tilde-∞ y) z))

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
-- isIterativeSet (sup-W A f) = Σ (isEmbedding f) (λ _ → (a : A) → isIterativeSet (f a))
-- potentially don't do pattern matching, change everywhere afterwards?

V⁰ : {ℓ : Level} → Type (ℓ-suc ℓ)
V⁰ {ℓ = ℓ} = Σ[ x ∈ V∞ {ℓ} ] isIterativeSet x

overline-0 : V⁰ {ℓ} → Type ℓ
-- overline-0 (sup-W A f , p) = A
overline-0 = overline-∞ ∘ fst

tilde-0 : (A : V⁰ {ℓ}) → overline-0 A → V∞ {ℓ}
-- tilde-0 (sup-W B f , p) = f
tilde-0 = tilde-∞ ∘ fst

-- see module T00Tilde-0
postulate tilde-0' : (A : V⁰ {ℓ}) → overline-0 A → V⁰ {ℓ}
-- tilde-0' A y = tilde-0 A y , {!A .snd .snd y!}

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

sup⁰ : {ℓ : Level} → (Σ[ A ∈ Type ℓ ] A ↪ V⁰ {ℓ}) → V⁰ {ℓ}
sup⁰ {ℓ} (A , f) .fst = sup-∞ A (compEmbedding cor11 f .fst) -- λ x → f .fst x .fst
sup⁰ {ℓ} (A , f) .snd .fst = compEmbedding cor11 f .snd
sup⁰ {ℓ} (A , f) .snd .snd y = f .fst y .snd

postulate desup⁰ : {ℓ : Level} → V⁰ {ℓ} → (Σ[ A ∈ Type ℓ ] A ↪ V⁰ {ℓ})

-- Ch. 3

El⁰ : V⁰ {ℓ} → Type ℓ
El⁰ = overline-0

postulate thm17 : {ℓ : Level} → (x : V⁰ {ℓ}) → isSet (El⁰ x)

postulate pro18 : {ℓ : Level} → {A : Type ℓ} → ((A ↪ V⁰ {ℓ}) ≃ (Σ[ a ∈ V⁰ {ℓ} ] El⁰ a ≡ A))

-- Proposition 19

empty⁰ : V⁰
empty⁰ = emptySet-∞ , (λ ()) , λ ()

empty⁰Is⊥ : El⁰ empty⁰ ≡ ⊥
empty⁰Is⊥ = refl

postulate unit⁰ : V⁰ {ℓ}
postulate unit⁰IsUnit : El⁰ unit⁰ ≡ Unit

postulate bool⁰ : V⁰ {ℓ}
postulate bool⁰IsBool : El⁰ bool⁰ ≡ Bool

-- Proposition 20
postulate ℕ⁰ : V⁰ {ℓ}
postulate ℕ⁰Isℕ : El⁰ ℕ⁰ ≡ ℕ

-- Proposition 21
postulate orderedPair : (V⁰ {ℓ} × V⁰ {ℓ}) ↪ V⁰ {ℓ}

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
