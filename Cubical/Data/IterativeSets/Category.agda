module Cubical.Data.IterativeSets.Category where

open import Cubical.Foundations.Prelude
open import Cubical.Data.IterativeSets.Base
open import Cubical.Categories.Category
open import Cubical.Foundations.HLevels
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Sets
open import Cubical.Foundations.Isomorphism
open import Cubical.Categories.Limits.Initial
open import Cubical.Categories.Limits.Terminal
open import Cubical.Homotopy.Base
open import Cubical.Data.Unit

V : {ℓ : Level} → Category (ℓ-suc ℓ) ℓ
V {ℓ} .Category.ob = V⁰ {ℓ}
V .Category.Hom[_,_] x y = El⁰ x → El⁰ y
V .Category.id x = x
V .Category._⋆_ f g x = g (f x)
V .Category.⋆IdL _ = refl
V .Category.⋆IdR _ = refl
V .Category.⋆Assoc f g h = refl
V .Category.isSetHom {x = x} {y = y} = isSet→ (thm17 y)

Functor-V-SET : {ℓ : Level} → Functor (V {ℓ}) (SET ℓ)
Functor-V-SET {ℓ = ℓ} .Functor.F-ob x .fst = El⁰ x
Functor-V-SET {ℓ = ℓ} .Functor.F-ob x .snd = thm17 x
Functor-V-SET {ℓ = ℓ} .Functor.F-hom f = f
Functor-V-SET {ℓ = ℓ} .Functor.F-id = refl
Functor-V-SET {ℓ = ℓ} .Functor.F-seq g f = refl

isFullyFaithful-Functor-V-SET : {ℓ : Level} → Functor.isFullyFaithful (Functor-V-SET {ℓ})
isFullyFaithful-Functor-V-SET {ℓ = ℓ} x y = isoToIsEquiv (iso _ (λ f → f) (λ x → refl) λ x → refl)

initial-object-V : {ℓ : Level} → Initial (V {ℓ})
initial-object-V {ℓ = ℓ} .fst = empty⁰ {ℓ}
initial-object-V .snd _ .fst ()
initial-object-V .snd _ .snd f = funExt∼ λ ()

isContr→ : {ℓ ℓ' : Level} {A : Type ℓ} {B : Type ℓ'} → isContr B → isContr (A → B)
isContr→ iscontrB .fst _ = iscontrB .fst
isContr→ iscontrB .snd f = funExt (λ x → iscontrB .snd (f x))

terminal-object-V : {ℓ : Level} → Terminal (V {ℓ})
terminal-object-V {ℓ = ℓ} .fst = unit⁰ {ℓ}
terminal-object-V {ℓ = ℓ} .snd _ = isContr→ (isContrUnit* {ℓ})
