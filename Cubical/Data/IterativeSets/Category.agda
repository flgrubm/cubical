module Cubical.Data.IterativeSets.Category where

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude

open import Cubical.Foundations.HLevels
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Sets
open import Cubical.Foundations.Isomorphism
open import Cubical.Homotopy.Base
open import Cubical.Data.Sigma

open import Cubical.Categories.Category
open import Cubical.Categories.Limits.Initial
open import Cubical.Categories.Limits.Terminal
open import Cubical.Categories.Limits.BinCoproduct
open import Cubical.Categories.Limits.BinProduct

open import Cubical.Data.Empty
open import Cubical.Data.Unit
open import Cubical.Data.Sum renaming (rec to ⊎-rec)

open import Cubical.Data.IterativeSets.Base
open import Cubical.Data.IterativeSets.Empty
open import Cubical.Data.IterativeSets.Unit
open import Cubical.Data.IterativeSets.Sum
open import Cubical.Data.IterativeSets.Sigma

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

initial-objects-coincide : {ℓ : Level} → Functor-V-SET {ℓ} .Functor.F-ob (initial-object-V .fst) .fst ≡ ⊥* {ℓ}
initial-objects-coincide = refl

isContr→ : {ℓ ℓ' : Level} {A : Type ℓ} {B : Type ℓ'} → isContr B → isContr (A → B)
isContr→ iscontrB .fst _ = iscontrB .fst
isContr→ iscontrB .snd f = funExt (λ x → iscontrB .snd (f x))

terminal-object-V : {ℓ : Level} → Terminal (V {ℓ})
terminal-object-V {ℓ = ℓ} .fst = unit⁰ {ℓ}
terminal-object-V {ℓ = ℓ} .snd _ = isContr→ (isContrUnit* {ℓ})

terminal-objects-coincide : {ℓ : Level} → Functor-V-SET {ℓ} .Functor.F-ob (terminal-object-V .fst) .fst ≡ Unit* {ℓ}
terminal-objects-coincide = refl

binary-coproducts : {ℓ : Level} → BinCoproducts (V {ℓ})
binary-coproducts x y .BinCoproduct.binCoprodOb = x +⁰ y
binary-coproducts x y .BinCoproduct.binCoprodInj₁ = inl
binary-coproducts x y .BinCoproduct.binCoprodInj₂ = inr
binary-coproducts x y .BinCoproduct.univProp f g .fst .fst = ⊎-rec f g
binary-coproducts x y .BinCoproduct.univProp f g .fst .snd .fst = refl
binary-coproducts x y .BinCoproduct.univProp f g .fst .snd .snd = refl
binary-coproducts x y .BinCoproduct.univProp {z} f g .snd E = Σ≡Prop (λ _ → isProp× (isSet→ (thm17 z) _ f) (isSet→ (thm17 z) _ g)) (funExt helper)
    where
        helper : (a : El⁰ x ⊎ El⁰ y) → ⊎-rec f g a ≡ E .fst a
        helper (inl a) = funExt⁻ (sym (E .snd .fst)) a
        helper (inr b) = funExt⁻ (sym (E .snd .snd)) b

binary-coproducts-coincide : {ℓ : Level} {x y : V .Category.ob} → Functor-V-SET {ℓ} .Functor.F-ob (binary-coproducts x y .BinCoproduct.binCoprodOb) .fst ≡ (Functor-V-SET {ℓ} .Functor.F-ob x .fst ⊎ Functor-V-SET {ℓ} .Functor.F-ob y .fst )
binary-coproducts-coincide = refl

binary-products : {ℓ : Level} → BinProducts (V {ℓ})
binary-products x y .BinProduct.binProdOb = x ×⁰ y
binary-products x y .BinProduct.binProdPr₁ = fst
binary-products x y .BinProduct.binProdPr₂ = snd
binary-products x y .BinProduct.univProp f g .fst .fst c .fst = f c
binary-products x y .BinProduct.univProp f g .fst .fst c .snd = g c
binary-products x y .BinProduct.univProp f g .fst .snd .fst = refl
binary-products x y .BinProduct.univProp f g .fst .snd .snd = refl
binary-products x y .BinProduct.univProp {z} f g .snd E = Σ≡Prop (λ _ → isProp× (isSet→ (thm17 x) _ f) (isSet→ (thm17 y) _ g)) (funExt helper)
    where
        -- TODO: maybe rewrite since it seems like actually using both funExt and funExt⁻ is unnecessary, seeing that we don't need to pattern match on c anyway
        helper : (c : El⁰ z) → (f c , g c) ≡ E .fst c
        helper c = ≡-× (funExt⁻ (sym (E .snd .fst)) c) (funExt⁻ (sym (E .snd .snd)) c)

binary-products-coincide : {ℓ : Level} {x y : V .Category.ob} → Functor-V-SET {ℓ} .Functor.F-ob (binary-products x y .BinProduct.binProdOb) .fst ≡ (Functor-V-SET {ℓ} .Functor.F-ob x .fst × Functor-V-SET {ℓ} .Functor.F-ob y .fst )
binary-products-coincide = refl
