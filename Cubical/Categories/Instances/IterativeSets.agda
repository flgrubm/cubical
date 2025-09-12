module Cubical.Data.IterativeSets.Category where

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude

open import Cubical.Foundations.HLevels
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Sets
open import Cubical.Foundations.Isomorphism
open import Cubical.Homotopy.Base
open import Cubical.Data.Sigma
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv

open import Cubical.Categories.Category
open import Cubical.Categories.Limits.Initial
open import Cubical.Categories.Limits.Terminal
open import Cubical.Categories.Limits.BinCoproduct
open import Cubical.Categories.Limits.BinProduct
open import Cubical.Categories.Limits.Pullback

open import Cubical.Data.Empty
open import Cubical.Data.Unit
open import Cubical.Data.Sum renaming (rec to ⊎-rec)

open import Cubical.Data.IterativeSets.Base
open import Cubical.Data.IterativeSets.Empty
open import Cubical.Data.IterativeSets.Unit
open import Cubical.Data.IterativeSets.Sum
open import Cubical.Data.IterativeSets.Sigma
open import Cubical.Data.IterativeSets.Fiber
open import Cubical.Data.IterativeSets.Identity

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

binary-coproducts-V : {ℓ : Level} → BinCoproducts (V {ℓ})
binary-coproducts-V x y .BinCoproduct.binCoprodOb = x +⁰ y
binary-coproducts-V x y .BinCoproduct.binCoprodInj₁ = inl
binary-coproducts-V x y .BinCoproduct.binCoprodInj₂ = inr
binary-coproducts-V x y .BinCoproduct.univProp f g .fst .fst = ⊎-rec f g
binary-coproducts-V x y .BinCoproduct.univProp f g .fst .snd .fst = refl
binary-coproducts-V x y .BinCoproduct.univProp f g .fst .snd .snd = refl
binary-coproducts-V x y .BinCoproduct.univProp {z} f g .snd E = Σ≡Prop (λ _ → isProp× (isSet→ (thm17 z) _ f) (isSet→ (thm17 z) _ g)) (funExt helper)
    where
        helper : (a : El⁰ x ⊎ El⁰ y) → ⊎-rec f g a ≡ E .fst a
        helper (inl a) = funExt⁻ (sym (E .snd .fst)) a
        helper (inr b) = funExt⁻ (sym (E .snd .snd)) b

binary-coproducts-coincide : {ℓ : Level} {x y : V .Category.ob} → Functor-V-SET {ℓ} .Functor.F-ob (binary-coproducts-V x y .BinCoproduct.binCoprodOb) .fst ≡ (Functor-V-SET {ℓ} .Functor.F-ob x .fst ⊎ Functor-V-SET {ℓ} .Functor.F-ob y .fst )
binary-coproducts-coincide = refl

binary-products-V : {ℓ : Level} → BinProducts (V {ℓ})
binary-products-V x y .BinProduct.binProdOb = x ×⁰ y
binary-products-V x y .BinProduct.binProdPr₁ = fst
binary-products-V x y .BinProduct.binProdPr₂ = snd
binary-products-V x y .BinProduct.univProp f g .fst .fst c .fst = f c
binary-products-V x y .BinProduct.univProp f g .fst .fst c .snd = g c
binary-products-V x y .BinProduct.univProp f g .fst .snd .fst = refl
binary-products-V x y .BinProduct.univProp f g .fst .snd .snd = refl
binary-products-V x y .BinProduct.univProp {z} f g .snd E = Σ≡Prop (λ _ → isProp× (isSet→ (thm17 x) _ f) (isSet→ (thm17 y) _ g)) (funExt helper)
    where
        -- TODO: maybe rewrite since it seems like actually using both funExt and funExt⁻ is unnecessary, seeing that we don't need to pattern match on c anyway
        helper : (c : El⁰ z) → (f c , g c) ≡ E .fst c
        helper c = ≡-× (funExt⁻ (sym (E .snd .fst)) c) (funExt⁻ (sym (E .snd .snd)) c)

binary-products-coincide : {ℓ : Level} {x y : V .Category.ob} → Functor-V-SET {ℓ} .Functor.F-ob (binary-products-V x y .BinProduct.binProdOb) .fst ≡ (Functor-V-SET {ℓ} .Functor.F-ob x .fst × Functor-V-SET {ℓ} .Functor.F-ob y .fst )
binary-products-coincide = refl

-- exponentials: where in the library?

--pullbacks

private
    module _ {ℓ ℓ' : Level} {A : Type ℓ} {B : Type ℓ'} (f : A → B) (b₁ b₂ : B) where
        ≡-implies-fiber-≡ : b₁ ≡ b₂ → fiber f b₁ ≡ fiber f b₂
        ≡-implies-fiber-≡ = cong (fiber f)
    module _ {ℓ ℓ' : Level} {B : I → Type ℓ} {C : I → Type ℓ'} {x : B i0 × C i0} {y : B i1 × C i1} (P : PathP B (x .fst) (y .fst)) (Q : PathP C (x .snd) (y .snd)) where
        ×-PathP : PathP (λ i → B i × C i) x y
        ×-PathP i .fst = P i
        ×-PathP i .snd = Q i
        
pullback-V : {ℓ : Level} → Pullbacks (V {ℓ})
pullback-V (cospan l m r s₁ s₂) .Pullback.pbOb = Σ⁰ m (λ a → fiber⁰ {x = l} {y = m} s₁ a ×⁰ fiber⁰ {x = r} {y = m} s₂ a)
pullback-V (cospan l m r s₁ s₂) .Pullback.pbPr₁ = fst ∘ fst ∘ snd
pullback-V (cospan l m r s₁ s₂) .Pullback.pbPr₂ = fst ∘ snd ∘ snd
pullback-V (cospan l m r s₁ s₂) .Pullback.pbCommutes = funExt λ x → x .snd .fst .snd ∙ sym (x .snd .snd .snd)
pullback-V (cospan l m r s₁ s₂) .Pullback.univProp {d} h k H .fst .fst x .fst = s₁ (h x)
pullback-V (cospan l m r s₁ s₂) .Pullback.univProp {d} h k H .fst .fst x .snd .fst .fst = h x
pullback-V (cospan l m r s₁ s₂) .Pullback.univProp {d} h k H .fst .fst x .snd .fst .snd = refl
pullback-V (cospan l m r s₁ s₂) .Pullback.univProp {d} h k H .fst .fst x .snd .snd .fst = k x
pullback-V (cospan l m r s₁ s₂) .Pullback.univProp {d} h k H .fst .fst x .snd .snd .snd = funExt⁻ (sym H) x
pullback-V (cospan l m r s₁ s₂) .Pullback.univProp {d} h k H .fst .snd .fst = refl
pullback-V (cospan l m r s₁ s₂) .Pullback.univProp {d} h k H .fst .snd .snd = refl
pullback-V {ℓ} (cospan l m r s₁ s₂) .Pullback.univProp {d} h k H .snd E = Σ≡Prop (λ _ → isProp× (isSet→ (thm17 l) h _) (isSet→ (thm17 r) k _)) (funExt (λ x → ΣPathP (helper' x)))
    where
        helper' : (x : El⁰ d) → Σ[ p ∈ s₁ (h x) ≡ E .fst x .fst ] PathP (λ i → (fiber s₁ (p i) × fiber s₂ (p i))) ((h x , refl) , (k x , funExt⁻ (sym H) x)) (E .fst x .snd)
        helper' x .fst = cong s₁ (funExt⁻ (E .snd .fst) x) ∙ E .fst x .snd .fst .snd
        helper' x .snd = ×-PathP (ΣPathPProp (λ a → thm17 m (s₁ a) (E .fst x .fst)) (funExt⁻ (E .snd .fst) x)) (ΣPathPProp (λ a → thm17 m (s₂ a) (E .fst x .fst)) (funExt⁻ (E .snd .snd) x))
        
-- pullback-V' : {ℓ : Level} → Pullbacks (V {ℓ})
-- pullback-V' (cospan l m r s₁ s₂) .Pullback.pbOb = Σ⁰ r λ xᵣ → Σ⁰ l (λ xₗ → Id⁰ m (s₁ xₗ) (s₂ xᵣ))
-- pullback-V' (cospan l m r s₁ s₂) .Pullback.pbPr₁ = fst ∘ snd
-- pullback-V' (cospan l m r s₁ s₂) .Pullback.pbPr₂ = fst
-- pullback-V' (cospan l m r s₁ s₂) .Pullback.pbCommutes = funExt (snd ∘ snd)
-- pullback-V' (cospan l m r s₁ s₂) .Pullback.univProp {d} h k H .fst .fst x = (k x) , ((h x) , (funExt⁻ H x))
-- pullback-V' (cospan l m r s₁ s₂) .Pullback.univProp {d} h k H .fst .snd .fst = refl
-- pullback-V' (cospan l m r s₁ s₂) .Pullback.univProp {d} h k H .fst .snd .snd = refl
-- pullback-V' {ℓ} (cospan l m r s₁ s₂) .Pullback.univProp {d} h k H .snd E = Σ≡Prop (λ _ → isProp× (isSet→ (thm17 l) h _) (isSet→ (thm17 r) k _)) (funExt helper')
--     where
--         helper' : (x : El⁰ {ℓ} d) → pullback-V' {ℓ} (cospan l m r s₁ s₂) .Pullback.univProp h k H .fst .fst x ≡ E .fst x
--         helper' x = ΣPathP (funExt⁻ (E .snd .snd) x , ΣPathPProp (λ a → thm17 m (s₁ a) (s₂ (E .fst x .fst))) (funExt⁻ (E .snd .fst) x))

-- pushout 
