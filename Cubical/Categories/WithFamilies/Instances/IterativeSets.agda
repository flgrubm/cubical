module Cubical.Categories.WithFamilies.Instances.IterativeSets where

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude

open import Cubical.Categories.WithFamilies.Base
open import Cubical.Categories.Functor.Base
open import Cubical.Foundations.HLevels
open import Cubical.Categories.Category.Base
open import Cubical.Categories.Instances.Sets
open import Cubical.Foundations.Function
open import Cubical.Categories.Constructions.Elements
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Transport
open import Cubical.Data.Sigma
open import Cubical.Functions.FunExtEquiv
open import Cubical.Foundations.HLevels


open import Cubical.Data.IterativeSets.Base
open import Cubical.Data.IterativeSets.Pi
open import Cubical.Data.IterativeSets.Sigma
open import Cubical.Categories.Instances.IterativeSets

open import Cubical.Categories.Presheaf
open import Cubical.Categories.Functor

import Cubical.Categories.Constructions.Elements as Els -- renaming (Covariant.∫ to ∫)
open Els.Contravariant

open Category
open CwF
open Functor


private
  module _ where
    isSetPathP : {ℓ : Level} {A : I → Type ℓ} → isSet (A i1) → (x : A i0) (y : A i1) → isSet (PathP A x y)
    isSetPathP = isOfHLevelPathP 2

    cong∙ : {ℓ ℓ' : Level} {A : Type ℓ} (f : A → Type ℓ') {x y z : A} {p : x ≡ y} {q : y ≡ z} → cong f (p ∙ q) ≡ cong f p ∙ cong f q
    cong∙ f {p} {q} = {!!}
    
    tt : {ℓ : Level} {A B : Type ℓ} (p q : A ≡ B) (p≡q : p ≡ q) (x : A) → transport p x ≡ transport q x
    tt _ _ p≡q x = cong (λ r → transport r x) p≡q

    ttSet : {ℓ : Level} {A B : Type ℓ} → isSet A → isSet B → isSet (A ≡ B)
    ttSet = isOfHLevel≡ 2

V-CwF : {ℓ : Level} → CwF (V {ℓ}) (ℓ-suc ℓ) (ℓ-suc ℓ)

V-CwF .emptyContext = terminal-object-V

V-CwF .tyPresheaf .F-ob Γ .fst = El⁰ Γ → V⁰
V-CwF .tyPresheaf .F-ob _ .snd = isSet→ thm12
V-CwF .tyPresheaf .F-hom f g x = g (f x)
V-CwF .tyPresheaf .F-id = refl
V-CwF .tyPresheaf .F-seq _ _ = refl

-- use PathP more!
-- use isSet
V-CwF .tmPresheaf .F-ob X .fst = Lift ((x : El⁰ (X .fst)) → El⁰ (X .snd x))
V-CwF .tmPresheaf .F-ob X .snd = isOfHLevelLift 2 (isSetΠ (λ x → thm17 (X .snd x)))
V-CwF .tmPresheaf .F-hom f t = lift (λ x → transport (cong El⁰ (funExt⁻ (f .snd) x)) (t .lower (f .fst x)))
V-CwF .tmPresheaf .F-id = funExt (λ _ → cong lift (funExt (λ _ → transportRefl _)))
V-CwF .tmPresheaf .F-seq f g = {!!} -- funExt (λ x → cong lift (funExt (λ y → transportComposite (λ i → El⁰ (funExt⁻ q (σ y) i)) {!λ i → El⁰ (funExt⁻ p (σ y) i)!} {!!})))
-- transport
--       (λ i →
--          El⁰
--          (funExt⁻
--           (seq' (Contravariant.∫ᴾ V-CwF .tyPresheaf) (σ , q) (γ , p) .snd) y
--           i))
--       (x .lower
--        (seq' (Contravariant.∫ᴾ V-CwF .tyPresheaf) (σ , q) (γ , p) .fst y))
--       ≡
--       transport (λ i → El⁰ (funExt⁻ q y i))
--       (transport (λ i → El⁰ (funExt⁻ p (σ y) i)) (x .lower (γ (σ y))))
-- J2 {!!} {!!} q p -- σ : El⁰ Ε → El⁰ Δ, γ : El⁰ Δ → El⁰ Γ

V-CwF .ctxExtFunctor .F-ob X = Σ⁰ (X .fst) (X .snd)
V-CwF .ctxExtFunctor .F-hom {x} {y} f t .fst = f .fst (t .fst)
V-CwF .ctxExtFunctor .F-hom {x} {y} f t .snd = subst⁻ El⁰ (funExt⁻ (f .snd) (t .fst)) (t .snd)
V-CwF .ctxExtFunctor .F-id = funExt (λ x → ΣPathP (refl , (transportRefl (x .snd))))
V-CwF .ctxExtFunctor .F-seq {x} {y} {z} f g = funExt (λ t → ΣPathP (refl ,
    let 
        C = ∫ᴾ V-CwF .tyPresheaf

        p : Path V⁰ (x .snd (t .fst)) (z .snd (g .fst (f .fst (t .fst))))
        p i = seq' C {x} {y} {z} f g .snd (~ i) (t .fst)

        q : Path V⁰ (y .snd (f .fst (t .fst))) (z .snd (g .fst (f .fst (t .fst))))
        q i = g .snd (~ i) (f .fst (t .fst))

        r : Path V⁰ (x .snd (t .fst)) (y .snd (f .fst (t .fst)))
        r i = f .snd (~ i) (t .fst)

        p≡r∙q : p ≡ r ∙ q
        p≡r∙q = thm12 _ _ p (r ∙ q)

        goal : subst El⁰ p (t .snd) ≡ subst El⁰ q (subst El⁰ r (t .snd))
        goal = cong (λ a → subst El⁰ a (t .snd)) p≡r∙q ∙ substComposite El⁰ r q (t .snd)
    in goal))

--  funExt (λ t → ΣPathP (refl ,  {- cong {x = (funExt⁻ (((∫ᴾ V-CwF .tyPresheaf) ⋆ f) g .snd) (t .fst))} {y = {!!}} (λ p → subst⁻ El⁰ p (t .snd)) {!!}-} congP (λ p → {!transport p (t .snd)!}) {!!} ∙ transportComposite (cong El⁰ (funExt⁻ (sym (f .snd)) (t .fst))) (cong El⁰ (funExt⁻ (sym (g .snd)) (f .fst (t .fst)))) (t .snd)))
-- funExt (λ t → ΣPathP (refl , (
    -- (V-CwF .ctxExtFunctor .F-hom (f ⋆⟨ ∫ᴾ V-CwF .tyPresheaf ⟩ g) t) .snd
    --     ≡⟨⟩
    -- transport {!!} {!x .snd!}
    --     ≡⟨ {!!} ⟩
    -- {!!}
    --     ∎)))
-- this one works somewhat: -- cong (λ r → transport (cong El⁰ r) (t .snd)) (thm12 (x .snd (t .fst)) (z .snd (g (f (t .fst)))) (funExt⁻ (sym (((f , p) ⋆⟨ ∫ᴾ V-CwF .tyPresheaf ⟩ (g , q)) .snd)) (t .fst)) (funExt⁻ (sym p) (t .fst) ∙ funExt⁻ (sym q) (f (t .fst)))) ∙ cong (λ r → transport r (t .snd)) (cong∙ El⁰) ∙ transportComposite (cong El⁰ (funExt⁻ (sym p) (t .fst))) (cong El⁰ (funExt⁻ (sym q) (f (t .fst)))) (t .snd)))
-- tt {!!} {!!} {!!} a ∙ transportComposite (cong El⁰ (funExt⁻ (sym p) t)) (cong El⁰ (funExt⁻ (sym q) (f t))) a))
    -- where
    --     pathsEqual : (t : Σ[ a ∈ El⁰ (x .fst) ] El⁰ (x .snd a)) → funExt⁻ (sym (((f , p) ⋆⟨ ∫ᴾ V-CwF .tyPresheaf ⟩ (g , q)) .snd)) (t .fst) ≡ funExt⁻ (sym p) (t .fst) ∙ funExt⁻ (sym q) (f (t .fst))
    --     pathsEqual t = thm12 (x .snd (t .fst)) (z .snd (g (f (t .fst)))) (funExt⁻ (sym (((f , p) ⋆⟨ ∫ᴾ V-CwF .tyPresheaf ⟩ (g , q)) .snd)) (t .fst)) (funExt⁻ (sym p) (t .fst) ∙ funExt⁻ (sym q) (f (t .fst)))
        
    --     ll : (t : Σ[ a ∈ El⁰ (x .fst) ] El⁰ (x .snd a)) → transport (cong El⁰ (funExt⁻ (sym (((f , p) ⋆⟨ ∫ᴾ V-CwF .tyPresheaf ⟩ (g , q)) .snd)) (t .fst))) (t .snd) ≡ transport (cong El⁰ (funExt⁻ (sym p) (t .fst) ∙ funExt⁻ (sym q) (f (t .fst)))) (t .snd)
    --     ll t = cong (λ r → transport (cong El⁰ r) (t .snd)) (pathsEqual t)

    --     mm : (t : Σ[ a ∈ El⁰ (x .fst) ] El⁰ (x .snd a)) → transport (cong El⁰ (funExt⁻ (sym p) (t .fst) ∙ funExt⁻ (sym q) (f (t .fst)))) (t .snd) ≡ transport (cong El⁰ (funExt⁻ (sym p) (t .fst)) ∙ cong El⁰ (funExt⁻ (sym q) (f (t .fst)))) (t .snd)
    --     mm t = cong (λ r → transport r (t .snd)) (cong∙ El⁰)
        
    --     rr : (t : Σ[ a ∈ El⁰ (x .fst)] El⁰ (x .snd a)) → transport (cong El⁰ (funExt⁻ (sym p) (t .fst)) ∙ (cong El⁰ (funExt⁻ (sym q) (f (t .fst))))) (t .snd) ≡ transport (cong El⁰ (funExt⁻ (sym q) (f (t .fst)))) (transport (cong El⁰ (funExt⁻ (sym p) (t .fst))) (t .snd))
    --     rr t = transportComposite (cong El⁰ (funExt⁻ (sym p) (t .fst))) (cong El⁰ (funExt⁻ (sym q) (f (t .fst)))) (t .snd)

    --     hh : (t : Σ[ a ∈ El⁰ (x .fst) ] El⁰ (x .snd a)) → transport (cong El⁰ (funExt⁻ (((f , p) ⋆⟨ ∫ᴾ V-CwF .tyPresheaf ⟩ (g , q)) .snd) (t .fst))) (t .snd) ≡ transport (cong El⁰ {!funExt⁻ (sym q) (f (t .fst))!}) (transport (cong El⁰ (funExt⁻ (sym p) (t .fst))) (t .snd))
    --     -- hh : (t
    --     hh t = {!? ∙ (rr t)!}
        -- attempt at avoiding pattern matching
        -- rnr : (t : Σ[ a ∈ El⁰ (x .fst) ] El⁰ (x .snd a)) → funExt⁻ (sym ((f ⋆⟨ ∫ᴾ V-CwF .tyPresheaf ⟩ g) .snd)) (t .fst) ≡ funExt⁻ (sym (f .snd)) (t .fst) ∙ funExt⁻ (sym q) (f (t .fst))
        -- rnr t = thm12 (x .snd (t .fst)) (z .snd (g (f (t .fst)))) (funExt⁻ (sym ((f ⋆⟨ ∫ᴾ V-CwF .tyPresheaf ⟩ (g , q)) .snd)) (t .fst)) (funExt⁻ (sym (f .snd)) (t .fst) ∙ funExt⁻ (sym q) (f (t .fst)))
        
        -- ne : (t : Σ[ a ∈ El⁰ (x .fst) ] El⁰ (x .snd a)) → transport (cong El⁰ (funExt⁻ (sym ((f ⋆⟨ ∫ᴾ V-CwF .tyPresheaf ⟩ (g , q)) .snd)) (t .fst))) (t .snd) ≡ transport (cong El⁰ (funExt⁻ (sym (f .snd)) (t .fst) ∙ funExt⁻ (sym q) (f (t .fst)))) (t .snd)
        -- ne t = cong (λ r → transport (cong El⁰ r) (t .snd)) (rnr t)

        -- mi : (t : Σ[ a ∈ El⁰ (x .fst) ] El⁰ (x .snd a)) → transport (cong El⁰ (funExt⁻ (sym (f .snd)) (t .fst) ∙ funExt⁻ (sym q) (f (t .fst)))) (t .snd) ≡ transport (cong El⁰ (funExt⁻ (sym (f .snd)) (t .fst)) ∙ cong El⁰ (funExt⁻ (sym q) (f (t .fst)))) (t .snd)
        -- mi t = cong (λ r → transport r (t .snd)) (cong∙ El⁰)
        
        -- rr : (t : Σ[ a ∈ El⁰ (x .fst)] El⁰ (x .snd a)) → transport (cong El⁰ (funExt⁻ (sym (f .snd)) (t .fst)) ∙ (cong El⁰ (funExt⁻ (sym q) (f (t .fst))))) (t .snd) ≡ transport (cong El⁰ (funExt⁻ (sym q) (f (t .fst)))) (transport (cong El⁰ (funExt⁻ (sym (f .snd)) (t .fst))) (t .snd))
        -- rr t = transportComposite (cong El⁰ (funExt⁻ (sym (f .snd)) (t .fst))) (cong El⁰ (funExt⁻ (sym q) (f (t .fst)))) (t .snd)

        -- hh : (t : Σ[ a ∈ El⁰ (x .fst) ] El⁰ (x .snd a)) → transport (cong El⁰ (funExt⁻ ((f ⋆⟨ ∫ᴾ V-CwF .tyPresheaf ⟩ (g , q)) .snd) (t .fst))) (t .snd) ≡ transport (cong El⁰ {!funExt⁻ (sym q) (f (t .fst))!}) (transport (cong El⁰ (funExt⁻ (sym (f .snd)) (t .fst))) (t .snd))
        -- -- hh : (t
        -- hh t = {!? ∙ (rr t)!}
        -- just in case
-- tt {!!} {!!} {!!} {!!}  ∙ (transportComposite (cong El⁰ (funExt⁻ (sym p) t)) (cong El⁰ (funExt⁻ (sym q) (f t))) a)))-- it's not equlities, but the transports are with paths that are equal
 

        -- ttt : (V-CwF .ctxExtFunctor .F-hom (((∫ᴾ V-CwF .tyPresheaf) ⋆ (f , p)) (g , q₁)) .patternInTele0) ≡ transport ((λ i → El⁰ (funExt⁻ (λ i₁ → p (~ i₁)) (.patternInTele0 .fst) i)) ∙ (λ i → El⁰ (funExt⁻ (λ i₁ → q₁ (~ i₁)) (f (.patternInTele0 .fst)) i))) (.patternInTele0 .snd)
        -- ttt = ?
--
-- funExt (λ x → {!V-CwF .ctxExtFunctor .F-hom (((∫ᴾ V-CwF .tyPresheaf) Category.⋆ (f , p)) (g , q)) x !})
-- {!V-CwF .ctxExtFunctor .F-hom (g , q) (V-CwF .ctxExtFunctor .F-hom (f , p) x) !}) -- Σ≡Prop (λ y → {!thm17 (C y)!}) refl)
--  ΣPathP (refl , cong (λ p → transport p a) (tmp x) ∙ (transportComposite (cong El⁰ (funExt⁻ (sym p) x)) (cong El⁰ (funExt⁻ (sym q) (f x))) a)))
-- transportComposite {!!} {!!} a)) -- {!transportComposite ? (cong El⁰ (funExt⁻ (sym p) x)) a!})) -- transportComposite {!!} {!!} a))
    -- where
    --     tmp : (x : El⁰ Γ) → (λ i → El⁰ (funExt⁻ (λ i₁ → ((∫ᴾ V-CwF .tyPresheaf) Category.⋆ (f , p)) (g , q) .snd (~ i₁)) x i)) ≡ ((λ i → El⁰ (funExt⁻ (λ i₁ → p (~ i₁)) x i)) ∙ (λ i → El⁰ (funExt⁻ (λ i₁ → q (~ i₁)) (f x) i)))
    --     tmp x = {!!}

-- 

-- transport
--       (λ i →
--          El⁰
--          (funExt⁻
--           (λ i₁ →
--              ((∫ᴾ V-CwF .tyPresheaf) Category.⋆ (γ , p)) (f , q) .snd (~ i₁))
--           x i))
--       a
--       ≡
--       transport (λ i → El⁰ (funExt⁻ (λ i₁ → q (~ i₁)) (γ x) i))
--       (transport (λ i → El⁰ (funExt⁻ (λ i₁ → p (~ i₁)) x i)) a)

V-CwF .ctxExtEquiv Γ Δ a = isoToEquiv isom
    where
        isom : Iso _ _
        isom .Iso.fun f = (λ x → fst (f x)) , lift (λ x → snd (f x))
        -- the following doesn't work for some reason
        -- isom .Iso.fun f .fst = (λ x → fst (f x))
        -- isom .Iso.fun f .snd = lift (λ x → snd (f x))
        isom .Iso.inv (f , g) A .fst = f A
        isom .Iso.inv (f , g) A .snd = g .lower A
        isom .Iso.rightInv (f , g) = refl
        isom .Iso.leftInv f = refl

V-CwF .ctxExtEquivNat Δ Δ' Γ A δ γ = ΣPathP (refl , {!!})
-- subst⁻ (λ a → Lift ((x : El⁰ Δ') → El⁰ (a x))) (∘ᴾAssoc V (V-CwF .tyPresheaf) A (λ x → fst (γ x)) δ) (action (∫ᴾ V-CwF .tyPresheaf) (V-CwF .tmPresheaf) (δ , refl) (lift (λ x → snd (γ x))))

test : {ℓ : Level} → Presheaf (∫ᴾ (V-CwF {ℓ} .tyPresheaf)) ℓ
test .F-ob (Γ , A) .fst = (x : El⁰ Γ) → El⁰ (A x)
test .F-ob (Γ , A) .snd = isSetΠ λ x → thm17 (A x)
test .F-hom {Γ , A} {Δ , B} (f , p) t x = transport (cong El⁰ (funExt⁻ p x)) (t (f x))
test .F-id {Γ , A} = funExt λ _ → funExt (λ _ → transportRefl _)
test .F-seq {Γ , A} {Δ , B} {Λ , C} (f , p) (g , q) = funExt₂ λ t x → {!Σ≡Prop!} -- (tmp x t) ∙ transportComposite (cong El⁰ (funExt⁻ p (g x))) (cong El⁰ (funExt⁻ q x)) (t (f (g x))) -- funExt λ t → funExt λ x → {!!} 

    -- where
    --   tmp : (x : El⁰ Λ) (t : (x₁ : El⁰ Γ) → El⁰ (A x₁)) → transport (λ i → El⁰ (funExt⁻ ((g , q) ⋆⟨ {!∫ᴾ V-CwF .tyPresheaf!} ⟩ (f , p) .snd) x i)) (t ( f (g x))) ≡ transport ((λ i → El⁰ (funExt⁻ p (g x) i)) ∙ (λ i → El⁰ (funExt⁻ q x i))) (t (f (g x)))
    --   -- tmp : (x : El⁰ Λ) (t : (x₁ : El⁰ Γ) → El⁰ (A x₁)) → transport (λ i → El⁰ (funExt⁻ (seq' (∫ᴾ V-CwF .tyPresheaf) (g , q) (f , p) .snd) x i)) (t ( f (g x))) ≡ transport ((λ i → El⁰ (funExt⁻ p (g x) i)) ∙ (λ i → El⁰ (funExt⁻ q x i))) (t (f (g x)))
    --   tmp x t = {!!}



-- transport
--       (λ i →
--          El⁰
--          (funExt⁻ (seq' (∫ᴾ V-CwF .tyPresheaf) (g , q) (f , p) .snd) x i))
--       (t (seq' (∫ᴾ V-CwF .tyPresheaf) (g , q) (f , p) .fst x))
--       ≡
--       transport (λ i → El⁰ (funExt⁻ q x i))
--       (transport (λ i → El⁰ (funExt⁻ p (g x) i)) (t (f (g x))))
