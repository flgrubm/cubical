open import Cubical.Foundations.Prelude
open import Cubical.Relation.Binary.Base
open import Cubical.Foundations.Transport

open import Cubical.Data.IterativeSets.Base
open import Cubical.Data.IterativeSets.Empty
open import Cubical.Data.IterativeSets.Unit
open import Cubical.Data.IterativeSets.Sum
open import Cubical.Data.IterativeSets.Sigma
open import Cubical.Data.IterativeSets.Fiber
open import Cubical.Data.IterativeSets.Identity

open import Cubical.Foundations.HLevels

module Cubical.ECat.Setoids where

Setoid : {ℓ ℓ' : Level} → Type (ℓ-max (ℓ-suc ℓ) (ℓ-suc ℓ'))
Setoid {ℓ} {ℓ'} = Σ[ A ∈ Type ℓ ] EquivRel A ℓ'

setoid-≈-syntax : {ℓ ℓ' : Level} → (A : Setoid {ℓ} {ℓ'}) (x y : A .fst) → Type ℓ'
setoid-≈-syntax A x y = A .snd .fst x y

syntax setoid-≈-syntax A x y = x ≈⟨ A ⟩ y

Type→Setoid : {ℓ : Level} → Type ℓ → Setoid {ℓ} {ℓ}
Type→Setoid {ℓ} A .fst = A
Type→Setoid {ℓ} A .snd .fst = _≡_
Type→Setoid {ℓ} A .snd .snd .BinaryRelation.isEquivRel.reflexive _ = refl
Type→Setoid {ℓ} A .snd .snd .BinaryRelation.isEquivRel.symmetric _ _ = sym
Type→Setoid {ℓ} A .snd .snd .BinaryRelation.isEquivRel.transitive a b c = _∙_

SetoidMap : {ℓA ℓA' ℓB ℓB' : Level} → (A : Setoid {ℓA} {ℓA'}) (B : Setoid {ℓB} {ℓB'}) → Type (ℓ-max (ℓ-max (ℓ-max ℓA ℓA') ℓB) ℓB')
SetoidMap A B = Σ[ f ∈ (A .fst → B .fst) ] ((x y : A .fst) → x ≈⟨ A ⟩ y → f x ≈⟨ B ⟩ f y)

SetoidMap2 : {ℓA ℓA' ℓB ℓB' ℓC ℓC' : Level} → (A : Setoid {ℓA} {ℓA'}) (B : Setoid {ℓB} {ℓB'}) (C : Setoid {ℓC} {ℓC'}) → Type (ℓ-max (ℓ-max (ℓ-max (ℓ-max (ℓ-max ℓA ℓA') ℓB) ℓB') ℓC) ℓC')
SetoidMap2 A B C = Σ[ f ∈ (A .fst → B .fst → C .fst) ] ((a x : A .fst) (b y : B .fst) → a ≈⟨ A ⟩ x → b ≈⟨ B ⟩ y → f a b ≈⟨ C ⟩ f x y)

record ECat {ℓOb ℓHom ℓHomEquiv : Level} : Type (ℓ-max (ℓ-max (ℓ-suc ℓOb) (ℓ-suc ℓHom)) (ℓ-suc ℓHomEquiv)) where
  field
    Ob : Type ℓOb
    Hom[_,_] : Ob → Ob → Setoid {ℓHom} {ℓHomEquiv}

    id : {x : Ob} → Hom[ x , x ] .fst
    ecomp : {x y z : Ob} → SetoidMap2 Hom[ x , y ] Hom[ y , z ] Hom[ x , z ]
    idl : {x y : Ob} (f : Hom[ x , y ] .fst) → ecomp .fst (id {x}) f ≈⟨ Hom[ x , y ] ⟩ f
    idr : {x y : Ob} (f : Hom[ x , y ] .fst) → ecomp .fst f (id {y}) ≈⟨ Hom[ x , y ] ⟩ f
    assoc : {x y z a : Ob} (f : Hom[ x , y ] .fst) (g : Hom[ y , z ] .fst) (h : Hom[ z , a ] .fst) → ecomp .fst f (ecomp .fst g h) ≈⟨ Hom[ x , a ] ⟩ ecomp .fst (ecomp .fst f g ) h

record HCat {ℓOb ℓObEquiv ℓHom ℓHomEquiv : Level} : Type (ℓ-max (ℓ-max (ℓ-max (ℓ-suc ℓOb) (ℓ-suc ℓObEquiv)) (ℓ-suc ℓHom)) (ℓ-suc ℓHomEquiv)) where
  field
    ObSetoid : Setoid {ℓOb} {ℓObEquiv}
  Ob : Type ℓOb
  Ob = ObSetoid .fst

  field
    Hom[_,_] : Ob → Ob → Setoid {ℓHom} {ℓHomEquiv}
    id : {x : Ob} → Hom[ x , x ] .fst
    ecomp : {x y z : Ob} → SetoidMap2 Hom[ x , y ] Hom[ y , z ] Hom[ x , z ]
    idl : {x y : Ob} (f : Hom[ x , y ] .fst) → ecomp .fst (id {x}) f ≈⟨ Hom[ x , y ] ⟩ f
    idr : {x y : Ob} (f : Hom[ x , y ] .fst) → ecomp .fst f (id {y}) ≈⟨ Hom[ x , y ] ⟩ f
    assoc : {x y z a : Ob} (f : Hom[ x , y ] .fst) (g : Hom[ y , z ] .fst) (h : Hom[ z , a ] .fst) → ecomp .fst f (ecomp .fst g h) ≈⟨ Hom[ x , a ] ⟩ ecomp .fst (ecomp .fst f g ) h

    -- new
    tr : {x y : Ob} → x ≈⟨ ObSetoid ⟩ y → Hom[ x , y ] .fst
    tr-refl : {x : Ob} → (p : x ≈⟨ ObSetoid ⟩ x) → tr p ≈⟨ Hom[ x , x ] ⟩ id {x} 
    tr-prop : {x y : Ob} (p q : x ≈⟨ ObSetoid ⟩ y) → tr p ≈⟨ Hom[ x , y ] ⟩ tr q
    tr-comp : {x y z : Ob} (p : x ≈⟨ ObSetoid ⟩ y) (q : y ≈⟨ ObSetoid ⟩ z) (r : x ≈⟨ ObSetoid ⟩ z) → ecomp .fst (tr p) (tr q) ≈⟨ Hom[ x , z ] ⟩ tr r

record EFunctor {ℓOb ℓHom ℓHomEquiv ℓOb' ℓHom' ℓHomEquiv' : Level} (C : ECat {ℓOb} {ℓHom} {ℓHomEquiv}) (D : ECat {ℓOb'} {ℓHom'} {ℓHomEquiv'}) : Type {!!} where
  field
    EF-Ob : C .ECat.Ob → D .ECat.Ob
    EF-Hom : {x y : C .ECat.Ob} → SetoidMap (C .ECat.Hom[_,_] x y) (D .ECat.Hom[_,_] (EF-Ob x) (EF-Ob y))

record HFunctor {ℓOb ℓObEquiv ℓHom ℓHomEquiv ℓOb' ℓObEquiv' ℓHom' ℓHomEquiv' : Level} (C : HCat {ℓOb} {ℓObEquiv} {ℓHom} {ℓHomEquiv}) (D : HCat {ℓOb'} {ℓObEquiv'} {ℓHom'} {ℓHomEquiv'}) : Type {!!} where
  field
    EF-ObSetoid : SetoidMap (C .HCat.ObSetoid) (D .HCat.ObSetoid)
  EF-Ob : HCat.Ob C → HCat.Ob D
  EF-Ob = EF-ObSetoid .fst

  field
    EF-Hom : {x y : HCat.Ob C} → SetoidMap (C .HCat.Hom[_,_] x y) (D .HCat.Hom[_,_] (EF-Ob x) (EF-Ob y))

isContrSetoid : {ℓ ℓ' : Level} → Setoid {ℓ} {ℓ'} → Type (ℓ-max ℓ ℓ')
isContrSetoid S = Σ[ c ∈ S .fst ] ((x : S .fst) → c ≈⟨ S ⟩ x)

ETerminal : {ℓOb ℓHom ℓHomEquiv : Level} → ECat {ℓOb} {ℓHom} {ℓHomEquiv} → Type (ℓ-max (ℓ-max ℓOb ℓHom) ℓHomEquiv)
ETerminal C = Σ[ t ∈ C .ECat.Ob ] ((x : C .ECat.Ob) → isContrSetoid (C .ECat.Hom[_,_] x t))

HTerminal : {ℓOb ℓObEquiv ℓHom ℓHomEquiv : Level} → HCat {ℓOb} {ℓObEquiv} {ℓHom} {ℓHomEquiv} → Type (ℓ-max (ℓ-max ℓOb ℓHom) ℓHomEquiv)
HTerminal C = Σ[ t ∈ HCat.Ob C ] ((x : HCat.Ob C) → isContrSetoid (C .HCat.Hom[_,_] x t))

_^Eop : {ℓOb ℓHom ℓHomEquiv : Level} → ECat {ℓOb} {ℓHom} {ℓHomEquiv} → ECat {ℓOb} {ℓHom} {ℓHomEquiv}
(C ^Eop) .ECat.Ob = C .ECat.Ob
(C ^Eop) .ECat.Hom[_,_] x y = C .ECat.Hom[_,_] y x
(C ^Eop) .ECat.id = C .ECat.id
(C ^Eop) .ECat.ecomp .fst f g = C .ECat.ecomp .fst g f
(C ^Eop) .ECat.ecomp .snd f₁ f₂ g₁ g₂ p q = C .ECat.ecomp .snd g₁ g₂ f₁ f₂ q p
(C ^Eop) .ECat.idl = C .ECat.idr
(C ^Eop) .ECat.idr = C .ECat.idl
(C ^Eop) .ECat.assoc = {!!}


-- SET is an HCat

SET : {ℓ : Level} → HCat {{!!}} {{!!}} {{!!}} {{!!}}
SET {ℓ} .HCat.ObSetoid = Type→Setoid (hSet ℓ)
SET {ℓ} .HCat.Hom[_,_] x y = Type→Setoid (x .fst → y .fst)
SET {ℓ} .HCat.id x = x
SET {ℓ} .HCat.ecomp .fst f g x = g (f x)
SET {ℓ} .HCat.ecomp .snd f₁ f₂ g₁ g₂ p q i x = q i (p i x)
SET {ℓ} .HCat.idl _ = refl
SET {ℓ} .HCat.idr _ = refl
SET {ℓ} .HCat.assoc _ _ _ = refl
SET {ℓ} .HCat.tr = subst fst
SET {ℓ} .HCat.tr-refl = {!!}
SET {ℓ} .HCat.tr-prop = {!!}
SET {ℓ} .HCat.tr-comp = {!!}

-- V⁰ is an HCat

V : {ℓ : Level} → HCat {ℓ-suc ℓ} {ℓ-suc ℓ} {ℓ} {ℓ}
V {ℓ} .HCat.ObSetoid = Type→Setoid (V⁰ {ℓ})
V {ℓ} .HCat.Hom[_,_] x y = Type→Setoid (El⁰ x → El⁰ y)
V {ℓ} .HCat.id x = x
V {ℓ} .HCat.ecomp .fst f g x = g (f x)
V {ℓ} .HCat.ecomp .snd f₁ f₂ g₁ g₂ p q i x = q i (p i x)
V {ℓ} .HCat.idl f = refl
V {ℓ} .HCat.idr f = refl
V {ℓ} .HCat.assoc f g h = refl
V {ℓ} .HCat.tr = subst El⁰
V {ℓ} .HCat.tr-refl {x} p = funExt (isSet-subst {A = V⁰ {ℓ}} {B = El⁰ {ℓ}} isSetV⁰ p)
V {ℓ} .HCat.tr-prop {x} {y} p q = funExt (λ a → cong (λ m → subst El⁰ m a) (isSetV⁰ x y p q))
V {ℓ} .HCat.tr-comp {x} {y} {z} p q r = funExt (λ a → sym (substComposite (El⁰ {ℓ}) {x} {y} {z} p q a) ∙ cong (λ m → subst El⁰ m a) (isSetV⁰ x z (p ∙ q) r))


