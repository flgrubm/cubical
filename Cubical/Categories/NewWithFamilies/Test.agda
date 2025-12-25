module Cubical.Categories.WithFamilies.Test where

open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Presheaf
open import Cubical.Data.Sigma
open import Cubical.Foundations.Equiv

open Category
open Functor

∫ᴾ_ : {ℓ ℓ' ℓS : Level} {C : Category ℓ ℓ'} → Presheaf C ℓS → Category (ℓ-max ℓ ℓS) (ℓ-max ℓ' ℓS)
∫ᴾ_ {C = C} P .ob = Σ[ A ∈ C .ob ] (P ⟅ A ⟆) .fst
∫ᴾ_ {C = C} P .Hom[_,_] (A , x) (B , y) = fiber (λ (f : C [ B , A ]) → (P ⟪ f ⟫) x) y
-- ∫ᴾ_ {C = C} P .Hom[_,_] (A , x) (B , y) = Σ[ f ∈ C .Hom[_,_] B A ] ((P ⟪ f ⟫) x) ≡ y
∫ᴾ_ {C = C} P .id {A , x} .fst = C .id {A}
∫ᴾ_ {C = C} P .id {A , x} .snd = funExt⁻ (P .F-id) x
∫ᴾ_ {C = C} P ._⋆_ {A , x} {B , y} {D , z} f g .fst = {!_⋆⟨_⟩_!}
∫ᴾ_ {C = C} P ._⋆_ {A , x} {B , y} {D , z} f g .snd = {!!}
∫ᴾ_ {C = C} P .⋆IdL = {!!}
∫ᴾ_ {C = C} P .⋆IdR = {!!}
∫ᴾ_ {C = C} P .⋆Assoc = {!!}
∫ᴾ_ {C = C} P .isSetHom = {!!}
