open import Cubical.Foundations.Prelude
open import Cubical.ECat.Setoids

module Cubical.ECat.ECat where

record ECat : Type {!!} where
  field
    Ob : Type
    Hom[_,_] : Ob → Ob → Type
    HomEquiv[_,_] : Ob → Ob → 
    id : {x : Ob} → Hom[_,_] x x
