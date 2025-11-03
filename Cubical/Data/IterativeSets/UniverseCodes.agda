module Cubical.Data.IterativeSets.UniverseCodes where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism


Iso-Lift : {ℓ ℓ' : Level} {A : Type ℓ} → Iso A (Lift {j = ℓ'} A)
Iso-Lift .Iso.fun = lift
Iso-Lift .Iso.inv = lower
Iso-Lift .Iso.rightInv _ = refl
Iso-Lift .Iso.leftInv _ = refl
