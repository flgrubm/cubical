module Cubical.Data.W.W where

open import Cubical.Foundations.Prelude

-- TODO: potentially move _∈_ to a separate module, avoiding the imports
open import Cubical.Foundations.Equiv
open import Cubical.Relation.Nullary

private
  variable
    ℓ ℓ' ℓ'' ℓ''' ℓ'''' : Level

data W (S : Type ℓ) (P : S → Type ℓ') : Type (ℓ-max ℓ ℓ') where
  sup-W : (s : S) → (P s → W S P) → W S P

private
    variable
        S : Type ℓ
        P : S → Type ℓ'
        x y : W S P

nodes : (x : W S P) → S
nodes (sup-W a _) = a

arities : (x : W S P) → P (nodes x) → W S P
arities (sup-W _ f) = f

W-nodes-arities : x ≡ sup-W (nodes x) (arities x)
W-nodes-arities {x = sup-W _ _} = refl

WInd : (S : Type ℓ) (P : S → Type ℓ') (M : W S P → Type ℓ'') →
       (e : {s : S} {f : P s → W S P} → ((p : P s) → M (f p)) → M (sup-W s f)) →
       (w : W S P) → M w
WInd S P M e (sup-W s f) = e (λ p → WInd S P M e (f p))

WInd2 : (S : Type ℓ) (P : S → Type ℓ') (S' : Type ℓ'') (P' : S' → Type ℓ''')
        (M : W S P → W S' P' → Type ℓ'''')
        (e : {s : S} {f : P s → W S P} {s' : S'} {f' : P' s' → W S' P'} →
            ((p : P s) (p' : P' s') → M (f p) (f' p')) → M (sup-W s f) (sup-W s' f'))
        → (w : W S P) → (x : W S' P') → M w x
WInd2 S P S' P' M e (sup-W s f) (sup-W s' f') = e (λ p p' → WInd2 S P S' P' M e (f p) (f' p'))

_∈W_ : {S : Type ℓ} {P : S → Type ℓ'} (x y : W S P) → Type (ℓ-max ℓ ℓ')
x ∈W y = fiber (arities y) x

∈W-irrefl : ¬ x ∈W x
∈W-irrefl {x = sup-W x α} p = ∈W-irrefl {x = α (p .fst)} (transport (cong (λ r → r ∈W r) (sym (p .snd))) p)
