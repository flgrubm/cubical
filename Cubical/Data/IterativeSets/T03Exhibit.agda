module Cubical.Data.IterativeSets.T03Exhibit where
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
open import Cubical.Foundations.Path

open import Cubical.Data.Sigma

-- open import Cubical.

open import Cubical.Homotopy.Base

open import Cubical.Data.W.W

open import Cubical.Data.IterativeSets.Base

private
  variable
    ℓ ℓ' ℓ'' : Level
    A A' : Type ℓ
    B B' : A → Type ℓ'

-- Version without J

-- these should really be in the library, but I haven't found it there?

refl∙refl≡refl : {A : Type ℓ} {x : A} → refl ∙ refl ≡ refl {x = x}
refl∙refl≡refl = sym (compPath-filler refl refl)

∙refl-is-identity : {A B : Type ℓ} (p : A ≡ B) → p ∙ refl ≡ p
∙refl-is-identity p = sym (compPath-filler p refl)

∙refl-is-identity' : {A B : Type ℓ} (p : A ≡ B) → p ∙ refl ≡ p
∙refl-is-identity' = J (λ C q → q ∙ refl ≡ q) refl∙refl≡refl

refl∙-is-identity : {A B : Type ℓ} (p : A ≡ B) → refl ∙ p ≡ p
refl∙-is-identity = J (λ C q → refl ∙ q ≡ q) refl∙refl≡refl

compTransport-is-transportComp : {A B C : Type ℓ} (x : A) (p : A ≡ B) (q : B ≡ C) → transport q (transport p x) ≡ transport (p ∙ q) x
compTransport-is-transportComp x p q = J (λ y q' → transport q' (transport p x) ≡ transport (p ∙ q') x) (transportRefl (transport p x) ∙ cong (λ r → transport r x) (sym (∙refl-is-identity p))) q

Path∙symPath-cancel : {A B : Type ℓ} (p : A ≡ B) → p ∙ (sym p) ≡ refl
Path∙symPath-cancel p = cong (λ r → p ∙ r) (sym (∙refl-is-identity (sym p))) ∙ compPathl-cancel p refl

symPath∙Path-cancel : {A B : Type ℓ} (p : A ≡ B) → (sym p) ∙ p ≡ refl
symPath∙Path-cancel p = cong (λ r → r ∙ p) (sym (refl∙-is-identity (sym p))) ∙ compPathr-cancel p refl

f-w/oJ : {ℓ ℓ' : Level} {A : Type ℓ} {B : A → Type ℓ'} {x y : W A B} → (x ≡ y) → (Σ[ p ∈ (overline-W x ≡ overline-W y) ] (tilde-W x ∼ (tilde-W y ∘ (transport (cong B p)))))
f-w/oJ {A = A} {B = B} {x = sup-∞ x α} {y = sup-∞ y β} p .fst = cong overline-W p
f-w/oJ {A = A} {B = B} {x = sup-∞ x α} {y = sup-∞ y β} p .snd z i = tilde-W (p i) (transport-filler (cong (B ∘ overline-W) p) z i)

f-w/oJ-inv : {ℓ ℓ' : Level} {A : Type ℓ} {B : A → Type ℓ'} {x y : W A B} → (Σ[ p ∈ (overline-W x ≡ overline-W y) ] (tilde-W x ∼ (tilde-W y ∘ (transport (cong B p))))) → (x ≡ y)
f-w/oJ-inv {A = A} {B = B} {x = sup-W x α} {y = sup-W y β} (p , q) i = sup-∞ (p i) (k' i)
    where
        k : PathP (λ j → B (p j) → W A B) (α ∘ (transport refl)) (β ∘ (transport (cong B p)) ∘ (transport (sym (cong B p))))
        k j z = (funExt q) j (transport (cong B (λ k → p (j ∧ ~ k))) z)

        k' : PathP (λ j → B (p j) → W A B) α β
        k' = funExt αpart ◁ k ▷ funExt βpart
            where
                αpart : (a : B x) → α a ≡ α (transport refl a)
                αpart a = cong α (sym (transportRefl a))
                βpart : (b : B y) → β (transport (cong B p) (transport (sym (cong B p)) b)) ≡ β b
                βpart b = (cong β (compTransport-is-transportComp b (sym (cong B p)) (cong B p))
                    ∙ cong (λ r → β (transport r b)) (symPath∙Path-cancel (cong B p))
                    ∙ cong β (transportRefl b))

-- version specifically for V∞ {ℓ}
f-V∞-w/oJ-inv : {x y : V∞ {ℓ}} → (Σ[ p ∈ (overline-∞ x ≡ overline-∞ y) ] (tilde-∞ x ≡ (tilde-∞ y ∘ (transport p)))) → (x ≡ y)
f-V∞-w/oJ-inv {ℓ} {x = sup-∞ A f} {y = sup-∞ B g} (p , q) i = sup-W (p i) (k' i)
    where
        -- k : (j : I) → p j → V∞ {ℓ}
        k : PathP (λ j → p j → V∞ {ℓ}) (f ∘ (transport refl)) (g ∘ (transport p) ∘ (transport (sym p)))
        k j z = q j (transport (λ k → p (j ∧ ~ k)) z)

        k' : PathP (λ j → p j → V∞ {ℓ}) f g
        k' = funExt fpart ◁ k ▷ funExt gpart
            where
                fpart : (a : A) → f a ≡ f (transport refl a)
                fpart a = cong f (sym (transportRefl a))
                gpart : (b : B) → g (transport p (transport (sym p) b)) ≡ g b
                gpart b = cong g (compTransport-is-transportComp b (sym p) p ∙ cong (λ r → transport r b) (symPath∙Path-cancel p) ∙ transportRefl b)

-- ret : {ℓ ℓ' : Level} {A : Type ℓ} {B : A → Type ℓ'} {x y : W A B} → retract (f {x = x} {y = y}) (finv {x = x} {y = y})
-- ret {x = x} {y = y} = J (λ z p → {!retract (f {x = sup-W x α} {y = z}) (finv {x = sup-W y β} {y = z})!}) {!!}
--     where
--         fam : (z : W A B) → (x ≡ z) → Type ?
--         fam z _ = retract (f {x = x} {y = z}) (finv {x = x} {y = z})

sup-W-overline-tilde : {x : W A B} → x ≡ sup-W (overline-W x) (tilde-W x)
sup-W-overline-tilde {x = sup-W x α} = refl

-- ret : {ℓ ℓ' : Level} {A : Type ℓ} {B : A → Type ℓ'} {x y : W A B} → retract (f {x = x} {y = y}) (finv {x = x} {y = y})
-- ret {B = B} {x = sup-W x α} {y = sup-W y β} p =
--     finv (f p)
--         ≡⟨⟩
--     finv (cong overline-W p , λ z i → tilde-W (p i) (transport-filler (cong (B ∘ overline-W) p) z i))
--         ≡⟨⟩
--     λ i → sup-W (cong overline-W p i) (? i)
--         ≡⟨ {!!} ⟩
--     p
--         ∎


-- With J

f-w/J : {ℓ ℓ' : Level} {A : Type ℓ} {B : A → Type ℓ'} {x y : W A B} → (x ≡ y) → (Σ[ p ∈ (overline-W x ≡ overline-W y) ] (tilde-W x ∼ (tilde-W y ∘ (transport (cong B p)))))
f-w/J {ℓ = ℓ} {ℓ' = ℓ'} {A = A} {B = B} {x = x} {y = y} = J P d
    where
        P : (z : W A B) → x ≡ z → Type (ℓ-max ℓ ℓ')
        P z p = Σ[ p ∈ (overline-W x ≡ overline-W z) ] (tilde-W x ∼ (tilde-W z ∘ (transport (cong B p))))
        d : P x refl
        d .fst = refl
        d .snd b = cong (tilde-W x) (sym (transportRefl b))

f-V∞-w/J : {x y : V∞ {ℓ}} → x ≡ y → Σ[ e ∈ overline-∞ x ≡ overline-∞ y ] tilde-∞ x ∼ (tilde-∞ y ∘ transport e)
f-V∞-w/J {x = x} {y = y} = J (λ z p → Σ[ e ∈ overline-∞ x ≡ overline-∞ z ] tilde-∞ x ∼ (tilde-∞ z ∘ transport e)) (refl , (λ a → cong (tilde-∞ x) (sym (transportRefl a))))

f-w/J-inv : {ℓ ℓ' : Level} {A : Type ℓ} {B : A → Type ℓ'} {x y : W A B} → (Σ[ p ∈ (overline-W x ≡ overline-W y) ] (tilde-W x ∼ (tilde-W y ∘ (transport (cong B p))))) → (x ≡ y)
f-w/J-inv {ℓ = ℓ} {ℓ' = ℓ'} {A = A} {B = B} {x = sup-W x α} {y = sup-W y β} (p , h) = J2 Q r p (funExt h)
    where
        Q : (y' : A) (p' : x ≡ y') (β' : (b : B x) → W A B) → α ≡ β' → Type (ℓ-max ℓ ℓ')
        Q y' p' β' h' = sup-W x α ≡ sup-W y' f
            where
                f : B y' → W A B
                f b = {!β' (transport (cong B (sym p')) b)!}
                -- f b = {!α (transport (cong B (sym p')) b)!}
        r : Q _ refl _ refl
        r = refl
