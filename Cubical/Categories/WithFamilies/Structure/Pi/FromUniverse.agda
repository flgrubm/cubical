module Cubical.Categories.WithFamilies.Structure.Pi.FromUniverse where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Function

open import Cubical.Data.Sigma.Properties

open import Cubical.Categories.WithFamilies.Base
import Cubical.Categories.WithFamilies.FromUniverse as FU
open import Cubical.Categories.WithFamilies.Structure.Pi.Base

private
  variable
    ℓ ℓ' ℓ'' ℓ''' : Level

module Internal (U : Type ℓ)
         (USet : isSet U)
         (El : U → Type ℓ')
         (ElSet : (Γ : U) → isSet (El Γ))
         (Unit : U)
         (UnitTerminal : isContr (El Unit))
         (Sig : (Γ : U) → (El Γ → U) → U)
         (SigIso : (Γ : U) (A : El Γ → U) → El (Sig Γ A) ≃ (Σ[ x ∈ El Γ ] El (A x)))
         (Pi : (Γ : U) → (El Γ → U) → U)
         (PiIso : (Γ : U) (A : El Γ → U) → El (Pi Γ A) ≃ ((x : El Γ) → El (A x)))
         where
  open FU.Internal U USet El ElSet Unit UnitTerminal Sig SigIso

  U-Π : Π-Structure-CwF UCwF
  U-Π .Π-Structure-CwF.pi Γ A B x = Pi (A x) λ y → B (invEq (SigIso Γ A) (x , y))

  U-Π .Π-Structure-CwF.pi-nat {Γ} {Δ} A B σ = funExt (λ x → cong (Pi (A (σ x))) (funExt (λ y → cong (λ m → B (invEq (SigIso Γ A) m))
    let
      r : (Σ (El Γ) (λ v → El (A v)))
      r = σ x , y

      s : (Σ (El Γ) (λ v → El (A v)))
      s = (σ (SigIso Δ (λ x₁ → A (σ x₁)) .fst (invEq (SigIso Δ (λ x₁ → A (σ x₁))) (x , y))
                             .fst)) , SigIso Δ (λ x₁ → A (σ x₁)) .fst (invEq (SigIso Δ λ v → A (σ v)) (x , y)) .snd
      
      
      t : Σ (El Γ) (λ v → El (A v))
      t = (σ (SigIso Δ (λ x₁ → A (σ x₁)) .fst (invEq (SigIso Δ (λ x₁ → A (σ x₁))) (x , y)) .fst)) , subst⁻ El refl (SigIso Δ (λ x₁ → A (σ x₁)) .fst (invEq (SigIso Δ λ v → A (σ v)) (x , y)) .snd)

      r≡s : r ≡ s
      r≡s i = ((σ (secEq (SigIso Δ λ v → A (σ v)) (x , y) (~ i) .fst)) , secEq (SigIso Δ λ v → A (σ v)) (x , y) (~ i) .snd)

      s≡t : s ≡ t
      s≡t = cong (λ m → (σ (SigIso Δ (λ x₁ → A (σ x₁)) .fst (invEq (SigIso Δ (λ x₁ → A (σ x₁))) (x , y)) .fst)) , m) (sym (substRefl {B = El} (SigIso Δ (λ x₁ → A (σ x₁)) .fst (invEq (SigIso Δ (λ v → A (σ v))) (x , y)) .snd)))
    in r≡s ∙ s≡t)))

  U-Π .Π-Structure-CwF.pi-iso {Γ} A B =
    let
      fun : ((x : El Γ) →
              El
              (Pi (A x)
               (λ y → B (invEq (SigIso Γ A) (x , y))))) →
             (x : El (Sig Γ A)) → El (B x)
             -- CwF.Tm UCwF Γ (U-Π .Π-Structure-CwF.pi Γ A B) →
             -- CwF.Tm UCwF (CwF.ctxExt UCwF Γ A) B
      fun F p =
        let
          pair : Σ (El Γ) (λ x₁ → El (A x₁))
          pair = SigIso Γ A .fst p

          x : El Γ
          x = pair .fst

          y : El (A x)
          y = pair .snd

          internal-pi : El (Pi (A x) (λ y₁ → B (invEq (SigIso Γ A) (x , y₁))))
          internal-pi = F x

          agda-func : (y₁ : El (A x)) → El (B (invEq (SigIso Γ A) (x , y₁)))
          agda-func = (PiIso (A x) (λ y₁ → B (invEq (SigIso Γ A) (x , y₁)))) .fst internal-pi

          val : El (B (invEq (SigIso Γ A) (x , y)))
          val = agda-func y
        in subst (λ m → El (B m)) (retEq (SigIso Γ A) p) val

      inv : ((x : El (Sig Γ A)) → El (B x)) →
             (x : El Γ) →
             El
             (Pi (A x)
              (λ y → B (snd (SigIso Γ A) .equiv-proof (x , y) .fst .fst)))
      inv b x = invEq (PiIso (A x) (λ y → B (invEq (SigIso Γ A) (x , y)))) λ y → b (invEq (SigIso Γ A) (x , y))

      subst-dep-path : ∀ {ℓ ℓ'} {A : Type ℓ} {P : A → Type ℓ'} 
                 (b : (x : A) → P x) {x y : A} (p : x ≡ y) → 
                 subst P p (b x) ≡ b y
      subst-dep-path {P = P} b {x = x} {y = y} p = J (λ y p' → subst P p' (b x) ≡ b y) (substRefl {B = P} (b x)) p

      pathP-to-subst : ∀ {ℓ ℓ'} {A : Type ℓ} {P : A → Type ℓ'} 
                 {x y : A} (p : x ≡ y) {u : P x} {v : P y}
                 → PathP (λ i → P (p i)) u v
                 → subst P p u ≡ v
      pathP-to-subst _ = fromPathP
      
      sec : section fun inv
      sec b = funExt (λ p →
        let
          pair = SigIso Γ A .fst p
          x = pair .fst
          y = pair .snd

          pi-sec : PiIso (A x) (λ y₁ → B (invEq (SigIso Γ A) (x , y₁))) .fst
                    (invEq (PiIso (A x) (λ y₁ → B (invEq (SigIso Γ A) (x , y₁))))
                     (λ y₁ → b (invEq (SigIso Γ A) (x , y₁))))
                    ≡ (λ y₁ → b (invEq (SigIso Γ A) (x , y₁)))
          pi-sec = secEq (PiIso (A x) (λ y₁ → B (invEq (SigIso Γ A) (x , y₁)))) (λ y₁ → b (invEq (SigIso Γ A) (x , y₁)))

          val0 : El (B (invEq (SigIso Γ A) (x , y)))
          val0 = fst (PiIso (A x) (λ y₁ → B (snd (SigIso Γ A) .equiv-proof (x , y₁) .fst .fst))) (inv b x) y

          val1 : El (B (invEq (SigIso Γ A) pair))
          val1 = b (invEq (SigIso Γ A) pair)

          val-eq : val0 ≡ val1
          val-eq j = pi-sec j y

          eq : invEq (SigIso Γ A) pair ≡ p
          eq = retEq (SigIso Γ A) p

          step1 : subst (λ z → El (B z)) eq val0 ≡ subst (λ z → El (B z)) eq val1
          step1 j = subst (λ z → El (B z)) eq (val-eq j)

          step2 : subst (λ z → El (B z)) eq val1 ≡ b p
          step2 = subst-dep-path b eq
        in step1 ∙ step2)

      ret : retract fun inv
      ret F = funExt (λ x →
        let
          inner-eq : (λ y → fun F (invEq (SigIso Γ A) (x , y))) ≡ PiIso (A x) (λ z → B (invEq (SigIso Γ A) (x , z))) .fst (F x)
          inner-eq = funExt (λ y →
            let
              p : El (Sig Γ A)
              p = invEq (SigIso Γ A) (x , y)

              pair : Σ (El Γ) (λ x₁ → El (A x₁))
              pair = fst (SigIso Γ A) p

              s : pair ≡ (x , y)
              s = secEq (SigIso Γ A) (x , y)

              val0 : El (B (invEq (SigIso Γ A)(SigIso Γ A .fst p)))
              val0 = fst (PiIso (A (fst pair)) (λ y₁ → B (invEq (SigIso Γ A) (fst (fst (SigIso Γ A) p) , y₁)))) (F (fst pair)) (snd pair)

              val1 : El (B p)
              val1 = fst (PiIso (A x) (λ y₁ → B (invEq (SigIso Γ A) (x , y₁)))) (F x) y

              dpath : PathP (λ j → El (B (invEq (SigIso Γ A) (s j)))) val0 val1
              dpath j = PiIso (A (fst (s j))) (λ y₁ → B (invEq (SigIso Γ A) (fst (secEq (SigIso Γ A) (x , y) j) , y₁))) .fst (F (fst (s j))) (snd (s j))

              s-subst-eq : subst (λ z → El (B z)) (λ j → invEq (SigIso Γ A) (s j)) val0 ≡ val1
              s-subst-eq = pathP-to-subst {P = λ z → El (B z)} (λ j → invEq (SigIso Γ A) (s j)) dpath
              
              ret-path : invEq (SigIso Γ A) pair ≡ p
              ret-path = retEq (SigIso Γ A) p

              s-path : invEq (SigIso Γ A) pair ≡ p
              s-path i = invEq (SigIso Γ A) (s i)

              path-eq : ret-path ≡ s-path
              path-eq = ElSet (Sig Γ A) (invEq (SigIso Γ A) pair) p ret-path s-path

              subst-eq : subst (λ z → El (B z)) ret-path val0 ≡ subst (λ z → El (B z)) s-path val0
              subst-eq i = subst (λ z → El (B z)) (path-eq i) val0

            in (subst-eq ∙ s-subst-eq))

          goal = cong (invEq (PiIso (A x) (λ z → B (invEq (SigIso Γ A) (x , z))))) inner-eq ∙ retEq (PiIso (A x) (λ y → B (invEq (SigIso Γ A) (x , y)))) (F x)
        in goal)
    in isoToEquiv (iso fun inv sec ret)

  U-Π .Π-Structure-CwF.pi-iso-nat = {!!}
