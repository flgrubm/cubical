module Cubical.Categories.WithFamilies.Structure.Sigma.FromUniverse where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Function

open import Cubical.Data.Sigma.Properties

open import Cubical.Categories.WithFamilies.Base
import Cubical.Categories.WithFamilies.FromUniverse as FU
open import Cubical.Categories.WithFamilies.Structure.Sigma.Base

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
         where
  open FU.Internal U USet El ElSet Unit UnitTerminal Sig SigIso

  U-Σ : Σ-Structure-CwF UCwF
  U-Σ .Σ-Structure-CwF.idsubst-action _ x = x
  U-Σ .Σ-Structure-CwF.sig Γ A B x = Sig (A x) (λ a → B (invEq (SigIso Γ A) (x , a)))

  U-Σ .Σ-Structure-CwF.sig-nat {Γ} {Δ} A B σ = funExt (λ x → cong (Sig (A (σ x))) (funExt (λ y → cong (λ m → B (invEq (SigIso Γ A) m)) (let
      -- the same as ctxExtFunctorHomDestructured, but in a let binding so it reduces more
      destructured : (Γ' Δ' : U) (A' : El Γ' → U) (B' : El Δ' → U) → (Σ[ f ∈ (El Γ' → El Δ') ] (λ a → B' (f a)) ≡ A') → (Σ[ x ∈ El Γ' ] El (A' x)) → (Σ[ x ∈ El Δ' ] El (B' x)) 
      destructured _ _ _ _ (f , p) (x , a) = (f x) , (subst⁻ El (funExt⁻ p x) a)

      r : Σ[ v ∈ El Γ ] El (A v)
      r = (σ x , y)
      
      s : Σ[ v ∈ El Γ ] El (A v)
      s = σ x , subst⁻ El refl y

      t : Σ[ v ∈ El Γ ] El (A v)
      t = destructured Δ Γ (λ x₁ → A (σ x₁)) A (σ , (λ _ x₁ → A (σ x₁))) (SigIso Δ (λ x₁ → A (σ x₁)) .fst (invEq (SigIso Δ (λ x₁ → A (σ x₁))) (x , y)))

      s≡r : s ≡ r
      s≡r = cong (λ m → σ x , m) (substRefl {B = El} y)
      
      t≡s : t ≡ s
      t≡s = cong (destructured Δ Γ (λ x₁ → A (σ x₁)) A (σ , (λ _ x₁ → A (σ x₁)))) (secEq (SigIso Δ (λ x₁ → A (σ x₁))) (x , y))
      
      goal : r ≡ t
      goal = sym (t≡s ∙ s≡r)
    in goal))))

  U-Σ .Σ-Structure-CwF.sig-iso {Γ} A B = let
      iso1 : Iso ((x : El Γ) → El (Sig (A x) (λ a → B (invEq (SigIso Γ A) (x , a)))))
                 ((x : El Γ) → Σ[ a ∈ El (A x) ] El (B (invEq (SigIso Γ A) (x , a))))
      iso1 = codomainIsoDep (λ x → equivToIso (SigIso (A x) (λ a → B (invEq (SigIso Γ A) (x , a)))))
      
      iso2 : Iso ((x : El Γ) → Σ[ a ∈ El (A x) ] El (B (invEq (SigIso Γ A) (x , a))))
                 (Σ[ v ∈ ((x : El Γ) → El (A x)) ] ((x : El Γ) → El (B (invEq (SigIso Γ A) (x , v x)))))
      iso2 = Σ-Π-Iso

      -- fun : ((x : El Γ) →
      --         El (Sig (A x) (λ a → B (invEq (SigIso Γ A) (x , a)))))
      --       → Σ ((x : El Γ) → El (A x))
      --            (λ v → (x : El Γ) → El (B (invEq (SigIso Γ A) (x , v x))))
      -- fun F = (λ x → SigIso (A x) (λ a → B (invEq (SigIso Γ A) (x , a))) .fst (F x) .fst) , λ x → SigIso (A x) (λ a → B (invEq (SigIso Γ A) (x , a))) .fst (F x) .snd

      -- inv : Σ ((x : El Γ) → El (A x)) (λ v → (x : El Γ) → El (B (invEq (SigIso Γ A) (x , v x)))) 
      --       → ((x : El Γ) → El (Sig (A x) (λ a → B (invEq (SigIso Γ A) (x , a)))))
      -- inv (a , b) x = invEq (SigIso (A x) (λ a → B (invEq (SigIso Γ A) (x , a)))) (a x , b x)

      -- sec : (s : Σ ((x : El Γ) → El (A x)) (λ v → (x : El Γ) → El (B (invEq (SigIso Γ A) (x , v x))))) → fun (inv s) ≡ s 
      -- sec (a , b) = let
      --     f : (a₁ : El Γ) → Σ (El (A a₁)) (λ x → El (B (invEq (SigIso Γ A) (a₁ , x))))
      --     f x = SigIso (A x) (λ a₁ → B (invEq (SigIso Γ A) (x , a₁))) .fst (invEq (SigIso (A x) (λ a₁ → B (invEq (SigIso Γ A) (x , a₁)))) (a x , b x))

      --     p : f ≡ (λ x → (a x , b x))
      --     p = funExt (λ x → secEq (SigIso (A x) (λ a₁ → B (invEq (SigIso Γ A) (x , a₁)))) (a x , b x))

      --     goal : (fst ∘ f , snd ∘ f) ≡ (a , b)
      --     goal i = fst ∘ (p i) , snd ∘ (p i)
      --   in goal

      -- ret : (F : (x : El Γ) → El (Sig (A x) (λ a → B (invEq (SigIso Γ A) (x , a))))) → inv (fun F) ≡ F
      -- ret F = funExt (λ x → retEq (SigIso (A x) (λ a → B (invEq (SigIso Γ A) (x , a)))) (F x))
    in isoToEquiv (compIso iso1 iso2) -- (iso fun inv sec ret)

  -- U-Σ .Σ-Structure-CwF.sig-iso {Γ} A B = isoToEquiv isom
  --   where
  --     isom : Iso ((x : El Γ) → El (Sig (A x) (λ a → B (invEq (SigIso Γ A) (x , a)))))
  --                (Σ ((x : El Γ) → El (A x)) (λ a → (x : El Γ) → El (B (invEq (SigIso Γ A) (x , a x)))))
  --     isom .Iso.fun F .fst x = SigIso (A x) (λ a → B (invEq (SigIso Γ A) (x , a))) .fst (F x) .fst
  --     isom .Iso.fun F .snd x = SigIso (A x) (λ a → B (invEq (SigIso Γ A) (x , a))) .fst (F x) .snd
  --     isom .Iso.inv (a , b) x = invEq (SigIso (A x) (λ a → B (invEq (SigIso Γ A) (x , a)))) (a x , b x)
  --     isom .Iso.sec (a , b) = goal
  --       where
  --         f : (a₁ : El Γ) → Σ (El (A a₁)) (λ x → El (B (invEq (SigIso Γ A) (a₁ , x))))
  --         f x = SigIso (A x) (λ a₁ → B (invEq (SigIso Γ A) (x , a₁))) .fst (invEq (SigIso (A x) (λ a₁ → B (invEq (SigIso Γ A) (x , a₁)))) (a x , b x))

  --         p : f ≡ (λ x → (a x , b x))
  --         p = funExt (λ x → secEq (SigIso (A x) (λ a₁ → B (invEq (SigIso Γ A) (x , a₁)))) (a x , b x))

  --         goal : (fst ∘ f , snd ∘ f) ≡ (a , b)
  --         goal i .fst = fst ∘ (p i)
  --         goal i .snd = snd ∘ (p i)
  --     isom .Iso.ret F = funExt goal
  --       where
  --         goal : (x : El Γ) →
  --                 invEq
  --                 (SigIso (A x) (λ a → B (invEq (SigIso Γ A) (x , a))))
  --                 (SigIso (A x)
  --                  (λ a → B (invEq (SigIso Γ A) (x , a))) .fst
  --                  (F x))
  --                 ≡ F x
  --         goal x = retEq (SigIso (A x) (λ a → B (invEq (SigIso Γ A) (x , a)))) (F x)

  U-Σ .Σ-Structure-CwF.ctxExtSubstSigmaSndEq {Γ} {Δ} A B a σ = funExt (λ x → let
      -- the same as ctxExtFunctorHomDestructured, but in a let binding so it reduces more
      destructured : (Γ' Δ' : U) (A' : El Γ' → U) (B' : El Δ' → U) → (Σ[ f ∈ (El Γ' → El Δ') ] (λ a → B' (f a)) ≡ A') → (Σ[ x ∈ El Γ' ] El (A' x)) → (Σ[ x ∈ El Δ' ] El (B' x)) 
      destructured _ _ _ _ (f , p) (x , a) = (f x) , (subst⁻ El (funExt⁻ p x) a)

      r : U
      r = B (invEq (SigIso Δ A) (σ x , a (σ x)))

      s : U
      s = B (invEq (SigIso Δ A) (σ x , subst⁻ El refl (a (σ x))))

      s' : U
      s' = B (invEq (SigIso Δ A) (destructured Γ Δ (λ x₁ → A (σ x₁)) A (σ , (λ _ x₁ → A (σ x₁))) ((x , a (σ x)))))

      s≡s' : s ≡ s'
      s≡s' = refl

      t : U
      t = B (invEq (SigIso Δ A) (destructured Γ Δ (λ x₁ → A (σ x₁)) A (σ , (λ _ x₁ → A (σ x₁))) (SigIso Γ (λ x₁ → A (σ x₁)) .fst (invEq (SigIso Γ (λ x₁ → A (σ x₁))) (x , a (σ x))))))

      u : U
      u = B (invEq (SigIso Δ A) (destructured Γ Δ (λ x₁ → A (σ x₁)) A (σ , (λ _ x₁ → A (σ x₁))) (SigIso Γ (λ x₁ → A (σ x₁)) .fst (invEq (SigIso Γ (λ x₁ → A (σ x₁))) (x , subst⁻ El refl (a (σ x)))))))

      s≡r : s ≡ r
      s≡r = cong (λ m → B (invEq (SigIso Δ A) (σ x , m))) (substRefl {B = El} (a (σ x)))

      t≡s : t ≡ s
      t≡s = cong (λ m → B (invEq (SigIso Δ A) (destructured Γ Δ (λ x₁ → A (σ x₁)) A (σ , (λ _ x₁ → A (σ x₁))) m))) (secEq (SigIso Γ (λ x₁ → A (σ x₁))) (x , a (σ x)))

      u≡t : u ≡ t
      u≡t = cong (λ m → B (invEq (SigIso Δ A) (destructured Γ Δ (λ x₁ → A (σ x₁)) A (σ , (λ _ x₁ → A (σ x₁))) (SigIso Γ (λ x₁ → A (σ x₁)) .fst (invEq (SigIso Γ (λ x₁ → A (σ x₁))) (x , m)))))) (substRefl {B = El} (a (σ x)))
      
      goal : r ≡ u
      goal = sym (u≡t ∙∙ t≡s ∙∙ s≡r)
    in goal)
      
  U-Σ .Σ-Structure-CwF.sig-iso-nat {Δ} {Γ} A B m f = goal
    where
      -- the same as ctxExtFunctorHomDestructured, but in a let binding so it reduces more
      destructured : (Γ' Δ' : U) (A' : El Γ' → U) (B' : El Δ' → U) → (Σ[ f ∈ (El Γ' → El Δ') ] (λ a → B' (f a)) ≡ A') → (Σ[ x ∈ El Γ' ] El (A' x)) → (Σ[ x ∈ El Δ' ] El (B' x)) 
      destructured _ _ _ _ (f , p) (x , a) = (f x) , (subst⁻ El (funExt⁻ p x) a)

      module FollowTheElement where
        l1 : (x : El Δ) →
              El ((UCwF CwF.∘Ty (λ z → U-Σ .Σ-Structure-CwF.sig Γ A B z)) f x)
        l1 = λ x → subst El refl (m (f x))

        l1≡ : CwF._[_] UCwF m f ≡ l1
        l1≡ = refl

        l1' : (x : El Δ) →
               El ((UCwF CwF.∘Ty (λ z → U-Σ .Σ-Structure-CwF.sig Γ A B z)) f x)
        l1' x = m (f x)

        l1≡l1' : l1 ≡ l1'
        l1≡l1' = funExt (λ x → substRefl {B = El} (m (f x)))

        l2 : (x : El Δ) →
              El
              (U-Σ .Σ-Structure-CwF.sig Δ ((UCwF CwF.∘Ty A) f)
               ((UCwF CwF.∘Ty B) (CwF.⟨ UCwF , f ⟩ A)) x)
        l2 = subst (CwF.Tm UCwF Δ) (U-Σ .Σ-Structure-CwF.sig-nat A B f) l1

        l2' : (x : El Δ) →
              El
              (U-Σ .Σ-Structure-CwF.sig Δ ((UCwF CwF.∘Ty A) f)
               ((UCwF CwF.∘Ty B) (CwF.⟨ UCwF , f ⟩ A)) x)
        l2' = subst (CwF.Tm UCwF Δ) (U-Σ .Σ-Structure-CwF.sig-nat A B f) l1'

        l2≡l2' : l2 ≡ l2'
        l2≡l2' = cong (subst (CwF.Tm UCwF Δ) (U-Σ .Σ-Structure-CwF.sig-nat A B f)) l1≡l1'

        l3 : Σ (CwF.Tm UCwF Δ ((UCwF CwF.∘Ty A) f))
              (λ a →
                 CwF.Tm UCwF Δ
                 ((UCwF CwF.∘Ty (UCwF CwF.∘Ty B) (CwF.⟨ UCwF , f ⟩ A))
                  (CwF.ctxExtSubst UCwF ((UCwF CwF.∘Ty A) f) (CwF.IdSubst UCwF)
                   (U-Σ .Σ-Structure-CwF.idsubst-action ((UCwF CwF.∘Ty A) f) a))))
        l3 = U-Σ .Σ-Structure-CwF.sig-iso (CwF._∘Ty_ UCwF A f) (CwF._∘Ty_ UCwF B (CwF.⟨_,_⟩ UCwF f A)) .fst l2

        l3' : Σ (CwF.Tm UCwF Δ ((UCwF CwF.∘Ty A) f))
              (λ a →
                 CwF.Tm UCwF Δ
                 ((UCwF CwF.∘Ty (UCwF CwF.∘Ty B) (CwF.⟨ UCwF , f ⟩ A))
                  (CwF.ctxExtSubst UCwF ((UCwF CwF.∘Ty A) f) (CwF.IdSubst UCwF)
                   (U-Σ .Σ-Structure-CwF.idsubst-action ((UCwF CwF.∘Ty A) f) a))))
        l3' = U-Σ .Σ-Structure-CwF.sig-iso (CwF._∘Ty_ UCwF A f) (CwF._∘Ty_ UCwF B (CwF.⟨_,_⟩ UCwF f A)) .fst l2'

        l3≡l3' : l3 ≡ l3'
        l3≡l3' = cong (U-Σ .Σ-Structure-CwF.sig-iso (CwF._∘Ty_ UCwF A f) (CwF._∘Ty_ UCwF B (CwF.⟨_,_⟩ UCwF f A)) .fst) l2≡l2'

        r1 : (Σ[ a ∈ ((x : El Γ) → El (A x)) ] ((x : El Γ) → El (B (invEq (SigIso Γ A) (x , a x)))))
        r1 = U-Σ .Σ-Structure-CwF.sig-iso A B .fst m

        r2 : (Σ[ a ∈ ((x : El Γ) → El (A x)) ] ((x : El Δ) → El (B (invEq (SigIso Γ A) (f x , a (f x))))))
        r2 .fst = r1 .fst
        r2 .snd x = subst El refl (r1 .snd (f x))
        
        r2≡ : (r1 .fst , λ x → CwF._[_] UCwF (r1 .snd) f x) ≡ r2
        r2≡ = refl

        r2' : (Σ[ a ∈ ((x : El Γ) → El (A x)) ] ((x : El Δ) → El (B (invEq (SigIso Γ A) (f x , a (f x))))))
        r2' .fst = r1 .fst
        r2' .snd x = r1 .snd (f x)

        r2≡r2' : r2 ≡ r2'
        r2≡r2' = ΣPathP (refl , (funExt (λ x → substRefl {B = El} (r1 .snd (f x)))))

        r3 : (Σ[ a ∈ ((x : El Γ) → El (A x)) ] ((x : El Δ) → El (B (invEq (SigIso Γ A) (destructured Δ Γ (λ x₁ → A (f x₁)) A (f , refl) (SigIso Δ (λ x₁ → A (f x₁)) .fst (invEq (SigIso Δ (λ x₁ → A (f x₁))) (x , subst⁻ El refl (a (f x))))))))))
             -- El (B (invEq (SigIso Γ A) (ctxExtFunctorHomDestructured Δ Γ (λ x₁ → A (f x₁)) A (f , refl) (SigIso Δ (λ x₁ → A (f x₁)) .fst (invEq (SigIso Δ (λ x₁ → A (f x₁))) (x , subst⁻ El refl (a (f x))))))))))
        r3 .fst = r2 .fst
        r3 .snd x = transport
                     (λ i →
                        El
                        (U-Σ .Σ-Structure-CwF.ctxExtSubstSigmaSndEq A B (r2 .fst) f i
                         (transp (λ j → El Δ) i x)))
                     (r2 .snd (transport refl x))
                     -- 

        r3≡ : (r2 .fst , subst (CwF.Tm UCwF Δ) (U-Σ .Σ-Structure-CwF.ctxExtSubstSigmaSndEq A B (r2 .fst) f) (r2 .snd)) ≡ r3
        r3≡ = refl

        r3' : Σ ((x : El Γ) → El (A x))
               (λ a →
                  (x : El Δ) →
                  El
                  (B
                   (invEq (SigIso Γ A)
                    (f
                     (SigIso Δ (λ x₁ → A (f x₁)) .fst
                      (invEq (SigIso Δ (λ x₁ → A (f x₁)))
                       (x , subst⁻ El refl (a (f x))))
                      .fst)
                     ,
                     subst El refl
                     (SigIso Δ (λ x₁ → A (f x₁)) .fst
                      (invEq (SigIso Δ (λ x₁ → A (f x₁)))
                       (x , subst⁻ El refl (a (f x))))
                      .snd)))))
        r3' .fst = r2' .fst
        r3' .snd x = transport
                      (λ i →
                         El
                         (U-Σ .Σ-Structure-CwF.ctxExtSubstSigmaSndEq A B (r2' .fst) f i
                          (transp (λ _ → El Δ) i x)))
                      (r2' .snd (transport (λ _ → El Δ) x))
        -- r3' .fst = r2' .fst
        -- r3' .snd x = transport
        --               (λ i →
        --                  El
        --                  (U-Σ .Σ-Structure-CwF.ctxExtSubstSigmaSndEq A B (r2' .fst) f i
        --                   (transp (λ j → El Δ) i x)))
        --               (r2' .snd (transport refl x))

        r3'≡ : (r2' .fst , subst (CwF.Tm UCwF Δ) (U-Σ .Σ-Structure-CwF.ctxExtSubstSigmaSndEq A B (r2' .fst) f) (r2' .snd)) ≡ r3'
        r3'≡ = refl

        r3≡r3' : r3 ≡ r3'
        r3≡r3' = ΣPathP (refl , funExt (λ x → cong (λ r → transport (λ i → El (U-Σ .Σ-Structure-CwF.ctxExtSubstSigmaSndEq A B (r .fst) f i (transp (λ j → El Δ) i x))) (r .snd (transport refl x))) r2≡r2'))

        r3'' : Σ ((x : El Γ) → El (A x))
               (λ a →
                  (x : El Δ) →
                  El
                  (B
                   (invEq (SigIso Γ A)
                    (f
                     (SigIso Δ (λ x₁ → A (f x₁)) .fst
                      (invEq (SigIso Δ (λ x₁ → A (f x₁)))
                       (x , subst⁻ El refl (a (f x))))
                      .fst)
                     ,
                     subst El refl
                     (SigIso Δ (λ x₁ → A (f x₁)) .fst
                      (invEq (SigIso Δ (λ x₁ → A (f x₁)))
                       (x , subst⁻ El refl (a (f x))))
                      .snd)))))

        r3'' .fst = r2' .fst
        r3'' .snd x = transport
                      (λ i →
                         El
                         (U-Σ .Σ-Structure-CwF.ctxExtSubstSigmaSndEq A B (r2' .fst) f i
                           (transp (λ k → El Δ) i x)))
                      (r2' .snd (transport refl x))

        r4 : Σ ((x : El Δ) → El (A (f x))) λ a →
                                              (x : El Δ) →
                                              El
                                              (B
                                               (invEq (SigIso Γ A)
                                                (f
                                                 (SigIso Δ (λ x₁ → A (f x₁)) .fst
                                                  (invEq (SigIso Δ (λ x₁ → A (f x₁))) (x , a x))
                                                  .fst)
                                                 ,
                                                 subst⁻ El refl
                                                 (SigIso Δ (λ x₁ → A (f x₁)) .fst
                                                  (invEq (SigIso Δ (λ x₁ → A (f x₁))) (x , a x))
                                                  .snd))))
        r4 .fst = λ x → subst El refl (r3 .fst (f x))
        r4 .snd = r3 .snd

        r4≡ : (CwF._[_] UCwF (r3 .fst) f , r3 .snd) ≡ r4
        r4≡ = refl

        r4Copy : Σ (CwF.Tm UCwF Δ ((UCwF CwF.∘Ty A) f))
              (λ a →
                 CwF.Tm UCwF Δ
                 ((UCwF CwF.∘Ty (UCwF CwF.∘Ty B) (CwF.⟨ UCwF , f ⟩ A))
                  (CwF.ctxExtSubst UCwF ((UCwF CwF.∘Ty A) f) (CwF.IdSubst UCwF)
                   (U-Σ .Σ-Structure-CwF.idsubst-action ((UCwF CwF.∘Ty A) f) a))))

        r4Copy .fst = λ x → subst El refl (fst
                                           (SigIso (A (f x))
                                            (λ a → B (invEq (SigIso Γ A) (f x , a))) .fst
                                            (m (f x))))
        r4Copy .snd = λ x →
                         transport
                         (λ i →
                            El
                            (U-Σ .Σ-Structure-CwF.ctxExtSubstSigmaSndEq A B (r2 .fst) f i
                             (transp (λ j → El Δ) i x)))
                         (r2 .snd (transport (λ _ → El Δ) x))

        r4≡Copy : r4 ≡ r4Copy
        r4≡Copy = refl

        l3'Copy : Σ ((x : El Δ) → El (A (f x))) λ a →
                                                   (x : El Δ) →
                                                   El
                                                   (B
                                                    (invEq (SigIso Γ A)
                                                     (f
                                                      (SigIso Δ (λ x₁ → A (f x₁)) .fst
                                                       (invEq (SigIso Δ (λ x₁ → A (f x₁))) (x , a x))
                                                       .fst)
                                                      ,
                                                      subst⁻ El refl
                                                      (SigIso Δ (λ x₁ → A (f x₁)) .fst
                                                       (invEq (SigIso Δ (λ x₁ → A (f x₁))) (x , a x))
                                                       .snd))))
                  -- Σ (CwF.Tm UCwF Δ ((UCwF CwF.∘Ty A) f))
                  --  (λ a →
                  --     CwF.Tm UCwF Δ
                  --     ((UCwF CwF.∘Ty (UCwF CwF.∘Ty B) (CwF.⟨ UCwF , f ⟩ A))
                  --      (CwF.ctxExtSubst UCwF ((UCwF CwF.∘Ty A) f) (CwF.IdSubst UCwF) a)))
        l3'Copy .fst = λ x →
                          fst
                          (SigIso (A (f x))
                           (λ a →
                              B
                              (invEq (SigIso Γ A)
                               (f
                                (SigIso Δ (λ x₁ → A (f x₁)) .fst
                                 (invEq (SigIso Δ (λ x₁ → A (f x₁))) (x , a))
                                 .fst)
                                ,
                                transport refl
                                  (SigIso Δ (λ x₁ → A (f x₁)) .fst
                                    (invEq (SigIso Δ (λ x₁ → A (f x₁))) (x , a))
                                    .snd))))
                           .fst
                           (transport
                            (λ i →
                               El
                               (Sig (A (f (transp (λ _ → El Δ) i x)))
                                (λ x₁ →
                                   B
                                   (invEq (SigIso Γ A)
                                    (hcomp
                                     (doubleComp-faces
                                      (λ _ →
                                         f
                                         (SigIso Δ (λ x₂ → A (f x₂)) .fst
                                          (invEq (SigIso Δ (λ x₂ → A (f x₂)))
                                           (transp (λ _ → El Δ) i x , x₁))
                                          .fst)
                                         ,
                                         transport refl
                                         (SigIso Δ (λ x₂ → A (f x₂)) .fst
                                          (invEq (SigIso Δ (λ x₂ → A (f x₂)))
                                           (transp (λ _ → El Δ) i x , x₁))
                                          .snd))
                                      (λ i₁ →
                                         f (transp (λ _ → El Δ) i x) ,
                                         transp (λ _ → El (A (f (transp (λ _ → El Δ) i x)))) i₁ x₁)
                                      (~ i))
                                     (f
                                      (snd (SigIso Δ (λ x₂ → A (f x₂))) .equiv-proof
                                       (transp (λ _ → El Δ) i x , x₁) .fst .snd (~ i) .fst)
                                      ,
                                      transport refl
                                      (snd (SigIso Δ (λ x₂ → A (f x₂))) .equiv-proof
                                       (transp (λ _ → El Δ) i x , x₁) .fst .snd (~ i) .snd)))))))
                            (m (f (transport (λ _ → El Δ) x)))))
        l3'Copy .snd x = snd
                          (SigIso (A (f x))
                           (λ a →
                              B
                              (invEq (SigIso Γ A)
                               (f
                                (SigIso Δ (λ x₁ → A (f x₁)) .fst
                                 (invEq (SigIso Δ (λ x₁ → A (f x₁))) (x , a))
                                 .fst)
                                ,
                                transport
                                (λ i →
                                   El
                                   (A
                                    (f
                                     (SigIso Δ (λ x₁ → A (f x₁)) .fst
                                      (invEq (SigIso Δ (λ x₁ → A (f x₁))) (x , a))
                                      .fst))))
                                (SigIso Δ (λ x₁ → A (f x₁)) .fst
                                 (invEq (SigIso Δ (λ x₁ → A (f x₁))) (x , a))
                                 .snd))))
                           .fst
                           (transport
                            (λ i →
                               El
                               (Sig (A (f (transp (λ _ → El Δ) i x)))
                                (λ x₁ →
                                   B
                                   (invEq (SigIso Γ A)
                                    (hcomp
                                     (doubleComp-faces
                                      (λ _ →
                                         f
                                         (SigIso Δ (λ x₂ → A (f x₂)) .fst
                                          (invEq (SigIso Δ (λ x₂ → A (f x₂)))
                                           (transp (λ j → El Δ) i x , x₁))
                                          .fst)
                                         ,
                                         transport
                                         (λ i₁ →
                                            El
                                            (A
                                             (f
                                              (SigIso Δ (λ x₂ → A (f x₂)) .fst
                                               (invEq (SigIso Δ (λ x₂ → A (f x₂)))
                                                (transp (λ _ → El Δ) i x , x₁))
                                               .fst))))
                                         (SigIso Δ (λ x₂ → A (f x₂)) .fst
                                          (invEq (SigIso Δ (λ x₂ → A (f x₂)))
                                           (transp (λ _ → El Δ) i x , x₁))
                                          .snd))
                                      (λ i₁ →
                                         f (transp (λ _ → El Δ) i x) ,
                                         transp (λ _ → El (A (f (transp (λ _ → El Δ) i x)))) i₁ x₁)
                                      (~ i))
                                     (f
                                      (snd (SigIso Δ (λ x₂ → A (f x₂))) .equiv-proof
                                       (transp (λ _ → El Δ) i x , x₁) .fst .snd (~ i) .fst)
                                      ,
                                      transport refl
                                      (snd (SigIso Δ (λ x₂ → A (f x₂))) .equiv-proof
                                       (transp (λ _ → El Δ) i x , x₁) .fst .snd (~ i) .snd)))))))
                            (m (f (transport (λ _ → El Δ) x)))))

        l3'≡Copy : l3' ≡ l3'Copy
        l3'≡Copy = refl

      goal : FollowTheElement.l3
              ≡
             FollowTheElement.r4
      goal = {!!} -- ΣPathP (funExt (λ x → {!!}) , {!!})
























      test1 : CwF.Tm UCwF Γ (U-Σ .Σ-Structure-CwF.sig Γ A B) ≡ ((x : El Γ) → El (Sig (A x) (λ a → B (invEq (SigIso Γ A) (x , a)))))
      test1 = refl

      test2 : CwF.Tm UCwF Δ (CwF._∘Ty_ UCwF (U-Σ .Σ-Structure-CwF.sig Γ A B) f) ≡ ((x : El Δ) → El (Sig (A (f x)) (λ a → B (invEq (SigIso Γ A) (f x , a)))))
      test2 = refl

      test3 : CwF.Tm UCwF Δ (U-Σ .Σ-Structure-CwF.sig Δ (CwF._∘Ty_ UCwF A f) (CwF._∘Ty_ UCwF B (CwF.⟨_,_⟩ UCwF f A))) ≡ ((x : El Δ) →
        El (
          Sig (A (f x)) (
            λ a → B (
              invEq (SigIso Γ A) (
                f (
                  SigIso Δ (λ x₁ → A (f x₁)) .fst (
                    invEq (SigIso Δ (λ x₁ → A (f x₁))) (x , a))
                  .fst)
                , subst⁻ El refl (
                  SigIso Δ (λ x₁ → A (f x₁)) .fst (
                    invEq (SigIso Δ (λ x₁ → A (f x₁))) (x , a))
                  .snd))))))
      test3 = refl

      testA : (Σ[ a ∈ CwF.Tm UCwF Γ A ] CwF.Tm UCwF Γ (CwF._∘Ty_ UCwF B (CwF.ctxExtSubst UCwF A (idfun (El Γ)) a)))
              ≡
              (Σ[ a ∈ ((x : El Γ) → El (A x)) ] ((x : El Γ) → El (B (invEq (SigIso Γ A) (x , a x)))))
      testA = refl

      testB : (Σ[ a ∈ CwF.Tm UCwF Γ A ] CwF.Tm UCwF Δ (CwF._∘Ty_ UCwF (CwF._∘Ty_ UCwF B (CwF.ctxExtSubst UCwF A (idfun (El Γ)) a)) f))
        ≡
        (Σ[ a ∈ ((x : El Γ) → El (A x)) ] ((x : El Δ) → El (B (invEq (SigIso Γ A) (f x , a (f x))))))
      testB = refl

      testC : (Σ[ a ∈ CwF.Tm UCwF Γ A ] CwF.Tm UCwF Δ (CwF._∘Ty_ UCwF B (CwF.ctxExtSubst UCwF A f (CwF._[_] UCwF a f))))
        ≡
        (Σ[ a ∈ ((x : El Γ) → El (A x)) ] ((x : El Δ) → El (B (invEq (SigIso Γ A) (f x , subst⁻ El refl (a (f x)))))))
      testC = refl

      testD : (Σ[ a ∈ CwF.Tm UCwF Γ A ] CwF.Tm UCwF Δ (CwF._∘Ty_ UCwF (CwF._∘Ty_ UCwF B (CwF.⟨_,_⟩ UCwF f A)) (CwF.ctxExtSubst UCwF (CwF._∘Ty_ UCwF A f) (idfun (El Δ)) (CwF._[_] UCwF a f))))
        ≡
        (Σ[ a ∈ ((x : El Γ) → El (A x)) ] ((x : El Δ) → El (B (invEq (SigIso Γ A) (ctxExtFunctorHomDestructured Δ Γ (λ x₁ → A (f x₁)) A (f , refl) (SigIso Δ (λ x₁ → A (f x₁)) .fst (invEq (SigIso Δ (λ x₁ → A (f x₁))) (x , subst⁻ El refl (a (f x))))))))))
      testD = refl
