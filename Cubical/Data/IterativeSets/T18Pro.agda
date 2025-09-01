module Cubical.Data.IterativeSets.T18Pro where
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

open import Cubical.Data.Sigma

-- open import Cubical.

open import Cubical.Homotopy.Base

open import Cubical.Data.W.W

open import Cubical.Data.IterativeSets.Base

private
  variable
    ℓ ℓ' ℓ'' : Level

module _ where
    postulate compEmbedding-precompose-id↪ : {ℓA ℓB : Level} {A : Type ℓA} {B : Type ℓB} (Embf : A ↪ B) → compEmbedding Embf (id↪ A) ≡ Embf
    -- compEmbedding-precompose-id↪ {A = A} {B = B} (f , femb) = ΣPathP (refl , (
    --     snd (compEmbedding (f , femb) (id↪ A))
    --         ≡⟨⟩
    --     isEmbedding-∘ femb (id↪ A .snd)
    --         ≡⟨⟩
    --     isEmbedding-∘ femb (Equiv→Embedding (idEquiv A) .snd)
    --         ≡⟨⟩
    --     isEmbedding-∘ femb (Equiv→Embedding (idfun A , idIsEquiv A) .snd)
    --         ≡⟨⟩
    --     isEmbedding-∘ femb (isEquiv→isEmbedding (idIsEquiv A))
    --         ≡⟨⟩
    --     (λ w x → {!compEquiv (cong idfun , (isEquiv→isEmbedding (idIsEquiv A))) (cong f , femb (idfun w) (idfun x))!})
    --         ≡⟨ {!!} ⟩
    --     femb
    --         ∎))

    postulate compEmbedding-postcompose-id↪ : {ℓA ℓB : Level} {A : Type ℓA} {B : Type ℓB} (Embf : A ↪ B) → compEmbedding (id↪ B) Embf ≡ Embf

pro18'' : {ℓ : Level} → {A : Type ℓ} → ((A ↪ V⁰ {ℓ}) ≃ (Σ[ a ∈ V⁰ {ℓ} ] El⁰ a ≡ A))
pro18'' {ℓ = ℓ} {A = A} = isoToEquiv (iso (α {ℓ' = ℓ} A) (β {ℓ' = ℓ} A) (sec {ℓ' = ℓ} A) (ret {ℓ' = ℓ} A))
    where
        α : {ℓ' : Level} (B : Type ℓ') → (B ↪ V⁰ {ℓ'}) → (Σ[ a ∈ V⁰ {ℓ'} ] El⁰ a ≡ B)
        α B emb = sup⁰ (B , emb) , refl

        β : {ℓ' : Level} (B : Type ℓ') → (Σ[ a ∈ V⁰ {ℓ'} ] El⁰ a ≡ B) → (B ↪ V⁰ {ℓ'})
        β B (a , p) = compEmbedding (desup⁰' a) (Equiv→Embedding (pathToEquiv (sym p)))

        -- sec-helper' : {ℓ' : Level} → (a : V⁰ {ℓ'}) → (B : Type ℓ') → (p : El⁰ a ≡ B) → α B (β B (a , p)) ≡ (a , p)
        -- sec-helper' a = J> (
        --     α (El⁰ a) (β (El⁰ a) (a , refl))
        --         ≡⟨⟩
        --     α (El⁰ a) (compEmbedding (desup⁰' a) (Equiv→Embedding (pathToEquiv (sym refl))))
        --         ≡⟨⟩
        --     sup⁰ (El⁰ a , compEmbedding (desup⁰' a) (Equiv→Embedding (pathToEquiv (sym refl)))) , _
        --         ≡⟨⟩
        --     sup⁰ (El⁰ a , compEmbedding (desup⁰' a) (Equiv→Embedding (pathToEquiv refl))) , _
        --         ≡⟨ cong (λ s → sup⁰ (El⁰ a , compEmbedding (desup⁰' a) (Equiv→Embedding s)) , _) pathToEquivRefl ⟩
        --     sup⁰ (El⁰ a , compEmbedding (desup⁰' a) (Equiv→Embedding (idEquiv (El⁰ a)))) , refl
        --         ≡⟨⟩
        --     sup⁰ (El⁰ a , compEmbedding (desup⁰' a) (id↪ (El⁰ a))) , refl
        --         ≡⟨ cong (λ s → sup⁰ (El⁰ a , s) , refl) (compEmbedding-precompose-id↪ _) ⟩
        --     sup⁰ (El⁰ a , desup⁰' a) , refl
        --         ≡⟨ {!!} ⟩
        --     sup⁰ (desup⁰ a) , _
        --         ≡⟨ cong (λ s → s , _) (retEq sup⁰desup⁰≃ a) ⟩
        --     a , refl
        --         ∎)

        sec-helper : {ℓ' : Level} → (a : V⁰ {ℓ'}) → (B : Type ℓ') → (p : El⁰ a ≡ B) → α B (β B (a , p)) ≡ (a , p)
        sec-helper (sup-W D f , its) = J> (
            α D (β D ((sup-W D f , its) , refl))
                ≡⟨⟩
            α D (compEmbedding (desup⁰' (sup-W D f , its)) (Equiv→Embedding (pathToEquiv (sym refl))))
                ≡⟨⟩
            sup⁰ (D , compEmbedding (desup⁰' (sup-W D f , its)) (Equiv→Embedding (pathToEquiv (sym refl)))) , _
                ≡⟨⟩
            sup⁰ (D , compEmbedding (desup⁰' (sup-W D f , its)) (Equiv→Embedding (pathToEquiv refl))) , _
                ≡⟨ cong (λ s → sup⁰ (D , compEmbedding (desup⁰' (sup-W D f , its)) (Equiv→Embedding s)) , _) pathToEquivRefl ⟩
            sup⁰ (D , compEmbedding (desup⁰' (sup-W D f , its)) (Equiv→Embedding (idEquiv D))) , _
                ≡⟨⟩
            sup⁰ (D , compEmbedding (desup⁰' (sup-W D f , its)) (id↪ D)) , _
                ≡⟨ cong (λ s → sup⁰ (D , s) , _) (compEmbedding-precompose-id↪ _) ⟩
            sup⁰ (D , desup⁰' (sup-W D f , its)) , _
                ≡⟨⟩
            sup⁰ (desup⁰ (sup-W D f , its)) , _
                ≡⟨ cong (λ s → s , _) (retEq sup⁰desup⁰≃ (sup-W D f , its)) ⟩
            (sup-W D f , its) , _
                ∎)
        
        sec : {ℓ' : Level} (B : Type ℓ') → section (α {ℓ'} B) (β {ℓ'} B)
        sec B (a , p) = sec-helper a B p

        ret : {ℓ' : Level} (B : Type ℓ') → retract (α {ℓ'} B) (β {ℓ'} B)
        ret {ℓ'} B emb =
            β B (sup⁰ (B , emb) , refl) ≡⟨⟩
            compEmbedding (desup⁰' (sup⁰ (B , emb))) (Equiv→Embedding (pathToEquiv (sym refl)))
                ≡⟨⟩
            compEmbedding (desup⁰' (sup⁰ (B , emb))) (Equiv→Embedding (pathToEquiv refl))
                ≡⟨ cong (λ s → compEmbedding (desup⁰' (sup⁰ (B , emb))) (Equiv→Embedding s)) pathToEquivRefl ⟩
            compEmbedding (desup⁰' (sup⁰ (B , emb))) (Equiv→Embedding (idEquiv _))
                ≡⟨⟩
            compEmbedding (desup⁰' (sup⁰ (B , emb))) (id↪ _) ≡⟨ compEmbedding-precompose-id↪ _ ⟩
            -- {!!} ≡⟨ {!!} ⟩
            desup⁰' (sup⁰ (B , emb)) ≡⟨ cong snd (secEq sup⁰desup⁰≃ (B , emb)) ⟩
            emb ∎

pro18' : {ℓ : Level} → {A : Type ℓ} → ((A ↪ V⁰ {ℓ}) ≃ (Σ[ a ∈ V⁰ {ℓ} ] El⁰ a ≡ A))
pro18' {ℓ = ℓ} {A = A} = isoToEquiv (iso α β sec ret)
    where
        α : A ↪ V⁰ {ℓ} → Σ[ a ∈ V⁰ ]  El⁰ a ≡ A
        α emb = sup⁰ (A , emb) , refl

        β : Σ[ a ∈ V⁰ ] El⁰ a ≡ A → A ↪ V⁰ {ℓ}
        β (a , p) = J (λ B _ → B ↪ V⁰ {ℓ}) (desup⁰' a) p

        β' : Σ[ a ∈ V⁰ ] El⁰ a ≡ A → A ↪ V⁰ {ℓ}
        β' (a , p) = compEmbedding (desup⁰' a) (Equiv→Embedding (pathToEquiv (sym p)))

        -- sec' : (a : V⁰ {ℓ}) → (p : El⁰ a ≡ A) → α (β (a , p)) ≡ (a , p)
        -- sec' a p = J P d p
        --     where
        --         P : (B : Type ℓ) → El⁰ a ≡ B → Type (ℓ-suc ℓ)
        --         P B q = α (β (a , {!q!})) ≡ (a , {!!})
        --         d : P (El⁰ a) refl
        --         d = {!!}

        -- sec'-sym : (a : V⁰ {ℓ}) → (p : El⁰ a ≡ A) → α (β (a , p)) ≡ (a , p)
        -- sec'-sym a p = J P d (sym p)
        --     where
        --         P : (B : Type ℓ) → A ≡ B → Type (ℓ-suc ℓ)
        --         P B q = α (β (a , {!!})) ≡ (a , {!!})
        --         d : P (A) refl
        --         d = {!!}

        postulate sec : section α β
        -- sec (a , p) = sec' a p -- J (λ B p' → {!section α β!}) {!α (β (a , refl)) ≡⟨ ? ⟩ (a , refl) ∎!} p

        --     where
        --         secRefl : α (β ((a , refl) :> Σ[ a ∈ V⁰ {ℓ} ] El⁰ a ≡ A)) ≡ ((a , refl) :> Σ[ a ∈ V⁰ {ℓ} ] El⁰ a ≡ A)
        --         secRefl = ?
        -- -- sec' : section α β
        -- sec' (a , p) =
        --     α (β (a , p))
        --         ≡⟨⟩
        --     sup⁰ (A , β (a , p)) , refl
        --         ≡⟨ {!!} ⟩
        --     sup⁰ (A , compEmbedding (desup⁰' a) (Equiv→Embedding (pathToEquiv (sym p)))) , refl
        --         ≡⟨ {!!} ⟩
        --     a , p
        --         ∎
        ret : retract α β
        ret emb = JRefl (λ B _ → B ↪ V⁰ {ℓ}) (desup⁰' (sup⁰ (A , emb))) ∙ cong snd (secEq sup⁰desup⁰≃ (A , emb))
            -- β (α emb)
            --     ≡⟨⟩
            -- β (sup⁰ (A , emb) , refl)
            --     ≡⟨ JRefl (λ B _ → B ↪ V⁰ {ℓ}) (desup⁰' (sup⁰ (A , emb))) ⟩
            -- desup⁰' (sup⁰ (A , emb))
            --     ≡⟨⟩
            -- desup⁰ (sup⁰ (A , emb)) .snd
            --     ≡⟨ cong snd (secEq sup⁰desup⁰≃ (A , emb)) ⟩
            -- --(A , emb) .snd
            -- --     ≡⟨⟩
            -- emb
            --     ∎

-- trying out J rule
-- sym' : {A : Type ℓ} {x y : A} → x ≡ y → y ≡ x
-- sym' {A = A} {x = x} {y = y} = J {x = x} (λ z _ → z ≡ x) refl

-- symP' : {A : Type ℓ} {a : A} → Σ[ x ∈ A ] a ≡ x → Σ[ x ∈ A ] x ≡ a
-- symP' {A = A} {a = a} (x , p) = J {x = a} (λ y _ → Σ[ z ∈ A ] z ≡ a) {!!} p

