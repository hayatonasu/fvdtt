{-# OPTIONS --rewriting #-}

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; trans; sym; cong; cong-app; subst) renaming (refl to ≡refl)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _∎; step-≡)
open import Agda.Primitive 
open import Agda.Builtin.Nat
open import Agda.Builtin.Sigma

{-# BUILTIN REWRITE _≡_ #-}

module fvtt where

    _×_ : Set → Set → Set
    A × B = Σ A (λ _ → B)

    data Version : Set where 
        product : Version
        product+unit : Version
        product+unit+composition : Version
    
    data Type : Set 
    data Ctx : Set
    data Term : Ctx → Type → Set 
    data Termsubst : Ctx → Ctx → Set
    data Pro : Ctx → Ctx → Set
    data CtxSeq : Set 
    data ProCtx : CtxSeq → Set

    data Type where
        Unit : Type
        Prod : Type → Type → Type

    data Ctx where
        ε : Ctx -- empty context
        _′_ : Ctx → Type → Ctx -- Γ , x : A
    infixr 5 _′_

    _⋆_ : Ctx → Ctx → Ctx
    Γ ⋆ ε = Γ
    Γ ⋆ ( Δ ′ A ) = ( Γ ⋆ Δ ) ′ A
    infixr 6 _⋆_

    data CtxSeq where                                           -- Γ♪ = Γ₀ ; ... ; Γₙ
        ι : Ctx → CtxSeq                                        -- Γ♪ = Γ
        _⨾_ : CtxSeq → Ctx → CtxSeq                              -- Γ♪ = ( Γ­₀ ; ... ; Γₙ ) ⨾ Γ 
    infixr 4 _⨾_

    head : CtxSeq → Ctx                                          -- head Γ₀ ; ... ; Γₙ = Γ₀
    head (ι Γ) = Γ
    head (Γ ⨾ Δ) = head Γ

    tail : CtxSeq → Ctx                                          -- tail Γ₀ ; ... ; Γₙ = Γₙ
    tail (ι Γ) = Γ 
    tail (Γ♪ ⨾ Δ) = Δ

    _⨾-_ : (Γ♪ Δ♪ : CtxSeq) → CtxSeq                              -- (Γ₀ ; ... ; Γₙ) ⨾- (Δ₀ ; ... ; Δₙ) = Γ₀ ; ... ; Γₙ ; Δ₀ ; ... ; Δₙ
    Γ♪ ⨾- (ι Δ) = Γ♪ ⨾ Δ
    Γ♪ ⨾- (Δ♪ ⨾ Δ) = (Γ♪ ⨾- Δ♪) ⨾ Δ

    data preCtxSeqSeq : Set where                                -- Γ♩ = Γ ⨾pre (Γ₀⁰; ... ; Γ₀­ⁿ⁰) ⨾pre ... ⨾pre (Γ­ₘ⁰ ; ... ; Γₘ­ⁿᵐ) 
        ιpre : Ctx → preCtxSeqSeq                               
        _⨾pre_ : preCtxSeqSeq → CtxSeq → preCtxSeqSeq   

    headd : preCtxSeqSeq → Ctx 
    headd (ιpre Γ) = Γ
    headd (Γ♩ ⨾pre Δ♪) = headd Γ♩ 

    taill : preCtxSeqSeq → Ctx                                   -- taill ((Γ₀⁰; ... ; Γ₀­ⁿ⁰) ⨾pre ... ⨾pre (Γ­ₘ⁰ ; ... ; Γₘ­ⁿᵐ)) = Γₘ­ⁿᵐ
    taill (ιpre Γ) = Γ
    taill (Γ ⨾pre Δ) = tail Δ


    well-typed : preCtxSeqSeq → Set                               -- Γ₀ⁿ⁰=Γ₁⁰ × ... × Γₘ₋₁­ⁿ⁽ᵐ⁻¹⁾=Γₘ⁰
    well-typed (ιpre Γ) = 1 ≡ 1
    well-typed (Γ♩ ⨾pre Δ♪) = (well-typed Γ♩) × (taill Γ♩ ≡ head Δ♪) 

    CtxSeqSeq : Set                                             -- Γ₀⁰; ... ; [Γ₀­ⁿ⁰=Γ₁⁰] ; ... ; [Γₘ₋₁­ⁿ⁽ᵐ⁻¹⁾=Γₘ⁰]; ... ; Γₘ­ⁿᵐ
    CtxSeqSeq = Σ preCtxSeqSeq well-typed

    ι′ : CtxSeq → CtxSeqSeq
    ι′ Γ♪ = ( ιpre ( head Γ♪ ) ⨾pre Γ♪ , ≡refl , ≡refl ) 
    infixr 6 ι′

    ι′′ : Ctx → CtxSeqSeq
    ι′′ Γ = ι′ ( ι Γ )
    infixr 6 ι′′

    head′ : CtxSeqSeq → Ctx
    head′ ( Γ♩ , ξ ) = headd Γ♩

    tail′ : CtxSeqSeq → Ctx
    tail′ ( Γ♩ , ξ ) = taill Γ♩

    _⨾′_ : (Γ♩ : CtxSeqSeq) → (Δ♪ : CtxSeq) → {tail′ Γ♩ ≡ head Δ♪} → CtxSeqSeq
    _⨾′_ Γ♩ Δ♪ { ξ }  = ( fst Γ♩ ⨾pre Δ♪ , (snd Γ♩ , ξ ))

    glued-concat : (Γ♪ Δ♪ : CtxSeq) → tail Γ♪ ≡ head Δ♪ → CtxSeq  -- glued-concat (Γ₀ ; ... ; Γₙ) (Δ₀ ; ... ; Δₘ) = Γ₀ ; ... ; Γₙ = Δ₀ ; ... ; Δₘ
    glued-concat (ι Γ) Δ♪ ⅋ = Δ♪
    glued-concat (Γ♪ ⨾ Γ) Δ♪ ⅋ = Γ♪ ⨾- Δ♪

    alltogether : CtxSeqSeq → CtxSeq                              -- alltogether (Γ₀⁰; ... ; [Γ₀­ⁿ⁰=Γ₁⁰] ; ... ; [Γₘ₋₁­ⁿ⁽ᵐ⁻¹⁾=Γₘ⁰]; ... ; Γₘ­ⁿᵐ) = Γ₀⁰ ; ... ; Γ₀­ⁿ⁰=Γ₁⁰ ; ... ; Γₘ₋₁­ⁿ⁽ᵐ⁻¹⁾=Γₘ⁰ ; ... ; Γₘ­ⁿᵐ
    alltogether (ιpre Γ , ξ) = ι Γ
    alltogether ((Γ♩ ⨾pre ι Δ) , ξ) = alltogether ( Γ♩ , fst ξ )  
    alltogether ((Γ♩ ⨾pre (Δ♪ ⨾ Θ)) , ξ) = alltogether (Γ♩ ⨾pre Δ♪ , ξ) ⨾ Θ

    thin-out : CtxSeqSeq → CtxSeq                                 -- thin-out (Γ₀⁰; ... ; [Γ₀­ⁿ⁰=Γ₁⁰] ; ... ; [Γₘ₋₁­ⁿ⁽ᵐ⁻¹⁾=Γₘ⁰]; ... ; Γₘ­ⁿᵐ) = Γ₀⁰ ; Γ₀­ⁿ⁰=Γ₁⁰ ; ... ; Γₘ₋₁­ⁿ⁽ᵐ⁻¹⁾=Γₘ⁰ ; Γₘ­ⁿᵐ
    thin-out (ιpre Γ , ξ) = ι Γ
    thin-out ((Γ♩ ⨾pre Δ♪) , ξ) = thin-out ( Γ♩ , fst ξ) ⨾ tail Δ♪

    -- We need some calculation here for the formalization

    altogether-ι′ : ∀ {Γ♪} → alltogether (ι′ Γ♪) ≡ Γ♪
    altogether-ι′ {ι Γ} = ≡refl
    altogether-ι′ {Γ♪ ⨾ Δ} = 
        begin 
            alltogether (ι′ (Γ♪ ⨾ Δ))
        ≡⟨ (≡refl) ⟩
            alltogether (ιpre (head (Γ♪ ⨾ Δ)) ⨾pre (Γ♪ ⨾ Δ) , ≡refl , ≡refl)
        ≡⟨ ≡refl ⟩
            alltogether (ιpre (head (Γ♪ ⨾ Δ)) ⨾pre (Γ♪) , ≡refl , ≡refl) ⨾ Δ
        ≡⟨ ≡refl ⟩
            alltogether (ι′ (Γ♪)) ⨾ Δ
        ≡⟨ cong ( λ θ → θ ⨾ Δ) altogether-ι′ ⟩
            Γ♪ ⨾ Δ
        ∎

    alt-ιpre-head-⨾pre : ∀ {Γ♪} → alltogether ( ( ιpre ( head Γ♪) ⨾pre Γ♪) , ≡refl , ≡refl) ≡ Γ♪
    alt-ιpre-head-⨾pre {ι x} = ≡refl
    alt-ιpre-head-⨾pre {Γ♪ ⨾ Δ} = 
        begin 
            alltogether ( ( ιpre ( head (Γ♪ ⨾ Δ)) ⨾pre (Γ♪ ⨾ Δ)) , ≡refl , ≡refl)
        ≡⟨ ≡refl ⟩
            alltogether ( ( ιpre ( head Γ♪) ⨾pre (Γ♪ ⨾ Δ)) , ≡refl , ≡refl)
        ≡⟨ ≡refl ⟩
            alltogether ( ( ιpre ( head Γ♪) ⨾pre Γ♪) , ≡refl , ≡refl) ⨾ Δ
        ≡⟨ subst (λ x → x ⨾ Δ) {!   !} alt-ιpre-head-⨾pre {Γ♪} ⟩
            Γ♪ ⨾ Δ
        ∎
        
    alltogether-⨾ : ∀ { Γ♩ Δ } → ( alltogether (Γ♩ ⨾′ ι Δ)) ≡ ( alltogether Γ♩ )
    alltogether-⨾ {Γ♩} {Δ} = ≡refl

    alltogether-⨾- : ∀ { Γ♩ Δ♪ } → ( alltogether Γ♩ ⨾- Δ♪ ) ≡ ( alltogether ( Γ♩ ⨾′ Δ♪ ))
    alltogether-⨾- {Γ♩} {ι Δ} = 
        begin
            alltogether Γ♩ ⨾- ι Δ
        ≡⟨ {!   !} ⟩
            alltogether Γ♩ 
        ≡⟨ sym (alltogether-⨾ {Γ♩} {Δ})  ⟩
            alltogether ( Γ♩ ⨾′ ι Δ )
        ∎
    alltogether-⨾- {Γ♩} {Δ♪ ⨾ x} = {!   !}
    -- 


    infixr 3 _∈_
    data _∈_ : Type → Ctx → Set where                           -- x : A ∈ Γ
        z : ∀ {Γ A} → A ∈ (Γ ′ A)                               -- x : A ∈ ( Γ , x : A )
        s : ∀ {Γ A B} → A ∈ Γ → A ∈ (Γ ′ B)                     -- x : A ∈ Γ → x : A ∈ ( Γ , y : B )
    
    data Term where
        var : ∀ {Γ A} 
            → A ∈ Γ                         -- x : A ∈ Γ
                                            ----------------
            → Term Γ A                      -- Γ ⊢ x : A
        unit : ∀ {Γ}
            → Term Γ Unit                   -- Γ ⊢ 〈 〉 : Unit
        〈_,_〉 : ∀ {Γ A B}
            → Term Γ A                      -- Γ ⊢ t₁ : A
            → Term Γ B                      -- Γ ⊢ t₂ : B
                                            ----------------
            → Term Γ (Prod A B)             -- Γ ⊢ 〈 t₁ , t₂ 〉 : A × B
        〈0〉 : ∀ {Γ A B}
            → Term Γ (Prod A B)             -- Γ ⊢ t : A × B
                                            ----------------
            → Term Γ A                      -- Γ ⊢ 〈 0 〉 t : A
        〈1〉 : ∀ {Γ A B}
            → Term Γ (Prod A B)             -- Γ ⊢ t : A × B
                                            ----------------
            → Term Γ B                      -- Γ ⊢ 〈 1 〉 t : B
        _[_] : ∀ {Γ Δ A} 
            → Term Δ A                      -- Δ ⊢ t : A
            → Termsubst Γ Δ                 -- Γ ⊢ σ / Δ
                                            ----------------
            → Term Γ A                      -- Γ ⊢ t [ σ / Δ ] : A
    infixr 5 _[_]

    data Termsubst where
        Empty : ∀ {Γ} 
            → Termsubst Γ ε                 -- Γ ⊢ [] / []
        _ʻʻ_ : ∀ {Γ Δ A} 
            → Termsubst Γ Δ                 -- Γ ⊢ σ / Δ
            → Term Γ A                      -- Γ ⊢ t : A
                                            ----------------
            → Termsubst Γ (Δ ′ A)           -- Γ ⊢ σ , t / Δ , A

    data TermsubstSeq : CtxSeq → CtxSeq → Set where   -- Γ♪ ⊢ σ♪ / Δ♪
        ιι : ∀ {Γ Δ} 
            → Termsubst Γ Δ                 -- Γ ⊢ σ / Δ
                                            ----------------
            → TermsubstSeq (ι Γ) (ι Δ)      -- Γ ⊢ σ / Δ
        _⨾⨾_ : ∀ {Γ♪ Δ♪ Γ Δ} 
            → TermsubstSeq Γ♪ Δ♪           -- Γ♪ ⊢ σ / Δ♪
            → Termsubst Γ Δ             -- Γ ⊢ τ / Δ
                                            ----------------
            → TermsubstSeq (Γ♪ ⨾ Γ) (Δ♪ ⨾ Δ) -- Γ♪ ⨾ Γ ⊢ σ / Δ♪ ⨾ Δ

    head-t : ∀ {Γ♪ Δ♪} 
        → TermsubstSeq Γ♪ Δ♪                                  -- Γ₀ ; ... ; Γₙ ⊢ σ₀ ; ... ; σₙ / Δ₀ ; ... ; Δₙ
        → Termsubst (head Γ♪) (head Δ♪)                        -- Γ₀ ⊢ σ₀ / Δ₀
    head-t (ιι σ) = σ
    head-t (σ♪ ⨾⨾ τ) = head-t σ♪


    tail-t : ∀ {Γ♪ Δ♪} 
        → TermsubstSeq Γ♪ Δ♪                                  -- Γ₀ ; ... ; Γₙ ⊢ σ₀ ; ... ; σₙ / Δ₀ ; ... ; Δₙ
        → Termsubst (tail Γ♪) (tail Δ♪)                        -- Γₙ ⊢ σₙ / Δₙ
    tail-t (ιι σ) = σ
    tail-t (σ♪ ⨾⨾ τ) = τ
    
    data Pro where                                             -- Γ ; Δ ⊢ α pro 
        _∧_ : ∀ {Γ Δ} 
            → Pro Γ Δ                       -- Γ ; Δ ⊢ α pro
            → Pro Γ Δ                       -- Γ ; Δ ⊢ β pro
                                            ----------------
            → Pro Γ Δ                       -- Γ ; Δ ⊢ α ∧ β pro
        ⊤ : ∀ {Γ Δ} 
            → Pro Γ Δ                       -- Γ ; Δ ⊢ ⊤ pro
        _[_⨾_]p : ∀ {Γ Δ Γ′ Δ′} 
            → Pro Γ Δ                       -- Γ ; Δ ⊢ α pro
            → Termsubst Γ′ Γ                -- Γ′ ⊢ σ / Γ
            → Termsubst Δ′ Δ                -- Δ′ ⊢ τ / Δ
                                            ----------------
            → Pro Γ′ Δ′                     -- Γ′ ; Δ′ ⊢ α [ σ / Γ ; τ / Δ ] pro
    infixr 4 _[_⨾_]p

    data ProCtx where                                   -- Γ₀ ; ... ; Γₙ ⊢ a₁ : α₁ ⨾̂ ... ⨾̂ aₙ : αₙ = A
        ė : ∀ {Γ} 
            → ProCtx (ι Γ)                  -- Γ ⊢ · 
        _⨾̂_ : ∀ {Γ♪ Δ} 
            → ProCtx Γ♪                    -- Γ₀ ; ... ; Γₙ ⊢ a₁ : α₁ ⨾̂ ... ⨾̂ aₙ : αₙ 
            → Pro (tail Γ♪) Δ              -- Γₙ ; Δ ⊢ β pro
                                            ----------------
            → ProCtx (Γ♪ ⨾ Δ)              -- Γ₀ ; ... ; Γₙ ; Δ ⊢ a₁ : α₁ ⨾̂ ... ⨾̂ aₙ : αₙ ; b : β
    infixr 5 _⨾̂_

    _⨾-pro_ : ∀ { Γ♪ Δ♪ } → { tail Γ♪ ≡ head Δ♪ } →  ( A : ProCtx Γ♪ ) → ( B : ProCtx Δ♪ ) → ProCtx ( alltogether (( ι′ Γ♪ )⨾′ Δ♪ ))
    _⨾-pro_ {Γ♪} {(ι Δ)} {ξ} A ė = {!   !}
    _⨾-pro_ {Γ♪} {(Δ♪ ⨾ Θ)} {ξ} A (B ⨾̂ x) = {!   !}


    proctx-subst : ∀ {Γ♪ Δ♪} 
        → TermsubstSeq Γ♪ Δ♪                                  -- Γ₀ ; ... ; Γₙ ⊢ σ₀ ; ... ; σₙ / Δ₀ ; ... ; Δₙ
        → ProCtx Δ♪                                           -- Δ₀ ; ... ; Δₙ ⊢ a₁ : α₁ ⨾̂ ... ⨾̂ aₙ : αₙ
                                                            ----------------
        → ProCtx Γ♪                                            -- Γ₀ ; ... ; Γₙ ⊢ a₁ : α₁ [ σ₀ / Δ₀ ; ... ; σₙ / Δₙ ] ⨾̂ ... ⨾̂ aₙ : αₙ [ σ₀ / Δ₀ ; ... ; σₙ / Δₙ ]
    proctx-subst (ιι σ) ė = ė                                  -- · [ σ / Δ ] = ·
    proctx-subst (σ♪ ⨾⨾ τ) ( A ⨾̂ α ) = ( proctx-subst σ♪ A) ⨾̂ ( α [ (tail-t σ♪) ⨾ τ ]p ) 

    data ProCtxSeq : CtxSeqSeq → Set where                      -- Γ₀⁰; ... ; [Γ₀­ⁿ⁰=Γ₁⁰] ; ... ; [Γₘ₋₁­ⁿ⁽ᵐ⁻¹⁾=Γₘ⁰]; ... ; Γₘ­ⁿᵐ ⊢ A₁ ; ... ; Aₙ = A♫ 
        ιpro : ∀ {Γ♪} 
            → ProCtx Γ♪                                        -- Γ₀ ; ... ; Γₙ ⊢ a₁ : α₁ ⨾̂ ... ⨾̂ aₙ : αₙ
                                                                ----------------
            → ProCtxSeq (ι′ Γ♪)                                -- Γ₀ ; ... ; Γₙ ⊢ a₁ : α₁ ⨾̂ ... ⨾̂ aₙ : αₙ
        _⨾pro_ : ∀ {Γ♩ Δ♪} 
            → ProCtxSeq Γ♩                                     -- Γᵢ⁰ ; ... ; Γᵢⁿⁱ ⊢ aᵢ⁰ : αᵢ⁰ ⨾̂ ... ⨾̂ aᵢⁿⁱ : αᵢⁿⁱ (i = 1, ..., m)
            → ProCtx Δ♪                                        -- Δ₀ ; ... ; Δₙ ⊢ b₁ : β₁ ⨾̂ ... ⨾̂ bₙ : βₙ
            → { ξ : tail′ Γ♩ ≡ head Δ♪ }                       -- Γₘ⁰ ≡ Δ₀
                                                                ----------------        
            → ProCtxSeq ( _⨾′_ Γ♩ Δ♪ { ξ })                     -- Γᵢ⁰ ; ... ; Γᵢⁿ ⊢ aᵢ⁰ : αᵢ⁰ ⨾̂ ... ⨾̂ aᵢⁿⁱ : αᵢⁿⁱ (i = 1, ..., m) + Δ₀ ; ... ; Δₙ ⊢ b₁ : β₁ ⨾̂ ... ⨾̂ bₙ : βₙ
    
    alltogether-pro : ∀ {Γ♩} → ProCtxSeq Γ♩ → ProCtx (alltogether Γ♩)
    alltogether-pro (ιpro A) = subst ProCtx ( sym altogether-ι′) A
    alltogether-pro (A♫ ⨾pro B) = {!   !}

    data Proterm : (Γ♪ : CtxSeq) → ProCtx Γ♪ → Pro (head Γ♪) (tail Γ♪) → Set
    data ProtermSeq : (Γ♩ : CtxSeqSeq) → ProCtxSeq Γ♩ → ProCtx (thin-out Γ♩) → Set 

    data Proterm where
        ≺_,_≻ : ∀ {Γ♪}
            → ( A : ProCtx Γ♪ )                   -- Γ₀ ; ... ; Γₙ ∣ A proctx
            → ( α :( Pro ( head Γ♪ ) ( tail Γ♪ )) )         -- Γ₀ ; Γₙ ⊢ α pro
            → ( β : (Pro ( head Γ♪ ) ( tail Γ♪ ) ))       -- Γ₀ ; Γₙ ⊢ β pro
            → Proterm Γ♪ A α                     -- Γ₀ ; ... ; Γₙ ∣ A ⊢ m : α 
            → Proterm Γ♪ A β                     -- Γ₀ ; ... ; Γₙ ∣ A ⊢ n : β
            → Proterm Γ♪ A ( α ∧ β )               -- Γ₀ ; ... ; Γₙ ∣ A ⊢ ≺ m , n ≻ : α ∧ β
        ≺ ≻ : ∀ {Γ♪}
            → ( A : ProCtx Γ♪ )                   -- Γ₀ ; ... ; Γₙ ∣ A proctx
            → Proterm Γ♪ A ⊤                     -- Γ₀ ; ... ; Γₙ ∣ A ⊢ ≺ ≻ : ⊤
        π₀ : ∀ {Γ♪}
            → ( A : ProCtx Γ♪ )                   -- Γ₀ ; ... ; Γₙ ∣ A proctx
            → ( α : (Pro ( head Γ♪ ) ( tail Γ♪ ) ))       -- Γ₀ ; Γₙ ⊢ α pro
            → ( β : (Pro ( head Γ♪ ) ( tail Γ♪ ) ))       -- Γ₀ ; Γₙ ⊢ β pro
            → Proterm Γ♪ A ( α ∧ β )               -- Γ₀ ; ... ; Γₙ ∣ A ⊢ m : α ∧ β
            → Proterm Γ♪ A α                     -- Γ₀ ; ... ; Γₙ ∣ A ⊢ π₀ m : α
        π₁ : ∀ {Γ♪}
            → ( A : ProCtx Γ♪ )                   -- Γ₀ ; ... ; Γₙ ∣ A proctx
            → ( α : (Pro ( head Γ♪ ) ( tail Γ♪ ) ))       -- Γ₀ ; Γₙ ⊢ α pro
            → ( β : (Pro ( head Γ♪ ) ( tail Γ♪ ) ))       -- Γ₀ ; Γₙ ⊢ β pro
            → Proterm Γ♪ A ( α ∧ β )               -- Γ₀ ; ... ; Γₙ ∣ A ⊢ m : α ∧ β
            → Proterm Γ♪ A β                     -- Γ₀ ; ... ; Γₙ ∣ A ⊢ π₁ m : β
        _[_]t : ∀ {Γ♪ Δ♪} 
            → { A : ProCtx Δ♪ }                   -- Δ₀ ; ... ; Δₙ ⊢ A proctx
            → { β : Pro ( head Δ♪ ) ( tail Δ♪ ) }       -- Δ₀ ; Δₙ ⊢ β pro
            → ( m : Proterm Δ♪ A β )               -- Δ₀ ; ... ; Δₙ ∣ A ⊢ m : β
            → ( σ : TermsubstSeq Γ♪ Δ♪ )           -- Γ₀ ; ... ; Γₙ ⊢ σ₀ ; ... ; σₙ / Δ₀ ; ... ; Δₙ
            → Proterm Γ♪ ( proctx-subst σ A ) ( β [ head-t σ ⨾ tail-t σ ]p ) -- Γ₀ ; ... ; Γₙ ∣ A [ σ₀ / Δ₀ ; ... ; σₙ / Δₙ ] ⊢ m [ σ₀ / Δ₀ ; ... ; σₙ / Δₙ ] : β [ σ₀ / Δ₀ ; ... ; σₙ / Δₙ ]
        _[[_]] : ∀ {Γ♩}                                      -- Γ₀⁰; ... ; [Γ₀­ⁿ⁰=Γ₁⁰] ; ... ; [Γₘ₋₁­ⁿ⁽ᵐ⁻¹⁾=Γₘ⁰]; ... ; Γₘ­ⁿᵐ 
            → { A♫ : ProCtxSeq Γ♩ }                       -- Γᵢ⁰ ; ... ; Γᵢⁿ ⊢ Aᵢ (i = 1, ..., m)
            → { B : ProCtx (thin-out Γ♩) }                   -- ­Γ₀⁰; ... ; Γₘ­ⁿᵐ ⊢ B = β₁ ⨾̂ ... ⨾̂ βₘ
            → { γ : Pro ( head′ Γ♩ ) ( tail′ Γ♩ ) }        -- Γ₀⁰; Γₘ­ⁿᵐ ⊢ γ pro
            → Proterm (thin-out Γ♩) B {!   !}                   -- ­Γ₀⁰; ... ; Γₘ­ⁿᵐ ∣ B ⊢ n : γ
            → ProtermSeq Γ♩ A♫ B                 -- Γ₀⁰; ... ; [Γ₀­ⁿ⁰=Γ₁⁰] ; ... ; [Γₘ₋₁­ⁿ⁽ᵐ⁻¹⁾=Γₘ⁰]; ... ; [Γₘ­ⁿᵐ=Δ₀] ; Δ₁ ; ... ; Δₙ ⊢ m₁ : β₁ ⨾̂ ... ⨾̂ mₘ : βₘ
            → Proterm (alltogether Γ♩) (alltogether-pro A♫) {!   !}

    -- The following is just a technicality, it is not important for the main point of the question

    thin-out-tail=tail : (Γ♩ : CtxSeqSeq)
        → tail (thin-out Γ♩) ≡ tail′ Γ♩
    thin-out-tail=tail (ιpre x , ξ) = ≡refl
    thin-out-tail=tail ((G ⨾pre x) , ξ) = ≡refl

    Pro-curried2 : ∀ {Δ} → (Γ : Ctx) → Set 
    Pro-curried2 {Δ} Γ = Pro Γ Δ

    merging-pro1 : ∀ {Γ♩ Δ♪} 
        → { ξ : tail′ Γ♩ ≡ head Δ♪ }
        → Pro (head Δ♪) (tail Δ♪)
        → Pro (tail (thin-out Γ♩)) (tail Δ♪)
    merging-pro1 {Γ♩} {Δ♪} {ξ} α = subst Pro-curried2 (trans (sym ξ) (sym (thin-out-tail=tail Γ♩)) ) α

    -- 

    data ProtermSeq where
        ιprot : ∀ {Γ♪} 
            → { A : ProCtx Γ♪ }                   -- Γ₀ ; ... ; Γₙ ∣ A proctx
            → { α : (Pro ( head Γ♪ ) ( tail Γ♪ ) )}       -- Γ₀ ; Γₙ ⊢ α pro
            → Proterm Γ♪ A α                     -- Γ₀ ; ... ; Γₙ ∣ A ⊢ m : α
            → ProtermSeq (ι′ Γ♪) (ιpro A) (ė ⨾̂ α)       -- Γ₀ ; ... ; Γₙ ∣ A ⊢ m : α
        _⨾prot_ : ∀ {Γ♩ Δ♪}
            → { A♫ : ProCtxSeq Γ♩ }                -- Γ₀⁰; ... ; Γ₀­ⁿ⁰ ⊢ A₀ proctx , ... , Γₘ⁰ ; ... ; Γₘ­ⁿᵐ ⊢ Aₘ proctx
            → { B : ProCtx Δ♪ }                   -- Δ₀ ; ... ; Δₙ ⊢ B proctx
            → { ξ : tail′ Γ♩ ≡ head Δ♪ }               -- Γₘ⁰ ≡ Δ₀
            → { γ♫ : ProCtx (thin-out Γ♩) }        -- ­Γ₀⁰ ; Γ₀¹ ⊢ γ₀ pro, ... , ­Γₘ­⁰ ; Γₘ­ⁿᵐ ⊢ γₘ pro
            → { δ : Pro ( head Δ♪ ) ( tail Δ♪ ) }       -- Δ₀ ; Δₙ ⊢ δ pro 
             → ProtermSeq ( _⨾′_ Γ♩ Δ♪ { ξ }) ( _⨾pro_ A♫ B { ξ }) ( γ♫ ⨾̂ (merging-pro1 {Γ♩} {Δ♪} {ξ} δ) ) -- Γ₀⁰; ... ; [Γ₀­ⁿ⁰=Γ₁⁰] ; ... ; [Γₘ₋₁­ⁿ⁽ᵐ⁻¹⁾=Γₘ⁰]; ... ; [Γₘ­ⁿᵐ=Δ₀] ; Δ₁ ; ... ; Δₙ ⊢ γ₀ ⨾̂ ... ⨾̂ γₘ ⨾̂ δ 
