{-# OPTIONS --rewriting #-}

open import Agda.Primitive 
open import Agda.Builtin.Nat
open import Agda.Builtin.Sigma
open import Agda.Builtin.Equality using (_≡_) renaming (refl to ≡refl)
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
    data TermsubstSeq : CtxSeq → CtxSeq → Set
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

    data preCtxSeqSeq : Set where                                -- Γ♩ = Γ ⨾′ (Γ₀⁰; ... ; Γ₀­ⁿ⁰) ⨾′ ... ⨾′ (Γ­ₘ⁰ ; ... ; Γₘ­ⁿᵐ) 
        ι′ : Ctx → preCtxSeqSeq                               
        _⨾′_ : preCtxSeqSeq → CtxSeq → preCtxSeqSeq              

    tail′ : preCtxSeqSeq → Ctx                                   -- tail′ ((Γ₀⁰; ... ; Γ₀­ⁿ⁰) ⨾′ ... ⨾′ (Γ­ₘ⁰ ; ... ; Γₘ­ⁿᵐ)) = Γₘ­ⁿᵐ
    tail′ (ι′ Γ) = Γ
    tail′ (Γ ⨾′ Δ) = tail Δ

    well-typed : preCtxSeqSeq → Set                               -- Γ₀ⁿ⁰=Γ₁⁰ × ... × Γₘ₋₁­ⁿ⁽ᵐ⁻¹⁾=Γₘ⁰
    well-typed (ι′ Γ) = 1 ≡ 1
    well-typed (Γ♩ ⨾′ Δ♪) = (well-typed Γ♩) × (tail′ Γ♩ ≡ head Δ♪) 

    CtxSeqSeq : Set                                             -- Γ₀⁰; ... ; [Γ₀­ⁿ⁰=Γ₁⁰] ; ... ; [Γₘ₋₁­ⁿ⁽ᵐ⁻¹⁾=Γₘ⁰]; ... ; Γₘ­ⁿᵐ
    CtxSeqSeq = Σ preCtxSeqSeq well-typed

    glued-concat : (Γ♪ Δ♪ : CtxSeq) → tail Γ♪ ≡ head Δ♪ → CtxSeq  -- glued-concat (Γ₀ ; ... ; Γₙ) (Δ₀ ; ... ; Δₘ) = Γ₀ ; ... ; Γₙ = Δ₀ ; ... ; Δₘ
    glued-concat (ι Γ) Δ♪ ⅋ = Δ♪
    glued-concat (Γ♪ ⨾ Γ) Δ♪ ⅋ = Γ♪ ⨾- Δ♪

    alltogether : CtxSeqSeq → CtxSeq                              -- alltogether (Γ₀⁰; ... ; [Γ₀­ⁿ⁰=Γ₁⁰] ; ... ; [Γₘ₋₁­ⁿ⁽ᵐ⁻¹⁾=Γₘ⁰]; ... ; Γₘ­ⁿᵐ) = Γ₀⁰ ; ... ; Γ₀­ⁿ⁰=Γ₁⁰ ; ... ; Γₘ₋₁­ⁿ⁽ᵐ⁻¹⁾=Γₘ⁰ ; ... ; Γₘ­ⁿᵐ
    alltogether (ι′ Γ , ξ) = ι Γ
    alltogether ((Γ♩ ⨾′ ι Δ) , ξ) = alltogether ( Γ♩ , fst ξ )  
    alltogether ((Γ♩ ⨾′ (Δ♪ ⨾ Θ)) , ξ) = alltogether (Γ♩ ⨾′ Δ♪ , ξ) ⨾ Θ

    thin-out : CtxSeqSeq → CtxSeq                                 -- thin-out (Γ₀⁰; ... ; [Γ₀­ⁿ⁰=Γ₁⁰] ; ... ; [Γₘ₋₁­ⁿ⁽ᵐ⁻¹⁾=Γₘ⁰]; ... ; Γₘ­ⁿᵐ) = Γ₀⁰ ; Γ₀­ⁿ⁰=Γ₁⁰ ; ... ; Γₘ₋₁­ⁿ⁽ᵐ⁻¹⁾=Γₘ⁰ ; Γₘ­ⁿᵐ
    thin-out (ι′ Γ , ξ) = ι Γ
    thin-out ((Γ♩ ⨾′ Δ♪) , ξ) = thin-out ( Γ♩ , fst ξ) ⨾ tail Δ♪

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

    data TermsubstSeq where                     -- Γ♪ ⊢ σ♪ / Δ♪
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
    
    data Pro where
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

    data ProCtx where
        ė : ∀ {Γ} 
            → ProCtx (ι Γ)                  -- Γ ⊢ · proctx
        _⨾̂_ : ∀ {Γ♪ Δ} 
            → ProCtx Γ♪                    -- Γ₀ ; ... ; Γₙ ⊢ α₁ ⨾̂ ... ⨾̂ αₙ proctx
            → Pro (tail Γ♪) Δ              -- Γₙ ; Δ ⊢ β pro
                                            ----------------
            → ProCtx (Γ♪ ⨾ Δ)              -- Γ₀ ; ... ; Γₙ ; Δ ⊢ α₁ ⨾̂ ... ⨾̂ αₙ ⨾̂ β proctx
    infixr 5 _⨾̂_

    proctx-subst : ∀ {Γ♪ Δ♪} 
        → TermsubstSeq Γ♪ Δ♪                                  -- Γ₀ ; ... ; Γₙ ⊢ σ₀ ; ... ; σₙ / Δ₀ ; ... ; Δₙ
        → ProCtx Δ♪                                           -- Δ₀ ; ... ; Δₙ ⊢ α₁ ⨾̂ ... ⨾̂ αₙ proctx
                                                            ----------------
        → ProCtx Γ♪                                            -- Γ₀ ; ... ; Γₙ ⊢ α₁ [ σ₀ / Δ₀ ; ... ; σₙ / Δₙ ] ⨾̂ ... ⨾̂ αₙ [ σ₀ / Δ₀ ; ... ; σₙ / Δₙ ] proctx
    proctx-subst (ιι σ) ė = ė                                  -- · [ σ / Δ ] = ·
    proctx-subst (σ♪ ⨾⨾ τ) ( A ⨾̂ α ) = ( proctx-subst σ♪ A) ⨾̂ ( α [ (tail-t σ♪) ⨾ τ ]p ) 

    data Proterm : (Γ♪ : CtxSeq) → ProCtx Γ♪ → Pro (head Γ♪) (tail Γ♪) → Set 
    -- data ProtermSeq : (Γ♪ : CtxSeqSeq) → ProCtx (head Γ♪) → Pro (head (head Γ♪)) (tail (head Γ♪)) → Set --- これは嘘です

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
        -- _{_} : ∀ {Γ♩} 
        --     →