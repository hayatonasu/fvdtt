{-# OPTIONS --rewriting #-}

open import Agda.Primitive 
open import Agda.Builtin.Nat
open import Agda.Builtin.Sigma

module fvtt where

    -- data List {l} (A : Set l) : Set l where
    --     [] : List A
    --     _::_ : A → List A → List A

    -- len : {l : Level} → {A : Set l} → List A → Nat 
    -- len [] = zero
    -- len (x :: k) = suc (len k)

    -- ap : {l : Level} → {A : Set l} → { B : Set (lsuc l)} → (A → B) → ( List A → List B)
    -- ap {l} {A} {B} f [] = []
    -- ap {l} {A} {B} f (x :: k) = (f x) :: (ap f k)
    

    -- _,_ : {l : Level} → {A : Set l} → List A → List A → List A
    -- [] , ys = ys
    -- (x :: xs) , ys = x :: (xs , ys)

    -- record Sig (l : Level) : Set (lsuc l) where
    --     field
    --         GrdTy : Set l
    --         GrdFunc : List GrdTy → GrdTy → Set l
    --         GrdPro : List GrdTy → List GrdTy → Set l

    -- Ctx : {l : Level} → Sig l → Set l
    -- Ctx {l} L = List (Sig.GrdTy L)

    -- -- data fjudg {l} (L : Sig l) : Ctx L → Set l where 
    -- --     : 
    
    
    data Type : Set 
    data Ctx : Set
    data Term : Ctx → Type → Set 
    data Termsubst : Ctx → Ctx → Set
    data Pro : Ctx → Ctx → Set
    data CtxSeq : Set 
    data ProCtx : CtxSeq → Set
    data Proterm : (Γ♩ : CtxSeq) → ProCtx Γ♩ → Set

    data Type where
        Unit : Type
        Prod : Type → Type → Type

    data Ctx where
        ε : Ctx
        _′_ : Ctx → Type → Ctx
    infixr 5 _′_

    _⋆_ : Ctx → Ctx → Ctx
    _⋆_ Γ ε = Γ
    _⋆_ Γ  ( Δ ′ A ) = ( Γ ⋆ Δ ) ′ A
    infixr 6 _⋆_

    data CtxSeq where
        ι : Ctx → CtxSeq
        _⨾_ : CtxSeq → CtxSeq → CtxSeq
    infixr 4 _⨾_

    head : CtxSeq → Ctx
    head (ι Γ) = Γ
    head (Γ ⨾ Δ) = head Γ

    tail : CtxSeq → Ctx
    tail (ι Γ) = Γ 
    tail (Γ ⨾ Δ) = tail Δ

    infixr 3 _∈_
    data _∈_ : Type → Ctx → Set where
        z : ∀ {Γ A} → A ∈ (Γ ′ A)
        s : ∀ {Γ A B} → A ∈ Γ → A ∈ (Γ ′ B)
    
    data Term where
        var : ∀ {Γ A} → A ∈ (Γ ⋆ ε) → Term Γ A 
    
    data Termsubst where
    
    data Pro where

    
    data ProCtx where
    
    data Proterm where
    