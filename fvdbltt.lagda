\documentclass{article}
\usepackage{preamble_fvdbltt}
\usepackage{agda}

\usepackage{unicode-math}
\setmathfont{XITS Math}

\usepackage{newunicodechar}
\newunicodechar{λ}{\ensuremath{\mathnormal\lambda}}
\newunicodechar{∎}{\ensuremath{\mathnormal{\blacksquare}}}
\newunicodechar{≡}{\ensuremath{\equiv}}
\newunicodechar{⟨}{\ensuremath{\langle}}
\newunicodechar{⟩}{\ensuremath{\rangle}}
\newunicodechar{ℕ}{\ensuremath{\mathbb{N}}}
\newunicodechar{⊕}{\ensuremath{\oplus}}

\title{Implementation of the FVDBLTT in Agda}
\author{Hayato Nasu}
\date{\today}

\begin{document}

\maketitle

\begin{code}
{-# OPTIONS --rewriting #-}

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; trans; sym; cong; cong-app; subst) renaming (refl to ≡refl)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _∎; step-≡)
open import Agda.Primitive 
open import Agda.Builtin.Nat
open import Agda.Builtin.Sigma
open import Agda.Builtin.List

{-# BUILTIN REWRITE _≡_ #-}


module fvdbltt where

\end{code}

First of all, we define the index system for paths of profunctors.

\begin{code}

    data ℕ : Set where
        zero : ℕ
        suc : ℕ → ℕ

    data two : Set where
        tt : two
        ff : two

    _×_ : Set → Set → Set
    A × B = Σ A (λ _ → B)
    infixr 4 _×_

    proj₁ : {A : Set} {B : Set} → A × B → A
    proj₁ (a , b) = a

    proj₂ : {A : Set} {B : Set} → A × B → B
    proj₂ (a , b) = b


    data singleton : Set where
        ⊤ : singleton


    _⊕_ : Set → Set → Set
    A ⊕ B = Σ two (λ i → K i) where
        K : two → Set
        K tt = A
        K ff = B
    infixr 4 _⊕_

    inl : {A B : Set} → A → A ⊕ B
    inl a = tt , a

    inr : {A B : Set} → B → A ⊕ B
    inr b = ff , b
    

    data ∅ : Set where


    Fin : ℕ → Set
    Fin zero = ∅
    Fin (suc n) = singleton ⊕ Fin n

    Iterative-number-families : (k : ℕ) → Set
    Iterative-number-families zero = singleton                                                       --- * : Iterative-number-families zero
    Iterative-number-families (suc k) = Σ ℕ (λ i → (Fin i) → Iterative-number-families k)           ---  ( n , (fᵢ) (i ∈ n) ) : Iterative-number-families (suc k) where n : ℕ, fᵢ : Iterative-number-families k 

    pre-total-index : {k : ℕ} → Iterative-number-families k → Set 
    pre-total-index {zero} S = singleton 
    pre-total-index {suc k} ( n , f ) = Σ (Fin n) (λ i → pre-total-index {k} (f i))

    total-index : {k : ℕ} → Iterative-number-families k → Set
    total-index {k} S = pre-total-index S ⊕ singleton
\end{code}


\bibliographystyle{halpha}
\bibliography{fvdbltt}

   
\end{document}