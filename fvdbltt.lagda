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
\newunicodechar{⊎}{\ensuremath{\oplus}}

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
open import Agda.Builtin.Nat using (suc; zero) renaming (Nat to ℕ)
open import Agda.Builtin.Unit renaming (⊤ to singleton; tt to ⊤)
open import Agda.Builtin.Sigma
open import Agda.Builtin.Bool renaming (Bool to two; true to tt; false to ff)
open import Agda.Builtin.List

open import Data.Sum using (_⊎_) renaming (inj₁ to inl; inj₂ to inr)
open import Data.Product using (_×_) renaming (proj₁ to projl; proj₂ to projr)


{-# BUILTIN REWRITE _≡_ #-}


module fvdbltt where 

\end{code}

First of all, we define the index system for paths of profunctors.

\begin{code}

    
    data ∅ : Set where

    if_then_else : (A : Set) -> two -> A -> A -> A
    if_then_else A tt a b = a
    if_then_else A ff a b = b

    Fin : ℕ → Set
    Fin zero = ∅
    Fin (suc n) = Fin n ⊎ singleton

    the-first : {n : ℕ} → Fin (suc n)
    the-first {zero} = inr ⊤
    the-first {suc n} = inl the-first

    next : { n : ℕ } → Fin n → Fin (suc n)
    next {suc n} (inl x) = inl (next x)
    next {suc n} (inr ⊤) = inr ⊤

    Iterative-number-families : (k : ℕ) → Set
    Iterative-number-families zero = singleton                                                       --- * : Iterative-number-families zero
    Iterative-number-families (suc k) = Σ ℕ (λ i → (Fin i) → Iterative-number-families k)           ---  ( n , (fᵢ) (i ∈ n) ) : Iterative-number-families (suc k) where n : ℕ, fᵢ : Iterative-number-families k 

    pre-total-index : {k : ℕ} → Iterative-number-families k → Set 
    pre-total-index {zero} S = singleton 
    pre-total-index {suc k} ( n , f ) = Σ (Fin n) (λ i → pre-total-index {k} (f i))

    total-index : {k : ℕ} → Iterative-number-families k → Set
    total-index {k} S = pre-total-index S ⊎ singleton



    next-index : {k : ℕ} → {S : Iterative-number-families k} → pre-total-index {k} S → total-index {k} S
    next-index {zero} {⊤} i = inr ⊤
    next-index {suc k} {n , f} (t , p) with next-index {k} {f t} p                              --- f : (Fin n) → Iterative-number-families k, t : Fin n, p : pre-total-index {k} (f t)
    ... | inl j = inl (t , j)                                                                   --- if next-index p : pre-total-index ?, then we just take it as the next index 
    ... | inr ⊤ with n | t                                                                      --- if next-index p : singleton, then we push it to the next layer
    ... | suc n | inl t = inl ( next t , {!   !} )                             --- if t = the-first, then we take the-first-index f
    ... | suc n | inr ⊤ = inr ⊤
    

    --  I could not fill the hole in the above code. This is the first index of the next group but I could not define it.
\end{code}


\bibliographystyle{halpha}
\bibliography{fvdbltt}

       
\end{document} 