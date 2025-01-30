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

    _×_ : Set → Set → Set
    A × B = Σ A (λ _ → B)
\end{code}


\bibliographystyle{halpha}
\bibliography{fvdbltt}


\end{document}