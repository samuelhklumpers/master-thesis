\documentclass{article}

\usepackage{hyperref}
\usepackage[links]{agda}

\usepackage{subfiles}


\begin{document}
This document is generated from a literate agda file.

\AgdaTarget{Test}
\begin{code}
module Tex.Test where

data Test : Set where
  a : Test
  b : Test
\end{code}

Check linking \AgdaDatatype{Test}.

Hiding test:
\AgdaTarget{YouCantSeeMe}
\begin{code}[hide]
data YouCantSeeMe : Set where
\end{code}

Who is \AgdaDatatype{YouCantSeeMe}

Importing
\begin{code}
open import Tex.Test2
\end{code}

\subfile{Tex/Test2}

\end{document}
