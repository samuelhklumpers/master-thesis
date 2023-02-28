\documentclass[Test.tex]{subfiles}

\usepackage{hyperref}
\usepackage[links]{agda}

\begin{document}
This document is generated from a literate agda file as well.

\AgdaTarget{Test2}
\begin{code}
module Tex.Test2 where

data Test2 : Set where
  a2 : Test2
  b2 : Test2
\end{code}

Check linking \AgdaDatatype{Test2}.

Hiding test:
\AgdaTarget{YouCantSeeMe2}
\begin{code}[hide]
data YouCantSeeMe2 : Set where
\end{code}

Who is \AgdaDatatype{YouCantSeeMe2}

\end{document}
