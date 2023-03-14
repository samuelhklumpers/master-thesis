\documentclass[../Main.tex]{subfiles}


\begin{document}
\begin{code}
module Tex.Snippets where

open import Cubical.Data.Sigma.Base
open import Agda.Builtin.Cubical.Path
open import Level

private variable
  ℓ : Level


isContr : Type ℓ → Type ℓ
\end{code}
%<*isContr>
\AgdaTarget{isContr}
\begin{code}
isContr A = Σ[ x ∈ A ] (∀ y → x ≡ y)
\end{code}
%</isContr>

\begin{code}



\end{code}
\end{document}