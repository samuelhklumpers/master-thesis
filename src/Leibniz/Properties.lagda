\documentclass[Main.tex]{subfiles}

\begin{document}
\begin{code}
{-# OPTIONS --cubical --copatterns #-}

module Leibniz.Properties where

import Cubical.Data.Nat as N
import Cubical.Data.Nat.Properties as NP
open import Cubical.Foundations.SIP

open import Prelude
open import Extra.Nat
open import Extra.Algebra
open import Extra.Algebra.Definitions

open import Leibniz.Base


0b-not-1b : ¬ (0b ≡ x 1b)
0b-not-1b p = subst P p tt
  where
  P : Leibniz → Type
  P 0b     = ⊤
  P (n 1b) = ⊥
  P (n 2b) = ⊤

0b-not-2b : ¬ (0b ≡ x 2b)
0b-not-2b p = subst P p tt
  where
  P : Leibniz → Type
  P 0b     = ⊤
  P (n 1b) = ⊤
  P (n 2b) = ⊥

1b-not-2b : ¬ (x 1b ≡ y 2b)
1b-not-2b p = subst P p tt
  where
  P : Leibniz → Type
  P 0b     = ⊤
  P (n 1b) = ⊤
  P (n 2b) = ⊥

1b-inj : ∀ {x y} → x 1b ≡ y 1b → x ≡ y
1b-inj = cong (1 >>_)

2b-inj : ∀ {x y} → x 2b ≡ y 2b → x ≡ y
2b-inj = cong (1 >>_)
\end{code}

%<*toN-suc>
\begin{code}
⟦⟧-suc : ∀ x → ⟦ bsuc x ⟧ ≡ ℕ.suc ⟦ x ⟧
⟦⟧-suc 0b     = refl
⟦⟧-suc (x 1b) = refl
⟦⟧-suc (x 2b) = cong (λ k → (1 N.+ 2 N.· k)) (⟦⟧-suc x) ∙ cong ℕ.suc (NP.·-suc 2 ⟦ x ⟧) 
\end{code}
%</toN-suc>

%<*fromN-1>
\begin{code}
fromℕ-1+2· : ∀ x → fromℕ (1 N.+ 2 N.· x) ≡ (fromℕ x) 1b
fromℕ-1+2· ℕ.zero    = refl
fromℕ-1+2· (ℕ.suc x) = cong (bsuc ∘ bsuc) (cong fromℕ (NP.+-suc x (x N.+ ℕ.zero)) ∙ fromℕ-1+2· x)

fromℕ-2+2· : ∀ x → fromℕ (2 N.+ 2 N.· x) ≡ (fromℕ x) 2b
fromℕ-2+2· x = cong bsuc (fromℕ-1+2· x)
\end{code}
%</fromN-1>

%<*N-iso-L>
\begin{code}
ℕ↔L : Iso ℕ Leibniz
ℕ↔L = iso fromℕ ⟦_⟧ sec ret
  where
  sec : section fromℕ ⟦_⟧
  sec 0b     = refl
  sec (n 1b) = fromℕ-1+2· ⟦ n ⟧ ∙ cong _1b (sec n)
  sec (n 2b) = fromℕ-2+2· ⟦ n ⟧ ∙ cong _2b (sec n)

  ret : retract fromℕ ⟦_⟧
  ret ℕ.zero    = refl
  ret (ℕ.suc n) = ⟦⟧-suc (fromℕ n) ∙ cong ℕ.suc (ret n)
\end{code}
%</N-iso-L>

%<*N-equiv-L>
\begin{code}
ℕ≃L : ℕ ≃ Leibniz
ℕ≃L = isoToEquiv ℕ↔L
\end{code}
%</N-equiv-L>

\AgdaTarget{ℕ≡L}
%<*N-is-L>
\begin{code}
ℕ≡L : ℕ ≡ Leibniz
ℕ≡L = ua ℕ≃L
\end{code}
%</N-is-L>

%<*isSetL>
\begin{code}
isSetL : isSet Leibniz
isSetL = subst isSet ℕ≡L N.isSetℕ
\end{code}
%</isSetL>

\begin{code}
discreteL : Discrete Leibniz
discreteL = subst Discrete (ua ℕ≃L) N.discreteℕ

-- compare with
{-
discreteL : Discrete Leibniz
discreteL 0b 0b = yes refl
discreteL 0b (y 1b) = no 0b-not-1b
discreteL 0b (y 2b) = no 0b-not-2b
discreteL (x 1b) 0b = no (0b-not-1b ∘ sym)
discreteL (x 1b) (y 1b) with discreteL x y
... | yes p = yes (cong _1b p)
... | no ¬p = no (¬p ∘ 1b-inj)
discreteL (x 1b) (y 2b) = no 1b-not-2b
discreteL (x 2b) 0b = no (0b-not-2b ∘ sym)
discreteL (x 2b) (y 1b) = no (1b-not-2b ∘ sym)
discreteL (x 2b) (y 2b) with discreteL x y
... | yes p = yes (cong _2b p)
... | no ¬p = no (¬p ∘ 2b-inj)
-}

open import Extra.Nat using (Magmaℕ)

+-suc : ∀ x y → bsuc (x + y) ≡ bsuc x + y
+-suc 0b 0b     = refl
+-suc 0b (y 1b) = refl
+-suc 0b (y 2b) = refl
+-suc (x 1b) 0b     = refl
+-suc (x 1b) (y 1b) = refl
+-suc (x 1b) (y 2b) = refl
+-suc (x 2b) 0b     = refl
+-suc (x 2b) (y 1b) = cong _2b (+-suc x y)
+-suc (x 2b) (y 2b) = cong (_1b ∘ bsuc) (+-suc x y)

+ℕ≡+L : ∀ x y → fromℕ (x N.+ y) ≡ fromℕ x + fromℕ y
+ℕ≡+L ℕ.zero    y = refl
+ℕ≡+L (ℕ.suc x) y = cong bsuc (+ℕ≡+L x y) ∙ +-suc (fromℕ x) (fromℕ y)

Magmaℕ≃MagmaL : Magmaℕ ≡ MagmaL
Magmaℕ≃MagmaL = equivFun (MagmaΣPath _ _) proof
  where
  proof : Magmaℕ ≃[ MagmaEquivStr ] MagmaL
  fst proof = ℕ≃L
  snd proof = +ℕ≡+L

L-assoc : Associative _≡_ (snd MagmaL)
L-assoc = subst (λ A → Associative _≡_ (snd A)) Magmaℕ≃MagmaL ℕ-assoc
\end{code}
\end{document}