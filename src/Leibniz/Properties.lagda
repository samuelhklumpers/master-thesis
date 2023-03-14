\documentclass[Main.tex]{subfiles}

\begin{document}
\begin{code}
{-# OPTIONS --cubical --copatterns #-}

module Leibniz.Properties where

import Cubical.Data.Nat as N
import Cubical.Data.Nat.Properties as NP
import Data.Nat.Tactic.RingSolver as NS

open import Cubical.Foundations.SIP

open import Prelude
open import Extra.Nat
open import Extra.Algebra
open import Extra.Algebra.Definitions

open import Leibniz.Base

import Cubical.Data.Equality as Eq


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
\AgdaTarget{toℕ-suc}
\begin{code}
toℕ-suc : ∀ x → toℕ (bsuc x) ≡ ℕ.suc (toℕ x)
\end{code}
%</toN-suc>
\begin{code}
toℕ-suc 0b     = refl
toℕ-suc (x 1b) = refl
toℕ-suc (x 2b) = cong
  (λ k → (1 N.+ 2 N.· k))
  (toℕ-suc x) ∙ cong ℕ.suc (NP.·-suc 2 (toℕ x)) 
\end{code}

%<*fromN-1>
\AgdaTarget{fromℕ-1+2·}
\begin{code}
fromℕ-1+2· : ∀ x → fromℕ (1 N.+ 2 N.· x) ≡ (fromℕ x) 1b
\end{code}
%</fromN-1>
\begin{code}
fromℕ-1+2· ℕ.zero    = refl
fromℕ-1+2· (ℕ.suc x) = cong
  (bsuc ∘ bsuc)
  (cong fromℕ (NP.+-suc x (x N.+ ℕ.zero)) ∙ fromℕ-1+2· x)
\end{code}
%<*fromN-2>
\AgdaTarget{fromℕ-2+2·}
\begin{code}
fromℕ-2+2· : ∀ x → fromℕ (2 N.+ 2 N.· x) ≡ (fromℕ x) 2b
\end{code}
%</fromN-2>
\begin{code}
fromℕ-2+2· x = cong bsuc (fromℕ-1+2· x)
\end{code}

%<*N-iso-L>
\AgdaTarget{ℕ↔L}
\begin{code}
ℕ↔L : Iso ℕ Leibniz
ℕ↔L = iso fromℕ toℕ sec ret
  where
  sec : section fromℕ toℕ
  sec 0b     = refl
  sec (n 1b) = fromℕ-1+2· (toℕ n) ∙ cong _1b (sec n)
  sec (n 2b) = fromℕ-2+2· (toℕ n) ∙ cong _2b (sec n)

  ret : retract fromℕ toℕ
  ret ℕ.zero    = refl
  ret (ℕ.suc n) = toℕ-suc (fromℕ n) ∙ cong ℕ.suc (ret n)
\end{code}
%</N-iso-L>

%<*N-equiv-L>
\AgdaTarget{ℕ≃L}
\begin{code}
ℕ≃L : ℕ ≃ Leibniz
ℕ≃L = isoToEquiv ℕ↔L
\end{code}
%</N-equiv-L>

%<*N-is-L>
\AgdaTarget{ℕ≡L}
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
\end{code}

\begin{code}
open import Prelude.UseAs

open Iso
\end{code}

\begin{code}
{-# TERMINATING #-}
\end{code}
%<*plus-def>
\AgdaTarget{plus-def}
\begin{code}
plus-def : ∀ x y → Def (fromℕ (toℕ x N.+ toℕ y))
plus-def 0b y          = ℕ↔L .rightInv y use-as-def
plus-def (x 1b) 0b     =
  bsuc (fromℕ (toℕ x N.+ (toℕ x N.+ ℕ.zero) N.+ ℕ.zero))
    ≡⟨ cong (bsuc ∘ fromℕ) (NP.+-zero (2 N.· toℕ x)) ⟩
  bsuc (fromℕ (toℕ x N.+ (toℕ x N.+ ℕ.zero)))
    ≡⟨ fromℕ-1+2· (toℕ x) ⟩
  fromℕ (toℕ x) 1b                                         
    ≡⟨ cong _1b (ℕ↔L .rightInv x) ⟩
  x 1b ∎ use-as-def
plus-def (x 1b) (y 1b) = 
  fromℕ ((1 N.+ 2 N.· toℕ x) N.+ (1 N.+ 2 N.· toℕ y))    
    ≡⟨ cong fromℕ (Eq.eqToPath (eq (toℕ x) (toℕ y))) ⟩
  fromℕ (2 N.+ (2 N.· (toℕ x N.+ toℕ y)))               
    ≡⟨ fromℕ-2+2· (toℕ x N.+ toℕ y) ⟩
  fromℕ (toℕ x N.+ toℕ y) 2b                            
    ≡⟨ cong _2b (by-definition (plus-def x y)) ⟩
  defined-by (plus-def x y) 2b ∎ use-as-def
    where
    eq : ∀ x y
       → (1 N.+ 2 N.· x) N.+ (1 N.+ 2 N.· y) Eq.≡ 2 N.+ (2 N.· (x N.+ y))
    eq = NS.solve-∀
-- similar clauses omitted
\end{code}
%</plus-def>
\begin{code}[hide]
plus-def (x 1b) (y 2b) =
  fromℕ (toℕ (x 1b) N.+ toℕ (y 2b))                      ≡⟨ cong fromℕ (Eq.eqToPath (eq (toℕ x) (toℕ y))) ⟩
  bsuc (fromℕ (2 N.+ (2 N.· (toℕ x N.+ toℕ y))))         ≡⟨ cong bsuc (fromℕ-2+2· (toℕ x N.+ toℕ y)) ⟩
  bsuc (fromℕ (toℕ x N.+ toℕ y)) 1b ≡⟨ cong (λ z → bsuc z 1b) (by-definition (plus-def x y)) ⟩
  bsuc (defined-by (plus-def x y)) 1b ∎                  use-as-def
    where
    eq : (x y : ℕ) → (1 N.+ 2 N.· x) N.+ (2 N.+ 2 N.· y) Eq.≡ 3 N.+ (2 N.· (x N.+ y))
    eq = NS.solve-∀
plus-def (x 2b) 0b     = (cong fromℕ (NP.+-comm (toℕ (x 2b)) _) ∙ by-definition (plus-def 0b (x 2b))) use-as-def
plus-def (x 2b) (y 1b) = (cong fromℕ (NP.+-comm (toℕ (x 2b)) _) ∙ by-definition (plus-def (y 1b) (x 2b))) use-as-def
  -- I kind of expected the termination checker to unfold this far enough..
plus-def (x 2b) (y 2b) =
  fromℕ (toℕ (x 2b) N.+ toℕ (y 2b))                      ≡⟨ cong fromℕ (Eq.eqToPath (eq (toℕ x) (toℕ y))) ⟩
  (fromℕ (4 N.+ (2 N.· (toℕ x N.+ toℕ y))))              ≡⟨ cong (bsuc ∘ bsuc) (fromℕ-2+2· (toℕ x N.+ toℕ y)) ⟩
  bsuc (fromℕ (toℕ x N.+ toℕ y)) 2b                      ≡⟨ cong (λ z → bsuc z 2b) (by-definition (plus-def x y)) ⟩
  bsuc (defined-by (plus-def x y)) 2b ∎                  use-as-def
    where
    eq : (x y : ℕ) → (2 N.+ 2 N.· x) N.+ (2 N.+ 2 N.· y) Eq.≡ 4 N.+ (2 N.· (x N.+ y))
    eq = NS.solve-∀
\end{code}

%<*plus-good>
\AgdaTarget{plus}
\AgdaTarget{plus-coherent}
\begin{code}
plus : ∀ x y → Leibniz
plus x y = defined-by (plus-def x y)

plus-coherent : ∀ x y → fromℕ (x N.+ y) ≡ plus (fromℕ x) (fromℕ y)
plus-coherent x y = cong fromℕ
  (cong₂ N._+_ (sym (ℕ↔L .leftInv x)) (sym (ℕ↔L .leftInv _))) ∙
   by-definition (plus-def (fromℕ x) (fromℕ y))
\end{code}
%</plus-good>

\begin{code}
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
\end{code}

%<*magmaL>
\AgdaTarget{MagmaL}
\begin{code}
MagmaL : Magma
fst MagmaL = Leibniz
snd MagmaL = plus
\end{code}
%</magmaL>

%<*magma-equal>
\AgdaTarget{Magmaℕ≃MagmaL}
\begin{code}
Magmaℕ≃MagmaL : Magmaℕ ≡ MagmaL
Magmaℕ≃MagmaL = equivFun (MagmaΣPath _ _) proof
  where
  proof : Magmaℕ ≃[ MagmaEquivStr ] MagmaL
  fst proof = ℕ≃L
  snd proof = plus-coherent
\end{code}
%</magma-equal>

%<*assoc-transport>
\begin{code}
plus-assoc : Associative _≡_ plus
plus-assoc = subst
    (λ A → Associative _≡_ (snd A))
    Magmaℕ≃MagmaL
    ℕ-assoc
\end{code}
%</assoc-transport>
\end{document}
