\documentclass[../Main.tex]{subfiles}

\begin{document}
\begin{code}
{-# OPTIONS --cubical --copatterns --postfix-projections #-}
module Tex.NumRep where

open import Prelude
open import Data.Nat
open import Cubical.Data.Sigma
open import Cubical.Data.Sum
open import Cubical.Data.Unit
open import Cubical.Data.Empty
open import Prelude.UseAs
open import Extra.TypeIsos
\end{code}

%<*leq-split>
\AgdaTarget{<-split}
\begin{code}
<-split : ∀ n → (Σ[ m ∈ ℕ ] m < suc n) ≃ (⊤ ⊎ (Σ[ m ∈ ℕ ] m < n))
\end{code}
%</leq-split>
\begin{code}
<-split n = isoToEquiv (iso to from sec ret)
  where
  to : (Σ[ m ∈ ℕ ] m < suc n) → (⊤ ⊎ (Σ[ m ∈ ℕ ] m < n))
  to (zero  , _)     = inl tt
  to (suc m , s≤s p) = inr (m , p)

  from : (⊤ ⊎ (Σ[ m ∈ ℕ ] m < n)) → (Σ[ m ∈ ℕ ] m < suc n)
  from (inl _)       = 0     , s≤s z≤n
  from (inr (m , p)) = suc m , s≤s p

  sec : section to from
  sec (inl tt) = refl
  sec (inr x)  = refl

  ret : retract to from
  ret (zero  , s≤s z≤n) = refl
  ret (suc m , s≤s p)   = refl
\end{code}

%<*Fin-def>
\AgdaTarget{Fin-def}
\AgdaTarget{Fin}
\begin{code}
Fin-def : ∀ n → Def (Σ[ m ∈ ℕ ] m < n)
Fin-def zero    = ⊥-strict (λ ()) use-as-def
Fin-def (suc n) =
  ua (<-split n) ∙
  cong (⊤ ⊎_) (by-definition (Fin-def n)) use-as-def

Fin : ℕ → Type
Fin n = defined-by (Fin-def n)
\end{code}
%</Fin-def>


%<*Lookup>
\AgdaTarget{Lookup}
\begin{code}
Lookup : Type → ℕ → Type
Lookup A n = Fin n → A
\end{code}
%</Lookup>

%<*Vec>
\AgdaTarget{Vec-def}
\AgdaTarget{Vec}
\begin{code}
Vec-def : ∀ A n → Def (Lookup A n) 
Vec-def A zero    = isContr→≡Unit isContr⊥→A use-as-def
Vec-def A (suc n) = 
  ((⊤ ⊎ Fin n) → A)
    ≡⟨ ua Π⊎≃ ⟩
  (⊤ → A) × (Fin n → A)
    ≡⟨ cong₂ _×_
       (UnitToTypePath A)
       (by-definition (Vec-def A n)) ⟩
  A × (defined-by (Vec-def A n)) ∎ use-as-def

Vec : ∀ A n → Type
Vec A n = defined-by (Vec-def A n)
\end{code}
%</Vec>

%<*Array>
\AgdaTarget{Array}
\AgdaTarget{lookup}
\AgdaTarget{tail}
\begin{code}
record Array (V : Type → ℕ → Type) : Type₁ where
  field
    lookup : ∀ {A n} → V A n → Fin n → A
    tail   : ∀ {A n} → V A (suc n) → V A n
\end{code}
%</Array>

\begin{code}
open Array
\end{code}

%<*Laws>
\AgdaTarget{ArrayLaws}
\AgdaTarget{lookup∘tail}
\begin{code}
record ArrayLaws {C} (Arr : Array C) : Type₁ where
  field
    lookup∘tail : ∀ {A n} (xs : C A (suc n)) (i : Fin n)
                → Arr .lookup (Arr .tail xs) i ≡ Arr .lookup xs (inr i)
\end{code}
%</Laws>

\begin{code}
open ArrayLaws
\end{code}

%<*FunArray>
\AgdaTarget{FunArray}
\begin{code}
FunArray : Array Lookup
FunArray .lookup f = f
FunArray .tail   f = f ∘ inr
\end{code}
%</FunArray>

%<*FunLaw>
\AgdaTarget{FunLaw}
\begin{code}
FunLaw : ArrayLaws FunArray
FunLaw .lookup∘tail _ _ = refl
\end{code}
%</FunLaw>

%<*VecArray>
\AgdaTarget{VectorArray}
\begin{code}
VectorArray : Array Vec
VectorArray .lookup {n = n} = f n
  where
  f : ∀ {A} n → Vec A n → Fin n → A
  f (suc n) (x , xs) (inl _) = x
  f (suc n) (x , xs) (inr i) = f n xs i
VectorArray .tail (x , xs) = xs
\end{code}
%</VecArray>

\begin{code}
VectorLaw : ArrayLaws VectorArray
VectorLaw .lookup∘tail {n = n} xs i = f n xs i
  where
  f : ∀ {A} n (xs : Vec A (suc n)) (i : Fin n)
    → VectorArray .lookup {n = n} (VectorArray .tail {n = n} xs) i
    ≡ VectorArray .lookup {n = suc n} xs (inr i)
  f n xs i = refl
\end{code}

\end{document}
