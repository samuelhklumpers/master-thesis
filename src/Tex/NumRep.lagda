\documentclass[../Main.tex]{subfiles}

\begin{document}
\begin{code}
{-# OPTIONS --cubical --copatterns #-}
module Tex.NumRep where

open import Prelude
open import Data.Nat
open import Cubical.Data.Sigma
open import Cubical.Data.Sum
open import Cubical.Data.Unit
open import Cubical.Data.Empty
open import Prelude.UseAs
open import TypeIsos
\end{code}

\begin{code}
<-split : ∀ n → (Σ[ m ∈ ℕ ] m < suc n) ≃ (⊤ ⊎ (Σ[ m ∈ ℕ ] m < n))
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


\begin{code}
Fin-def : ∀ n → Def (Σ[ m ∈ ℕ ] m < n)
Fin-def zero    = ⊥-strict (λ ()) use-as-def
Fin-def (suc n) =
  ua (<-split n) ∙
  cong (⊤ ⊎_) (by-definition (Fin-def n)) use-as-def

Fin : ℕ → Type
Fin n = defined-by (Fin-def n)
\end{code}

\begin{code}
Lookup : Type → ℕ → Type
Lookup A n = Fin n → A
\end{code}

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
\end{code}

\begin{code}
record Array (C : Type → ℕ → Type) : Type₁ where
  field
    lookup : ∀ {n A} → C A n → Fin n → A
    tail   : ∀ {n A} → C A (suc n) → C A n

open Array

record ArrayLaws {C} (Arr : Array C) : Type₁ where
  field
    lookup∘tail : ∀ {n A} {i : Fin n} {xs : C A (suc n)}
                → Arr .lookup (Arr .tail xs) i ≡ Arr .lookup xs (inr i)
\end{code}

\end{document}
