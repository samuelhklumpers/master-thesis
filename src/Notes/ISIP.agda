{-# OPTIONS --cubical #-}

module ISIP where

open import Cubical.Data.Sigma.Properties
open import Cubical.Data.Sigma.Base
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.SIP


import Cubical.Structures.Axioms               as Axioms
open Axioms using ( AxiomsStructure ; AxiomsEquivStr
                  ; axiomsUnivalentStr ; transferAxioms) public

private variable
  a b c : Level


-- let's try to write down an interface for vectors

-- since we're going to implement vectors using unary and binary numbers, we will want an interface for numbers
RawNatStructure : Type a → Type a
RawNatStructure N = N × (N → N) × (N → N)
--                 zero, suc,   pred

NatAxioms : (N : Type) → RawNatStructure N → Type
NatAxioms N (z , s , p) = (n : N) → p (s n) ≡ n

NatStructure : Type → Type
NatStructure = AxiomsStructure RawNatStructure NatAxioms

Nat : Type₁
Nat = TypeWithStr ℓ-zero NatStructure

-- now a vector is something like
VecStructure : (N : Nat) → (V : fst N → Type a → Type a) → Type (ℓ-suc a)
VecStructure (N , ((z , s , p), ax)) V = ∀ A → V z A × (∀ n → V n A → V (s n) A)
-- fixing N in this direction was probably not helpful

{-
VecAxioms : (N : Nat) → (V : fst N → Type → Type) → RawVecStructure N V → Type
VecAxioms N V S = ∀ A → {!!}
-}

-- so first of all, this isn't going to work because TypeWithStr is not polymorphic, nor indexed
-- i.e., our interface is (way) too restrictive for SIP
Vec : Type₁
Vec = Σ[ N ∈ Nat ] TypeWithStr ℓ-zero {!VecStructure N!}

private variable
  Ix : Type a

IFun : Type a → (b : Level) → Type (ℓ-max a (ℓ-suc b)) 
IFun Ix b = Ix → Type b

private variable
  F : IFun Ix a

IxStructure : (F : IFun Ix a) (S : ∀ i → F i → Type b) (T : ∀ i → F i → Type c) → Type {!!}
IxStructure F S T = {!∀  S X → T X !}

