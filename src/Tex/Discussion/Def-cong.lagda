\begin{document}
\begin{code}
{-# OPTIONS --type-in-type #-}

module Tex.Discussion.Def-cong where

open import Agda.Primitive
  using    ( Level
           ; SSet )
  renaming ( lzero to ℓ-zero
           ; lsuc  to ℓ-suc
           ; _⊔_   to ℓ-max
           ; Set   to Type
           ; Setω  to Typeω )

open import Relation.Binary.PropositionalEquality
open import Function.Base
open import Data.Product


private variable
  A B C : Type
  
record _≃_ A B : Type where
  constructor iso
  field
    fun  : A → B
    inv  : B → A
    rightInv  : ∀ b → fun (inv b) ≡ b 
    leftInv   : ∀ a → inv (fun a) ≡ a

{-
record Σ' (A : Type) (B : A → Type) : Type where
  constructor _use-as-def
  field
    {fst} : A
    snd : B fst
    
open Σ'
infix 1 _use-as-def
-}

infix 10 _≃_

open _≃_

FDef : {AT BT : Type} → AT → (AT → Type) → (BT → Type) → Type
FDef {BT = BT} A f g = Σ BT λ B → f A ≃ g B

open import Ornament.OrnDesc
open import Ornament.Desc
open import Data.Nat
open import Data.Fin

Lookup : Type → ℕ → Type
Lookup A n = Fin n → A

intp : Desc (∅ ▷ const Type) ℕ → Type → ℕ → Type 
intp D A n = μ D (_ , A) n


{- defined-by     : {A : Type} → Def A        → Type
by-definition  : {A : Type} → (d : Def A)  → A ≃ (defined-by d)
defined-by     = fst
by-definition  = snd -}

infix  1 ≃-begin_
infixr 2 _≃⟨_⟩_
infixr 2 _≃⟨⟩_
infix  3 _≃-∎

_≃⟨_⟩_ : ∀ A {B C} → A ≃ B → B ≃ C → A ≃ C
_≃⟨⟩_ : ∀ A {B} → A ≃ B → A ≃ B
_≃-∎ : ∀ A → A ≃ A

≃-begin_ : ∀ {A B} → A ≃ B → A ≃ B
≃-begin A≃B = A≃B

(A ≃⟨ A≃B ⟩ B≃C) .fun       = B≃C .fun ∘ A≃B .fun
(A ≃⟨ A≃B ⟩ B≃C) .inv       = A≃B .inv ∘ B≃C .inv
(A ≃⟨ A≃B ⟩ B≃C) .rightInv b rewrite A≃B .rightInv (B≃C .inv b) = B≃C .rightInv b
(A ≃⟨ A≃B ⟩ B≃C) .leftInv  a rewrite B≃C .leftInv (A≃B .fun a)  = A≃B .leftInv a

A ≃⟨⟩ A≃B = A≃B

A ≃-∎ = iso id id (λ _ → refl) (λ _ → refl)

postulate
  funExt≃ : {A : Type} (f g : A → Type) → (∀ a → f a ≃ g a) → (∀ a → f a) ≃ (∀ a → g a)

{-
Vec-def : FDef Lookup (λ F → ∀ A n → F A n) (λ D → ∀ A n → intp D A n)
Vec-def  = _
         , funExt≃ (λ A → ∀ n → Lookup A n) (λ A → ∀ n → intp _ A n) λ A →
           funExt≃ (Lookup A) (intp _ A) (λ n →
           proof A n)
  where
  proof : ∀ A n → Lookup A n ≃ intp VecD A n
  proof A zero    = {!!}
  proof A (suc n) = {!!}
-}
\end{code}
\end{document}
