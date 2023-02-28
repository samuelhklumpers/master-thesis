module IDesc.Examples.STLC where

open import Data.Unit
open import Data.Nat
open import Data.Fin
open import Data.Vec hiding (_∈_ ; module _∈_)
open import Data.Product
open import Data.List

open import Relation.Binary.PropositionalEquality

open import IDesc.IDesc
open import IDesc.Fixpoint
open import IDesc.Tagged

-- Paper: Example 3.10

infixr 60 _⇒_
data Ty : Set where
  unit : Ty
  _⇒_ : (A B : Ty) → Ty


infixl 50 _∙_
data Context : Set where
  ε : Context
  _∙_ : (Γ : Context)(T : Ty) → Context

infix  40 _∈_
data _∈_ : Ty → Context → Set where
  ze : ∀{Γ T} → T ∈ Γ ∙ T
  su : ∀{Γ T T'} → T ∈ Γ → T ∈ Γ ∙ T'

STLCD : func (Context × Ty) (Context × Ty)
STLCD = func.mk λ { (Γ , T) → 
          `Σ (Fin 3) λ 
          { zero → `Σ (T ∈ Γ) λ _ → `1 
          ; (suc zero) → `Σ Ty λ S → `var (Γ , S ⇒ T) `× `var (Γ , S) 
          ; (suc (suc zero)) → help Γ T 
          ; (suc (suc (suc ()))) } }
  where help : Context → Ty → IDesc (Context × Ty)
        help Γ unit = `Σ (Fin 1) λ { zero → `1 ; (suc ()) }
        help Γ (S ⇒ T) = `Σ (Fin 1) λ { zero → `var (Γ ∙ S , T) ; (suc ()) }

infix 20 _⊢_
_⊢_ : Context → Ty → Set
Γ ⊢ T = μ STLCD (Γ , T)

var : ∀{Γ T} → T ∈ Γ → Γ ∙ T ⊢ T
var v = ⟨ zero , ze , tt ⟩

app : ∀{Γ S T} → Γ ⊢ S ⇒ T → Γ ⊢ S → Γ ⊢ T
app f s = ⟨ suc zero , _ , f , s ⟩

void : ∀{Γ} → Γ ⊢ unit
void = ⟨ suc (suc zero) , zero , tt ⟩

lam : ∀{Γ S T} → Γ ∙ S ⊢ T → Γ ⊢ S ⇒ T
lam b = ⟨ suc (suc zero) , zero , b ⟩