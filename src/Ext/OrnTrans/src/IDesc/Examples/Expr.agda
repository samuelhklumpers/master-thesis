module IDesc.Examples.Expr where

open import Data.Unit hiding (_≟_)
open import Data.Bool hiding (_≟_)
open import Data.Nat hiding (_≟_)
open import Data.Fin hiding (lift)
open import Data.Vec 
open import Data.Product

open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality

open import IDesc.IDesc
open import IDesc.Fixpoint
open import IDesc.Tagged

infix 4 _≟_


data Ty : Set where
 `nat `bool : Ty

_≟_ : Decidable {A = Ty} _≡_
`nat ≟ `nat = yes refl
`nat ≟ `bool = no (λ ())
`bool ≟ `nat = no (λ ())
`bool ≟ `bool = yes refl


Val : Ty → Set
Val `nat = ℕ
Val `bool = Bool

ExprD : tagDesc Ty
ExprD = (2 , λ ty → (`Σ (Val ty) λ _ → `1) ∷ 
                    (`var `bool `× `var ty `× `var ty `× `1) ∷ []) ,
        ((λ { `nat → 1 
            ; `bool → 1 })) , 
         (λ { `nat → `var `nat `× `var `nat `× `1 ∷ [] 
            ; `bool → `var `nat `× `var `nat `× `1 ∷ [] })

Expr : Ty → Set
Expr = μ (toDesc ExprD)


val : ∀{ty} → Val ty → Expr ty
val v = ⟨ zero , v , tt ⟩

cond : ∀{ty} → Expr `bool → Expr ty → Expr ty → Expr ty
cond b tr fs = ⟨ suc zero , b , tr , fs , tt ⟩

plus : Expr `nat → Expr `nat → Expr `nat 
plus x y = ⟨ suc (suc zero) , x , y , tt ⟩

le : Expr `nat → Expr `nat → Expr `bool
le x y = ⟨ suc (suc zero) , x , y , tt ⟩