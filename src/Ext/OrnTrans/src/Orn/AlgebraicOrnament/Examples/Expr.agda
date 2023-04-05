module Orn.AlgebraicOrnament.Examples.Expr where

open import Data.Unit
open import Data.Nat
open import Data.Fin hiding (_+_ ; lift)
open import Data.Product

open import Relation.Binary.PropositionalEquality

open import IDesc.IDesc
open import IDesc.Fixpoint
open import IDesc.InitialAlgebra
open import IDesc.Induction

import  Orn.AlgebraicOrnament

-- Paper: Example 4.24

ExprD : func ⊤ ⊤
ExprD = func.mk λ _ → 
        `σ 2 (λ { zero → `Σ ℕ λ _ → `1 
                ; (suc zero) → `var tt `× `var tt `× `1 
                ; (suc (suc ())) })

Expr : Set
Expr = μ ExprD tt

const : ℕ → Expr
const n = ⟨ zero , n , tt ⟩

add : Expr → Expr → Expr
add m n = ⟨ suc zero , m , n , tt ⟩

α : Alg ExprD (λ _ → ℕ)
α {tt} (zero , n , tt) = n
α {tt} (suc zero , el , er , tt) = el + er
α {tt} (suc (suc ()) , _)

open Orn.AlgebraicOrnament.Func ExprD α

ExprSem : ℕ → Set
ExprSem n = μ algOrnD (tt , n)

constS : (n : ℕ) → ExprSem n
constS n = ⟨ (zero , n , tt) , refl , tt ⟩

addS : ∀{m n} → ExprSem m → ExprSem n → ExprSem (m + n)
addS {m}{n} e₁ e₂ = ⟨ (suc zero , m , n , tt) , refl , e₁ , e₂ , tt ⟩

private
  record ⟨optimise-0+_⟩ {n : ℕ}(e : ExprSem n) : Set where
    constructor return
    field
      call : ExprSem n
  open ⟨optimise-0+_⟩ public

  β : DAlg algOrnD (λ e → ⟨optimise-0+ e ⟩) 
  β {tt , .n} {(zero , n , tt) , refl ,  tt} tt = return (constS n)
  β {tt , n} {(suc zero , zero , .n , tt) , refl , e₁ , e₂ , tt} (optL , optR , tt) = return (call optR)
  β {tt , .(suc (m + n))} {(suc zero , suc m , n , tt) , refl , e₁ , e₂ , tt} (optL , optR , tt) = return (addS e₁ e₂) 
  β {_} {(suc (suc ()) , _) , _ , _} _

  optimise : ∀{n} → (e : ExprSem n) → ⟨optimise-0+ e ⟩
  optimise = induction algOrnD (λ e → ⟨optimise-0+ e ⟩) β

optimise-0+ : ∀{n} → (e : ExprSem n) → ExprSem n
optimise-0+ e = call (optimise e)

module Test where

  test-0+ : ∀{k n} → optimise-0+ (addS {0}{k} (constS 0) n) ≡ optimise-0+ n
  test-0+ = refl

  test-0+0+ : ∀{k n} → optimise-0+ (addS {0}{k} (addS (constS 0) (constS 0)) n) ≡ optimise-0+ n
  test-0+0+ = refl