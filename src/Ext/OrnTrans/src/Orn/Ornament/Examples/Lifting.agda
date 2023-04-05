

open import Data.Unit
open import Data.Product

open import Logic.Logic 

open import IDesc.IDesc

open import Orn.Ornament

module Orn.Ornament.Examples.Lifting
           {K L : Set}
           {X : K → Set} where

private
  u : Σ K X → K
  u = proj₁

□h : (D : IDesc  K) → ⟦ D ⟧ X → Orn u D
□h `1 tt = `1
□h (`var k) x = `var (inv (k , x))
□h (T `× T') (t , t') =  □h T t `× □h T' t'
□h (`σ n T) (k , xs) = deleteσ k (□h (T k) xs)
□h (`Σ S T) (s , xs) = deleteΣ s (□h (T s) xs)
□h (`Π S T) f = `Π λ s → □h (T s) (f s)

□ : (D : func  K L) → orn D proj₁ proj₁
□ D = orn.mk (λ { (k , x) →  □h (func.out D k) x })
