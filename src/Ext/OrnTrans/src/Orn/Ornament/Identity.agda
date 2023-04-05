

module Orn.Ornament.Identity 
         {I : Set}
       where

open import Function

open import Logic.Logic

open import IDesc.IDesc

open import Orn.Ornament

-- Paper: Example 4.9
idO : (D : func  I I) → orn D id id
idO D = orn.mk (λ i → help (func.out D i))
  where help : (D : IDesc  I) → Orn id D
        help (`var i) = `var (inv i)
        help `1 = `1
        help (D₁ `× D₂) = help D₁ `× help D₂
        help (`σ n T) = `σ λ k → help (T k)
        help (`Σ S T) = `Σ λ s → help (T s)
        help (`Π S T) = `Π λ s → help (T s)