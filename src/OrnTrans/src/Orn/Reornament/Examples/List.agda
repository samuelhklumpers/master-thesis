module Orn.Reornament.Examples.List 
         (A : Set) 
       where



open import Data.Unit
open import Data.Product

open import IDesc.Fixpoint
open import IDesc.Examples.Nat

open import Orn.Ornament
open import Orn.Ornament.Examples.List

open import Orn.Reornament

-- Paper: Example 4.30

Vec : Nat → Set
Vec n = μ ⌈ ListO A ⌉D (tt , n)

vnil : Vec ze
vnil = ⟨ tt ⟩

vcons : ∀{n} → A → Vec n → Vec (su n)
vcons a xs = ⟨ a , xs ⟩