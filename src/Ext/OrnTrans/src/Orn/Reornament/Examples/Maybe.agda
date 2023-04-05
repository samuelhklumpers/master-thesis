module Orn.Reornament.Examples.Maybe
         (A : Set) 
       where



open import Data.Unit
open import Data.Product

open import IDesc.Fixpoint
open import IDesc.Examples.Bool

open import Orn.Ornament
open import Orn.Ornament.Examples.Maybe

open import Orn.Reornament

-- Paper: Example 4.31

iMaybe : Bool → Set
iMaybe b = μ ⌈ MaybeO A ⌉D (tt , b)

inothing : iMaybe false
inothing = ⟨ tt ⟩ 

ijust : A → iMaybe true
ijust a = ⟨ a , tt ⟩
