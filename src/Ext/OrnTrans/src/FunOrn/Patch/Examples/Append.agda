module FunOrn.Patch.Examples.Append
         (A : Set)
       where

open import FunOrn.Functions.Examples.Plus
open import FunOrn.FunOrnament.Examples.Append

open import FunOrn.Patch

-- Paper: Example 5.18
typeILookup : Set
typeILookup = Patch _+_ (typeAppend A)