module FunOrn.Patch.Examples.Lookup 
         (A : Set)
       where

open import FunOrn.Functions.Examples.Le
open import FunOrn.FunOrnament.Examples.Lookup

open import FunOrn.Patch

-- Paper: Example 5.16
typeILookup : Set
typeILookup = Patch _<_ (typeLookup A)