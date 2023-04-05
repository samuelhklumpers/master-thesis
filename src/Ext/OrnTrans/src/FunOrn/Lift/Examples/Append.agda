module FunOrn.Lift.Examples.Append
         {A : Set}
       where

open import Data.Unit
open import Data.Product
open import Data.Fin hiding (_+_ ; fold ; lift)

open import Logic.Logic

open import IDesc.Fixpoint
open import IDesc.Induction
open import IDesc.Examples.Nat
open import IDesc.Examples.Bool

open import Orn.Reornament
open import Orn.Ornament.Examples.List

open import Orn.Reornament.Examples.List

open import FunOrn.Functions.Examples.Plus
open import FunOrn.FunOrnament.Examples.Append
open import FunOrn.Patch.Examples.Append

open import FunOrn.Functions
open import FunOrn.FunOrnament
open import FunOrn.Patch
open import FunOrn.Lift.Induction
open import FunOrn.Lift.Constructor

-- Paper: Example 6.21
αL : (m : Nat) →
     μ ⌈ ListO A ⌉D (tt , m) →
     liftIH (ListO A)
              (λ {i}{xs} → α m {i}{xs}) 
              (μ⁺ ListO A [ inv tt ]× `⊤)
αL m xs {tt , ⟨ zero , tt ⟩} {tt} tt = xs , tt
αL m xs {tt , ⟨ suc zero , n ⟩} {a , ys} (ih , tt) =
     lift-constructor (ListO A) {i⁺ = inv tt} {T = `⊤} {T⁺ = `⊤} 
                     (a , tt) 
                     ih  tt
αL m xs {tt , ⟨ suc (suc ()) , _ ⟩} _

-- Paper: Example 6.12
vappend :  Patch _+_ (typeAppend A)
vappend m xs n ys = lift-ind (ListO A) {tt} {inv tt}
                            {T = μ NatD [ tt ]× `⊤} 
                            {T⁺ = μ⁺ ListO A [ inv tt ]× `⊤ }
                            (λ {i}{hs} → α m {i}{hs}) 
                            (λ {i}{hs} → αL m xs {i}{hs}) n ys

open import FunOrn.Patch.Apply

append : ⟦ typeAppend A ⟧FunctionOrn
append = patch (typeAppend A) _+_ vappend
