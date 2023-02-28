module FunOrn.Lift.Examples.Head 
         (A : Set)
       where

open import Data.Unit
open import Data.Fin hiding (fold ; lift)
open import Data.Product

open import Logic.Logic

open import IDesc.IDesc
open import IDesc.Fixpoint
open import IDesc.InitialAlgebra
open import IDesc.Examples.Bool
open import IDesc.Examples.Nat 

open import Orn.Ornament
open import Orn.Ornament.Examples.List
open import Orn.Ornament.Examples.Maybe

open import FunOrn.Functions
open import FunOrn.FunOrnament
open import FunOrn.Patch
open import FunOrn.Lift.Fold
open import FunOrn.Lift.Constructor

-- Paper: Example 6.3
typeIsSuc : Type
typeIsSuc = μ NatD [ tt ]→ μ BoolD [ tt ]× `⊤

α : Alg NatD (λ _ → Bool × ⊤)
α {tt} (zero , tt) = false , tt
α {tt} (suc zero , _) = true , tt
α {tt} (suc (suc ()) , _)

isSuc : ⟦ typeIsSuc ⟧Type
isSuc = fold NatD α
  

typeHead : FunctionOrn typeIsSuc
typeHead = μ⁺ ListO A [ inv tt ]→ 
             μ⁺ MaybeO A [ inv tt ]× `⊤

-- Paper: Example 6.18
αL : liftAlg (ListO A) α (μ⁺ MaybeO A [ inv tt ]× `⊤)
αL {tt , ⟨ zero , tt ⟩} xs = lift-constructor (MaybeO A) tt tt tt
αL {tt , ⟨ suc zero , n ⟩} (a , xs) = lift-constructor ((MaybeO A)) (a , tt) tt tt
αL {tt , ⟨ suc (suc ()) , _ ⟩} _

-- Paper: Example 6.9
vhead : Patch isSuc typeHead
vhead = lift-fold (ListO A)  {T⁺ = μ⁺ MaybeO A [ inv tt ]× `⊤} α (λ {i} → αL {i})

open import FunOrn.Patch.Apply

head : ⟦ typeHead ⟧FunctionOrn
head = patch typeHead isSuc vhead
