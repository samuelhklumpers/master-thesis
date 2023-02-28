module FunOrn.Lift.Examples.Lookup 
         {A : Set}
       where

open import Data.Unit
open import Data.Product
open import Data.Fin hiding (_<_ ; fold ; lift)

open import Logic.Logic

open import IDesc.Fixpoint
open import IDesc.Induction
open import IDesc.Examples.Nat
open import IDesc.Examples.Bool

open import Orn.Ornament.Identity
open import Orn.Ornament.Examples.List
open import Orn.Ornament.Examples.Maybe

open import Orn.Reornament.Examples.List
open import Orn.Reornament.Examples.Maybe

open import FunOrn.Functions.Examples.Le
open import FunOrn.FunOrnament.Examples.Lookup
open import FunOrn.Patch.Examples.Lookup

open import FunOrn.Functions
open import FunOrn.FunOrnament
open import FunOrn.Patch
open import FunOrn.Lift.Induction
open import FunOrn.Lift.Case
open import FunOrn.Lift.Constructor

-- Paper: Example 6.19
βL : (n : Nat) → A →
     Patch {T = μ NatD [ tt ]→ μ BoolD [ tt ]× `⊤} 
           (induction NatD (λ _ → Nat → Bool × ⊤) (λ {i}{xs} → α {i}{xs}) n)
           (μ⁺ (idO NatD) [ inv tt ]→ μ⁺ MaybeO A [ inv tt ]× `⊤) →
     liftCases (idO NatD) 
              (λ {i} xs → β
                (induction NatD _ (λ {i}{xs} → α {i}{xs}) n)
                {i} xs) 
              (μ⁺ MaybeO A [ inv tt ]× `⊤)
βL n a ih {tt , ⟨ zero , tt ⟩} tt = 
        lift-constructor (MaybeO A) (a , tt) tt tt
βL n a ih {tt , ⟨ suc zero , m ⟩} m' = ih m m'
βL n a ih {tt , ⟨ suc (suc ()) , _ ⟩} _

-- Paper: Example 6.11
-- Paper: Example 6.19
αL : liftIH (ListO A) (λ {i}{xs} → α {i}{xs}) 
              (μ⁺ (idO NatD) [ inv tt ]→ μ⁺ MaybeO A [ inv tt ]× `⊤)
αL {tt , ⟨ zero , tt ⟩} {tt} (tt) = 
        λ x xs → lift-constructor (MaybeO A) tt tt tt
αL {tt , ⟨ suc zero , n ⟩} {a , m } ih = 
       lift-case (idO NatD) 
               {T = μ BoolD [ tt ]× `⊤} 
               {T⁺ = μ⁺ MaybeO A [ inv tt ]× `⊤}
               (λ {i} xs → β (induction NatD _ (λ {i}{xs} → α {i}{xs}) n) {i} xs) 
               (λ {i} xs → βL n a ih {i} xs)
αL {tt , ⟨ suc (suc ()) , _ ⟩} {_} _

-- Paper: Example 6.11
vlookup : Patch _<_ (typeLookup A)
vlookup m m' n vs = lift-ind (ListO A) {i = tt}{i⁺ = inv tt} 
                           {T = μ NatD [ tt ]→ μ BoolD [ tt ]× `⊤}
                           {T⁺ = μ⁺ (idO NatD) [ inv tt ]→ 
                                 μ⁺ MaybeO A [ inv tt ]× `⊤} 
                           (λ {i}{xs} → α {i}{xs})
                           (λ{i}{xs} → αL {i}{xs}) n vs m m'

open import FunOrn.Patch.Apply

lookup : ⟦ typeLookup A ⟧FunctionOrn
lookup = patch (typeLookup A) _<_ vlookup
