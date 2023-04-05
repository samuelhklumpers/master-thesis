module IDesc.Examples.Walk where

open import Data.Unit
open import Data.Nat
open import Data.Fin hiding (lift)
open import Data.Vec 
open import Data.Product

open import Relation.Binary.PropositionalEquality

open import IDesc.IDesc
open import IDesc.Fixpoint
open import IDesc.Tagged


WalkD : tagDesc ℕ
WalkD = (1 , (λ n → `var (suc n) `× `1 ∷ [])) ,
        ((λ { zero → 1 
            ; (suc n) → 1 }) , 
          λ { zero → `1 ∷ [] 
            ; (suc n) → `var n `× `1 ∷ [] })

Walk : ℕ → Set
Walk = μ (toDesc WalkD)

up : ∀{n} → Walk (suc n) → Walk n
up w = ⟨ zero , w , tt ⟩

stop : Walk 0
stop = ⟨ suc zero , tt ⟩

down : ∀{n} → Walk n → Walk (suc n)
down w = ⟨ suc zero , w , tt ⟩