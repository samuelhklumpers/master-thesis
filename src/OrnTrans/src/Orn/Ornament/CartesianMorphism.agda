
open import Function

open import Data.Unit
open import Data.Product
open import Data.Nat
open import Data.Fin hiding (lift)

open import Logic.Logic

open import IDesc.IDesc

open import Orn.Ornament

module Orn.Ornament.CartesianMorphism
           {I J K L : Set}
           {D : func  K L}
           {u : I → K}{v : J → L}
           (o : orn D u v) where


forgetOrnNT : ∀{X : K → Set }{D} → (O : Orn u D) → 
               ⟦ ⟦ O ⟧Orn ⟧ (X ∘ u) → ⟦ D ⟧ X 
forgetOrnNT (insert S D⁺) (s , xs) = forgetOrnNT (D⁺ s) xs
forgetOrnNT (`var (inv i)) xs = xs
forgetOrnNT `1 tt = tt
forgetOrnNT (O₁ `× O₂) (t₁ , t₂) = forgetOrnNT O₁ t₁ , forgetOrnNT O₂ t₂
forgetOrnNT (`σ T⁺) (k , xs) = k , forgetOrnNT (T⁺ k) xs
forgetOrnNT (`Σ T⁺) (s , xs) = s , forgetOrnNT (T⁺ s) xs
forgetOrnNT (`Π T⁺) f = λ s → forgetOrnNT (T⁺ s) (f s)
forgetOrnNT (deleteΣ s T⁺) xs = s , forgetOrnNT T⁺ xs
forgetOrnNT (deleteσ k T⁺) xs = k , forgetOrnNT T⁺ xs

-- Paper: Definition 4.13
forgetNT : {X : K → Set } → 
            {j : J} →
            ⟦ ⟦ o ⟧orn ⟧func (X ∘ u) j → ⟦ D ⟧func X (v j)
forgetNT {X} {j} = forgetOrnNT (orn.out o j)