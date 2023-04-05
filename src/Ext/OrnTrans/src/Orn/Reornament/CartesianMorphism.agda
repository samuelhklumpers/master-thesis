open import Function

open import Data.Unit
open import Data.Product
open import Data.Nat
open import Data.Fin

open import Logic.Logic

open import IDesc

open import Orn.Ornament

module Orn.Reornament.CartesianMorphism
           {I J K L : Set}
           {D : func K L}
           {u : I → K}{v : J → L}
           (o : orn D u v) where


forgetOrnNat : ∀{X D} → (O : Orn u D) → 
            ⟦ ⟦ O ⟧Orn ⟧ (X ∘ u) → ⟦ D ⟧ X 
forgetOrnNat (insert S D⁺) (s , xs) = forgetOrnNat (D⁺ s) xs
forgetOrnNat (`var (inv i)) xs = xs
forgetOrnNat `1 tt = tt
forgetOrnNat (O₁ `× O₂) (t₁ , t₂) = forgetOrnNat O₁ t₁ , forgetOrnNat O₂ t₂
forgetOrnNat (`σ T⁺) (k , xs) = k , forgetOrnNat (T⁺ k) xs
forgetOrnNat (`Σ T⁺) (s , xs) = s , forgetOrnNat (T⁺ s) xs
forgetOrnNat (`Π T⁺) f = λ s → forgetOrnNat (T⁺ s) (f s)
forgetOrnNat (deleteΣ s T⁺) xs = s , forgetOrnNat T⁺ xs
forgetOrnNat (deleteσ k T⁺) xs = k , forgetOrnNat T⁺ xs

forgetNat : {X : K → Set} → 
            ⟦ ⟦ o ⟧orn ⟧func (X ∘ u) ⇒ ⟦ func.mk (func.out D ∘ v) ⟧func X
forgetNat {X} {j} = forgetOrnNat (orn.out o j)