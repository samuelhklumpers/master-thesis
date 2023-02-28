module IDesc.Tagged where

open import Function

open import Data.Nat hiding (_⊔_)
open import Data.Fin hiding (lift) renaming (_+_ to _F+_)
open import Data.Vec
open import Data.Product

open import IDesc.IDesc


tagDesc : Set → Set₁
tagDesc I = Tags I × iTags I
  where
    Tags : Set → Set₁
    Tags I = Σ[ n ∈ ℕ ] (I → Vec (IDesc  I) n)

    iTags : Set → Set₁
    iTags I = Σ[ f ∈ (I → ℕ) ] ((i : I) → Vec (IDesc  I) (f i))

-- TODO: Must be part of the stdlib
private
  ⟨_∣_⟩ : ∀{k}{A : Set k}{m n} → (Fin m → A) → (Fin n → A) → Fin (m + n) → A
  ⟨_∣_⟩ {A = A} {m = m}{n = n} f g k = help m f k
    where help : (m : ℕ) → (Fin m → A) → Fin (m + n) → A
          help zero f k = g k
          help (suc m) f zero = f zero
          help (suc m) f (suc k) = help m (f ∘ suc) k

toDesc : {I : Set} → tagDesc I → func  I I 
toDesc ((n , ds) , (f , ids)) =
       func.mk λ i → 
         `Σ (Fin (n + f i))
            λ { k → 
                ⟨ (flip lookup) (ds i) ∣ (flip lookup) (ids i) ⟩ k }

toTagged : {I : Set} → func I I → tagDesc  I
toTagged d = (( 1 , λ i → func.out d i ∷ []) , ( (λ i → 0) , λ i → []))
