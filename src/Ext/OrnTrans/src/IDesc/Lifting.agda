 

open import Data.Unit
open import Data.Product

open import Logic.Logic

open import IDesc.IDesc
open import IDesc.Fixpoint


module IDesc.Lifting
          {I : Set}
          {X : I → Set } where


□h : (D : IDesc  I)(P : ∀{i} → X i → Set) (xs : ⟦ D ⟧ X) → Set
□h `1 P tt = ⊤
□h (`var i) P xs = P xs
□h (T `× T') P (t , t') =  □h T P t × □h T' P t'
□h (`σ n T) P (k , xs) = □h (T k) P xs
□h (`Σ S T) P (s , xs) = □h (T s) P xs
□h (`Π S T) P f = (s : S) → □h (T s) P (f s) 

□hmap : (D : IDesc  I){P : ∀{i} → X i → Set}(p : ∀{i} → (x : X i) → P x)
          (xs : ⟦ D ⟧ X) → □h D P xs
□hmap `1 p tt = tt
□hmap (`var i) p xs = p xs
□hmap (T `× T') p (t , t')= □hmap T p t , □hmap T' p t'
□hmap (`σ n T) p (k , xs) = □hmap (T k) p xs
□hmap (`Σ S T) p (s , xs) = □hmap (T s) p xs
□hmap (`Π S T) p f = λ s → □hmap (T s) p (f s)

□ : (D : func  I I)(P : ∀{i} → X i → Set)(xs : Σ[ i ∈ I ] ⟦ D ⟧func X i) → Set
□ D P (i , xs) = □h (func.out D i) P xs

□map : (D : func  I I){P : ∀{i} → X i → Set}(p : ∀{i} → (x : X i) → P x)
          (xs : Σ[ i ∈ I ] ⟦ D ⟧func X i) → □ D P xs
□map D p (i , xs) = □hmap (func.out D i) p xs 


