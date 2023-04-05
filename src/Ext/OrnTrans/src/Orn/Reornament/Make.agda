
open import Function

open import Data.Unit
open import Data.Product

open import Relation.Binary.PropositionalEquality

open import Logic.Logic

open import IDesc.IDesc
open import IDesc.Fixpoint
open import IDesc.InitialAlgebra

open import Orn.Ornament

module Orn.Reornament.Make
         {K I : Set }
         {D : func  I I}
         {u : K → I}
         (o : orn D u u) 
       where

open import Orn.Reornament
open import Orn.Ornament.CartesianMorphism o
open import Orn.Ornament.Algebra o

-- Paper: Remark 4.32
make : ∀{k} →
         (x : μ ⟦ o ⟧orn k) → μ ⌈ o ⌉D (k , fold ⟦ o ⟧orn forgetAlg x)
make {k} ⟨ xs ⟩ = ⟨ help (orn.out o k ) xs ⟩
  where help : ∀{D' : IDesc I} → (O : Orn u D') →
               (xs : ⟦ ⟦ O ⟧Orn ⟧ (μ ⟦ o ⟧orn)) → 
               ⟦ ⟦ Reorn O (forgetOrnNT O (Fold.hyps ⟦ o ⟧orn forgetAlg ⟦ O ⟧Orn xs)) ⟧Orn ⟧ (μ ⌈ o ⌉D)
        help (insert S D⁺) (s , xs) = s , help (D⁺ s) xs
        help (`var (inv i)) ⟨ xs ⟩ = ⟨ help (orn.out o i) xs ⟩
        help `1 xs = tt
        help (O₁ `× O₂) (xs₁ , xs₂) = help O₁ xs₁ , help O₂ xs₂
        help (`σ T⁺) (k , xs) = help (T⁺ k) xs
        help (`Σ T⁺) (s , xs) = help (T⁺ s) xs
        help (`Π T⁺) xs s = help (T⁺ s) (xs s)
        help (deleteΣ s O) xs = refl , help O xs
        help (deleteσ k O) xs = refl , help O xs
