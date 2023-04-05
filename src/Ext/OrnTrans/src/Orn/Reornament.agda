
open import Function

open import Data.Unit hiding (_≟_)
open import Data.Product

open import Relation.Binary.PropositionalEquality

open import Logic.Logic

open import IDesc.IDesc
open import IDesc.Fixpoint
open import IDesc.InitialAlgebra

open import Orn.Ornament



module Orn.Reornament 
         {K I : Set }
         {D : func  I I}
         {u : K → I}
       where


forgetIdx : Σ K (μ D ∘ u) → K
forgetIdx = proj₁ 

-- Paper: Definition 4.29
-- Typeset: Reorn O = ⌈ O ⌉
Reorn : ∀{D'} → (O : Orn u D') → ⟦ D' ⟧ (μ D) → Orn forgetIdx ⟦ O ⟧Orn
Reorn `1 tt = `1
Reorn (O₁ `× O₂) (xs₁ , xs₂) = Reorn O₁ xs₁ `× Reorn O₂ xs₂
Reorn (`σ T⁺) (k , xs) = deleteσ k (Reorn (T⁺ k) xs)
Reorn (`Σ T⁺) (s , xs) = deleteΣ s (Reorn (T⁺ s) xs)
Reorn (`Π T⁺) f = `Π λ s → Reorn (T⁺ s) (f s)
Reorn (`var (inv k)) xs = `var (inv (k , xs))
Reorn (insert S D⁺) xs = `Σ λ s → Reorn (D⁺ s) xs
Reorn (deleteΣ {T = T} s o) (s' , xs) = insert (s' ≡ s) λ q → Reorn o (subst (λ s → ⟦ T s ⟧ (μ D)) q xs) 
Reorn (deleteσ {T = T} k o) (k' , xs) = insert (k' ≡ k) λ { q → Reorn o (subst (λ k → ⟦ T k ⟧ (μ D)) q xs) }

-- Paper: Definition 4.29
⌈_⌉ : (o : orn D u u) → orn ⟦ o ⟧orn forgetIdx forgetIdx
⌈ o ⌉ = mk (λ { (k , ⟨ xs ⟩) → Reorn (orn.out o k) xs })


⌈_⌉D : orn D u u → func  (Σ K (μ D ∘ u)) (Σ K (μ D ∘ u))
⌈ o ⌉D = ⟦ ⌈ o ⌉ ⟧orn
