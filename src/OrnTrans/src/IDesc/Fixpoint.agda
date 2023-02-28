module IDesc.Fixpoint 
          {I : Set} where

open import IDesc.IDesc

data μ (D : func  I I)(i : I) : Set  where
  ⟨_⟩ : ⟦ D ⟧func (μ D) i → μ D i