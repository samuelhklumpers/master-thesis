open import Function

open import Level

open import Data.Product
open import Data.Unit 

open import Relation.Binary.PropositionalEquality

open import Logic.Logic
open import Logic.IProp
open Logic.IProp.Applicative {zero}

open import IDesc.IDesc
open import IDesc.Lifting
open import IDesc.Fixpoint
open import IDesc.Induction
open import IDesc.InitialAlgebra

open import Orn.Ornament

module Orn.Reornament.Coherence
         {K I : Set }
         {D : func  I I}
         {u : K → I}
         (o : orn D u u) 
       where

open import Logic.IProp

open import Orn.Reornament 
open import Orn.Ornament.Algebra o 
open import Orn.Ornament.CartesianMorphism
open import Orn.Reornament.Algebra o

-- Paper: Remark 4.32
coherentOrn : ∀{k t} → 
                (t⁺ : μ ⌈ o ⌉D (k , t)) → 
                ⊢ t ≡ forget (forgetReornament t⁺)
coherentOrn {k}{t} = induction (⌈ o ⌉D) P
                        (λ {i}{xs} → step {i} {xs})

    where P : {kx : Σ K (μ D ∘ u)} → μ ⌈ o ⌉D kx → Set 
          P {(k , x)} t⁺ = ⊢ x ≡ fold ⟦ o ⟧orn  forgetAlg (forgetReornament t⁺)

          step' : (D' : IDesc I)
                  (i :  ⟦ D' ⟧ (μ D))
                  (o' : Orn u D') →
                  let reornD' : IDesc (Σ K (μ D ∘ u))
                      reornD' = ⟦ Reorn o' i ⟧Orn in
                  (xs : ⟦ reornD' ⟧ (μ ⌈ o ⌉D)) → 
                  □h reornD' (λ {kx} t⁺ → ⊢ proj₂ kx ≡ fold ⟦ o ⟧orn forgetAlg (forgetReornament t⁺)) xs →
                  ⊢ i ≡ forgetOrnNT o o' 
                            (Fold.hyps ⟦ o ⟧orn forgetAlg ⟦ o' ⟧Orn 
                                (forgetOrnNT ⌈ o ⌉ (Reorn o' i) 
                                    (Fold.hyps ⌈ o ⌉D (λ {i} → reornAlgebra {i}) reornD' xs)))
          step' D i (insert S D⁺) (s , xs) ih = step' D i (D⁺ s) xs ih
          step' .(`var (u k)) ⟨ i ⟩ (`var (inv k)) ⟨ xs ⟩ ih = ih
          step' .`1 tt `1 xs ih = pf refl
          step' .(D₁ `× D₂) (i₁ , i₂) (_`×_ {D₁}{D₂} O₁ O₂) (xs₁ , xs₂) (ih₁ , ih₂) = 
            cong₂ (λ x y → (x , y)) <$>
              step' D₁ i₁ O₁ xs₁ ih₁ ⊛
              step' D₂ i₂ O₂ xs₂ ih₂
          step' .(`σ n T) (k , i) (`σ {n} {T} T⁺) xs ih = cong⊢ (λ x → (k , x )) (step' (T k) i (T⁺ k) xs ih)
          step' .(`Σ S T) (s , i) (`Σ {S} {T} T⁺) xs ih = cong⊢ (λ x → (s , x )) (step' (T s) i (T⁺ s) xs ih)
          step' .(`Π S T) i (`Π {S} {T} T⁺) xs ih = extensionality (λ s → step' (T s) (i s) (T⁺ s) (xs s) (ih s))
          step' .(`Σ S T) (s , i) (deleteΣ {S} {T} .s o') (refl , xs) ih = cong⊢ (λ x → (s , x)) (step' (T s) i  o' xs ih)
          step' .(`σ n T) (k , i) (deleteσ {n} {T} .k o') (refl , xs) ih = cong⊢ (λ x → (k , x)) (step' (T k) i  o' xs ih)


          step : DAlg (⌈ o ⌉D) P
          step {(k , ⟨ xs ⟩)} {os} ps = cong⊢ ⟨_⟩ (step' (func.out D (u k)) xs (orn.out o k) os ps)
