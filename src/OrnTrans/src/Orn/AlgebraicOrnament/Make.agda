 

open import Data.Product
open import Data.Unit

open import Logic.Logic

open import IDesc.IDesc
open import IDesc.Fixpoint
open import IDesc.InitialAlgebra
open import IDesc.Induction
open import IDesc.Lifting

open import Relation.Binary.PropositionalEquality

module Orn.AlgebraicOrnament.Make
           {K : Set }
           {X : K → Set }
           (D : func  K K)
           (α : ⟦ D ⟧func X ⇒ X) where

open import Orn.Ornament

import Orn.AlgebraicOrnament
open Orn.AlgebraicOrnament.Func D α
open Orn.AlgebraicOrnament hiding (algOrnD)

open import Orn.Ornament.Examples.Lifting renaming (□h to □ho)


toILift : {I : Set }
          {X : I → Set }
          (D : IDesc  I)
          (P : ∀{i} → X i → Set )
          (xs : ⟦ D ⟧ X) →
          □h D P xs → 
          ⟦ (⟦ □ho {L = I} D xs ⟧Orn) ⟧ 
            (λ ix → P {proj₁ ix} (proj₂ ix))
toILift (`var i) P xs ih = ih
toILift `1 P xs ih = ih
toILift (D₁ `× D₂) P (xs₁ , xs₂) (ih₁ , ih₂) = 
  toILift D₁ P xs₁ ih₁ , toILift D₂ P xs₂ ih₂
toILift (`σ n T) P (k , xs) ih = toILift (T k) P xs ih
toILift (`Σ S T) P (s , xs) ih = toILift (T s) P xs ih
toILift (`Π S T) P xs ih = λ s → toILift (T s) P (xs s) (ih s)

-- This generalizes (slightly, but not fully) □map:
□gmap : (D' : IDesc  K)
           {Q : ∀{i} → X i → Set }
           {α : ∀{i} → ⟦ func.out D i ⟧ X → X i}
           (xs : ⟦ D' ⟧ (μ D)) →
           □h D' (λ t → Q (fold D α t)) xs →
           □h D' Q (Fold.hyps D α D' xs)
□gmap (`var i) xs ih = ih
□gmap `1 xs ih = ih
□gmap (D₁ `× D₂) (xs₁ , xs₂) (ih₁ , ih₂) = 
    □gmap D₁ xs₁ ih₁ , □gmap D₂ xs₂ ih₂
□gmap (`σ n T) (k , xs) ih = □gmap (T k) xs ih
□gmap (`Σ S T) (s , xs) ih = □gmap (T s) xs ih
□gmap (`Π S T) xs ih = λ s → □gmap (T s) (xs s) (ih s)
  

-- Paper: Remark 4.21
-- Typeset: make D α xs = make D^{α} xs
make : ∀{k} → (x : μ D k) → μ algOrnD (k , fold D α x)
make x = induction D (λ {k} x → μ algOrnD (k , fold D α x)) step x
        where step' : (k : K)
                      (D' : IDesc  K)
                      (α' : ⟦ D' ⟧ X → X k)
                      (xs : ⟦ D' ⟧ (μ D))
                      (ih : □h D' (λ {k} x → μ algOrnD (k , fold D α x)) xs) →
                      ⟦ Desc.algOrnD k (α' (Fold.hyps D α D' xs))  D' α' ⟧ (μ algOrnD)

              step' k (`var i) α' xs ih = Fold.fold D α xs , 
                                          refl , ih
              step' k `1 α' tt tt = tt , (refl , tt)
              step' k (D₁ `× D₂) α' (xs₁ , xs₂) (ih₁ , ih₂) = 
                ( Fold.hyps D α D₁ xs₁ , Fold.hyps D α D₂ xs₂) , 
                refl , 
                toILift D₁ (λ {k} x → μ algOrnD (k , x)) 
                     (Fold.hyps D α D₁ xs₁) 
                     (□gmap D₁ xs₁ ih₁) , 
                toILift D₂ (λ {k} x → μ algOrnD (k , x)) 
                     (Fold.hyps D α D₂ xs₂)
                     (□gmap D₂ xs₂ ih₂) 
              step' k (`σ n T) α' (s , xs) ih = 
                (s , Fold.hyps D α (T s) xs) , 
                refl , 
                toILift (T s) (λ {k} x → μ algOrnD (k , x)) 
                     (Fold.hyps D α (T s) xs)
                     (□gmap (T s) xs ih)
              step' k (`Σ S T) α' (s , xs) ih = 
                (s , (Fold.hyps D α (T s) xs)) ,
                refl , 
                toILift (T s) (λ {k} x → μ algOrnD (k , x)) 
                     (Fold.hyps D α (T s) xs)
                     (□gmap (T s) xs ih)
              step' k (`Π S T) α' xs ih = 
                (λ s → Fold.hyps D α (T s) (xs s)) , 
                refl , 
                λ s → toILift (T s) 
                           (λ {k₁} x₁ → μ algOrnD (k₁ , x₁))
                           (Fold.hyps D α (T s) (xs s))
                           (□gmap (T s) (xs s) (ih s))

              step : DAlg D (λ {k} x → μ algOrnD (k , fold D α x))
              step {k}{xs} x = ⟨ step' k (func.out D k) (α {k}) xs x ⟩
