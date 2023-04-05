

open import Data.Nat hiding (fold)
open import Data.Fin hiding (fold ; lift )
open import Data.Product
open import Data.Sum
open import Data.Unit

open import Relation.Binary.PropositionalEquality

open import Logic.Logic
open import Logic.IProp 
open import Level renaming (zero to zeroL ; suc to sucL)
open Logic.IProp.Applicative {zeroL}

open import IDesc.IDesc
open import IDesc.Fixpoint
open import IDesc.InitialAlgebra
open import IDesc.Lifting
open import IDesc.Induction

open import Orn.Ornament.Examples.Lifting hiding (□) renaming (□h to □ho)
open import Orn.Ornament

module Orn.AlgebraicOrnament.Coherence
           {K : Set }
           {X : K → Set }
           (D : func  K K)
           (α : ⟦ D ⟧func X ⇒ X) where

open import Orn.AlgebraicOrnament
open import Orn.Ornament.Algebra {u = proj₁} (algOrn D α)
open import Orn.Ornament.CartesianMorphism

forgetAlgOrn : ∀{k x} → μ (algOrnD D α) (k , x) → μ D k
forgetAlgOrn = forget

-- Thanks to Andrea Vezzosi for the proof!

-- Paper: Remark 4.21
coherentOrn : ∀{k x} → 
                (t : μ (algOrnD D α) (k , x)) → 
                ⊢ x ≡ fold D α (forget t)
coherentOrn = induction (algOrnD D α) P
                        (λ {i}{xs} → step {i} {xs})

    where P : {kx : Σ K X} → μ (algOrnD D α) kx → Set 
          P {(k , x)} t = ⊢ x ≡ fold D α (forget t)

          step' : (kx : Σ K X)
                  (D' : IDesc  K)
                  (α' : ⟦ D' ⟧ X → X (proj₁ kx)) →
                  let algOrnD' : IDesc  (Σ K X)
                      algOrnD' =  Desc.algOrnD (proj₁ kx) (proj₂ kx) D' α' in
                  (xs : ⟦ algOrnD' ⟧ (μ (algOrnD D α))) →
                  □h algOrnD' (λ {kx} t → ⊢ proj₂ kx ≡ fold D α  (forget t)) xs →
                  ⊢ proj₁ xs ≡ Fold.hyps D α D' 
                                           (forgetOrnNT (algOrn D α) (□ho D' (proj₁ xs))
                                             (Fold.hyps (algOrnD D α) forgetAlg ⟦ □ho D' (proj₁ xs) ⟧Orn  (proj₂ (proj₂ xs))))
          step' (k , x) (`var i) α' (xs , q , xxs) ih = ih
          step' (k , x) `1  α' (tt , q , tt) tt = pf refl
          step' (k , x) (D₁ `× D₂)  α' 
                ((xs₁ , xs₂) , q  , xxs₁ , xxs₂) (ih₁ , ih₂) = 
                cong₂ (λ x y → (x , y)) <$>
                  step' (k , x) D₁ (λ xs₁ → α' (xs₁ , xs₂)) (xs₁ , q , xxs₁) ih₁ ⊛ 
                  step' (k , x) D₂ (λ xs₂ → α' (xs₁ , xs₂)) (xs₂ , q , xxs₂) ih₂
          step' (k , x) (`σ n T)  α' ((s , xs) , q , xxs) ih = 
                cong⊢ (λ x → s , x) 
                      (step' (k , x) (T s) (λ xs → α' (s , xs)) (xs , q , xxs) ih)
          step' (k , x) (`Σ S T)  α' ((s , xs) , q , xxs) ih = 
                cong⊢ (λ x → s , x) 
                      (step' (k , x) (T s) (λ xs → α' (s , xs)) (xs , q , xxs) ih)
          step' (k , .(α' f)) (`Π S T)  α' (f , refl , xxs) ih = 
                extensionality (λ s → 
                  step' (k , α' f) (T s) (λ xs → α' f ) (f s , refl , (xxs s)) (ih s))

          step : DAlg (algOrnD D α) P
          step {(k , .(α xs))} {(xs , refl , xxs)} ih =
            cong⊢ α (step' (k , α xs) 
                           (func.out D k) (α {k}) 
                           ((xs , refl ,  xxs)) ih)
