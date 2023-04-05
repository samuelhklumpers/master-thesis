
open import Function

open import Data.Unit hiding (_≟_)
open import Data.Product

open import Relation.Binary.PropositionalEquality

open import Logic.Logic

open import IDesc.IDesc
open import IDesc.Fixpoint
open import IDesc.InitialAlgebra

open import Orn.Ornament



module FunOrn.Lift.MkReorn
         {K I : Set }
         {D : func  I I}
         {u : K → I}
         (o : orn D u u)
       where

open import Orn.Reornament

-- Paper: Definition 6.14
Extension : ∀{D}{X : I → Set } → Orn u D → ⟦ D ⟧ X → Set 
Extension `1 tt = ⊤
Extension (O₁ `× O₂) (xs₁ , xs₂) = Extension O₁ xs₁ × Extension O₂ xs₂
Extension (`σ T⁺) (k , xs) = Extension (T⁺ k) xs
Extension (`Σ T⁺) (s , xs) = Extension (T⁺ s) xs
Extension (`Π T⁺) f = (s : _) → Extension (T⁺ s) (f s)
Extension (`var (inv k)) xs = ⊤
Extension (insert S D⁺) xs = Σ[ s ∈ S ] Extension (D⁺ s) xs
Extension {X = X} (deleteΣ {T = T} s o) (s' , xs) = Σ[ q ∈ s' ≡ s ] Extension o (subst (λ s → ⟦ T s ⟧ X) q xs) 
Extension {X = X} (deleteσ {T = T} k o) (k' , xs) = Σ[ q ∈ k' ≡ k ] Extension o (subst (λ k → ⟦ T k ⟧ X) q xs)

-- Paper: Definition 6.15
Structure : ∀{D'}(O : Orn u D') →
            (xs' : ⟦ D' ⟧ (μ D)) → Extension O xs' → Set 
Structure `1 tt tt = ⊤
Structure (O₁ `× O₂) (xs₁ , xs₂) (e₁ , e₂) = Structure O₁ xs₁ e₁ × Structure O₂ xs₂ e₂
Structure (`σ T⁺) (k , xs) e = Structure (T⁺ k) xs e
Structure (`Σ T⁺) (s , xs) e = Structure (T⁺ s) xs e
Structure (`Π T⁺) f e = (s : _) → Structure (T⁺ s) (f s) (e s)
Structure (`var (inv k)) xs tt =  (μ ⌈ o ⌉D (k , xs))
Structure (insert S D⁺) xs (s , e) = Structure (D⁺ s) xs e
Structure (deleteΣ s O) (.s , xs) (refl , e) = Structure O xs e
Structure (deleteσ k O) (.k , xs) (refl , e) = Structure O xs e

-- Paper: Definition 6.16
mkReorn : ∀{D' xs} → (O : Orn u D') → (e : Extension O xs) → Structure O xs e → ⟦ ⟦ Reorn O xs ⟧Orn ⟧ (μ ⌈ o ⌉D)
mkReorn (insert S D⁺) (s , e) xs = s , mkReorn (D⁺ s) e xs
mkReorn (`var (inv i)) e xs = xs
mkReorn `1 e xs₁ = tt
mkReorn (o₁ `× o₂) (e₁ , e₂) (xs₁ , xs₂) = mkReorn o₁ e₁ xs₁ , mkReorn o₂ e₂ xs₂
mkReorn (`σ T⁺) e xs = mkReorn (T⁺ _) e xs
mkReorn (`Σ T⁺) e xs = mkReorn (T⁺ _) e xs
mkReorn (`Π T⁺) e xs = λ s → mkReorn (T⁺ s) (e s) (xs s)
mkReorn (deleteΣ s o₁) (refl , e) xs = refl , mkReorn o₁ e xs
mkReorn (deleteσ k o₁) (refl , e) xs = refl , mkReorn o₁ e xs


Extra : {i : I}{i⁺ : u ⁻¹ i}
         (x : ⟦ D ⟧func (μ D) i) → Set 
Extra {i⁺ = inv i⁺} x = Extension (orn.out o i⁺) x

Args : {i : I}{i⁺ : u ⁻¹ i}
       (x : ⟦ D ⟧func (μ D) i)
       (e : Extra {i⁺ = i⁺} x) → Set 
Args {i⁺ = inv i⁺} x e = Structure (orn.out o i⁺) x e 


mkreorn : ∀{k xs} → (e : Extra {u k}{inv k} xs) → Args {u k}{inv k} xs e → μ ⌈ o ⌉D (k , ⟨ xs ⟩)
mkreorn e as = ⟨ (mkReorn (orn.out o _) e as) ⟩
