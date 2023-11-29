\begin{code}
{-# OPTIONS --type-in-type #-}

module Appendix.NoNesting where

open import Agda.Primitive
  using    ( Level
           ; SSet )
  renaming ( lzero to ℓ-zero
           ; lsuc  to ℓ-suc
           ; _⊔_   to ℓ-max
           ; Set   to Type
           ; Setω  to Typeω )

open import Relation.Binary.PropositionalEquality hiding (J)

open import Data.Unit
open import Data.Empty
open import Data.Product renaming (proj₁ to fst; proj₂ to snd)
open import Data.Sum
open import Data.Nat

open import Function.Base
\end{code}

\begin{code}
private variable
  I J K L : Type
  A B C X Y Z : Type
  P P′ : Type

infixr 5 _∷_
infixr 10 _▷_

data Tel (P : Type) : Type
⟦_⟧tel : (Γ : Tel P) → P → Type

_⊢_ : (Γ : Tel P) → Type → Type
Γ ⊢ A = Σ _ ⟦ Γ ⟧tel → A

data Tel P where
  ∅   : Tel P
  _▷_ : (Γ : Tel P) (S : Γ ⊢ Type) → Tel P

⟦ ∅     ⟧tel p = ⊤
⟦ Γ ▷ S ⟧tel p = Σ (⟦ Γ ⟧tel p) (S ∘ (p ,_)) 

ExTel : Tel ⊤ → Type
ExTel Γ = Tel (⟦ Γ ⟧tel tt)

private variable
    Γ Δ Θ : Tel P
    U V W : ExTel Γ

_⊧_ : (V : Tel P) → V ⊢ Type → Type
V ⊧ S = ∀ p → S p

_▷′_ : (Γ : Tel P) (S : Type) → Tel P
Γ ▷′ S = Γ ▷ λ _ → S

_&_⊢_ : (Γ : Tel ⊤) → ExTel Γ → Type → Type
Γ & V ⊢ A = V ⊢ A

⟦_&_⟧tel : (Γ : Tel ⊤) (V : ExTel Γ) → Type
⟦ Γ & V ⟧tel = Σ (⟦ Γ ⟧tel tt) ⟦ V ⟧tel

Cxf : (Γ Δ : Tel ⊤) → Type
Cxf Γ Δ = ⟦ Γ ⟧tel tt → ⟦ Δ ⟧tel tt

Vxf : (f : Cxf Γ Δ) (V : ExTel Γ) (W : ExTel Δ) → Type
Vxf f V W = ∀ {p} → ⟦ V ⟧tel p → ⟦ W ⟧tel (f p)

over : {f : Cxf Γ Δ} → Vxf f V W → ⟦ Γ & V ⟧tel → ⟦ Δ & W ⟧tel
over g (p , v) = _ , g v

Vxf-▷ : {V W : ExTel Γ} (f : Vxf id V W) (S : W ⊢ Type) → Vxf id (V ▷ (S ∘ over f)) (W ▷ S)
Vxf-▷ f S (p , v) = f p , v
\end{code}

\begin{code}
data Con-ix (Γ : Tel ⊤) (V : ExTel Γ) (I : Type) : Type
data U-ix (Γ : Tel ⊤) (I : Type) : Type where
  []   : U-ix Γ I
  _∷_  : Con-ix Γ ∅ I → U-ix Γ I → U-ix Γ I

data Con-ix Γ V I where
  𝟙   : V ⊢ I → Con-ix Γ V I
  ρ   : V ⊢ I → Con-ix Γ V I → Con-ix Γ V I
  σ   : (S : V ⊢ Type) → Con-ix Γ (V ▷ S) I → Con-ix Γ V I

⟦_⟧C : Con-ix Γ V I → (⟦ Γ ⟧tel tt → I → Type) → (⟦ Γ & V ⟧tel → I → Type)
⟦ 𝟙 j    ⟧C X pv i = i ≡ (j pv)
⟦ ρ j C  ⟧C X pv@(p , v) i = X p (j pv) × ⟦ C ⟧C X pv i
⟦ σ S C  ⟧C X pv@(p , v) i = Σ[ s ∈ S pv ] ⟦ C ⟧C X (p , v , s) i

⟦_⟧D : U-ix Γ I → (⟦ Γ ⟧tel tt → I → Type) → (⟦ Γ ⟧tel tt → I → Type)
⟦ []      ⟧D X p i = ⊥
⟦ C ∷ Cs  ⟧D X p i = ⟦ C ⟧C X (p , tt) i  ⊎ ⟦ Cs ⟧D X p i

data μ-ix (D : U-ix Γ I) (p : ⟦ Γ ⟧tel tt) (i : I) : Type where
  con : ⟦ D ⟧D (μ-ix D) p i → μ-ix D p i
\end{code}

\begin{code}
data U-nest (Γ : Tel ⊤) (J : Type) : Type
data Con-nest (Γ : Tel ⊤) (V : ExTel Γ) (J : Type) : Type 

data U-nest Γ J where
  []   : U-nest Γ J
  _∷_  : Con-nest Γ ∅ J → U-nest Γ J → U-nest Γ J
  
data Con-nest Γ V J where
  𝟙  :  (j : Γ & V ⊢ J) → Con-nest Γ V J
  
  ρ  :  (j : Γ & V ⊢ J) (g : Cxf Γ Γ) (C : Con-nest Γ V J)
     →  Con-nest Γ V J
     
  σ  :  (S : V ⊢ Type) (C : Con-nest Γ (V ▷ S) J)
     →  Con-nest Γ V J
\end{code}

\begin{code}
transformC : ∀ {Γ V W} (CD : Con-nest Γ V ⊤) → (p : W ⊢ ⟦ Γ & V ⟧tel) → Con-ix ∅ W (⟦ Γ ⟧tel tt)
transformC (𝟙 j) p = 𝟙 λ { w → p w .fst }
transformC (ρ j g CD) p = ρ (λ { w → g (p w .fst) }) (transformC CD p)
transformC (σ S CD) p = σ (λ { w → S (p w) }) (transformC CD λ { (_ , (w , s)) → p (_ , w) .fst , (p (_ , w) .snd , s) })

transform : U-nest Γ ⊤ → U-ix ∅ (⟦ Γ ⟧tel tt)
transform []       = []
transform {Γ = Γ} (CD ∷ D) = σ (λ _ → ⟦ Γ ⟧tel tt) (transformC CD (λ (_ , (_ , p)) → (p , _))) ∷ transform D
\end{code}

\begin{code}
RandomD : U-nest (∅ ▷ const Type) ⊤
RandomD = 𝟙 _ 
        ∷ σ (λ { ((_ , A) , _) → A })
        ( ρ _ (λ { (_ , A) → (_ , (A × A)) })
        ( 𝟙 _))
        ∷ σ (λ { ((_ , A) , _) → A × A })
        ( ρ _ (λ { (_ , A) → (_ , (A × A)) })
        ( 𝟙 _))
        ∷ []

power : ℕ → (A → A) → A → A
power zero    f x = x
power (suc n) f x = f (power n f x)

data Pair (A : Type) : Type where
  pair : A → A → Pair A

RandomD′ : U-ix (∅ ▷ const Type) ℕ
RandomD′ = σ (λ _ → ℕ)
         ( 𝟙 λ { (_ , (_ , n)) → n }) 
         ∷ σ (λ _ → ℕ)
         ( σ (λ { ((_ , A) , (_ , n)) → power n Pair A })
         ( ρ (λ { (_ , ((_ , n) , _)) → suc n })
         ( 𝟙 λ { (_ , ((_ , n) , _)) → n } )))
         ∷ σ (λ _ → ℕ)
         ( σ (λ { ((_ , A) , (_ , n)) → power (suc n) Pair A })
         ( ρ (λ { (_ , ((_ , n) , _)) → suc n })
         ( 𝟙 λ { (_ , ((_ , n) , _)) → n } )))
         ∷ []

RandomD″ : U-ix ∅ Type
RandomD″ = σ (λ _ → Type)
         ( 𝟙 λ { (_ , (_ , A)) → A }) 
         ∷ σ (λ _ → Type)
         ( σ (λ { (_ , (_ , A)) → A })
         ( ρ (λ { (_ , ((_ , A) , _)) → A × A })
         ( 𝟙 λ { (_ , ((_ , A) , _)) → A } )))
         ∷ σ (λ _ → Type)
         ( σ (λ { (_ , (_ , A)) → A × A })
         ( ρ (λ { (_ , ((_ , A) , _)) → A × A })
         ( 𝟙 λ { (_ , ((_ , A) , _)) → A } )))
         ∷ []

RandomD‴ : U-ix ∅ (⟦ ∅ ▷ const Type ⟧tel tt)
RandomD‴ = transform RandomD

example : μ-ix RandomD‴ tt (tt , ℕ)
example = con (inj₂ (inj₁ ((tt , ℕ) , (0 , ((con (inj₂ (inj₁ (((tt , (ℕ × ℕ))) , ((1 , 2) , (con (inj₁ (((tt , ((ℕ × ℕ) × (ℕ × ℕ)))) , refl)) , refl)))))) , refl)))))
\end{code}
