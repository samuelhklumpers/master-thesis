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

open import Data.Empty
--open import Data.Product renaming (proj₁ to fst; proj₂ to snd)
open import Data.Sum

open import Function.Base
open import Tex.Background hiding (_≡_)
\end{code}

\begin{code}
private variable
  I J K L : Type
  A B C X Y Z : Type
  P P′ : Type
  Γ Δ Θ : Tel P
  U V W : ExTel Γ

infixr 5 _∷_
\end{code}

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


_⊧_ : (V : Tel P) → V ⊢ Type → Type
V ⊧ S = ∀ p → S p

_▷′_ : (Γ : Tel P) (S : Type) → Tel P
Γ ▷′ S = Γ ▷ λ _ → S

\begin{code}
_&_⊢_ : (Γ : Tel ⊤) → ExTel Γ → Type → Type
Γ & V ⊢ A = V ⊢ A
\end{code}

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

data Con-ix (Γ : Tel ⊤) (V : ExTel Γ) (I : Type) : Type
data U-ix (Γ : Tel ⊤) (I : Type) : Type where
  []   : U-ix Γ I
  _∷_  : Con-ix Γ ∅ I → U-ix Γ I → U-ix Γ I

data Con-ix Γ V I where
  𝟙   : V ⊢ I → Con-ix Γ V I
  ρ   : V ⊢ I → Con-ix Γ V I → Con-ix Γ V I
  σ   : (S : V ⊢ Type) → Con-ix Γ (V ▷ S) I → Con-ix Γ V I

⟦_⟧C-ix : Con-ix Γ V I → (⟦ Γ ⟧tel tt → I → Type) → (⟦ Γ & V ⟧tel → I → Type)
⟦ 𝟙 j    ⟧C-ix X pv i = i ≡ (j pv)
⟦ ρ j C  ⟧C-ix X pv@(p , v) i = X p (j pv) × ⟦ C ⟧C-ix X pv i
⟦ σ S C  ⟧C-ix X pv@(p , v) i = Σ[ s ∈ S pv ] ⟦ C ⟧C-ix X (p , v , s) i

⟦_⟧D-ix : U-ix Γ I → (⟦ Γ ⟧tel tt → I → Type) → (⟦ Γ ⟧tel tt → I → Type)
⟦ []      ⟧D-ix X p i = ⊥
⟦ C ∷ Cs  ⟧D-ix X p i = ⟦ C ⟧C-ix X (p , tt) i  ⊎ ⟦ Cs ⟧D-ix X p i

data μ-ix (D : U-ix Γ I) (p : ⟦ Γ ⟧tel tt) (i : I) : Type where
  con : ⟦ D ⟧D-ix (μ-ix D) p i → μ-ix D p i

\begin{code}
uncon : ∀ {D : U-ix Γ I} {p i} → μ-ix D p i → ⟦ D ⟧D-ix (μ-ix D) p i
uncon (con x) = x

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

%<*uniform>
\AgdaTarget{uniformC}
\AgdaTarget{uniformD}
\begin{code}
uniformC  : ∀ {Γ V W} (CD : Con-nest Γ V ⊤)
          → (p : W ⊢ ⟦ Γ & V ⟧tel) → Con-ix ∅ W (⟦ Γ ⟧tel tt)
uniformC (𝟙 j)       p  = 𝟙 λ { w → p w .fst }
uniformC (ρ j g CD)  p  = ρ (λ { w → g (p w .fst) })
                        ( uniformC CD p)
uniformC (σ S CD)    p  = σ (λ { w → S (p w) })
                        ( uniformC CD λ { (_ , (w , s))
                          → let (p' , v) = p (_ , w) in p' , v , s })

uniformD : U-nest Γ ⊤ → U-ix ∅ (⟦ Γ ⟧tel tt)
uniformD []                = []
uniformD {Γ = Γ} (CD ∷ D)  = σ (λ _ → ⟦ Γ ⟧tel tt)
                           ( uniformC CD (λ (_ , (_ , p)) → (p , _)))
                           ∷ uniformD D
\end{code}
%</uniform>

mapμ : ∀ {I} {D' : U-ix Γ I} {D : U-ix Γ I}
    → (∀ X → ⟦ D' ⟧D-ix X →₃ ⟦ D ⟧D-ix X) → μ-ix D' →₃ μ-ix D
mapμ f = fold (λ p i x → con (f _ p i x))

_∘3_ : {A B : Type} {X Y Z : A → B → Type} → Y →₃ Z → X →₃ Y → X →₃ Z
(g ∘3 f) _ _ x = g _ _ (f _ _ x)

StalkC : ∀ {Γ V} → Con-nest Γ V ⊤ → Con-ix ∅ ∅ ⊤
StalkC (𝟙 j)      = 𝟙 _
StalkC (ρ j g CD) = {! ? ⊎ StalkC CD !} -- need Σ-descriptions
StalkC (σ S CD)   = StalkC CD

StalkD : U-nest Γ ⊤ → U-ix ∅ ⊤
StalkD []       = []
StalkD (CD ∷ D) = StalkC CD ∷ StalkD D

defunC : ∀ {Γ V W I} → (CD : Con-nest Γ V ⊤) → (W ⊢ (⟦ StalkC CD ⟧C-ix I _ _ → I tt tt))
       →  (i : W ⊢ I tt tt) (h : I tt tt → Cxf Γ Γ)
          (v : ∀ p i → ⟦ W ⟧tel (h i p) → ⟦ Γ & V ⟧tel)
       →  Con-ix Γ W (I tt tt)
defunC (𝟙 j)      f i h v = 𝟙 i
defunC (ρ j g CD) f i h v = ρ (λ { w → {!f w!} }) (defunC CD (λ { w → f w ∘ (i w ,_) }) i h v)
defunC (σ S CD)   f i h v = σ (λ { w → S {!!} }) {!!}

defunD : ∀ {I} (D : U-nest Γ ⊤) → (⟦ StalkD D ⟧D-ix I →₃ I) → U-ix Γ (I tt tt)
defunD []       f = []
defunD (CD ∷ D) f = {!defunC !} ∷ defunD D (f ∘3 λ _ _ → inj₂)


RandomD : U-nest (∅ ▷ const Type) ⊤
RandomD = 𝟙 _ 
        ∷ σ (λ { ((_ , A) , _) → A })
        ( ρ _ (λ { (_ , A) → (_ , (A × A)) })
        ( 𝟙 _))
        ∷ σ (λ { ((_ , A) , _) → A × A })
        ( ρ _ (λ { (_ , A) → (_ , (A × A)) })
        ( 𝟙 _))
        ∷ []

%<*Pair>
\AgdaTarget{power}
\AgdaTarget{Pair, pair}
\begin{code}
power : ℕ → (A → A) → A → A
power zero    f x = x
power (suc n) f x = f (power n f x)

data Pair (A : Type) : Type where
  pair : A → A → Pair A
\end{code}
%</Pair>

%<*RandomD-2>
\begin{code}
RandomD-2  : U-ix (∅ ▷ const Type) ℕ
RandomD-2  = σ (λ _ → ℕ)
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
\end{code}
%</RandomD-2>

%<*RandomD-1>
\begin{code}
RandomD-1  : U-ix ∅ Type
RandomD-1  = σ (λ _ → Type)
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
\end{code}
%</RandomD-1>

RandomD-3 : U-ix ∅ (⟦ ∅ ▷ const Type ⟧tel tt)
RandomD-3 = uniformD RandomD-1

example : μ-ix RandomD-3 tt (tt , ℕ)
example = con (inj₂ (inj₁ (_ , (0 , ((con (inj₂ (inj₁ (_ , ((1 , 2) , (con (inj₁ (_ , refl)) , refl)))))) , refl)))))
