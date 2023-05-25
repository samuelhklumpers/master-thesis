{-# OPTIONS --type-in-type --with-K #-}


module Ornament.TypeInType.Desc where

open Agda.Primitive renaming (Set to Type)

open import Data.Unit
open import Data.Empty
open import Data.Product
open import Data.Sum hiding (map₂)
open import Data.Nat
open import Function.Base

open import Agda.Primitive.Cubical
open import Agda.Builtin.Cubical.Path
--open import Relation.Binary.PropositionalEquality hiding (J)


private variable
  J K L : Type
  A B C X Y Z : Type
  P P′ : Type


infixr 10 _∷_
infixr 10 _▷_


-- telescopes
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

⟦_&_⟧tel : (Γ : Tel ⊤) (V : ExTel Γ) → Type
⟦ Γ & V ⟧tel = Σ (⟦ Γ ⟧tel tt) ⟦ V ⟧tel

_&_⊢_ : (Γ : Tel ⊤) (V : ExTel Γ) → Type → Type
Γ & V ⊢ A = ⟦ Γ & V ⟧tel → A

Fun : Tel ⊤ → Type → Type
Fun Γ J = ⟦ Γ ⟧tel tt → J → Type

private variable
  Γ Δ Θ : Tel P
  U V W   : ExTel Γ

Cxf : (Γ Δ : Tel ⊤) → Type
Cxf Γ Δ = ⟦ Γ ⟧tel tt → ⟦ Δ ⟧tel tt

Exf : (Γ Δ : Tel ⊤) (V : ExTel Γ) (W : ExTel Δ) → Type
Exf Γ Δ V W = ⟦ Γ & V ⟧tel → ⟦ Δ & W ⟧tel

Vxf : (Γ : Tel ⊤) (V W : ExTel Γ) → Type
Vxf Γ V W = ∀ {p} → ⟦ V ⟧tel p → ⟦ W ⟧tel p

Exf-▷ : (f : Exf Γ Δ V W) (S : Δ & W ⊢ Type) → Exf Γ Δ (V ▷ (S ∘ f)) (W ▷ S)
Exf-▷ f S (p , v , s) = let (p' , v') = f (p , v) in p' , v' , s

Vxf-Exf : Vxf Γ V W → Exf Γ Γ V W
Vxf-Exf f (p , v) = p , f v

liftM2 : (A → B → C) → (X → A) → (X → B) → X → C
liftM2 f g h x = f (g x) (h x)


-- descriptions
{-# NO_POSITIVITY_CHECK #-}
data Desc (Γ : Tel ⊤) (J : Type) : Type
data μ (D : Desc Γ J) (p : ⟦ Γ ⟧tel tt) : J → Type
data Con (Γ : Tel ⊤) (J : Type) (V : ExTel Γ) : Type where
  𝟙 : Γ & V ⊢ J → Con Γ J V
  ρ : Γ & V ⊢ J → Cxf Γ Γ → Con Γ J V → Con Γ J V
  σ : (S : Γ & V ⊢ Type) → Vxf Γ (V ▷ S) W → Con Γ J W → Con Γ J V
  δ : (j : Γ & V ⊢ K) (g : Γ & V ⊢ ⟦ Δ ⟧tel tt) (D : Desc Δ K) (h : Vxf Γ (V ▷ liftM2 (μ D) g j) W) → Con Γ J W → Con Γ J V

σ+ : (S : Γ & V ⊢ Type) → Con Γ J (V ▷ S) → Con Γ J V
σ+ S C = σ S id C

σ- : (S : Γ & V ⊢ Type) → Con Γ J V → Con Γ J V
σ- S C = σ S proj₁ C

δ+ : (j : Γ & V ⊢ K) (g : Γ & V ⊢ ⟦ Δ ⟧tel tt) (D : Desc Δ K) → Con Γ J (V ▷ liftM2 (μ D) g j) → Con Γ J V
δ+ j g R D = δ j g R id D

δ- : (j : Γ & V ⊢ K) (g : Γ & V ⊢ ⟦ Δ ⟧tel tt) (D : Desc Δ K) → Con Γ J V → Con Γ J V
δ- j g R D = δ j g R proj₁ D

ρ0 : Γ & V ⊢ J → Con Γ J V → Con Γ J V
ρ0 i D = ρ i id D


data Desc Γ J where
  []  : Desc Γ J
  _∷_ : Con Γ J ∅ → Desc Γ J → Desc Γ J 

data Tag Γ : Type where
  CT : ExTel Γ → Tag Γ
  DT : Tag Γ

UnTag : (Γ : Tel ⊤) (J : Type) → Tag Γ → Type
UnTag Γ J (CT V) = Con Γ J V
UnTag Γ J DT     = Desc Γ J

UnFun : (Γ : Tel ⊤) (J : Type) → Tag Γ → Type
UnFun Γ J (CT V) = ⟦ Γ & V ⟧tel → J → Type
UnFun Γ J DT     = Fun Γ J


-- interpretation
⟦_⟧ : {t : Tag Γ} → UnTag Γ J t → Fun Γ J → UnFun Γ J t
⟦_⟧ {t = CT V} (𝟙 j)         X pv i         = i ≡ j pv
⟦_⟧ {t = CT V} (ρ j f D)     X pv@(p , v) i = X (f p) (j pv) × ⟦ D ⟧ X pv i
⟦_⟧ {t = CT V} (σ S h D)     X pv@(p , v) i = Σ[ s ∈ S pv ] ⟦ D ⟧ X (p , h (v , s)) i
⟦_⟧ {t = CT V} (δ j g R h D) X pv@(p , v) i = Σ[ s ∈ μ R (g pv) (j pv) ] ⟦ D ⟧ X (p , h (v , s)) i
⟦_⟧ {t = DT}   []            X p i = ⊥
⟦_⟧ {t = DT}   (C ∷ D)       X p i = (⟦ C ⟧ X (p , tt) i) ⊎ (⟦ D ⟧ X p i) 


data μ D p where
  con : ∀ {i} → ⟦ D ⟧ (μ D) p i → μ D p i
  

-- examples
module Descriptions where
  NatD : Desc ∅ ⊤
  NatD = 𝟙 _
       ∷ ρ0 _ (𝟙 _)
       ∷ []

  VecD : Desc (∅ ▷ const Type) ℕ
  VecD = 𝟙 (const 0)
       ∷ σ- (proj₂ ∘ proj₁) (σ+ (const ℕ) (ρ0 (proj₂ ∘ proj₂) (𝟙 (suc ∘ proj₂ ∘ proj₂))))
       ∷ []

  DigitD : Desc (∅ ▷ const Type) ⊤
  DigitD = σ- (proj₂ ∘ proj₁) (𝟙 _)
         ∷ σ- (proj₂ ∘ proj₁) (σ- (proj₂ ∘ proj₁) (𝟙 _))
         ∷ σ- (proj₂ ∘ proj₁) (σ- (proj₂ ∘ proj₁) (σ- (proj₂ ∘ proj₁) (𝟙 _)))
         ∷ []
         
  data Node (A : Type) : Type where
    two   : A → A     → Node A
    three : A → A → A → Node A

  FingerD : Desc (∅ ▷ const Type) ⊤
  FingerD = 𝟙 _
          ∷ σ- (proj₂ ∘ proj₁) (𝟙 _)
          ∷ δ- _ proj₁ DigitD (ρ _ (λ { (_ , A) → (_ , Node A) }) (δ- _ proj₁ DigitD (𝟙 _)))
          ∷ []


-- ornaments
data Orn : Type where
data ConOrn (f : Exf Δ Γ W V) (e : K → L) : Con Γ J V → Con Δ K W → Type where
  𝟙 : ∀ {i j} → (∀ p → e (j p) ≡ i (f p)) → ConOrn f e (𝟙 i) (𝟙 j)
  σ : ∀ {S} {V'} {W'} {D : Con Γ J V'} {E : Con Δ K W'} {g : Vxf Γ _ _} {h : Vxf Δ _ _} {f'}
    → ConOrn f' e D E → (∀ p → Vxf-Exf g (Exf-▷ f S p) ≡ f' (Vxf-Exf h p)) → ConOrn f e (σ S g D) (σ (S ∘ f) h E)

  {- σ : ∀ {S} {V'} {W'} {D : Con Γ J V'} {E : Con Δ K W'} {g : Vxf Γ _ _} {h : Vxf Δ _ _} {f'}
    → (k : ∀ p s → proj₁ (f p) ≡ proj₁ (f' (proj₁ p , (h (proj₂ p , s))))) → (∀ p s → g (proj₂ (f p) , s) ≡ {!proj₂ (f' ?)!}) → ConOrn f' e D E → ConOrn f e (σ S g D) (σ (S ∘ f) h E) -}


{- diagrams

-- σ
% https://q.uiver.app/#q=WzAsMTMsWzEsMSwiXFxHYW1tYSxWIl0sWzAsMSwiXFxEZWx0YSxXIl0sWzIsMSwiXFxtYXRocm17VHlwZX0iXSxbMCwwLCJKIl0sWzEsMCwiSSJdLFsxLDIsIlZcXHJoZCBTIl0sWzIsMiwiViciXSxbMSwzLCJXXFxyaGQgKFNcXGNpcmMgZikiXSxbMiwzLCJXJyJdLFszLDIsIlxcR2FtbWEsVlxccmhkIFMiXSxbNCwyLCJcXEdhbW1hLFYnIl0sWzMsMywiXFxEZWx0YSxXXFxyaGQgKFNcXGNpcmMgZikiXSxbNCwzLCJcXERlbHRhLFcnIl0sWzEsMCwiZiJdLFswLDIsIlMiXSxbMyw0LCJlIl0sWzUsNiwiZyJdLFs3LDgsImgiXSxbOSwxMCwiXFxoYXR7Z30iXSxbMTEsMTIsIlxcaGF0e2h9Il0sWzEyLDEwLCJmJyIsMl0sWzExLDksImYgXFxyaGQgUyJdXQ==



-}
