\begin{code}
{-# OPTIONS --type-in-type --with-K --allow-unsolved-metas #-}


module Ornament.Numerical where

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
open import Data.Vec
open import Data.Product renaming (proj₁ to fst; proj₂ to snd)
open import Data.Sum hiding (map₂)
open import Data.Nat

open import Function.Base

open import Ornament.Desc
--open import Ornament.Orn
open import Ornament.OrnDesc


private variable
  If If′ If″ If‴ : Info
  I J K M : Type
  A B C X Y Z : Type
  P P′ : Type
  Γ Δ Θ Λ : Tel P
  D E : DescI If Γ I
  U V W   : ExTel Γ
  CD CE : ConI If Γ V I
  V′ W′ : ExTel Δ

open Info
\end{code}

%<*Number>
\begin{code}
Number : Info
Number .𝟙i = ℕ
Number .ρi = ℕ
Number .σi S = ∀ p → S p → ℕ
Number .δi Γ J = (Γ ≡ ∅) × (J ≡ ⊤) × ℕ
\end{code}
%</Number>

%<*toN-type>
\begin{code}
value : {D : DescI Number Γ ⊤} → ∀ {p} → μ D p tt → ℕ
\end{code}
%</toN-type>

\begin{code}
value {D = D} = value-lift D id-InfoF
  where
  value-lift : (D : DescI If Γ ⊤) → InfoF If Number → ∀ {p} → μ D p tt → ℕ
  
  value-lift {If = If} D ϕ = fold (λ _ _ → value-desc D) _ tt
    where
\end{code}

%<*toN-con>
\begin{code}
    value-desc : (D : DescI If Γ ⊤) → ∀ {a b} → ⟦ D ⟧D (λ _ _ → ℕ) a b → ℕ
    value-con : (C : ConI If Γ V ⊤) → ∀ {a b} → ⟦ C ⟧C (λ _ _ → ℕ) a b → ℕ

    value-desc (C ∷ D) (inj₁ x) = value-con C x
    value-desc (C ∷ D) (inj₂ y) = value-desc D y

    value-con  (𝟙 {if = k} j) refl                          
             = ϕ .𝟙f k

    value-con  (ρ {if = k} j g C)                   (n , x)
             = ϕ .ρf k * n + value-con C x

    value-con  (σ S {if = S→ℕ} h C)                 (s , x)
             = ϕ .σf _ S→ℕ _ s + value-con C x

    value-con  (δ {if = if} {iff = iff} j g R h C)  (r , x)
             with ϕ .δf _ _ if
    ...      | refl , refl , k  
             = k * value-lift R (ϕ ∘InfoF iff) r + value-con C x
\end{code}
%</toN-con>

%<*NatND>
\begin{code}
NatND : DescI Number ∅ ⊤
NatND = 𝟙 {if = 0} _
      ∷ ρ0 {if = 1} _ (𝟙 {if = 1} _)
      ∷ []
\end{code}
%</NatND>

\begin{code}
BinND : DescI Number ∅ ⊤
BinND = 𝟙 {if = 0} _
      ∷ ρ0 {if = 2} _ (𝟙 {if = 1} _)
      ∷ ρ0 {if = 2} _ (𝟙 {if = 2} _)
      ∷ []
\end{code}

%<*trieifyOD>
\begin{code}
trieifyOD : (D : DescI Number ∅ ⊤) → OrnDesc Plain (∅ ▷ const Type) ! ⊤ ! D
trieifyOD D = trie-desc D id-InfoF
  module trieifyOD where
  trie-desc  : (D : DescI If ∅ ⊤) → InfoF If Number
             → OrnDesc Plain (∅ ▷ const Type) ! ⊤ ! D
             
  trie-con   : {f : VxfO ! W V} (C : ConI If ∅ V ⊤) → InfoF If Number
             → ConOrnDesc {Δ = ∅ ▷ const Type} {W = W} {J = ⊤} Plain f ! C

  trie-desc []      ϕ = []
  trie-desc (C ∷ D) ϕ = trie-con C ϕ ∷ trie-desc D ϕ

  trie-con (𝟙 {if = k} j) ϕ
    = OΔσ- (λ ((_ , A) , _) → Vec A (ϕ .𝟙f k))
    ( 𝟙 _ (const refl))
  
  trie-con (ρ {if = k} j g C) ϕ
    = ρ _ (λ (_ , A) → (_ , Vec A (ϕ .ρf k))) (const refl) (const refl)
    ( trie-con C ϕ)

  trie-con (σ S {if = if} h C) ϕ
    = Oσ+ S
    ( OΔσ- (λ ((_ , A) , _ , s) → Vec A (ϕ .σf _ if _ s))
    ( trie-con C ϕ))

  trie-con {f = f} (δ {if = if} {iff = iff} j g R h C) ϕ
    with ϕ .δf _ _ if    
  ... | refl , refl , k
    = O∙δ+  ! (λ ((_ , A) , _) → (_ , Vec A k))
            (trie-desc R (ϕ ∘InfoF iff))
            (λ _ _ → refl) (λ _ _ → refl)
    ( trie-con C ϕ)
\end{code}
%</trieifyOD>


%<*PhalanxND>
\begin{code}
ThreeND : DescI Number ∅ ⊤
ThreeND  = 𝟙 {if = 1} _
         ∷ 𝟙 {if = 2} _
         ∷ 𝟙 {if = 3} _
         ∷ []

PhalanxND : DescI Number ∅ ⊤
PhalanxND  = 𝟙 {if = 0} _
           ∷ 𝟙 {if = 1} _
           ∷ δ- {if = refl , refl , 1} {iff = id-InfoF} _ _ ThreeND
           ( ρ0 {if = 2} _
           ( δ- {if = refl , refl , 1} {iff = id-InfoF} _ _ ThreeND
           ( 𝟙 {if = 0} _))) 
           ∷ []
\end{code}
%</PhalanxND>

\begin{code}
module FingerOD where
\end{code}
%<*DigitOD-2>
\begin{code}
  DigitOD′ : OrnDesc Plain (∅ ▷ const Type) ! ⊤ id ThreeND
  DigitOD′  = OΔσ- (λ ((_ , A) , _) → Vec A 1)
            ( 𝟙 _ (const refl))
            ∷ OΔσ- (λ ((_ , A) , _) → Vec A 2)
            ( 𝟙 _ (const refl))
            ∷ OΔσ- (λ ((_ , A) , _) → Vec A 3)
            ( 𝟙 _ (const refl))
            ∷ []
\end{code}
%</DigitOD-2>

%<*FingerOD-2>
\begin{code}
  FingerOD′  : OrnDesc Plain (∅ ▷ const Type) ! ⊤ id PhalanxND
  FingerOD′  = OΔσ- (λ ((_ , A) , _) → Vec A 0)
             ( 𝟙 _ (const refl))
             ∷ OΔσ- (λ ((_ , A) , _) → Vec A 1)
             ( 𝟙 _ (const refl))
             ∷ O∙δ+ ! (λ ((_ , p) , _) → (_ , Vec p 1)) DigitOD′ (λ _ _ → refl) (λ _ _ → refl)
             ( ρ _ (λ (_ , A) → _ , Vec A 2) (const refl) (const refl)
             ( O∙δ+ ! (λ ((_ , p) , _) → (_ , Vec p 1)) DigitOD′ (λ _ _ → refl) (λ _ _ → refl)
             ( OΔσ- (λ ((_ , A) , _) → Vec A 0)
             ( 𝟙 _ (const refl)) )))
             ∷ []
\end{code}
%<*FingerOD-2>

%<*itrieifyOD>
\begin{code}
itrieifyOD : (D : DescI Number ∅ ⊤) → OrnDesc Plain (∅ ▷ const Type) ! (μ D tt tt) ! D
itrieifyOD D = itrie-desc D D (λ _ _ → con) id-InfoF
  where
  itrie-desc  : ∀ {If} (N' : DescI If ∅ ⊤) (D : DescI If ∅ ⊤)
              → (⟦ D ⟧D (μ N') ⇶ μ N')
              → InfoF If Number
              → OrnDesc Plain (∅ ▷ const Type) ! (μ N' tt tt) ! D

  itrie-con   : ∀ {If} (N' : DescI If ∅ ⊤) {f : VxfO ! W V} (C : ConI If ∅ V ⊤)
              → (∀ p w → ⟦ C ⟧C (μ N') (tt , f {p = p} w) _ → μ N' tt tt)
              → InfoF If Number
              → ConOrnDesc {Δ = ∅ ▷ const Type} {W = W} {J = μ N' tt tt} Plain f ! C

  itrie-desc N' []      n ϕ  = []
  itrie-desc N' (C ∷ D) n ϕ  = itrie-con N' C (λ p w x → n _ _ (inj₁ x)) ϕ
                             ∷ itrie-desc N' D (λ p w x → n _ _ (inj₂ x)) ϕ

  itrie-con N' (𝟙 {if = k} j) n ϕ
    = OΔσ- (λ ((_ , A) , _) → Vec A (ϕ .𝟙f k))
    ( 𝟙 (λ { (p , w) → n p w refl }) (const refl))

  itrie-con N' (ρ {if = k} j g C) n ϕ
    = OΔσ+ (λ _ → μ N' tt tt)
    ( ρ  (λ { (p , w , m) → m }) (λ (_ , A) → (_ , Vec A (ϕ .ρf k)))
         (const refl) (const refl)
    ( itrie-con N' C (λ { p (w , m) x → n p w (m , x) }) ϕ))

  itrie-con N' (σ S {if = if} h C) n ϕ
    = Oσ+ S
    ( OΔσ- (λ ((_ , A) , _ , s) → Vec A (ϕ .σf _ if _ s))
    ( itrie-con N' C (λ { p (w , s) x → n p w (s , x) }) ϕ))

  itrie-con N' {f = f} (δ {if = if} {iff = iff} j g R h C) n ϕ
    with ϕ .δf _ _ if    
  ... | refl , refl , k
    = OΔσ+ (λ _ → μ R tt tt)
    ( O∙δ+  (λ { (p , w , r) → r }) (λ ((_ , A) , _) → (_ , Vec A k))
            (itrie-desc R R (λ _ _ → con) (ϕ ∘InfoF iff))
            (λ _ _ → refl) (λ _ _ → refl)
    ( itrie-con  N' C (λ { p ((w , r) , z) x
        → n p w (ornForget (itrie-desc R R (λ _ _ → con) (ϕ ∘InfoF iff)) (tt , Vec (p .snd) k) r z , x) }) ϕ))
\end{code}
%</itrieifyOD>

\begin{code}
module FingerIOD where
  pattern three1  = con (inj₁ refl)
  pattern three2  = con (inj₂ (inj₁ refl))
  pattern three3  = con (inj₂ (inj₂ (inj₁ refl)))

  pattern phalanx1 = con (inj₁ refl)
  pattern phalanx2 = con (inj₂ (inj₁ refl))
  pattern phalanx3 l m r = con (inj₂ (inj₂ (inj₁ (l , m , r , refl))))

  DigitIOD : OrnDesc Plain (∅ ▷ const Type) ! (μ ThreeND tt tt) ! ThreeND
  DigitIOD  =  OΔσ- (λ ((_ , A) , _) → Vec A 1)
            (  𝟙 (const three1) (const refl))
            ∷ OΔσ- (λ ((_ , A) , _) → Vec A 2)
            (  𝟙 (const three2) (const refl))
            ∷ OΔσ- (λ ((_ , A) , _) → Vec A 3)
            (  𝟙 (const three3) (const refl))
            ∷ []

  FingerIOD : OrnDesc Plain (∅ ▷ const Type) ! (μ PhalanxND tt tt) ! PhalanxND
  FingerIOD  = OΔσ- (λ ((_ , A) , _) → Vec A 0)
             (  𝟙 (const phalanx1) (const refl))
             ∷  OΔσ- (λ ((_ , A) , _) → Vec A 1)
             (  𝟙 (const phalanx2) (const refl))
             ∷  OΔσ+ (const (μ ThreeND tt tt))
             (  O∙δ+ (λ { (p , w , r) → r }) (λ ((_ , A) , _) → (_ , Vec A 1))
                DigitIOD (λ _ _ → refl) (λ _ _ → refl)
             (  OΔσ+ (const (μ PhalanxND tt tt))
             (  ρ (λ { (p , w , m) → m }) (λ (_ , A) → _ , Vec A 2) (const refl) (const refl)
               (OΔσ+ (const (μ ThreeND tt tt))
             (  O∙δ+ (λ { (p , w , r) → r }) (λ ((_ , A) , _) → (_ , Vec A 1))
                DigitIOD (λ _ _ → refl) (λ _ _ → refl)
             (  OΔσ- (λ ((_ , A) , _) → Vec A 0)
             (  𝟙 (λ { (p , ((((_ , l) , _) , m) , r) , _) → phalanx3 l m r } ) (const refl))))))))
             ∷ []
\end{code}
