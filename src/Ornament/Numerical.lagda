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
open import Ornament.OrnDesc


private variable
  Me Me′ Me″ Me‴ : Meta
  I J K M : Type
  A B C X Y Z : Type
  P P′ : Type
  Γ Δ Θ Λ : Tel P
  D E : DescI Me Γ I
  U V W   : ExTel Γ
  CD CE : ConI Me Γ V I
  V′ W′ : ExTel Δ

open Meta
\end{code}

%<*1-case>
\begin{code}
𝟙-case : ℕ → ConI Number ∅ V ⊤
𝟙-case k = 𝟙 {me = k} _
\end{code}
%</1-case>

%<*rho-case>
\begin{code}
ρ-case : ℕ → ConI Number ∅ V ⊤ → ConI Number ∅ V ⊤
ρ-case k C = ρ0 {me = k} _ C
\end{code}
%</rho-case>

%<*sigma-case>
\begin{code}
σ-case : (S : V ⊢ Type) → (∀ p → S p → ℕ) → ConI Number ∅ V ⊤ → ConI Number ∅ V ⊤
σ-case S f C = σ- S {me = f} C
\end{code}
%</sigma-case>

%<*delta-case>
\begin{code}
δ-case : ℕ → DescI Number ∅ ⊤ → ConI Number ∅ V ⊤ → ConI Number ∅ V ⊤
δ-case k R C = δ {me = refl , refl , k} {id-MetaF} _ _ R C
\end{code}
%</delta-case>

%<*trieifyOD>
\begin{code}
TreeOD : (D : DescI Number ∅ ⊤) → OrnDesc Plain (∅ ▷ λ _ → Type) ! ⊤ ! D
TreeOD D = Tree-desc D id-MetaF
  module TreeOD where
  Tree-desc  : (D : DescI Me ∅ ⊤) → MetaF Me Number
             → OrnDesc Plain (∅ ▷ λ _ → Type) ! ⊤ ! D
             
  Tree-con   : {re-var : Vxf ! W V} (C : ConI Me ∅ V ⊤) → MetaF Me Number
             → ConOrnDesc {Δ = ∅ ▷ λ _ → Type} {W = W} {J = ⊤} Plain re-var ! C

  Tree-desc []      ϕ = []
  Tree-desc (C ∷ D) ϕ = Tree-con C ϕ ∷ Tree-desc D ϕ

  Tree-con (𝟙 {me = k} j) ϕ
    = OΔσ- (λ ((_ , A) , _) → Vec A (ϕ .𝟙f k))
    ( 𝟙 _ (λ _ → refl))
  
  Tree-con (ρ {me = k} _ _ C) ϕ
    = ρ (λ (_ , A) → (_ , Vec A (ϕ .ρf k))) _ (λ _ → refl) (λ _ → refl)
    ( Tree-con C ϕ)

  Tree-con (σ S {me = f} h C) ϕ
    = Oσ+ S
    ( OΔσ- (λ ((_ , A) , _ , s) → Vec A (ϕ .σf _ f _ s))
    ( Tree-con C ϕ))

  Tree-con (δ {me = me} {iff = iff} g j R C) ϕ
    with ϕ .δf _ _ me    
  ... | refl , refl , k
    = ∙δ  (λ { ((_ , A) , _) → (_ , Vec A k) }) ! (Tree-desc R (ϕ ∘MetaF iff))
          (λ _ _ → refl) (λ _ _ → refl)
    ( Tree-con C ϕ)
\end{code}
%</trieifyOD>


%<*DigitOD-2>
\begin{code}
DigitOD : OrnDesc Plain (∅ ▷ λ _ → Type) ! ⊤ id PhalanxND
DigitOD  = OΔσ- (λ ((_ , A) , _) → Vec A 1)
          ( 𝟙 _ (λ _ → refl))
          ∷ OΔσ- (λ ((_ , A) , _) → Vec A 2)
          ( 𝟙 _ (λ _ → refl))
          ∷ OΔσ- (λ ((_ , A) , _) → Vec A 3)
          ( 𝟙 _ (λ _ → refl))
          ∷ []
\end{code}
%</DigitOD-2>

%<*FingerOD-2>
\begin{code}
FingerOD  : OrnDesc Plain (∅ ▷ λ _ → Type) ! ⊤ id CarpalND
FingerOD  = OΔσ- (λ ((_ , A) , _) → Vec A 0)
           ( 𝟙 _ (λ _ → refl))
           ∷ OΔσ- (λ ((_ , A) , _) → Vec A 1)
           ( 𝟙 _ (λ _ → refl))
           ∷ ∙δ (λ ((_ , p) , _) → (_ , Vec p 1)) ! DigitOD (λ _ _ → refl) (λ _ _ → refl)
           ( ρ (λ (_ , A) → _ , Vec A 2) _ (λ _ → refl) (λ _ → refl)
           ( ∙δ (λ ((_ , p) , _) → (_ , Vec p 1)) ! DigitOD (λ _ _ → refl) (λ _ _ → refl)
           ( OΔσ- (λ ((_ , A) , _) → Vec A 0)
           ( 𝟙 _ (λ _ → refl)) )))
           ∷ []
\end{code}
%</FingerOD-2>

%<*itrieify-type>
\begin{code}
TrieOD : (N : DescI Number ∅ ⊤)
           →  OrnDesc Plain (∅ ▷ λ _ → Type)
              id (μ N tt tt) ! (toDesc (TreeOD N))
TrieOD N = Trie-desc N N (λ _ _ → con) id-MetaF
\end{code}
%</itrieify-type>
\begin{code}
  where mutual
  open TreeOD N
\end{code}
%<*itrieify-desc>
\begin{code}
  Trie-desc  : ∀ {Me} (N' : DescI Me ∅ ⊤) (D : DescI Me ∅ ⊤)
              (n : ⟦ D ⟧D (μ N') ⇶ μ N') (ϕ : MetaF Me Number)
              →  OrnDesc Plain (∅ ▷ λ _ → Type)
                 id (μ N' tt tt) ! (toDesc (Tree-desc D ϕ) )
  Trie-desc N' []      n ϕ  = []
  Trie-desc N' (C ∷ D) n ϕ  = Trie-con N' C (λ p w x → n _ _ (inj₁ x)) ϕ
                             ∷ Trie-desc N' D (λ p w x → n _ _ (inj₂ x)) ϕ
\end{code}
%</itrieify-desc>
%<*itrieify-con>
\begin{code}
  Trie-con   : ∀ {Me} (N' : DescI Me ∅ ⊤) {re-var : Vxf id W V}
              {re-var′ : Vxf ! V U} (C : ConI Me ∅ U ⊤)
              (n : ∀ p w → ⟦ C ⟧C (μ N') (tt , re-var′ (re-var {p = p} w)) _ → μ N' tt tt)
              (ϕ : MetaF Me Number)
              →  ConOrnDesc {Δ = ∅ ▷ λ _ → Type} {W = W} {J = μ N' tt tt} Plain
                 {re-par = id} re-var ! (toCon (Tree-con {re-var = re-var′} C ϕ))
  Trie-con N' (𝟙 {me = k} j) n ϕ
    = Oσ- _
    ( 𝟙 (λ { (p , w) → n p w refl }) (λ _ → refl))

  Trie-con N' (ρ {me = k} g j C) n ϕ
    = OΔσ+ (λ _ → μ N' tt tt)
    ( ρ  (λ { (_ , A) → _ }) (λ { (p , w , i) → i })
         (λ _ → refl) (λ _ → refl)
    ( Trie-con N' C (λ { p (w , i) x → n p w (i , x) }) ϕ))

  Trie-con N' (σ S {me = f} h C) n ϕ
    = Oσ+ (S ∘ var→par _)
    ( Oσ- _
    ( Trie-con N' C (λ { p (w , s) x → n p w (s , x) }) ϕ))

  Trie-con N' (δ {me = me} {iff = iff} g j R C) n ϕ
    with ϕ .δf _ _ me    
  ... | refl , refl , k
    = OΔσ+ (λ _ → μ R tt tt)
    ( ∙δ  (λ ((_ , A) , _) → (_ , Vec A k)) (λ { (p , w , i) → i })
            (Trie-desc R R (λ _ _ → con) (ϕ ∘MetaF iff))
            (λ _ _ → refl) (λ _ _ → refl)
    ( Trie-con N' C (λ { p (w , i) x → n p w (i , x) }) ϕ))
\end{code}
%</itrieify-con>


\begin{code}
module FingerIOD where
  pattern phalanx1  = con (inj₁ refl)
  pattern phalanx2  = con (inj₂ (inj₁ refl))
  pattern phalanx3  = con (inj₂ (inj₂ (inj₁ refl)))

  pattern carpal1 = con (inj₁ refl)
  pattern carpal2 = con (inj₂ (inj₁ refl))
  pattern carpal3 l m r = con (inj₂ (inj₂ (inj₁ (l , m , r , refl))))

  IDigitOD : OrnDesc Plain (∅ ▷ λ _ → Type) id (μ PhalanxND tt tt) ! (toDesc DigitOD)
  IDigitOD  = Oσ- _
            ( 𝟙 (λ _ → phalanx1) (λ _ → refl))
            ∷ Oσ- _
            ( 𝟙 (λ _ → phalanx2) (λ _ → refl))
            ∷ Oσ- _
            ( 𝟙 (λ _ → phalanx3) (λ _ → refl))
            ∷ []


  IFingerOD : OrnDesc Plain (∅ ▷ λ _ → Type) id (μ CarpalND tt tt) ! (toDesc FingerOD)
  IFingerOD  = Oσ- _
             ( 𝟙 (λ _ → carpal1) (λ _ → refl))
             ∷ Oσ- _
             ( 𝟙 (λ _ → carpal2) (λ _ → refl))
             ∷ OΔσ+ (λ _ → (μ PhalanxND tt tt))
             ( ∙δ _ (λ { (p , w , r) → r }) IDigitOD (λ _ _ → refl) (λ _ _ → refl)
             ( OΔσ+ (λ _ → (μ CarpalND tt tt))
             ( ρ (λ (_ , A) → _ , Vec A 2) (λ { (p , w , m) → m }) (λ _ → refl) (λ _ → refl)
             ( OΔσ+ (λ _ → (μ PhalanxND tt tt))
             ( ∙δ _ (λ { (p , w , r) → r }) IDigitOD (λ _ _ → refl) (λ _ _ → refl)
             ( Oσ- _
             ( 𝟙 (λ { (_ , ((_ , l) , m) , r) → carpal3 l m r }) (λ _ → refl))))))))
             ∷ [] 
\end{code}
