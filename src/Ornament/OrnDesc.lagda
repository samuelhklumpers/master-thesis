\begin{code}
{-# OPTIONS --type-in-type --with-K #-}


module Ornament.OrnDesc where

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
open import Data.Sum hiding (map₂)
open import Data.Nat

open import Function.Base

open import Ornament.Desc


private variable
  Me Me′ If″ If‴ : Meta
  I J K M : Type
  A B C X Y Z : Type
  P P′ : Type
  Γ Δ Θ Λ : Tel P
  D E : DescI Me Γ I
  U V W   : ExTel Γ
  CD CE : ConI Me Γ V I
  V′ W′ : ExTel Δ
\end{code}

%<*toOrn>
toOrn :  {f : Cxf Δ Γ} {re-index : J → I} {D : DescI Me Γ I}
         (OD : OrnDesc Me′ Δ f J re-index D) → Orn f re-index D (toDesc OD)

toConOrn :  {c : Cxf Δ Γ} {re-var : Vxf c W V} {re-index : J → I} {D : ConI Me Γ I V}
            (OD : ConOrnDesc Me′ re-var re-index D) → ConOrn re-var re-index D (toCon OD)
%</toOrn>

-- note, we abstract OrnDesc over {Me}, rather than taking {Me} as a module argument, so that ∙δ can take a OrnDesc with different Meta

\begin{code}
_∼_ : {B : A → Type} → (f g : ∀ a → B a) → Type
f ∼ g = ∀ a → f a ≡ g a

infix 0 _∼_

mutual
\end{code}

%<*OrnDesc>
\AgdaTarget{OrnDesc}
\begin{code}
  data OrnDesc     {Me} (Me′ : Meta) (Δ : Tel ⊤)
                   (re-par : Cxf Δ Γ) (J : Type) (re-index : J → I)
                   : DescI Me Γ I → Type where
    []   : OrnDesc Me′ Δ re-par J re-index []
    _∷_  : ConOrnDesc Me′ {re-par = re-par} ! re-index {Me = Me} CD
         → OrnDesc Me′ Δ re-par J re-index D
         → OrnDesc Me′ Δ re-par J re-index (CD ∷ D)
\end{code}
%</OrnDesc>

%<*ConOrn-preserve>
\AgdaTarget{ConOrnDesc}
\begin{code}
  data ConOrnDesc  (Me′ : Meta) {re-par : Cxf Δ Γ}
                   (re-var : Vxf re-par W V) (re-index : J → I)
                   : ConI Me Γ V I → Type  where
    𝟙  : {i : Γ & V ⊢ I} (j : Δ & W ⊢ J)
       → re-index ∘ j ∼ i ∘ var→par re-var
       → {me : Me .𝟙i} {me′ : Me′ .𝟙i}
       → ConOrnDesc Me′ re-var re-index (𝟙 {Me} {me = me} i)

    ρ : {g : Cxf Γ Γ} (d : Cxf Δ Δ)
        {i : Γ & V ⊢ I} (j : Δ & W ⊢ J)
      → g ∘ re-par ∼ re-par ∘ d
      → re-index ∘ j ∼ i ∘ var→par re-var
      → {me : Me .ρi} {me′ : Me′ .ρi}
      → ConOrnDesc Me′ re-var re-index CD
      → ConOrnDesc Me′ re-var re-index (ρ {Me} {me = me} g i CD)

    σ : (S : Γ & V ⊢ Type)
        {g : Vxf id (V ▷ S) V′} (h : Vxf id (W ▷ (S ∘ var→par re-var)) W′)
        (v′ : Vxf re-par W′ V′)
      → (∀ {p} → g ∘ Vxf-▷ re-var S ∼ v′ {p = p} ∘ h)
      → {me : Me .σi S} {me′ : Me′ .σi (S ∘ var→par re-var)}
      → ConOrnDesc Me′ v′ re-index CD
      → ConOrnDesc Me′ re-var re-index (σ {Me} S {me = me} g CD)

    δ : (R : DescI If″ Θ K) (t : Γ & V ⊢ ⟦ Θ ⟧tel tt) (j : Γ & V ⊢ K)
      → {me : Me .δi Θ K} {iff : MetaF If″ Me}
        {me′ : Me′ .δi Θ K} {iff′ : MetaF If″ Me′}
      → ConOrnDesc Me′ re-var re-index CD
      → ConOrnDesc  Me′ re-var re-index
                    (δ {Me} {me = me} {iff = iff} t j R CD)
\end{code}
%</ConOrn-preserve>

%<*ConOrn-extend>
\AgdaTarget{Δσ, Δδ}
\begin{code}
    Δσ : (S : Δ & W ⊢ Type) (h : Vxf id (W ▷ S) W′)
         (v′ : Vxf re-par W′ V)
       → (∀ {p} → re-var ∘ fst ∼ v′ {p = p} ∘ h)
       → {me′ : Me′ .σi S}
       → ConOrnDesc Me′ v′ re-index CD
       → ConOrnDesc Me′ re-var re-index CD 

    Δδ : (R : DescI If″ Θ J) (t : W ⊢ ⟦ Θ ⟧tel tt) (j : W ⊢ J)
       → {me′ : Me′ .δi Θ J} {iff′ : MetaF If″ Me′}
       → ConOrnDesc Me′ re-var re-index CD
       → ConOrnDesc Me′ re-var re-index CD 
\end{code}
%</ConOrn-extend>

%<*ConOrn-compose>
\AgdaTarget{∙δ}
\begin{code}
    ∙δ : {R : DescI If″ Θ K} {c′ : Cxf Λ Θ} {fΘ : V ⊢ ⟦ Θ ⟧tel tt}
         (fΛ : W ⊢ ⟦ Λ ⟧tel tt) {k′ : M → K} {k : V ⊢ K}
         (m : W ⊢ M) 
       → (RR′ : OrnDesc If‴ Λ c′ M k′ R)
       → (p₁ : ∀ q w → c′ (fΛ (q , w)) ≡ fΘ (re-par q , re-var w))
       → (p₂ : ∀ q w → k′ (m (q , w))  ≡ k (re-par q , re-var w))
       → ∀ {me} {iff} {me′ : Me′ .δi Λ M} {iff′ : MetaF If‴ Me′}
       → (DE : ConOrnDesc Me′ re-var re-index CD)
       → ConOrnDesc  Me′ re-var re-index
                     (δ {Me} {me = me} {iff = iff} fΘ k R CD)
\end{code}
%</ConOrn-compose>


%<*toDesc>
\AgdaTarget{toDesc, toCon}
\begin{code}
  toDesc  : {re-var : Cxf Δ Γ} {re-index : J → I} {D : DescI Me Γ I}
          → OrnDesc Me′ Δ re-var J re-index D → DescI Me′ Δ J
  toDesc []       = []
  toDesc (CO ∷ O) = toCon CO ∷ toDesc O

  toCon   :  {re-par : Cxf Δ Γ} {re-var : Vxf re-par W V}
             {re-index : J → I} {D : ConI Me Γ V I}
          → ConOrnDesc Me′ re-var re-index D → ConI Me′ Δ W J
  toCon (𝟙 j _ {me′ = me})
    = 𝟙 {me = me} j

  toCon (ρ j h _ _ {me′ = me} CO)
    = ρ {me = me} j h (toCon CO)

  toCon {re-var = v} (σ S h _ _ {me′ = me} CO)
    = σ (S ∘ var→par v) {me = me} h (toCon CO)

  toCon {re-var = v} (δ R j t {me′ = me} {iff′ = iff} CO)
    = δ {me = me} {iff = iff} (j ∘ var→par v) (t ∘ var→par v) R (toCon CO)

  toCon (Δσ S h _ _ {me′ = me} CO)
    = σ S {me = me} h (toCon CO)
  
  toCon (Δδ R t j {me′ = me} {iff′ = iff} CO)
    = δ {me = me} {iff = iff} t j R (toCon CO)
  
  toCon (∙δ fΛ m RR′ _ _ {me′ = me} {iff′ = iff} CO)
    = δ {me = me} {iff = iff} fΛ m (toDesc RR′) (toCon CO)
\end{code}
%</toDesc>

\begin{code}
  ornErase : ∀ {Δ} {Γ} {J} {I} {Me} {Me′} {re-var : Cxf Δ Γ} {re-index : J → I}
             {D : DescI Me Γ I} {X} (OD : OrnDesc Me′ Δ re-var J re-index D) (p : ⟦ Δ ⟧tel tt)
             (j : J) (x : ⟦ toDesc OD ⟧D (λ p j → X (re-var p) (re-index j)) p j) →
           ⟦ D ⟧D X (re-var p) (re-index j)
  ornErase (OC ∷ OD) p j (inj₁ x) = inj₁ (conOrnErase OC (p , tt) j x)
  ornErase (OC ∷ OD) p j (inj₂ y) = inj₂ (ornErase OD p j y)

  conOrnErase : ∀ {Δ} {Γ V W} {J} {I} {Me} {Me′} {re-var : Cxf Δ Γ} {re-par : Vxf re-var W V} {re-index : J → I}
              {X} {CD : ConI Me Γ V I}
              (OC : ConOrnDesc Me′ re-par re-index CD) (p : ⟦ Δ & W ⟧tel) (j : J)
              (x : ⟦ toCon OC ⟧C (λ p₁ j₁ → X (re-var p₁) (re-index j₁)) p j) →
            ⟦ CD ⟧C X (var→par re-par p) (re-index j)
  conOrnErase {re-index = i} (𝟙 j′ x₁) p j x = trans (cong i x) (x₁ p)
  conOrnErase {X = X} (ρ d j′ x₁ x₂ OC) (p , w) j (x , y) = subst₂ X (sym (x₁ p)) (x₂ (p , w)) x , conOrnErase OC (p , w) j y
  conOrnErase {re-var = v} {X = X} (σ {CD = CD} S h v′ x₁ OC) (p , w) j (s , x) = s , subst₂ (⟦ CD ⟧C X) (cong (v p ,_) (sym (x₁ (w , s)))) refl (conOrnErase OC (p , h (w , s)) j x) 
  conOrnErase {X = X} (δ {CD = CD} R t j′ OC) (p , w) j (r , x) = r , conOrnErase OC (p , w) j x
  conOrnErase {X = X} (Δσ {CD = CD} S h v′ x₁ OC) (p , w) j (s , x) = subst (λ a → ⟦ CD ⟧C X a _) (cong (_ ,_) (sym (x₁ (w , s)))) (conOrnErase OC (p , h (w , s)) j x)
  conOrnErase {X = X} (Δδ {CD = CD} R t j′ OC) (p , w) j (r , x) = conOrnErase OC (p , w) j x
  conOrnErase {re-var = v} {X = X} (∙δ {CD = CD} {R = R} fΛ m RR′ p₁ p₂ OC) (p , w) j (r , x) = subst₂ (μ R) (p₁ _ _) (p₂ _ _) (ornForget RR′ _ _ r) , conOrnErase OC (p , w) j x

  ornAlg : ∀ {Δ} {Γ : Tel ⊤} {J} {I} {Me} {Me′} {re-var : Cxf Δ Γ}
           {re-index : J → I} {D : DescI Me Γ I} (OD : OrnDesc Me′ Δ re-var J re-index D) →
         ⟦ toDesc OD ⟧D (λ p j → μ D (re-var p) (re-index j)) →₃
         (λ p j → μ D (re-var p) (re-index j))
  ornAlg OD p i x = con (ornErase OD p i x)
\end{code}

%<*ornForget>
\AgdaTarget{ornForget}
\begin{code}
  ornForget : {re-var : Cxf Δ Γ} {re-index : J → I} {D : DescI Me Γ I}
            → (OD : OrnDesc Me′ Δ re-var J re-index D)
            → μ (toDesc OD) →₃ λ d j → μ D (re-var d) (re-index j)
  ornForget OD = fold (ornAlg OD)
\end{code}
%</ornForget>

\begin{code}
module _ {Me′ : Meta} {re-par : Cxf Δ Γ} {re-var : Vxf re-par W V} {re-index : J → I} {Me : Meta} where  
  Oρ0 : {i : Γ & V ⊢ I} (j : Δ & W ⊢ J)
    → re-index ∘ j ∼ i ∘ var→par re-var
    → {me : Me .ρi} {me′ : Me′ .ρi}
    → ConOrnDesc Me′ re-var re-index CD
    → ConOrnDesc Me′ re-var re-index (ρ {Me} {me = me} id i CD)
  Oρ0 j q {me′ = me′} CO = ρ id j (λ a → refl) q {me′ = me′} CO
\end{code}

%<*O-sigma-pm>
\AgdaTarget{Oσ+}
\begin{code}
  Oσ+ : (S : Γ & V ⊢ Type) {CD : ConI Me Γ V′ I} {h : Vxf _ _ _}
    → {me : Me .σi S} {me′ : Me′ .σi (S ∘ var→par re-var)}
    → ConOrnDesc Me′ (h ∘ Vxf-▷ re-var S) re-index CD
    → ConOrnDesc Me′ re-var re-index (σ {Me} S {me = me} h CD)
  Oσ+ S {h = h} {me′ = me′} CO
    = σ S id (h ∘ Vxf-▷ re-var S) (λ _ → refl) {me′ = me′} CO
\end{code}
%</O-sigma-pm>

\begin{code}
  Oσ- : (S : Γ & V ⊢ Type) {CD : ConI Me Γ V I}
    → {me : Me .σi S} {me′ : Me′ .σi (S ∘ var→par re-var)}
    → ConOrnDesc Me′ re-var re-index CD
    → ConOrnDesc Me′ re-var re-index (σ {Me} S {me = me} fst CD)
  Oσ- S {me′ = me′} CO = σ S fst re-var (λ _ → refl) {me′ = me′} CO
  
  OΔσ+ : {CD : ConI Me _ _ _} (S : Δ & W ⊢ Type)
     → {me′ : Me′ .σi S}
     → ConOrnDesc Me′ (re-var ∘ fst) re-index CD
     → ConOrnDesc Me′ re-var re-index CD
  OΔσ+ S {me′ = me′} CO = Δσ S id (re-var ∘ fst) (λ _ → refl) {me′ = me′} CO
     
  OΔσ- : {CD : ConI Me _ _ _} (S : Δ & W ⊢ Type)
     → {me′ : Me′ .σi S}
     → ConOrnDesc Me′ re-var re-index CD
     → ConOrnDesc Me′ re-var re-index CD 
  OΔσ- S {me′ = me′} CO = Δσ S fst re-var (λ _ → refl) {me′ = me′} CO
\end{code}

%<*VecOD>
\begin{code}
VecOD : OrnDesc Plain (∅ ▷ λ _ → Type) id ℕ ! ListD
VecOD = nilOD ∷ consOD ∷ []
  where
  nilOD   = 𝟙 (λ _ → zero) (λ _ → refl)
  consOD  = OΔσ+ (λ _ → ℕ)
          ( Oσ- (λ ((_ , A) , _) → A)
          ( Oρ0 (λ (_ , (_ , n)) → n) (λ _ → refl)
          ( 𝟙 (λ (_ , (_ , n)) → suc n) (λ _ → refl))))
\end{code}
%</VecOD>

%<*RandomOD>
\begin{code}
RandomOD : OrnDesc Plain (∅ ▷ λ _ → Type) ! ⊤ id BinND
RandomOD = ZeroOD ∷ OneOD ∷ TwoOD ∷ []
  where
  ZeroOD   = 𝟙 _ (λ _ → refl)
  OneOD    =  OΔσ- (λ ((_ , A) , _) → A)
           (  ρ (λ (_ , A) → (_ , Pair A)) _ (λ _ → refl) (λ _ → refl)
           (  𝟙 _ (λ _ → refl)))
  TwoOD    =  OΔσ- (λ ((_ , A) , _) → A)
           (  OΔσ- (λ ((_ , A) , _) → A)
           (  ρ (λ (_ , A) → (_ , Pair A)) _ (λ _ → refl) (λ _ → refl) 
           (  𝟙 _ (λ _ → refl))))
\end{code}
%</RandomOD>

\begin{code}
module Ignore where
\end{code}
%<*DigitOD>
\begin{code}
  DigitOD : OrnDesc Plain (∅ ▷ λ _ → Type) ! ⊤ id PhalanxND
  DigitOD = OneOD ∷ TwoOD ∷ ThreeOD ∷ []
    where
    OneOD      = OΔσ- (λ ((_ , A) , _) → A)
               ( 𝟙 _ (λ _ → refl))
    TwoOD      = OΔσ- (λ ((_ , A) , _) → A)
               ( OΔσ- (λ ((_ , A) , _) → A)
               ( 𝟙 _ (λ _ → refl)))
    ThreeOD    = OΔσ- (λ ((_ , A) , _) → A)
               ( OΔσ- (λ ((_ , A) , _) → A)
               ( OΔσ- (λ ((_ , A) , _) → A)
               ( 𝟙 _ (λ _ → refl))))
\end{code}
%</DigitOD>

%<*FingerOD>
\begin{code}
  FingerOD : OrnDesc Plain (∅ ▷ λ _ → Type) ! ⊤ id CarpalND
  FingerOD = EmptyOD ∷ SingleOD ∷ DeepOD ∷ []
    where
    EmptyOD    = 𝟙 _ (λ _ → refl)
    SingleOD   = OΔσ- (λ ((_ , A) , _) → A)
               ( 𝟙 _ (λ _ → refl))
    DeepOD     = ∙δ (λ (p , _) → p) _ DigitOD (λ _ _ → refl) (λ _ _ → refl)
               ( ρ (λ (_ , A) → (_ , (A × A))) _ (λ _ → refl) (λ _ → refl)
               ( ∙δ (λ (p , _) → p) _ DigitOD (λ _ _ → refl) (λ _ _ → refl)
               ( 𝟙 _ (λ _ → refl))))
\end{code}
%</FingerOD>

