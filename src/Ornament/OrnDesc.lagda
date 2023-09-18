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
open import Data.Sum
open import Data.Nat

open import Function.Base

open import Ornament.Desc
-- open import Ornament.Orn



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
\end{code}

%<*toOrn>
toOrn :  {f : Cxf Δ Γ} {i : J → I} {D : DescI If Γ I}
         (OD : OrnDesc If′ Δ f J i D) → Orn f i D (toDesc OD)

toConOrn :  {c : Cxf Δ Γ} {v : VxfO c W V} {i : J → I} {D : ConI If Γ I V}
            (OD : ConOrnDesc If′ v i D) → ConOrn v i D (toCon OD)
%</toOrn>

-- note, we abstract OrnDesc over {If}, rather than taking {If} as a module argument, so that ∙δ can take a OrnDesc with different Info

\begin{code}
_∼_ : {B : A → Type} → (f g : ∀ a → B a) → Type
f ∼ g = ∀ a → f a ≡ g a

infix 0 _∼_

mutual
\end{code}
%<*OrnDesc>
\begin{code}
  data OrnDesc     {If} (If′ : Info) (Δ : Tel ⊤)
                   (c : Cxf Δ Γ) (J : Type) (i : J → I)
                   : DescI If Γ I → Type where
    []   : OrnDesc If′ Δ c J i []
    _∷_  : ConOrnDesc If′ {c = c} id i {If = If} CD
         → OrnDesc If′ Δ c J i D
         → OrnDesc If′ Δ c J i (CD ∷ D)

  data ConOrnDesc  (If′ : Info) {c : Cxf Δ Γ}
                   (v : VxfO c W V) (i : J → I)
                   : ConI If Γ V I → Type  where
    𝟙  : {i′ : Γ & V ⊢ I} (j′ : Δ & W ⊢ J)
       → i ∘ j′ ∼ i′ ∘ over v
       → {if : If .𝟙i} {if′ : If′ .𝟙i}
       → ConOrnDesc If′ v i (𝟙 {If} {if = if} i′)

    ρ : {i′ : Γ & V ⊢ I} (j′ : Δ & W ⊢ J)
        {g : Cxf Γ Γ} (h : Cxf Δ Δ)
      → g ∘ c ∼ c ∘ h
      → i ∘ j′ ∼ i′ ∘ over v
      → {if : If .ρi} {if′ : If′ .ρi}
      → ConOrnDesc If′ v i CD
      → ConOrnDesc If′ v i (ρ {If} {if = if} i′ g CD)

    σ : (S : Γ & V ⊢ Type)
        {g : Vxf Γ (V ▷ S) V′} (h : Vxf Δ (W ▷ (S ∘ over v)) W′)
        (v′ : VxfO c W′ V′)
      → (∀ {p} → g ∘ VxfO-▷ v S ∼ v′ {p = p} ∘ h)
      → {if : If .σi S} {if′ : If′ .σi (S ∘ over v)}
      → ConOrnDesc If′ v′ i CD
      → ConOrnDesc If′ v i (σ {If} S {if = if} g CD)

    δ : (R : DescI If″ Θ J) (j : Γ & V ⊢ J) (t : Γ & V ⊢ ⟦ Θ ⟧tel tt)
        {g : Vxf Γ _ V′} (h : Vxf Δ _ W′)
        {v′ : VxfO c W′ V′}
      → (∀ {p} → g ∘ VxfO-▷ v (liftM2 (μ R) t j) ∼ v′ {p = p} ∘ h)
      → {if : If .δi Θ J} {iff : InfoF If″ If}
        {if′ : If′ .δi Θ J} {iff′ : InfoF If″ If′}
      → ConOrnDesc If′ v′ i CD
      → ConOrnDesc If′ v i (δ {If} {if = if} {iff = iff} j t R g CD)

    Δσ : (S : Δ & W ⊢ Type) (h : Vxf Δ (W ▷ S) W′)
         (v′ : VxfO c W′ V)
       → (∀ {p} → v ∘ fst ∼ v′ {p = p} ∘ h)
       → {if′ : If′ .σi S}
       → ConOrnDesc If′ v′ i CD
       → ConOrnDesc If′ v i CD 

    Δδ : (R : DescI If″ Θ J) (j : W ⊢ J) (t : W ⊢ ⟦ Θ ⟧tel tt)
         (h : Vxf Δ (W ▷ liftM2 (μ R) t j) W′)
         {v′ : VxfO c W′ V}
       → (∀ {p} → v ∘ fst ∼ v′ {p = p} ∘ h)
       → {if′ : If′ .δi Θ J} {iff′ : InfoF If″ If′}
       → ConOrnDesc If′ v′ i CD
       → ConOrnDesc If′ v i CD 

    ∙δ : {R : DescI If″ Θ K} {c′ : Cxf Λ Θ} {k′ : M → K} {k : V ⊢ K}
         {fΘ : V ⊢ ⟦ Θ ⟧tel tt} {g : Vxf _ (V ▷ liftM2 (μ R) fΘ k) V′}  
         (m : W ⊢ M) (fΛ : W ⊢ ⟦ Λ ⟧tel tt)
       → (RR′ : OrnDesc If‴ Λ c′ M k′ R)
         (h : Vxf _ (W ▷ liftM2 (μ (toDesc RR′)) fΛ m) W′)
         {v′ : VxfO c W′ V′}   
       → (p₁ : ∀ q w → c′ (fΛ (q , w)) ≡ fΘ (c q , v w))
       → (p₂ : ∀ q w → k′ (m (q , w))  ≡ k (c q , v w))
       → ∀ {if} {iff} {if′ : If′ .δi Λ M} {iff′ : InfoF If‴ If′}
       → (DE : ConOrnDesc If′ v′ i CD)
       → ConOrnDesc If′ v i (δ {If} {if = if} {iff = iff} k fΘ R g CD)
\end{code}
%</OrnDesc>

omitted:
∙δ
 -- → (∀ {p′} (p : ⟦ W ▷ liftM2 (μ (toDesc RR′)) fΛ m ⟧tel p′) → v′ (h p) ≡ g (VxfO-▷-map v (liftM2 (μ R) fΘ l) (liftM2 (μ (toDesc RR′)) fΛ m) (λ q w x → transport2 (μ R) (p₁ _ _) (p₂ _ _) (ornForget (toOrn RR′) (fΛ (q , w)) x)) p))



    Δρ : (j : Δ & W ⊢ J) (h : Cxf Δ Δ)
       → {if′ : If′ .ρi}
       → ConOrnDesc If′ v i CD
       → ConOrnDesc If′ v i CD


δ:
-- (h : Vxf Δ {!W ▷ liftM2 (μ R) (k ∘ over v) (j ∘ over v)!} W′)
-- → (∀ {p′} (p : ⟦ W ▷ liftM2 (μ R) (k ∘ over v) (j ∘ over v) ⟧tel p′) → g (VxfO-▷ v (liftM2 (μ R) k j) p) ≡ v′ (h p))

Δσ:
-- (∀ {p′} (p : ⟦ W ▷ S ⟧tel p′) → v (p .fst) ≡ v′ (h p))

Δδ:
-- (∀ {p′} (p : ⟦ W ▷ liftM2 (μ R) t j ⟧tel p′) → v (p .fst) ≡ v′ (h p))


{-
  -- fixing
  ∇σ : ∀ {S} {V′} {D : ConI If Γ I V′} {g : Vxf Γ _ _}
     → (s : V ⊧ S)
     → ConOrnDesc If′ ((g ∘ ⊧-▷ s) ∘ v) i D
     → ∀ {if}
     → ConOrnDesc If′ v i (σ S {if = if} g D)

  ∇δ : ∀ {R : DescI If″ Θ K} {V′} {D : ConI If Γ I V′} {m} {k} {g : Vxf Γ _ _}
     → (s : V ⊧ liftM2 (μ R) m k)
     → ConOrnDesc If′ ((g ∘ ⊧-▷ s) ∘ v) i D
     → ∀ {if iff}
     → ConOrnDesc If′ v i (δ {if = if} {iff = iff} k m R g D)
-}


%<*toDesc>
\begin{code}
  toDesc  : {v : Cxf Δ Γ} {i : J → I} {D : DescI If Γ I}
          → OrnDesc If′ Δ v J i D → DescI If′ Δ J
  toDesc []       = []
  toDesc (CO ∷ O) = toCon CO ∷ toDesc O

  toCon   : {c : Cxf Δ Γ} {v : VxfO c W V} {i : J → I} {D : ConI If Γ V I}
          → ConOrnDesc If′ v i D → ConI If′ Δ W J
  toCon (𝟙 j′ x {if′ = if}) = 𝟙 {if = if} j′
  toCon (ρ j′ h x x₁ {if′ = if} CO) = ρ {if = if} j′ h (toCon CO)
  toCon {v = v} (σ S h v′ x {if′ = if} CO) = σ (S ∘ over v) {if = if} h (toCon CO)
  toCon {v = v} (δ R j t h x {if′ = if} {iff′ = iff} CO) = δ {if = if} {iff = iff} (j ∘ over v) (t ∘ over v) R h (toCon CO)
  toCon (Δσ S h v′ x {if′ = if} CO) = σ S {if = if} h (toCon CO)
  toCon (Δδ R j t h x {if′ = if} {iff′ = iff} CO) = δ {if = if} {iff = iff} j t R h (toCon CO)
  toCon (∙δ m fΛ RR′ h p₁ p₂ {if′ = if} {iff′ = iff} CO) = δ {if = if} {iff = iff} m fΛ (toDesc RR′) h (toCon CO)
\end{code}
%</toDesc>


-- this is pretty awful, maybe not very in line with the whole "let's make stuff compact" idea
-- makes you think
\begin{code}
module _ {If′ : Info} {c : Cxf Δ Γ} {v : VxfO c W V} {i : J → I} {If : Info} where  
  Oρ0 : {i′ : Γ & V ⊢ I} (j′ : Δ & W ⊢ J)
    → i ∘ j′ ∼ i′ ∘ over v
    → {if : If .ρi} {if′ : If′ .ρi}
    → ConOrnDesc If′ v i CD
    → ConOrnDesc If′ v i (ρ {If} {if = if} i′ id CD)
  Oρ0 j′ q {if′ = if′} CO = ρ j′ id (λ a → refl) q {if′ = if′} CO
\end{code}

%<*O-sigma-pm>
\begin{code}
  Oσ+ : (S : Γ & V ⊢ Type) {CD : ConI If Γ (V ▷ S) I}
    → {if : If .σi S} {if′ : If′ .σi (S ∘ over v)}
    → ConOrnDesc If′ (VxfO-▷ v S) i CD
    → ConOrnDesc If′ v i (σ {If} S {if = if} id CD)
  Oσ+ S {if′ = if′} CO = σ S id (VxfO-▷ v S) (λ _ → refl) {if′ = if′} CO

  Oσ- : (S : Γ & V ⊢ Type) {CD : ConI If Γ V I}
    → {if : If .σi S} {if′ : If′ .σi (S ∘ over v)}
    → ConOrnDesc If′ v i CD
    → ConOrnDesc If′ v i (σ {If} S {if = if} fst CD)
  Oσ- S {if′ = if′} CO = σ S fst v (λ _ → refl) {if′ = if′} CO
\end{code}
%</O-sigma-pm>

\begin{code}
  Oδ+ : (R : DescI If″ Θ J) (j : Γ & V ⊢ J) (t : Γ & V ⊢ ⟦ Θ ⟧tel tt)
        {CD : ConI If Γ (V ▷ liftM2 (μ R) t j) I}
    → {if : If .δi Θ J} {iff : InfoF If″ If}
      {if′ : If′ .δi Θ J} {iff′ : InfoF If″ If′}
    → ConOrnDesc If′ (VxfO-▷ v (liftM2 (μ R) t j)) i CD
    → ConOrnDesc If′ v i (δ {If} {if = if} {iff = iff} j t R id CD)
  Oδ+ R j t {if′ = if′} {iff′ = iff′} CO = δ R j t id (λ _ → refl) {if′ = if′} {iff′ = iff′} CO

  Oδ- : (R : DescI If″ Θ J) (j : Γ & V ⊢ J) (t : Γ & V ⊢ ⟦ Θ ⟧tel tt)
        {CD : ConI If Γ V I}
    → {if : If .δi Θ J} {iff : InfoF If″ If}
      {if′ : If′ .δi Θ J} {iff′ : InfoF If″ If′}
    → ConOrnDesc If′ v i CD
    → ConOrnDesc If′ v i (δ {If} {if = if} {iff = iff} j t R fst CD)
  Oδ- R j t {if′ = if′} {iff′ = iff′} CO = δ R j t fst (λ _ → refl) {if′ = if′} {iff′ = iff′} CO

  OΔσ+ : {CD : ConI If _ _ _} (S : Δ & W ⊢ Type)
     → {if′ : If′ .σi S}
     → ConOrnDesc If′ (v ∘ fst) i CD
     → ConOrnDesc If′ v i CD
  OΔσ+ S {if′ = if′} CO = Δσ S id (v ∘ fst) (λ _ → refl) {if′ = if′} CO
     
  OΔσ- : {CD : ConI If _ _ _} (S : Δ & W ⊢ Type)
     → {if′ : If′ .σi S}
     → ConOrnDesc If′ v i CD
     → ConOrnDesc If′ v i CD 
  OΔσ- S {if′ = if′} CO = Δσ S fst v (λ _ → refl) {if′ = if′} CO

  OΔδ+ : (R : DescI If″ Θ J) (j : W ⊢ J) (t : W ⊢ ⟦ Θ ⟧tel tt)
     → {if′ : If′ .δi Θ J} {iff′ : InfoF If″ If′}
     → ConOrnDesc If′ (v ∘ fst) i CD
     → ConOrnDesc If′ v i CD
  OΔδ+ R j t {if′ = if′} {iff′ = iff′} CO = Δδ R j t id (λ _ → refl) {if′ = if′} {iff′ = iff′} CO

  OΔδ- : (R : DescI If″ Θ J) (j : W ⊢ J) (t : W ⊢ ⟦ Θ ⟧tel tt)
     → {if′ : If′ .δi Θ J} {iff′ : InfoF If″ If′}
     → ConOrnDesc If′ v i CD
     → ConOrnDesc If′ v i CD
  OΔδ- R j t {if′ = if′} {iff′ = iff′} CO = Δδ R j t fst (λ _ → refl) {if′ = if′} {iff′ = iff′} CO

  {-
  -- these need ornForget to run x)
  O∙δ+ : {R : DescI If″ Θ K} {c′ : Cxf Λ Θ} {k′ : M → K} {k : V ⊢ K}
       {fΘ : V ⊢ ⟦ Θ ⟧tel tt} (m : W ⊢ M) (fΛ : W ⊢ ⟦ Λ ⟧tel tt)
       {CD : ConI If Γ (V ▷ liftM2 (μ R) fΘ k) I}
     → (RR′ : OrnDesc If‴ Λ c′ M k′ R)
     → (p₁ : ∀ q w → c′ (fΛ (q , w)) ≡ fΘ (c q , v w))
     → (p₂ : ∀ q w → k′ (m (q , w))  ≡ k (c q , v w))
     → ∀ {if} {iff} {if′ : If′ .δi Λ M} {iff′ : InfoF If‴ If′}
     → (DE : ConOrnDesc If′ (VxfO-▷ v (liftM2 (μ R) fΘ k)) i CD)
     → ConOrnDesc If′ v i (δ {If} {if = if} {iff = iff} k fΘ R id CD)
  O∙δ+ m fΛ RR′ p₁ p₂ {if′ = if′} {iff′ = iff′} CO = ∙δ m fΛ RR′ id {v′ = {!VxfO-▷ ? (liftM2 (μ (toDesc RR′)) fΛ m)!}} p₁ p₂ {if′ = if′} {iff′ = iff′} {!CO!}

  O∙δ- : {R : DescI If″ Θ K} {c′ : Cxf Λ Θ} {k′ : M → K} {k : V ⊢ K}
       {fΘ : V ⊢ ⟦ Θ ⟧tel tt} {g : Vxf _ (V ▷ liftM2 (μ R) fΘ k) V′}  
       (m : W ⊢ M) (fΛ : W ⊢ ⟦ Λ ⟧tel tt)
     → (RR′ : OrnDesc If‴ Λ c′ M k′ R)
       (h : Vxf _ (W ▷ liftM2 (μ (toDesc RR′)) fΛ m) W′)
       {v′ : VxfO c W′ V′}   
     → (p₁ : ∀ q w → c′ (fΛ (q , w)) ≡ fΘ (c q , v w))
     → (p₂ : ∀ q w → k′ (m (q , w))  ≡ k (c q , v w))
     → ∀ {if} {iff} {if′ : If′ .δi Λ M} {iff′ : InfoF If‴ If′}
     → (DE : ConOrnDesc If′ v′ i CD)
     → ConOrnDesc If′ v i (δ {If} {if = if} {iff = iff} k fΘ R g CD)
  O∙δ- = {!!}
  -}
\end{code}

%<*VecOD>
\begin{code}
VecOD : OrnDesc Plain (∅ ▷ const Type) id ℕ ! ListD
VecOD = (𝟙 (const zero) (const refl))
      ∷ (OΔσ+ (const ℕ)
      (  Oσ- (λ ((_ , A) , _) → A)
      (  Oρ0 (λ (_ , (_ , n)) → n) (const refl)
      (  𝟙 (λ (_ , (_ , n)) → suc n) (const refl)))))
      ∷ []
\end{code}
%</VecOD>

%<*LeibnizD>
\begin{code}
LeibnizD : Desc ∅ ⊤
LeibnizD = 𝟙 _
         ∷ ρ0 _ (𝟙 _)
         ∷ ρ0 _ (𝟙 _)
         ∷ []
\end{code}
%</LeibnizD>

%<*RandomOD>
\begin{code}
RandomOD : OrnDesc Plain (∅ ▷ const Type) ! ⊤ id LeibnizD
RandomOD  = 𝟙 _ (const refl)
          ∷  OΔσ- (λ ((_ , A) , _) → A)
          (  ρ _ (λ (_ , A) → (_ , Pair A)) (const refl) (const refl)
          (  𝟙 _ (const refl)))
          ∷  OΔσ- (λ ((_ , A) , _) → A)
          (  OΔσ- (λ ((_ , A) , _) → A)
          (  ρ _ (λ (_ , A) → (_ , Pair A)) (const refl) (const refl)
          (  𝟙 _ (const refl))))
          ∷ []
\end{code}
%</RandomOD>


  toCon (Δρ j h {if′ = if} CO) = ρ {if = if} j h (toCon CO)

old:
toDesc  : {v : Cxf Δ Γ} {i : J → I} {D : DescI If Γ I}
        → OrnDesc If′ Δ v J i D → DescI If′ Δ J

toCon   : {c : Cxf Δ Γ} {v : VxfO c W V} {i : J → I} {D : ConI If Γ V I}
        → ConOrnDesc If′ v i D → ConI If′ Δ W J

toDesc []      = []
toDesc (C ∷ D) = toCon C ∷ toDesc D 

toCon (𝟙 k x {if′ = if}) = 𝟙 {if = if} k
toCon (ρ k h D x y {if′ = if}) = ρ {if = if} k h (toCon D)
toCon {v = v} (σ S h v′ D x {if′ = if}) = σ (S ∘ over v) {if = if} h (toCon D)
toCon {v = v} (δ R j k h D x {if′ = if} {iff′ = iff}) = δ {if = if} {iff = iff} (j ∘ over v) (k ∘ over v) R h (toCon D)
toCon (Δρ k h D {if′ = if}) = ρ {if = if} k h (toCon D)
toCon (Δσ S v′ h D x {if′ = if}) = σ S {if = if} h (toCon D)
toCon (Δδ R k m h D x {if′ = if} {iff′ = iff}) = δ {if = if} {iff = iff} k m R h (toCon D)
--toCon (∙δ fΛ m D RR′ h p₁ p₂ x {if′ = if} {iff′ = iff}) = δ {if = if} {iff = iff} m fΛ (toDesc RR′) h (toCon D)


--toCon (∇σ s D) = toCon D
--toCon (∇δ s D) = toCon D


toOrn []      = []
toOrn (C ∷ D) = toConOrn C ∷ toOrn D 

toConOrn (𝟙 k x) = 𝟙 x
toConOrn (ρ k h D x y) = ρ (toConOrn D) x y
toConOrn (σ S h v′ D x) = σ v′ (toConOrn D) x
toConOrn (δ R j k h D x) = δ (toConOrn D) x
toConOrn (Δρ k h D) = Δρ (toConOrn D)
toConOrn (Δσ S v′ h D x) = Δσ v′ (toConOrn D) x
toConOrn (Δδ R k m h D x) = Δδ (toConOrn D) x
toConOrn (∇σ s D) = ∇σ s (toConOrn D)
toConOrn (∇δ s D) = ∇δ s (toConOrn D)
toConOrn (∙δ fΛ m D RR′ h p₁ p₂ x) = ∙δ (toConOrn D) (toOrn RR′) p₁ p₂ x
