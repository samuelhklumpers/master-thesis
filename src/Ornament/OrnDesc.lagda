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
\end{code}
%</OrnDesc>

%<*ConOrn-preserve>
\begin{code}
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

    δ : (R : DescI If″ Θ K) (j : Γ & V ⊢ K) (t : Γ & V ⊢ ⟦ Θ ⟧tel tt)
        {g : Vxf Γ _ V′} (h : Vxf Δ _ W′)
        {v′ : VxfO c W′ V′}
      → (∀ {p} → g ∘ VxfO-▷ v (liftM2 (μ R) t j) ∼ v′ {p = p} ∘ h)
      → {if : If .δi Θ K} {iff : InfoF If″ If}
        {if′ : If′ .δi Θ K} {iff′ : InfoF If″ If′}
      → ConOrnDesc If′ v′ i CD
      → ConOrnDesc If′ v i (δ {If} {if = if} {iff = iff} j t R g CD)
\end{code}
%</ConOrn-preserve>

%<*ConOrn-extend>
\begin{code}
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
\end{code}
%</ConOrn-extend>

%<*ConOrn-compose-1>
\begin{code}
    ∙δ : {R : DescI If″ Θ K} {c′ : Cxf Λ Θ} {k′ : M → K} {k : V ⊢ K}
         {fΘ : V ⊢ ⟦ Θ ⟧tel tt} {g : Vxf _ (V ▷ liftM2 (μ R) fΘ k) V′}  
         (m : W ⊢ M) (fΛ : W ⊢ ⟦ Λ ⟧tel tt)
       → (RR′ : OrnDesc If‴ Λ c′ M k′ R)
         (h : Vxf _ (W ▷ liftM2 (μ (toDesc RR′)) fΛ m) W′)
         {v′ : VxfO c W′ V′}   
       → (p₁ : ∀ q w → c′ (fΛ (q , w)) ≡ fΘ (c q , v w))
       → (p₂ : ∀ q w → k′ (m (q , w))  ≡ k (c q , v w))
\end{code}
%</ConOrn-compose-1>
\begin{code}
       → (∀ {p′} (p : ⟦ W ▷ liftM2 (μ (toDesc RR′)) fΛ m ⟧tel p′) → v′ (h p) ≡ g (VxfO-▷-map v (liftM2 (μ R) fΘ k) (liftM2 (μ (toDesc RR′)) fΛ m) (λ q w x → subst₂ (μ R) (p₁ _ _) (p₂ _ _) (ornForget RR′ (fΛ (q , w)) (m (q , w)) x)) p))
\end{code}
%<*ConOrn-compose-2>
\begin{code}
       → ∀ {if} {iff} {if′ : If′ .δi Λ M} {iff′ : InfoF If‴ If′}
       → (DE : ConOrnDesc If′ v′ i CD)
       → ConOrnDesc If′ v i (δ {If} {if = if} {iff = iff} k fΘ R g CD)
\end{code}
%</ConOrn-compose-2>

omitted:
∙δ
 -- 



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
  toCon (𝟙 j′ x {if′ = if})
    = 𝟙 {if = if} j′

  toCon (ρ j′ h x x₁ {if′ = if} CO)
    = ρ {if = if} j′ h (toCon CO)

  toCon {v = v} (σ S h v′ x {if′ = if} CO)
    = σ (S ∘ over v) {if = if} h (toCon CO)

  toCon {v = v} (δ R j t h x {if′ = if} {iff′ = iff} CO)
    = δ {if = if} {iff = iff} (j ∘ over v) (t ∘ over v) R h (toCon CO)

  toCon (Δσ S h v′ x {if′ = if} CO)
    = σ S {if = if} h (toCon CO)
  
  toCon (Δδ R j t h x {if′ = if} {iff′ = iff} CO)
    = δ {if = if} {iff = iff} j t R h (toCon CO)
  
  toCon (∙δ m fΛ RR′ h p₁ p₂ p₃ {if′ = if} {iff′ = iff} CO)
    = δ {if = if} {iff = iff} m fΛ (toDesc RR′) h (toCon CO)
\end{code}
%</toDesc>

\begin{code}
  ornErase : ∀ {Δ} {Γ} {J} {I} {If} {If′} {v : Cxf Δ Γ} {i : J → I}
             {D : DescI If Γ I} {X} (OD : OrnDesc If′ Δ v J i D) (p : ⟦ Δ ⟧tel tt)
             (j : J) (x : ⟦ toDesc OD ⟧D (λ p j → X (v p) (i j)) p j) →
           ⟦ D ⟧D X (v p) (i j)
  ornErase (OC ∷ OD) p j (inj₁ x) = inj₁ (conOrnErase OC (p , tt) j x)
  ornErase (OC ∷ OD) p j (inj₂ y) = inj₂ (ornErase OD p j y)

  conOrnErase : ∀ {Δ} {Γ V W} {J} {I} {If} {If′} {v : Cxf Δ Γ} {c : VxfO v W V} {i : J → I}
              {X} {CD : ConI If Γ V I}
              (OC : ConOrnDesc If′ c i CD) (p : ⟦ Δ & W ⟧tel) (j : J)
              (x : ⟦ toCon OC ⟧C (λ p₁ j₁ → X (v p₁) (i j₁)) p j) →
            ⟦ CD ⟧C X (over c p) (i j)
  conOrnErase {i = i} (𝟙 j′ x₁) p j x = trans (cong i x) (x₁ p)
  conOrnErase {X = X} (ρ j′ h x₁ x₂ OC) (p , w) j (x , y) = subst₂ X (sym (x₁ p)) (x₂ (p , w)) x , conOrnErase OC (p , w) j y
  conOrnErase {v = v} {X = X} (σ {CD = CD} S h v′ x₁ OC) (p , w) j (s , x) = s , subst₂ (⟦ CD ⟧C X) (cong (v p ,_) (sym (x₁ (w , s)))) refl (conOrnErase OC (p , h (w , s)) j x) 
  conOrnErase {X = X} (δ {CD = CD} R j₁ t h x₁ OC) (p , w) j (r , x) = r , subst (λ a → ⟦ CD ⟧C X a _) (cong (_ ,_) (sym (x₁ (w , r)))) (conOrnErase OC (p , h (w , r)) j x)
  conOrnErase {X = X} (Δσ {CD = CD} S h v′ x₁ OC) (p , w) j (s , x) = subst (λ a → ⟦ CD ⟧C X a _) (cong (_ ,_) (sym (x₁ (w , s)))) (conOrnErase OC (p , h (w , s)) j x)
  conOrnErase {X = X} (Δδ {CD = CD} R j₁ t h x₁ OC) (p , w) j (r , x) = subst (λ a → ⟦ CD ⟧C X a _) (cong (_ ,_) (sym (x₁ (w , r)))) (conOrnErase OC (p , h (w , r)) j x)
  conOrnErase {v = v} {X = X} (∙δ {CD = CD} {R = R} m fΛ RR′ h p₁ p₂ p₃ OC) (p , w) j (r , x) = subst₂ (μ R) (p₁ _ _) (p₂ _ _) (ornForget RR′ _ _ r) , subst (λ a → ⟦ CD ⟧C X a _) (cong (v p ,_) (p₃ (w , r))) (conOrnErase OC (p , h (w , r)) j x)

  ornAlg : ∀ {Δ} {Γ : Tel ⊤} {J} {I} {If} {If′} {v : Cxf Δ Γ}
           {i : J → I} {D : DescI If Γ I} (OD : OrnDesc If′ Δ v J i D) →
         ⟦ toDesc OD ⟧D (λ p j → μ D (v p) (i j)) ⇶
         (λ p j → μ D (v p) (i j))
  ornAlg OD p i x = con (ornErase OD p i x)

  ornForget : {v : Cxf Δ Γ} {i : J → I} {D : DescI If Γ I}
            → (OD : OrnDesc If′ Δ v J i D)
            → μ (toDesc OD) ⇶ λ d j → μ D (v d) (i j)
  ornForget OD = fold (ornAlg OD)
\end{code}


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
  Oσ+ : (S : Γ & V ⊢ Type) {CD : ConI If Γ V′ I} {h : Vxf _ _ _}
    → {if : If .σi S} {if′ : If′ .σi (S ∘ over v)}
    → ConOrnDesc If′ (h ∘ VxfO-▷ v S) i CD
    → ConOrnDesc If′ v i (σ {If} S {if = if} h CD)
  Oσ+ S {h = h} {if′ = if′} CO
    = σ S id (h ∘ VxfO-▷ v S) (λ _ → refl) {if′ = if′} CO

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

  O∙δ+ : {R : DescI If″ Θ K} {c′ : Cxf Λ Θ} {k′ : M → K} {k : V ⊢ K}
       {fΘ : V ⊢ ⟦ Θ ⟧tel tt} {g : Vxf _ (V ▷ liftM2 (μ R) fΘ k) V′}  
       (m : W ⊢ M) (fΛ : W ⊢ ⟦ Λ ⟧tel tt)
     → (RR′ : OrnDesc If‴ Λ c′ M k′ R)
     → (p₁ : ∀ q w → c′ (fΛ (q , w)) ≡ fΘ (c q , v w))
     → (p₂ : ∀ q w → k′ (m (q , w))  ≡ k (c q , v w))
     → ∀ {if} {iff} {if′ : If′ .δi Λ M} {iff′ : InfoF If‴ If′}
     → (DE : ConOrnDesc If′ (g ∘ VxfO-▷ v (liftM2 (μ R) fΘ k) ∘ map₂ λ {x} y → subst₂ (μ R) (p₁ _ _) (p₂ _ _) (ornForget RR′ (fΛ (_ , x)) (m (_ , x)) y)) i CD)
     → ConOrnDesc If′ v i (δ {If} {if = if} {iff = iff} k fΘ R g CD)
  O∙δ+ m fΛ RR′ p₁ p₂ {if′ = if′} {iff′ = iff′} CO = ∙δ m fΛ RR′ id p₁ p₂ (λ _ → refl) {if′ = if′} {iff′ = iff′} CO


  O∙δ- : {R : DescI If″ Θ K} {c′ : Cxf Λ Θ} {k′ : M → K} {k : V ⊢ K}
         {fΘ : V ⊢ ⟦ Θ ⟧tel tt} {g : Vxf _ (V ▷ liftM2 (μ R) fΘ k) V′}  
         (m : W ⊢ M) (fΛ : W ⊢ ⟦ Λ ⟧tel tt)
       → (RR′ : OrnDesc If‴ Λ c′ M k′ R)
         {v′ : VxfO c W V′}   
       → (p₁ : ∀ q w → c′ (fΛ (q , w)) ≡ fΘ (c q , v w))
       → (p₂ : ∀ q w → k′ (m (q , w))  ≡ k (c q , v w))
       → (∀ {p′} (p : Σ (⟦ W ⟧tel p′) _) →  v′ (fst p) ≡
          g  (VxfO-▷-map v (liftM2 (μ R) fΘ k) (liftM2 (μ (toDesc RR′)) fΛ m)
             (λ  q w x → subst₂ (μ R) (p₁ q w) (p₂ q w)
                 (ornForget RR′ (fΛ (q , w)) (m (q , w)) x)) p))
       → ∀ {if} {iff} {if′ : If′ .δi Λ M} {iff′ : InfoF If‴ If′}
       → (DE : ConOrnDesc If′ v′ i CD)
       → ConOrnDesc If′ v i (δ {If} {if = if} {iff = iff} k fΘ R g CD)
  O∙δ- m fΛ RR′ p₁ p₂ p₃ {if′ = if′} {iff′ = iff′} CO = ∙δ m fΛ RR′ fst p₁ p₂ p₃ {if′ = if′} {iff′ = iff′} CO
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

%<*PhalanxD>
\begin{code}
ThreeD : Desc ∅ ⊤
ThreeD = 𝟙 _ ∷ 𝟙 _ ∷ 𝟙 _ ∷ []

PhalanxD : Desc ∅ ⊤
PhalanxD = 𝟙 _
         ∷ 𝟙 _
         ∷ δ- _ _ ThreeD
         ( ρ0 _
         ( δ- _ _ ThreeD
         ( 𝟙 _))) 
         ∷ []
\end{code}
%</PhalanxD>

%<*DigitOD>
\begin{code}
DigitOD : OrnDesc Plain (∅ ▷ const Type) ! ⊤ id ThreeD
DigitOD = OΔσ- (λ ((_ , A) , _) → A)
        ( 𝟙 _ (const refl))
        ∷ OΔσ- (λ ((_ , A) , _) → A)
        ( OΔσ- (λ ((_ , A) , _) → A)
        ( 𝟙 _ (const refl)))
        ∷ OΔσ- (λ ((_ , A) , _) → A)
        ( OΔσ- (λ ((_ , A) , _) → A)
        ( OΔσ- (λ ((_ , A) , _) → A)
        ( 𝟙 _ (const refl))))
        ∷ []
\end{code}
%</DigitOD>

%<*FingerOD>
\begin{code}
FingerOD : OrnDesc Plain (∅ ▷ const Type) ! ⊤ id PhalanxD
FingerOD = 𝟙 _ (const refl)
         ∷ OΔσ- (λ ((_ , A) , _) → A)
         ( 𝟙 _ (const refl))
         ∷ O∙δ- _ (λ (p , _) → p) DigitOD (λ _ _ → refl) (λ _ _ → refl) (λ _ → refl)
         ( ρ _ (λ (_ , A) → (_ , Pair A)) (const refl) (const refl)
         ( O∙δ- _ (λ (p , _) → p) DigitOD (λ _ _ → refl) (λ _ _ → refl) (λ _ → refl)
         ( 𝟙 _ (const refl))))
         ∷ []
\end{code}
%</FingerOD>

