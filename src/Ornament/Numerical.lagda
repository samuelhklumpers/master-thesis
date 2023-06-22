\begin{code}
{-# OPTIONS --type-in-type --with-K #-}


module Ornament.Numerical where

open import Ornament.Desc
open import Ornament.Orn
open import Ornament.OrnDesc


open Agda.Primitive renaming (Set to Type)

open import Data.Unit
open import Data.Empty
open import Data.Product
open import Data.Sum hiding (map₂)

open import Data.List as L using (List)
open List

open import Data.Nat hiding (_!)
open import Data.Fin using (Fin; #_)
open import Function.Base
open import Data.Vec using (Vec)


open import Relation.Binary.PropositionalEquality using (_≡_; cong; sym; refl; subst) renaming (trans to _∙_; subst₂ to subst2)



private variable
  J K L : Type
  A B C X Y Z : Type
  P P′ : Type
  Γ Δ Θ : Tel P
  U V W   : ExTel Γ
  If : Info

open Info

\end{code}

%<*Number>
\begin{code}
Number : Info
Number .𝟙i = ℕ
Number .ρi = ℕ
Number .σi S = ∀ p → S p → ℕ
Number .δi Γ J = Γ ≡ ∅ × J ≡ ⊤ × ℕ
\end{code}
%</Number>

%<*toN-type>
\begin{code}
toℕ : {D : DescI Number Γ ⊤} → ∀ {p} → μ D p tt → ℕ
\end{code}
%</toN-type>

\begin{code}
toℕ {D = D} = toℕ-lift D id-InfoF
  where
  toℕ-lift : (D : DescI If Γ ⊤) → InfoF If Number → ∀ {p} → μ D p tt → ℕ
  
  toℕ-lift {If = If} D ϕ = fold (λ _ _ → toℕ-desc D) _ tt
    where
\end{code}

%<*toN-con>
\begin{code}
    toℕ-desc : (D : DescI If Γ ⊤) → ∀ {a b} → ⟦ D ⟧ (λ _ _ → ℕ) a b → ℕ
    toℕ-con : (C : ConI If Γ ⊤ V) → ∀ {a b} → ⟦ C ⟧ (λ _ _ → ℕ) a b → ℕ

    toℕ-desc (C ∷ D) (inj₁ x) = toℕ-con C x
    toℕ-desc (C ∷ D) (inj₂ y) = toℕ-desc D y

    toℕ-con  (𝟙 {if = k} j) refl                          
             = ϕ .𝟙f k

    toℕ-con  (ρ {if = k} j g C)                   (n , x)
             = ϕ .ρf k * n + toℕ-con C x

    toℕ-con  (σ S {if = S→ℕ} h C)                 (s , x)
             = ϕ .σf _ S→ℕ _ s + toℕ-con C x

    toℕ-con  (δ {if = if} {iff = iff} j g R h C)  (r , x)
             with ϕ .δf _ _ if
    ...      | refl , refl , k  
             = k * toℕ-lift R (ϕ ∘InfoF iff) r + toℕ-con C x
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

bin-2 : μ BinND tt tt
bin-2 = con (inj₂ (inj₂ (inj₁ (con (inj₁ refl) , refl))))

bin-5 : μ BinND tt tt
bin-5 = con (inj₂ (inj₁ (con (inj₂ (inj₂ (inj₁ (con (inj₁ refl) , refl)))) , refl)))

-- simple the number system underlying simple finger trees
DigND : DescI Number ∅ ⊤
DigND = 𝟙 {if = 1} _
      ∷ 𝟙 {if = 2} _
      ∷ 𝟙 {if = 3} _
      ∷ []

FingND : DescI Number ∅ ⊤
FingND = 𝟙 {if = 0} _
       ∷ 𝟙 {if = 1} _
       ∷ δ- {if = refl , refl , 1} {iff = id-InfoF} _ _ DigND (ρ0 {if = 2} _ (δ- {if = refl , refl , 1} {iff = id-InfoF} _ _ DigND (𝟙 {if = 0} _)))
       ∷ []

-- 1 ⟨ 0 ⟩ 1
finger-2 : μ FingND tt tt
finger-2 = con (inj₂ (inj₂ (inj₁ (con (inj₁ refl) , con (inj₁ refl) , con (inj₁ refl) , refl))))

-- 1 ⟨ 2 ⟩ 2
finger-7 : μ FingND tt tt
finger-7 = con (inj₂ (inj₂ (inj₁ (con (inj₁ refl) , finger-2 , con (inj₂ (inj₁ refl)) , refl))))


\end{code}

Theorem: given a number system D, there is a "good container" D', which also satisfies (x : μ D' A tt) → size x ≡ shape x
%<*TrieO-type>
\begin{code}
TrieO : (D : DescI Number ∅ ⊤) → OrnDesc Plain (∅ ▷ const Type) ! ⊤ ! D
\end{code}
%</TrieO-type>

\begin{code}
TrieO D = TrieO-desc D id-InfoF
  module TrieO where
  TrieO-desc : (D : DescI If ∅ ⊤) → InfoF If Number → OrnDesc Plain (∅ ▷ const Type) ! ⊤ ! D
\end{code}

%<*TrieO-con-type>
\begin{code}
  TrieO-con  : ∀ {V} {W : ExTel (∅ ▷ const Type)} {f : VxfO ! W V}
             (C : ConI If ∅ ⊤ V) → InfoF If Number
             → ConOrnDesc Plain {W = W} {K = ⊤} f ! C
\end{code}
%</TrieO-con-type>

\begin{code}
  TrieO-desc []      f = []
  TrieO-desc (C ∷ D) f = TrieO-con C f ∷ TrieO-desc D f
\end{code}
  
-- trie (λ X tt → ⊤) {toℕ tt → k} 
-- ⇒ (λ X A → A^k)
%<*TrieO-1>
\begin{code}
  TrieO-con {f = f} (𝟙 {if = k} j) ϕ =                             
    Δσ (λ { ((_ , A) , _) → Vec A (ϕ .𝟙f k)}) f proj₁              
    (𝟙 ! (const refl))                           
    (λ p → refl)
\end{code}
%</TrieO-1>

   
-- trie (λ X tt → X tt × F X tt) {toℕ (x , y) → k * toℕ x + toℕ y}
-- ⇒ (λ X A → X (A ^ k) × trie F X A)
%<*TrieO-rho>
\begin{code}
  TrieO-con {f = f} (ρ {if = k} j g C) ϕ =                         
    ρ ! (λ { (_ , A) → _ , Vec A (ϕ .ρf k) })                      
    (TrieO-con C ϕ)                                           
    (λ p → refl) λ p → refl
\end{code}
%</TrieO-rho>

-- trie (λ X tt → S × F X tt) {toℕ (s , y) → if s + toℕ y}
-- ⇒ (λ X A → Σ[ s ∈ S ] A^(if s) × trie F X A)
%<*TrieO-sigma>
\begin{code}
  TrieO-con {f = f} (σ S {if = if} h C) ϕ =                              
    σ S id (h ∘ VxfO-▷ f S)                                              
    (Δσ (λ { ((_ , A) , _ , s) → Vec A (ϕ .σf _ if _ s) }) (h ∘ _) id
    (TrieO-con C ϕ)
    λ p → refl) (λ p → refl)
\end{code}
%</TrieO-sigma>


-- trie (λ X tt → G tt × F X tt) {toℕ (r , y) → k * toℕ r + toℕ y}
-- ⇒ (λ X A → trie G (μ (trie G)) A × trie F X A)
%<*TrieO-delta>
\begin{code}
  TrieO-con {f = f} (δ {if = if} {iff = iff} j g R h C) ϕ with ϕ .δf _ _ if    
  ... | refl , refl , k =                                                      
    ∙δ
      {f'' =  λ { (w , x) → h  (f w , ornForget
              (toOrn (TrieO-desc R (ϕ ∘InfoF iff))) _ x) }}
      (λ { ((_ , A) , _) → _ , Vec A k }) !
    (TrieO-con C ϕ)
    (TrieO-desc R (ϕ ∘InfoF iff)) id
    (λ _ _ → refl) (λ _ _ → refl) λ p → refl
\end{code}
%</TrieO-delta>

\begin{code}
_L+_ : List (ConI If Γ J ∅) → DescI If Γ J → DescI If Γ J
[]        L+ D = D
(C ∷ Cs)  L+ D = C ∷ (Cs L+ D)

PathD : (D : DescI Number ∅ ⊤) → Desc ∅ (μ D tt tt)
PathD′ : (D : DescI If ∅ ⊤) (if : InfoF If Number) → Desc ∅ (μ D tt tt)

PathD E = PathD′ E id-InfoF
PathD′ E if = PathDD E if λ a b → con
  module PathD where
    N : _
    N = μ E tt tt

    PathDD : (D : DescI If ∅ ⊤) (if : InfoF If Number) → (⟦ D ⟧ (λ _ _ → N) ⇶ λ _ _ → N) → Desc ∅ (μ E tt tt)
    PathDC : (C : ConI If ∅ ⊤ V) (if : InfoF If Number) (f : Vxf ∅ W V) → (∀ b → ⟦ C ⟧ (λ _ _ → N) (tt , f b) _ → N) → List (Con ∅ (μ E tt tt) W)

    PathDD []      if ϕ = []
    PathDD (C ∷ D) if ϕ = PathDC C if id (λ _ c → ϕ _ _ (inj₁ c)) L+ PathDD D if λ p i → ϕ p i ∘ inj₂

    PathDC (𝟙 {if = k} j) if f ϕ
      = σ- (const (Fin (if .𝟙f k))) (𝟙 (λ { (_ , w) → ϕ w refl }))
      ∷ []

    -- looks scary, pretty regular to write down though
    PathDC (ρ {if = k} j g C) if f ϕ
      = σ- (const (Fin (if .ρf k))) (σ+ (const N) (σ+ (λ { (p , w , _) → ⟦ C ⟧ (λ _ _ → N) (p , f w) tt }) (ρ0 (proj₂ ∘ proj₁ ∘ proj₂) (𝟙 λ { (_ , (w , n) , c) → ϕ w (n , c) }))))
      ∷ L.map (σ+ (const N)) (PathDC C if (f ∘ proj₁) (λ { (w , n) c → ϕ w (n , c) }))

    PathDC (σ S {if = k} h C)     if f ϕ
      = σ+ (λ { (p , w) → S (p , f w) }) (σ+ (λ { (p , w , s) → ⟦ C ⟧ (λ _ _ → N) (p , h (f w , s)) tt }) (σ- (λ { (p , (w , s) , c) → Fin (if .σf _ k (p , f w) s) }) (𝟙 λ { (p , (w , s) , c) → ϕ w (s , c) })))
      ∷ L.map (σ+ λ { (p , w) → S (p , f w) }) (PathDC C if (h ∘ Vxf-▷ f S) λ { (w , s) c → ϕ w (s , c) })

    PathDC (δ {If′ = If′} {if = k} {iff = iff} j g R h C) if f ϕ with if .δf _ _ k
    ... | refl , refl , k
      = σ- (const (Fin k)) (σ+ (const (μ R tt tt)) (σ+ (λ { (p , w , r) → ⟦ C ⟧ (λ _ _ → N) (p , h (f w , r)) tt }) (δ- (proj₂ ∘ proj₁ ∘ proj₂) ! (PathD′ R (if ∘InfoF iff)) (𝟙 λ { (p , (w , r) , c) → ϕ w (r , c) }))))
      ∷ L.map (δ+ ! ! R) (PathDC C if (λ { (w , r) → h (f w , r) }) λ { (w , r) c → ϕ w (r , c) })
\end{code}

\begin{code}
BinID : Desc ∅ (μ BinND tt tt)
BinID = PathD BinND

BinI : μ BinND tt tt → Type
BinI n = μ BinID tt n

-- the constructors are
-- i0  : ⊥ → BinI 0
-- 1b1 : 2 → BinI n → BinI (n 1b)
-- 1b0 : 1 → BinI (n 1b)
-- 2b1 : 2 → BinI n → BinI (n 2b)
-- 2b0 : 2 → BinI (n 2b)
-- (I think)

-- like the 3rd index into bin-5
bin-3/5 : BinI bin-5
bin-3/5 = con (inj₂ (inj₁ (# 1 , _ , (refl , ((con (inj₂ (inj₂ (inj₂ (inj₂ (inj₁ (_ , (# 0 , refl)))))))) , refl)))))
\end{code}

ITrieO : (D : DescI Number ∅ ⊤) → OrnDesc Plain (∅ ▷ const Type) id (μ D tt tt) ! (toDesc (TrieO D))
ITrieO D = ITrieO′ D D id-InfoF
  module ITrieO where
    module _ (D' : DescI Number ∅ ⊤) where
      ITrieO′ : (D : DescI If ∅ ⊤) (if : InfoF If Number) → OrnDesc Plain (∅ ▷ const Type) id (μ D' tt tt) ! (toDesc (TrieO.TrieO-desc D' D if))
      
      N : _
      N = μ D' tt tt

      ITrieO-desc : (D : DescI If ∅ ⊤) → (⟦ D ⟧ (λ _ _ → N) ⇶ λ _ _ → N) → (if : InfoF If Number) → OrnDesc Plain (∅ ▷ const Type) id (μ D' tt tt) ! (toDesc (TrieO.TrieO-desc D' D if))

      ITrieO-con  : ∀ {U V} {W : ExTel (∅ ▷ const Type)} {f : VxfO ! U V} {g : VxfO id W U}
                 (C : ConI If ∅ ⊤ V) → (∀ a b → ⟦ C ⟧ (λ _ _ → N) (tt , f (g {p = a} b)) _ → N) → (if : InfoF If Number)
                 → ConOrnDesc Plain {W = W} {K = μ D' tt tt} g ! (toCon {f = f} (TrieO.TrieO-con D' C if))

      ITrieO-desc []      ϕ if = []
      ITrieO-desc (C ∷ D) ϕ if = ITrieO-con C (λ a b x → ϕ tt b (inj₁ x)) if ∷ (ITrieO-desc D (ϕ ∘₃ inj₂) if)
      
      ITrieO-con {f = f} {g = g} (𝟙 {if = k} j) ϕ if
        = σ _ id (g ∘ proj₁) (𝟙 (λ { (p , w , _) → ϕ p w refl }) λ p → refl) (λ p → refl)

      ITrieO-con {f = f} {g = g} (ρ {if = k} j h C) ϕ if
        = Δσ (const N) (g ∘ proj₁) id
        ( ρ (λ (p , w , n) → n) (λ { (_ , A) → _ , Vec A (if .ρf k) })
          (ITrieO-con C (λ { a (u , n) x → ϕ a u (n , x) }) if)
        (λ p → refl) (λ p → refl)) (λ p → refl)
        
      ITrieO-con {f = f} {g = g} (σ S {if = k} h C)      ϕ if
        = σ _ id (VxfO-▷ g (S ∘ over f))
        ( σ _ id (VxfO-▷ (VxfO-▷ g (S ∘ over f)) (λ { ((_ , A) , _ , s) → Vec A (if .σf _ k _ s) }))
          (ITrieO-con C (λ { a ((w , s) , _) x → ϕ a w (s , x) }) if)
        λ p → refl) λ p → refl
        
      ITrieO-con {f = f} {g = g} (δ {if = k} {iff = iff} j g' R h C) ϕ if with if .δf _ _ k
      ... | refl , refl , k
        = Δσ (const (μ R tt tt)) (g ∘ proj₁) id
        ( Δσ (const (μ D' tt tt)) (g ∘ proj₁ ∘ proj₁) id
        ( ∙δ {f'' = VxfO-▷-map (g ∘ proj₁ ∘ proj₁)
                     (liftM2 (μ (toDesc (TrieO.TrieO-desc D' R (if ∘InfoF iff)))) (λ { ((_ , A) , _) → tt , Vec A k }) !)
                     (liftM2 (μ (toDesc (ITrieO-desc R {!!} (if ∘InfoF iff)))) (λ p → tt , Vec (id (p .proj₁) .proj₂) k) (λ x → proj₂ (proj₂ x)))
                     {!!} }
             (λ { ((_ , A) , ((w , r) , _)) → tt , Vec A k }) (proj₂ ∘ proj₂)
          (ITrieO-con C {!λ { a (((w , r) , n) , _)  x → ϕ a w (r , {!!}) }!} if)
          {!ITrieO R!} id
        (λ _ _ → refl) (λ _ _ → refl) λ p → refl) λ p → refl) λ p → refl
    
      ITrieO′ D if = ITrieO-desc D {!!} if


--(liftM2 (μ (toDesc (TrieO.TrieO-desc D' R (if ∘InfoF iff)))) (λ { ((_ , A) , _) → tt , Vec A k }) !)
--ITrieO-desc R (λ { a b x → ϕ {!!} {!!} {!!} }) (if ∘InfoF iff)

-- to prove: size x ≡ shape x
-- * μ D is likely to be Traversable when all σ's in it are
-- * as every S in a DescI Number ∅ ⊤ is necessarily invariant, it is also trivially Traversable

-- to prove: every OrnDesc induces an ornamental algebra -> doesn't work
-- to prove: for some appropriate Ix : (D : DescI Number ∅ ⊤) → Desc ∅ (μ D tt tt),
--           Ix D is also initial for the algebra of the algebraic ornament induced by the ornamental algebra (yes)

-- to summarize, for every number system, there is an appropriate "list", which has an appropriate "vector"
-- this vector is representable, the list is traversable, and everything still satisfies size ≡ shape ≡ index

%<*Unit>
\begin{code}
UnitD : DescI Number ∅ ⊤
UnitD = 𝟙 {if = 1} _
      ∷ []
\end{code}
%</Unit>



