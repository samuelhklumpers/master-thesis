\begin{document}
\begin{code}
{-# OPTIONS --type-in-type #-}
module Tex.Discussion.Sigma-Desc where

open import Agda.Primitive
  using    ( Level
           ; SSet )
  renaming ( lzero to ℓ-zero
           ; lsuc  to ℓ-suc
           ; _⊔_   to ℓ-max
           ; Set   to Type
           ; Setω  to Typeω )

open import Function.Base
open import Data.Unit
open import Data.Nat
open import Data.Fin
open import Data.Empty
open import Data.Maybe


\end{code}

%<*Leibniz>
\begin{code}
data Leibniz : Type where
  0b       : Leibniz
  1b_ 2b_  : Leibniz → Leibniz
\end{code}
%</Leibniz>

\begin{code}

private variable
  n m : Leibniz

\end{code}

%<*FinB>
\begin{code}
data FinB : Leibniz → Type where
  0/1      : FinB (1b n)
  0/2 1/2  : FinB (2b n)

  0-1b_ 1-1b_ : FinB n → FinB (1b n)
  0-2b_ 1-2b_ : FinB n → FinB (2b n)
\end{code}
%</FinB>



%<*Sigma-Desc>
\begin{code}
data Σ-Desc (I : Type) : Type where
  𝟙 : I → Σ-Desc I
  ρ : I → Σ-Desc I → Σ-Desc I 
  σ : (S : Type) → (S → Σ-Desc I) → Σ-Desc I
\end{code}
%</Sigma-Desc>



%<*LeibnizD>
\begin{code}
LeibnizΣD : Σ-Desc ⊤
LeibnizΣD = σ (Fin 3) λ
  { zero              → 𝟙 _
  ; (suc zero)        → ρ _ (𝟙 _)
  ; (suc (suc zero))  → ρ _ (𝟙 _) }
\end{code}
%</LeibnizD>



%<*FinBD>
\begin{code}
FinBΣD : Σ-Desc Leibniz
FinBΣD = σ (Fin 3) λ
  { zero              → σ (Fin 0) λ _ → 𝟙 0b
  ; (suc zero)        → σ Leibniz λ n → σ (Fin 2) λ
    { zero        → σ (Fin 1) λ _ →        𝟙 (1b n) 
    ; (suc zero)  → σ (Fin 2) λ _ → ρ n (  𝟙 (1b n)) }
  ; (suc (suc zero))  → σ Leibniz λ n → σ (Fin 2) λ
    { zero        → σ (Fin 2) λ _ →        𝟙 (2b n) 
    ; (suc zero)  → σ (Fin 2) λ _ → ρ n (  𝟙 (2b n)) } }
\end{code}
%</FinBD>
\end{document}




-- here is the construction of using Paths using lists of constructors
-- it is very hard to combine with the indexed numerical representations

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
    PathDD (C ∷ D) if ϕ = PathDC C if id (λ _ c → ϕ _ _ (inl c)) L+ PathDD D if λ p i → ϕ p i ∘ inr

    PathDC (𝟙 {if = k} j) if f ϕ
      = σ- (const (Fin (if .𝟙f k))) (𝟙 (λ { (_ , w) → ϕ w refl }))
      ∷ []

    -- looks scary, pretty regular to write down though
    PathDC (ρ {if = k} j g C) if f ϕ
      = σ- (const (Fin (if .ρf k))) (σ+ (const N) (σ+ (λ { (p , w , _) → ⟦ C ⟧ (λ _ _ → N) (p , f w) tt }) (ρ0 (snd ∘ fst ∘ snd) (𝟙 λ { (_ , (w , n) , c) → ϕ w (n , c) }))))
      ∷ L.map (σ+ (const N)) (PathDC C if (f ∘ fst) (λ { (w , n) c → ϕ w (n , c) }))

    PathDC (σ S {if = k} h C)     if f ϕ
      = σ+ (λ { (p , w) → S (p , f w) }) (σ+ (λ { (p , w , s) → ⟦ C ⟧ (λ _ _ → N) (p , h (f w , s)) tt }) (σ- (λ { (p , (w , s) , c) → Fin (if .σf _ k (p , f w) s) }) (𝟙 λ { (p , (w , s) , c) → ϕ w (s , c) })))
      ∷ L.map (σ+ λ { (p , w) → S (p , f w) }) (PathDC C if (h ∘ Vxf-▷ f S) λ { (w , s) c → ϕ w (s , c) })

    PathDC (δ {If′ = If′} {if = k} {iff = iff} j g R h C) if f ϕ with if .δf _ _ k
    ... | refl , refl , k
      = σ- (const (Fin k)) (σ+ (const (μ R tt tt)) (σ+ (λ { (p , w , r) → ⟦ C ⟧ (λ _ _ → N) (p , h (f w , r)) tt }) (δ- (snd ∘ fst ∘ snd) ! (PathD′ R (if ∘InfoF iff)) (𝟙 λ { (p , (w , r) , c) → ϕ w (r , c) }))))
      ∷ L.map (δ+ ! ! R) (PathDC C if (λ { (w , r) → h (f w , r) }) λ { (w , r) c → ϕ w (r , c) })

unμ : {D : DescI If Γ J} → ∀ {p i} → μ D p i ≃ ⟦ D ⟧ (μ D) p i
unμ .fst (con x) = x
unμ .snd .equiv-proof y .fst = con y , λ i → y
unμ .snd .equiv-proof y .snd (con x , p) = ΣPathP ((λ i → con (p (~ i))) , λ j i → p (~ j ∨ i))

PathD-correct : ∀ D n → μ (PathD D) tt n ≃ Fin (value n)
PathD-correct D n = compEquiv unμ {!compEquiv (go D id-InfoF n) {!!}!}
  where
  open PathD D

  go :  (E : DescI If ∅ ⊤) (if : InfoF If Number)
        (c : ⟦ E ⟧ (λ _ _ → N id-InfoF) ⇶ (λ _ _ → N id-InfoF))
     →  ∀ n → ⟦ PathDD id-InfoF E if c ⟧ (μ (PathD D)) tt n ≃ ⟦ PathDD id-InfoF E if c ⟧ (λ _ n → Fin (value n)) tt n
     
  go2 : (E : ConI If ∅ ⊤ V) (if : InfoF If Number) → ∀ n v → ⟦ {!PathDC!} ⟧ (μ (PathD D)) (tt , v) n ≃ ⟦ {!!} ⟧ (λ _ n → Fin (value n)) (tt , v) n

  go []       _  _ _ = idEquiv ⊥
  go (E ∷ Es) if c n = {!⟦ PathDD id-InfoF (E ∷ Es) if c ⟧ (μ (PathD D)) tt n!}
  
  --go []       n = {!idEquiv ⊥!}
  --go (E ∷ Es) n = {!⊎-equiv (go2 E n tt) (go Es n)!}

  go2 E n = {!!}


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
bin-3/5 = con (inr (inl (# 1 , _ , (refl , ((con (inr (inr (inr (inr (inl (_ , (# 0 , refl)))))))) , refl)))))

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
      ITrieO-desc (C ∷ D) ϕ if = ITrieO-con C (λ a b x → ϕ tt b (inl x)) if ∷ (ITrieO-desc D (ϕ ∘₃ inr) if)
      
      ITrieO-con {f = f} {g = g} (𝟙 {if = k} j) ϕ if
        = σ _ id (g ∘ fst) (𝟙 (λ { (p , w , _) → ϕ p w refl }) λ p → refl) (λ p → refl)

      ITrieO-con {f = f} {g = g} (ρ {if = k} j h C) ϕ if
        = Δσ (const N) (g ∘ fst) id
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
        = Δσ (const (μ R tt tt)) (g ∘ fst) id
        ( Δσ (const (μ D' tt tt)) (g ∘ fst ∘ fst) id
        ( ∙δ {f'' = VxfO-▷-map (g ∘ fst ∘ fst)
                     (liftM2 (μ (toDesc (TrieO.TrieO-desc D' R (if ∘InfoF iff)))) (λ { ((_ , A) , _) → tt , Vec A k }) !)
                     (liftM2 (μ (toDesc (ITrieO-desc R {!!} (if ∘InfoF iff)))) (λ p → tt , Vec (id (p .fst) .snd) k) (λ x → snd (snd x)))
                     {!!} }
             (λ { ((_ , A) , ((w , r) , _)) → tt , Vec A k }) (snd ∘ snd)
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

UnitD : DescI Number ∅ ⊤
UnitD = 𝟙 {if = 1} _
      ∷ []


