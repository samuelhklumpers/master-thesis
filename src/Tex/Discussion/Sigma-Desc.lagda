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

_L+_ : List (ConI Me Γ J ∅) → DescI Me Γ J → DescI Me Γ J
[]        L+ D = D
(C ∷ Cs)  L+ D = C ∷ (Cs L+ D)

PathD : (D : DescI Number ∅ ⊤) → Desc ∅ (μ D tt tt)
PathD′ : (D : DescI Me ∅ ⊤) (me : MetaF Me Number) → Desc ∅ (μ D tt tt)

PathD E = PathD′ E id-MetaF
PathD′ E me = PathDD E me λ a b → con
  module PathD where
    N : _
    N = μ E tt tt

    PathDD : (D : DescI Me ∅ ⊤) (me : MetaF Me Number) → (⟦ D ⟧ (λ _ _ → N) ⇶ λ _ _ → N) → Desc ∅ (μ E tt tt)
    PathDC : (C : ConI Me ∅ ⊤ V) (me : MetaF Me Number) (f : Vxf ∅ W V) → (∀ b → ⟦ C ⟧ (λ _ _ → N) (tt , f b) _ → N) → List (Con ∅ (μ E tt tt) W)

    PathDD []      me ϕ = []
    PathDD (C ∷ D) me ϕ = PathDC C me id (λ _ c → ϕ _ _ (inl c)) L+ PathDD D me λ p i → ϕ p i ∘ inr

    PathDC (𝟙 {me = k} j) me f ϕ
      = σ- (λ _ → (Fin (me .𝟙f k))) (𝟙 (λ { (_ , w) → ϕ w refl }))
      ∷ []

    -- looks scary, pretty regular to write down though
    PathDC (ρ {me = k} j g C) me f ϕ
      = σ- (λ _ → (Fin (me .ρf k))) (σ+ (λ _ → N) (σ+ (λ { (p , w , _) → ⟦ C ⟧ (λ _ _ → N) (p , f w) tt }) (ρ0 (snd ∘ fst ∘ snd) (𝟙 λ { (_ , (w , n) , c) → ϕ w (n , c) }))))
      ∷ L.map (σ+ (λ _ → N)) (PathDC C me (f ∘ fst) (λ { (w , n) c → ϕ w (n , c) }))

    PathDC (σ S {me = k} h C)     me f ϕ
      = σ+ (λ { (p , w) → S (p , f w) }) (σ+ (λ { (p , w , s) → ⟦ C ⟧ (λ _ _ → N) (p , h (f w , s)) tt }) (σ- (λ { (p , (w , s) , c) → Fin (me .σf _ k (p , f w) s) }) (𝟙 λ { (p , (w , s) , c) → ϕ w (s , c) })))
      ∷ L.map (σ+ λ { (p , w) → S (p , f w) }) (PathDC C me (h ∘ Vxf-▷ f S) λ { (w , s) c → ϕ w (s , c) })

    PathDC (δ {Me′ = Me′} {me = k} {iff = iff} j g R h C) me f ϕ with me .δf _ _ k
    ... | refl , refl , k
      = σ- (λ _ → (Fin k)) (σ+ (λ _ → (μ R tt tt)) (σ+ (λ { (p , w , r) → ⟦ C ⟧ (λ _ _ → N) (p , h (f w , r)) tt }) (δ- (snd ∘ fst ∘ snd) ! (PathD′ R (me ∘MetaF iff)) (𝟙 λ { (p , (w , r) , c) → ϕ w (r , c) }))))
      ∷ L.map (δ+ ! ! R) (PathDC C me (λ { (w , r) → h (f w , r) }) λ { (w , r) c → ϕ w (r , c) })

unμ : {D : DescI Me Γ J} → ∀ {p i} → μ D p i ≃ ⟦ D ⟧ (μ D) p i
unμ .fst (con x) = x
unμ .snd .equiv-proof y .fst = con y , λ i → y
unμ .snd .equiv-proof y .snd (con x , p) = ΣPathP ((λ i → con (p (~ i))) , λ j i → p (~ j ∨ i))

PathD-correct : ∀ D n → μ (PathD D) tt n ≃ Fin (value n)
PathD-correct D n = compEquiv unμ {!compEquiv (go D id-MetaF n) {!!}!}
  where
  open PathD D

  go :  (E : DescI Me ∅ ⊤) (me : MetaF Me Number)
        (c : ⟦ E ⟧ (λ _ _ → N id-MetaF) ⇶ (λ _ _ → N id-MetaF))
     →  ∀ n → ⟦ PathDD id-MetaF E me c ⟧ (μ (PathD D)) tt n ≃ ⟦ PathDD id-MetaF E me c ⟧ (λ _ n → Fin (value n)) tt n
     
  go2 : (E : ConI Me ∅ ⊤ V) (me : MetaF Me Number) → ∀ n v → ⟦ {!PathDC!} ⟧ (μ (PathD D)) (tt , v) n ≃ ⟦ {!!} ⟧ (λ _ n → Fin (value n)) (tt , v) n

  go []       _  _ _ = idEquiv ⊥
  go (E ∷ Es) me c n = {!⟦ PathDD id-MetaF (E ∷ Es) me c ⟧ (μ (PathD D)) tt n!}
  
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

ITrieO : (D : DescI Number ∅ ⊤) → OrnDesc Plain (∅ ▷ λ _ → Type) id (μ D tt tt) ! (toDesc (TrieO D))
ITrieO D = ITrieO′ D D id-MetaF
  module ITrieO where
    module _ (D' : DescI Number ∅ ⊤) where
      ITrieO′ : (D : DescI Me ∅ ⊤) (me : MetaF Me Number) → OrnDesc Plain (∅ ▷ λ _ → Type) id (μ D' tt tt) ! (toDesc (TrieO.TrieO-desc D' D me))
      
      N : _
      N = μ D' tt tt

      ITrieO-desc : (D : DescI Me ∅ ⊤) → (⟦ D ⟧ (λ _ _ → N) ⇶ λ _ _ → N) → (me : MetaF Me Number) → OrnDesc Plain (∅ ▷ λ _ → Type) id (μ D' tt tt) ! (toDesc (TrieO.TrieO-desc D' D me))

      ITrieO-con  : ∀ {U V} {W : ExTel (∅ ▷ λ _ → Type)} {f : Vxf ! U V} {g : Vxf id W U}
                 (C : ConI Me ∅ ⊤ V) → (∀ a b → ⟦ C ⟧ (λ _ _ → N) (tt , f (g {p = a} b)) _ → N) → (me : MetaF Me Number)
                 → ConOrnDesc Plain {W = W} {K = μ D' tt tt} g ! (toCon {f = f} (TrieO.TrieO-con D' C me))

      ITrieO-desc []      ϕ me = []
      ITrieO-desc (C ∷ D) ϕ me = ITrieO-con C (λ a b x → ϕ tt b (inl x)) me ∷ (ITrieO-desc D (ϕ ∘₃ inr) me)
      
      ITrieO-con {f = f} {g = g} (𝟙 {me = k} j) ϕ me
        = σ _ id (g ∘ fst) (𝟙 (λ { (p , w , _) → ϕ p w refl }) λ p → refl) (λ p → refl)

      ITrieO-con {f = f} {g = g} (ρ {me = k} j h C) ϕ me
        = Δσ (λ _ → N) (g ∘ fst) id
        ( ρ (λ (p , w , n) → n) (λ { (_ , A) → _ , Vec A (me .ρf k) })
          (ITrieO-con C (λ { a (u , n) x → ϕ a u (n , x) }) me)
        (λ p → refl) (λ p → refl)) (λ p → refl)
        
      ITrieO-con {f = f} {g = g} (σ S {me = k} h C)      ϕ me
        = σ _ id (Vxf-▷ g (S ∘ over f))
        ( σ _ id (Vxf-▷ (Vxf-▷ g (S ∘ over f)) (λ { ((_ , A) , _ , s) → Vec A (me .σf _ k _ s) }))
          (ITrieO-con C (λ { a ((w , s) , _) x → ϕ a w (s , x) }) me)
        λ p → refl) λ p → refl
        
      ITrieO-con {f = f} {g = g} (δ {me = k} {iff = iff} j g' R h C) ϕ me with me .δf _ _ k
      ... | refl , refl , k
        = Δσ (λ _ → (μ R tt tt)) (g ∘ fst) id
        ( Δσ (λ _ → (μ D' tt tt)) (g ∘ fst ∘ fst) id
        ( ∙δ {f'' = Vxf-▷-map (g ∘ fst ∘ fst)
                     (liftM2 (μ (toDesc (TrieO.TrieO-desc D' R (me ∘MetaF iff)))) (λ { ((_ , A) , _) → tt , Vec A k }) !)
                     (liftM2 (μ (toDesc (ITrieO-desc R {!!} (me ∘MetaF iff)))) (λ p → tt , Vec (id (p .fst) .snd) k) (λ x → snd (snd x)))
                     {!!} }
             (λ { ((_ , A) , ((w , r) , _)) → tt , Vec A k }) (snd ∘ snd)
          (ITrieO-con C {!λ { a (((w , r) , n) , _)  x → ϕ a w (r , {!!}) }!} me)
          {!ITrieO R!} id
        (λ _ _ → refl) (λ _ _ → refl) λ p → refl) λ p → refl) λ p → refl
    
      ITrieO′ D me = ITrieO-desc D {!!} me


--(liftM2 (μ (toDesc (TrieO.TrieO-desc D' R (me ∘MetaF iff)))) (λ { ((_ , A) , _) → tt , Vec A k }) !)
--ITrieO-desc R (λ { a b x → ϕ {!!} {!!} {!!} }) (me ∘MetaF iff)

-- to prove: size x ≡ shape x
-- * μ D is likely to be Traversable when all σ's in it are
-- * as every S in a DescI Number ∅ ⊤ is necessarily invariant, it is also trivially Traversable

-- to prove: every OrnDesc induces an ornamental algebra -> doesn't work
-- to prove: for some appropriate Ix : (D : DescI Number ∅ ⊤) → Desc ∅ (μ D tt tt),
--           Ix D is also initial for the algebra of the algebraic ornament induced by the ornamental algebra (yes)

-- to summarize, for every number system, there is an appropriate "list", which has an appropriate "vector"
-- this vector is representable, the list is traversable, and everything still satisfies size ≡ shape ≡ index

UnitD : DescI Number ∅ ⊤
UnitD = 𝟙 {me = 1} _
      ∷ []


