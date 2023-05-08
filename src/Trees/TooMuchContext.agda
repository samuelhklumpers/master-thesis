module Trees.NestedOrnaments where

--open import Prelude.UseAs
--open import Prelude hiding (⟨_⟩)

open import Data.Product
open import Data.List
open import Data.Sum
open import Data.Unit
open import Data.Bool
open import Data.Empty
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Level renaming (zero to ℓ-zero; suc to ℓ-suc; _⊔_ to ℓ-max)

private variable
  a b c : Level
  X Y Z : Set a
  x y z : X


data Poly a : Set (ℓ-suc a)
data U a : Set (ℓ-suc a) where
  set : (X : Set a)            → U a
  app : (p : Poly a) (u : U a) → U a
  par :                          U a
  
data Poly a where
  Id  : Poly a
  K   : (u : U a)      → Poly a
  _+_ : (l r : Poly a) → Poly a
  _*_ : (l r : Poly a) → Poly a

⟦_⟧ₚ : Poly a → Set a → Set a
⟦_⟧ᵤ : U a → Set a → Set a
⟦ set X   ⟧ᵤ A = X
⟦ app p u ⟧ᵤ A = ⟦ p ⟧ₚ (⟦ u ⟧ᵤ A)
⟦ par     ⟧ᵤ A = A

⟦ Id ⟧ₚ A = A
⟦ K u ⟧ₚ A = ⟦ u ⟧ᵤ A
⟦ p + q ⟧ₚ A = ⟦ p ⟧ₚ A ⊎ ⟦ q ⟧ₚ A
⟦ p * q ⟧ₚ A = ⟦ p ⟧ₚ A × ⟦ q ⟧ₚ A

-- rather than doing full contexts, let's stick to a single parameter
data RDesc (I : Set a) b (Γ : ℕ) : Set (ℓ-suc (ℓ-max a b)) where
  ṿ : (is : List (U b × I)) → RDesc I b 
  σ : (u : U b) (D : ∀ X → ⟦ u ⟧ᵤ X → RDesc I b) → RDesc I b

Desc : Set a → (b : Level) → Set (ℓ-suc (ℓ-max a b))
Desc I b = I → RDesc I b

NatD : Desc ⊤ ℓ-zero
NatD _ = σ (set Bool) λ X → λ
  { false → ṿ []
  ; true  → ṿ [ (par , _) ] }

ListD : Desc ⊤ ℓ-zero
ListD _ = σ (set Bool) λ X → λ
  { false → ṿ []
  ; true  → σ par λ _ _ → ṿ [ (par , _) ] }

PTreeD : Desc ⊤ ℓ-zero
PTreeD _ = σ (set Bool) λ X → λ
  { false → σ par λ _ _ → ṿ []
  ; true  → ṿ [ (app (Id * Id) par , _) ] }


-- data FunD : Set where
--   ⊕ ⊗ : FunD
  
-- data Poly : Set where
--   par : Poly
--   add : (p q : Poly) → Poly
--   mul : (f : FunD) (p q : Poly) → Poly

-- NDesc : Set

-- data FDesc : Set where
--   var : (p : Poly)              → FDesc
--   par : (p : Poly)              → FDesc
--   num : (p : Poly) (nd : NDesc) → FDesc

-- data CDesc : Set where
--   constant  : (c : ℕ)                  → CDesc
--   leaf      : (fd : FDesc)             → CDesc
--   node      : (f : FunD) (l r : CDesc) → CDesc
  
-- NDesc = List CDesc

-- -- While we would usually look at functors Set → Set, we would rather restrict our universe to "just the numbers"
-- data U : Set where
--   top : U
--   bot : U
--   app : (nd : NDesc) (u : U) → U
--   pol : (p : Poly) (u : U) → U -- we pay a bit of duplication to split U → Set and U → U
-- -- so we will also have to look at functors U → U

-- NTyp : NDesc → (U → U) → U → Set
-- data μ (nd : NDesc) (u : U) : Set where
--   con : NTyp nd (app nd) u → μ nd u

-- UTyp : U → Set
-- PTyp : Poly → U → Set

-- UTyp top = ⊤
-- UTyp bot = ⊥
-- UTyp (app nd u) = μ nd u
-- UTyp (pol p u) = PTyp p u

-- PTyp par u = UTyp u
-- PTyp (add p q) u = PTyp p u ⊎ PTyp q u
-- PTyp (mul _ p q) u = PTyp p u × PTyp q u

-- FTyp : FDesc → (U → U) → U → Set
-- FTyp (var p)    X u = UTyp (X (pol p u))
-- FTyp (par p)    X u = PTyp p u
-- FTyp (num p nd) X u = μ nd (pol p u)

-- CTyp : CDesc → (U → U) → U → Set
-- CTyp (constant c) _ _ = ⊤
-- CTyp (leaf fd)    X u = FTyp fd X u
-- CTyp (node _ l r) X u = CTyp l X u × CTyp r X u

-- NTyp []         _ _ = ⊥
-- NTyp (cd ∷ cds) X u = (CTyp cd X u) ⊎ (NTyp cds X u)

-- NatD : NDesc
-- NatD = constant 0 ∷ node ⊕ (constant 1) (leaf (var par)) ∷ []

-- Nat = μ NatD top

-- Nat-2 : Nat
-- Nat-2 = con (inj₂ (inj₁ (_ , con (inj₂ (inj₁ (_ , con (inj₁ _)))))))

-- -- Q: would you still call this a number?
-- DtD : NDesc
-- DtD = node ⊕ (leaf (par par)) (leaf (par par)) ∷ node ⊕ (leaf (par par)) (node ⊕ (leaf (par par)) (leaf (par par))) ∷ node ⊕ (leaf (par par)) (node ⊕ (leaf (par par)) (leaf (par par))) ∷ node ⊕ (leaf (par par)) (node ⊕ (leaf (par par)) (node ⊕ (leaf (par par)) (leaf (par par)))) ∷ node ⊕ (leaf (par par)) (node ⊕ (leaf (par par)) (node ⊕ (leaf (par par)) (node ⊕ (leaf (par par)) (leaf (par par))))) ∷ node ⊕ (leaf (par par)) (node ⊕ (leaf (par par)) (node ⊕ (leaf (par par)) (node ⊕ (leaf (par par)) (leaf (par par))))) ∷ node ⊕ (leaf (par par)) (node ⊕ (leaf (par par)) (node ⊕ (leaf (par par)) (node ⊕ (leaf (par par)) (node ⊕ (leaf (par par)) (leaf (par par)))))) ∷ []

-- NodeD : Poly
-- NodeD = add (mul ⊕ par par) (mul ⊕ par (mul ⊕ par par))

-- FtD : NDesc
-- FtD = constant 0 ∷ leaf (par par)  ∷ node ⊕ (leaf (num par DtD)) (leaf (var NodeD)) ∷ []

-- Ft = μ FtD top

-- {-
-- F-23 : Ft
-- F-23 = con (inj₂ (inj₂ (inj₁ (con (inj₂ (inj₂ (inj₂ (inj₂ (inj₁ _))))) , con (inj₂ (inj₂ (inj₁ (con {!help!} , con (inj₁ _)))))))))
-- -}

-- F-4 : Ft
-- F-4 = con (inj₂ (inj₂ (inj₁ (con (inj₁ _) , con (inj₂ (inj₁ (inj₁ _)))))))


-- private variable
--   nd : NDesc
--   cd : CDesc
--   fd : FDesc
--   u  : U

-- NVal : (nd' : NDesc) → NTyp nd' (app nd) u → ℕ
-- Val : μ nd u → ℕ
-- Val (con x) = NVal _ x

-- FunV : FunD → ℕ → ℕ → ℕ
-- FunV ⊕ = _+_
-- FunV ⊗ = _*_

-- PVal : (u : U) (p : Poly) → PTyp p u → ℕ
-- UVal : (u : U)    → UTyp u   → ℕ

-- PVal u par         x        = UVal u x
-- PVal u (add p q)   (inj₁ x) = PVal u p x
-- PVal u (add p q)   (inj₂ y) = PVal u q y
-- PVal u (mul f p q) (x , y)  = FunV f (PVal u p x) (PVal u q y)

-- UVal top _ = 1
-- UVal (app nd u) x = Val x
-- UVal (pol p u) x = PVal u p x

-- FVal : (fd : FDesc) → FTyp fd (app nd) u → ℕ
-- FVal (var p)    x = Val x
-- FVal (par p)    x = PVal _ p x
-- FVal (num p nd) x = Val x

-- CVal : (cd : CDesc) → CTyp cd (app nd) u → ℕ
-- CVal (constant c) x = c
-- CVal (leaf fd)    x = FVal fd x
-- CVal (node f l r) (x , y) = FunV f (CVal l x) (CVal r y)

-- NVal (cd ∷ cds) (inj₁ x) = CVal cd x
-- NVal (cd ∷ cds) (inj₂ y) = NVal cds y

-- 2≡2 : Val Nat-2 ≡ 2
-- 2≡2 = refl

-- 4≡4 : Val F-4 ≡ 4
-- 4≡4 = refl

-- NIx : ∀ u → (nd' : NDesc) → NTyp nd' (app nd) u → Set
-- data Ix : μ nd u → Set where
--   ix : ∀ {u x} → NIx u nd x → Ix (con x) 

-- UIx : (u : U) → UTyp u → Set
-- PIx : (p : Poly) → PTyp p u → Set

-- UIx top        _ = ⊤
-- UIx (app nd u) x = Ix x
-- UIx (pol p u)  x = PIx p x

-- FunIx : FunD → Set → Set → Set
-- FunIx ⊕ = _⊎_
-- FunIx ⊗ = _×_

-- PIx {u = u} par x = UIx u x
-- PIx (add p q) (inj₁ x) = PIx p x
-- PIx (add p q) (inj₂ y) = PIx q y
-- PIx (mul f p q) (x , y) = FunIx f (PIx p x) (PIx q y)

-- FIx : (fd : FDesc) → FTyp fd (app nd) u → Set
-- FIx (var p) x = Ix x
-- FIx (par p) x = PIx p x
-- FIx (num p nd) x = Ix x

-- CIx : (cd : CDesc) → CTyp cd (app nd) u → Set
-- CIx (constant c) tt      = Fin c
-- CIx (leaf fd)    x       = FIx fd x
-- CIx (node f l r) (x , y) = FunIx f (CIx l x) (CIx r y)

-- NIx u (cd ∷ cds) (inj₁ x) = CIx cd x
-- NIx u (cd ∷ cds) (inj₂ y) = NIx u cds y

-- {- Fin-2 : Ix Nat-2
-- Fin-2 = ix (inj₂ (ix (inj₂ (ix {!Fin 0!})))) -}

-- Fin-1/2 : Ix Nat-2
-- Fin-1/2 = ix (inj₂ (ix (inj₁ zero)))

-- FFin-2/4 : Ix F-4
-- FFin-2/4 = ix (inj₂ (ix (inj₁ tt)))

-- -- \o/ finger trees are numerical representations after all

-- FT : Ft → Set → Set
-- FT x A = Ix x → A

-- sucFt : Ft → Ft
-- sucFt (con (inj₁ tt)) = con (inj₂ (inj₁ tt))
-- sucFt (con (inj₂ (inj₁ tt))) = con (inj₂ (inj₂ (inj₁ (con (inj₁ (tt , tt)) , con (inj₁ tt)))))
-- sucFt (con (inj₂ (inj₂ (inj₁ (x , m))))) = {!!}

-- cons : ∀ {n} {A : Set} → A → FT n A → FT (sucFt n) A
-- cons x xs = {!!}


-- -- NTrie : (D : NDesc) → Set → NTyp D (μ ND) → Set

-- -- data Trie {ND : NDesc} (A : Set) : μ ND → Set where
-- --   trie : ∀ {x} → NTrie ND A x → Trie A (con x)

-- -- FTrie : (FD : FDesc) → Set → FTyp FD (μ ND) → Set
-- -- FTrie var      A x = Trie A x
-- -- FTrie (num ND) A x = Trie A x

-- -- CTrie : (CD : CDesc) → Set → CTyp CD (μ ND) → Set
-- -- CTrie (nil c)        A tt      = Vec A c
-- -- CTrie (cons FD ⊕ CD) A (x , y) = FTrie FD A x × CTrie CD A y
-- -- CTrie (cons FD ⊗ CD) A (x , y) = FTrie FD (CTrie CD A y) x

-- -- NTrie (CD ∷ ND) A (inj₁ x) = CTrie CD A x
-- -- NTrie (CD ∷ ND) A (inj₂ y) = NTrie ND A y

-- -- Trie-2 : Trie ℕ Nat-2
-- -- Trie-2 = trie (trie (trie [] , zero ∷ []) , zero ∷ [])
