module Ornament.Number where

open import Data.Product
open import Data.Sum
open import Data.Unit
open import Data.Empty
open import Function.Base
open import Data.Fin using (Fin; zero; suc)
open import Data.Nat
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Level 

infixr 10 _∷_

data Sum : Set
data NDesc : Set where
  []  : NDesc
  _∷_ : Sum → NDesc → NDesc

data Factor : Set where
  par : Factor
  num : NDesc → Factor
  rec : NDesc → Factor

data Product : Set where
  *n   : ℕ → Product
  _*∷_ : Factor → Product → Product
  
data Sum where
  +n   : ℕ → Sum
  _+∷_ : Product → Sum → Sum

Id : NDesc
Id = ((par *∷ (*n 1)) +∷ (+n 0)) ∷ []


open import Ornament.DescL

Fun : NDesc → Desc ⊤ (∅ ▷ const Set) ℓ-zero
Fun' : Sum → Con ⊤ (∅ ▷ const Set) ℓ-zero
Fun' (+n _) = 𝟙 _
Fun' (*n _ +∷ xs) = Fun' xs
Fun' ((par *∷ ys) +∷ xs)   = σf′ proj₂ (Fun' (ys +∷ xs))
Fun' ((num x *∷ ys) +∷ xs) = σd′ (const tt) id (Fun x) (Fun' (ys +∷ xs))
Fun' ((rec x *∷ ys) +∷ xs) = rec (const tt) (λ { (_ , A) → (_ , μ (Fun x) (_ , A) _) }) (Fun' (ys +∷ xs))

Fun []       = []
Fun (x ∷ xs) = Fun' x ∷ (Fun xs)

-- unsurprising
{-# TERMINATING #-}
eval2 : ∀ {A} (d : NDesc) → (μ (Fun d)) (_ , A) _ → (A → ℕ) → ℕ
eval : ∀ {A} (d : NDesc) {d'} → ⟦ Fun d ⟧Desc (μ (Fun d')) (_ , A) _ → (A → ℕ) → ℕ
eval2 d (con x) = eval d x

eval' : ∀ {A} (s : Sum) {d'} → ⟦ Fun' s ⟧Con-ℓ ℓ-zero (μ (Fun d')) (_ , A) _ → (A → ℕ) → ℕ → ℕ

eval (s ∷ d) (inj₁ x) f = eval' s x f 1
eval (s ∷ d) (inj₂ y) f = eval d y f

eval' (+n n) (lift refl) f _ = n
eval' (*n n     +∷ s) x f m = m * n + eval' s x f 1
eval' ((par *∷ p) +∷ s) (a , x) f m = eval' (p +∷ s) x f (f a * m)  
eval' ((num d *∷ p) +∷ s) (y , x) f m = eval' (p +∷ s) x f (eval2 d y f)
eval' ((rec d *∷ p) +∷ s) (r , x) f m = eval' (p +∷ s) x f (eval2 _ r λ z → eval2 _ z f)

open import Ornament.OrnL

Trie' : ∀ (s : Sum) {nd'} → ConOrnDesc {J = μ (Fun nd') (_ , ⊤) _} {Δ = ∅ ▷ (const Set)} (const tt) id (Fun' s) ℓ-zero

Trie : ∀ (nd : NDesc) {nd'} → OrnDesc {Δ = ∅ ▷ (const Set)} {J = μ (Fun nd') (_ , ⊤) _} (const tt) id (Fun nd) ℓ-zero
Trie []      = []
Trie (s ∷ d) = Trie' s ∷ Trie d

Trie' (+n n) = {!!}
Trie' (*n n +∷ s) = {!!}
Trie' ((par *∷ p) +∷ s) = {!!}
Trie' ((num d *∷ p) +∷ s) = {!!}
Trie' ((rec d *∷ p) +∷ s) = {!!}


-- NIx : ∀ u → (nd' : NDesc) → NTyp nd' (app nd) u → Set
-- data Ix : μ nd u → Set where
--   ix : ∀ {u x} → NIx u nd x → Ix (con x) 

-- UIx : (u : U) → UTyp u → Set
-- PIx : (p : Poly) → PTyp p u → Set

-- UIx top        _ = ⊤
-- UIx (app nd u) x = Ix x
-- UIx (pol p u)  x = PIx p x

-- FunIx : Op → Set → Set → Set
-- FunIx ⊕ = _⊎_
-- FunIx ⊗ = _×_

-- PIx {u = u} var x = UIx u x
-- PIx (add p q) (inj₁ x) = PIx p x
-- PIx (add p q) (inj₂ y) = PIx q y
-- PIx (mul f p q) (x , y) = FunIx f (PIx p x) (PIx q y)

-- FIx : (fd : FDesc) → FTyp fd (app nd) u → Set
-- FIx (rec p) x = Ix x
-- FIx (var p) x = PIx p x
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
-- -- FTrie rec      A x = Trie A x
-- -- FTrie (num ND) A x = Trie A x

-- -- CTrie : (CD : CDesc) → Set → CTyp CD (μ ND) → Set
-- -- CTrie (nil c)        A tt      = Vec A c
-- -- CTrie (cons FD ⊕ CD) A (x , y) = FTrie FD A x × CTrie CD A y
-- -- CTrie (cons FD ⊗ CD) A (x , y) = FTrie FD (CTrie CD A y) x

-- -- NTrie (CD ∷ ND) A (inj₁ x) = CTrie CD A x
-- -- NTrie (CD ∷ ND) A (inj₂ y) = NTrie ND A y

-- -- Trie-2 : Trie ℕ Nat-2
-- -- Trie-2 = trie (trie (trie [] , zero ∷ []) , zero ∷ [])
