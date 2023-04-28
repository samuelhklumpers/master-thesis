{-# OPTIONS --with-K #-}

module Trees.Trieify where

--open import Prelude.UseAs
--open import Prelude hiding (⟨_⟩)

open import Data.Product
open import Data.List
open import Data.Vec
open import Data.Sum
open import Data.Unit
open import Data.Empty
open import Data.Fin using (Fin; zero; suc)
open import Data.Nat
open import Relation.Binary.PropositionalEquality hiding ([_])


NDesc : Set

data FDesc : Set where
  var : FDesc
  num : NDesc → FDesc

data FunD : Set where
  ⊕ ⊗ : FunD

data CDesc : Set where
  nil  : ℕ → CDesc
  cons : FDesc → FunD → CDesc → CDesc -- regrettably not a very good choice and does not support all sensible representations (at least, not without needlessly convoluted constructions), but also not too hard or interesting to fix

NDesc = List CDesc

NTyp : NDesc → Set → Set
data μ (ND : NDesc) : Set where
  con : NTyp ND (μ ND) → μ ND 

FTyp : FDesc → Set → Set
FTyp var      X = X
FTyp (num ND) _ = μ ND

CTyp : CDesc → Set → Set
CTyp (nil _)        _ = ⊤
CTyp (cons FD _ CD) X = FTyp FD X × CTyp CD X

NTyp []        X = ⊥
NTyp (CD ∷ ND) X = CTyp CD X ⊎ NTyp ND X

NatD : NDesc
NatD = (nil 0) ∷ ((cons var ⊕ (nil 1)) ∷ [])

Nat = μ NatD

Nat-2 : Nat
Nat-2 = con (inj₂ (inj₁ (con (inj₂ (inj₁ (con (inj₁ _) , _))) , _)))

private variable
  ND : NDesc
  CD : CDesc
  FD : FDesc

NVal : (D : NDesc) → NTyp D (μ ND) → ℕ
Val : μ ND → ℕ
Val (con x) = NVal _ x

FVal : (FD : FDesc) → FTyp FD (μ ND) → ℕ
FVal var      x = Val x -- yes replacing var with _ here does not work
FVal (num ND) x = Val x

FunV : FunD → ℕ → ℕ → ℕ
FunV ⊕ = _+_
FunV ⊗ = _*_

CVal : (CD : CDesc) → CTyp CD (μ ND) → ℕ
CVal (nil c)        tt      = c
CVal (cons FD f CD) (x , y) = FunV f (FVal FD x) (CVal CD y)

NVal (CD ∷ ND) (inj₁ x) = CVal CD x
NVal (CD ∷ ND) (inj₂ y) = NVal ND y

2≡2 : Val Nat-2 ≡ 2
2≡2 = refl

NIx : (D : NDesc) → NTyp D (μ ND) → Set
data Ix : μ ND → Set where
  ix : ∀ {x} → NIx ND x → Ix (con x) 

FIx : (FD : FDesc) → FTyp FD (μ ND) → Set
FIx var      x = Ix x
FIx (num ND) x = Ix x

FunIx : FunD → Set → Set → Set
FunIx ⊕ = _⊎_
FunIx ⊗ = _×_

CIx : (CD : CDesc) → CTyp CD (μ ND) → Set
CIx (nil c)        tt      = Fin c
CIx (cons FD f CD) (x , y) = FunIx f (FIx FD x) (CIx CD y)

NIx (CD ∷ ND) (inj₁ x) = CIx CD x
NIx (CD ∷ ND) (inj₂ y) = NIx ND y

{- Fin-2 : Ix Nat-2
Fin-2 = ix (inj₁ (ix (inj₁ (ix {!Fin 0!})))) -}

Fin-1/2 : Ix Nat-2
Fin-1/2 = ix (inj₁ (ix (inj₂ zero)))


NTrie : (D : NDesc) → Set → NTyp D (μ ND) → Set

data Trie {ND : NDesc} (A : Set) : μ ND → Set where
  trie : ∀ {x} → NTrie ND A x → Trie A (con x)

FTrie : (FD : FDesc) → Set → FTyp FD (μ ND) → Set
FTrie var      A x = Trie A x
FTrie (num ND) A x = Trie A x

CTrie : (CD : CDesc) → Set → CTyp CD (μ ND) → Set
CTrie (nil c)        A tt      = Vec A c
CTrie (cons FD ⊕ CD) A (x , y) = FTrie FD A x × CTrie CD A y
CTrie (cons FD ⊗ CD) A (x , y) = FTrie FD (CTrie CD A y) x

NTrie (CD ∷ ND) A (inj₁ x) = CTrie CD A x
NTrie (CD ∷ ND) A (inj₂ y) = NTrie ND A y

Trie-2 : Trie ℕ Nat-2
Trie-2 = trie (trie (trie [] , zero ∷ []) , zero ∷ [])


module FingerTrees where
  -- Q: do finger trees fit into this?
  -- necessarily, if they did, then we would have an ND such that μ ND ≃ FingerTree ⊤

  DtD : NDesc
  DtD = nil 2 ∷ nil 3 ∷ nil 3 ∷ nil 4 ∷ nil 5 ∷ nil 5 ∷ nil 6 ∷ []

  {-
  FtD : NDesc
  FtD = nil 0 ∷ nil 1 ∷ cons (num DtD) ⊕ {!this should be FtD but replacing DtD with Node DtD!} ∷ []
  -}

  NodeD : NDesc → NDesc
  NodeD ND = cons (num ND) ⊕ (cons (num ND) ⊕ (nil 0)) ∷ cons (num ND) ⊕ (cons (num ND) ⊕ (cons (num ND) ⊕ (nil 0))) ∷ []

  {-
  FtD : NDesc → NDesc
  FtD ND = nil 0 ∷ nil 1 ∷ cons (num ND) ⊕ {!ok, but var would keep ND, while num (FtD (NodeD ND)) obviously does not terminate!} ∷ []
  -}

  -- Let's extend NDesc to allow nesting!
  
