{-# OPTIONS --with-K #-}

module Trees.Nesting where

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
  cons : FDesc → FunD → CDesc → CDesc

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
FVal var      x = Val x
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

NIx : (D : NDesc) → (μ ND → Set) → NTyp D (μ ND) → Set
data Ix : μ ND → Set where
  ix : ∀ {x} → NIx ND Ix x → Ix (con x) 

FIx : (FD : FDesc) → (μ ND → Set) → FTyp FD (μ ND) → Set
FIx var      F x = F x
FIx (num ND) F x = Ix x

FunIx : FunD → Set → Set → Set
FunIx ⊕ = _⊎_
FunIx ⊗ = _×_

CIx : (CD : CDesc) → (μ ND → Set) → CTyp CD (μ ND) → Set
CIx (nil c)        F tt      = Fin c
CIx (cons FD f CD) F (x , y) = FunIx f (FIx FD F x) (CIx CD F y)

NIx (CD ∷ ND) F (inj₁ x) = CIx CD F x
NIx (CD ∷ ND) F (inj₂ y) = NIx ND F y

{- Fin-2 : Ix Nat-2
Fin-2 = ix (inj₁ (ix (inj₁ (ix {!Fin 0!})))) -}

Fin-1/2 : Ix Nat-2
Fin-1/2 = ix (inj₁ (ix (inj₂ zero)))

NTrie : (D : NDesc) → (Set → μ ND → Set) → Set → NTyp D (μ ND) → Set
{-# NO_POSITIVITY_CHECK #-}
-- Q: I don't directly see why not
data Trie {ND : NDesc} (A : Set) : μ ND → Set where
  trie : ∀ {x} → NTrie ND Trie A x → Trie A (con x) 

FTrie : (FD : FDesc) → (Set → μ ND → Set) → Set → FTyp FD (μ ND) → Set
FTrie var      F A x = F A x
FTrie (num ND) F A x = Trie A x

{- FunT : FunD → (Set → Set) → (Set → Set) → Set → Set
FunT ⊕ F G A = F A × G A
FunT ⊗ F G A = F (G A) -}

CTrie : (CD : CDesc) → (Set → μ ND → Set) → Set → CTyp CD (μ ND) → Set
CTrie (nil c)        F A tt      = Vec A c
CTrie (cons FD ⊕ CD) F A (x , y) = FTrie FD F A x × CTrie CD F A y
CTrie (cons FD ⊗ CD) F A (x , y) = FTrie FD F (CTrie CD F A y) x

--FunT f (λ B → FTrie FD F B x) (λ B → CTrie CD F B y) A

NTrie (CD ∷ ND) F A (inj₁ x) = CTrie CD F A x
NTrie (CD ∷ ND) F A (inj₂ y) = NTrie ND F A y

Trie-2 : Trie ℕ Nat-2
Trie-2 = trie (trie (trie [] , zero ∷ []) , zero ∷ [])

-- Q: and now fit nested types into this?
