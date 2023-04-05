module Twosided where

open import Cubical.Data.Nat
open import Cubical.Data.List
open import Cubical.Data.Vec
open import Ext.ProgOrn.Ornaments hiding (_⋈_)
open import Cubical.Data.Unit renaming (Unit to ⊤)
open import Prelude hiding (⌊_⌋; _◁_; _▷_)

{-
let's start from

data FingerTree a = Empty
                  | Single a
                  | Deep (Digit a) (FingerTree (Node a)) (Digit a)

data Digit a = One a | Two a a | Three a a a | Four a a a a
data Node a = Node2 a a | Node3 a a a

note that Node is problematic, so we let

data Node a = Node3 a a

simplifying

FingerTree ⊤ = Empty | Single | Deep Digit (FingerTree (⊤ × ⊤ × ⊤)) Digit
-}


data Digit : Type where
  d1 d2 d3 d4 : Digit

data FTag : Type where
  f1 f2 f3 : FTag

FNumD : Desc ⊤
FNumD tt = σ FTag λ
  { f1 → ṿ []
  ; f2 → ṿ []
  ; f3 → Digit σ′ Digit σ′ ṿ [ tt ] }

FNum = μ FNumD tt

Dtoℕ : Digit → ℕ
Dtoℕ d1 = 1
Dtoℕ d2 = 2
Dtoℕ d3 = 3
Dtoℕ d4 = 4

toℕ : FNum → ℕ
toℕ (con (f1 , _))             = 0
toℕ (con (f2 , _))             = 1
toℕ (con (f3 , n , m , x , _)) = Dtoℕ n + 3 · toℕ x + Dtoℕ m

sucl : FNum → FNum
sucl (con (f1 , _))             = con (f2 , _)
sucl (con (f2 , _))             = con (f3 , d1 , d1 , con (f1 , _) , _)
sucl (con (f3 , d1 , m , x , _)) = con (f3 , d2 , m , x , _)
sucl (con (f3 , d2 , m , x , _)) = con (f3 , d3 , m , x , _)
sucl (con (f3 , d3 , m , x , _)) = con (f3 , d4 , m , x , _)
sucl (con (f3 , d4 , m , x , _)) = con (f3 , d1 , m , sucl x , _)

sucr : FNum → FNum
sucr (con (f1 , _))             = con (f2 , _)
sucr (con (f2 , _))             = con (f3 , d1 , d1 , con (f1 , _) , _)
sucr (con (f3 , n , d1 , x , _)) = con (f3 , n , d2 , x , _)
sucr (con (f3 , n , d2 , x , _)) = con (f3 , n , d3 , x , _)
sucr (con (f3 , n , d3 , x , _)) = con (f3 , n , d4 , x , _)
sucr (con (f3 , n , d4 , x , _)) = con (f3 , n , d2 , sucr x , _)

power : ℕ → (A → A) → A → A
power ℕ.zero    f = λ x → x
power (ℕ.suc n) f = f ∘ power n f

Vec′ : ℕ → Type → Type
Vec′ n A = Vec A n

FTreeOD : Type → OrnDesc ℕ ! FNumD
FTreeOD A (ok n) = σ FTag λ
  { f1 → ṿ _
  ; f2 → Δ[ _ ∈ power n (Vec′ 3) A ] ṿ _
  ; f3 → σ[ l ∈ Digit ] σ[ r ∈ Digit ] 
         Δ[ _ ∈ Vec (power n (Vec′ 3) A) (Dtoℕ l) ]
         Δ[ _ ∈ Vec (power n (Vec′ 3) A) (Dtoℕ r) ]
         ṿ (ok (suc n) , _) }

FTree′ : Type → ℕ → Type
FTree′ A = μ ⌊ FTreeOD A ⌋

FTree : Type → Type
FTree A = FTree′ A 0

private variable
  n m : ℕ

_◁_ : power n (Vec′ 3) A → FTree′ A n → FTree′ A n 
x ◁ con (f1 , _)     = con (f2 , x , _)
x ◁ con (f2 , y , _) = con (f3 , d1 , d1 , x ∷ [] , y ∷ [] , con (f1 , _) , _)
x ◁ con (f3 , d1 , r , ls , rs , m , _) = con (f3 , d2 , r , x ∷ ls , rs , m , _)
x ◁ con (f3 , d2 , r , ls , rs , m , _) = con (f3 , d3 , r , x ∷ ls , rs , m , _)
x ◁ con (f3 , d3 , r , ls , rs , m , _) = con (f3 , d4 , r , x ∷ ls , rs , m , _)
x ◁ con (f3 , d4 , r , l ∷ ls , rs , m , _) = con (f3 , d2 , r , x ∷ l ∷ [] , rs , (ls ◁ m) , _)

_◁′_ : Vec (power n (Vec′ 3) A) m → FTree′ A n → FTree′ A n 
[] ◁′ r = r
(x ∷ xs) ◁′ r = xs ◁′ (x ◁ r)

_▷_ : FTree′ A n → power n (Vec′ 3) A → FTree′ A n
con (f1 , _) ▷ x = con (f2 , x , _)
con (f2 , y , _) ▷ x = con (f3 , d1 , d1 , y ∷ [] , x ∷ [] , con (f1 , _) , _)
con (f3 , l , d1 , ls , rs , m , _) ▷ x = con (f3 , l , d2 , ls , x ∷ rs , m , _)
con (f3 , l , d2 , ls , rs , m , _) ▷ x = con (f3 , l , d3 , ls , x ∷ rs , m , _)
con (f3 , l , d3 , ls , rs , m , _) ▷ x = con (f3 , l , d4 , ls , x ∷ rs , m , _)
con (f3 , l , d4 , ls , r ∷ rs , m , _) ▷ x = con (f3 , l , d2 , ls , x ∷ r ∷ [] , (m ▷ rs) , _)

_▷′_ : FTree′ A n → Vec (power n (Vec′ 3) A) m → FTree′ A n
l ▷′ [] = l
l ▷′ (x ∷ xs) = (l ▷ x) ▷′ xs

-- Fingertrees: annotate the tree with its sizes -> basically cheating by storing the indexing structure in our case
-- gives lookup in log-time


{-
-- unfortunate
{-# TERMINATING #-}
joinTree : FTree′ A n → List (power n (Vec′ 3) A) → FTree′ A n → FTree′ A n
joinTree (con (f1 , _)) [] r = r
joinTree (con (f1 , _)) (x ∷ xs) r = joinTree (con (f1 , _)) xs (x ◁ r) 
joinTree (con (f2 , x , _)) xs r = x ◁ joinTree (con (f1 , _)) xs r
joinTree l@(con (f3 , ls)) xs (con (f2 , x , _)) = joinTree l xs (con (f1 , _)) ▷ x
joinTree (con (f3 , ll , lr , lls , llrs , lm , _)) xs (con (f3 , rl , rr , rls , rrs , rm , _)) = con (f3 , ll , rr , lls , rrs , joinTree lm {!oh no!!} rm , _)
joinTree l@(con (f3 , ls)) [] (con (f1 , _)) = l
joinTree l@(con (f3 , ls)) (x ∷ xs) (con (f1 , _)) = joinTree (l ▷ x) xs (con (f1 , _))
-}

_⋈_ : FTree′ A n → FTree′ A n → FTree′ A n
con (f1 , _) ⋈ ys = ys
con (f2 , x , _) ⋈ ys = x ◁ ys
con xs@(f3 , xl , xr , xls , xrs , xm , _) ⋈ con (f1 , _) = con xs
con xs@(f3 , xl , xr , xls , xrs , xm , _) ⋈ con (f2 , y , _) = con xs ▷ y
-- hard case..., need some divmod-like stuff to shuffle things to work
con xs@(f3 , xl , xr , xls , xrs , xm , _) ⋈ con (f3 , yl , yr , yls , yrs , ym , _) = con (f3 , xl , yr , xls , yrs , {!(xm ▷′ xrs) ⋈ (yls ◁′ ym)!} , _)
-- but then it would still perform linearly :(
