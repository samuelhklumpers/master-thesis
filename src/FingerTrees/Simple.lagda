\begin{code}
{-# OPTIONS --with-K #-}

module FingerTrees.Simple where


module Bad where
\end{code}

%<*bin-bad>
\begin{code}

  data Digit : Set where
    𝟙 𝟚 : Digit

  data Bin : Set where
    𝟘 𝟙   : Bin
    _⟨_⟩_ : Digit → Bin → Digit → Bin
\end{code}
%</bin-bad>

\begin{code}
  suc : Bin → Bin
  suc 𝟘 = 𝟙
  suc 𝟙 = 𝟙 ⟨ 𝟘 ⟩ 𝟙 
  suc (𝟙 ⟨ m ⟩ r) = 𝟚 ⟨ m ⟩ r
  suc (𝟚 ⟨ m ⟩ r) = 𝟙 ⟨ suc m ⟩ r

\end{code}

%<*bad-1>
\begin{code}
  bad-1 : Bin
  bad-1 = 𝟚 ⟨ 𝟚 ⟨ 𝟚 ⟨ 𝟙 ⟩ 𝟙 ⟩ 𝟙 ⟩ 𝟙
\end{code}
%</bad-1>

\begin{code}

\end{code}

%<*bad-2>
\begin{code}
  bad-2 : Bin
  bad-2 = 𝟙 ⟨ 𝟙 ⟨ 𝟙 ⟨ 𝟙 ⟨ 𝟘 ⟩ 𝟙 ⟩ 𝟙 ⟩ 𝟙 ⟩ 𝟙
\end{code}
%</bad-2>

\begin{code}


\end{code}

%<*bin-good>
\begin{code}
data Digit : Set where
  𝟙 𝟚 𝟛 : Digit

data Bin : Set where
  𝟘 𝟙   : Bin
  _⟨_⟩_ : Digit → Bin → Digit → Bin
\end{code}
%</bin-good>

\begin{code}

private variable
  A B : Set
  d e : Digit
  n m : Bin

open import Data.Product

succ-l : Digit → Digit
succ-l 𝟙 = 𝟚
succ-l 𝟚 = 𝟛
succ-l 𝟛 = 𝟚

succ-m : Digit → Bin → Bin
succ : Bin → Bin
succ 𝟘 = 𝟙
succ 𝟙 = 𝟙 ⟨ 𝟘 ⟩ 𝟙 
succ (l ⟨ m ⟩ r) = succ-l l ⟨ succ-m l m ⟩ r

succ-m 𝟙 m = m
succ-m 𝟚 m = m
succ-m 𝟛 m = succ m

\end{code}

%<*good-1>
\begin{code}
good-1 : Bin
good-1 = 𝟛 ⟨ 𝟛 ⟨ 𝟛 ⟨ 𝟙 ⟩ 𝟙 ⟩ 𝟙 ⟩ 𝟙
\end{code}
%</good-1>

\begin{code}

\end{code}

%<*good-2>
\begin{code}
good-2 : Bin
good-2 = 𝟚 ⟨ 𝟚 ⟨ 𝟚 ⟨ 𝟙 ⟨ 𝟘 ⟩ 𝟙 ⟩ 𝟙 ⟩ 𝟙 ⟩ 𝟙
\end{code}
%</good-2>

\begin{code}

cuss : Bin → Bin
cuss 𝟘 = 𝟙
cuss 𝟙 = 𝟙 ⟨ 𝟘 ⟩ 𝟙
cuss (l ⟨ m ⟩ 𝟙) = l ⟨ m ⟩ 𝟚
cuss (l ⟨ m ⟩ 𝟚) = l ⟨ m ⟩ 𝟛
cuss (l ⟨ m ⟩ 𝟛) = l ⟨ cuss m ⟩ 𝟚

open import Data.Nat

\end{code}

%<*interpret>
\begin{code}
⟦_⟧D : Digit → ℕ
⟦ 𝟙 ⟧D = 1
⟦ 𝟚 ⟧D = 2
⟦ 𝟛 ⟧D = 3

⟦_⟧B : Bin → ℕ
⟦ 𝟘 ⟧B         = 0
⟦ 𝟙 ⟧B         = 1
⟦ l ⟨ m ⟩ r ⟧B = ⟦ l ⟧D + 2 * ⟦ m ⟧B + ⟦ r ⟧D
\end{code}
%</interpret>

\begin{code}

\end{code}

%<*ix>
\begin{code}
data IxD : Digit → Set where
  𝟙-1         : IxD 𝟙
  𝟚-1 𝟚-2     : IxD 𝟚
  𝟛-1 𝟛-2 𝟛-3 : IxD 𝟛

data IxB : Bin → Set where
  𝟙-1  : IxB 𝟙
  ⟨⟩-l : IxD d → IxB (d ⟨ n ⟩ e)
  ⟨⟩-m1 : IxB n → IxB (d ⟨ n ⟩ e)
  ⟨⟩-m2 : IxB n → IxB (d ⟨ n ⟩ e)
  ⟨⟩-r : IxD e → IxB (d ⟨ n ⟩ e)
\end{code}
%</ix>

\begin{code}

\end{code}

%<*rep>
\begin{code}
Array : Set → Bin → Set
Array A b = IxB b → A
\end{code}
%</rep>

\begin{code}
izeroD : ∀ {d} → IxD (succ-l d)
izeroD {𝟙} = 𝟚-1
izeroD {𝟚} = 𝟛-1
izeroD {𝟛} = 𝟚-1

\end{code}

%<*izero>
\begin{code}
izero : ∀ {n} → IxB (succ n)
\end{code}
%</izero>

\begin{code}
izero {𝟘}         = 𝟙-1
izero {𝟙}         = ⟨⟩-l 𝟙-1
izero {l ⟨ m ⟩ r} = ⟨⟩-l izeroD

isuccD : IxD d → IxB (succ (d ⟨ m ⟩ e))
isuccD 𝟙-1 = ⟨⟩-l 𝟚-2
isuccD 𝟚-1 = ⟨⟩-l 𝟛-2
isuccD 𝟚-2 = ⟨⟩-l 𝟛-3
isuccD 𝟛-1 = ⟨⟩-l 𝟚-2
isuccD 𝟛-2 = ⟨⟩-m1 izero
isuccD 𝟛-3 = ⟨⟩-m2 izero

\end{code}

%<*isucc>
\begin{code}
isucc : IxB n → IxB (succ n)

\end{code}
%</isucc>

\begin{code}
isucc-m : IxB n → IxB (succ-m d n)
isucc-m {d = 𝟙} i = i
isucc-m {d = 𝟚} i = i
isucc-m {d = 𝟛} i = isucc i 

isucc 𝟙-1      = ⟨⟩-r 𝟙-1
isucc (⟨⟩-l i) = isuccD i
isucc (⟨⟩-m1 {d = d} i) = ⟨⟩-m1 (isucc-m {d = d} i)
isucc (⟨⟩-m2 {d = d} i) = ⟨⟩-m2 (isucc-m {d = d} i)
isucc (⟨⟩-r i) = ⟨⟩-r i

{-
open import Data.Fin.Base using (Fin; zero; suc; _↑ˡ_; _↑ʳ_)
⟦_⟧ID : IxD d → Fin ⟦ d ⟧D
⟦ 𝟙-1 ⟧ID = zero
⟦ 𝟚-1 ⟧ID = zero
⟦ 𝟚-2 ⟧ID = suc zero
⟦ 𝟛-1 ⟧ID = zero
⟦ 𝟛-2 ⟧ID = suc zero
⟦ 𝟛-3 ⟧ID = suc (suc zero)

⟦_⟧IB : IxB n → Fin ⟦ n ⟧B
⟦ 𝟙-1 ⟧IB = zero
⟦ ⟨⟩-l {_} {n} i ⟧IB = (⟦ i ⟧ID ↑ˡ (2 * ⟦ n ⟧B)) ↑ˡ ⟦ _ ⟧D
⟦ ⟨⟩-m1 {n} {d} i ⟧IB = (⟦ d ⟧D ↑ʳ (⟦ i ⟧IB ↑ˡ 1 * ⟦ n ⟧B)) ↑ˡ ⟦ _ ⟧D 
⟦ ⟨⟩-m2 {n} {d} i ⟧IB = (⟦ d ⟧D ↑ʳ (⟦ n ⟧B ↑ʳ (⟦ i ⟧IB ↑ˡ 0))) ↑ˡ ⟦ _ ⟧D 
⟦ ⟨⟩-r {n} i ⟧IB = _ ↑ʳ ⟦ i ⟧ID

open import Relation.Binary.HeterogeneousEquality

izero-c : (i : IxB n) → _≅_ (⟦ isucc i ⟧IB) {B = Fin (suc ⟦ n ⟧B)} (suc ⟦ i ⟧IB)
izero-c 𝟙-1 = refl
izero-c (⟨⟩-l x) = {!ew!}
izero-c (⟨⟩-m1 i) = {!!}
izero-c (⟨⟩-m2 i) = {!!}
izero-c (⟨⟩-r x) = {!!}
-}

\end{code}

%<*iview>
\begin{code}
data IxV : IxB (succ n) → Set where
  as-izero : IxV {n} izero
  as-isucc : (i : IxB n) → IxV (isucc i)

iview : {n : Bin} → (i : IxB (succ n)) → IxV i
\end{code}
%</iview>

\begin{code}
iview {𝟘} 𝟙-1 = as-izero
iview {l ⟨ m ⟩ r} (⟨⟩-r i) = as-isucc (⟨⟩-r i)
iview {𝟙} (⟨⟩-l 𝟙-1) = as-izero
iview {𝟙} (⟨⟩-r 𝟙-1) = as-isucc 𝟙-1
iview {𝟙 ⟨ m ⟩ r} (⟨⟩-l 𝟚-1) = as-izero
iview {𝟙 ⟨ m ⟩ r} (⟨⟩-l 𝟚-2) = as-isucc (⟨⟩-l 𝟙-1)
iview {𝟚 ⟨ m ⟩ r} (⟨⟩-l 𝟛-1) = as-izero
iview {𝟚 ⟨ m ⟩ r} (⟨⟩-l 𝟛-2) = as-isucc (⟨⟩-l 𝟚-1)
iview {𝟚 ⟨ m ⟩ r} (⟨⟩-l 𝟛-3) = as-isucc (⟨⟩-l 𝟚-2)
iview {𝟛 ⟨ m ⟩ r} (⟨⟩-l 𝟚-1) = as-izero
iview {𝟛 ⟨ m ⟩ r} (⟨⟩-l 𝟚-2) = as-isucc (⟨⟩-l 𝟛-1)
iview {𝟙 ⟨ m ⟩ r} (⟨⟩-m1 i) = as-isucc (⟨⟩-m1 i)
iview {𝟚 ⟨ m ⟩ r} (⟨⟩-m1 i) = as-isucc (⟨⟩-m1 i)
iview {𝟛 ⟨ m ⟩ r} (⟨⟩-m1 i) with iview i
... | as-izero = as-isucc (⟨⟩-l 𝟛-2)
... | as-isucc i = as-isucc (⟨⟩-m1 i)
iview {𝟙 ⟨ m ⟩ r} (⟨⟩-m2 i) = as-isucc (⟨⟩-m2 i)
iview {𝟚 ⟨ m ⟩ r} (⟨⟩-m2 i) = as-isucc (⟨⟩-m2 i)
iview {𝟛 ⟨ m ⟩ r} (⟨⟩-m2 i) with iview i
... | as-izero = as-isucc (⟨⟩-l 𝟛-3)
... | as-isucc i = as-isucc (⟨⟩-m2 i)

\end{code}

%<*ops>
\begin{code}
head : Array A (succ n) → A
head {n = 𝟘} f = f 𝟙-1
head {n = 𝟙} f = f (⟨⟩-l 𝟙-1)
head {n = 𝟙 ⟨ m ⟩ r} f = f (⟨⟩-l 𝟚-1)
head {n = 𝟚 ⟨ m ⟩ r} f = f (⟨⟩-l 𝟛-1)
head {n = 𝟛 ⟨ m ⟩ r} f = f (⟨⟩-l 𝟚-1)

cons : A → Array A n → Array A (succ n)
cons {n = n} x f i with iview i
... | as-izero   = x
... | as-isucc i = f i
\end{code}
%</ops>

\begin{code}

\end{code}

%<*trieified>
\begin{code}
data Finger (A : Set) : Digit → Set where
  𝟙 : A → Finger A 𝟙
  𝟚 : A → A → Finger A 𝟚
  𝟛 : A → A → A → Finger A 𝟛

data Array′ (A : Set) : Bin → Set where
  𝟘     : Array′ A 𝟘
  𝟙     : A → Array′ A 𝟙
  _⟨_⟩_ : Finger A d → Array′ A n → Array′ A n → Finger A e →  Array′ A (d ⟨ n ⟩ e)
\end{code}
%</trieified>

\begin{code}
open import Relation.Binary.PropositionalEquality

module _ (x : 
\end{code}

%<*succ-noncomm>
\begin{code}
    ∀ n → succ (cuss n) ≡ cuss (succ n)
\end{code}
%</succ-noncomm>

\begin{code}
  ) where


module _ (_ : 
\end{code}

%<*head-cons>
\begin{code}
    (x : A) (xs : Array A n) → head (cons x xs) ≡ x
\end{code}
%</head-cons>

\begin{code}
  ) where

postulate
  snoc : Array A n → A → Array A (cuss n)
  
\end{code}

data Rel : (n m : Bin) → Set where
  refl : ∀ n → Rel n n
  symm : Rel n m → Rel m n
  trans : ∀ {k} → Rel n m → Rel m k → Rel n k
  cong : Rel n m → Rel (d ⟨ n ⟩ e) (d ⟨ m ⟩ e)

  flip : Rel (𝟛 ⟨ 𝟘 ⟩ 𝟙) (𝟙 ⟨ 𝟙 ⟩ 𝟙)
  roll : Rel n m → Rel (succ n) (cuss m)

-- you might be able to get away with leaving out one or two of symm or trans

rel-1 : Rel (𝟛 ⟨ 𝟚 ⟨ 𝟘 ⟩ 𝟙 ⟩ 𝟛) (𝟙 ⟨ 𝟙 ⟨ 𝟙 ⟩ 𝟙 ⟩ 𝟛)
rel-1 = trans (roll (refl (𝟚 ⟨ 𝟚 ⟨ 𝟘 ⟩ 𝟙 ⟩ 𝟛))) (trans (cong (trans (symm (roll (refl (𝟚 ⟨ 𝟘 ⟩ 𝟙)))) flip)) (roll (refl (𝟙 ⟨ 𝟙 ⟨ 𝟙 ⟩ 𝟙 ⟩ 𝟚))))

succ-rel : Rel n m → Rel (succ n) (succ m)
succ-rel r = trans (roll r) (symm (roll (refl _)))
