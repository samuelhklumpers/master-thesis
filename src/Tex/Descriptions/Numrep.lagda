\begin{document}
\begin{code}
{-# OPTIONS --type-in-type #-}

module Tex.Descriptions.Numrep where

open import Agda.Primitive
  using    ( Level
           ; SSet )
  renaming ( lzero to ℓ-zero
           ; lsuc  to ℓ-suc
           ; _⊔_   to ℓ-max
           ; Set   to Type
           ; Setω  to Typeω )

open import Function.Base

open import Tex.Background using (ℕ; zero; suc; _≡_; refl; ⊤; ⊥; tt; _⊎_; inj₁; inj₂; _×_; fst; snd; Σ; _,_; Σ-syntax; _<_; z<s; s<s)

{-# BUILTIN EQUALITY _≡_ #-}

private variable
  A B C : Type
\end{code}


module Fin-Lookup where
  open import Tex.Background using (Fin; zero; suc)
  %<*Lookup>
  \AgdaTarget{Lookup}
  Lookup : Type → ℕ → Type
  Lookup A n = Fin n → A
  %</Lookup>

  %<*Lookup-insert>
  insert? : ∀ {n} → Lookup A n → Fin (suc n) → A → Lookup A (suc n)
  insert? xs zero x zero = x
  insert? xs zero x (suc j) = xs j
  insert? {n = suc n} xs (suc i) x zero = xs zero
  insert? {n = suc n} xs (suc i) x (suc j) = insert? (xs ∘ suc) i x j
  %</Lookup-insert>

  insert-lookup? : ∀ {n} → (xs : Lookup n A) (i : Fin (suc n)) (x : A) → insert? xs i x i ≡ x
  insert-lookup? xs zero x = refl
  insert-lookup? {n = suc n} xs (suc i) x = insert-lookup? (xs ∘ suc) i x


%<*Iso>
\AgdaTarget{Iso}
\AgdaTarget{rightInv}
\AgdaTarget{leftInv}
\begin{code}
record _≃_ A B : Type where
  constructor iso
  field
    fun  : A → B
    inv  : B → A
    rightInv  : ∀ b → fun (inv b) ≡ b 
    leftInv   : ∀ a → inv (fun a) ≡ a
\end{code}
%</Iso>

%<*isigma>
\AgdaTarget{Σ'}
\AgdaTarget{use-as-def, \_use-as-def}
\begin{code}
record Σ' (A : Type) (B : A → Type) : Type where
  constructor _use-as-def
  field
    {fst} : A
    snd : B fst
\end{code}
%</isigma>
\begin{code}
open Σ'
infix 1 _use-as-def
infix 10 _≃_

open _≃_
\end{code}

%<*Def>
\AgdaTarget{Def}
\AgdaTarget{defined-by}
\AgdaTarget{by-definition}
\begin{code}
Def : Type → Type
Def A = Σ' Type λ B → A ≃ B

defined-by     : {A : Type} → Def A        → Type
by-definition  : {A : Type} → (d : Def A)  → A ≃ (defined-by d)
\end{code}
%</Def>


\begin{code}
defined-by     = fst
by-definition  = snd

infix  1 ≃-begin_
infixr 2 _≃⟨_⟩_
infixr 2 _≃⟨⟩_
infix  3 _≃-∎
\end{code}

<*Iso-reasoning>
\begin{code}
_≃⟨_⟩_ : ∀ A {B C} → A ≃ B → B ≃ C → A ≃ C
_≃⟨⟩_ : ∀ A {B} → A ≃ B → A ≃ B
_≃-∎ : ∀ A → A ≃ A
\end{code}
</Iso-reasoning>

\begin{code}
≃-begin_ : ∀ {A B} → A ≃ B → A ≃ B
≃-begin A≃B = A≃B

(A ≃⟨ A≃B ⟩ B≃C) .fun       = B≃C .fun ∘ A≃B .fun
(A ≃⟨ A≃B ⟩ B≃C) .inv       = A≃B .inv ∘ B≃C .inv
(A ≃⟨ A≃B ⟩ B≃C) .rightInv b rewrite A≃B .rightInv (B≃C .inv b) = B≃C .rightInv b
(A ≃⟨ A≃B ⟩ B≃C) .leftInv  a rewrite B≃C .leftInv (A≃B .fun a)  = A≃B .leftInv a

A ≃⟨⟩ A≃B = A≃B

A ≃-∎ = iso id id (λ _ → refl) (λ _ → refl)
\end{code}

%<*Fin-lemmas>
\begin{code}
⊥-strict  : (A → ⊥) → A ≃ ⊥
<-split   : ∀ n → (Σ[ m ∈ ℕ ] m < suc n) ≃ (⊤ ⊎ (Σ[ m ∈ ℕ ] m < n))
\end{code}
%</Fin-lemmas>

consequences of ua
\begin{code}
postulate
\end{code} 
%<*Fin-lemmas-2>
\begin{code}
  funExt  : {f g : A → B} → (∀ a → f a ≡ g a) → f ≡ g
  cong    : (P : Type → Type) → A ≃ B → P A ≃ P B
\end{code}
%</Fin-lemmas-2>


\begin{code}
⊥-strict f .fun = f
⊥-strict f .inv = λ ()
⊥-strict f .rightInv ()
⊥-strict f .leftInv a with f a
... | ()

<-split n = iso to from sec ret
  where
  to : (Σ[ m ∈ ℕ ] m < suc n) → (⊤ ⊎ (Σ[ m ∈ ℕ ] m < n))
  to (zero  , _)     = inj₁ tt
  to (suc m , s<s p) = inj₂ (m , p)

  from : (⊤ ⊎ (Σ[ m ∈ ℕ ] m < n)) → (Σ[ m ∈ ℕ ] m < suc n)
  from (inj₁ _)       = zero  , z<s
  from (inj₂ (m , p)) = suc m , s<s p

  sec : ∀ y → to (from y) ≡ y
  sec (inj₁ tt) = refl
  sec (inj₂ x)  = refl

  ret : ∀ x → from (to x) ≡ x
  ret (zero , z<s)    = refl
  ret (suc m , s<s p) = refl
\end{code}

%<*Fin-def>
\begin{code}
Fin-def : ∀ n → Def (Σ[ m ∈ ℕ ] m < n)
Fin-def zero             =
  Σ[ m ∈ ℕ ] (m < zero)  ≃⟨  ⊥-strict (λ ()) ⟩
  ⊥                      ≃-∎ use-as-def
Fin-def (suc n)                 =
  Σ[ m ∈ ℕ ] (m < suc n)        ≃⟨  <-split n ⟩
  (⊤ ⊎ (Σ[ m ∈ ℕ ] m < n))      ≃⟨  cong (⊤ ⊎_) (by-definition (Fin-def n)) ⟩
  (⊤ ⊎ defined-by (Fin-def n))  ≃-∎ use-as-def
\end{code}
%</Fin-def>

%<*Fin>
\begin{code}
Fin : ℕ → Type
Fin n = defined-by (Fin-def n)
\end{code}
%</Fin>


%<*Lookup2>
\begin{code}
Lookup : Type → ℕ → Type
Lookup A n = Fin n → A
\end{code}
%</Lookup2>

%<*Vec-lemmas>
\begin{code}
⊥→A≃⊤ : (⊥ → A) ≃ ⊤
⊤→A≃A : (⊤ → A) ≃ A
⊎→≃→× : ((A ⊎ B) → C) ≃ ((A → C) × (B → C))
\end{code}
%</Vec-lemmas>

\begin{code}
⊥→A≃⊤ .fun _ = tt
⊥→A≃⊤ .inv _ = λ ()
⊥→A≃⊤ .rightInv tt = refl
⊥→A≃⊤ .leftInv a = funExt (λ ())
\end{code}


\begin{code}
⊤→A≃A .fun f = f tt
⊤→A≃A .inv a = λ _ → a
⊤→A≃A .rightInv b = refl
⊤→A≃A .leftInv a = refl
\end{code}

\begin{code}
⊎→≃→× .fun f = (f ∘ inj₁) , (f ∘ inj₂)
⊎→≃→× .inv (f , g) = λ { (inj₁ x) → f x ; (inj₂ x) → g x }
⊎→≃→× .rightInv (f , g) = refl
⊎→≃→× .leftInv a = funExt λ { (inj₁ x) → refl ; (inj₂ x) → refl }
\end{code}

%<*Vec-def>
\begin{code}
Vec-def : ∀ A n → Def (Lookup A n)
Vec-def A zero    =
  (Fin zero → A)  ≃⟨⟩
  (⊥ → A)         ≃⟨ ⊥→A≃⊤ ⟩
  ⊤               ≃-∎ use-as-def

Vec-def A (suc n)                 =
  (Fin (suc n) → A)               ≃⟨⟩
  (⊤ ⊎ Fin n → A)                 ≃⟨ ⊎→≃→× ⟩
  (⊤ → A) × (Fin n → A)           ≃⟨ cong (_× (Fin n → A)) ⊤→A≃A ⟩
  A × (Fin n → A)                 ≃⟨ cong (A ×_) (by-definition (Vec-def A n)) ⟩
  A × (defined-by (Vec-def A n))  ≃-∎ use-as-def
\end{code}
%</Vec-def>

%<*Vec>
\begin{code}
Vec : Type → ℕ → Type
Vec A n = defined-by (Vec-def A n)

Vec-Lookup : ∀ A n → Lookup A n ≃ Vec A n
Vec-Lookup A n = by-definition (Vec-def A n)
\end{code}
%</Vec>
\end{document}
