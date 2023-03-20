\begin{document}
\begin{code}
{-# OPTIONS --cubical --copatterns --postfix-projections #-}

module Extra.Category.WellFounded where

open import Cubical.Data.Sigma
open import Cubical.Data.Vec as V
open import Cubical.Data.Vec.Properties
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv.Base
open import Cubical.Functions.Embedding
open import Cubical.Relation.Nullary.Properties
open import Cubical.HITs.PropositionalTruncation as ∥∥₁ renaming (rec to rec₁)
open import Data.Nat
open import Data.Unit

import Cubical.Data.Equality as Eq


open import Prelude hiding (rec)
open import Extra.Category
open import Extra.Category.Poly
open import Extra.ProgOrn.Desc hiding (All)
open import Extra.ProgOrn.Mu.Properties 

open Algebra
open Alg→
open Initial
\end{code}

%<*Wf-rec>
\AgdaTarget{Wf-rec}
\begin{code}
Wf-rec : (D : Desc′) (X : Algebra (Ḟ D)) → Wf D (X .forget)
       → (Ḟ D A → A) → X .Carrier → A
\end{code}
%</Wf-rec>
\begin{code}
Wf-rec {A = A} D X wf f x = rec x (wf x)
  module Wf-rec where
  private
    cx = X .forget
    CX = X .Carrier

  rec   : ∀ x → Acc D cx x → A
  Ḟ-mapRec  : ∀ E x → Acc' D cx E x → Base A E 
  V-mapRec : ∀ n (x : Vec {ℓ = ℓ-suc ℓ-zero} CX n) → All (Acc D cx) x → Vec A n 

  rec _ (acc (x' , p) a) = f (Ḟ-mapRec _ x' a)
  
  Ḟ-mapRec (ṿ n)   (in-ṿ x)       (acc-ṿ a) = in-ṿ (V-mapRec n x a)
  Ḟ-mapRec (σ S D) (in-σ (s , x)) (acc-σ a) = in-σ (s , Ḟ-mapRec (D s) x a)

  V-mapRec zero    []       a        = []
  V-mapRec (suc n) (x ∷ xs) (ax ∷ a) = (rec x ax) ∷ V-mapRec n xs a

injective : {A : Type ℓ} {B : Type ℓ′} → (A → B) → Type (ℓ-max ℓ ℓ′) 
injective {ℓ = ℓ} {ℓ′ = ℓ′} f = ∀ x y → _≡_ {ℓ = ℓ′} (f x) (f y) → _≡_ {ℓ = ℓ} x y

module _ {A : Type₁} (D : Desc′) (X : Algebra (Ḟ D)) (wf : Wf D (X .forget)) (f : (Ḟ D A → A)) (inj : injective (X .forget)) where
  open module WfRec (x : X .Carrier) = Wf-rec D X wf f x

  private
    cx = X .forget
    CX = X .Carrier
\end{code}

%<*Wf-rec-irr>
\AgdaTarget{Wf-rec-irrelevant}
\begin{code}
  Wf-rec-irrelevant : ∀ x′ y′ x a b → rec x′ x a ≡ rec y′ x b 
\end{code}
%</Wf-rec-irr>
\begin{code}
  Wf-rec-irrelevant x′ y′ x a b = go-1 x a b
    where
    go-1 : ∀ x a b → rec x′ x a ≡ rec y′ x b
    go-2 : ∀ E x a b → Ḟ-mapRec x′ E x a ≡ Ḟ-mapRec y′ E x b
    go-3 : ∀ n x a b → V-mapRec x′ n x a ≡ V-mapRec y′ n x b
    
    go-1 x (acc (x' , p) a) (acc (y' , q) b) with Eq.pathToEq (inj _ _ (p ∙ sym q))
    ... | Eq.refl = cong f (go-2 D x' a b)

    go-2 .(ṿ _)   (in-ṿ x)       (acc-ṿ a) (acc-ṿ b) = cong in-ṿ (go-3 _ x a b)
    go-2 .(σ _ _) (in-σ (s , x)) (acc-σ a) (acc-σ b) = cong in-σ (cong (s ,_) (go-2 _ x a b))

    go-3 .zero    []       []       []       = refl
    go-3 .(suc _) (x ∷ xs) (ax ∷ a) (bx ∷ b) = cong₂ _∷_ (go-1 x ax bx) (go-3 _ xs a b)

\end{code}

%<*Wf-rec-unfold>
\AgdaTarget{unfold-Wf-rec}
\begin{code}
  unfold-Wf-rec : ∀ x′ → rec (cx x′) (cx x′) (wf (cx x′))
                       ≡ f (Base-map (λ y → rec y y (wf y)) x′)
\end{code}
%</Wf-rec-unfold>
\begin{code}
  unfold-Wf-rec x′ = go-1 x′ (wf (cx x′))
    where
    go-1 : ∀ x a → rec (cx x′) (cx x) a ≡ f (Base-map (λ y → rec y y (wf y)) x)
    go-2 : ∀ E x a → Ḟ-mapRec (cx x′) E x a ≡ Base-map (λ y → rec y y (wf y)) x
    go-3 : ∀ n (x : Vec CX n) a → V-mapRec (cx x′) n x a ≡ V.map (λ y → rec y y (wf y)) x

    go-1 x (acc (x' , p) a) = cong f (go-2 D x' a ∙ cong (Base-map _) (inj _ _ p))

    go-2 _ (in-ṿ x)       (acc-ṿ a) = cong in-ṿ (go-3 _ x a)
    go-2 _ (in-σ (s , x)) (acc-σ a) = cong in-σ (cong (s ,_) (go-2 _ x a))

    go-3 zero    []       []       = refl
    go-3 (suc n) (x ∷ xs) (ax ∷ a) = cong (rec (cx x′) x ax ∷_) (go-3 n xs a) ∙ congS (_∷ V.map (λ y → rec y y (wf y)) xs) (Wf-rec-irrelevant (cx x′) x x ax (wf x))

Wf-rec-coh : (D : Desc′) (X : Algebra (Ḟ D)) (wf : Wf D (X .forget)) (Y : Algebra (Ḟ D)) (inj : injective (X .forget)) → Alg→-Sqr (RawḞ D) X Y (Wf-rec D X wf (Y .forget))
Wf-rec-coh D X wf Y inj = funExt (unfold-Wf-rec D X wf (Y .forget) inj)
\end{code}

%<*Wf+inj=Init>
\AgdaTarget{Wf+inj→Init}
\begin{code}
Wf+inj→Init : (D : Desc′) (X : Algebra (Ḟ D)) → Wf D (X .forget)
            → injective (X .forget) → InitAlg (RawḞ D) X
\end{code}
%</Wf+inj=Init>
\begin{code}
Wf+inj→Init D X wf inj .initiality Y =
  let f = alg→ (Wf-rec D X wf (Y .forget)) ∣ Wf-rec-coh D X wf Y inj ∣₁
  in f , λ g → ∥∥₁.map (Alg→-Path f g ∘ f≡g g) (g .coh)
  where
  open Algebra X renaming (Carrier to CX; forget to cx)
  open Algebra Y renaming (Carrier to CY; forget to cy)

  module _ (g : Alg→ (RawḞ D) X Y) (sqr : Alg→-Sqr (RawḞ D) X Y (g .mor)) where
    go-1 : ∀ x → Acc D (X .forget) x → Wf-rec D X wf (Y .forget) x ≡ g .mor x
    go-2 : ∀ E (x : Base CX E) → Acc' D (X .forget) E x → Base-map (Wf-rec D X wf (Y .forget)) x ≡ Base-map (g .mor) x
    go-3 : ∀ n (xs : Vec CX n) → All (Acc D (X .forget)) xs → V.map (Wf-rec D X wf (Y .forget)) xs ≡ V.map (g .mor) xs

    go-1 x (acc (x' , p) a) = subst (λ x → Wf-rec D X wf (Y .forget) x ≡ g .mor x) p
      (funExt⁻ (Wf-rec-coh D X wf Y inj) x'
      ∙ cong cy (go-2 D x' a)
      ∙ sym (funExt⁻ sqr x'))

    go-2 (ṿ n)   (in-ṿ xs)      (acc-ṿ a) = cong in-ṿ (go-3 _ xs a)
    go-2 (σ S D) (in-σ (s , x)) (acc-σ a) = cong in-σ (cong (s ,_) (go-2 _ x a))

    go-3 .zero    []       []       = refl
    go-3 .(suc _) (x ∷ xs) (ax ∷ a) = cong₂ _∷_ (go-1 x ax) (go-3 _ xs a)

    f≡g : Wf-rec D X wf (Y .forget) ≡ g .mor
    f≡g = funExt (λ x → go-1 x (wf x))

\end{code}

%<*Wf+inj=mu>
\AgdaTarget{Wf+inj≡μ}
\begin{code}
Wf+inj≃μ : (D : Desc′) (X : Algebra (Ḟ D)) → Wf D (X .forget)
         → injective (X .forget) → X .Carrier ≃ μ D
\end{code}
%</Wf+inj=mu>
\begin{code}
Wf+inj≃μ D X wf inj = InitAlg-≃ (FunḞ D) X (μ-Alg D) (Wf+inj→Init D X wf inj) (InitM D)
\end{code}
\end{document}
