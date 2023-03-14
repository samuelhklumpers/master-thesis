\documentclass[../../Main.tex]{subfiles}

\begin{document}
\begin{code}
module Extra.Category where

open import Cubical.Data.Sigma
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Prelude
open import Cubical.HITs.PropositionalTruncation

open import Function.Base using (id; _∘_)


private variable
  ℓ ℓ′ : Level
  A B C : Type ℓ


record RawFunctor ℓ : Type (ℓ-suc ℓ) where
  field
\end{code}
%<*RawFunctor>
\AgdaTarget{F₀}
\AgdaTarget{fmap, .fmap}
\begin{code}
    F₀   : Type ℓ → Type ℓ
    fmap : (A → B) → F₀ A → F₀ B
\end{code}
%</RawFunctor>
\begin{code}
open RawFunctor


-- keeping these as f x = g x, otherwise we'd have to give the types anyway
record Functor ℓ : Type (ℓ-suc ℓ) where
  field
    RawF   : RawFunctor ℓ

  open RawFunctor RawF renaming (F₀ to F; fmap to mapF)
 
  field
\end{code}
%<*Functor>
\AgdaTarget{f-id}
\AgdaTarget{f-comp}
\begin{code}
    f-id   : (x : F A)
           → mapF id x ≡ x

    f-comp : (g : B → C) (f : A → B) (x : F A)
           → mapF (g ∘ f) x ≡ mapF g (mapF f x) 
\end{code}
%</Functor>
\begin{code}

open Functor


\end{code}
%<*Algebra>
\AgdaTarget{Algebra}
\AgdaTarget{Carrier}
\AgdaTarget{forget, .forget}
\begin{code}
record Algebra (F : Type ℓ → Type ℓ) : Type (ℓ-suc ℓ) where
  field
    Carrier : Type ℓ
    forget  : F Carrier → Carrier
\end{code}
%</Algebra>
\begin{code}

open Algebra


Alg→-Sqr : (RawF : RawFunctor ℓ) (AlgA AlgB : Algebra (RawF .F₀)) → (AlgA .Carrier → AlgB .Carrier) → Type ℓ
\end{code}
%<*AlgSqr>
\AgdaTarget{Alg→-Sqr}
\begin{code}
Alg→-Sqr F A B f = f ∘ A .forget ≡ B .forget ∘ F .fmap f
\end{code}
%</AlgSqr>
\begin{code}

\end{code}
%<*AlgMap>
\AgdaTarget{Alg→}
\AgdaTarget{mor, .mor}
\AgdaTarget{coh, .coh}
\begin{code}
record Alg→ (RawF : RawFunctor ℓ)
            (AlgA AlgB : Algebra (RawF .F₀)) : Type ℓ where
  constructor alg→
  
  field
    mor : AlgA .Carrier → AlgB .Carrier
    coh : ∥ Alg→-Sqr RawF AlgA AlgB mor ∥₁ 
\end{code}
%</AlgMap>
\begin{code}

open Alg→

\end{code}
%<*AlgPath>
\AgdaTarget{Alg→-Path}
\begin{code}
Alg→-Path : {F : RawFunctor ℓ} {A B : Algebra (F .F₀)}
          → (g f : Alg→ F A B) → g .mor ≡ f .mor → g ≡ f
\end{code}
%</AlgPath>
\begin{code}
Alg→-Path {F = F} {A = A} {B = B} g f p i = alg→ (p i) (∥∥-isPropDep (λ h → Alg→-Sqr F A B h) (g .coh) (f .coh) p i)

id-Alg→ : (FunF : Functor ℓ) (X : Algebra (FunF .RawF .F₀)) → Alg→ (FunF .RawF) X X
id-Alg→ FunF X .mor = id
id-Alg→ FunF X .coh = ∣ funExt (λ x → cong (X .forget) (sym (FunF .f-id x))) ∣₁

∘-Alg→ : (FunF : Functor ℓ) (X Y Z : Algebra (FunF .RawF .F₀)) → Alg→ (FunF .RawF) Y Z → Alg→ (FunF .RawF) X Y → Alg→ (FunF .RawF) X Z
∘-Alg→ FunF X Y Z g f .mor = g .mor ∘ f .mor
∘-Alg→ FunF X Y Z (alg→ g gc') (alg→ f fc') .coh = rec2 squash₁ (λ x y → ∣ go x y ∣₁) gc' fc'
  where
  open Functor FunF renaming (RawF to RawF'; f-comp to compF)
  open RawFunctor RawF' renaming (F₀ to F; fmap to mapF)

  go : Alg→-Sqr RawF' Y Z g → Alg→-Sqr RawF' X Y f → Alg→-Sqr RawF' X Z (λ x → g (f x))
  go gc fc = funExt λ x → 
    g (f (X .forget x))           ≡⟨ cong g (funExt⁻ fc x) ⟩
    g (Y .forget (mapF f x))      ≡⟨ funExt⁻ gc _ ⟩
    Z .forget (mapF g (mapF f x)) ≡⟨ cong (Z .forget) (sym (compF _ _ _)) ⟩
    Z .forget (mapF (g ∘ f) x)    ∎


weakContr : Type ℓ → Type ℓ -- mildly stronger than connected?
\end{code}
%<*weakContr>
\AgdaTarget{weakContr}
\begin{code}
weakContr A = Σ[ x ∈ A ] (∀ y → ∥ x ≡ y ∥₁)
\end{code}
%</weakContr>
\begin{code}

weakProp : Type ℓ → Type ℓ
weakProp A = (x y : A) → ∥ x ≡ y ∥₁

weakContr→weakProp : {A : Type ℓ} → weakContr A → weakProp A
weakContr→weakProp (x , p) y z = rec2 squash₁ (λ q r → ∣ sym q ∙ r ∣₁) (p y) (p z)


\end{code}
%<*Initial>
\AgdaTarget{Initial}
\AgdaTarget{initiality, .initiality}
\begin{code}
record Initial (C : Type ℓ) (R : C → C → Type ℓ′)
               (Z : C) : Type (ℓ-max (ℓ-suc ℓ) ℓ′) where
  field
    initiality : ∀ X → weakContr (R Z X)
\end{code}
%</Initial>
\begin{code}

open Initial


InitAlg : (RawF : RawFunctor ℓ) (A : Algebra (RawF .F₀)) → Type (ℓ-suc (ℓ-suc ℓ))
\end{code}
%<*InitAlg>
\AgdaTarget{InitAlg}
\begin{code}
InitAlg RawF A = Initial (Algebra (RawF .F₀)) (Alg→ RawF) A
\end{code}
%</InitAlg>

%<*InitAlg-equiv>
\AgdaTarget{InitAlg-≃}
\begin{code}
InitAlg-≃ : (F : Functor ℓ) (A B : Algebra (F .RawF .F₀))
            → InitAlg (F .RawF) A → InitAlg (F .RawF) B
            → A .Carrier ≃ B .Carrier
\end{code}
%</InitAlg-equiv>

\begin{code}
InitAlg-≃ FunF A B IA IB = fun .mor , eq
  where
  RawF' = FunF .RawF
  
  fun : Alg→ RawF' A B
  fun = IA .initiality B .fst

  inv : Alg→ RawF' B A
  inv = IB .initiality A .fst

  module _ (sec' : ∘-Alg→ FunF B A B fun inv ≡ id-Alg→ FunF B)
           (ret' : ∘-Alg→ FunF A B A inv fun ≡ id-Alg→ FunF A)
    where
    sec : section (fun .mor) (inv .mor)
    sec x = funExt⁻ (cong mor sec') x

    ret : retract (fun .mor) (inv .mor)
    ret x = funExt⁻ (cong mor ret') x

    eq' : isEquiv (fun .mor)
    eq' = isoToIsEquiv (iso (fun .mor) (inv .mor) sec ret)

  eq : isEquiv (fun .mor)
  eq = rec2 (isPropIsEquiv (fun .mor)) eq'
    (weakContr→weakProp (IB .initiality B) _ _)
    (weakContr→weakProp (IA .initiality A) _ _)
\end{code}
\end{document}