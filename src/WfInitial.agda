{-# OPTIONS --cubical --copatterns --postfix-projections #-}

module WfInitial where

open import Level renaming (zero to lzero; suc to lsuc)
open import Data.Nat
open import Data.Unit
open import Data.Vec as V
import Data.Vec.Properties as VP
open import Data.Vec.Relation.Unary.All
open import Cubical.Data.Sigma

import Cubical.Data.Equality as Eq

open import Prelude
open import Cubical.Foundations.Equiv.Base


data Desc : Set₁  where
  ṿ   : ℕ → Desc
  σ   : (S : Set) (D : S → Desc) → Desc

syntax σ S (λ s → D) = σ[ s ∈ S ] D

data Intp (X : Set₁) : Desc → Set₁ where
  in-ṿ : ∀ {n}   → Vec X n                   → Intp X (ṿ n) 
  in-σ : ∀ {S D} → Σ[ s ∈ S ] (Intp X (D s)) → Intp X (σ S D)
  -- hacking ⟦_⟧ to work --without-K

-- bumps everything to Set₁, but that's fine because Lift
 
Ḟ : Desc → Set₁ → Set₁
Ḟ D X = Intp X D

Ḟ-map : ∀ {D} → (A → B) → Ḟ D A → Ḟ D B
Ḟ-map f (in-ṿ x)       = in-ṿ (V.map f x)
Ḟ-map f (in-σ (s , x)) = in-σ (s , Ḟ-map f x)

data μ (D : Desc) : Set₁ where
  con : Ḟ D (μ D) → μ D

DiscreteDesc? : Desc → Type
DiscreteDesc? (ṿ x)   = ⊤
DiscreteDesc? (σ S D) = isSet S × ((s : S) → DiscreteDesc? (D s))

Discreteμ : ∀ {D} → DiscreteDesc? D → Discrete (μ D)
Discreteμ DiscreteD = {!!}

isSetμ : ∀ {D} → DiscreteDesc? D → isSet (μ D)
isSetμ DiscreteD = Discrete→isSet (Discreteμ DiscreteD)

mutual
  fold : {D : Desc} {X : Set₁} → (Ḟ D X → X) → μ D → X
  fold {D = D} f (con ds) = f (mapFold D f ds)

  mapFold : {D : Desc} (D' : Desc) → {X : Set₁} → (Ḟ D X → X) → Intp (μ D) D' → Intp X D'
  mapFold (ṿ n)    f (in-ṿ ds)         = in-ṿ (mapFold-Ṗ f n ds)
  mapFold (σ S D') f (in-σ (s , ds))   = in-σ (s , mapFold (D' s) f ds)

  mapFold-Ṗ : {D : Desc} {X : Set₁} → (Ḟ D X → X) → ∀ n → Vec (μ D) n → Vec X n
  mapFold-Ṗ f zero    _        = []
  mapFold-Ṗ f (suc n) (d ∷ ds) = (fold f d ∷ mapFold-Ṗ f n ds)

map-fold : ∀ {D E} (x : Ḟ E (μ D)) (f : Ḟ D A → A) → mapFold E f x ≡ Ḟ-map (fold f) x
map-fold-Ṗ : ∀ {D} → (f : Ḟ D A → A) → {n : ℕ} → (xs : Vec (μ D) n) → mapFold-Ṗ f n xs ≡ V.map (fold f) xs

map-fold (in-ṿ xs)      f = cong in-ṿ (map-fold-Ṗ f xs)
map-fold (in-σ (s , x)) f = cong in-σ (cong (s ,_) (map-fold x f))

map-fold-Ṗ f []       = refl
map-fold-Ṗ f (x ∷ xs) = cong (fold f x ∷_) (map-fold-Ṗ f xs)


record Alg (X : Set₁) (D : Desc) : Set₁ where
  field
    forget : Ḟ D X → X

open Alg


data Acc {X} (D : Desc) (A : Alg X D) (x : X) : Set₁
data Acc' {X} (D : Desc) (A : Alg X D) : (E : Desc) → Ḟ E X → Set₁

data Acc D A x where
  acc : (y : fiber (A .forget) x) → Acc' D A D (fst y) → Acc D A x

data Acc' D A where
  acc-ṿ : ∀ {n x}             → All (Acc D A) x  → Acc' D A (ṿ n) (in-ṿ x)
  acc-σ : ∀ {S E} {s : S} {x} → Acc' D A (E s) x → Acc' D A (σ S E) (in-σ (s , x))

Wf : ∀ {X} (D : Desc) → Alg X D → Set₁
Wf D A = ∀ x → Acc D A x 


data RecFun (A : Set₁) : Desc → Set₁ where
  recurse : ∀ {n}   → (Vec A n                → A) → RecFun A (ṿ n)
  args    : ∀ {S D} → ((s : S) → Intp A (D s) → A) → RecFun A (σ S D)

funAlg : ∀ {A} → (D : Desc) → RecFun A D → Ḟ D A → A
funAlg (ṿ n) (recurse f) (in-ṿ x) = f x
funAlg (σ S D) (args f) (in-σ (s , x)) = f s x

fix : ∀ {A} → (D : Desc) → RecFun A D → μ D → A
fix D P = fold (funAlg D P)

-- conjecture: if f : F X → X is mono and X is F-accessible, then X is F-initial
-- 1. note that then f is also epi, hence iso
-- 2. X is "not too large"
-- Furthermore, a map to the initial F I = I exists and is forced by accessibility?

thm1 : ∀ {X D} {A : Alg X D} → Wf D A → X → μ D
thm1 wf x = go x (wf x)
  where
  go   : ∀ {X D}   {A : Alg X D} x → Acc D A x → μ D
  go'  : ∀ {X D} E {A : Alg X D} x → Acc' D A E x → Ḟ E (μ D) 
  go'' : ∀ {X D} n {A : Alg X D} (x : Vec X n) → All (Acc D A) x → Vec (μ D) n 

  go x (acc (x' , p) a) = con (go' _ x' a)
  
  go' (ṿ n)   (in-ṿ x)       (acc-ṿ a) = in-ṿ (go'' n x a)
  go' (σ S D) (in-σ (s , x)) (acc-σ a) = in-σ (s , go' (D s) x a)

  go'' zero    []       a        = []
  go'' (suc n) (x ∷ xs) (ax ∷ a) = (go x ax) ∷ go'' n xs a
  -- I can't believe it actually works


record RawFunctor ℓ : Type (ℓ-suc ℓ) where
  field
    F₀   : Type ℓ → Type ℓ
    fmap : (A → B) → F₀ A → F₀ B

open RawFunctor


record Functor ℓ : Type (ℓ-suc ℓ) where
  field
    RawF   : RawFunctor ℓ

  open RawFunctor RawF renaming (F₀ to F; fmap to mapF)
 
  field
    f-id   : (x : F A)
           → mapF id x ≡ x

    -- keeping these as f x = g x: otherwise we'd have to give the types anyway

    f-comp : (g : B → C) (f : A → B) (x : F A)
           → mapF (g ∘ f) x ≡ mapF g (mapF f x) 

open Functor


record Alg' (F : Type ℓ → Type ℓ) : Type (ℓ-suc ℓ) where
  field
    Carrier : Type ℓ
    forget  : F Carrier → Carrier

    isSetAlg : isSet Carrier

open Alg'


Alg→ : (RawF : RawFunctor ℓ) → (A B : Alg' (RawF .F₀)) → Type ℓ
Alg→ RawF AlgA AlgB = Σ[ mor ∈ (AlgA .Carrier → AlgB .Carrier) ] (mor ∘ AlgA .forget) ≡ (AlgB .forget ∘ RawF .fmap mor)


record Initial (C : Type ℓ) (R : C → C → Type ℓ′) (Z : C) : Type (ℓ-max (ℓ-suc ℓ) ℓ′) where
  field
    initiality : ∀ X → isContr (R Z X)

open Initial


InitAlg : (RawF : RawFunctor ℓ) (A : Alg' (RawF .F₀)) → Type (ℓ-suc (ℓ-suc ℓ))
InitAlg RawF A = Initial (Alg' (RawF .F₀)) (Alg→ RawF) A


id-Alg→ : (FunF : Functor ℓ) (X : Alg' (FunF .RawF .F₀)) → Alg→ (FunF .RawF) X X
id-Alg→ FunF X .fst = id
id-Alg→ FunF X .snd = funExt (λ x → cong (X .forget) (sym (FunF .f-id x)))

∘-Alg→ : (FunF : Functor ℓ) (X Y Z : Alg' (FunF .RawF .F₀)) → Alg→ (FunF .RawF) Y Z → Alg→ (FunF .RawF) X Y → Alg→ (FunF .RawF) X Z
∘-Alg→ FunF X Y Z g f .fst = g .fst ∘ f .fst
∘-Alg→ FunF X Y Z g f .snd = funExt λ x → 
  g .fst (f .fst (X .forget x))               ≡⟨ cong (g .fst) (funExt⁻ (f .snd) x) ⟩
  g .fst (Y .forget (mapF (f .fst) x))        ≡⟨ funExt⁻ (g .snd) _ ⟩
  Z .forget (mapF (g .fst) (mapF (f .fst) x)) ≡⟨ cong (Z .forget) (sym (compF _ _ _)) ⟩
  Z .forget (mapF (g .fst ∘ f .fst) x) ∎
    where
    open Functor FunF renaming (RawF to RawF'; f-comp to compF)
    open RawFunctor RawF' renaming (F₀ to F; fmap to mapF)

RawḞ : (D : Desc) → RawFunctor (ℓ-suc ℓ-zero)
RawḞ D .F₀   = Ḟ D
RawḞ D .fmap = Ḟ-map

Ḟ-id : ∀ {D} → (x : Ḟ D A) → Ḟ-map id x ≡ x
Ḟ-id (in-ṿ xs)      = cong in-ṿ (Eq.eqToPath (VP.map-id xs))
Ḟ-id (in-σ (s , x)) = cong in-σ (cong (s ,_) (Ḟ-id x))

Ḟ-comp : ∀ {D} (g : B → C) (f : A → B) (x : Ḟ D A)
       → Ḟ-map (g ∘ f) x ≡ Ḟ-map g (Ḟ-map f x)
Ḟ-comp g f (in-ṿ xs)      = cong in-ṿ (Eq.eqToPath (VP.map-∘ _ _ _))
Ḟ-comp g f (in-σ (s , x)) = cong in-σ (cong (s ,_) (Ḟ-comp g f x))

FunḞ : (D : Desc) → Functor (ℓ-suc ℓ-zero)
FunḞ D .RawF   = RawḞ D
FunḞ D .f-id   = Ḟ-id
FunḞ D .f-comp = Ḟ-comp

μ-Alg : (D : Desc) → DiscreteDesc? D → Alg' (Ḟ D)
μ-Alg D _ .Carrier  = μ D
μ-Alg D _ .forget   = con
μ-Alg D d .isSetAlg = isSetμ d

InitM : (D : Desc) → (d : DiscreteDesc? D) → InitAlg (RawḞ D) (μ-Alg D d)
InitM D d .initiality AlgX = h
  where
  p : Alg→ (RawḞ D) (μ-Alg D d) AlgX
  p .fst = fold (AlgX .forget)
  p .snd = funExt λ x → cong (AlgX .forget) (map-fold x (AlgX .forget))

  p! : ∀ y → p ≡ y
  p! (f , sqr) = ΣPathP (funExt fold≡f , toPathP (isSet→ (AlgX .isSetAlg) _ _ _ sqr))
    where
    fold≡f : ∀ x → p .fst x ≡ f x
    help : ∀ {D} x → Ḟ-map {D = D} (fold (AlgX .forget)) x ≡ Ḟ-map f x
    helpV : ∀ {n} → (xs : Vec (μ D) n) → V.map (fold (AlgX .forget)) xs ≡ V.map f xs

    fold≡f (con x) = sym (funExt⁻ sqr x ∙ cong (AlgX .forget) (sym (map-fold x (AlgX .forget) ∙ help x)))

    help (in-ṿ xs)      = cong in-ṿ (helpV xs)
    help (in-σ (s , x)) = cong in-σ (cong (s ,_) (help x))

    helpV []       = refl
    helpV (x ∷ xs) = cong₂ _∷_ (fold≡f x) (helpV xs)

  h : isContr (Alg→ (RawḞ D) (μ-Alg D d) AlgX)
  h = p , p!


mainResult : (D : Desc) → DiscreteDesc? D → (AlgX : Alg' (Ḟ D)) → InitAlg (RawḞ D) AlgX → AlgX .Carrier ≃ μ D
mainResult D d AlgX InitX = isoToEquiv (iso to from sec ret)
  where
  FunD = FunḞ D
  RawD = FunD .RawF
  AlgM = μ-Alg D d

  toAlg : Alg→ RawD AlgX AlgM
  toAlg = InitX .initiality AlgM .fst

  fromAlg : Alg→ RawD AlgM AlgX
  fromAlg = InitM D d .initiality AlgX .fst

  sectionAlg : ∘-Alg→ FunD AlgM AlgX AlgM toAlg fromAlg ≡ id-Alg→ FunD AlgM
  sectionAlg = isContr→isProp (InitM D d .initiality AlgM) _ _

  retractAlg : ∘-Alg→ FunD AlgX AlgM AlgX fromAlg toAlg ≡ id-Alg→ FunD AlgX
  retractAlg = isContr→isProp (InitX .initiality AlgX) _ _

  to   = fst toAlg
  from = fst fromAlg

  sec : section to from
  sec x = funExt⁻ (cong fst sectionAlg) x

  ret : retract to from
  ret x = funExt⁻ (cong fst retractAlg) x

-- Now all that's left to do is putting back the indices...
-- (Also run an example)
