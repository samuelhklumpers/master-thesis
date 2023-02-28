```
{-# OPTIONS --cubical --copatterns --allow-unsolved-metas #-}

module Initiality where

open import Prelude hiding (⌊_⌋)
open import ProgOrn.Ornaments hiding (NatD) renaming (_⇉_ to _i⇉_) 

open import Data.List
import Data.Vec as V

import Cubical.Data.Nat as N
import Data.Fin as Fin
open import Data.Bool
open import Data.Fin hiding (toℕ)
```


Here is an idea I could have noticed earlier.
Usually when we're proving A ≃ B we spend most of the time struggling with one of the two directions,
or writing down endless chains of lemma's to prove that we actually have sections/retractions.

Typically, however, we know a bit more about A and B which we often ignore.
Particularly, when A or B is given as an interpretation of a description, we get heaps of information for free.
(Which, granted, we are half assuming, half ignoring in the usual setup where A or B is a simple inductive).

That is, we know that an interpretation is an initial algebra for the base functor of the description.
If we can show that the other side is also initial for this functor, then we should get A ≃ B "for free".

Let's try to run this idea through.
Recall the description of natural numbers
```
NatD : Desc ⊤
NatD tt = σ Bool (λ
  { false → ṿ []
  ; true  → ṿ [ tt ] })
```

The beginner's quest towards univalence is then to show Nat ≃ Bin, therefore Nat ≡ Bin.
Instead of diving at _≃_ directly, let's investigate what an algebra for NatD looks like.

Let us spell out the definition of an algebra for an (indexed) functor. (We can probably pick this out of some category theory library)
```
IType : Type → Type₁
IType I = I → Type

IFun : Type → Type₁ 
IFun I = IType I → IType I

_⇉_ : ∀ {I} (A B : IType I) → Type
A ⇉ B = ∀ i → A i → B i

record Alg {I} (F : IFun I) : Type₁ where
  field
    Carrier : IType I
    forget  : F Carrier ⇉ Carrier

open Alg
```

The base functor for NatD is something like NatF X = 1 + X,
and an algebra for NatF is a Type N equipped with a map 1 + N → N.
E.g. for ℕ we have (zero, suc) : 1 + ℕ → ℕ.

When we write down an inductive datatype, we are essentially encoding a base functor,
and assuming that the type is the initial algebra for this base functor.

Let us define some terms necessary to characterize such algebras:
A morphism of algebras is
```
record RawIFunctor {I} (F : IFun I) : Type₁ where
  field
    fmap : ∀ {X Y} → X ⇉ Y → F X ⇉ F Y

open RawIFunctor


_∘I_ : ∀ {I} {A B C : IType I} → B ⇉ C → A ⇉ B → A ⇉ C
g ∘I f = λ i x → g i (f i x)

record IFunctor {I} {F : IFun I} (RawF : RawIFunctor F) : Type₁ where
  field
    f-id   : ∀ {X : IType I} → ∀ i (x : F X i) → RawF .fmap (λ i x → x) i x ≡ x
    f-comp : ∀ {X Y Z : IType I} → (g : Y ⇉ Z) (f : X ⇉ Y) → ∀ i (x : F X i) → RawF .fmap (g ∘I f) i x ≡ RawF .fmap g i (RawF .fmap f i x) 

open IFunctor

{-
record _Alg→_ {I} {F : IFun I} {{FunF : RawIFunctor F}} (A B : Alg F) : Type₁ where
  field
    mor    : A .Carrier ⇉ B .Carrier
    square : Path (F (A .Carrier) ⇉ B .Carrier) (mor ∘ A .forget) (B .forget ∘ FunF .fmap mor)
-}


Alg→ : ∀ {I} {F : IFun I} (FunF : RawIFunctor F) → Alg F → Alg F → Type
Alg→ FunF A B = Σ[ mor ∈ A .Carrier ⇉ B .Carrier ] (mor ∘I A .forget) ≡ (B .forget ∘I FunF .fmap mor)
```

I.e. it is fairly literally "an arrow respecting the algebra structure".

An initial algebra is simply an initial object in the category of algebras
```
record Initial {ℓ ℓ′} (C : Type ℓ) (R : C → C → Type ℓ′) (Z : C) : Type (ℓ-max (ℓ-suc ℓ) ℓ′) where
  field
    initiality : ∀ X → isContr (R Z X)

open Initial

InitAlg : ∀ {I} {F : IFun I} (FunF : RawIFunctor F) (A : Alg F) → Type (ℓ-suc (ℓ-suc ℓ-zero))
InitAlg {F = F} FunF A = Initial (Alg F) (Alg→ FunF) A
```

Evidently, the least fixpoint μ of a base functor should be an initial algebra for that functor
```
Nat : ⊤ → Type
Nat = μ NatD

explicit : ∀ {I} {A B : IType I} → A i⇉ B → A ⇉ B
explicit f = λ i x → f x

Nat-Alg : Alg (Ḟ NatD) -- mechanical
Carrier Nat-Alg = Nat
forget  Nat-Alg = explicit con

module _ {I} where
  map-Ṗ : ∀ is {X Y : IType I} → X ⇉ Y → Ṗ is X → Ṗ is Y
  map-Ṗ []       f _  = _
  map-Ṗ (i ∷ is) f px = f i (fst px) , map-Ṗ is f (snd px)

  map-⟦⟧ : ∀ (r : RDesc I) {X Y : IType I} → X ⇉ Y → ⟦ r ⟧ X → ⟦ r ⟧ Y
  map-⟦⟧ (ṿ is)  f x = map-Ṗ is f x
  map-⟦⟧ (σ S D) f x = fst x , map-⟦⟧ (D (fst x)) f (snd x)

  module _ (D : Desc I) where
    map-Ḟ : ∀ {X Y : IType I} → X ⇉ Y → Ḟ D X ⇉ Ḟ D Y
    map-Ḟ f i x = map-⟦⟧ (D i) f x

    RawIFunctorḞ : RawIFunctor (Ḟ D)
    fmap RawIFunctorḞ = map-Ḟ

NatF = RawIFunctorḞ NatD

Nat-Init : InitAlg NatF Nat-Alg  -- mechanical?
Nat-Init .initiality X = h
  where
  m : ∀ i → Nat i → X .Carrier i
  m i (con (false , _))     = X .forget i (false , _)
  m i (con (true  , n , _)) = X .forget i (true  , m i n , _)

  s : ∀ i n → m i (con n) ≡ X .forget i (map-Ḟ NatD m i n)
  s i (false , _)     = refl
  s i (true  , n , _) = refl

  h : isContr (Alg→ NatF Nat-Alg X)
  h .fst .fst = m
  h .fst .snd = λ i j x → s j x i
  h .snd = k
    where
    k : (y : Alg→ NatF Nat-Alg X) → fst h ≡ y
    k y = ΣPathP ((λ i j x → e j x i) , {!annoying but we can ask that all algebras are sets!})
      where
      e : ∀ i x → m i x ≡ fst y i x
      e i (con (false , _))     = sym (funExt⁻ (funExt⁻ (snd y) i) (false , _)) 
      e i (con (true  , n , _)) = cong (λ z → X .forget i (true , z , _)) (e i n) ∙ sym (funExt⁻ (funExt⁻ (snd y) i) (true , n , _))
```

On the other hand, if there were another initial algebra for this functor, then the two are necessarily isomorphic, as they would be initial objects, hence isomorphic, in the category of algebras.
```
Nat-Functor : IFunctor NatF
Nat-Functor = {!ah!}

identity-Alg→ : (X : Alg (Ḟ NatD)) → Alg→ NatF X X
fst (identity-Alg→ X) = λ i x → x
snd (identity-Alg→ X) = funExt (λ y → funExt λ x → cong (X .forget y) (sym (Nat-Functor .f-id _ x)))

∘-Alg→ : (X Y Z : Alg (Ḟ NatD)) → Alg→ NatF Y Z → Alg→ NatF X Y → Alg→ NatF X Z
fst (∘-Alg→ X Y Z g f) = fst g ∘I fst f
snd (∘-Alg→ X Y Z g f) =  
  (fst g ∘I fst f) ∘I X .forget ≡⟨ refl ⟩
  fst g ∘I (fst f ∘I X .forget) ≡⟨ {!!} ⟩
  fst g ∘I (Y .forget ∘I NatF .fmap (fst f)) ≡⟨ refl ⟩
  (fst g ∘I Y .forget) ∘I NatF .fmap (fst f) ≡⟨ {!!} ⟩
  (Z .forget ∘I NatF .fmap (fst g)) ∘I NatF .fmap (fst f) ≡⟨ refl ⟩
  Z .forget ∘I (NatF .fmap (fst g) ∘I NatF .fmap (fst f)) ≡⟨ {!!} ⟩
  Z .forget ∘I NatF .fmap (fst g ∘I fst f) ∎

mainResult : (X : Alg (Ḟ NatD)) → InitAlg NatF X → X .Carrier tt ≃ Nat-Alg .Carrier tt
mainResult X init = isoToEquiv (iso to from sec ret)
  where
  toAlg : Alg→ NatF X Nat-Alg
  toAlg = fst (init .initiality Nat-Alg)

  fromAlg : Alg→ NatF Nat-Alg X
  fromAlg = fst (Nat-Init .initiality X)

  sectionAlg : ∘-Alg→ Nat-Alg X Nat-Alg toAlg fromAlg ≡ identity-Alg→ Nat-Alg
  sectionAlg = isContr→isProp (Nat-Init .initiality Nat-Alg) _ _

  retractAlg : ∘-Alg→ X Nat-Alg X fromAlg toAlg ≡ identity-Alg→ X
  retractAlg = isContr→isProp (init .initiality X) _ _

  to   = fst toAlg tt
  from = fst fromAlg tt

  sec : section to from
  sec x = funExt⁻ (funExt⁻ (cong fst sectionAlg) tt) x

  ret : retract to from
  ret x = funExt⁻ (funExt⁻ (cong fst retractAlg) tt) x
```

Now we only have to prove Init-Alg NatF Bin-Alg...
