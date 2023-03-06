{-# OPTIONS --cubical #-}

module Trampoline where

open import Prelude hiding (⌊_⌋; inspect)
open import Cubical.Data.Equality as Eq

open import Data.List


RDesc : Set → Set₁
RDesc I = Σ[ S ∈ Set ] (S → List I)

Desc : Set → Set₁
Desc I = I → RDesc I

Prod : {I : Set} → List I → (I → Set) → Set
Prod []       X = ⊤
Prod (i ∷ is) X = X i × Prod is X

⟦_⟧ : {I : Set} → RDesc I → (I → Set) → Set
⟦ D ⟧ X = Σ[ s ∈ fst D ] Prod (snd D s) X

Base : {I : Set} → Desc I → (I → Set) → (I → Set)
Base D X i = ⟦ D i ⟧ X

data μ {I : Set} (D : Desc I) (i : I) : Set where
  con : Base D (μ D) i → μ D i

NatD : Desc ⊤
NatD tt = Bool , λ { false → [] ; true → [ tt ] }

data Inv {A B : Set} (f : A → B) : B → Set where
  ok : ∀ x → Inv f (f x)

RAddDesc : {I : Set} → RDesc I → Set₁
RAddDesc D = fst D → Set

AddDesc : {I : Set} (D : Desc I) → Set₁
AddDesc D = ∀ i → RAddDesc (D i)

toRDesc : {I : Set} → (D : RDesc I) → RAddDesc D → RDesc I
toRDesc D r = (Σ[ s ∈ fst D ] (r s)) , snd D ∘ fst

toDesc : {I : Set} → (D : Desc I) → AddDesc D → Desc I
toDesc D A i = toRDesc (D i) (A i)

NatD-ListD : Type → AddDesc NatD
NatD-ListD A tt = λ { false → ⊤ ; true → A }

ListD : Type → Desc ⊤
ListD A = toDesc NatD (NatD-ListD A)

--ROrnDesc : {I : Set} (J : Set) (e : J → I) → RDesc I → Set
--ROrnDesc J e D = (s : fst D) → Prod (snd D s) (Inv e) 

plus : (A : AddDesc NatD) → (i : ⊤) → μ (toDesc NatD A) i → μ (toDesc NatD A) i → μ (toDesc NatD A) i
plus A tt (con ((false , b) , c)) (con ((x     , y) , z)) = con ((x , y) , z)
plus A tt (con ((true  , b) , c)) (con ((false , y) , z)) = con ((true , b) , c)
plus A tt (con ((true  , b) , c)) (con ((true  , y) , z)) = con ((true , b) , ((plus A tt (fst c) (fst z)) , _))

-- of course, this is pointless, because every AddDesc over NatD is a list one way or another..
