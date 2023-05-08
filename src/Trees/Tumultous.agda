{-# OPTIONS --type-in-type --guardedness #-}

module Trees.Tumultous where

open import Relation.Binary.PropositionalEquality hiding (J)
open import Data.Unit
open import Function using (const)


-- we want to be able to 
-- 1. describe nested types
-- 2. compose descriptions
-- 3. inspect the parameters of a description

-- this means we have to
-- 1. be able to give expressions as parameters
-- 2. give descriptions as fields
-- 3. have a semi-closed universe



-- contexts are assignments of values to parameters
data Cxt : Set
data TypeExpr : Cxt → Set 

private variable
  I J : Set
  Γ Δ : Cxt
  S T : TypeExpr Γ


infixr 10 _⊗_
infixr 9  _⊕_

infixl 10 _▷_
infix  9  _∋_



record RDesc (I : Set) (Γ : Cxt) : Set

data Cxt where
  ∅   : Cxt
  _▷_ : (Γ : Cxt) (S : TypeExpr Γ) → Cxt

data _∋_ : Cxt → TypeExpr Γ → Set where
  𝕧 : (Γ ▷ S) ∋ S
  𝕤 : Γ ∋ S → Γ ▷ T ∋ S

data Expr : (Γ : Cxt) → TypeExpr Γ → Set

-- expressions in a context
data TypeExpr where
  set : TypeExpr Γ
  exp : Expr Γ set → TypeExpr Γ
  sub : TypeExpr (Γ ▷ S) → Expr Γ S → TypeExpr Γ
  weak : TypeExpr Γ → TypeExpr (Γ ▷ S)

data Expr where
  𝕧-i : (i : Γ ∋ S) → Expr Γ set
  descK : RDesc I Γ → I → Expr Γ set

⟦_⟧Cxt : Cxt → Set
⟦ Γ ⟧Cxt = ⊤

-- a constructor description lists the fields of a constructor
data CDesc (I : Set) (Γ : Cxt) : Set where
  1′  : (⟦ Γ ⟧Cxt → I) → CDesc I Γ
  _⊗_ : (S : TypeExpr Γ) → CDesc I (Γ ▷ S) → CDesc I Γ

-- a description lists the constructors of a datatype
data Desc (I : Set) (Γ : Cxt) : Set where
  0′  : Desc I Γ
  _⊕_ : CDesc I Γ → Desc I Γ → Desc I Γ
  
record RDesc I Γ where
  coinductive
  constructor i-d
  field
    e-d : Desc I Γ

open RDesc

NatD : RDesc ⊤ ∅
NatD .e-d = 1′ (const tt) ⊕ exp (descK NatD tt) ⊗ 1′ (λ _ → tt) ⊕ 0′
--                                                    ^
--                can't use const here otherwise the termination checker gets fussy

PairD : RDesc ⊤ (∅ ▷ set)
PairD .e-d = exp (𝕧-i 𝕧) ⊗ 1′ (λ _ → tt) ⊕ 0′

PerfectD : RDesc ⊤ (∅ ▷ set)
PerfectD .e-d = exp (𝕧-i 𝕧) ⊗ 1′ (λ _ → tt) ⊕ sub (weak (exp (descK PerfectD tt))) (descK PairD tt) ⊗ 1′ (λ _ → tt) ⊕ 0′

EitherD : RDesc ⊤ (∅ ▷ set ▷ set)
EitherD .e-d = exp (𝕧-i (𝕤 𝕧)) ⊗ 1′ (const tt) ⊕ exp (𝕧-i 𝕧) ⊗ 1′ (const tt) ⊕ 0′

-- no parameters in indices, no identity types :(
-- EqD : RDesc 
