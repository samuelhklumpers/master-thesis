module IDesc.IDesc where

 
open import Data.Unit 
open import Data.Nat hiding (_⊔_)
open import Data.Fin hiding (lift)
open import Data.Product 

open import Logic.Logic

infixr 30 _`×_

-- Paper: Definition 3.2
data IDesc (I : Set) : Set₁ where
  `var : (i : I) → IDesc I
  `1 : IDesc I
  `Σ : (S : Set )(T : S → IDesc I) → IDesc I
  `Π : (S : Set )(T : S → IDesc I) → IDesc I
  -- Redundant (but first-order) connectives:
  _`×_ : (A B : IDesc I) → IDesc I
  `σ : (n : ℕ)(T : Fin n → IDesc I) → IDesc I

-- Paper: Definition 3.2
⟦_⟧ : {I : Set} → IDesc I → (I → Set) → Set
⟦ `var i ⟧ X = X i
⟦ `1 ⟧ X = ⊤
⟦ A `× B ⟧ X = ⟦ A ⟧ X × ⟦ B ⟧ X
⟦ `σ n T ⟧ X = Σ[ k ∈ Fin n ] ⟦ T k ⟧ X
⟦ `Σ S T ⟧ X = Σ[ s ∈ S ] ⟦ T s ⟧ X
⟦ `Π S T ⟧ X = (s : S) → ⟦ T s ⟧ X

-- Paper typesetting: ⟦_⟧^{→}
⟦_⟧map : ∀{ I X Y} → (D : IDesc  I) → (f : X ⇒ Y) →  ⟦ D ⟧ X → ⟦ D ⟧ Y
⟦ `var i ⟧map f xs = f xs
⟦ `1 ⟧map f tt = tt
⟦ A `× B ⟧map f (a , b) = ⟦ A ⟧map f a , ⟦ B ⟧map f b
⟦ `σ n T ⟧map f (k , xs) = k , ⟦ T k ⟧map f xs
⟦ `Σ S T ⟧map f (s , xs) = s , ⟦ T s ⟧map f xs
⟦ `Π S T ⟧map f xs = λ s → ⟦ T s ⟧map f (xs s)

{-
This definition does not play well with unification:

func : (I J : Set) → Set₁
func I J = J → IDesc I

Instead, we sugar it in a record, as follows:
-}

-- Paper: Definition 3.3
record func (I J : Set) : Set₁ where
  constructor mk
  field
    out : J → IDesc I

-- Paper: Definition 3.3
-- Paper typesetting: ⟦_⟧
⟦_⟧func : {I J : Set} → func  I J → (I → Set) → (J → Set)
⟦ D ⟧func X j = ⟦ func.out D j ⟧ X 

-- Paper: Definition 3.3
-- Paper typesetting: ⟦_⟧^{→}
⟦_⟧fmap : ∀{ I J X Y} → (D : func I J) → (f : X ⇒ Y) →  ⟦ D ⟧func X ⇒ ⟦ D ⟧func Y
⟦ D ⟧fmap f {j} xs = ⟦ func.out D j ⟧map f xs
