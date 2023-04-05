module Logic.Logic where



open import Data.Unit

infixr 5 _⇒_

Pow : Set → Set₁
Pow I = I → Set

_⇒_ : ∀{I : Set} → (P Q : Pow I) → Set
P ⇒ Q = {i : _} → P i → Q i

-- Paper: Remark 4.2
data _⁻¹_ {A B : Set}(f : A → B) : Pow B where
  inv : (a : A) → f ⁻¹ (f a)
