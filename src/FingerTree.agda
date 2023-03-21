module FingerTree where

open import Cubical.Data.Nat
open import Cubical.Data.List
open import ProgOrn.Ornaments
open import Cubical.Data.Unit renaming (Unit to ⊤)
open import Prelude hiding (⌊_⌋; _◁_)


-- a wild stab at fingertrees


data Three : Type where
  one two three : Three

data Four : Type where
  one two three four : Four

FingerNumberD : Desc ⊤
FingerNumberD tt = σ Three λ
  { one   → ṿ []
  ; two   → ṿ []
  ; three → Four σ′ Four σ′ (ṿ [ tt ]) }

data Digit (A : Type) : Four → Type where
  one   : A → Digit A one
  two   : A → A → Digit A two
  three : A → A → A → Digit A three
  four  : A → A → A → A → Digit A four

data Node (A : Type) : Type where
  node2 : A → A     → Node A
  node3 : A → A → A → Node A

power : ℕ → (A → A) → A → A
power ℕ.zero    f = λ x → x
power (ℕ.suc n) f = f ∘ power n f

FingerNumber-FingerTreeOD : Type → OrnDesc ℕ ! FingerNumberD
FingerNumber-FingerTreeOD A (ok n) = σ Three (λ
  { one   → ṿ _
  ; two   → Δ[ _ ∈ power n Node A ] ṿ _
  ; three → σ[ i ∈ Four ] σ[ j ∈ Four ] Δ[ _ ∈ Digit (power n Node A) i ] Δ[ _ ∈ Digit (power n Node A) j ] ṿ (ok (suc n) , _)  })

-- that didn't take very long
-- (but now to exploit it ...)

FingerTree′ : Type → ℕ → Type
FingerTree′ A n = μ ⌊ FingerNumber-FingerTreeOD A ⌋ n

FingerTree : Type → Type
FingerTree A = FingerTree′ A 0

-- I regret this I kind of want to use practical generic programming now
_◁_ : ∀ {n} → power n Node A → FingerTree′ A n → FingerTree′ A n
a ◁ con (one   , _) = con (two , a , _)
a ◁ con (two   , b , _) = con (three , one , one , (one a) , (one b) , (con (one , _) , _))
a ◁ con (three , .one , j , one x , r , c) = con (three , (two , j , two a x , r , c))
a ◁ con (three , .two , j , two x x₁ , r , c) = con (three , (three , j , three a x x₁ , r , c))
a ◁ con (three , .three , j , three x x₁ x₂ , r , c) = con (three , (four , j , four a x x₁ x₂ , r , c))
a ◁ con (three , .four , j , four x x₁ x₂ x₃ , r , c , _) = con (three , (two , j , two a x , r , ((node3 x₁ x₂ x₃ ◁ c) , _)))

-- sweet though

