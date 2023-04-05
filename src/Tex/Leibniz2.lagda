\begin{code}
module Tex.Leibniz2 where


open import Leibniz.Base
open import Leibniz.Properties

open import Extra.Category.WellFounded
open import Extra.Category.Poly
open import Extra.Category
open import Extra.Algebra
open import Extra.ProgOrn.Desc

open import Prelude

open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv

import Cubical.Data.Nat as N
open import Cubical.Data.Bool
open import Cubical.Data.Equality                   as Eq  using () renaming (eqToPath to path)
open import Cubical.Data.Sigma
open import Cubical.Data.Vec


NatD : Desc′
NatD = σ Bool λ
  { false → ṿ 0
  ; true  → ṿ 1 }

Nat : Set₁
Nat = μ NatD

open Algebra

-- this all seems like a bit more work than in Leibniz.Properties (leaving aside the lifts...), but perhaps this is more mechanical/automatable somehow?

pattern zero   = in-σ (false , in-ṿ [])
pattern succ n = in-σ (true  , in-ṿ (n ∷ []))

Leibniz₁ = Lift {j = ℓ-suc ℓ-zero} Leibniz

pattern 0b₁   = lift 0b
_1b₁ : Leibniz₁ → Leibniz₁
_2b₁ : Leibniz₁ → Leibniz₁
(lift x) 1b₁ = lift (x 1b)
(lift x) 2b₁ = lift (x 2b)

-- manual

bsuc₁ : Leibniz₁ → Leibniz₁
bsuc₁ (lift x) = lift (bsuc x)
\end{code}

%<*bsuc'>
\begin{code}
bsuc' : Base Leibniz₁ NatD → Leibniz₁
bsuc' zero     = 0b₁
bsuc' (succ n) = bsuc₁ n

L-Alg : Algebra (Ḟ NatD)
L-Alg .Carrier = Leibniz₁
L-Alg .forget  = bsuc'
\end{code}
%</bsuc'>
mechanical
%<*Peano-View>
\begin{code}
data Peano-View : Leibniz₁ → Type₁ where
  as-zero : Peano-View 0b₁
  as-suc  : (n : Leibniz₁) (v : Peano-View n) → Peano-View (bsuc₁ n)

view-1b : ∀ {n} → Peano-View n → Peano-View (n 1b₁)
view-2b : ∀ {n} → Peano-View n → Peano-View (n 2b₁)
view    : (n : Leibniz₁) → Peano-View n
\end{code}
%</Peano-View>

\begin{code}
view-1b as-zero      = as-suc 0b₁ as-zero
view-1b (as-suc n v) = as-suc _ (view-2b v)

view-2b as-zero      = as-suc (0b₁ 1b₁) (as-suc 0b₁ as-zero)
view-2b (as-suc n v) = as-suc _ (as-suc _ (view-2b v))

view 0b₁           = as-zero
view (lift (n 1b)) = view-1b (view (lift n))
view (lift (n 2b)) = view-2b (view (lift n))
\end{code}

%<*Wf-bsuc>
\begin{code}
view→Acc : ∀ {n} → Peano-View n → Acc NatD bsuc' n
Wf-bsuc : Wf NatD bsuc'
Wf-bsuc n = view→Acc (view n)
\end{code}
%</Wf-bsuc>

\begin{code}
view→Acc as-zero      = acc (in-σ (false , in-ṿ []) , refl) (acc-σ (acc-ṿ []))
view→Acc (as-suc n v) = acc (in-σ (true , in-ṿ (n ∷ [])) , refl) (acc-σ (acc-ṿ (view→Acc v ∷ [])))

-- mechanical ish
inj-bsuc : ∀ x y → bsuc' x ≡ bsuc' y → x ≡ y
inj-bsuc (in-σ (false , in-ṿ [])) (in-σ (false , in-ṿ []))                     _ = refl
inj-bsuc (in-σ (false , in-ṿ [])) (in-σ (true , in-ṿ (lift x ∷ [])))           p = ⊥-rec (0b-not-bsuc x (cong lower p))
inj-bsuc (in-σ (true , in-ṿ (lift x ∷ []))) (in-σ (false , in-ṿ []))           p = ⊥-rec (0b-not-bsuc x (sym (cong lower p)))
inj-bsuc (in-σ (true , in-ṿ (lift x ∷ []))) (in-σ (true , in-ṿ (lift y ∷ []))) p = congS (λ h → in-σ (true , in-ṿ (h ∷ []))) (cong lift (Eq.eqToPath (bsuc-inj x y (Eq.pathToEq (cong lower p)))))
\end{code}

%<*L-is-mu-N>
\begin{code}
L≃μN : _≃_ Leibniz₁ (μ NatD)
L≃μN = Wf+inj≃μ NatD L-Alg Wf-bsuc λ x y p → inj-bsuc x y p
\end{code}
%</L-is-mu-N>
