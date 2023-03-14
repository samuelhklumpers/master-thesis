-- completely unused "induction" principles for μ
module Extra.ProgOrn.Mu.Induction where

open import Cubical.Data.Nat
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.Data.Empty
open import Cubical.Data.Vec as V hiding (map)
open import Cubical.Foundations.Prelude
open import Cubical.Relation.Nullary

import Cubical.Data.Equality as Eq

open import Function.Base
open import Data.Product using (uncurry)

open import Extra.ProgOrn.Desc


private variable
    ℓ ℓ′ : Level
    A B  : Type ℓ
    D E  : Desc′


□ : (D : Desc′) (P : A → Type ℓ) (x : Base A D) → Type ℓ
□ (ṿ n)   P (in-ṿ xs)      = All P xs
□ (σ S D) P (in-σ (s , x)) = □ (D s) P x

module _ (P : μ D → Type ℓ)
         (alg : ∀ x → □ D P x → P (con x)) where
         
  induction : (d : μ D) → P d
  induction-ṿ : ∀ {n} → (xs : Vec (μ D) n) → All P xs
  induction-□ : (d : Base (μ D) E) → □ E P d

  induction (con x) = alg x (induction-□ x)

  induction-ṿ []       = tt*
  induction-ṿ (x ∷ xs) = (induction x) , (induction-ṿ xs)

  induction-□ (in-ṿ xs)      = induction-ṿ xs
  induction-□ (in-σ (s , x)) = induction-□ x


□′ : (D : Desc′) (Q : (S : Type) → S → Type ℓ) (P : A → Type ℓ′) (x : Base A D) → Type (ℓ-max ℓ ℓ′)
□′ {ℓ = ℓ} (ṿ n)   Q P (in-ṿ xs) = Lift {j = ℓ} (All P xs)
□′ (σ S D) Q P (in-σ (s , x))    = Q S s × □′ (D s) Q P x

module _ (Q : (S : Type) → S → Type ℓ) where
  AllD : Desc′ → Type ℓ
  AllD (ṿ n)   = Unit*
  AllD (σ S D) = ∀ s → Q S s × AllD (D s)

  module _ (P : μ D → Type ℓ′)
           (ad : AllD D)
           (alg : ∀ x → □′ D Q P x → P (con x))
           where

    data Below : Desc′ → Desc′ → Type (ℓ-suc ℓ) where
      self : ∀ {D}                         → Below D     D
      down : ∀ {D S E s} → Below (σ S E) D → Below (E s) D 

    Below→Q : ∀ {E} → Below E D → AllD D → AllD E
    Below→Q self     g = g
    Below→Q (down b) g = Below→Q b g _ .snd

    induction′ : (d : μ D) → P d
    induction′-□ : Below E D → (d : Base (μ D) E) → □′ E Q P d
    induction′-ṿ : ∀ {n} → (xs : Vec (μ D) n) → All P xs

    induction′ (con x) = alg x (induction′-□ self x)

    induction′-□ b (in-ṿ xs)      = lift (induction′-ṿ xs)
    induction′-□ b (in-σ (s , x)) = Below→Q b ad s .fst , induction′-□ (down b) x

    induction′-ṿ []       = tt*
    induction′-ṿ (x ∷ xs) = (induction′ x) , (induction′-ṿ xs)
    
-- move to Extra.Dec
×-Dec : Dec A → Dec B → Dec (A × B)
×-Dec (yes p) (yes p₁) = yes (p , p₁)
×-Dec (yes p) (no ¬p) = no (λ z → ¬p (snd z))
×-Dec (no ¬p) (yes p) = no (λ z → ¬p (fst z))
×-Dec (no ¬p) (no ¬p₁) = no (λ z → ¬p₁ (snd z))

mapDec′ : (f : A → B) (g : B → A) → Dec A → Dec B
mapDec′ f g = mapDec f (_∘ g)

-- ??
J⁻ : ∀ {x y : A} → (P : ∀ y → x ≡ y → Type ℓ) (p : x ≡ y) (d : P y p) → P x refl
J⁻ P p d = transport (λ i → P (p (~ i)) (λ j → p (~ i ∧ j))) d

isSet→cong-snd : {A : Type ℓ} {B : A → Type ℓ′} → isSet A → (a : A) (b b' : B a) → Path (Σ A B) (a , b) (a , b') → b ≡ b'
isSet→cong-snd {A = A} {B = B} isSetA a b b' p = sym (substRefl {A = A} {B = B} {x = a} b) ∙ subst (λ q → subst B q b ≡ b') (isSetA _ _ (h .fst) refl) (fromPathP (h .snd))
  where
  h = PathPΣ p

Discreteμ : AllD (λ S _ → Discrete S) D → Discrete (μ D)
Discreteμ {D = D'} d = induction′ (λ S _ → Discrete S) (λ x → (y : μ D') → Dec (x ≡ y)) d λ { x a (con y) → mapDec′ (cong con) (cong unCon) (go x a y) }
  where
  go : (x : Base (μ D) E) → □′ E (λ S _ → Discrete S) (λ x → ∀ y → Dec (x ≡ y)) x → ∀ y → Dec (x ≡ y)
  go (in-ṿ x) a (in-ṿ y) = mapDec′ (cong in-ṿ) (cong un-ṿ) (go' x y (lower a))
    where
    go' : ∀ {m} (x y : Vec (μ D) m) → All (λ y → (z : μ D) → Dec (y ≡ z)) x → Dec (x ≡ y)
    go' []       []       a = yes refl
    go' (x ∷ xs) (y ∷ ys) a = mapDec′ (uncurry (λ p → cong₂ _∷_ p {u = xs} {v = ys})) (λ p → (cong head p) , (cong tail p)) (×-Dec (a .fst y) (go' xs ys (a .snd)))

  go (in-σ x) a (in-σ y) = mapDec′ (cong in-σ) (cong un-σ) (go' x y (a .fst) (a .snd))
    where
    go' : ∀ {S : Type} {E : S → Desc′} (x y : Σ[ s ∈ S ] (Base (μ D) (E s))) → Discrete S → □′ (E (x .fst)) (λ S _ → Discrete S) (λ z → (w : μ D) → Dec (z ≡ w)) (x .snd) → Dec (x ≡ y)
    go' (s , x) (t , y) Sdis a with Sdis s t
    ... | no ¬p = no (λ q → ¬p (cong fst q))
    ... | yes p with Eq.pathToEq p
    ... | Eq.refl = mapDec′ (cong (s ,_)) (isSet→cong-snd (Discrete→isSet Sdis) s x y) (go x a y)

isSetμ : ∀ {D} → AllD (λ S _ → Discrete S) D → isSet (μ D)
isSetμ DiscreteD = Discrete→isSet (Discreteμ DiscreteD)





-- in conclusion, writing eliminators for μ is fairly painful and generally does not achieve what you wanted anyway

{-
-- rip lol
□′-2 : (D : Desc′) (Q : (S : Type) → (s t : S) → Type ℓ) (P : A → B → Type ℓ) (x : Base A D) (y : Base B D) → Type ℓ
□′-2 (ṿ n)   Q P (in-ṿ xs)      (in-ṿ ys)      = All (uncurry P) (zipWith _,_ xs ys)
□′-2 (σ S D) Q P (in-σ (s , x)) (in-σ (t , y)) = Q S s t × □′-2 (D s) Q P {!!} {!!}

AllD-Lift : ∀ {Q : ∀ S → S → Type ℓ} D → AllD Q D → AllD (λ S s → Lift {j = ℓ′} (Q S s)) D
AllD-Lift (ṿ n)   ad   = tt*
AllD-Lift (σ S D) ad s = (lift (fst (ad s))) , (AllD-Lift (D s) (snd (ad s)))


-- the less useful variant of elim2
induction′-2 : (Q : (S : Type) → S → Type ℓ) (P : (x y : μ D) → Type ℓ) → AllD Q D
             → (∀ x y → □′ D Q (λ y → P (con x) y) y → P (con x) (con y))
             → (x y : μ D) → P x y
induction′-2 {D = D} Q P ad f x = lower {j = ℓ-suc ℓ-zero} $ induction′ (λ S s → Lift {j = ℓ-suc ℓ-zero} (Q S s)) (λ x → Lift (∀ y → P x y)) (AllD-Lift _ ad) go x 
  where
  go : ∀ x → □′ D (λ S s → Lift {j = ℓ-suc ℓ-zero} (Q S s)) (λ x → Lift {j = ℓ-suc ℓ-zero} (∀ y → P x y)) x → Lift {j = ℓ-suc ℓ-zero} (∀ y → P (con x) y)
  go x a = lift (induction′ Q (λ y → P (con x) y) ad (f x))


isSetμ : AllD (λ S _ → isSet S) D → isSet (μ D)
isSetμ {D = D} ad = {!go!}
  where
  h : ∀ x y → □′ D (λ S z → Lift (isSet S)) (λ y → (p q : x ≡ unCon y) → p ≡ q) y → (p q : x ≡ y) → p ≡ q
  h (in-ṿ xs)      (in-ṿ ys)      a = {!!}
  h (in-σ (s , x)) (in-σ (t , y)) a = {!!}

  -- this would work if this eliminator was not useless
  go : (x y : μ D) (p q : unCon x ≡ unCon y) → p ≡ q
  go = induction′-2 (λ S _ → Lift {j = ℓ-suc ℓ-zero} (isSet S)) (λ x y → (p q : unCon x ≡ unCon y) → p ≡ q) (AllD-Lift _ ad) h
-}
