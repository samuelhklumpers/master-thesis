module Ornament.Examples where

open import Agda.Primitive public
  using    ( Level
           ; SSet )
  renaming ( lzero to ℓ-zero
           ; lsuc  to ℓ-suc
           ; _⊔_   to ℓ-max
           ; Set   to Type
           ; Setω  to Typeω )

--open import Data.Unit.Polymorphic
open import Data.Unit
open import Data.Product
open import Data.Sum
open import Data.Nat
open import Level using (Lift; lift)
open import Function.Base 
open import Relation.Binary.PropositionalEquality

open import Ornament.DescL
open import Ornament.Number


private variable
  a b c : Level


module Descriptions where
  NatD : Desc ⊤ ∅ ℓ-zero
  NatD = 𝟙 _ ∷ rec (const tt) id (𝟙 _) ∷ []

  VecD : Desc ℕ ∅ ℓ-zero
  VecD = 𝟙 (const 0) ∷ σf (const ℕ) (rec proj₂ id (𝟙 (suc ∘ proj₂))) ∷ []

  data Node (A : Type a) : Type a where
    two   : A → A     → Node A
    three : A → A → A → Node A

  DigitD : Desc ⊤ (∅ ▷ const Type) ℓ-zero
  DigitD = σf′ proj₂ (𝟙 _)
         ∷ σf′ proj₂ (σf′ proj₂ (𝟙 _))
         ∷ σf′ proj₂ (σf′ proj₂ (σf′ proj₂ (𝟙 _)))
         ∷ []

  FingerD : Desc ⊤ (∅ ▷ const Type) ℓ-zero
  FingerD = 𝟙 _
          ∷ σf′ proj₂ (𝟙 _)
          ∷ σd′ _ id DigitD (rec _ (λ { (x , y) → x , Node y }) (σd′ _ id DigitD (𝟙 _)))
          ∷ []

  FingerTree = μ FingerD

  ex-1 : FingerTree (_ , ℕ) _
  ex-1 = con (inj₂ (inj₂ (inj₁ (con (inj₁ (0 , lift refl)) , con (inj₂ (inj₁ (two 1 2 , lift refl))) , con (inj₂ (inj₁ (3 , 4 , lift refl))) , lift refl))))


module Numbers where  
  NatD : NDesc
  NatD = +n 0 ∷ (((rec Id) *∷ (*n 1)) +∷ (+n 1)) ∷ []

  Nat = μ (Fun NatD) (_ , ⊤) _

  Nat-2 : Nat
  Nat-2 = con (inj₂ (inj₁ (con (inj₂ (inj₁ (con (inj₁ (lift refl)) , lift refl))) , lift refl)))

  2≡2 : eval2 NatD Nat-2 (const 1000) ≡ 2
  2≡2 = refl

  DigitD : NDesc
  DigitD = ((par *∷ *n 1) +∷ +n 0)
         ∷ ((par *∷ *n 2) +∷ +n 0)
         ∷ ((par *∷ *n 3) +∷ +n 0)
         ∷ []

  NodeD : NDesc
  NodeD = ((par *∷ *n 2) +∷ +n 0) ∷ ((par *∷ *n 3) +∷ +n 0) ∷ []

  FingerD : NDesc
  FingerD = +n 0
          ∷ +n 1
          ∷ ((num DigitD *∷ *n 1) +∷ ((rec NodeD *∷ *n 1) +∷ ((num DigitD *∷ *n 1) +∷ (+n 0))))
          ∷ []

--   FtD : NDesc
--   FtD = constant 0 ∷ leaf (var par)  ∷ node ⊕ (leaf (num var DtD)) (leaf (rec NodeD)) ∷ []

--   Ft = μ FtD top

--   {-
--   F-23 : Ft
--   F-23 = con (inj₂ (inj₂ (inj₁ (con (inj₂ (inj₂ (inj₂ (inj₂ (inj₁ _))))) , con (inj₂ (inj₂ (inj₁ (con {!help!} , con (inj₁ _)))))))))
--   -}

--   F-4 : Ft
--   F-4 = con (inj₂ (inj₂ (inj₁ (con (inj₁ _) , con (inj₂ (inj₁ (inj₁ _)))))))



-- NatD : Desc (⊤ {ℓ-zero}) ∅
-- NatD _ = 𝟙 ⊕ tt rec id ⊗ 𝟙 ⊕ 𝟘

-- VecD : Desc ℕ (∅ ▷ const Type)
-- VecD zero    = 𝟙 ⊕ 𝟘
-- VecD (suc n) = (fld proj₂ ⊗ (n rec id ⊗ 𝟙)) ⊕ 𝟘


-- DigitD : Desc (⊤ {ℓ-zero}) (∅ ▷ const Type)
-- DigitD _ = (fld proj₂ ⊗ 𝟙)
--          ⊕ (fld proj₂ ⊗ fld proj₂ ∘ proj₁ ⊗ 𝟙)
--          ⊕ (fld proj₂ ⊗ fld proj₂ ∘ proj₁ ⊗ fld proj₂ ∘ proj₁ ∘ proj₁ ⊗ 𝟙)
--          ⊕ 𝟘

-- FingerD : Desc (⊤ {ℓ-zero}) (∅ ▷ const Type)
-- FingerD _ = 𝟙
--           ⊕ (fld proj₂ ⊗ 𝟙)
--           ⊕ tt rec mapTel id (const Type) (const Node) ⊗ (tt & id dsc DigitD ⊗′ (tt & id dsc DigitD ⊗ 𝟙))
--           ⊕ 𝟘

-- ListO : Orn ⊤ id (∅ ▷ const Type) (const tt) NatD 
-- ListO (ok _) = 𝟙 ⊕ ((Δf proj₂ {!!}) ⊕ 𝟘)

