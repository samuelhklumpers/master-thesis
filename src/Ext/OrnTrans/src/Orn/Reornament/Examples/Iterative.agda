module Orn.Reornament.Examples.Iterative (A B C : Set) where



open import Data.Unit
open import Data.Nat
open import Data.Bool
open import Data.Product

open import Relation.Binary.PropositionalEquality

open import Level renaming (zero to zeroL ; suc to sucL)

open import Logic.Logic
open import Logic.IProp
open Logic.IProp.Applicative {zeroL}

open import IDesc.IDesc
open import IDesc.Fixpoint

open import Orn.Ornament
open import Orn.Reornament

-- Paper: Remark 4.33

test : func ⊤ ⊤
test = mk (λ x → `Σ A (λ a → 
                 `Π B λ b → 
                 `Σ Bool λ x → 
                 `var tt))

forget : ℕ → ⊤
forget n = tt

testO : orn test forget forget
testO = mk (λ n → `Σ (λ a → 
                  insert C (λ c → 
                  `Π (λ b → 
                  deleteΣ true 
                         (`var (inv (ℕ.suc n)))))))

postulate 
  a : A
  b : B
  c : C
  n : ℕ
  x : Bool
  xs : μ test tt

reorn1 : orn ⟦ testO ⟧orn proj₁ proj₁
reorn1 = ⌈ testO ⌉

reorn1O : Orn proj₁ (func.out ⟦ testO ⟧orn n)
reorn1O = orn.out reorn1 (n , ⟨ a , (λ _ → x , xs) ⟩)

{-
 reorn1 (n , ⟨ a , (λ _ → x , xs) ⟩ )  ↝ 
     deleteΣ a
       (`Σ (λ c →
        `Π (λ b →
          insert (x ≡ true) (λ q →
          `var (inv (ℕ.suc n , xs))))))
-}

reorn2 : orn ⟦ reorn1 ⟧orn proj₁ proj₁
reorn2 = ⌈ reorn1 ⌉

postulate
  a' : A
  xs⁺ : μ ⟦ testO ⟧orn (ℕ.suc n)

reorn2O : Orn proj₁ (func.out ⟦ reorn1 ⟧orn (n , ⟨ a , (λ _ → x , xs) ⟩))
reorn2O = orn.out reorn2 ((n , ⟨ a , (λ _ → x , xs) ⟩) , ⟨ a' , c , (λ _ → xs⁺) ⟩)

{-
 reorn2 ((n , ⟨ a , (λ _ → x , xs) ⟩) , ⟨ a , c , (λ _ → xs⁺) ⟩ ) ↝
     insert (a' ≡ a) (λ qa →
     deleteΣ c
       (`Π (λ b →
        `Σ (λ qx →
          `var (inv ((ℕ.suc n , xs) , xs⁺ b))))))
-}

reorn3 : orn ⟦ reorn2 ⟧orn proj₁ proj₁
reorn3 = ⌈ reorn2 ⌉

postulate 
  c' : C
  xs⁺⁺ : μ ⟦ reorn1 ⟧orn (ℕ.suc n , xs)

reorn3O : Orn proj₁  (func.out ⟦ reorn2 ⟧orn ((n , ⟨ a , (λ _ → true , xs) ⟩) , ⟨ (a , (c , (λ _ → xs⁺))) ⟩))
reorn3O = orn.out reorn3 (((n , ⟨ a , (λ _ → true , xs) ⟩) , ⟨ a , c , (λ _ → xs⁺) ⟩) , ⟨ (c' , (λ b → refl , xs⁺⁺)) ⟩)

{-
 reorn3 (((n , ⟨ a , (λ _ → true , xs) ⟩) , ⟨ a , c , (λ _ → xs⁺) ⟩ ) , ⟨ c' , λ b → refl , xs⁺⁺ ⟩ ) ↝
    `Σ (λ q₁ →
    insert (c' ≡ c) (λ q₂ →
    `Π (λ b →
    deleteΣ refl 
     (`var (inv (((ℕ.suc n , xs) , xs⁺ b , xs⁺⁺ b)))))))
-}


lemma : ∀{i₁ i₂ i₃ i₄} → (x y : μ ⟦ reorn3 ⟧orn (((i₁ , i₂) , i₃) , i₄)) → ⊢ x ≡ y
lemma {i₂ = ⟨ i₂₁ , i₂₂ ⟩}
      {⟨ .i₂₁ , i₄₁ , i₃₃ ⟩} 
      {⟨ .i₄₁ , i₄₂ ⟩} 
      ⟨ refl , refl , x ⟩ 
      ⟨ refl , refl , y ⟩ = cong (λ x → ⟨ refl , refl , x ⟩) <$>
                                 extensionality (λ b → lemma (x b) (y b))
