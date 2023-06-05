{-# OPTIONS --type-in-type --with-K #-}


module Ornament.TypeInType.Numerical where

open import Ornament.TypeInType.Desc
open import Ornament.TypeInType.Orn
open import Ornament.TypeInType.OrnDesc


open Agda.Primitive renaming (Set to Type)

open import Data.Unit
open import Data.Empty
open import Data.Product
open import Data.Sum hiding (map₂)
open import Data.Nat
open import Function.Base
open import Data.Vec using (Vec)


open import Relation.Binary.PropositionalEquality using (_≡_; cong; sym; refl; subst) renaming (trans to _∙_; subst₂ to subst2)



private variable
  J K L : Type
  A B C X Y Z : Type
  P P′ : Type
  Γ Δ Θ : Tel P
  U V W   : ExTel Γ
  If : Info

open Info

Number : Info
Number .𝟙i = ℕ
Number .ρi = ℕ
Number .σi S = ∀ p → S p → ℕ
Number .δi Γ J = Γ ≡ ∅ × J ≡ ⊤ × ℕ

eval : (D : DescI If Γ ⊤) → InfoF If Number → ∀ {p} → μ D p tt → ℕ
eval {If = If} D ϕ = fold (λ _ _ → ev D) _ tt
  where
  ev : (D : DescI If Γ ⊤) → ∀ {a b} → ⟦ D ⟧ (λ _ _ → ℕ) a b → ℕ
  ev' : (C : ConI If Γ ⊤ V) → ∀ {a b} → ⟦ C ⟧ (λ _ _ → ℕ) a b → ℕ

  ev (C ∷ D) (inj₁ x) = ev' C x
  ev (C ∷ D) (inj₂ y) = ev D y

  ev' (𝟙 {if = k} j) refl                          = ϕ .𝟙f k
  ev' (ρ {if = k} j g C)                   (n , x) = ϕ .ρf k * n + ev' C x
  ev' (σ S {if = S→ℕ} h C)                 (s , x) = ϕ .σf _ S→ℕ _ s + ev' C x
  ev' (δ {if = if} {iff = iff} j g R h C)  (r , x) with ϕ .δf _ _ if
  ... | refl , refl , k                            = k * eval R (ϕ ∘InfoF iff) r + ev' C x

NatND : DescI Number ∅ ⊤
NatND = 𝟙 {if = 0} _
      ∷ ρ0 {if = 1} _ (𝟙 {if = 1} _)
      ∷ []

BinND : DescI Number ∅ ⊤
BinND = 𝟙 {if = 0} _
      ∷ ρ0 {if = 2} _ (𝟙 {if = 1} _)
      ∷ ρ0 {if = 2} _ (𝟙 {if = 2} _)
      ∷ []

bin-2 : μ BinND tt tt
bin-2 = con (inj₂ (inj₂ (inj₁ (con (inj₁ refl) , refl))))

bin-5 : μ BinND tt tt
bin-5 = con (inj₂ (inj₁ (con (inj₂ (inj₂ (inj₁ (con (inj₁ refl) , refl)))) , refl)))

{-
module Simple where
  DigND : DescI Number ∅ ⊤
  DigND = 𝟙 {if = 1} _
        ∷ 𝟙 {if = 2} _
        ∷ 𝟙 {if = 3} _
        ∷ []

  FingND : DescI Number ∅ ⊤
  FingND = 𝟙 {if = 0} _
         ∷ 𝟙 {if = 1} _
         ∷ δ- {if = refl , refl , 1} _ _ DigND (ρ0 {if = 2} _ (δ- {if = refl , refl , 1} _ _ DigND (𝟙 {if = 0} _)))
         ∷ []
-}

-- goal : D2 = toDesc (TrieO-1 D) ⇒ μ (D2 A n) ≃ Vec A (toℕ n)
-- if D = C ∷ D′, then D2 = C2 ∷ D′2 and we need
-- μ (D2 A (inj₁ n)) = ⟦ C2 ⟧  (μ D2) A n ≃ Vec A (toℕ n)
-- μ (D2 A (inj₂ n)) = ⟦ D′2 ⟧ (μ D2) A n ≃ Vec A (toℕ n)

-- C = ρ0 _ C′ then C2 = ρ j g C′2
-- μ (C2 A (r , n)) = ⟦ ρ j g C′2 ⟧ (μ C2) A (r , n)
--                  = μ C2 (g A) (j r) × ⟦ C′2 ⟧ (μ C2) A n ≃ Vec A (toℕ (r , n))
--                  = Vec A (g (toℕ (j r)) + n)                                                     
-- toℕ {if = ⊕} (r , n) = toℕ r + toℕ n
-- toℕ {if = ⊛} (r , n) = toℕ r * toℕ n

-- ⇒ this is only going to work if ⊛ is not *
-- let's just settle for toℕ {if = ⊛ k} (r , n) = k * r + n
-- i.e. Op = ℕ

-- C = ρ _ g C′ then C2 = ρ j h C′2
-- μ (C2 A (r , n)) = ⟦ ρ j g C′2 ⟧ (μ C2) A (r , n)
--                  = μ C2 (g A) (j r) × ⟦ C′2 ⟧ (μ C2) A n ≃ Vec A ???
--                  = Vec A (g (toℕ (j r)) + n)                                        


-- so full ρ in numbers does not work, or maybe in a very restricted sense (you would need ρi to be something like Op × ((g : Cxf Γ Γ) → map g ℕ → ℕ) 
-- ρ0 should work, so define RegDesc < Desc and RegCon < Con

-- on the other hand, σi could be used for variable multiplication?
-- let's keep it as just a variable + for now

-- similarly δ breaks a bit because all of the sudden numbers can sneak parameters back in

--{-# TERMINATING #-}


TrieO-1  : (D : DescI If ∅ ⊤) → InfoF If Number → OrnDesc Plain (∅ ▷ const Type) ! ⊤ ! D

module _ {D' : DescI If ∅ ⊤} where
  TrieO  : (D : DescI If ∅ ⊤) → InfoF If Number → OrnDesc Plain (∅ ▷ const Type) ! ⊤ ! D
  TrieOC : ∀ {V} {W : ExTel (∅ ▷ const Type)} {f : VxfO ! W V} (C : ConI If ∅ ⊤ V) → InfoF If Number → ConOrnDesc Plain {W = W} {K = ⊤} f ! C
 
  TrieO []      f = []
  TrieO (C ∷ D) f = TrieOC C f ∷ TrieO D f
  
  TrieOC {f = f} (𝟙 {if = k} j) ϕ =                                -- if the number is constantly k here
    Δσ (λ { ((_ , A) , _) → Vec A (ϕ .𝟙f k)}) f proj₁              -- add k A's here
    (𝟙 ! (const refl))                           
    (λ p → refl)
    
  TrieOC {f = f} (ρ {if = k} j g C) ϕ =                            -- if the number is recursively k * r + n here
    ρ ! (λ { (_ , A) → _ , Vec A (ϕ .ρf k) })                      -- keep the recursive field with parameter A^k
    (TrieOC C ϕ)                                                   -- and compute the rest of the OD
    (λ p → refl) λ p → refl
    
  TrieOC {f = f} (σ S {if = if} h C) ϕ =
    σ S id (h ∘ VxfO-▷ f S)
    (Δσ (λ { ((_ , A) , _ , s) → Vec A (ϕ .σf _ if _ s) }) (h ∘ _) id
    (TrieOC C ϕ)
    λ p → refl) (λ p → refl)

  TrieOC {f = f} (δ {if = if} {iff = iff} j g R h C) ϕ with ϕ .δf _ _ if
  ... | refl , refl , k =
    ∙δ {f'' = λ { (w , x) → h (f w , ornForget (toOrn (TrieO-1 R (ϕ ∘InfoF iff))) _ x) }} (λ { ((_ , A) , _) → _ , Vec A k }) !
    (TrieOC C ϕ)
    (TrieO-1 R (ϕ ∘InfoF iff)) id (λ _ _ → refl) (λ _ _ → refl) λ p → refl

TrieO-1 D f = TrieO {D' = D} D f


-- ornamental algebras ⇒ make unindexed tries ⇒ get indexed ones (I hope)

{-
TrieO-1  : (D : DescI If ∅ ⊤) → InfoF If Number → OrnDesc Plain (∅ ▷ const Type) ! (μ D tt _) ! D

module _ {D' : DescI If ∅ ⊤} where
  TrieO  : (D : DescI If ∅ ⊤) → InfoF If Number → (⟦ D ⟧ (μ D') tt _ → μ D' tt _) → OrnDesc Plain (∅ ▷ const Type) ! (μ D' tt _) ! D
  TrieOC : ∀ {V} {W : ExTel (∅ ▷ const Type)} {f : VxfO ! W V} (C : ConI If ∅ ⊤ V) → InfoF If Number → (∀ {p} w → ⟦ C ⟧ (μ D') (tt , f {p = p} w) _ → μ D' tt _) → ConOrnDesc Plain {W = W} {K = μ D' tt _} f ! C
  TrieO-forget : ∀ {If′} {iff : InfoF If′ If} (R : DescI If′ ∅ ⊤) {p' : Σ ⊤ (λ x → Type)} (ϕ : InfoF If Number) (q : μ R tt tt) {if : ℕ} s →
                 q ≡ ornForget (toOrn (TrieO-1 R (ϕ ∘InfoF iff))) (tt , Vec (proj₂ p') if) {i = q} s
 
  TrieO []      f ix = []
  TrieO (C ∷ D) f ix = TrieOC C f (λ v x → ix (inj₁ x)) ∷ TrieO D f (ix ∘ inj₂)

  TrieOC {f = f} (𝟙 {if = if} j) ϕ ix =                               -- if the number is constantly if here
    Δσ (λ { ((_ , A) , _) → Vec A (ϕ .𝟙f if)}) f proj₁                      -- add if A's here
    (𝟙 (λ { ((_ , A) , w) → ix w refl })                            -- the index is completely determined by the context
    (const refl)) λ p → refl  
    
  TrieOC {f = f} (ρ {if = if} j g C) ϕ ix =                           -- if the number is recursively if * r + n here
    Δσ (const (μ D' tt tt)) (f ∘ proj₁) id                          -- for an index r
    (ρ (proj₂ ∘ proj₂) (λ { (_ , A) → _ , Vec A (ϕ .ρf if) })               -- keep the recursive field at r with parameter A^k
    (TrieOC C ϕ λ { (w , r) n → ix w (r , n) } )                      -- and compute the rest of the OD, the index is constructed from r and the context
    (λ p → refl) λ p → refl) λ p → refl
    
  TrieOC {f = f} (σ S {if = if} h C) ϕ ix =
    σ S id (h ∘ VxfO-▷ f S)
    (Δσ (λ { ((_ , A) , _ , s) → Vec A (ϕ .σf _ if _ s) }) (h ∘ _) id
    (TrieOC C ϕ λ { ((w , s) , x) n → ix w (s , n) })
    λ p → refl) (λ p → refl)

  TrieOC {f = f} (δ {if = if} {iff = iff} j g R h C) ϕ ix with ϕ .δf _ _ if
  ... | refl , refl , if =
    Δσ (const (μ R tt tt)) (f ∘ proj₁) id
    (Δσ (const (μ D' tt tt)) (f ∘ proj₁ ∘ proj₁) id
    (∙δ (λ { ((_ , A) , ((w , r) , n)) → _ , Vec A if }) (proj₂ ∘ proj₁ ∘ proj₂)
    (TrieOC C ϕ λ { (w , r) x → ix w (r , x) })
    (TrieO-1 R (ϕ ∘InfoF iff)) (proj₁ ∘ proj₁) (λ _ _ → refl) (λ _ _ → refl) λ { {p'} (((p , q) , r) , s) → cong (λ q → h (f p , q)) (TrieO-forget R ϕ q s) })
    λ p → refl) λ p → refl

  TrieO-forget R ϕ (con q) (con s) = {!!}

TrieO-1 D f = TrieO {D' = D} D f con
-}

{-
Bin = μ BinND tt tt

BTreeOD = TrieO-1 BinND
BTreeD = toDesc ? BTreeOD

BTree : Type → Bin → Type
BTree A n = μ BTreeD (_ , A) n

btree-5 : BTree ℕ bin-5
btree-5 = con (inj₂ (inj₁ (bin-2 , (con (inj₂ (inj₂ (inj₁ (con (inj₁ refl) , con (inj₁ ({!0!} , refl)) , {!2 * 2!} , refl)))) , {!1!} , refl))))
-}
