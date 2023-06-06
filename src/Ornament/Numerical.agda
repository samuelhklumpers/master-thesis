{-# OPTIONS --type-in-type --with-K #-}


module Ornament.Numerical where

open import Ornament.Desc
open import Ornament.Orn
open import Ornament.OrnDesc


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

toℕ : {D : DescI Number Γ ⊤} → ∀ {p} → μ D p tt → ℕ
toℕ {D = D} = toℕ-lift D id-InfoF
  where
  toℕ-lift : (D : DescI If Γ ⊤) → InfoF If Number → ∀ {p} → μ D p tt → ℕ
  
  toℕ-lift {If = If} D ϕ = fold (λ _ _ → toℕ-desc D) _ tt
    where
    toℕ-desc : (D : DescI If Γ ⊤) → ∀ {a b} → ⟦ D ⟧ (λ _ _ → ℕ) a b → ℕ
    toℕ-con : (C : ConI If Γ ⊤ V) → ∀ {a b} → ⟦ C ⟧ (λ _ _ → ℕ) a b → ℕ

    toℕ-desc (C ∷ D) (inj₁ x) = toℕ-con C x
    toℕ-desc (C ∷ D) (inj₂ y) = toℕ-desc D y

    toℕ-con (𝟙 {if = k} j) refl                          = ϕ .𝟙f k
    toℕ-con (ρ {if = k} j g C)                   (n , x) = ϕ .ρf k * n + toℕ-con C x
    toℕ-con (σ S {if = S→ℕ} h C)                 (s , x) = ϕ .σf _ S→ℕ _ s + toℕ-con C x
    toℕ-con (δ {if = if} {iff = iff} j g R h C)  (r , x) with ϕ .δf _ _ if
    ... | refl , refl , k                                = k * toℕ-lift R (ϕ ∘InfoF iff) r + toℕ-con C x

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

-- simple the number system underlying simple finger trees
DigND : DescI Number ∅ ⊤
DigND = 𝟙 {if = 1} _
      ∷ 𝟙 {if = 2} _
      ∷ 𝟙 {if = 3} _
      ∷ []

FingND : DescI Number ∅ ⊤
FingND = 𝟙 {if = 0} _
       ∷ 𝟙 {if = 1} _
       ∷ δ- {if = refl , refl , 1} {iff = id-InfoF} _ _ DigND (ρ0 {if = 2} _ (δ- {if = refl , refl , 1} {iff = id-InfoF} _ _ DigND (𝟙 {if = 0} _)))
       ∷ []

-- 1 ⟨ 0 ⟩ 1
finger-2 : μ FingND tt tt
finger-2 = con (inj₂ (inj₂ (inj₁ (con (inj₁ refl) , con (inj₁ refl) , con (inj₁ refl) , refl))))

-- 1 ⟨ 2 ⟩ 2
finger-7 : μ FingND tt tt
finger-7 = con (inj₂ (inj₂ (inj₁ (con (inj₁ refl) , finger-2 , con (inj₂ (inj₁ refl)) , refl))))


-- theorem: given a number system D, there is a "good container" D', which also satisfies (x : μ D' A tt) → size x ≡ shape x
TrieO : (D : DescI Number ∅ ⊤) → OrnDesc Plain (∅ ▷ const Type) ! ⊤ ! D
TrieO D = TrieO-desc D id-InfoF
  module TrieO where
  TrieO-desc : (D : DescI If ∅ ⊤) → InfoF If Number → OrnDesc Plain (∅ ▷ const Type) ! ⊤ ! D
  TrieO-con  : ∀ {V} {W : ExTel (∅ ▷ const Type)} {f : VxfO ! W V} (C : ConI If ∅ ⊤ V) → InfoF If Number → ConOrnDesc Plain {W = W} {K = ⊤} f ! C
 
  TrieO-desc []      f = []
  TrieO-desc (C ∷ D) f = TrieO-con C f ∷ TrieO-desc D f
  
  TrieO-con {f = f} (𝟙 {if = k} j) ϕ =                             -- trie (λ X tt → ⊤) {toℕ tt → k} 
    Δσ (λ { ((_ , A) , _) → Vec A (ϕ .𝟙f k)}) f proj₁              -- ⇒ (λ X A → A^k)
    (𝟙 ! (const refl))                           
    (λ p → refl)
    
  TrieO-con {f = f} (ρ {if = k} j g C) ϕ =                         -- trie (λ X tt → X tt × F X tt) {toℕ (x , y) → k * toℕ x + toℕ y}
    ρ ! (λ { (_ , A) → _ , Vec A (ϕ .ρf k) })                      -- ⇒ (λ X A → X (A ^ k) × trie F X A)
    (TrieO-con C ϕ)                                           
    (λ p → refl) λ p → refl
    
  TrieO-con {f = f} (σ S {if = if} h C) ϕ =                              -- trie (λ X tt → S × F X tt) {toℕ (s , y) → if s + toℕ y}
    σ S id (h ∘ VxfO-▷ f S)                                              -- ⇒ (λ X A → Σ[ s ∈ S ] A^(if s) × trie F X A)
    (Δσ (λ { ((_ , A) , _ , s) → Vec A (ϕ .σf _ if _ s) }) (h ∘ _) id
    (TrieO-con C ϕ)
    λ p → refl) (λ p → refl)

  TrieO-con {f = f} (δ {if = if} {iff = iff} j g R h C) ϕ with ϕ .δf _ _ if    -- trie (λ X tt → G tt × F X tt) {toℕ (r , y) → k * toℕ r + toℕ y}
  ... | refl , refl , k =                                                      -- ⇒ (λ X A → trie G (μ (trie G)) A × trie F X A)
    ∙δ {f'' = λ { (w , x) → h (f w , ornForget (toOrn (TrieO-desc R (ϕ ∘InfoF iff))) _ x) }} (λ { ((_ , A) , _) → _ , Vec A k }) !
    (TrieO-con C ϕ)
    (TrieO-desc R (ϕ ∘InfoF iff)) id (λ _ _ → refl) (λ _ _ → refl) λ p → refl

-- to prove: size x ≡ shape x
-- * μ D is likely to be Traversable when all σ's in it are
-- * as every S in a DescI Number ∅ ⊤ is necessarily invariant, it is also trivially Traversable

-- to prove: every OrnDesc induces an ornamental algebra
-- to prove: for some appropriate Ix : (D : DescI Number ∅ ⊤) → Desc ∅ (μ D tt tt),
--           Ix D is also initial for the algebra of the algebraic ornament induced by the ornamental algebra (yes)

-- to summarize, for every number system, there is an appropriate "list", which has an appropriate "vector"
-- this vector is representable, the list is traversable, and everything still satisfies size ≡ shape ≡ index





{- -- older, direct attempt at indexed tries
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
