module F-2+3·X·3-Tree.Properties where

open import Cubical.Data.List as L
open import Cubical.Data.Sigma
open import Cubical.Data.Nat
open import Cubical.Data.Maybe
open import Cubical.Functions.Surjection
open import Cubical.HITs.SetQuotients as SQ
open import Cubical.Structures.Auto as Auto
open import Cubical.Foundations.SIP
open import Cubical.Structures.Function
open import Cubical.Structures.Pointed
open import Cubical.Structures.Constant


open import F-2+3·X·3-Tree.Base
open import CrudeEquiv
open FromEmbedding
open import Prelude

private variable
  n m : ℕ

--Let's make sure it's still roughly List!

flatten : ∀ n → power n Two A → List A
flatten zero xs = L.[ xs ]
flatten (suc n) (xs , ys) = flatten n xs L.++ flatten n ys

DtoList : ∀ n {d} → Tup (power n Two A) d → List A
DtoList n (one a) = flatten n a
DtoList n (two a b) = flatten n a L.++ flatten n b
DtoList n (three a b c) = flatten n a L.++ flatten n b L.++ flatten n c

toList : Tree′ A n → List A
toList none                   = []
toList {n = n} (single x)     = flatten n x
toList {n = n} (deep pf m sf) = DtoList n pf L.++ toList m L.++ DtoList n sf

toList-cons′ : (x : El A n) (xs : Tree′ A n) → toList (cons′ x xs) ≡ flatten n x L.++ toList xs
toList-cons′ x none           = sym (++-unit-r _) 
toList-cons′ x (single y)     = refl
toList-cons′ {n = n} x (deep (one a) m sf) = L.++-assoc (flatten n x) (flatten n a) (toList m L.++ DtoList n sf)
toList-cons′ {n = n} x (deep (two a b) m sf) = L.++-assoc (flatten n x) _ _
toList-cons′ {n = n} x (deep (three a b c) m sf) = 
  (flatten n x L.++ flatten n a) L.++ toList (cons′ (b , c) m) L.++ DtoList n sf ≡⟨ cong (λ h → (flatten n x L.++ flatten n a) L.++ h L.++ DtoList n sf) (toList-cons′ (b , c) m) ⟩
  (flatten n x L.++ flatten n a) L.++ ((flatten n b L.++ flatten n c) L.++ toList m) L.++ DtoList n sf ≡⟨ L.++-assoc (flatten n x) _ _ ⟩
  flatten n x L.++ flatten n a L.++ ((flatten n b L.++ flatten n c) L.++ toList m) L.++ DtoList n sf ≡⟨ cong (λ h → flatten n x L.++ flatten n a L.++ h) (L.++-assoc (flatten n b L.++ flatten n c) _ _) ⟩
  flatten n x L.++ flatten n a L.++ (flatten n b L.++ flatten n c) L.++ toList m L.++ DtoList n sf ≡⟨ cong (flatten n x L.++_) (sym (L.++-assoc (flatten n a) _ _)) ⟩
  flatten n x L.++ (flatten n a L.++ flatten n b L.++ flatten n c) L.++ toList m L.++ DtoList n sf ∎



toTree : List A → Tree A
toTree []       = none
toTree (x ∷ xs) = cons′ x (toTree xs)

toList-toTree : section (toList {A = A}) toTree
toList-toTree []       = refl
toList-toTree (x ∷ xs) = toList-cons′ _ (toTree xs) ∙ cong (x ∷_) (toList-toTree xs)

Tree↠List : Tree A ↠ List A
Tree↠List = toList , section→isSurjection {g = toTree} toList-toTree

TreeQ : Type → Type
TreeQ A = Tree A / λ x y → toList x ≡ toList y

TreeQ≃List : isSet A → TreeQ A ≃ List A
TreeQ≃List isSetA = crude (isOfHLevelList 0 isSetA) Tree↠List


Flex2S-Str : (A : Type) → Type → Type 
Flex2S-Str A X = (X → Maybe A) × (A → X → X) × (X → A → X)

Flex2S : Type → Type₁
Flex2S A = TypeWithStr ℓ-zero (Flex2S-Str A)


Flex2S-EquivStr : (A : Type) → (X Y : Flex2S A) → typ X ≃ typ Y → Type 
Flex2S-EquivStr A = Auto.AutoEquivStr (Flex2S-Str A)

Flex2S-UnivalentStr : (A : Type) → UnivalentStr _ (Flex2S-EquivStr A)
Flex2S-UnivalentStr A = Auto.autoUnivalentStr (Flex2S-Str A)

Flex2S-ΣPath : (A : Type) → (X Y : Flex2S A) → X ≃[ Flex2S-EquivStr A ] Y → X ≡ Y
Flex2S-ΣPath A = sip (Flex2S-UnivalentStr A)

headL : List A → Maybe A
headL []      = nothing
headL (x ∷ _) = just x

snocL : List A → A → List A
snocL []       y = L.[ y ]
snocL (x ∷ xs) y = x ∷ snocL xs y

-- I probably should have used this as the implementation
snocL-++ : (xs : List A) (x : A) → xs L.++ L.[ x ] ≡ snocL xs x
snocL-++ [] x = refl
snocL-++ (y ∷ xs) x = cong (y ∷_) (snocL-++ xs x)

head-toList : (a : Tree A) → headL (toList a) ≡ head′ a
head-toList none = refl
head-toList (single x) = refl
head-toList (deep (one a) m sf) = refl
head-toList (deep (two a b) m sf) = refl
head-toList (deep (three a b c) m sf) = refl

List-Flex2S : (A : Type) → Flex2S A
List-Flex2S A = List A , (headL , L._∷_ , snocL)


toList-snoc′ : (xs : Tree′ A n) (x : El A n) → toList (snoc′ xs x) ≡ toList xs L.++ flatten n x
toList-snoc′ none x = refl
toList-snoc′ (single y) x = refl
toList-snoc′ {n = n} (deep pf m (one a)) x = sym (L.++-assoc (DtoList n pf) _ _ ∙ (cong (DtoList n pf L.++_) (L.++-assoc (toList m) (flatten n a) _)))
toList-snoc′ {n = n} (deep pf m (two a b)) x = sym (L.++-assoc (DtoList n pf) _ _ ∙ cong (DtoList n pf L.++_) (L.++-assoc (toList m) _ _ ∙ cong (toList m L.++_) (L.++-assoc (flatten n a) _ _)))
toList-snoc′ {n = n} (deep pf m (three a b c)) x = 
  DtoList n pf L.++ toList (snoc′ m (a , b)) L.++ flatten n c L.++ flatten n x
    ≡⟨ cong (λ h → DtoList n pf L.++ h L.++ flatten n c L.++ flatten n x) (toList-snoc′ m (a , b)) ⟩
  DtoList n pf L.++ (toList m L.++ flatten n a L.++ flatten n b) L.++ flatten n c L.++ flatten n x ≡⟨ sym (L.++-assoc (DtoList n pf) _ _) ⟩
  (DtoList n pf L.++ (toList m L.++ flatten n a L.++ flatten n b)) L.++ flatten n c L.++ flatten n x ≡⟨ sym (L.++-assoc (DtoList n pf L.++ toList m L.++ flatten n a L.++ flatten n b) (flatten n c) (flatten n x)) ⟩
  ((DtoList n pf L.++ toList m L.++ flatten n a L.++ flatten n b) L.++ flatten n c) L.++ flatten n x ≡⟨ cong (L._++ flatten n x) (L.++-assoc (DtoList n pf) _ _) ⟩
  (DtoList n pf L.++ ((toList m L.++ flatten n a L.++ flatten n b) L.++ flatten n c)) L.++ flatten n x
    ≡⟨ cong (λ h → (DtoList n pf L.++ h) L.++ flatten n x) (L.++-assoc (toList m) _ _ ∙ cong (toList m L.++_) (L.++-assoc (flatten n a) _ _)) ⟩
  (DtoList n pf L.++ toList m L.++ flatten n a L.++ flatten n b L.++ flatten n c) L.++ flatten n x ∎


module _ {A : Type} (isSetA : isSet A) where
  headQ : TreeQ A → Maybe A
  headQ = SQ.rec (isOfHLevelMaybe 0 isSetA) head′ λ a b p → sym (head-toList a) ∙ cong headL p ∙ head-toList b

  consQ : A → TreeQ A → TreeQ A
  consQ x = SQ.rec squash/ (_/_.[_] ∘ cons′ x) λ a b p → eq/ (cons′ x a) (cons′ x b) (toList-cons′ x a ∙ cong (x ∷_) p ∙ sym (toList-cons′ x b))

  snocQ : TreeQ A → A → TreeQ A
  snocQ xs x = SQ.rec squash/ (_/_.[_] ∘ λ ys → snoc′ ys x) (λ a b p → eq/ _ _ (toList-snoc′ a x ∙ cong (L._++ L.[ x ]) p ∙ sym (toList-snoc′ b x))) xs

  TreeQ-Flex2S : Flex2S A
  TreeQ-Flex2S = TreeQ A , (headQ , consQ , snocQ)

  toList' = TreeQ≃List isSetA .fst

  toList∼ : (a : Tree A) → toList' _/_.[ a ] ≡ toList a
  toList∼ a = refl

  head∼ : (a : TreeQ A) → headQ a ≡ headL (toList' a)
  head∼ = elimProp (λ x → isOfHLevelMaybe 0 isSetA _ _) (λ a → sym (head-toList a))

  cons∼ : (x : A) (a : TreeQ A) → toList' (consQ x a) ≡ x ∷ (toList' a)
  cons∼ x = elimProp (λ x → isOfHLevelList 0 isSetA _ _) (toList-cons′ x)

  snoc∼ : (a : TreeQ A) (x : A) → toList' (snocQ a x) ≡ snocL (toList' a) x
  snoc∼ a x = elimProp (λ a → isOfHLevelList 0 isSetA (toList' (snocQ a x)) (snocL (toList' a) x)) (λ a → toList-snoc′ a x ∙ snocL-++ _ x) a

  TreeQ∼List : TreeQ-Flex2S ≃[ Flex2S-EquivStr A ] List-Flex2S A
  -- here Agda's very unhelpful "either you unfold all the way down or you don't unfold at all" policy makes the types of the holes unreadable, so you just kind of guess them
  TreeQ∼List = TreeQ≃List isSetA , head∼ , cons∼ , snoc∼

  TreeQ-Flex2S-List : TreeQ-Flex2S ≡ List-Flex2S A
  TreeQ-Flex2S-List = Flex2S-ΣPath A _ _ TreeQ∼List



record Flex-2Sided-Law {A} (Flex : Flex2S A) : Type₁ where
  Arr = Flex .fst
  op  = Flex .snd

  hd : Arr → Maybe A
  hd = op .fst

  cons : A → Arr → Arr
  cons = op .snd .fst

  snc : Arr → A → Arr
  snc = op .snd .snd

  field
    sccs : ∀ (x : A) y xs → snc (cons x xs) y ≡ cons x (snc xs y)
    hc   : ∀ (x : A) xs   → hd (cons x xs)    ≡ just x

open Flex-2Sided-Law using (sccs; hc)

List-Law : {A : Type} → Flex-2Sided-Law (List-Flex2S A)
List-Law .sccs x y xs = refl
List-Law .hc   x   xs = refl

TreeQ-Law : {A : Type} → (isSetA : isSet A) → Flex-2Sided-Law (TreeQ-Flex2S isSetA)
TreeQ-Law isSetA = subst Flex-2Sided-Law (sym (TreeQ-Flex2S-List isSetA)) List-Law
