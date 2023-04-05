open import Data.Sum

module MinimumExtraction
  (Val : Set) (_≤_ : Val → Val → Set)
  (≤-refl : {x : Val} → x ≤ x) (≤-trans : {x y z : Val} → x ≤ y → y ≤ z → x ≤ z)
  (_≤?_ : (x y : Val) → x ≤ y ⊎ y ≤ x) where

open import Function using (id; _∘_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Bool using (Bool; true; false)
open import Data.Product as Product using (Σ; proj₁; proj₂; _,_; Σ-syntax; _×_)
open import Data.Maybe as Maybe using (Maybe; nothing; just; map)
open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)


--------
-- McBride's instance searching technique (ICFP 2014)

if_then_else_ : {A B C : Set} → A ⊎ B → ({{_ : A}} → C) → ({{_ : B}} → C) → C
if inj₁ a then t else u = t {{a}}
if inj₂ b then t else u = u {{b}}

record Σᴵ (A : Set) (B : A → Set) : Set where
  constructor ⟨_⟩ 
  field
    fst     : A
    {{snd}} : B fst

infix 2 Σᴵ-syntax

Σᴵ-syntax : (A : Set) → (A → Set) → Set
Σᴵ-syntax = Σᴵ

syntax Σᴵ-syntax A (λ x → B) = Σᴵ[ x ∈ A ] B


--------
-- Binomial trees and basic binomial heaps

Ṗ : {I : Set} → List I → (I → Set) → Set
Ṗ []       X = ⊤
Ṗ (i ∷ is) X = X i × Ṗ is X

descend : ℕ → List ℕ
descend zero    = []
descend (suc n) = n ∷ descend n

data BForest : ℕ → Val → Set where
  forest : {r : ℕ} {x : Val} → Ṗ (descend r) (λ i → Σᴵ[ t ∈ Σ Val (BForest i) ] (x ≤ proj₁ t)) → BForest r x

pattern _◃_ t ts = forest (⟨ t ⟩ , ts)

BTree : ℕ → Set
BTree r = Σ Val (BForest r)

root : {r : ℕ} → BTree r → Val
root = proj₁

children : {r : ℕ} (t : BTree r) → BForest r (root t)
children = proj₂

attach : {r : ℕ} (t u : BTree r) {{_ : root u ≤ root t}} → BTree (suc r)
attach t (y , forest us) = y , t ◃ us

link : {r : ℕ} → BTree r → BTree r → BTree (suc r)
link t u = if root t ≤? root u then attach u t else attach t u

data BHeap : ℕ → Set where
  nul  : {r : ℕ}                                   → BHeap r
  zero : {r : ℕ}               (h : BHeap (suc r)) → BHeap r
  one  : {r : ℕ} (t : BTree r) (h : BHeap (suc r)) → BHeap r

extract : {r : ℕ} → BHeap r → Maybe (BTree r × BHeap r)
extract nul       = nothing
extract (zero  h) = Maybe.map (λ { ((x , t ◃ ts) , h) → (x , forest ts) , one t h }) (extract h)
extract (one t h) = just (t , zero h)


--------
-- Minimum extraction (and auxiliary binomial heap types)

data BHeapᴹ : ℕ → Maybe Val → Set where
  nul  : {r : ℕ} → BHeapᴹ r nothing
  min  : {r : ℕ} {v : Val} (t : BForest r v) {v' : Val} {{_ : v ≤ v'}} (h : BHeapᴹ (suc r) (just v')) → BHeapᴹ r (just v)
  sin  : {r : ℕ} {v : Val} (t : BForest r v) (h : BHeapᴹ (suc r) nothing) → BHeapᴹ r (just v)
  one  : {r : ℕ} {v : Val} (t : BTree r) {{_ : v ≤ root t}} (h : BHeapᴹ (suc r) (just v)) → BHeapᴹ r (just v)
  zero : {r : ℕ} {mv : Maybe Val} (h : BHeapᴹ (suc r) mv) → BHeapᴹ r mv

pattern ⟪_⟫ b = _ , b

toBHeapᴹ : {r : ℕ} → BHeap r → Σ (Maybe Val) (BHeapᴹ r)
toBHeapᴹ nul       = ⟪ nul ⟫
toBHeapᴹ (zero  h) = let ⟪ h' ⟫ = toBHeapᴹ h in ⟪ zero h' ⟫
toBHeapᴹ (one t h) with toBHeapᴹ h
toBHeapᴹ (one t h) | nothing , h' = ⟪ sin (children t) h' ⟫
toBHeapᴹ (one t h) | just v  , h' = if root t ≤? v then ⟪ min (children t) h' ⟫ else ⟪ one t h' ⟫

-- ornamental forgetful function
fromBHeapᴹ : {r : ℕ} {mv : Maybe Val} → BHeapᴹ r mv → BHeap r
fromBHeapᴹ nul       = nul
fromBHeapᴹ (min ts h) = one ⟪ ts ⟫ (fromBHeapᴹ h)
fromBHeapᴹ (sin ts h) = one ⟪ ts ⟫ (fromBHeapᴹ h)
fromBHeapᴹ (one t  h) = one t      (fromBHeapᴹ h)
fromBHeapᴹ (zero   h) = zero       (fromBHeapᴹ h)

data BHeapᴺ : ℕ → Maybe Val → Bool → Set where
  nul  : {r : ℕ} → BHeapᴺ r nothing true
  min  : {r : ℕ} {v : Val} (ts : BForest r v) {v' : Val} {{_ : v ≤ v'}} {norm : Bool}
         (h : BHeapᴺ (suc r) (just v') norm) → BHeapᴺ r (just v) true
  sin  : {r : ℕ} {v : Val} (ts : BForest r v) {norm : Bool}
         (h : BHeapᴺ (suc r) nothing norm) → BHeapᴺ r (just v) true
  one  : {r : ℕ} {v : Val} (t : BTree r) {{_ : v ≤ root t}} {norm : Bool}
         (h : BHeapᴺ (suc r) (just v) norm) → BHeapᴺ r (just v) false
  zero : {r : ℕ} {mv : Maybe Val} {norm : Bool}
         (h : BHeapᴺ (suc r) mv norm) → BHeapᴺ r mv norm

-- part of the algebraic ornamental isomorphism
toBHeapᴺ : {r : ℕ} {mv : Maybe Val} → BHeapᴹ r mv → Σ Bool (BHeapᴺ r mv)
toBHeapᴺ nul       = ⟪ nul ⟫
toBHeapᴺ (min t h) = let ⟪ h' ⟫ = toBHeapᴺ h in ⟪ min t h' ⟫
toBHeapᴺ (sin t h) = let ⟪ h' ⟫ = toBHeapᴺ h in ⟪ sin t h' ⟫
toBHeapᴺ (one t h) = let ⟪ h' ⟫ = toBHeapᴺ h in ⟪ one t h' ⟫
toBHeapᴺ (zero  h) = let ⟪ h' ⟫ = toBHeapᴺ h in ⟪ zero  h' ⟫

-- ornamental forgetful function
fromBHeapᴺ : {r : ℕ} {mv : Maybe Val} {norm : Bool} → BHeapᴺ r mv norm → BHeapᴹ r mv
fromBHeapᴺ nul        = nul
fromBHeapᴺ (min ts h) = min ts (fromBHeapᴺ h)
fromBHeapᴺ (sin ts h) = sin ts (fromBHeapᴺ h)
fromBHeapᴺ (one t  h) = one t  (fromBHeapᴺ h)
fromBHeapᴺ (zero   h) = zero   (fromBHeapᴺ h)

attach' : {r : ℕ} (t t' : BTree r) {{_ : root t' ≤ root t}}
          {v : Val} {{_ : v ≤ root t}} {{_ : v ≤ root t'}} → Σᴵ[ u ∈ BTree (suc r) ] v ≤ root u
attach' t (y , forest ts') = ⟨ y , forest (⟨ t ⟩ , ts') ⟩

link' : {r : ℕ} (t t' : BTree r) {v : Val} {{_ : v ≤ root t}} {{_ : v ≤ root t'}} → Σᴵ[ u ∈ BTree (suc r) ] v ≤ root u
link' t t' = if root t ≤? root t' then attach' t' t else attach' t t'

normalise-aux : {r : ℕ} {v : Val} → BHeapᴹ (suc r) (just v) →
                BForest r v × ((u : BTree r) {{_ : v ≤ root u}} →
                               Σ (Val × Bool) (λ { (v' , norm) → Σᴵ[ _ ∈ BHeapᴺ (suc r) (just v') norm ] v ≤ v' }))
normalise-aux (min (t ◃ ts) {v'} h) =
  forest ts , λ u → let ⟨ u' ⟩ = link' t u
                        ⟪ h' ⟫ = toBHeapᴺ h
                    in  if root u' ≤? v' then ⟪ ⟨ min (children u') h' ⟩ ⟫
                                         else ⟪ ⟨ one u' h'            ⟩ ⟫
normalise-aux (sin (t ◃ ts) h) =
  forest ts , λ u → let ⟨ u' ⟩ = link' t u
                        ⟪ h' ⟫ = toBHeapᴺ h
                    in  ⟪ ⟨ sin (children u') h' ⟩ ⟫
normalise-aux (one t h) with normalise-aux h
normalise-aux (one t h) | (t' ◃ ts) , f =
  forest ts , λ u → let ⟨ u' ⟩ = link' t' u
                        ((v' , _) , ⟨ h' ⟩) = f u'
                    in  if root t ≤? v' then ⟪ ⟨ min (children t) h' ⟩ ⟫ else ⟪ ⟨ one t h' ⟩ ⟫
normalise-aux (zero  h) with normalise-aux h
normalise-aux (zero  h) | (t ◃ ts) , f =
  forest ts , λ u → let ⟨ u' ⟩ = link' t u
                        ⟪ ⟨ h' ⟩ ⟫ = f u'
                    in  ⟪ ⟨ zero h' ⟩ ⟫

normalise : {r : ℕ} {mv : Maybe Val} → BHeapᴹ r mv → BHeapᴺ r mv true
normalise nul       = nul
normalise (min t h) = let ⟪ h' ⟫ = toBHeapᴺ h in min t h'
normalise (sin t h) = let ⟪ h' ⟫ = toBHeapᴺ h in sin t h'
normalise (one t h) with normalise-aux h
normalise (one t h) | us , f with f t
normalise (one t h) | us , f | ⟪ ⟨ h' ⟩ ⟫ = min us h'
normalise (zero  h) = zero (normalise h)

extract-min : {r : ℕ} → BHeap r → Maybe (BTree r × BHeap r)
extract-min = extract ∘ fromBHeapᴹ ∘ fromBHeapᴺ ∘ normalise ∘ proj₂ ∘ toBHeapᴹ


--------
-- Proving that extract-min extracts the minimum root

-- specificiation

_ᴿ∈_ : Val → {r : ℕ} → BHeap r → Set
x ᴿ∈ nul     = ⊥
x ᴿ∈ zero  h = x ᴿ∈ h
x ᴿ∈ one t h = x ≡ root t ⊎ x ᴿ∈ h

_≤ᴿ_ : Val → {r : ℕ} → BHeap r → Set
x ≤ᴿ h = {y : Val} → y ᴿ∈ h → x ≤ y

_IsMinRootOf_ : Val → {r : ℕ} → BHeap r → Set
x IsMinRootOf h = x ᴿ∈ h × x ≤ᴿ h

-- auxiliary proofs

root-element : {r : ℕ} {x : Val} (h : BHeapᴹ r (just x)) → x ᴿ∈ fromBHeapᴹ h
root-element (min ts h) = inj₁ refl
root-element (sin ts h) = inj₁ refl
root-element (one t  h) = inj₂ (root-element h)
root-element (zero   h) = root-element h

- : {A : Set} {{_ : A}} → A
- {{a}} = a

empty-heap : {r : ℕ} (h : BHeapᴹ r nothing) {x : Val} → ¬ (x ᴿ∈ fromBHeapᴹ h)
empty-heap nul      = id
empty-heap (zero h) = empty-heap h

lower-bound : {r : ℕ} {x : Val} (h : BHeapᴹ r (just x)) → x ≤ᴿ fromBHeapᴹ h
lower-bound (min ts h) (inj₁ refl) = ≤-refl
lower-bound (min ts h) (inj₂ eq  ) = ≤-trans - (lower-bound h eq)
lower-bound (sin ts h) (inj₁ refl) = ≤-refl
lower-bound (sin ts h) (inj₂ eq  ) = ⊥-elim (empty-heap h eq)
lower-bound (one t  h) (inj₁ refl) = -
lower-bound (one t  h) (inj₂ eq  ) = lower-bound h eq
lower-bound (zero   h) i           = lower-bound h i

min-root : {r : ℕ} {x : Val} (h : BHeapᴹ r (just x)) → x IsMinRootOf (fromBHeapᴹ h)
min-root h = root-element h , lower-bound h

first-root : {r : ℕ} → BHeap r → Maybe Val
first-root nul       = nothing
first-root (zero  h) = first-root h
first-root (one t h) = just (root t)

normal-first : {r : ℕ} {mx : Maybe Val} (h : BHeapᴺ r mx true) → first-root (fromBHeapᴹ (fromBHeapᴺ h)) ≡ mx
normal-first nul        = refl
normal-first (min ts h) = refl
normal-first (sin ts h) = refl
normal-first (zero   h) = normal-first h

extract-first : {r : ℕ} (h : BHeap r) → Maybe.map (root ∘ proj₁) (extract h) ≡ first-root h
extract-first nul       = refl
extract-first (zero  h) with extract-first h
extract-first (zero  h) | eq with extract h
extract-first (zero  h) | eq | just ((_ , forest _) , _) = eq
extract-first (zero  h) | eq | nothing = eq
extract-first (one t h) = refl

if-elim : {A B C : Set} (c : A ⊎ B) (ca : {{_ : A}} → C) (cb : {{_ : B}} → C) →
          (P : C → Set) → ({{_ : A}} → P ca) → ({{_ : B}} → P cb) → P (if c then ca else cb)
if-elim (inj₁ a) ca cb P pa pb = pa
if-elim (inj₂ b) ca cb P pa pb = pb

fromBHeapᴹ-toBHeapᴹ-inverse : {r : ℕ} (h : BHeap r) → fromBHeapᴹ (proj₂ (toBHeapᴹ h)) ≡ h
fromBHeapᴹ-toBHeapᴹ-inverse     nul       = refl
fromBHeapᴹ-toBHeapᴹ-inverse     (zero  h) = cong zero (fromBHeapᴹ-toBHeapᴹ-inverse h)
fromBHeapᴹ-toBHeapᴹ-inverse     (one t h) with fromBHeapᴹ-toBHeapᴹ-inverse h
fromBHeapᴹ-toBHeapᴹ-inverse     (one t h) | eq with toBHeapᴹ h
fromBHeapᴹ-toBHeapᴹ-inverse     (one t h) | eq | nothing , h' = cong (one t) eq
fromBHeapᴹ-toBHeapᴹ-inverse {r} (one t h) | eq | just x  , h' =
  if-elim {C = Σ[ mx ∈ Maybe Val ] BHeapᴹ r mx} (root t ≤? x) ⟪ min (children t) h' ⟫ ⟪ one t h' ⟫
    (λ w → fromBHeapᴹ (proj₂ w) ≡ one t h) (cong (one t) eq) (cong (one t) eq)

-- main theorems
-- the root of the tree extracted by extract-min is the minimum root
extract-min-just : {r : ℕ} (h : BHeap r) {t : BTree r} {h' : BHeap r} → extract-min h ≡ just (t , h') → (root t) IsMinRootOf h
extract-min-just h  eq with fromBHeapᴹ-toBHeapᴹ-inverse h
extract-min-just h  eq | eq'  with toBHeapᴹ h
extract-min-just h  eq | eq'  | mx      , h' with trans (sym (normal-first (normalise h')))
                                                        (trans (sym (extract-first (fromBHeapᴹ (fromBHeapᴺ (normalise h')))))
                                                               (cong (Maybe.map (root ∘ proj₁)) eq))
extract-min-just ._ eq | refl | just x  , h' | refl = min-root h'
extract-min-just h  eq | eq'  | nothing , h' | ()

-- a heap has no root (i.e., is empty) if extract-min fails for that heap
extract-min-nothing : {r : ℕ} (h : BHeap r) → extract-min h ≡ nothing → {x : Val} → ¬ (x ᴿ∈ h)
extract-min-nothing h  eq with fromBHeapᴹ-toBHeapᴹ-inverse h
extract-min-nothing h  eq | eq'  with toBHeapᴹ h
extract-min-nothing h  eq | eq'  | mx      , h' with trans (sym (normal-first (normalise h')))
                                                           (trans (sym (extract-first (fromBHeapᴹ (fromBHeapᴺ (normalise h')))))
                                                                  (cong (Maybe.map (root ∘ proj₁)) eq))
extract-min-nothing h  eq | eq'  | just x  , h' | ()
extract-min-nothing ._ eq | refl | nothing , h' | _  = empty-heap h'
