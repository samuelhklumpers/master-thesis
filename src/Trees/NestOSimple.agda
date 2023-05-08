module Trees.NestOSimple where

-- What do descs look like?
-- KG: ΣDescs because they're cool
-- Sijsling: List Descs because they represent actual types and trees are annoying

-- our Numbers need Trees, so we will have to go Tree -> List or something


-- parameters?
-- KG: external
-- Sijsling: contexts
-- Elliott: * -> *

-- what about us?

-- indices
-- KG: responses
-- Sijsling: equalities

-- let's stick to responses


-- here is our wishlist:
-- - finger trees
-- - heterogenization
-- - field ornaments
--
-- recall, we want finger trees so we can describe them as the obvious ornament over a certain number type
-- heterogenization gives us List→HList
-- field ornaments allow us to ornament a datatype composed of other datatypes with ornaments
--
-- finger trees require some form of nesting
-- heterogenization requires some form of separation of set/non-set parameters and flexibility in levels
-- field ornaments require us to (partially) close the universe


module List+Resp where
  data RCDesc (I : Set) : Set₁ where
    1′  :                  RCDesc I
    fd  : Set → RCDesc I → RCDesc I
    rec : I   → RCDesc I → RCDesc I

  data RDesc (I : Set) : Set₁ where
    0′  :                      RDesc I
    cns : RCDesc I → RDesc I → RDesc I
  

data ⊥ : Set where

record ⊤ : Set where
  constructor tt

record _×_ (A B : Set) : Set where
  constructor _,_

  field
    fst : A
    snd : B

open import Agda.Primitive

record Σ {a b} (A : Set a) (B : A → Set b) : Set (a ⊔ b) where
  constructor _,_

  field
    fst : A
    snd : B fst

open Σ

data _⊎_ (A B : Set) : Set where
  inl : A → A ⊎ B
  inr : B → A ⊎ B


module Closed where
  Desc : Set → Set₁
  ADesc = Σ Set Desc
  data RDesc (I : Set) : Set₁
  data RCDesc (I : Set) : Set₁ where
    1′  : RCDesc I
    fd  : (d : ADesc) → fst d → RCDesc I → RCDesc I
    rec : I → RCDesc I → RCDesc I

  data RDesc I where
    0′  :                      RDesc I
    cns : RCDesc I → RDesc I → RDesc I
  
  Desc I = I → RDesc I

  ⟦_⟧D : {I : Set} → Desc I → (I → Set) → I → Set
  ⟦_⟧RD : {I : Set} → RDesc I → (I → Set) → Set  
  ⟦_⟧RCD : {I : Set} → RCDesc I → (I → Set) → Set
  data μ {I : Set} (d : Desc I) : I → Set where
    con : ∀ {i} → ⟦ d ⟧D (μ d) i → μ d i
  
  ⟦ 1′ ⟧RCD            X = ⊤
  ⟦ fd rd j rcd ⟧RCD X = μ (snd rd) j × ⟦ rcd ⟧RCD X 
  ⟦ rec i rcd ⟧RCD     X = X i × ⟦ rcd ⟧RCD X

  ⟦ 0′ ⟧RD       X = ⊥
  ⟦ cns c rd ⟧RD X = ⟦ c ⟧RCD X ⊎ ⟦ rd ⟧RD X

  ⟦ d ⟧D X i = ⟦ d i ⟧RD X

  -- fingertrees | heterogenization | field ornaments
  ---------------+------------------+----------------
  -- No          | No               | Yes?

  open import Data.Nat

  VecD : Desc ⊤ → Desc ℕ
  VecD D zero    = cns 1′ 0′
  VecD D (suc n) = cns (fd (⊤ , D) tt (rec n 1′)) 0′

  Vec : Desc ⊤ → ℕ → Set
  Vec D = μ (VecD D)

  BoolD : Desc ⊤
  BoolD tt = cns 1′ (cns 1′ 0′)

  vec-2 : Vec BoolD 2
  vec-2 = con (inl (con (inl tt) , (con (inl (con (inr (inl tt)) , (con (inl tt) , _))) , tt)))


module Parameters where
  {- we establish a correspondence

    Desc I Γ <-> datatypes with index I and parameters Γ <-> ⟦ Γ ⟧ → I → Set

    a field in a type should be a ⟦ Γ ⟧ → Set
    in the context of Γ this is equivalently a ⟦ Δ ⟧ → Set and a ⟦ Γ ⟧ → ⟦ Δ ⟧
    or a ⟦ Δ ⟧ → J → Set with a J and a ⟦ Γ ⟧ → ⟦ Δ ⟧

    we just need a way to access ⟦ ∅ ▷ x ⟧
  -}

  private variable
    I J : Set

  data Cxt : Set₂
  ⟦_⟧Cxt : Cxt → Set₁

  private variable
    Γ Δ : Cxt

  data Cxt where
    ∅   : Cxt
    _▷_ : (Γ : Cxt) (S : ⟦ Γ ⟧Cxt → Set₁) → Cxt 

  open import Level

  ⟦ ∅ ⟧Cxt     = Lift _ ⊤
  ⟦ Γ ▷ S ⟧Cxt = Σ ⟦ Γ ⟧Cxt S
  
  Desc : Set → Cxt → Set₂

  private variable
    D E : Desc I Γ

  data RDesc (I : Set) (Γ : Cxt) : Set₂
  data RCDesc (I : Set) (Γ : Cxt) : Set₂
  data FDesc (I : Set) : Cxt → Set₂ where
    --leaf : FDesc I Γ 
    --fd   : Desc J Δ → J → (⟦ Γ ⟧Cxt → ⟦ Δ ⟧Cxt) → FDesc I Γ
    fd   : (⟦ Γ ⟧Cxt → Set) → FDesc I Γ
    -- indexfirst!
    rec  : I → (⟦ Γ ⟧Cxt → ⟦ Γ ⟧Cxt) → FDesc I Γ

  data RCDesc I Γ where
    1′  : RCDesc I Γ
    _⊗_ : FDesc I Γ → RCDesc I Γ → RCDesc I Γ

  data RDesc I Γ where
    0′  : RDesc I Γ
    _⊕_ : RCDesc I Γ → RDesc I Γ → RDesc I Γ
  
  Desc I Γ = I → RDesc I Γ

  ⟦_⟧D : Desc I Γ → (⟦ Γ ⟧Cxt → I → Set) → ⟦ Γ ⟧Cxt → I → Set
  ⟦_⟧RD : RDesc I Γ → (⟦ Γ ⟧Cxt → I → Set) → ⟦ Γ ⟧Cxt → Set  
  ⟦_⟧RCD : RCDesc I Γ → (⟦ Γ ⟧Cxt → I → Set) → ⟦ Γ ⟧Cxt → Set
  ⟦_⟧FD : FDesc I Γ → (⟦ Γ ⟧Cxt → I → Set) → ⟦ Γ ⟧Cxt → Set

  --⟦ leaf ⟧FD X ps = {!!}
  ⟦ fd P    ⟧FD X ps = P ps
  ⟦ rec i P ⟧FD X ps = X (P ps) i

  ⟦ 1′     ⟧RCD X ps = ⊤
  -- no dependence on earlier fields (yet!)
  ⟦ f ⊗ fs ⟧RCD X ps = ⟦ f ⟧FD X ps × ⟦ fs ⟧RCD X ps

  ⟦ 0′     ⟧RD X ps = ⊥
  ⟦ c ⊕ cs ⟧RD X ps = ⟦ c ⟧RCD X ps ⊎ ⟦ cs ⟧RD X ps

  ⟦ d ⟧D X ps i = ⟦ d i ⟧RD X ps 
  
  data μ (D : Desc I Γ) (ps : ⟦ Γ ⟧Cxt) (i : I) : Set where
    con : ⟦ D ⟧D (μ D) ps i → μ D ps i

  -- fingertrees | heterogenization | field ornaments
  ---------------+------------------+----------------
  -- Yes         | No               | No

  PerfectD : Desc ⊤ (∅ ▷ (λ _ → Set))
  PerfectD tt = ((fd (λ { (_ , A) → A })) ⊗ 1′) ⊕ (((rec tt (λ { (_ , A) → _ , (A × A) })) ⊗ 1′) ⊕ 0′)

  Perfect = μ PerfectD

  open import Data.Nat
  pf-2 : Perfect (_ , ℕ) tt
  pf-2 = con (inr (inl (con (inl ((0 , 1) , _)) , _)))


module Het where
  private variable
    I J : Set

  data Cxt : Set₂
  ⟦_⟧Cxt : Cxt → Set₁

  private variable
    Γ Δ : Cxt

  data U : Set₁ where
    set : U
    K   : Set → U

  open import Level

  ⟦_⟧U : U → Set₁
  ⟦ set ⟧U = Set
  ⟦ K x ⟧U = Lift _ x

  data Cxt where
    ∅   : Cxt
    _▷_ : (Γ : Cxt) (S : ⟦ Γ ⟧Cxt → U) → Cxt 

  open import Level

  ⟦ ∅ ⟧Cxt     = Lift _ ⊤
  ⟦ Γ ▷ S ⟧Cxt = Σ ⟦ Γ ⟧Cxt λ ps → ⟦ S ps ⟧U
  
  Desc : Set → Cxt → Set₂

  private variable
    D E : Desc I Γ

  data U→Set : U → Set₁ where
    set : U→Set set
    K   : ∀ {X} → (X → Set) → U→Set (K X)

  data Cxt→Set : Cxt → Set₂ where
    here  : ∀ {u} → (∀ ps → U→Set (u ps)) → Cxt→Set (Γ ▷ u)
    there : ∀ {u} → Cxt→Set Γ → Cxt→Set (Γ ▷ u)

  data RDesc (I : Set) (Γ : Cxt) : Set₂
  data RCDesc (I : Set) (Γ : Cxt) : Set₂
  data FDesc (I : Set) : Cxt → Set₂ where
    fd   : Cxt→Set Γ → FDesc I Γ
    rec  : I → FDesc I Γ

  data RCDesc I Γ where
    1′  : RCDesc I Γ
    _⊗_ : FDesc I Γ → RCDesc I Γ → RCDesc I Γ

  data RDesc I Γ where
    0′  : RDesc I Γ
    _⊕_ : RCDesc I Γ → RDesc I Γ → RDesc I Γ
  
  Desc I Γ = I → RDesc I Γ

  ⟦_⟧D : Desc I Γ → (⟦ Γ ⟧Cxt → I → Set) → ⟦ Γ ⟧Cxt → I → Set
  ⟦_⟧RD : RDesc I Γ → (⟦ Γ ⟧Cxt → I → Set) → ⟦ Γ ⟧Cxt → Set  
  ⟦_⟧RCD : RCDesc I Γ → (⟦ Γ ⟧Cxt → I → Set) → ⟦ Γ ⟧Cxt → Set
  ⟦_⟧FD : FDesc I Γ → (⟦ Γ ⟧Cxt → I → Set) → ⟦ Γ ⟧Cxt → Set

  app2 : {u : U} → U→Set u → ⟦ u ⟧U → Set
  app2 set   u = u
  app2 (K x) (lift u) = x u

  app : ∀ {Γ} (P : Cxt→Set Γ) (ps : ⟦ Γ ⟧Cxt) → Set
  app (here  P) (ps , p) = app2 (P ps) p
  app (there P) (ps , p) = app P ps

  ⟦ fd P  ⟧FD X ps = app P ps
  ⟦ rec i ⟧FD X ps = X ps i

  ⟦ 1′     ⟧RCD X ps = ⊤
  ⟦ f ⊗ fs ⟧RCD X ps = ⟦ f ⟧FD X ps × ⟦ fs ⟧RCD X ps

  ⟦ 0′     ⟧RD X ps = ⊥
  ⟦ c ⊕ cs ⟧RD X ps = ⟦ c ⟧RCD X ps ⊎ ⟦ cs ⟧RD X ps

  ⟦ d ⟧D X ps i = ⟦ d i ⟧RD X ps 
 
  data μ (D : Desc I Γ) (ps : ⟦ Γ ⟧Cxt) (i : I) : Set where
    con : ⟦ D ⟧D (μ D) ps i → μ D ps i
  

  -- fingertrees | heterogenization | field ornaments
  ---------------+------------------+----------------
  -- No          | Almost?          | No

  ListD : Desc ⊤ (∅ ▷ (λ _ → set))
  ListD tt = 1′ ⊕ (((fd (here (λ _ → set))) ⊗ ((rec tt) ⊗ 1′)) ⊕ 0′)

  List = μ ListD

  open import Data.Nat

  list-2 : List (_ , ℕ) tt
  list-2 = con (inr (inl (0 , (con (inl _) , _))))
