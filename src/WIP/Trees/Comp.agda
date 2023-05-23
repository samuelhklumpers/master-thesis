{-# OPTIONS --guardedness #-}

module Trees.Comp where

open import Data.Empty
open import Data.Unit
open import Data.Product
open import Cubical.Data.Sum


module Finite where
  data P : Set where
    𝟘 𝟙     :         P
    _+_ _*_ : P → P → P

  BoolP : P
  BoolP = 𝟙 + 𝟙

  ⟦_⟧ : P → Set
  ⟦ 𝟘 ⟧ = ⊥
  ⟦ 𝟙 ⟧ = ⊤
  ⟦ p + q ⟧ = ⟦ p ⟧ ⊎ ⟦ q ⟧ 
  ⟦ p * q ⟧ = ⟦ p ⟧ × ⟦ q ⟧

  Bool = ⟦ BoolP ⟧

  true : Bool
  true = inr _

 
module Rec where
  data P : Set where
    𝟘 𝟙     :         P
    _+_ _*_ : P → P → P
    Id      :         P

  NatP : P
  NatP = 𝟙 + Id

  ⟦_⟧ : P → Set → Set
  ⟦ 𝟘 ⟧ X = ⊥
  ⟦ 𝟙 ⟧ X = ⊤
  ⟦ p + q ⟧ X = ⟦ p ⟧ X ⊎ ⟦ q ⟧ X
  ⟦ p * q ⟧ X = ⟦ p ⟧ X × ⟦ q ⟧ X
  ⟦ Id ⟧ X = X

  data μ (p : P) : Set where
    con : ⟦ p ⟧ (μ p) → μ p 

  Nat = μ NatP

  three : Nat
  three = con (inr (con (inr (con (inr (con (inl _)))))))
  

module Nest where
  data P : Set where
    𝟘 𝟙     :         P
    _+_ _*_ : P → P → P
    Id      :         P
    ∘       : P     → P

  NatP : P
  NatP = 𝟙 + (∘ Id) 

  PerfectP : P
  PerfectP = Id + (∘ (Id * Id)) 

  ⟦_⟧ : P → P → Set → Set

  data μ (p : P) (X : Set) : Set where
    con : ⟦ p ⟧ p X → μ p X

  -- hardwiring μ into ⟦_⟧ is necessary to appease the positivity checker, but is otherwise harmless since it amounts to inlining
  ⟦ 𝟘 ⟧ F X = ⊥
  ⟦ 𝟙 ⟧ F X = ⊤
  ⟦ p + q ⟧ F X = ⟦ p ⟧ F X ⊎ ⟦ q ⟧ F X
  ⟦ p * q ⟧ F X = ⟦ p ⟧ F X × ⟦ q ⟧ F X
  ⟦ Id ⟧  F X = X
  ⟦ ∘ p ⟧ F X = μ F (μ p X)
  -- ∘ Id is now Rec

  Nat = μ NatP

  one : Nat ⊥
  one = con (inr (con (inl tt)))

  Perfect = μ PerfectP

  test-1 : Perfect ⊤
  test-1 = con (inl tt)
  
  test-2 : Perfect ⊤
  test-2 = con (inr (con (inl (con (tt , tt)))))

  ListP : P
  ListP = 𝟙 + (Id * (∘ Id))

  List′ = μ ListP

  nats : List′ (Nat ⊥)
  nats = con (inr (one , con (inl _)))

  -- F X = X + F (List X)
  TestP : P
  TestP = Id + (∘ ListP)

  Test = μ TestP

  test : Test (Nat ⊥)
  test = con (inr (con (inl (con (inr (one , con (inl tt)))))))

  IdP : P
  IdP = Id

  Id′ = μ Id

  id : Id′ ⊤
  id = con tt

  {-
  GoP : P
  GoP = ∘ Id

  Go = μ GoP

  go : Go ⊤
  go = con (con (con (con (con {!...!}))))

  Go2P : P
  Go2P = Id + (∘ (∘ Id))

  Go2 = μ Go2P

  go2 : Go2 ⊤
  go2 = con (inr (con (inr (con (inl (con (con (con {!!}))))))))

  Go3P : P
  Go3P = Id + (∘ (∘ 𝟙))
  
  Go3 = μ Go3P

  go3 : Go3 ⊤
  go3 = con (inr (con (inl (con (con {!!})))))
  -- like very unwellfounded trees
  -}

  -- μ (∘ p) X = ⟦ ∘ p ⟧ (∘ p) X = μ (∘ p) (μ (∘ p) X)


module Coind where
  record ∞P : Set
  data P : Set where
    𝟘 𝟙     :           P
    _+_ _*_ : ∞P → ∞P → P
    Id      :           P

  private variable
    p' q' : ∞P

  private variable
    p q : P

  record ∞P where
    coinductive
    constructor delay
    field
      force : P

  open ∞P

  NatP : ∞P
  NatP .force = delay 𝟙 + NatP

  data Intp (A : Set) : P → Set where
    i-𝟙 : Intp A 𝟙
    i-l : Intp A (force p') → Intp A (p' + q')
    i-r : Intp A (force q') → Intp A (p' + q')
    i-* : Intp A (force p') → Intp A (force q') → Intp A (p' * q')
    i-i : A → Intp A Id

  data μ (p : ∞P) : Set where
    con : Intp (μ p) (force p) → μ p

  Nat = μ NatP

  two : Nat
  two = con (i-r (i-r (i-l i-𝟙)))
