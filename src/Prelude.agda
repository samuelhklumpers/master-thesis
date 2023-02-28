{-# OPTIONS --cubical #-}

module Prelude where

open import Cubical.Foundations.Prelude             public 
open import Cubical.Foundations.Everything          public 
open import Cubical.Foundations.GroupoidLaws        public 

open import Cubical.Data.Bool                       public         using (Bool; true; false; isSetBool; Bool→Type)
open import Cubical.Data.Unit                       public         renaming (Unit to ⊤)
open import Cubical.Data.Sum                        public 
open import Cubical.Data.Nat                        public         using (ℕ)
open import Cubical.Data.Sigma                      public 
open import Cubical.Data.Empty                      public         renaming (elim to ⊥-elim; rec to ⊥-rec)

import Cubical.Data.Nat                             as ℕ
import Cubical.Data.Equality                        as Eq

open import Cubical.Data.Equality                   as Eq  using () renaming (eqToPath to path)

open import Cubical.HITs.SetQuotients.Properties    public using ()

open import Cubical.Relation.Binary                 public 
open import Cubical.Relation.Nullary                public 
open import Cubical.Relation.Nullary.Properties     public 

open import Cubical.HITs.SetQuotients               as SQ


variable
  ℓ ℓ′ ℓ″ ℓ‴ : Level
  A B C : Type ℓ
  x y z : A
