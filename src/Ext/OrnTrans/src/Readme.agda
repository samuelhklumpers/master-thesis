module Readme where

-- This development depends on the Agda standard library
-- [http://wiki.portal.chalmers.se/agda/pmwiki.php?n=Libraries.StandardLibrary]

-- It is known to typecheck with Agda v2.3.2.2 and the Agda standard
-- library v0.7.

-- To load the development, simply load this file (C-c C-l) and browse
-- the modules listed below (M-. on specific modules).


-- * Library functions: 

-- ** Predicate manipulation
open import Logic.Logic

-- ** Propositional universe 
-- (with proof irrelevance and extensional equality)
open import Logic.IProp

-- * Section 2: From Comparison to Lookup

open import FunOrn.Example

-- * Section 3: Universe of Descriptions

open import IDesc.IDesc
open import IDesc.Fixpoint
open import IDesc.InitialAlgebra
open import IDesc.Lifting
open import IDesc.Induction
open import IDesc.Case

-- ** Examples

open import IDesc.Examples.List
open import IDesc.Examples.Ordinal
open import IDesc.Examples.Bool
open import IDesc.Examples.Nat
open import IDesc.Examples.Vec
open import IDesc.Examples.Fin
open import IDesc.Examples.STLC
open import IDesc.Examples.Id

-- *** More examples (not in the paper)

open import IDesc.Examples.Forest
open import IDesc.Examples.Walk
open import IDesc.Examples.Expr

-- * Section 4: Universe of ornaments

open import Orn.Ornament

-- ** Section 4.1: Examples

open import Orn.Ornament.Examples.Maybe
open import Orn.Ornament.Examples.List
open import Orn.Ornament.Examples.Fin

open import Orn.Ornament.Identity

-- *** More examples (not in the paper)

open import Orn.Ornament.Examples.Vec
open import Orn.Ornament.Examples.Lifting

-- ** Section 4.2: Brady optimisations

open import Orn.Brady.Vec
open import Orn.Brady.Fin

-- ** Section 4.3: Ornamental algebra

open import Orn.Ornament.CartesianMorphism
open import Orn.Ornament.Algebra

-- ** Section 4.4: Algebraic ornaments

open import Orn.AlgebraicOrnament
open import Orn.AlgebraicOrnament.Coherence
open import Orn.AlgebraicOrnament.Make

-- *** Examples

open import Orn.AlgebraicOrnament.Examples.Vec
open import Orn.AlgebraicOrnament.Examples.Leq
open import Orn.AlgebraicOrnament.Examples.Expr

-- *** More examples (not in the paper)

open import Orn.AlgebraicOrnament.Examples.Lifting

-- ** Section 4.5: Reornaments

open import Orn.Reornament
open import Orn.Reornament.Coherence
open import Orn.Reornament.Make

-- *** Examples:

open import Orn.Reornament.Examples.List
open import Orn.Reornament.Examples.Maybe
open import Orn.Reornament.Examples.Iterative

-- * Section 5: Universe of function types and their ornaments

-- ** Section 5.1: Universe of function types

open import FunOrn.Functions

-- *** Examples

open import FunOrn.Functions.Examples.Le
open import FunOrn.Functions.Examples.Plus

-- ** Section 5.2: Functional ornament

open import FunOrn.FunOrnament

-- *** Examples

open import FunOrn.FunOrnament.Examples.Lookup
open import FunOrn.FunOrnament.Examples.Append

-- ** Section 5.3: Patches

open import FunOrn.Patch

-- *** Examples

open import FunOrn.Patch.Examples.Lookup
open import FunOrn.Patch.Examples.Append

-- ** Section 5.4: Patching and coherence

open import FunOrn.Patch.Apply
open import FunOrn.Patch.Coherence

-- ** Section 6: Smart constructors

-- *** Section 6.1: Transporting recursion patterns

open import FunOrn.Lift.Fold
open import FunOrn.Lift.Induction
open import FunOrn.Lift.Case

-- ** Section 6.2: Transporting constructors

open import FunOrn.Lift.MkReorn
open import FunOrn.Lift.Constructor

-- ** Examples

open import FunOrn.Lift.Examples.Head
open import FunOrn.Lift.Examples.Lookup
open import FunOrn.Lift.Examples.Append