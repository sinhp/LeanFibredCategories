/-
Copyright (c) 2023 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sina Hazratpour
-/

import Mathlib.CategoryTheory.Category.Cat
import Mathlib.CategoryTheory.Arrow
import Mathlib.CategoryTheory.Opposites
import Mathlib.CategoryTheory.Elements
import Mathlib.CategoryTheory.Equivalence
import Mathlib.CategoryTheory.Grothendieck
import Mathlib.CategoryTheory.MorphismProperty
import Frobenius.Fiber
import Frobenius.CartesianLift
import Frobenius.GrothendieckFibration

universe u

namespace CategoryTheory
open Category Opposite


/--
A __fibred notion__ of structure for a category `E` is a category `F` over the arrow category of `E` such that `cod · u : F → E` is a Grothendieck fibration, `u` is a cartesian functor, and `u` “creates cartesian lifts,”
meaning it restricts to define a discrete fibration `𝑢: F → E^2`
-/
structure FiberdStruct {E : Type*} [Category E] {F : Type*} [Category F] extends  where
hom :  F ⥤ Arrow E  -- U in the paper
grothendieck : isCovFibration V
cart : CartesianFunctor (P:= V) (Q:= Cod) hom
hom_creates_cartesian_lifts : isDiscreteFibration (Cart hom)


namespace FibStr



end FibStr
