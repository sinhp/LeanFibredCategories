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

universe u

namespace CategoryTheory
open Category Opposite

variable {C E : Type*} [Category C] [Category E]



/-- A functor P is a discrete fibration if every morphism P x ⟶ d has a unique lift. -/
class DiscreteFibration (P : E ⥤ C) where
lift : ∀ ⦃c d : C⦄ (f : c ⟶ d) (x :  P⁻¹ c), Unique (CovLift (P := P) f x)



namespace DiscreteFibration
variable {P : E ⥤ C}[DiscreteFibration P]

@[simp]
def Transport {c d : C} (f : c ⟶ d) : (P⁻¹ c) → (P⁻¹ d) := fun x ↦ (DiscreteFibration.lift f x).default.tgt

@[simp]
lemma proj_transport (f : c ⟶ d) (x : P⁻¹ c) : P.obj (Transport f x) = d := by simp

@[simp]
def BasedLiftOf {P : E ⥤ C} [DiscreteFibration P] {c d : C} (f : c ⟶ d) (x :  P⁻¹ c) : BasedLift P f x (Transport f x) where
  hom := (DiscreteFibration.lift f x).default
  eq := by aesop

-- @[simp]
-- lemma

/-- Every discrete fibration is a Grothendieck fibration. We give a constructive proof (not using choice) using the universal property of the propositional truncation (which we access by the recursion for the inductive type Nonempty).  -/
instance instCartesianCovLift (P : E ⥤ C) [DiscreteFibration P] {c d: C} (f : c ⟶ d) (x : P⁻¹ c) : CartesianCovLift (P:= P) f x where
  tgt := (DiscreteFibration.lift f x).default.tgt
  hom :=  (BasedLiftOf f x).hom
  eq := by aesop
  cart := by intro z g' u hu; simp at *; use (BasedLiftOf u (Transport f x));


end DiscreteFibration

class isDiscreteFibration (P : E ⥤ C) : Prop where
lift : ∀ ⦃c d : C⦄ (f : c ⟶ d) (x : P⁻¹ c), Nonempty (Unique (CovLift (P:= P) f x))
-- exists_lift : ∀ ⦃c d : C⦄ (f : c ⟶ d) (x : Fib P c), HasCovLift P f x
-- unique_lift : ∀ ⦃c d : C⦄ {f : c ⟶ d} {x : Fib P c} (g g' : CovLift P f x), g = g'
#print Inhabited
#check Inhabited.default
#check Unique
#print Unique.toInhabited
#check Unique.toInhabited

section
#check Unique.uniq
variable (a : Unique C)
#check a.default
#check a.1 -- a.default
#check a.2
end

#check DiscreteFibration.lift



instance instCleavageOfDiscreteFibration (P : E ⥤ C) [DiscreteFibration P] : Cleavage P where
  lift {c d: C} (f : c ⟶ d) (x : P⁻¹ c) := by infer_instance

section
variable (P : E ⥤ C)
#check Nonempty.map
#check Nonempty.map (@instCleavageOfDiscreteFibration (C:= C) (E:= E) _ _ P)
end


instance isFibrationOfisDiscreteFibration (P : E ⥤ C) [isDiscreteFibration P] : HasCleavage P where
  lift {c} {d} f x := prop_trunc sorry
