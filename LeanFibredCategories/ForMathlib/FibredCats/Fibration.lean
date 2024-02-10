/-
Copyright (c) 2024 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sina Hazratpour
-/
import Mathlib.CategoryTheory.Category.Cat
import Mathlib.CategoryTheory.Arrow
import Mathlib.CategoryTheory.Opposites
import Mathlib.CategoryTheory.Elements
import Mathlib.CategoryTheory.Equivalence
import Mathlib.CategoryTheory.Grothendieck
import LeanFibredCategories.ForMathlib.FibredCats.Basic
import LeanFibredCategories.ForMathlib.FibredCats.CartesianLift

namespace CategoryTheory

open Category Opposite BasedLift CartesianBasedLift Fiber

variable {C E : Type*} [Category C] [Category E]

/-- A Cloven fibration provides for every morphism `c ⟶ P x` in the base a cartesian lift in the total category. -/
class ClovenFibration (P : E ⥤ C) where
lift {c d : C} (f : c ⟶ d) (y : P⁻¹ d) : CartLift (P:= P) f y

class Fibration (P : E ⥤ C) where
lift {c d : C} (f : c ⟶ d) (y : P⁻¹ d) : HasCartLift (P:= P) f y

class Transport (P : E ⥤ C) where
  transport {c d : C} (f : c ⟶ d) (y : P⁻¹ d) : P⁻¹ c

notation f " ⋆ " y  : 10 => Transport.transport f y

@[simp]
lemma transport_proj {P : E ⥤ C} [Transport P] (f : c ⟶ d) (y : P⁻¹ d) :
P.obj (f ⋆ y) = c := by
  simp [Fiber.over]

namespace ClovenFibration

variable {P : E ⥤ C} [ClovenFibration P]

@[simp]
instance instTransport : Transport P where
  transport := fun f x ↦ ⟨(lift f x).src , by simp only [Fiber.over]⟩

@[simp]
def Transport (f : c ⟶ d) : (P⁻¹ d) → (P⁻¹ c) := fun y ↦ f ⋆ y

@[simp]
def basedLiftOf (f : c ⟶ d) (y : P⁻¹ d) : (f ⋆ y) ⟶[f] y := (lift f y).based_lift

instance instCartesianBasedLift {f : c ⟶ d} {y : P⁻¹ d} : CartesianBasedLift (basedLiftOf f y) := (lift f y).is_cart

@[simp]
def homOf (f : c ⟶ d) (y : P⁻¹ d) : (f ⋆ y : E) ⟶ (y : E) := (lift f y).based_lift.hom

@[simp]
lemma TransportHom_proj (f : c ⟶ d) (y : P⁻¹ d) :
P.map (homOf (P:= P) f y) = (eqToHom (transport_proj (P:= P) f y)) ≫ f ≫ eqToHom ((Fiber.over y).symm) := by
simp only [Fiber.mk_coe, homOf, BasedLift.over_base]

instance CartLiftOf (f : c ⟶ d) (y : P⁻¹ d) : CartLift f y := lift f y

@[simp]
lemma transport_id {c : C} (x : P⁻¹ c) : ((𝟙 c) ⋆ x) ≅ x where
  hom := _
  inv := _
  hom_inv_id := _
  inv_hom_id := _

@[simp]
lemma transport_comp {c d₁ d₂ : C} {f₁ : c ⟶ d₁} {f₂ : d₁ ⟶ d₂} {y : P⁻¹ d₂} : ((f₁ ≫ f₂) ⋆ y) ≅ f₁ ⋆ (f₂ ⋆ y) where
  hom := gaplift (basedLiftOf f₁ (f₂ ⋆ y)) (𝟙 c) (castIdComp.invFun  (gaplift (basedLiftOf f₂ y) f₁ (basedLiftOf (f₁ ≫ f₂) y)))
  inv := gaplift (basedLiftOf (f₁ ≫ f₂) y) (𝟙 c) (castIdComp.invFun ((basedLiftOf f₁ (f₂ ⋆ y)) ≫[l] (basedLiftOf f₂ y)))
  hom_inv_id := by simp; rw [← comp_hom _ _, ← id_hom]; congr; simp; sorry --aesop--apply gaplift_uniq' (BasedLiftOf f₁ (f₂ ⋆ y)) _
  inv_hom_id := sorry

end ClovenFibration

open ClovenFibration

class SplitFibration (P : E ⥤ C) extends ClovenFibration P where
transport_id_obj {c : C} (x : P⁻¹ c) : ((𝟙 c) ⋆ x).1 = x.1
transport_id_hom {c : C} (x : P⁻¹ c) : homOf (𝟙 c) x = eqToHom (transport_id_obj x) ≫ 𝟙 (x.1)
transport_comp_obj {c d₁ d₂ : C} (f₁ : c ⟶ d₁) (f₂ : d₁ ⟶ d₂) (x : P⁻¹ d₂) : ((f₁ ≫ f₂) ⋆ x).1 = (f₁ ⋆ (f₂ ⋆ x)).1
lift_comp_hom {c d e : C} (f₁ : c ⟶ d) (f₂ : d ⟶ d') (x : P⁻¹ d') :
homOf (f₁ ≫ f₂) x = homOf f₁ (f₂ ⋆ y) ≫ (homOf f₂ x)
