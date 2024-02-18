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

set_option pp.explicit false
--set_option pp.notation true
set_option trace.simps.verbose true
--set_option trace.Meta.synthInstance.instances true
--set_option trace.Meta.synthInstance true
set_option pp.coercions true

namespace CategoryTheory

open Category Opposite BasedLift Fiber FiberCat

variable {C E : Type*} [Category C] [Category E]

/-- A Cloven fibration provides for every morphism `c ⟶ P x` in the base a cartesian lift in the total category. -/
class ClovenFibration (P : E ⥤ C) where
lift {c d : C} (f : c ⟶ d) (y : P⁻¹ d) : CartLift (P:= P) f y

class Fibration (P : E ⥤ C) where
lift {c d : C} (f : c ⟶ d) (y : P⁻¹ d) : HasCartLift (P:= P) f y

class Transport (P : E ⥤ C) where
  transport {c d : C} (f : c ⟶ d) (y : P⁻¹ d) : P⁻¹ c

--notation f " ⋆ " y  : 10 => Transport.transport f y
scoped infixr:80 " ⋆ "  => Transport.transport -- NtS: infix right ensures that `f ⋆ y ⋆ z` is parsed as `f ⋆ (y ⋆ z)`

@[simp]
lemma transport_over {P : E ⥤ C} [Transport P] (f : c ⟶ d) (y : P⁻¹ d) :
P.obj (f ⋆ y) = c := by
  simp [Fiber.over]

namespace ClovenFibration

variable {P : E ⥤ C} [ClovenFibration P]

@[simp]
instance instTransport : Transport P where
  transport := fun f x ↦ ⟨(lift f x).src , by simp only [Fiber.over]⟩

example (f : c ⟶ d) (g : d ⟶ e) (y : P⁻¹ e) : f ⋆ g ⋆ y = f ⋆ (g ⋆ y) := rfl

@[simp]
def Transport (f : c ⟶ d) : (P⁻¹ d) → (P⁻¹ c) := fun y ↦ f ⋆ y

@[simp]
def basedLiftOf (f : c ⟶ d) (y : P⁻¹ d) : (f ⋆ y) ⟶[f] y := (lift f y).based_lift

instance instCartesianBasedLift {f : c ⟶ d} {y : P⁻¹ d} : Cartesian (basedLiftOf f y) := (lift f y).is_cart

@[simp]
def homOf (f : c ⟶ d) (y : P⁻¹ d) : (f ⋆ y : E) ⟶ (y : E) := (lift f y).based_lift.hom

@[simp]
lemma homOf_over (f : c ⟶ d) (y : P⁻¹ d) :
P.map (homOf (P:= P) f y) = (eqToHom (transport_over (P:= P) f y)) ≫ f ≫ eqToHom ((Fiber.over y).symm) := by
  simp only [Fiber.mk_coe, homOf, BasedLift.over_base]

instance CartLiftOf (f : c ⟶ d) (y : P⁻¹ d) : CartLift f y := lift f y

namespace FiberCat

def ofBasedLiftHom {c d : C} (f : c ⟶ d) (x : P⁻¹ c) (y : P⁻¹ d) (g : x ⟶[f] y) :
x ⟶ f ⋆ y where
  val := gaplift (basedLiftOf f y) (𝟙 c) (g.cast (id_comp f).symm)
  property := by simp_all only [basedLiftOf, over_base, id_comp, eqToHom_trans]

def equivFiberCatHomBasedLift {c d : C} (f : c ⟶ d) (x : P⁻¹ c) (y : P⁻¹ d) :
(x ⟶[f] y) ≃  (x ⟶ f ⋆ y) where
  toFun := fun g => ⟨gaplift (basedLiftOf f y) (𝟙 c) (BasedLift.cast (id_comp f).symm g), by aesop⟩
  invFun := fun g => ((BasedLift.ofFiberHom g) ≫[l] basedLiftOf f y).cast (id_comp f)



end FiberCat


--set_option trace.Meta.synthInstance true in
@[simp]
lemma transport_id {c : C} (x : P⁻¹ c) : ((𝟙 c) ⋆ x) ≅ x where
  hom := gaplift' (BasedLift.id x) (𝟙 c) (basedLiftOf (𝟙 c) x) (by simp only [comp_id])
  inv := gaplift' (basedLiftOf (𝟙 c) x) (𝟙 c) (BasedLift.id x) (by simp only [id_comp])
  hom_inv_id := by
    simp [FiberCat.comp_coe]; simp only [← BasedLift.id_hom]; apply hom_comp_cast (h₁ := (id_comp (𝟙 c)).symm).mpr ; rw [gaplift_comp];
    --change
    --rw [← cast_hom (h:= (id_comp (𝟙 x)).symm)];  --apply comp_hom_aux.mp;
  inv_hom_id := sorry

#exit

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
