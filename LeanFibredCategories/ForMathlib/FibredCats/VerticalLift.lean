/-
Copyright (c) 2024 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sina Hazratpour
-/
import Mathlib.CategoryTheory.Category.Basic
import LeanFibredCategories.ForMathlib.Data.Fiber
import LeanFibredCategories.ForMathlib.FibredCats.CartesianLift


namespace CategoryTheory

open Category Functor BasedLift

namespace Vertical

variable {C E : Type*} [Category C] [Category E] {P : E ⥤ C}

/-- The bijection between the hom-type of the fiber P⁻¹ c and the based-lifts of the identity morphism of c. -/
@[simps]
def vertBasedLiftEquiv {c : C} {x y : P⁻¹ c} : (x ⟶ y) ≃ (x ⟶[𝟙 c] y) where
  toFun := fun g ↦ ⟨g.1, by simp [g.2]⟩
  invFun := fun g ↦ g
  left_inv := by intro g; simp
  right_inv := by intro g; simp

/-- The bijection between the type of the isomporphisms in the fiber P⁻¹ c and the iso-based-lifts of the identity morphism of c. -/
noncomputable
def isoVertBasedLiftEquiv {c : C} {x y : P⁻¹ c} : (x ≅ y) ≃ (x ⟶[≅(𝟙 c)] y) where
  toFun := fun g => ⟨⟨g.hom.1, by simp [g.hom.2]⟩, by use g.inv.1; simp; cases g; aesop⟩
  invFun := fun g => {
    hom := ⟨g.hom , by simp⟩
    inv := ⟨ (asIso g.hom).inv , by simp⟩
    hom_inv_id := by aesop
    inv_hom_id := by aesop
  }
  left_inv := by intro α; dsimp; ext; rfl
  right_inv := by intro α; dsimp

/-- Vertical cartesian morphisms are isomorphism. -/
--@[simps]
def vertCartIso {P : E ⥤ C} {c: C} {e e' : P⁻¹ c} (g : e ⟶ e') [CartesianBasedLift (P:= P) (ofFiberHom g)] : e ≅ e' where
  hom := g
  inv := gaplift (ofFiberHom g) (𝟙 c) (id e' ≫[l] id e')
  inv_hom_id := by
    rw [← comp_id (𝟙 e')]; apply FiberCat.hom_ext; apply gaplift_hom_property
  hom_inv_id := by
    rw [← comp_id (𝟙 e)]
    let g' : e' ⟶[𝟙 c] e := ofFiberHom (gaplift (ofFiberHom g) (𝟙 c) (id e' ≫[l] id e'))
    have : ((ofFiberHom g ≫[l] g') ≫[l] ofFiberHom g) = (BasedLift.id e ≫[l] BasedLift.id e) ≫[l](ofFiberHom g) := by
      simp only [BasedLift.comp, ofFiberHom_hom, BasedLift.id, comp_id,
      Category.assoc, id_comp, BasedLift.mk.injEq]
      have H : ( (gaplift (ofFiberHom g) (𝟙 c) (id e' ≫[l] id e')) ≫[l] ofFiberHom g) = (BasedLift.id e' ≫[l] BasedLift.id e') := by apply gaplift_property
      have H' := comp_hom_aux.mp H
      simp only [BasedLift.comp, BasedLift.id, comp_id, ofFiberHom_hom] at H'
      rw [H']; simp only [comp_id]
    have H := gaplift_uniq' (ofFiberHom g) ((ofFiberHom g) ≫[l] g') (BasedLift.id e ≫[l] BasedLift.id e) (this)
    apply FiberCat.hom_ext
    dsimp
    have H' := comp_hom_aux.mp H
    simp only [ofFiberHom_hom, BasedLift.comp, BasedLift.id, comp_id] at H'
    simp only [comp_id, H']
    simp_all only [BasedLift.comp, ofFiberHom_hom, BasedLift.id, comp_id, id_comp, FiberCat.fiber_id_obj]
    exact H'


end Vertical

namespace CategoryTheory
