/-
Copyright (c) 2024 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sina Hazratpour
-/
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Sigma.Basic
import LeanFibredCategories.ForMathlib.Data.Fiber
import LeanFibredCategories.ForMathlib.FibredCats.CartesianLift
/-!
# Vertical Lifts

We call a lift `v : x ⟶[𝟙 c] y` of the identity morphism a vertical lift/morphism.

Question: Can we use extension types to define VertHom so that the proofs of `vertHomOfBasedLift` and `basedLiftOfVertHom` are more concise/automated?

-/


namespace CategoryTheory

open Category Functor Fiber BasedLift

--universe u v

variable {C E : Type} [Category C] [Category E] (P : E ⥤ C)

abbrev Vert := Σ c, P⁻¹ c

-- inductive VertHom {P : E ⥤ C} : (Vert P) → (Vert P) → Type max v u
--   | mk : ∀ {c : C} {X Y : P⁻¹ c}, (X ⟶ Y) → VertHom (⟨c, X⟩ : Vert P) (⟨c, Y⟩ : Vert P)

-- def VertHom {P : E ⥤ C} (x y : Vert P) := Σ (h : x.1 = y.1), x.2 ⟶[𝟙 x.1] (y.2.cast h.symm)

instance instCategoryVert : Category (Vert P) := inferInstance


variable {P}

/-- A based-lift of the identity generates a morphism in `Vert P. -/
def vertHomOfBasedLift {X Y : Vert P} (h : X.1 = Y.1)
(f : X.2 ⟶[𝟙 X.1] Y.2.cast h.symm) : (X ⟶ Y) := by
  obtain ⟨c, x⟩ := X
  obtain ⟨c', y⟩ := Y
  have H : c = c' := h
  subst H
  simp at f
  exact ⟨f.1, by aesop⟩

--NtS: shorter proof of above for mathlib
-- def vertHomOfBasedLift' {X Y : Vert P} {h : X.1 = Y.1}
-- (f : X.2 ⟶[𝟙 X.1] Y.2.cast h.symm) : (X ⟶ Y) := by
--   cases X; cases Y; simp at h; subst h; exact ⟨f.1, by aesop⟩

@[simp]
lemma base_eq_of_vert_hom {X Y : Vert P} (f : X ⟶ Y) : X.1 = Y.1 := by
  cases f;
  rfl

@[simp]
def basedLiftOfVertHomAux {X Y : Vert P} (f : X ⟶ Y) : X.2.1 ⟶ Y.2.1 := by
  obtain ⟨f'⟩ := f
  exact f'.1

@[simp]
lemma basedLiftOfVertHomAux_over {X Y : Vert P} {f : X ⟶ Y} :
have : P.obj Y.2.1 = X.1 := by simp [Fiber.over]; symm; exact base_eq_of_vert_hom f
P.map (basedLiftOfVertHomAux f) ≫ eqToHom (this) = eqToHom (X.2.over) ≫ 𝟙 X.1 := by
  cases f; simp

def basedLiftOfVertHom {X Y : Vert P} (f : X ⟶ Y) :
have : X.1 = Y.1 := base_eq_of_vert_hom f
X.2 ⟶[𝟙 X.1] Y.2.cast this.symm := ⟨basedLiftOfVertHomAux f, by cases f; simp⟩


@[simps!]
def basedLiftOfFiberHom {c : C} {x y : P⁻¹ c} (f : x ⟶ y) : x ⟶[𝟙 c] y :=
⟨f.1, by simp [f.2]⟩

/-- The bijection between the hom-type of the fiber P⁻¹ c and the based-lifts of the identity morphism of c. -/
@[simps!]
def equivFiberHomBasedLift {c : C} {x y : P⁻¹ c} : (x ⟶ y) ≃ (x ⟶[𝟙 c] y) where
  toFun := fun g ↦ basedLiftOfFiberHom g
  invFun := fun g ↦ g
  left_inv := by intro g; simp
  right_inv := by intro g; aesop

@[simps!]
def equivVertHomBasedLift {c : C} {x y : P⁻¹ c} : ((⟨c, x⟩ : Vert P) ⟶ ⟨c, y⟩) ≃ (x ⟶[𝟙 c] y) where
  toFun := fun g ↦ basedLiftOfVertHom g
  invFun := fun g ↦ vertHomOfBasedLift rfl g
  left_inv := by intro g; cases g; aesop
  right_inv := by intro g; aesop


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
def vertCartIso {P : E ⥤ C} {c: C} {e e' : P⁻¹ c} (g : e ⟶ e')
[Cartesian (basedLiftOfFiberHom g)] : e ≅ e' where
  hom := g
  inv := gaplift (basedLiftOfFiberHom g) (𝟙 c) (id e' ≫[l] id e')
  inv_hom_id := by
    rw [← comp_id (𝟙 e')]; apply FiberCat.hom_ext; apply gaplift_hom_property
  hom_inv_id := by
    rw [← comp_id (𝟙 e)]
    let g' : e' ⟶[𝟙 c] e := basedLiftOfFiberHom (gaplift (basedLiftOfFiberHom g) (𝟙 c) (id e' ≫[l] id e'))
    have : ((basedLiftOfFiberHom g ≫[l] g') ≫[l] basedLiftOfFiberHom g) = (BasedLift.id e ≫[l] BasedLift.id e) ≫[l](basedLiftOfFiberHom g) := by
      simp only [BasedLift.comp, basedLiftOfFiberHom_hom, BasedLift.id, comp_id,
      Category.assoc, id_comp, BasedLift.mk.injEq]
      have H : ( (gaplift (basedLiftOfFiberHom g) (𝟙 c) (id e' ≫[l] id e')) ≫[l] basedLiftOfFiberHom g) = (BasedLift.id e' ≫[l] BasedLift.id e') := by apply gaplift_property
      have H' := comp_hom'.mp H
      simp only [BasedLift.comp, BasedLift.id, comp_id, basedLiftOfFiberHom_hom] at H'
      rw [H']; simp only [comp_id]
    have H := gaplift_uniq' (basedLiftOfFiberHom g) ((basedLiftOfFiberHom g) ≫[l] g') (BasedLift.id e ≫[l] BasedLift.id e) (this)
    apply FiberCat.hom_ext
    dsimp
    have H' := comp_hom'.mp H
    simp only [basedLiftOfFiberHom_hom, BasedLift.comp, BasedLift.id, comp_id] at H'
    simp only [comp_id, H']
    simp_all only [BasedLift.comp, basedLiftOfFiberHom_hom, BasedLift.id, comp_id, id_comp, FiberCat.fiber_id_obj]
    exact H'

end CategoryTheory
