/-
Copyright (c) 2024 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sina Hazratpour
-/

import Mathlib.CategoryTheory.Category.Cat
import Mathlib.CategoryTheory.Arrow
import Mathlib.CategoryTheory.Opposites
import Mathlib.CategoryTheory.Equivalence
import Mathlib.CategoryTheory.EqToHom
import Mathlib.CategoryTheory.Sigma.Basic
import Mathlib.CategoryTheory.Limits.Preserves.Basic
import LeanFibredCategories.ForMathlib.Data.Fiber
import LeanFibredCategories.ForMathlib.CategoryTheory.Fibred.Basic

/-!
# Lifts

For a functor `P : E ⥤ C`, the structure `BasedLift` provides the type of lifts
of a given morphism in the base with fixed source and target in the fibers of `P`.

We provide various useful constructors:
* `BasedLift.tauto` regards a morphism `g` of the domain category `E` as a
  based lift of its image `P g` under functor `P`.
* `BasedLift.id` and `BasedLift.comp` provide the identity and composition of
  based lifts, respectively.

There are also typeclasses `IsLeftAdjoint` / `IsRightAdjoint`, carrying data witnessing
that a given functor is a left or right adjoint.
Given `[IsLeftAdjoint F]`, a right adjoint of `F` can be constructed as `rightAdjoint F`.

`Adjunction.comp` composes adjunctions.

`toEquivalence` upgrades an adjunction to an equivalence,
given witnesses that the unit and counit are pointwise isomorphisms.
Conversely `Equivalence.toAdjunction` recovers the underlying adjunction from an equivalence.

We provide the following notations:
* `x ⟶[f] y` for `BasedLift P f x y`
* `f ≫[l] g` for the composition of based lifts given by `BasedLift.comp f g`

-/

namespace CategoryTheory

open Category Opposite Functor Limits Cones

variable {C E : Type*} [Category C] [Category E]

/-- The type of lifts of a given morphism in the base
with fixed source and target in the fibers of the domain and codomain respectively.-/
@[ext]
structure BasedLift (P : E ⥤ C) {c d : C} (f : c ⟶ d) (src : P⁻¹ c) (tgt : P⁻¹ d) where
hom : (src : E) ⟶ (tgt : E)
over : (P.map hom) ≫ eqToHom (tgt.over) = eqToHom (src.2) ≫ f

section BasedLiftNotation

variable (P : E ⥤ C) {c d : C} (f : c ⟶ d) {x : P⁻¹ c} {y : P⁻¹ d}

notation x " ⟶[" f "] " y => BasedLift (P:= _) f x y

end BasedLiftNotation

/-- A lift of a morphism in the base with a fixed target in the fiber of
the codomain -/
@[ext]
structure Lift (P : E ⥤ C) {c d : C} (f : c ⟶ d) (tgt : P⁻¹ d) where
src : P⁻¹ c
lift : BasedLift P f src tgt

/-- A lift of a morphism in the base with a fixed source in the fiber of
the domain -/
@[ext]
structure CoLift (P : E ⥤ C) {c d : C} (f : c ⟶ d) (src : P⁻¹ c) where
tgt : P⁻¹ d
colift : BasedLift P f src tgt

/-- `HasLift P f y` represents the mere existence of a lift of the morphism `f` with target `y`. -/
def HasLift (P : E ⥤ C) {c d : C} (f : c ⟶ d) (y : P⁻¹ d) := Nonempty (Lift P f y)

/-- `HasColift P f x` represents the mere existence of a lift of the morphism `f` with source `x`. -/
def HasCoLift (P : E ⥤ C) {c d : C} (f : c ⟶ d) (x : P⁻¹ c) := Nonempty (CoLift P f x)

namespace BasedLift

variable {P : E ⥤ C}

@[simp, aesop forward safe]
lemma over_base {c d : C} {f : c ⟶ d} {x : P⁻¹ c} {y : P⁻¹ d} (g : BasedLift P f x y) : P.map g.hom = eqToHom (x.2) ≫ f ≫ (eqToHom (y.over).symm)  := by simp only [← Category.assoc _ _ _, ← g.over, assoc, eqToHom_trans, eqToHom_refl, comp_id]

/-- Coercion from BasedLift to the domain category. -/
instance (P : E ⥤ C) {c d : C} (f : c ⟶ d) (x : P⁻¹ c) (y : P⁻¹ d) : CoeOut (BasedLift P f x y) ((x : E) ⟶ (y : E)) where
  coe := fun l ↦ l.hom

/-- `BasedLift.tauto` regards a morphism `g` of the domain category `E` as a
based lift of its image `P g` under functor `P`. -/
@[simps]
def tauto {e e' : E} (g : e ⟶ e') : (Fiber.tauto e) ⟶[P.map g] (Fiber.tauto e') := ⟨g, by simp only [Fiber.tauto, eqToHom_refl, id_comp, comp_id]⟩

@[simps]
instance instCoeTautoBasedLift {e e' : E} {g : e ⟶ e'} : CoeDep (e ⟶ e') (g) (Fiber.tauto e  ⟶[P.map g] Fiber.tauto e') where
  coe := tauto g

/-- Two based lifts of the same base morphism are equal if their underlying morphisms are equal in the domain category. -/
lemma hom_ext {c d : C} {f : c ⟶ d} {x : P⁻¹ c} {y : P⁻¹ d} {g₁ g₂ : x ⟶[f] y} (h : g₁.hom = g₂.hom) : g₁ = g₂ := by
  cases g₁; cases g₂; congr

/-- Regarding a based lift of the identity base morphism as a morphism
 of the fiber category.-/
@[simp]
instance instCoeFiberHom {c : C} {x y : P⁻¹ c} : Coe (x ⟶[𝟙 c] y) (x ⟶ y) where
  coe := fun f ↦ ⟨ f.hom , by simp [f.over]⟩

/-- BasedLift.ofFiberHom regards a morphism in the fiber category `P⁻¹ c`
as a based lift of the identity morphism of `c`. -/
@[simps]
def ofFiberHom {c : C} {x y : P⁻¹ c} (f : x ⟶ y) : x ⟶[𝟙 c] y := ⟨f.1, by simp [f.2]⟩

lemma tauto_over_base (f : (P.obj x) ⟶ (P.obj y)) (e : (Fiber.tauto x) ⟶[f] (Fiber.tauto y)) : P.map e.hom = f := by simp only [Fiber.coe_mk, over_base, eqToHom_refl, comp_id, id_comp]

/-- The identity based lift. -/
@[simp, aesop forward safe]
def id (x : P⁻¹ c) : BasedLift P (𝟙 c) x x := ⟨𝟙 _, by simp⟩

lemma id_hom {x : P⁻¹ c} : (id x).hom = 𝟙 _ := rfl

/-- The composition of based lifts -/
@[simp]
def comp {c d d': C} {f : c ⟶ d} {f' : d ⟶ d'} {x : P⁻¹ c} {y : P⁻¹ d} {z : P⁻¹ d'} (g : x ⟶[f] y) (g' : y ⟶[f'] z) : x ⟶[f ≫ f'] z :=
⟨g.hom ≫ g'.hom, by simp only [P.map_comp]; rw [assoc, over_base g, over_base g']; simp  ⟩

section
variable (P : E ⥤ C){c d d': C}{x: P⁻¹ c} {y : P⁻¹ d} {z : P⁻¹ d'} (u : c ⟶ d) (v: d ⟶ d') (f : x ⟶[u] y) (g : y ⟶[v] z)
notation f " ≫[l] " g => BasedLift.comp f g
end

/-- The underlying morphism of a composition of based lifts is the composition of the underlying morphisms. -/
lemma comp_hom  {c d d': C} {f₁ : c ⟶ d} {f₂ : d ⟶ d'} {x : P⁻¹ c} {y : P⁻¹ d} {z : P⁻¹ d'} (g₁ : x ⟶[f₁] y) (g₂ : y ⟶[f₂] z) : (g₁ ≫[l] g₂).hom = g₁.hom ≫ g₂.hom := rfl

@[simp]
lemma comp_hom_aux {c d d': C} {f₁ : c ⟶ d} {f₂ : d ⟶ d'} {x : P⁻¹ c} {y : P⁻¹ d} {z : P⁻¹ d'} {g₁ : x ⟶[f₁] y} {g₂ : y ⟶[f₂] z} {h : x ⟶[f₁ ≫ f₂] z} : (g₁ ≫[l] g₂) = h ↔ g₁.hom ≫ g₂.hom = h.hom := by
constructor
· intro H; rw [← H]; simp
· intro H; ext; simp [H]

lemma comp_tauto_hom {x y z : E} {f : P.obj x ⟶ P.obj y} {l : Fiber.tauto x ⟶[f] (Fiber.tauto y)} {g : y ⟶ z} : (l ≫[l] tauto g).hom = l.hom ≫ g := rfl

/-- Cast a based lift along an equality of the base morphisms. -/
@[simps]
def cast {c d : C} {f f' : c ⟶ d} {x : P⁻¹ c} {y : P⁻¹ d} (h : f = f') : (x ⟶[f] y) ≃ (x ⟶[f'] y) where
  toFun := fun g ↦ ⟨g.hom, by rw [←h, g.over]⟩
  invFun := fun g ↦ ⟨g.hom, by rw [h, g.over]⟩
  left_inv := by intro g; simp
  right_inv := by intro g; simp





end BasedLift



end CategoryTheory
