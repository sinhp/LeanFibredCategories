/-
Copyright (c) 2024 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sina Hazratpour
-/

import LeanFibredCategories.ForMathlib.FibredCats.Basic
import LeanFibredCategories.ForMathlib.FibredCats.CartesianLift
import LeanFibredCategories.ForMathlib.FibredCats.VerticalLift


namespace CategoryTheory

open Category Opposite BasedLift Fiber FiberCat

universe v₁ u₁ v₂ u₂

-- variable (C : Type u₁) [Category.{v₁} C]


-- @[pp_with_univ]
-- class CategoryStruct (obj : Type u) extends Quiver.{v + 1} obj : Type max u (v + 1) where
--   /-- The identity morphism on an object. -/
--   id : ∀ X : obj, Hom X X
--   /-- Composition of morphisms in a category, written `f ≫ g`. -/
--   comp : ∀ {X Y Z : obj}, (X ⟶ Y) → (Y ⟶ Z) → (X ⟶ Z)

class DisplayStruct (C : Type u₁) extends Category.{v₁} C  where
  /-- The type of objects indexed over `C`. -/
  obj_over : C → Type u₂
  /-- The type of morphisms indexed over morphisms of `C`. -/
  hom_over : ∀ {c d : C}, (c ⟶ d) → obj_over c → obj_over d → Type v₂
  /-- The identity morphism overlying the identity morphism of `C`. -/
  id_over : ∀ {c : C} (x : obj_over c), hom_over (𝟙 c) x x
  /-- Composition of morphisms overlying composition of morphisms of `C`. -/
  comp_over : ∀ {c₁ c₂ c₃ : C} {f₁ : c₁ ⟶ c₂} {f₂ : c₂ ⟶ c₃} {x₁ : obj_over c₁} {x₂ : obj_over c₂} {x₃ : obj_over c₃}, hom_over f₁ x₁ x₂ → hom_over f₂ x₂ x₃ → hom_over (f₁ ≫ f₂) x₁ x₃

class Display (C : Type u₁) extends DisplayStruct.{v₁, u₁, v₂, u₂} C where
id_comp_over {c₁ c₂ : C} {f : c₁ ⟶ c₂} {x₁ : obj_over c₁} {x₂ : obj_over c₂} (g : hom_over f x₁ x₂) : comp_over (id_over x₁) g = (id_comp f).symm ▸ g
comp_id_over {c₁ c₂ : C} {f : c₁ ⟶ c₂} {x₁ : obj_over c₁} {x₂ : obj_over c₂} (g : hom_over f x₁ x₂) : comp_over g (id_over x₂) = (comp_id f).symm ▸ g

variable (C : Type u₁) (E : Type u₂) [Category.{v₁} C] [Category.{v₂} E]

/-- The display category `Display P` associated to a functor `P : E ⥤ C`. -/
instance instDisplayOfFunctor (P : E ⥤ C) : DisplayStruct C where
  obj_over c := P⁻¹ c
  hom_over f x y := x ⟶[f] y
  id_over x := BasedLift.id x
  comp_over := fun g₁ g₂ => g₁ ≫[l] g₂






end CategoryTheory
