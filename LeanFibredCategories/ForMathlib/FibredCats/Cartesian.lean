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
import Mathlib.CategoryTheory.MorphismProperty
import Mathlib.CategoryTheory.Limits.Preserves.Basic
import LeanFibredCategories.ForMathlib.Data.Fiber
import LeanFibredCategories.ForMathlib.FibredCats.Basic
import LeanFibredCategories.ForMathlib.FibredCats.Display

/-!
# Cartesian Lifts

There are also typeclasses `Display.Cartesian` and `Display.CoCartesian`
carrying data witnessing that a given lift is cartesian and cocartesian, respectively.

Specialized to the display category structure of a functor `P : E ⥤ C`,
we obtain the class `CartMor` of cartesian morphisms in `E`.
The type `CartMor P` is defined in terms of the predicate `isCartesianMorphism`.

In this file we shall refer to a hom-over `g : x ⟶[f] y` as a "lift" of
`f : c ⟶ d` to `x : F c` and `y : F d` since the map application of cartesianness concerns
the display structure of a functor `P : E ⥤ C`.

We prove the following closure properties of the class `CartMor` of cartesian morphisms:
- `cart_id` proves that the identity morphism is cartesian.
- `cart_comp` proves that the composition of cartesian morphisms is cartesian.
- `cart_iso_closed` proves that the class of cartesian morphisms is closed under isomorphisms.
- `cart_pullback` proves that, if `P` preserves pullbacks, then
the pullback of a cartesian morphism is cartesian.

`instCatCart` provides a category instance for the class of cartesian morphisms,
and `Cart.forget` provides the forgetful functor from the category of cartesian morphisms
to the domain category `E`.

-/

--set_option trace.simps.verbose true

namespace CategoryTheory

open Category Opposite Functor Limits Cones

variable {C E : Type*} [Category C] {F : C → Type*} [Display F]

namespace Display

variable {c d : C} {f : c ⟶ d} {x : F c} {y : F d}

/-- A hom-over `g : x ⟶[f] y` is cartesian if for every morphism `u`
in the base and every hom-over `g' : x ⟶[u ≫ f] z` over the composite
 `u ≫ f`, there is a unique morphism `l : y ⟶[u] z` over `u` such that
 `l ≫ g = g'`. -/
class Cartesian (g : x ⟶[f] y)
 where
uniq_lift : ∀ ⦃c' : C⦄ ⦃z : F c'⦄ (u : c' ⟶ c) (g' : z ⟶[u ≫ f]  y),
Unique {k : z ⟶[u] x // (k ≫ₗ g) = g'}

/-- A morphism `g : x ⟶[f] y` over `f` is cocartesian if for all morphisms `u` in the
base and `g' : x ⟶[f ≫ u] z` over the composite `f ≫ u`, there is a unique morphism
`l : y ⟶[u] z` over `u` such that `g ≫ l = g'`. -/
class CoCartesian (g : x ⟶[f] y) where
uniq_lift : ∀ ⦃d' : C⦄ ⦃z : F d'⦄ (u : d ⟶ d') (g' : x ⟶[f ≫ u] z),
Unique {k :  y ⟶[u] z // (g ≫ₗ k) = g'}

namespace Cartesian

open Display

variable (g : x ⟶[f] y) [Cartesian g]

/-- `gap g u g'` is the canonical map from a lift `g' : x' ⟶[u ≫ f] y` to a
cartesian lift `g` of `f`. -/
def gap (u : c' ⟶ c) (g' : x' ⟶[u ≫ f] y) : x' ⟶[u] x :=
(Cartesian.uniq_lift (g:= g) (z:= x') u g').default.val

/-- A variant of `gaplift` for `g' : x' ⟶[f'] y` with casting along `f' = u ≫ f` baked into the definition. -/
def gapCast (u : c' ⟶ c) {f' : c' ⟶ d} (g' : x' ⟶[f'] y) (w : f' = u ≫ f) :
x' ⟶[u] x :=
(Cartesian.uniq_lift (g:= g) (z:= x') u (w ▸ g')).default.val

@[simp]
lemma gap_cast (u : c' ⟶ c) {f' : c' ⟶ d} (g' : x' ⟶[f'] y)
(w : f' = u ≫ f) : gapCast g u g' w = gap g u (w ▸ g') := by
  rfl

/-- The composition of the gap lift and the cartesian hom-over is the given hom-over. -/
@[simp]
lemma gap_prop (u : c' ⟶ c) (g' : x' ⟶[u ≫ f] y) :
((gap g u g') ≫ₗ g) = g' :=
(Cartesian.uniq_lift (f:= f) (g:= g) (z:= x') u g').default.property


/-- The identity hom-over is cartesian. -/
instance instId {x : F c} : Cartesian (𝟙ₗ x) where
  uniq_lift := fun c' z u g' => {
    default := ⟨(comp_id u) ▸ g', by simp⟩
    uniq := by aesop
  }

/-- Cartesian based-lifts are closed under composition. -/
instance instComp {x : F c} {y : F d} {z : F d'} (g₁ : x ⟶[f₁] y) [Cartesian g₁]
(g₂ : y ⟶[f₂] z) [Cartesian g₂] : Cartesian (g₁ ≫ₗ g₂) where
  uniq_lift := fun c' w u g' => {
    default := ⟨gap g₁ u (gap g₂ (u ≫ f₁) (assoc  ▸ g')), by rw [← BasedLift.assoc_inv, gaplift_property g₁ _ _, gaplift_property g₂ _ _]; simp⟩
    uniq := by intro ⟨l, hl⟩; simp; apply gaplift_uniq; apply gaplift_uniq; rw [BasedLift.assoc]; simp; exact hl}


end Cartesian

end Display

end CategoryTheory
