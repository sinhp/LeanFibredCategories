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
import Mathlib.CategoryTheory.MorphismProperty
import Mathlib.CategoryTheory.Iso
import Mathlib.CategoryTheory.Limits.Shapes.Pullbacks
import Mathlib.CategoryTheory.Limits.Preserves.Basic
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks
import LeanFibredCategories.Fiber -- later change that to MathLib.Data.Fiber

/-!
# Lifts

For a functor `P : E ⥤ C`, the structure `BasedLift` provides the type of lifts
of a given morphism in the base with fixed source and target in the fibers of `P`.

We provide various useful constructors:
* `mkOfHomEquiv`
* `mkOfUnitCounit`
* `leftAdjointOfEquiv` / `rightAdjointOfEquiv`
  construct a left/right adjoint of a given functor given the action on objects and
  the relevant equivalence of morphism spaces.
* `adjunctionOfEquivLeft` / `adjunctionOfEquivRight` witness that these constructions
  give adjunctions.

There are also typeclasses `IsLeftAdjoint` / `IsRightAdjoint`, carrying data witnessing
that a given functor is a left or right adjoint.
Given `[IsLeftAdjoint F]`, a right adjoint of `F` can be constructed as `rightAdjoint F`.

`Adjunction.comp` composes adjunctions.

`toEquivalence` upgrades an adjunction to an equivalence,
given witnesses that the unit and counit are pointwise isomorphisms.
Conversely `Equivalence.toAdjunction` recovers the underlying adjunction from an equivalence.
-/

namespace CategoryTheory

open Category Opposite Functor Limits Cones

variable {C E : Type*} [Category C] [Category E]

/-NoteToSelf: we use `structure` declaration rather than subtype definition (akin to `Fib` in `Frobenius.Fiber`) since later we want to extend this structure it to get the **class** `CartBasedLifts`. -/
@[ext]
structure BasedLift (P : E ⥤ C) {c d : C} (f : c ⟶ d) (src : P⁻¹ c) (tgt : P⁻¹ d) where
hom : (src : E) ⟶ (tgt : E)
over : (P.map hom) ≫ eqToHom (tgt.over) = eqToHom (src.2) ≫ f


end CategoryTheory
