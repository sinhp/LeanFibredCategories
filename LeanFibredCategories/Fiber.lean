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


universe u

namespace CategoryTheory
open Category Opposite

@[ext]
structure Fib {C E : Type*} (P : E → C) (c : C) where
fiber : E
eq : P fiber = c

def Fib' {C E : Type*} (P : E → C) (c : C) := {d : E // P d = c}


namespace Fib
variable {P : E → C} {c d : C}
/- coercion from the fibre to the total category -/
instance  {c : C} : CoeOut (Fib P c) E where
  coe := Fib.fiber

@[simp]
lemma coe_mk (e : E) (h : P e = c) : (mk e h : E) = e := rfl

@[simp]
lemma mk_coe (x : Fib P c) : mk x.fiber x.eq = x := rfl

lemma coe_inj (x y : Fib P c) : (x : E) = y ↔ x = y := by
  constructor
  intro h; ext; exact h
  intro h; rw [h]

@[simp]
lemma proj (x : Fib P c) : P x = c := x.eq

@[simp]
lemma proj_eq (x y : Fib P c) : P x = P y := by simp

@[simps]
def tauto (e : E) : Fib P (P e) := ⟨e, rfl⟩

/--Regarding an object of the total space as an object in the fiber of its image.-/
instance  : CoeDep (E) (e : E) (Fib P (P e) ) where
  coe := tauto e

@[ext]
structure Total {C E : Type*} (P : E → C) where
base : C
fiber : Fib P base

end Fib



abbrev FibCat {C E : Type*} [Category C] [Category E] (P : E ⥤ C) (c : C) := Fib P.obj c
notation:75 P " ⁻¹ " c => FibCat P c

namespace FibCat
variable {C E : Type*} [Category C] [Category E] {P : E ⥤ C}{c d : C}

instance instCategoryFib {c : C} : Category (P ⁻¹ c) where
  Hom x y := { g : (x : E) ⟶ (y : E) | P.map g = eqToHom (Fib.proj_eq x y) }
  id x := ⟨𝟙 (x : E), by simp⟩
  comp g h := ⟨g.1 ≫ h.1, by simp; rw [g.2, h.2]; simp ⟩

@[simp, aesop forward safe]
lemma proj_fibre_hom (x y : P⁻¹ c) (g : x ⟶ y) : P.map g.1 = eqToHom (Fib.proj_eq x y) := g.2


namespace Op
@[simp]
lemma proj_fiber (x : P.op ⁻¹ (op c)) : P.obj (unop (x.fiber)) = c := by
cases' x with e h
simpa [Functor.op] using h

/-- The fibre of the opposite functor `P.op`  is isomorphic to the the fibre of `P`.  -/
@[simps]
def equiv (c : C) : (P.op ⁻¹ (op c) ) ≅ (P⁻¹ c)   where
  hom := fun x =>  (⟨unop x.fiber, by rw [proj_fiber] ⟩)  -- ⟨x.fiber, by simp⟩
  inv := fun x => ⟨op x.fiber , by simp only [Functor.op_obj, unop_op, Fib.proj]⟩  -- aesop generated

@[simp]
lemma unop_op_map  {c : C} {x y : (P.op) ⁻¹ (op c)} (f : x ⟶ y) : unop (P.op.map f.1) = P.map f.1.unop  := by rfl

@[simp]
lemma op_map_unop  {c : C} {x y : (P ⁻¹ c)ᵒᵖ} (f : x ⟶ y) : P.op.map (f.unop.1.op) = (P.map (f.unop.1)).op := rfl

/-- The fibre category of the opposite functor `P.op` is isomorphic to the opposite of the fibre category of `P`. -/

def Iso (P : E ⥤ C) (c : C) : Cat.of (P.op ⁻¹ (op c) ) ≅ Cat.of ((P⁻¹ c)ᵒᵖ)  where
  hom := {
    obj := fun x => op (⟨unop x.fiber, by rw [proj_fiber] ⟩)
    map := @fun x y f => ⟨f.1.unop, by dsimp; rw [← (unop_op_map f), f.2]; apply eqToHom_unop ⟩
  }
  inv := {
    obj := fun x => ⟨op x.unop.fiber , by simp only [Functor.op_obj, unop_op, Fib.proj]⟩
    map := @fun x y f => ⟨(f.unop.1).op , by dsimp;  simp [Functor.op_map]⟩
  }
  hom_inv_id := by aesop
  inv_hom_id := by aesop

end Op
end FibCat
