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
import Mathlib.CategoryTheory.Sigma.Basic

universe u

namespace CategoryTheory
open Category Opposite

-- @[ext]
-- structure Fib {C E : Type*} (P : E → C) (c : C) where
-- obj : E -- fiber
-- over' : P obj = c

@[simp]
def Fib {C E : Type*} (P : E → C) (c : C) := {d : E // P d = c}


namespace Fib
variable {P : E → C} {c d : C}
/- coercion from the fibre to the total category -/
instance  {c : C} : CoeOut (Fib P c) E where
  coe := fun x => x.1

@[simp]
lemma coe_mk (e : E) (h : P e = c) : ( (⟨e, h⟩ : Fib P c) : E) = e := rfl

@[simp]
lemma mk_coe (x : Fib P c) : ⟨x.1, x.2⟩  = x := rfl

lemma coe_inj (x y : Fib P c) : (x : E) = y ↔ x = y := by
  constructor
  · intro h; cases x; cases y; simp at h; subst h; rfl
  · intro h; rw [h]

@[simp]
lemma over (x : Fib P c) : P x = c := x.2

@[simp]
lemma over_eq (x y : Fib P c) : P x = P y := by simp [Fib.over]

@[simps]
def tauto (e : E) : Fib P (P e) := ⟨e, rfl⟩

/--Regarding an object of the total space as an object in the obj of its image.-/
instance instTautoFib (e : E) : CoeDep (E) (e) (Fib P (P e) ) where
  coe := tauto e

@[simp]
lemma tauto_over (e : E) : (tauto e : Fib P (P e)).1 = e := rfl

@[simp]
def eqRebase (e : Fib P c) (_ : c = d) : Fib P d := ⟨e.1, by simp_all only [over]⟩

@[simp]
lemma coe_tauto (e : Fib P c) : eqRebase (tauto e.1) (by simp [over]) =  e := by
  cases e; simp

@[simp]
lemma coe_tauto' (e : Fib P c) : (tauto e.1) =   eqRebase e (by simp [over]) := by
  cases e; rfl

@[ext]
structure Total {C E : Type*} (P : E → C) where
base : C
fiber : Fib P base

end Fib



abbrev FibCat {C E : Type*} [Category C] [Category E] (P : E ⥤ C) (c : C) := Fib P.obj c
notation:75 P " ⁻¹ " c => FibCat P c

namespace FibCat
variable {C E : Type*} [Category C] [Category E] {P : E ⥤ C}

@[simps]
instance instCategoryFib {c : C} : Category (P ⁻¹ c) where
  Hom x y := { g : (x : E) ⟶ (y : E) // P.map g = eqToHom (Fib.over_eq x y) }
  id x := ⟨𝟙 (x : E), by simp only [Functor.map_id, eqToHom_refl]⟩
  comp g h := ⟨g.1 ≫ h.1, by simp only [Functor.map_comp, Fib.over, eqToHom_trans]⟩

@[simp, aesop forward safe]
lemma fiber_hom_over {c: C} (x y : P⁻¹ c) (g : x ⟶ y) : P.map g.1 = eqToHom (Fib.over_eq x y) := g.2

@[simps]
def forget {c : C} : (P⁻¹ c) ⥤ E where
  obj := fun x => x
  map := @fun x y f => f.1

@[simp]
lemma fiber_comp_obj {c: C} (x y z : P⁻¹ c) (f: x ⟶ y) (g: y ⟶ z) : (f ≫ g).1 = f.1 ≫ g.1 := rfl

@[simp]
lemma fiber_comp_obj_eq {c: C} {x y z : P⁻¹ c} {f: x ⟶ y} {g: y ⟶ z} {h : x ⟶ z} : (f ≫ g = h) ↔  f.1 ≫ g.1  = h.1 := by
  constructor
  · intro H; cases H; rfl
  · intro H; cases f; cases g; cases h; simp at H; subst H; rfl

@[simp]
lemma fiber_id_obj {c: C} (x : P⁻¹ c) : (𝟙 x : x ⟶ x).val = 𝟙 (x : E) := rfl

def eqToHomFunctor : (Σc, P⁻¹ c) ⥤ Comma P (𝟭 C) where
  obj := fun ⟨c, x⟩ => ⟨x, c, eqToHom (x.over)⟩
  map := @fun ⟨_, x⟩ ⟨_, y⟩ ⟨f⟩ => {
    left := f.1
    right := 𝟙 _
    w := by simp only [Functor.id_obj, fiber_hom_over, eqToHom_trans, Functor.id_map, comp_id] -- aesop generated
  }
  map_id := by intro X; rfl
  map_comp := by aesop

/-eqToHomFunctor can be extended to a functor from the total category E to the comma category of P and 𝟭 C. This functor is a unit of a KZ-monad whose algebras are cocartesian fibrations.-/

/- Two morphisms in a fiber P⁻¹ c are equal if their underlying morphisms in E are equal. -/
lemma hom_ext {c : C} {x y : P⁻¹ c} {f g : x ⟶ y} (h : f.1 = g.1) : f = g := by
  cases f; cases g; simp at h; subst h; rfl

namespace Op

@[simp]
lemma obj_over (x : P.op ⁻¹ (op c)) : P.obj (unop (x.1)) = c := by
cases' x with e h
simpa [Functor.op] using h

/-- The fibres of the opposite functor `P.op` are isomorphic to the the fibres of `P`.  -/
@[simps]
def equiv (c : C) : (P.op ⁻¹ (op c) ) ≅ (P⁻¹ c)   where
  hom := fun x =>  (⟨unop x.1, by rw [obj_over] ⟩)  -- ⟨x.obj, by simp⟩
  inv := fun x => ⟨op x.1 , by simp only [Functor.op_obj, unop_op, Fib.over]⟩  -- aesop generated

@[simp]
lemma unop_op_map  {c : C} {x y : (P.op) ⁻¹ (op c)} (f : x ⟶ y) : unop (P.op.map f.1) = P.map f.1.unop  := by rfl

@[simp]
lemma op_map_unop  {c : C} {x y : (P ⁻¹ c)ᵒᵖ} (f : x ⟶ y) : P.op.map (f.unop.1.op) = (P.map (f.unop.1)).op := rfl

/-- The fiber category of the opposite functor `P.op` is isomorphic to the opposite of the fiber category of `P`. -/
def Iso (P : E ⥤ C) (c : C) : Cat.of (P.op ⁻¹ (op c) ) ≅ Cat.of ((P⁻¹ c)ᵒᵖ)  where
  hom := {
    obj := fun x => op (⟨unop x.1, by rw [obj_over] ⟩)
    map := @fun x y f => ⟨f.1.unop, by dsimp; rw [← (unop_op_map f), f.2]; apply eqToHom_unop ⟩
  }
  inv := {
    obj := fun x => ⟨op x.unop.1 , by simp only [Functor.op_obj, unop_op, Fib.over]⟩
    map := @fun x y f => ⟨(f.unop.1).op , by dsimp;  simp [Functor.op_map]⟩
  }
  hom_inv_id := by simp_all only [Fib.coe_mk, Functor.op_obj, Functor.op_map]; rfl
  inv_hom_id := by simp_all only [Fib.coe_mk, Functor.op_obj, unop_op, Functor.op_map]; rfl

end Op
end FibCat
