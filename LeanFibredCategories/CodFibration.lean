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
import Mathlib.CategoryTheory.Bicategory.Functor
import Frobenius.Fiber
import Frobenius.CartesianLift
import Frobenius.GrothendieckFibration


universe u

namespace CategoryTheory
open Category Opposite

variable {C E : Type*} [Category C] [Category E]

/-- The codomain functor-/
@[simp]
def Cod := Arrow.rightFunc (C:= C)

namespace Codomain

@[simp]
lemma cod_arrow {c: C} (e : Cod⁻¹ c) : Cod.obj e = c := e.eq

@[simp]
lemma cod_fiber_proj {c: C} {e : Cod⁻¹ c} : e.obj.right = c := e.eq

@[simp]
lemma cod_proj {c: C} (e : Cod⁻¹ c) :  (Cod.obj (e : Arrow C)) = (e : Arrow C).right := rfl

instance instFiberOfArrow {x c : C} : CoeOut (x ⟶ c) (Cod⁻¹ c) where
  coe := fun e ↦ ⟨ ⟨x, c, e⟩, rfl⟩

@[simp]
def ArrowOf {c: C} (e : Cod⁻¹ c) : Arrow C := e.obj.hom

@[simp]
lemma ArrowOf_right {c: C} (e : Cod⁻¹ c) : (ArrowOf e).right = c := e.2

instance instArrowOfFiber (e : Cod⁻¹ c) : CoeDep (Cod⁻¹ c) (e) ((e.obj.left : C) ⟶ c) where
 coe :=  e.obj.hom ≫ eqToHom (ArrowOf_right e)

@[simp]
lemma ArrowOf_coe_left {c: C} (e : x ⟶ c) : (ArrowOf (e : Cod⁻¹ c)).left = x := rfl

@[simp]
lemma ArrowOf_coe_right {c: C} (e : x ⟶ c) : (ArrowOf (e : Cod⁻¹ c)).right = c := rfl

@[simp]
def UnBasedLiftOf {x c d : C} (f : c ⟶ d) (e : x ⟶ c) : UnBasedLift Cod f where
  src := e -- coerced as ⟨e, rfl⟩
  tgt := e ≫ f -- coerced as `⟨e ≫ f, rfl⟩
  hom := ⟨𝟙 x, f, by simp_all only [Arrow.rightFunc_obj, Arrow.mk_right, Fib.coe_mk, Arrow.mk_left, Functor.id_obj, Functor.id_map,
    Arrow.mk_hom, id_comp]⟩ -- (𝟙,f) -- aesop generated proof
  eq := by aesop -- (𝟙,f).tgt = f

/-- BasedLiftOf specifies a based lift for every morphism f : c ⟶ d and an arrow e with codomain c. -/
@[simp]
def BasedLiftOf {c d : C} (f : c ⟶ d) (e : Cod⁻¹ c) : BasedLift Cod f e ⟨(e: (e.obj.left : C) ⟶ c) ≫ f, by rfl⟩ where
  hom := ⟨𝟙 _, eqToHom (ArrowOf_right e) ≫ f , by aesop⟩ -- (𝟙,f)
  eq := by simp -- (𝟙,f).tgt = f

@[simp, aesop forward safe]
lemma BasedLift.proj_eq_right {c d : C} {f : c ⟶ d} {e : Cod⁻¹ c} {e' : Cod⁻¹ d} (g : BasedLift Cod f e e') : g.hom.right = eqToHom (e.eq) ≫ f ≫ (eqToHom (e'.eq).symm)  := by simp [← assoc _ _ _, ← g.eq]

@[simps]
def CoLift {c d: C} (f : c ⟶ d) (e : Cod⁻¹ c) : CoLift Cod f e where
  tgt := ⟨(e: (e.obj.left : C) ⟶ c) ≫ f, by rfl⟩ -- e ≫ f
  colift := BasedLiftOf f e

@[simp]
lemma CoLift_proj {c d: C} {f : c ⟶ d} {e : Cod⁻¹ c}  : (CoLift f e).tgt.obj.right = d := rfl

/-- Every morphism in the base category has a cartesian lift with respect to the codomain functor. -/
instance instCartBasedLift {x c d : C} (f : c ⟶ d) (e : x ⟶ c) : CartBasedLifts Cod f   where
  hom := ⟨𝟙 x, f, by simp_all only [Fib.coe_mk, Functor.id_obj, Functor.id_map, Category.id_comp]⟩  -- the proof aesop generated
  eq := by simp
  cart := by intro e'' g' u hu; use ⟨⟨g'.left, u, by aesop⟩, by aesop⟩; simp; refine ⟨by aesop, by intro v hv; ext; aesop; aesop⟩

instance instCartCovLift' {x c d : C} (f : c ⟶ d) (e : x ⟶ c) : CartesianCovLift' (P:= Cod) f e :=
⟨CovLift f e, by intro e'' g' u hu; use ⟨⟨g'.left, u, by aesop⟩, by aesop⟩; simp; refine ⟨by aesop, by intro v hv; ext; aesop; aesop⟩⟩

instance instCartCovLift {c d : C} (f : c ⟶ d) (e : Cod⁻¹ c) : CartesianCovLift (P:= Cod) f e :=
⟨CovLift f e,
  ⟨
    fun d' e'' u g' =>
    {
      default := ⟨ ⟨ ⟨g'.hom.left, eqToHom (CovLift_proj)≫  u ≫ eqToHom (cod_fiber_proj).symm , by simp [BasedLift.proj (P:= Cod) (g:= g')]⟩ , by simp⟩, by simp ; ext <;> congr 1 <;> simp [BasedLift.comp_hom] <;> ext <;> simp ⟩ --; simp [BasedLift.proj_right g'] ⟩
      uniq := by intro v; aesop--rw [BasedLift.proj_right v];
    }
  ⟩
⟩

instance instHasCartLift {x c d : C} (f : c ⟶ d) (e : x ⟶ c) : HasCartesianLift (P:= Cod) f :=
⟨ instCartLift f e ⟩

instance instCovCleavage : CovCleavage Cod (C:= C) where
  lift := fun f e => instCartCovLift f e

instance instHasCartCovLift {c d : C} (f : c ⟶ d) (e : Cod⁻¹ c) : HasCartesianCovLift (P:= Cod) f (e : Cod⁻¹ c) :=
⟨ instCartCovLift f e ⟩

instance instCovFibration : isOpFibration Cod (C:= C) where
  lift := fun f e => instHasCartCovLift f e

end Codomain
