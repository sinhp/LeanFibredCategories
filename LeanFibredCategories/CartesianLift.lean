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
import Frobenius.Fiber

universe u

namespace CategoryTheory
open Category Opposite

variable {C E : Type*} [Category C] [Category E]

@[ext]
structure BasedLift (P : E ⥤ C) {c d : C} (f : c ⟶ d) (src : P⁻¹ c) (tgt : P⁻¹ d) where
hom : (src : E) ⟶ (tgt : E)
eq : eqToHom (src.eq) ≫ f = (P.map hom) ≫ eqToHom (tgt.eq)

@[ext]
structure UnBasedLift (P : E ⥤ C) {c d : C} (f : c ⟶ d) where
src : P⁻¹ c
tgt : P⁻¹ d
hom : (src : E) ⟶ (tgt : E)
eq : eqToHom (src.eq) ≫ f = (P.map hom) ≫ eqToHom (tgt.eq)


section
variable (P : E ⥤ C){c d : C} (f : c ⟶ d){x: P⁻¹ c} {y : P⁻¹ d}
notation x " ⟶[" f "] " y => BasedLift (P:= _) f x y
end

@[ext]
structure Lift (P : E ⥤ C) {c d : C} (f : c ⟶ d) (tgt : P⁻¹ d) where
src : P⁻¹ c
lift : BasedLift P f src tgt

@[ext]
structure CoLift (P : E ⥤ C) {c d : C} (f : c ⟶ d) (src : P⁻¹ c) where
tgt : P⁻¹ d
lift : BasedLift P f src tgt

def HasLift (P : E ⥤ C) {c d : C} (f : c ⟶ d) (x : P⁻¹ d) := Nonempty (Lift P f x)

def HasCoLift (P : E ⥤ C) {c d : C} (f : c ⟶ d) (x : P⁻¹ c) := Nonempty (CoLift P f x)

namespace UnBasedLift
variable {P : E ⥤ C}

@[simp, aesop forward safe]
lemma proj (f : c ⟶ d) (g : UnBasedLift P f) : P.map g.hom = eqToHom (g.src.eq) ≫ f ≫ (eqToHom (g.tgt.eq).symm)  := by simp [← Category.assoc _ _ _, g.eq]

/-coercion from Lift to the total category -/
instance  : CoeOut (UnBasedLift P f) (Σ x y : E, x ⟶ y) where
  coe := fun l ↦ ⟨l.src, l.tgt, l.hom⟩

/-Regarding a morphism in Lift P f as a morphism in the total category E. -/
instance  : CoeDep (UnBasedLift P f) (l : UnBasedLift P f) ((l.src : E) ⟶ (l.tgt : E)) where
  coe := l.hom
end UnBasedLift


namespace BasedLift
variable {P : E ⥤ C}

/-coercion from Based Lift to the total category -/
instance (P : E ⥤ C) {c d : C} (f : c ⟶ d) (x : P⁻¹ c) (y : P⁻¹ d) : CoeOut (BasedLift P f x y) ((x : E) ⟶ (y : E)) where
  coe := fun l ↦ l.hom


/--Regarding a morphism of the total space as a based lift over its image-/
@[simps]
def tauto {e e' : E} (g : e ⟶ e') : (Fib.tauto e) ⟶[P.map g] (Fib.tauto e') := ⟨g, by simp only [Fib.tauto_fiber, eqToHom_refl, id_comp, comp_id]⟩

@[simp]
instance  {e e' : E} {g : e ⟶ e'} : CoeDep (e ⟶ e') (g) (Fib.tauto e  ⟶[P.map g] Fib.tauto e') where
  coe := tauto g

@[simp, aesop forward safe]
lemma proj {c d : C} {f : c ⟶ d} {x : P⁻¹ c} {y : P⁻¹ d} (g : BasedLift P f x y) : P.map g.hom = eqToHom (x.eq) ≫ f ≫ (eqToHom (y.eq).symm)  := by simp [← Category.assoc _ _ _, g.eq]

@[simp, aesop forward safe]
lemma proj_to_image (f : (P.obj x) ⟶ (P.obj y)) (e : (Fib.tauto x) ⟶[f] (Fib.tauto y)) : P.map e.hom = f := by simp only [Fib.coe_mk, proj, eqToHom_refl, comp_id, id_comp]

@[simp, aesop forward safe]
def id (x : P⁻¹ c) : BasedLift P (𝟙 c) x x := ⟨𝟙 _, by simp⟩

@[simp, aesop forward safe]
def comp {c d d': C} {f : c ⟶ d} {f' : d ⟶ d'} {x : P⁻¹ c} {y : P⁻¹ d} {z : P⁻¹ d'} (g : x ⟶[f] y) (g' : y ⟶[f'] z) : x ⟶[f ≫ f'] z :=
⟨g.hom ≫ g'.hom, by simp only [P.map_comp]; rw [assoc, proj g, proj g']; simp  ⟩

@[simp]
lemma comp_hom  {c d d': C} {f : c ⟶ d} {f' : d ⟶ d'} {x : P⁻¹ c} {y : P⁻¹ d} {z : P⁻¹ d'} (g : x ⟶[f] y) (g' : y ⟶[f'] z) : (comp g g').hom = g.hom ≫ g'.hom := rfl

@[simp]
def reassocBaseIso {c' c d d' : C} {u' : c' ⟶ c} {f : c ⟶ d} {u : d ⟶ d'} {x : P⁻¹ c'} {y : P⁻¹ d'} : (x ⟶[(u' ≫ f) ≫ u] y) ≃ (x ⟶[u' ≫ (f ≫ u)] y) where
  toFun := fun g ↦ by cases' g with g hg; exact ⟨g, by simp_all only [assoc]⟩
  invFun := fun g ↦ by cases' g with g hg; exact ⟨g, by simp_all only [assoc]⟩
  left_inv := by intro g; rfl
  right_inv := by intro g; rfl

@[simp]
lemma comp_assoc {c' c d d' : C} {f₁ : c' ⟶ c} {f₂ : c ⟶ d} {f₃ : d ⟶ d'} {w : P⁻¹ c'} {x : P⁻¹ c} {y : P⁻¹ d} {z : P⁻¹ d'} (g₁ : w ⟶[f₁] x) (g₂ : x ⟶[f₂] y) (g₃ : y ⟶[f₃] z) :  (comp (comp g₁ g₂) g₃) = reassocBaseIso.invFun (comp g₁ (comp g₂ g₃)) := by simp only [reassocBaseIso, comp, assoc]

@[simp]
lemma comp_assoc_inv {c' c d d' : C} {f₁ : c' ⟶ c} {f₂ : c ⟶ d} {f₃ : d ⟶ d'} {w : P⁻¹ c'} {x : P⁻¹ c} {y : P⁻¹ d} {z : P⁻¹ d'} (g₁ : w ⟶[f₁] x) (g₂ : x ⟶[f₂] y) (g₃ : y ⟶[f₃] z) :  reassocBaseIso.toFun (comp (comp g₁ g₂) g₃) =  (comp g₁ (comp g₂ g₃)) := by simp only [reassocBaseIso, comp, assoc]


@[simp]
def equivIdComp  {c d : C} {f : c ⟶ d} {x : P⁻¹ c} {y : P⁻¹ d} : (x ⟶[(𝟙 c) ≫ f] y) ≃ (x ⟶[f] y)  where
  toFun := fun g ↦ ⟨g.hom, by simp only [proj, id_comp, assoc, eqToHom_trans, eqToHom_refl, comp_id]⟩ -- aesop generates a proof of this
  invFun := fun g ↦ comp (id x) g
  left_inv := by intro g; simp only [comp, id, id_comp] -- aesop generates a proof of this
  right_inv := by intro g; simp only [comp, id, id_comp] -- aesop

@[simp]
def equivCompId  {c d : C} {f : c ⟶ d} {x : P⁻¹ c} {y : P⁻¹ d} : (x ⟶[f ≫ (𝟙 d) ] y)  ≃ (x ⟶[f] y) where
  toFun := fun g ↦ ⟨g.hom, by simp only [proj, id_comp, assoc, eqToHom_trans, eqToHom_refl, comp_id]⟩ -- aesop generates a proof of this
  invFun := fun g ↦ comp g (id y)
  left_inv := by intro g; simp only [comp, id, comp_id] -- aesop generates a proof of this
  right_inv := by intro g; simp only [comp, id, comp_id] -- aesop

end BasedLift

abbrev TotalCat {C E : Type*} [Category C] [Category E] (P : E ⥤ C) := Fib.Total P.obj
prefix:75 " ∫ "  => TotalCat

@[ext]
structure TotalCatHom {P : E ⥤ C} (X Y : ∫ P) where
base : X.1 ⟶ Y.1
fiber : X.2 ⟶[base] Y.2

@[simps]
instance (P : E ⥤ C) : Category (∫ P) where
  Hom X Y := TotalCatHom X Y
  id X := ⟨𝟙 X.1 , BasedLift.id X.2⟩
  comp := @fun X Y Z f g => ⟨f.1 ≫ g.1, BasedLift.comp f.2 g.2⟩
  id_comp := by intro X Y f; cases' f with f1 f2; simp only [id_comp]; ext; simp only [id_comp]; simp only [id_comp]; simp; sorry
  comp_id := by intro X Y f; cases' f with f1 f2; sorry
  assoc := by intro X Y Z W f g h; sorry -- seems we cannot prove it; in fact i think ∫ P does not admit a category structure but a bicategory structure.


namespace Lift
variable {P : E ⥤ C}

instance  : CoeOut (Lift P f y) (Σ x : E, (x : E) ⟶ y) where
  coe := fun l ↦ ⟨l.src, l.lift.hom⟩

@[simp, aesop forward safe]
lemma proj (f : c ⟶ d) (y : P⁻¹ d) (g : Lift P f y) : P.map g.lift.hom = (eqToHom (g.src.eq)) ≫ f ≫ eqToHom (y.eq).symm  := by simp only [BasedLift.proj]

/-- Regarding a morphism in Lift P f as a morphism in the total category E. -/
instance  : CoeDep (Lift P f y) (l : Lift P f y) ((l.src : E) ⟶ (y : E)) where
  coe := l.lift.hom
end Lift


/-- A lift g : x ⟶[f] y over f is cartesian if for every morphism u in the base and every lift g' : x ⟶[u ≫ f] z over u ≫ f, there is a unique lift l : y ⟶[u] z over u such that l ≫ g = g'. -/
class CartesianBasedLift {P : E ⥤ C} {c d : C} {f : c ⟶ d} {x : P⁻¹ c} {y : P⁻¹ d} (g : x ⟶[f] y) where
uniq_lift : ∀ ⦃c' : C⦄ ⦃z : P⁻¹ c'⦄ (u : c' ⟶ c) (g' : z ⟶[u ≫ f]  y), Unique { l :  z ⟶[u] x // (BasedLift.comp l g) = g' }

/-- A morphism g : x ⟶[f] y over f is cocartesian if for all morphisms u in the base and g' : x ⟶[f ≫ u] z over f ≫ u, there is a unique morphism l : y ⟶[u] z over u such that g ≫ l = g'. -/
-- @[simp]
class CoCartesianBasedLift {P : E ⥤ C} {c d : C} {f : c ⟶ d} {x : P⁻¹ c} {y : P⁻¹ d} (g : x ⟶[f] y) where
uniq_colift : ∀ ⦃d' : C⦄ ⦃z : P⁻¹ d'⦄ (u : d ⟶ d') (g' : x ⟶[f ≫ u]  z), Unique { l :  y ⟶[u] z // (BasedLift.comp g l) = g' }


section CartesianBasedLift
variable {P : E ⥤ C} {c' c d : C} {f : c ⟶ d} {x : P⁻¹ c} {y : P⁻¹ d} {x' : P⁻¹ c'} (g : x ⟶[f] y) [CartesianBasedLift (P:= P) g]

/-- The canonical map from a lift g' : x' ⟶[u ≫ f] y to the cartesian lift of f. -/
@[simp]
def gaplift (u : c' ⟶ c) (g' : x' ⟶[u ≫ f] y) : x' ⟶[u] x := (CartesianBasedLift.uniq_lift (P:= P) (f:= f) (g:= g) (z:= x') u g').default.val

/-- The composition of the gap map and the cartesian lift is the given lift -/
@[simp]
lemma gaplift_property (u : c' ⟶ c) (g' : x' ⟶[u ≫ f] y) : BasedLift.comp (gaplift g u g') g = g' := (CartesianBasedLift.uniq_lift (P:= P) (f:= f) (g:= g) (z:= x') u g').default.property

@[simp]
lemma gaplift_hom_property (u : c' ⟶ c) (g' : x' ⟶[u ≫ f] y) : (gaplift g u g').hom ≫  g.hom = g'.hom := by rw [← BasedLift.comp_hom _ _]; congr 1; exact gaplift_property g u g'

@[simp]
lemma gaplift_uniq {u : c' ⟶ c} (g' : x' ⟶[u ≫ f] y) (v : x' ⟶[u] x) (hv : BasedLift.comp v g = g') : v = gaplift (g:= g) u g' := by simp [gaplift]; rw [← (CartesianBasedLift.uniq_lift (P:= P) (f:= f) (g:= g) (z:= x') u g').uniq ⟨v,hv⟩]

/-- The composition of gap maps with respect two gaps u: c' ⟶ c and u' : c'' ⟶ c  is the gap map of the composition u' ≫ u. -/
@[simp]
lemma gaplift_comp {u : c' ⟶ c} {u' : c'' ⟶ c'} {x'' : P⁻¹ c''} (g' : x' ⟶[u ≫ f] y) [CartesianBasedLift (P:= P) (f:= u ≫ f) g'] (g'' : x'' ⟶[u' ≫ u ≫ f] y) :
BasedLift.comp (gaplift  (g:= g') u' g'') (gaplift (g:= g) u g') = gaplift (g:= g) (u' ≫ u) (BasedLift.reassocBaseIso.invFun g'') := by refine gaplift_uniq (f:= f) g (BasedLift.reassocBaseIso.invFun g'') (BasedLift.comp (gaplift  (g:= g') u' g'') (gaplift (g:= g) u g')) (by rw [BasedLift.comp_assoc]; simp only [gaplift_property])

end CartesianBasedLift


section CoCartesianBasedLift
variable {P : E ⥤ C} {c d d': C} {f : c ⟶ d} {x : P⁻¹ c} {y : P⁻¹ d} {y' : P⁻¹ d'} (g : x ⟶[f] y) [CoCartesianBasedLift (P:= P) g]

@[simp]
def cogaplift (u : d ⟶ d') (g' : x ⟶[f ≫ u] y') : y ⟶[u] y' :=
(CoCartesianBasedLift.uniq_colift (P:= P) (f:= f) (g:= g) (z:= y') u g').default.val

/-- The composition of the cogap map and the cocartesian lift is the given lift -/
@[simp]
lemma cogaplift_property (u : d ⟶ d') (g' : x ⟶[f ≫ u] y') : BasedLift.comp g (cogaplift g u g') = g' := (CoCartesianBasedLift.uniq_colift (P:= P) (f:= f) (g:= g) (z:= y') u g').default.property

@[simp]
lemma cogaplift_hom_property (u : d ⟶ d') (g' : x ⟶[f ≫ u] z) : g.hom ≫ (cogaplift g u g').hom = g'.hom := by rw [← BasedLift.comp_hom _ _]; congr 1; exact cogaplift_property g u g'

/-- The uniqueness part of the universal property of the cogap lift -/
@[simp]
lemma cogaplift_uniq  {u : d ⟶ d'} (g' : x ⟶[f ≫ u] y') (v : y ⟶[u] y') (hv : BasedLift.comp g v = g') : v = cogaplift (g:= g) u g' := by
simp [cogaplift]
rw [← (CoCartesianBasedLift.uniq_colift (P:= P) (f:= f) (g:= g) (z:= y') u g').uniq ⟨v,hv⟩]

/-- The composition of cogap maps with respect two gaps u: d ⟶ d' and u' : d' ⟶ d''  is the cogap lift of the composition u ≫ u'. -/
@[simp]
lemma cogaplift_comp {u : d ⟶ d'} {u' : d' ⟶ d''} {y'' : P⁻¹ d''} (g' : x ⟶[f ≫ u] y') [CoCartesianBasedLift (P:= P) g'] (g'' : x ⟶[(f ≫ u) ≫ u'] y'') : BasedLift.comp  (cogaplift (g:= g) u g') (cogaplift (g:= g') u' g'') = cogaplift (g:= g) (u ≫ u') (BasedLift.reassocBaseIso.toFun g'') := by refine cogaplift_uniq (f:= f) g (BasedLift.reassocBaseIso.toFun g'') ( BasedLift.comp  (cogaplift (g:= g) u g') (cogaplift (g:= g') u' g'')) (by rw [← BasedLift.comp_assoc_inv]; simp only [cogaplift_property])

end CoCartesianBasedLift


@[simp]
abbrev CartesianMorphism {P : E ⥤ C} {x y : E} (g : x ⟶ y) := CartesianBasedLift (P:= P) (BasedLift.tauto g) -- note `def` did not work with instance synthesis in gapmap below and also makes the CartesianMorphism a function not a class

section CartesianMorphism
variable {P : E ⥤ C} {x y : E} (g : x ⟶ y) [CartesianMorphism (P:= P) g]

def gapmap {x' : E} (u : P.obj x' ⟶ P.obj x) (g' : (Fib.tauto x') ⟶[u ≫ P.map g] (Fib.tauto y)) : x' ⟶ x :=  (gaplift (BasedLift.tauto g) u g').hom

/-- The composition of the gap map and the cartesian lift is the given lift -/
@[simp]
lemma gapmap_property  (x' : E) (u : P.obj x' ⟶ P.obj x) (g' : (Fib.tauto x') ⟶[u ≫ P.map g] (Fib.tauto y)) : (gapmap g  u g' : x' ⟶ x ) ≫ g = g'.hom := gaplift_hom_property (BasedLift.tauto g) u g'

/-- The uniqueness part of the universal property of the gap map -/
@[simp]
lemma gapmap_uniq {x' : E} (u : P.obj x' ⟶ P.obj x) (g' : (Fib.tauto x') ⟶[u ≫ P.map g] (Fib.tauto y)) (v : (Fib.tauto x') ⟶[u] (Fib.tauto x)) (hv : BasedLift.comp v (BasedLift.tauto g) = g') : v.hom = gapmap g u g' := by congr 1; exact gaplift_uniq (BasedLift.tauto g) g' v hv

end CartesianMorphism


@[simp]
abbrev CoCartesianMorphism {P : E ⥤ C} {x y : E} (g : x ⟶ y) := CoCartesianBasedLift (P:= P) (c:= P.obj x) (d:= P.obj y) (BasedLift.tauto g) -- note `def` did not work with instance synthesis in gapmap below and also makes the CartesianMorphism a function not a class

section CoCartesianMorphism
variable {P : E ⥤ C} {x y : E} (g : x ⟶ y) [CoCartesianMorphism (P:= P) g]

def cogapmap {y' : E} (u : P.obj y ⟶ P.obj y') (g' : (Fib.tauto x) ⟶[P.map g ≫ u] (Fib.tauto y')) : y ⟶ y' :=  (cogaplift (BasedLift.tauto g) u g').hom

@[simp]
lemma cogapmap_property  (y' : E) (u : P.obj y ⟶ P.obj y') (g' : (Fib.tauto x) ⟶[P.map g ≫ u] (Fib.tauto y')) : g ≫ (cogapmap g  u g' : y ⟶ y' ) = g'.hom := cogaplift_hom_property (BasedLift.tauto g) u g'

@[simp]
lemma cogapmap_uniq {y' : E} (u : P.obj y ⟶ P.obj y') (g' : (Fib.tauto x) ⟶[P.map g ≫ u] (Fib.tauto y')) (v : (Fib.tauto y) ⟶[u] (Fib.tauto y')) (hv : BasedLift.comp (BasedLift.tauto g) v = g') : v.hom = cogapmap g u g' := by congr 1; exact cogaplift_uniq (BasedLift.tauto g) g' v hv

end CoCartesianMorphism


@[simp]
def isCartesianMorphism {P : E ⥤ C} {x y : E} (g : x ⟶ y) : Prop := ∀ ⦃c: C⦄ ⦃z: P⁻¹ c⦄ (u : c ⟶ P.obj x) (g' : z ⟶[u ≫ P.map g] Fib.tauto  y),
∃! (l : z ⟶[u] Fib.tauto x), l.hom ≫ g = g'.hom

/-- Axiom of choice gives for mere (unique) existence of gap map the data of a unique gap map. -/
instance {P : E ⥤ C} {x y : E} (g : x ⟶ y) (hcart: isCartesianMorphism (P:= P) g) : Nonempty (CartesianMorphism (P:= P) g) := ⟨{
  uniq_lift := fun c' x' u g' => {
    default := {
      val := ⟨(Classical.choose (hcart u g')).hom, by simp only [Fib.tauto_fiber, BasedLift.proj, eqToHom_refl, comp_id]⟩
      property := by ext; simp; exact (Classical.choose_spec (hcart u g')).1;
    }
    uniq := by intro l
               ext
               simp
               have : l.1.hom ≫ g = g'.hom := by simp [l.2]; aesop
               congr 1
               refine (Classical.choose_spec (hcart u g')).2 l.1 this
  }
}⟩

@[simp]
def CartMor (P : E ⥤ C) : MorphismProperty E :=  fun _ _ g => isCartesianMorphism (P:= P) g -- Nonempty (CartesianMorphism (P:= P) g)

section CartMor
variable {P : E ⥤ C}

@[simp]
def equivCompImageId  {c : C} {x : P⁻¹ c} {e : E} {u: c ⟶ P.obj e} : (x ⟶[u ≫ P.map (𝟙 e)] e) ≃ (x ⟶[u] e) where
  toFun := sorry
  invFun := fun g ↦ BasedLift.comp g (BasedLift.id e)
  --invFun := fun g ↦ ⟨g.hom, by simp only [proj, id_comp, assoc, eqToHom_trans, eqToHom_refl, comp_id]⟩ -- aesop generates a proof of this
  left_inv := by intro g; simp only [comp, id, comp_id] -- aesop generates a proof of this
  right_inv := by intro g; simp only [comp, id, comp_id] -- aesop


@[simp] lemma cart_id (e : E) : CartMor P (𝟙 e) := fun c z u g' ↦ ⟨BasedLift.equivCompId.invFun g', by sorry⟩


#exit
-- fun z g' u hu ↦
-- by use ⟨g', by aesop⟩;


-- @[simp] lemma cart_id (e : E) : CartMor P (𝟙 e) := ⟨ {
--   uniq_lift := fun c' z u g' => {
--     default := ⟨BasedLift.equivCompId.invFun g' , sorry⟩
--     uniq := _
--   }
-- } ⟩

#check BasedLift.equivCompId.toFun



end CartMor





@[simp]
def isCoCartesianMorphism {P : E ⥤ C} {x y : E} (g : x ⟶ y) : Prop := ∀ ⦃c: C⦄ ⦃z: P⁻¹ c⦄ (u : P.obj y ⟶ c) (g' : Fib.tauto x ⟶[P.map g ≫ u] z), ∃! (l : Fib.tauto y ⟶[u] z), g ≫ l.hom = g'.hom

/-- Axiom of choice gives for mere (unique) existence of cogap map the data of a unique cogap map. -/
instance {P : E ⥤ C} {x y : E} (g : x ⟶ y) (hcocart: isCoCartesianMorphism (P:= P) g) : Nonempty (CoCartesianMorphism (P:= P) g) := ⟨{
  uniq_colift := fun c' x' u g' => {
    default := {
      val := ⟨(Classical.choose (hcocart u g')).hom, by aesop⟩
      property := by ext; simp; exact (Classical.choose_spec (hcocart u g')).1;
    }
    uniq := by intro l
               ext
               simp
               have : g ≫ l.1.hom = g'.hom := by simp [l.2]; aesop
               congr 1
               refine (Classical.choose_spec (hcocart u g')).2 l.1 this
  }
}⟩



@[simp]
def CoCartMor (P : E ⥤ C): MorphismProperty E :=  fun _ _ f => isCoCartesianMorphism (P:= P) f

@[simp]
lemma cocart_id (e : E) : CoCartMor (P:= P) (𝟙 e) := fun z g' u hu ↦ by
use ⟨g', by aesop⟩
simp

@[simp]
lemma cocart_comp (f : w ⟶ x) (g : x ⟶ y) : CoCartMor (P:= P) f → CoCartMor (P:= P) g → CoCartMor (P:= P) (f ≫ g) := fun h₁ h₂ z g' u hu ↦ by
have hu' : P.map f ≫ P.map g ≫ u = P.map g' := by simpa [Functor.map_comp, Category.assoc] using hu
cases' (h₁ g' (P.map g ≫ u) hu') with l_f hlf
cases' (h₂ l_f.hom u (by rw [BasedLift.proj_to_image])) with l_g hlg
use l_g
constructor
· simp_all only [CoCartMor, CoCartesianMorphism, Fib.coe_mk, Functor.map_comp, Category.assoc]
· intro v hv; apply hlg.2; apply hlf.2 (⟨ g ≫ v.hom, _⟩ ); simp only [← Category.assoc]; exact hv; simp



section CartesianLift
variable {P : E ⥤ C} {c d : C}

class CoCartUnBasedLift (f : c ⟶ d) extends UnBasedLift P f where
cart : CoCartesianMorphism (P:= P) hom

def HasCoCartUnBasedLift (f : c ⟶ d) := Nonempty (CoCartUnBasedLift (P:= P) f)

class CartBasedLift (P : E ⥤ C) {c d : C} (f : c ⟶ d) (src : P⁻¹ c) (tgt : P⁻¹ d) extends BasedLift P f src tgt where
is_cart : CartesianBasedLift (P:= P) toBasedLift

class CartBasedMor (P : E ⥤ C) {c d : C} (f : c ⟶ d) (src : P⁻¹ c) (tgt : P⁻¹ d) extends BasedLift P f src tgt where
cart : CoCartesianMorphism P hom

instance CoeOut {c d : C} (f : c ⟶ d) (src : P⁻¹ c) (tgt : P⁻¹ d) : CoeOut (CartBasedLift P f src tgt) (src.fiber ⟶ tgt.fiber) where
  coe := fun l ↦ l.1.hom

class CartLift (f : c ⟶ d) (y : P⁻¹ d) extends Lift P f y where
is_cart : CartesianBasedLift (P:= P) lift

class CoCartLift (f : c ⟶ d) (x : P⁻¹ c) extends CoLift P f x where
is_cart : CoCartesianBasedLift (P:= P) f lift

class CartMor (f : c ⟶ d) (y : P⁻¹ d) extends Lift P f y where
is_cart : CoCartesianMorphism (P:= P) lift.hom

def HasCartLift (f : c ⟶ d) (y : P⁻¹ d) := Nonempty (CartLift (P:= P) f y)

def HasCoCartLift (f : c ⟶ d) (x : P⁻¹ c) := Nonempty (CoCartLift (P:= P) f x)

end CartesianLift


abbrev Cart ( _ : E ⥤ C) := E

/-- The subcategory of cartesian arrows -/
instance : Category (Cart P) where
  Hom x y := { f : x ⟶ y |  CoCartMor (P:= P) f }
  id x := ⟨𝟙 x, cocart_id P x⟩
  comp := @fun x y z f g => ⟨ f.1 ≫ g.1, cocart_comp P f.1 g.1 f.2 g.2⟩

namespace Cart
/-- The forgetful functor from the category of cartesian arrows to the total category -/
def forget : Cart P ⥤ E where
obj := fun x => x
map := @fun x y f => f

end Cart
end CoCartesianMorphism
