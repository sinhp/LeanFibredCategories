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
import Mathlib.CategoryTheory.Iso
import Mathlib.CategoryTheory.Limits.Shapes.Pullbacks
import Mathlib.CategoryTheory.Limits.Preserves.Basic
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks
import LeanFibredCategories.Fiber


universe u

namespace CategoryTheory
open Category Opposite Functor Limits Cones

variable {C E : Type*} [Category C] [Category E]

/-NoteToSelf: we use `structure` declaration rather than subtype definition (akin to `Fib` in `Frobenius.Fiber`) since later we want to extend this structure it to get the **class** `CartBasedLifts`. -/
@[ext]
structure BasedLift (P : E ⥤ C) {c d : C} (f : c ⟶ d) (src : P⁻¹ c) (tgt : P⁻¹ d) where
hom : (src : E) ⟶ (tgt : E)
over : (P.map hom) ≫ eqToHom (tgt.over) = eqToHom (src.2) ≫ f

@[ext]
structure UnBasedLift (P : E ⥤ C) {c d : C} (f : c ⟶ d) where
src : P⁻¹ c
tgt : P⁻¹ d
hom : (src : E) ⟶ (tgt : E)
over :  (P.map hom) ≫ eqToHom (tgt.2) = eqToHom (src.2) ≫ f


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
colift : BasedLift P f src tgt

def HasLift (P : E ⥤ C) {c d : C} (f : c ⟶ d) (x : P⁻¹ d) := Nonempty (Lift P f x)

def HasCoLift (P : E ⥤ C) {c d : C} (f : c ⟶ d) (x : P⁻¹ c) := Nonempty (CoLift P f x)

namespace UnBasedLift
variable {P : E ⥤ C}

@[simp, aesop forward safe]
lemma over_base (f : c ⟶ d) (g : UnBasedLift P f) : P.map g.hom = eqToHom (g.src.2) ≫ f ≫ (eqToHom (g.tgt.2).symm) := by simp [← Category.assoc _ _ _, ← g.over]

/--Coercion from Lift to the total category -/
instance  : CoeOut (UnBasedLift P f) (Σ x y : E, x ⟶ y) where
  coe := fun l ↦ ⟨l.src, l.tgt, l.hom⟩

/--Regarding a morphism in Lift P f as a morphism in the total category E. -/
instance  : CoeDep (UnBasedLift P f) (l : UnBasedLift P f) ((l.src : E) ⟶ (l.tgt : E)) where
  coe := l.hom
end UnBasedLift


namespace BasedLift
variable {P : E ⥤ C}

@[simp, aesop forward safe]
lemma over_base {c d : C} {f : c ⟶ d} {x : P⁻¹ c} {y : P⁻¹ d} (g : BasedLift P f x y) : P.map g.hom = eqToHom (x.2) ≫ f ≫ (eqToHom (y.over).symm)  := by simp [← Category.assoc _ _ _, ← g.over]

/--Coercion from Based Lift to the total category -/
instance (P : E ⥤ C) {c d : C} (f : c ⟶ d) (x : P⁻¹ c) (y : P⁻¹ d) : CoeOut (BasedLift P f x y) ((x : E) ⟶ (y : E)) where
  coe := fun l ↦ l.hom

/--Regarding a morphism of the total space as a based lift over its image-/
@[simps]
def tauto {e e' : E} (g : e ⟶ e') : (Fib.tauto e) ⟶[P.map g] (Fib.tauto e') := ⟨g, by simp only [Fib.tauto, eqToHom_refl, id_comp, comp_id]⟩

@[simps]
instance {e e' : E} {g : e ⟶ e'} : CoeDep (e ⟶ e') (g) (Fib.tauto e  ⟶[P.map g] Fib.tauto e') where
  coe := tauto g

lemma hom_ext {c d : C} {f : c ⟶ d} {x : P⁻¹ c} {y : P⁻¹ d} {g₁ g₂ : x ⟶[f] y} (h : g₁.hom = g₂.hom) : g₁ = g₂ := by
  cases g₁; cases g₂; congr

@[simp]
instance instFibHom {c : C} {x y : P⁻¹ c} : Coe (x ⟶[𝟙 c] y) (x ⟶ y) where
  coe := fun f ↦ ⟨ f.hom , by simp [f.over]⟩

@[simps]
def ofFibHom {c : C} {x y : P⁻¹ c} (f : x ⟶ y) : x ⟶[𝟙 c] y := ⟨f.1, by simp [f.2]⟩

@[simp, aesop forward safe]
lemma tauto_over_base (f : (P.obj x) ⟶ (P.obj y)) (e : (Fib.tauto x) ⟶[f] (Fib.tauto y)) : P.map e.hom = f := by simp only [Fib.coe_mk, over_base, eqToHom_refl, comp_id, id_comp]

@[simp, aesop forward safe]
def id (x : P⁻¹ c) : BasedLift P (𝟙 c) x x := ⟨𝟙 _, by simp⟩

@[simp]
lemma id_hom {x : P⁻¹ c} : (id x).hom = 𝟙 _ := rfl

@[simp, aesop forward safe]
def comp {c d d': C} {f : c ⟶ d} {f' : d ⟶ d'} {x : P⁻¹ c} {y : P⁻¹ d} {z : P⁻¹ d'} (g : x ⟶[f] y) (g' : y ⟶[f'] z) : x ⟶[f ≫ f'] z :=
⟨g.hom ≫ g'.hom, by simp only [P.map_comp]; rw [assoc, over_base g, over_base g']; simp  ⟩

section
variable (P : E ⥤ C){c d d': C}{x: P⁻¹ c} {y : P⁻¹ d} {z : P⁻¹ d'} (u : c ⟶ d) (v: d ⟶ d') (f : x ⟶[u] y) (g : y ⟶[v] z)
notation f " ≫[l] " g => BasedLift.comp f g
end

@[simp, aesop forward safe]
lemma comp_hom  {c d d': C} {f₁ : c ⟶ d} {f₂ : d ⟶ d'} {x : P⁻¹ c} {y : P⁻¹ d} {z : P⁻¹ d'} (g₁ : x ⟶[f₁] y) (g₂ : y ⟶[f₂] z) : (g₁ ≫[l] g₂).hom = g₁.hom ≫ g₂.hom := rfl

@[simp]
lemma comp_hom_over {c d d': C} {f₁ : c ⟶ d} {f₂ : d ⟶ d'} {x : P⁻¹ c} {y : P⁻¹ d} {z : P⁻¹ d'} {g₁ : x ⟶[f₁] y} {g₂ : y ⟶[f₂] z} {h : x ⟶[f₁ ≫ f₂] z} : (g₁ ≫[l] g₂) = h ↔ g₁.hom ≫ g₂.hom = h.hom := by
constructor
· intro H; rw [← H]; simp
· intro H; ext; simp [H]

@[simp]
lemma comp_tauto_hom {x y z : E} {f : P.obj x ⟶ P.obj y} {l : Fib.tauto x ⟶[f] (Fib.tauto y)} {g : y ⟶ z} : (l ≫[l] tauto g).hom = l.hom ≫ g := rfl

@[simps]
def eqRebase {c d : C} {f f' : c ⟶ d} {x : P⁻¹ c} {y : P⁻¹ d} (h : f = f') : (x ⟶[f] y) ≃ (x ⟶[f'] y) where
  toFun := fun g ↦ ⟨g.hom, by rw [←h, g.over]⟩
  invFun := fun g ↦ ⟨g.hom, by rw [h, g.over]⟩
  left_inv := by intro g; simp
  right_inv := by intro g; simp

 --⟨g.hom, by simp [g.over]⟩
@[simps!]
def eqRebaseToHom {c d : C} {f : c ⟶ d} {x : P⁻¹ c} {y : P⁻¹ d} :
(x ⟶[f] y) ≃ (x.1 ⟶[(eqToHom x.2) ≫ f] y) where
  toFun := fun g => ⟨g.hom, by simp [g.over]⟩
  invFun := fun g => ⟨g.hom, by simp [g.over]⟩
  left_inv := by intro g; simp
  right_inv := by intro g; simp

@[simps!]
def eqRebaseAssoc {c' c d d' : C} {u' : c' ⟶ c} {f : c ⟶ d} {u : d ⟶ d'} {x : P⁻¹ c'} {y : P⁻¹ d'} : (x ⟶[(u' ≫ f) ≫ u] y) ≃ (x ⟶[u' ≫ (f ≫ u)] y) := eqRebase (Category.assoc u' f u)

@[simp]
lemma eqRebaseToHom_cancel {c c' d : C} {u : c' ⟶ c} {f : c ⟶ d} {x' : P⁻¹ c'} {x : P⁻¹ c} {y : P⁻¹ d}  {l : x' ⟶[u] x} {g : x ⟶[f] y} {g' : x' ⟶[u ≫ f] y} : (l ≫[l] g) = g' ↔ ((eqRebaseToHom.toFun l) ≫[l] g) = eqRebaseAssoc.invFun (eqRebaseToHom.toFun g') := by sorry

@[simp]
lemma assoc {c' c d d' : C} {f₁ : c' ⟶ c} {f₂ : c ⟶ d} {f₃ : d ⟶ d'} {w : P⁻¹ c'} {x : P⁻¹ c} {y : P⁻¹ d} {z : P⁻¹ d'} (g₁ : w ⟶[f₁] x) (g₂ : x ⟶[f₂] y) (g₃ : y ⟶[f₃] z) :  ((g₁ ≫[l] g₂) ≫[l] g₃) = eqRebaseAssoc.invFun (comp g₁ (comp g₂ g₃)) := by simp only [comp, Category.assoc, eqRebaseAssoc, eqRebase]

@[simp]
lemma assoc_inv {c' c d d' : C} {f₁ : c' ⟶ c} {f₂ : c ⟶ d} {f₃ : d ⟶ d'} {w : P⁻¹ c'} {x : P⁻¹ c} {y : P⁻¹ d} {z : P⁻¹ d'} (g₁ : w ⟶[f₁] x) (g₂ : x ⟶[f₂] y) (g₃ : y ⟶[f₃] z) :  eqRebaseAssoc.toFun ((g₁ ≫[l] g₂) ≫[l] g₃) =  (g₁ ≫[l] (g₂ ≫[l] g₃)) := by simp only [comp, Category.assoc, eqRebaseAssoc, eqRebase]

@[simp]
def eqRebaseIdComp  {c d : C} {f : c ⟶ d} {x : P⁻¹ c} {y : P⁻¹ d} : (x ⟶[(𝟙 c) ≫ f] y) ≃ (x ⟶[f] y)  := eqRebase (id_comp f)

@[simp]
def eqRebaseCompId  {c d : C} {f : c ⟶ d} {x : P⁻¹ c} {y : P⁻¹ d} : (x ⟶[f ≫ (𝟙 d) ] y)  ≃ (x ⟶[f] y) := eqRebase (comp_id f)

@[simp]
lemma tauto_comp {e e' e'' : E} {g : e ⟶ e'} {g' : e' ⟶ e''} : tauto (g ≫ g') = eqRebase (P.map_comp g g').symm (tauto g ≫[l] tauto g') := rfl

@[simp]
lemma eqRebase_hom {c d : C} {f f' : c ⟶ d} {x : P⁻¹ c} {y : P⁻¹ d} {g : x ⟶[f] y} {h : f = f'} : (eqRebase h g).hom = g.hom := rfl

@[simp]
lemma tauto_comp_hom {e e' e'' : E} {g : e ⟶ e'} {g' : e' ⟶ e''} : (tauto (P:= P) g ≫[l] tauto (P:= P) g').hom = g ≫ g' := rfl


namespace Vertical

def vertBasedLiftEquiv {c : C} {x y : P⁻¹ c} : (x ⟶ y) ≃ (x ⟶[𝟙 c] y) where
  toFun := fun g ↦ ⟨g.1, by simp [g.2]⟩
  invFun := fun g ↦ g
  left_inv := by intro g; simp
  right_inv := by intro g; simp

end Vertical

end BasedLift


class IsoBasedLift {C E : Type*} [Category C] [Category E] {P : E ⥤ C} {c d : C} (f : c ⟶ d) [IsIso f] (x : P⁻¹ c) (y : P⁻¹ d) extends (x ⟶[f] y) where
  is_iso_hom : IsIso hom


/-- With this definition IsoBasedLift_inv becomes computable. -/
class IsoBasedLift' {C E : Type*} [Category C] [Category E] {P : E ⥤ C} {c d : C} (f : c ≅ d) (x : P⁻¹ c) (y : P⁻¹ d)  extends ((x : E) ≅ y) where
  -- The isomorphism lies over f
  eq : eqToHom (x.over) ≫ f.hom = (P.map hom) ≫ eqToHom (y.over) -- toIso.hom

namespace IsoBasedLift
variable {P : E ⥤ C} {c d : C} {f : c ⟶ d} [IsIso f] {x : P⁻¹ c} {y : P⁻¹ d}
notation x " ⟶[≅" f "] " y => IsoBasedLift (P:= _) f x y

@[simp]
instance instIsoOfIsoBasedLift (g : (x ⟶[≅f] y)) : IsIso g.hom := g.is_iso_hom

/-- Coercion from IsoBasedLift to BasedLift -/
instance : Coe (x ⟶[≅f] y) (x ⟶[f] y) where
  coe := fun l => ⟨l.hom, l.over⟩

namespace Vertical

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

end Vertical

noncomputable
def IsoBasedLift_inv (g : x ⟶[≅f] y) : (y ⟶[≅ inv f] x) where
  hom := inv g.hom
  over := by simp only [Iso.symm_hom, Functor.map_inv, BasedLift.over_base, IsIso.inv_comp, inv_eqToHom, IsIso.Iso.inv_hom,
  assoc, eqToHom_trans, eqToHom_refl, comp_id]
  is_iso_hom := IsIso.inv_isIso

end IsoBasedLift


namespace Lift
variable {P : E ⥤ C}

instance  : CoeOut (Lift P f y) (Σ x : E, (x : E) ⟶ y) where
  coe := fun l ↦ ⟨l.src, l.lift.hom⟩

@[simp, aesop forward safe]
lemma over_base (f : c ⟶ d) (y : P⁻¹ d) (g : Lift P f y) : P.map g.lift.hom = (eqToHom (g.src.over)) ≫ f ≫ eqToHom (y.over).symm  := by simp only [BasedLift.over_base]

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


namespace CartesianBasedLift
open BasedLift

variable {P : E ⥤ C} {c' c d : C} {f : c ⟶ d} {x : P⁻¹ c} {y : P⁻¹ d} {x' : P⁻¹ c'} (g : x ⟶[f] y) [CartesianBasedLift (P:= P) g]

/-- The canonical map from a lift g' : x' ⟶[u ≫ f] y to the cartesian lift of f. -/
@[simp]
def gaplift (u : c' ⟶ c) (g' : x' ⟶[u ≫ f] y) : x' ⟶[u] x := (CartesianBasedLift.uniq_lift (P:= P) (f:= f) (g:= g) (z:= x') u g').default.val

/-- The composition of the gap map and the cartesian lift is the given lift -/
@[simp]
lemma gaplift_property (u : c' ⟶ c) (g' : x' ⟶[u ≫ f] y) : ((gaplift g u g') ≫[l] g) = g' := (CartesianBasedLift.uniq_lift (P:= P) (f:= f) (g:= g) (z:= x') u g').default.property

/-- A variant of the gaplift property isolating the equality of morphisms in the total category. -/
@[simp]
lemma gaplift_hom_property (u : c' ⟶ c) (g' : x' ⟶[u ≫ f] y) : (gaplift g u g').hom ≫  g.hom = g'.hom := by rw [← BasedLift.comp_hom _ _]; congr 1; exact gaplift_property g u g'

/-- The uniqueness part of the universal property of the gap lift. -/
@[simp]
lemma gaplift_uniq {u : c' ⟶ c} (g' : x' ⟶[u ≫ f] y) (v : x' ⟶[u] x) (hv : (v ≫[l] g) = g') : v = gaplift (g:= g) u g' := by simp [gaplift]; rw [← (CartesianBasedLift.uniq_lift (P:= P) (f:= f) (g:= g) (z:= x') u g').uniq ⟨v,hv⟩]

/-- A variant of the  uniqueness lemma. -/
@[simp]
lemma gaplift_uniq' {u : c' ⟶ c} (v : x' ⟶[u] x) (v' : x' ⟶[u] x) (hv : (v ≫[l] g) = v' ≫[l] g) : v = v' := by rw [gaplift_uniq g (v' ≫[l] g) v hv]; symm; apply gaplift_uniq; rfl

/-- The composition of gap lifts with respect to morphisms u : c' ⟶ c and u' : c'' ⟶ c  is the gap lift of the composition u' ≫ u. -/
@[simp]
lemma gaplift_comp {u : c' ⟶ c} {u' : c'' ⟶ c'} {x'' : P⁻¹ c''} (g' : x' ⟶[u ≫ f] y) [CartesianBasedLift (P:= P) (f:= u ≫ f) g'] (g'' : x'' ⟶[u' ≫ u ≫ f] y) :
BasedLift.comp (gaplift  (g:= g') u' g'') (gaplift (g:= g) u g') = gaplift (g:= g) (u' ≫ u) (BasedLift.eqRebaseAssoc.invFun g'') := by refine gaplift_uniq (f:= f) g (BasedLift.eqRebaseAssoc.invFun g'') (BasedLift.comp (gaplift  (g:= g') u' g'') (gaplift (g:= g) u g')) (by rw [BasedLift.assoc]; simp only [gaplift_property])

/-- Cartesian based lifts are closed under composition. -/
instance instComp  {c d d' : C} {f₁ : c ⟶ d} {f₂ : d ⟶ d'} {x : P⁻¹ c} {y : P⁻¹ d} {z : P⁻¹ d'} (g₁ : x ⟶[f₁] y) [CartesianBasedLift (P:= P) g₁] (g₂ : y ⟶[f₂] z) [CartesianBasedLift (P:= P) g₂] : CartesianBasedLift (P:= P) (g₁ ≫[l] g₂) where
  uniq_lift := fun c' w u g' => {
    default := ⟨gaplift g₁ u (gaplift g₂ (u ≫ f₁) (eqRebaseAssoc.invFun g')), by rw [← BasedLift.assoc_inv, gaplift_property g₁ _ _, gaplift_property g₂ _ _]; simp⟩
    uniq := by intro ⟨l, hl⟩; simp; apply gaplift_uniq; apply gaplift_uniq; rw [BasedLift.assoc]; simp; exact hl}

/-- The cancellation lemma for cartesian based lifts. If  `g₂ : y ⟶[f₂] z` and `g₁ ≫[l] g₂ : z ⟶[f₂] z` are cartesian then `g₁` is cartesian. -/
@[simp]
lemma instCancel {g₁ : x ⟶[f₁] y} {g₂ : y ⟶[f₂] z} [CartesianBasedLift (P:= P) g₂] [CartesianBasedLift (g₁ ≫[l] g₂)] : CartesianBasedLift g₁ where
  uniq_lift := fun c' z' u₁ g₁' => {
    default := {
      val := gaplift (g:= g₁ ≫[l]  g₂) u₁ (eqRebaseAssoc (g₁' ≫[l] g₂))
      property := by apply gaplift_uniq' g₂ _ (g₁'); rw [BasedLift.assoc]; rw [ gaplift_property _ _ _]; simp
    }
    uniq := by intro l
               cases' l with l hl
               have : (l ≫[l] (g₁ ≫[l] g₂)) = eqRebaseAssoc (g₁' ≫[l] g₂) := by simp only [← BasedLift.assoc_inv]; rw [hl]; simp
               simp
               apply gaplift_uniq (g₁ ≫[l] g₂) (eqRebaseAssoc (g₁' ≫[l] g₂)) l (this)
  }

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
lemma cogaplift_comp {u : d ⟶ d'} {u' : d' ⟶ d''} {y'' : P⁻¹ d''} (g' : x ⟶[f ≫ u] y') [CoCartesianBasedLift (P:= P) g'] (g'' : x ⟶[(f ≫ u) ≫ u'] y'') : BasedLift.comp  (cogaplift (g:= g) u g') (cogaplift (g:= g') u' g'') = cogaplift (g:= g) (u ≫ u') (BasedLift.eqRebaseAssoc.toFun g'') := by refine cogaplift_uniq (f:= f) g (BasedLift.eqRebaseAssoc.toFun g'') ( BasedLift.comp  (cogaplift (g:= g) u g') (cogaplift (g:= g') u' g'')) (by rw [← BasedLift.assoc_inv]; simp only [cogaplift_property])

end CoCartesianBasedLift


@[simp]
abbrev CartesianMorphism {P : E ⥤ C} {x y : E} (g : x ⟶ y) := CartesianBasedLift (P:= P) (BasedLift.tauto g) -- note `def` did not work with instance synthesis in gapmap below and also makes the CartesianMorphism a function not a class

section CartesianMorphism
open CartesianBasedLift

variable {P : E ⥤ C} {x y : E} (g : x ⟶ y) [CartesianMorphism (P:= P) g]

def gapmap' {x' : E} (u : P.obj x' ⟶ P.obj x) (g' : (Fib.tauto x') ⟶[u ≫ P.map g] (Fib.tauto y)) : x' ⟶ x :=  (gaplift (BasedLift.tauto g) u g').hom

/-- The composition of the gap map and the cartesian lift is the given lift -/
@[simp]
lemma gapmap_property'  (x' : E) (u : P.obj x' ⟶ P.obj x) (g' : (Fib.tauto x') ⟶[u ≫ P.map g] (Fib.tauto y)) : (gapmap' g  u g' : x' ⟶ x ) ≫ g = g'.hom := gaplift_hom_property (BasedLift.tauto g) u g'

/-- The uniqueness part of the universal property of the gap map -/
@[simp]
lemma gapmap_uniq' {x' : E} (u : P.obj x' ⟶ P.obj x) (g' : (Fib.tauto x') ⟶[u ≫ P.map g] (Fib.tauto y)) (v : (Fib.tauto x') ⟶[u] (Fib.tauto x)) (hv : BasedLift.comp v (BasedLift.tauto g) = g') : v.hom = gapmap' g u g' := by congr 1; exact gaplift_uniq (BasedLift.tauto g) g' v hv

end CartesianMorphism


@[simp]
abbrev CoCartesianMorphism {P : E ⥤ C} {x y : E} (g : x ⟶ y) := CoCartesianBasedLift (P:= P) (c:= P.obj x) (d:= P.obj y) (BasedLift.tauto g) -- note `def` did not work with instance synthesis in gapmap below and also makes the CartesianMorphism a function not a class

section CoCartesianMorphism
variable {P : E ⥤ C} {x y : E} (g : x ⟶ y) [CoCartesianMorphism (P:= P) g]

def cogapmap {y' : E} (u : P.obj y ⟶ P.obj y') (g' : (Fib.tauto x) ⟶[P.map g ≫ u] (Fib.tauto y')) : y ⟶ y' :=  (cogaplift (BasedLift.tauto g) u g').hom

@[simp]
lemma cogapmap_property  (y' : E) (u : P.obj y ⟶ P.obj y') (g' : (Fib.tauto x) ⟶[P.map g ≫ u] (Fib.tauto y')) : g ≫ (cogapmap g  u g' : y ⟶ y' ) = g'.hom := cogaplift_hom_property (BasedLift.tauto g) u g'

@[simp]
lemma cogapmap_uniq {y' : E} (u : P.obj y ⟶ P.obj y') (g' : (Fib.tauto x) ⟶[P.map g ≫ u] (Fib.tauto y')) (v : (Fib.tauto y) ⟶[u] (Fib.tauto y')) (hv :  (g ≫[l] v) = g') : v.hom = cogapmap g u g' := by congr 1; exact cogaplift_uniq (BasedLift.tauto g) g' v hv

end CoCartesianMorphism

-- def isCartesianMorphism {P : E ⥤ C} {x y : E} (g : x ⟶ y) : Prop := ∀ ⦃c: C⦄ ⦃z: P⁻¹ c⦄ (u : c ⟶ P.obj x) (g' : z ⟶[u ≫ P.map g] Fib.tauto y), ∃! (l : z ⟶[u] x), l.hom ≫ g = g'.hom
/-- A morphism is cartesian if there is a uniqe gap map. -/
def isCartesianMorphism {P : E ⥤ C} {x y : E} (g : x ⟶ y) : Prop := ∀ ⦃z: E⦄ (u : P.obj z ⟶ P.obj x) (g' :  Fib.tauto z ⟶[u ≫ P.map g] y), ∃! (l : Fib.tauto z ⟶[u] x), (l.hom ≫ g) = g'.hom

/-- The class of cartesian morphisms -/
@[simp]
def CartMor (P : E ⥤ C) : MorphismProperty E :=  fun _ _ g => isCartesianMorphism (P:= P) g --Nonempty (CartesianMorphism (P:= P) g)


namespace CartMor
open MorphismProperty CartesianBasedLift BasedLift

variable {P : E ⥤ C} {x y : E}

noncomputable
def gapmap (g : x ⟶ y) (gcart : CartMor P g) {z : E} (u : P.obj z ⟶ P.obj x) (g' : Fib.tauto z ⟶[u ≫ P.map g] y) : (z : E) ⟶ x :=  (Classical.choose (gcart u g')).hom

@[simp]
lemma gapmap_over {z : E} {u : P.obj z ⟶ P.obj x} {g' : Fib.tauto z ⟶[u ≫ P.map g] Fib.tauto y} : P.map (gapmap g gcart u g') = u := by simp [gapmap]

/-- The composition of the gap map of a map g' and the cartesian lift g is the given map g'. -/
@[simp]
lemma gapmap_property {g : x ⟶ y} {gcart : CartMor P g} {z : E} {u : P.obj z ⟶ P.obj x} {g' : Fib.tauto z ⟶[u ≫ P.map g] y} : (gapmap g gcart u g') ≫ g = g'.hom := by apply (Classical.choose_spec (gcart u g')).1

@[simp]
lemma gapmap_uniq {z : E} {u : P.obj z ⟶ P.obj x} {g' : Fib.tauto z ⟶[u ≫ P.map g] Fib.tauto y}  (v : Fib.tauto z ⟶[u] x) (hv : v.hom ≫ g = g'.hom) : v.hom = gapmap g gcart u g' := by
simp [gapmap]
have : v = Classical.choose (gcart u g') := by refine (Classical.choose_spec (gcart u g')).2 v hv
rw [this]

@[simp]
lemma gapmap_uniq' (g : x ⟶ y) (gcart : CartMor P g) {c : C} {z : P⁻¹ c} (v₁ : (z : E) ⟶ x) (v₂ : (z : E) ⟶ x) (hv : v₁ ≫ g = v₂ ≫ g) (hv' : P.map v₁ = P.map v₂) : v₁ = v₂ := by
let v₁' := tauto (P:= P) v₁
let v₂' := tauto (P:= P) v₂
let g' := v₂' ≫[l] tauto g
have : P.map v₁ ≫ P.map g = P.map v₂ ≫ P.map g  := by rw [← P.map_comp, ← P.map_comp, hv]
have hv₁ : v₁'.hom ≫ g = g'.hom := by simp [Fib.tauto_over v₁, hv]
have hv₂ : v₂'.hom ≫ g = g'.hom := by simp
have hv₂' : (eqRebase hv'.symm v₂').hom ≫ g = (eqRebase (this.symm) g').hom := by simp [hv₂]
have H' := (gcart (P.map v₁) (eqRebase (this.symm) g')).unique hv₁ hv₂'
injection H'


/-- Axiom of choice gives for a mere (unique) existence of gap map the data of a unique gap map, and as such a structure of a cartesian morphism. -/
noncomputable
instance instCartOfisCart {P : E ⥤ C} {x y : E} (g : x ⟶ y) (gcart: CartMor P g) : CartesianMorphism (P:= P) g :=
{
  uniq_lift := fun c' x' u g' =>
  let u₁ := eqToHom x'.over ≫ u;
  let g₁ := BasedLift.eqRebaseAssoc.invFun (BasedLift.eqRebaseToHom g');
  {
    default := {
      val := ⟨(Classical.choose (gcart u₁ g₁)).hom, by simp only [BasedLift.over_base, eqToHom_refl, comp_id, id_comp]⟩
      property := by ext; simp; exact (Classical.choose_spec (gcart u₁ g₁)).1
    }
    uniq := by intro l
               ext
               have H : l.1.hom ≫ g = g'.hom := by simp [l.2]; aesop
               let H' := gapmap_uniq' g gcart (l.1.hom) (gapmap g gcart u₁ g₁) (by rw [H, gapmap_property]; simp) (by simp)
               rw [H']; rfl
  }
}

@[simp]
lemma cart_id (e : E) : CartMor P (𝟙 e) := fun z u g' ↦ by
use ⟨ (BasedLift.eqRebase ((whisker_eq u (P.map_id e)).trans (comp_id _))).toFun g', by aesop⟩
simp; intro v hv; ext; aesop

-- ⟨{
--   uniq_lift := fun c z u g' ↦ {
--     default := ⟨ (BasedLift.overRebase ((whisker_eq u (P.map_id e)).trans (comp_id _))).toFun g', by aesop⟩
--     uniq := by simp; intro v hv; ext; aesop
--   }
-- }⟩

/-- Cartesian morphisms are closed under composition. -/
lemma cart_comp : StableUnderComposition (CartMor P) := fun x y z f g hf hg w u g' => by
cases' (hg (u ≫ P.map f) ((BasedLift.eqRebase ((u ≫= P.map_comp f g).trans (Category.assoc u _ _).symm )).toFun g')) with lg hlg
cases' (hf u lg) with lf hlf
use lf
constructor
· simp only [Fib.tauto_over, CartMor, ← Category.assoc, hlf.1, hlg.1, eqRebase]
· intro v hv
  have : v.hom ≫ f = lg.hom := (BasedLift.comp_hom_over).mp (hlg.2 (v ≫[l] f) (hv ▸ assoc v.hom f g))
  apply hlf.2 v this

/-- Every isomorphism is cartesian. -/
lemma cart_iso {x y : E} (g : x ⟶ y) [IsIso g] : CartMor P g := fun z u g' => by
use (BasedLift.eqRebase (by simp)).toFun (g' ≫[l] BasedLift.tauto (inv g))
simp
intro v hv
congr! 1
aesop

/-- The property CartMor respect isomorphisms -/
lemma cart_iso_closed : RespectsIso (CartMor P) where
  left := fun e g hg => by apply cart_comp; exact cart_iso e.hom; assumption
  right := fun e g hg => by apply cart_comp; assumption; exact cart_iso e.hom

open IsPullback
/--Cartesian morphisms are closed under base change: Given a pullback square
```
  P---g'-->X
  |        |
 f'        f
  |        |
  v        v
  Y---g--->Z
```
if g is cartesian, then so is g'.-/
lemma cart_pullback [PreservesLimitsOfShape WalkingCospan P] : StableUnderBaseChange (CartMor P) := fun x y w z f g f' g' pb gcart  => by
intro w' u k
have pbw : P.map g' ≫ P.map f = P.map f' ≫ P.map g := by rw [← P.map_comp, ← P.map_comp, pb.w]
have pbw' : P.map k.hom ≫ P.map f  = (u ≫ P.map f') ≫ P.map g := by rw [Category.assoc]; rw [u ≫= pbw.symm]; simp only [Fib.tauto_over, over_base, eqToHom_refl, comp_id, id_comp, Category.assoc]
have hk : P.map k.hom = u ≫ P.map g' := by simp only [Fib.tauto_over, over_base, eqToHom_refl, comp_id, id_comp, Category.assoc]
let v' :  w' ⟶ y := gapmap g gcart (u ≫ P.map f') (eqRebase pbw' (eqRebase (hk.symm) k ≫[l] tauto f))
have : k.hom ≫ f = v' ≫ g := by simp [v', gapmap_property]
let pbc₁ : PullbackCone f g := PullbackCone.mk k.hom v' this
let pb₁ := pb |> IsPullback.flip |> isLimit
let pb₂ := isLimitPullbackConeMapOfIsLimit P (f:= f) (g:= g) pb.w.symm (pb |> IsPullback.flip |> isLimit)
let v : w' ⟶ w := pb₁.lift pbc₁
have hv₁ : P.map v ≫ P.map g' = P.map k.hom := by rw [← P.map_comp]; congr 1; exact pb₁.fac pbc₁ WalkingCospan.left
have hu₁ : u ≫ P.map g' = P.map k.hom := by simp only [Fib.tauto_over, over_base, eqToHom_refl, comp_id, id_comp]
have hv₂' : v ≫ f' = v' := pb₁.fac pbc₁ WalkingCospan.right
have hv₂ : P.map v ≫ P.map f' = u ≫ P.map f' := by rw [← P.map_comp, hv₂']; simp only [gapmap_over]
have hv₃ : P.map v = u := by apply PullbackCone.IsLimit.hom_ext pb₂; simp only [PullbackCone.mk_π_app_left]; rw [hv₁, ← hu₁]; simp only [PullbackCone.mk_π_app_right]; rw [hv₂]
use ⟨v, by rw [hv₃]; simp⟩
--dsimp
constructor
· apply pb₁.fac pbc₁ WalkingCospan.left
. intro l hl
  have : (l ≫[l] tauto f').hom ≫ g = (k ≫[l] tauto f).hom := by simp [comp_hom]; rw [pb.w, ← Category.assoc, hl, ← comp_tauto_hom]
  have : l.hom ≫ f' = v' := by rw [← comp_tauto_hom]; apply gapmap_uniq (l ≫[l] tauto f') this
  have : l.hom = v := by apply PullbackCone.IsLimit.hom_ext pb₁;
                         · simp [cone_fst]; rw [hl]; symm; exact pb₁.fac pbc₁ WalkingCospan.left
                         · simp [cone_snd]; rw [this]; symm; exact pb₁.fac pbc₁ WalkingCospan.right
  ext; assumption



namespace Vertical
open BasedLift CartesianBasedLift FibCat

/- Vertical cartesian lifts are isomorphism. -/
@[simps]
def vertCartIso {P : E ⥤ C} {c: C} {e e' : P⁻¹ c} (g : e ⟶ e') [CartesianBasedLift (P:= P) (ofFibHom g)] : e ≅ e' where
  hom := g
  inv := gaplift (ofFibHom g) (𝟙 c) (id e' ≫[l] id e')
  --apply gaplift_property;
  --apply gaplift_uniq' (ofFibHom g) (ofFibHom g);
  inv_hom_id := by rw [← comp_id (𝟙 e')]; apply FibCat.hom_ext; apply gaplift_hom_property
  hom_inv_id := by rw [← comp_id (𝟙 e)]
                   let g' : e' ⟶[𝟙 c] e := ofFibHom (gaplift (ofFibHom g) (𝟙 c) (id e' ≫[l] id e'))
                   have : ((ofFibHom g ≫[l] g') ≫[l] ofFibHom g) = (BasedLift.id e ≫[l] BasedLift.id e) ≫[l](ofFibHom g) := by
                                          simp [BasedLift.assoc]
                                          have H : ( (gaplift (ofFibHom g) (𝟙 c) (id e' ≫[l] id e')) ≫[l] ofFibHom g) = (BasedLift.id e' ≫[l] BasedLift.id e') := by apply gaplift_property
                                          have H' := comp_hom_over.mp H
                                          simp at H'
                                          rw [H']; simp
                   have H := gaplift_uniq' (ofFibHom g) ((ofFibHom g) ≫[l] g') (BasedLift.id e ≫[l] BasedLift.id e) (this)
                   apply FibCat.hom_ext
                   dsimp
                   have H' := comp_hom_over.mp H
                   simp at H'; simp [H']

/-There is an IsoBasedLift between two cartesian morphims over the same base morphism. -/

-- def isoOfGapLift {f : c ⟶ d} {x x' : P⁻¹ c} {y : P⁻¹ d} {g₁ : x ⟶[f] y } {g₂ : x' ⟶[f] y} [CartesianBasedLift (P:= P) g₁] [CartesianBasedLift (P:= P) g₂] : x' ⟶[≅(𝟙 c)] x where
--   hom := gaplift g₁ (𝟙 c) (BasedLift.id x' ≫[l] BasedLift.id x)
--   over := _
--   is_iso_hom := _


-- g₁ ≅ g₂ where
--   hom := gapmap g₁ (CartMor P g₁) u g'
--   inv := gapmap g₂ (CartMor P g₂) u g'
--   hom_inv_id := by rw [← comp_id g₁]; apply gapmap_uniq (CartMor P g₁) g' (gapmap g₁ (CartMor P g₁) u g') (gapmap_property g₁ (CartMor P g₁) u g')
--   inv_hom_id := by rw [← comp_id g₂]; apply gapmap_uniq (CartMor P g₂) g' (gapmap g₂ (CartMor P g₂) u g') (gapmap_property g₂ (CartMor P g₂) u g')


end Vertical
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
               --simp
               have : g ≫ l.1.hom = g'.hom := by simp [l.2]; aesop
               congr 1
               refine (Classical.choose_spec (hcocart u g')).2 l.1 this
  }
}⟩

@[simp]
def CoCartMor (P : E ⥤ C): MorphismProperty E :=  fun _ _ f => isCoCartesianMorphism (P:= P) f

section CoCartMor
variable {P : E ⥤ C}

/-- The identity morphism is cocartesian. -/
@[simp]
lemma cocart_id (e : E) : CoCartMor P (𝟙 e) := fun c z u g' ↦ by
use ⟨ (BasedLift.eqRebase ((eq_whisker (P.map_id e) u).trans (id_comp _))).toFun g', by aesop⟩
simp; intro v hv; ext; aesop

/-- Cocartesian morphisms are closed under composition. -/
@[simp]
lemma cocart_comp (f : x ⟶ y) (g : y ⟶ z) : CoCartMor (P:= P) f → CoCartMor (P:= P) g → CoCartMor (P:= P) (f ≫ g) := fun hf hg c w u g' ↦ by
cases' (hf (P.map g ≫ u) ((BasedLift.eqRebase ((P.map_comp f g =≫ u ).trans (assoc _ _ u) )).toFun g')) with lf hlf
cases' (hg u lf) with lg hlg
use lg
constructor
· simp [← assoc, hlf.1, hlg.1]
· intro v hv
  let hv' := (BasedLift.comp_hom (BasedLift.tauto g) v).symm ▸ (hv ▸ (assoc f g v.hom).symm)
  let hlf2 := (hlf.2 (g ≫[l] v)) hv'
  have : g ≫ v.hom = lf.hom := (BasedLift.comp_hom_over).mp hlf2
  apply hlg.2 v this

end CoCartMor


section CartLift
variable {P : E ⥤ C} {c d : C}

/-- The type of all cartesian lifts of a given morphism in the base -/
class CartBasedLifts (P : E ⥤ C) {c d : C} (f : c ⟶ d) (src : P⁻¹ c) (tgt : P⁻¹ d) extends BasedLift P f src tgt where
is_cart : CartesianBasedLift (P:= P) toBasedLift

instance instHomOfCartBasedLift {c d : C} (f : c ⟶ d) (src : P⁻¹ c) (tgt : P⁻¹ d) : CoeOut (CartBasedLifts P f src tgt) (src.1 ⟶ tgt.1) where
  coe := fun l ↦ l.1.hom

class CartesianLift (f : c ⟶ d) (y : P⁻¹ d) extends Lift P f y where
is_cart : CartesianBasedLift (P:= P) lift

class CoCartesianLift (f : c ⟶ d) (x : P⁻¹ c) extends CoLift P f x where
is_cart : CoCartesianBasedLift (P:= P) colift

def HasCartesianLift (f : c ⟶ d) (y : P⁻¹ d) := Nonempty (CartesianLift (P:= P) f y)

def HasCoCartesianLift (f : c ⟶ d) (x : P⁻¹ c) := Nonempty (CoCartesianLift (P:= P) f x)

end CartLift


abbrev Cart ( _ : E ⥤ C) := E
open CartMor
/-- The subcategory of cartesian arrows -/
instance {P : E ⥤ C} : Category (Cart P) where
  Hom x y := { f : x ⟶ y |  CartMor (P:= P) f }
  id x := ⟨𝟙 x, cart_id x⟩
  comp := @fun x y z f g => ⟨ f.1 ≫ g.1, cart_comp f.1 g.1 f.2 g.2⟩

namespace Cart

/-- The forgetful functor from the category of cartesian morphisms to the total category -/
def forget {P : E ⥤ C} : Cart P ⥤ E where
obj := fun x => x
map := @fun x y f => f

end Cart
