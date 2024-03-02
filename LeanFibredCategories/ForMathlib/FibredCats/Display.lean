/-
Copyright (c) 2024 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sina Hazratpour
-/

import LeanFibredCategories.ForMathlib.FibredCats.Basic
--import LeanFibredCategories.ForMathlib.FibredCats.CartesianLift
--import LeanFibredCategories.ForMathlib.FibredCats.VerticalLift

/-!
# Display Category Of A Functor

Given a type family `F : C → Type*` on a category `C` we then define the display category  `Display F`.

For a functor `P : E ⥤ C`, we define the structure `BasedLift f src tgt` as the type of
lifts in `E` of a given morphism `f  : c ⟶ d` in `C` which have a fixed source `src` and a
fixed target `tgt` in the fibers of `c` and `d` respectively. We call the elements of
`BasedLift f src tgt` based-lifts of `f` with source `src` and target `tgt`.

We also provide various useful constructors for based-lifts:
* `BasedLift.tauto` regards a morphism `g` of the domain category `E` as a
  tautological based-lift of its image `P.map g`.
* `BasedLift.id` and `BasedLift.comp` provide the identity and composition of
  based-lifts, respectively.
* We can cast a based-lift along an equality of the base morphisms using the equivalence `BasedLift.cast`.

We provide the following notations:
* `x ⟶[f] y` for `DisplayStruct.HomOver f x y`
* `f ≫ₗ g` for `DisplayStruct.comp_over f g`

We show that for a functor `P`, the type `BasedLift P` induces a display category structure on the fiber family `fun c => P⁻¹ c`.

-/


namespace CategoryTheory

open Category

variable {C : Type*} [Category C] (F : C → Type*)

class DisplayStruct where
  /-- The type of morphisms indexed over morphisms of `C`. -/
  HomOver : ∀ {c d : C}, (c ⟶ d) → F c → F d → Type*
  /-- The identity morphism overlying the identity morphism of `C`. -/
  id_over : ∀ {c : C} (x : F c), HomOver (𝟙 c) x x
  /-- Composition of morphisms overlying composition of morphisms of `C`. -/
  comp_over : ∀ {c₁ c₂ c₃ : C} {f₁ : c₁ ⟶ c₂} {f₂ : c₂ ⟶ c₃} {x₁ : F c₁} {x₂ : F c₂} {x₃ : F c₃}, HomOver f₁ x₁ x₂ → HomOver f₂ x₂ x₃ → HomOver (f₁ ≫ f₂) x₁ x₃

notation x " ⟶[" f "] " y => DisplayStruct.HomOver f x y
notation " 𝟙ₗ " => DisplayStruct.id_over
scoped infixr:80 "  ≫ₗ "  => DisplayStruct.comp_over

class Display extends DisplayStruct F where
id_comp_cast {c₁ c₂ : C} {f : c₁ ⟶ c₂} {x₁ : F c₁} {x₂ : F c₂}
(g : x₁ ⟶[f] x₂) : (𝟙ₗ x₁) ≫ₗ g = (id_comp f).symm ▸ g := by aesop_cat
comp_id_cast {c₁ c₂ : C} {f : c₁ ⟶ c₂} {x₁ : F c₁} {x₂ : F c₂}
(g : x₁ ⟶[f] x₂) : g ≫ₗ (𝟙ₗ x₂) = (comp_id f).symm ▸ g := by aesop_cat
assoc_cast {c₁ c₂ c₃ c₄ : C} {f₁ : c₁ ⟶ c₂} {f₂ : c₂ ⟶ c₃} {f₃ : c₃ ⟶ c₄} {x₁ : F c₁}
{x₂ : F c₂} {x₃ : F c₃} {x₄ : F c₄} (g₁ : x₁ ⟶[f₁] x₂)
(g₂ : x₂ ⟶[f₂] x₃) (g₃ : x₃ ⟶[f₃] x₄) :
(g₁ ≫ₗ g₂) ≫ₗ g₃ = (assoc f₁ f₂ f₃).symm ▸ (g₁ ≫ₗ (g₂ ≫ₗ g₃)) := by aesop_cat

attribute [simp] Display.id_comp_cast Display.comp_id_cast Display.assoc_cast
attribute [trans] Display.assoc_cast

namespace Display

def cast [DisplayStruct F] {c d : C} {f f' : c ⟶ d} {x : F c} {y : F d} (w : f = f')
(g : x ⟶[f] y) : x ⟶[f'] y
 := w ▸ g

@[simp]
lemma cast_cast [DisplayStruct F] {c d : C} {f f' : c ⟶ d} {x : F c} {y : F d} (w : f = f')
(w' : f' = f) (g : x ⟶[f'] y) : w' ▸ (w ▸ g) = g := by
  subst w'; rfl

@[simps!]
def castEquiv [DisplayStruct F] {c d : C} {f f' : c ⟶ d} {x : F c} {y : F d} (w : f = f') : (x ⟶[f] y) ≃ (x ⟶[f'] y) where
  toFun := fun g ↦ w ▸ g
  invFun := fun g ↦ w.symm ▸ g
  left_inv := by aesop_cat
  right_inv := by aesop_cat

variable {F} [Display F]

/-- A hom-over of an isomorphism is invertible if -/
class IsIso {c d : C} {f : c ⟶ d} [IsIso f] {x : F c} {y : F d} (g : x ⟶[f] y) : Prop where
  /-- The existence of an inverse hom-over. -/
  out : ∃ inv : y ⟶[inv f] x, (IsIso.hom_inv_id f) ▸ (g ≫ₗ inv) = 𝟙ₗ x ∧ (IsIso.inv_hom_id f) ▸ (inv ≫ₗ g) = 𝟙ₗ y

end Display

/-- The IsoDisplay structure associated to a family `F` of types over a category `C`: A display category is iso-display if every hom-over an isomorphism is itself a display isomorphism.  -/
class IsoDisplay extends Display F where
  iso_HomOver : ∀ {c d : C} {f : c ⟶ d} [IsIso f] {x : F c} {y : F d} (g : x ⟶[f] y), Display.IsIso g

variable  {E : Type*} [Category E] {P : E ⥤ C}

/-- The type of lifts of a given morphism in the base
with fixed source and target in the fibers of the domain and codomain respectively.-/
structure BasedLift {c d : C} (f : c ⟶ d) (src : P⁻¹ c) (tgt : P⁻¹ d) where
hom : (src : E) ⟶ (tgt : E)
over : (P.map hom) ≫ eqToHom (tgt.over) = eqToHom (src.2) ≫ f

namespace BasedLift

variable {E : Type*} [Category E] {P : E ⥤ C}

@[simp]
lemma over_base {c d : C} {f : c ⟶ d} {x : P⁻¹ c} {y : P⁻¹ d} (g : BasedLift f x y) : P.map g.hom = eqToHom (x.2) ≫ f ≫ (eqToHom (y.over).symm)  := by
  simp only [← Category.assoc _ _ _, ← g.over, assoc, eqToHom_trans, eqToHom_refl, comp_id]

/-- The identity based-lift. -/
@[simps!]
def id (x : P⁻¹ c) : BasedLift (𝟙 c) x x := ⟨𝟙 _, by simp⟩

/-- The composition of based-lifts -/
@[simps]
def comp {c₁ c₂ c₃: C} {f₁ : c₁ ⟶ c₂} {f₂ : c₂ ⟶ c₃} {x : P⁻¹ c₁} {y : P⁻¹ c₂} {z : P⁻¹ c₃} (g₁ : BasedLift f₁ x y) (g₂ : BasedLift f₂ y z) : BasedLift (f₁ ≫ f₂) x z :=
⟨g₁.hom ≫ g₂.hom, by simp only [P.map_comp]; rw [assoc, over_base g₁, over_base g₂]; simp⟩

@[simps!]
def cast {c d : C} {f f' : c ⟶ d} {x : P⁻¹ c} {y : P⁻¹ d} (w : f = f')
(g : BasedLift f x y) : BasedLift f' x y
 := ⟨g.hom, by rw [←w, g.over]⟩

end BasedLift

variable (P)

set_option trace.Meta.synthInstance true in
/-- The display structure `DisplayStruct P` associated to a functor `P : E ⥤ C`. This instance makes the display notations `_ ⟶[f] _`, `_ ≫ₗ _` and `𝟙ₗ` available for based-lifts.   -/
instance instDisplayStructOfFunctor : DisplayStruct (fun c => P⁻¹ c) where
  HomOver := fun f x y => BasedLift f x y
  id_over x := BasedLift.id x
  comp_over := fun g₁ g₂ => BasedLift.comp g₁ g₂

namespace BasedLift

variable {P}

section
variable {c d : C} {f : c ⟶ d} {x : P⁻¹ c} {y : P⁻¹ d} (g g' : x ⟶[f] y)
#check g
#reduce g
#check (g : BasedLift f x y)
end

@[ext]
theorem ext {c d : C} {f : c ⟶ d} {x : P⁻¹ c} {y : P⁻¹ d} (g g' : x ⟶[f] y)
(w : g.hom = g'.hom)  : g = g' := by
  cases' g with g hg
  cases' g' with g' hg'
  congr

@[simp]
lemma cast_rec {c d : C} {f f' : c ⟶ d} {x : P⁻¹ c} {y : P⁻¹ d} {w : f = f'} (g : x ⟶[f] y) : g.cast w  = w ▸ g := by
  subst w; rfl

@[simps!]
def castEquiv {c d : C} {f f' : c ⟶ d} {x : P⁻¹ c} {y : P⁻¹ d} (w : f = f') : (x ⟶[f] y) ≃ (x ⟶[f'] y) := Display.castEquiv (fun c => P⁻¹ c) w

-- where
--   toFun := fun g ↦ g.cast w
--   invFun := fun g ↦ g.cast w.symm
--   left_inv := by aesop_cat
--   right_inv := by aesop_cat

/-- `BasedLift.tauto` regards a morphism `g` of the domain category `E` as a
based-lift of its image `P g` under functor `P`. -/
@[simps!]
def tauto {e e' : E} (g : e ⟶ e') : (Fiber.tauto e) ⟶[P.map g] (Fiber.tauto e') := ⟨g, by simp only [Fiber.tauto, eqToHom_refl, id_comp, comp_id]⟩

lemma tauto_over_base (f : (P.obj x) ⟶ (P.obj y)) (e : (Fiber.tauto x) ⟶[f] (Fiber.tauto y)) : P.map e.hom = f := by
  simp only [Fiber.coe_mk, over_base, eqToHom_refl, comp_id, id_comp]

lemma tauto_comp_hom {e e' e'' : E} {g : e ⟶ e'} {g' : e' ⟶ e''} : (tauto (P:= P) g ≫ₗ  tauto g').hom = g ≫ g' := rfl

lemma comp_tauto_hom {x y z : E} {f : P.obj x ⟶ P.obj y} {l : Fiber.tauto x ⟶[f] (Fiber.tauto y)} {g : y ⟶ z} : (l ≫ₗ tauto g).hom = l.hom ≫ g := rfl

/-- A morphism of `E` coerced as a tautological based-lift. -/
@[simps]
instance instCoeTautoBasedLift {e e' : E} {g : e ⟶ e'} :
CoeDep (e ⟶ e') (g) (Fiber.tauto e  ⟶[P.map g] Fiber.tauto e') where
  coe := tauto g

lemma eq_id_of_hom_eq_id {c : C} {x : P⁻¹ c} {g : x ⟶[𝟙 c] x} :
(g.hom = 𝟙 x.1) ↔ (g = id x) := by
  aesop

@[simp]
lemma id_comp_cast {c d : C} {f : c ⟶ d} {x : P⁻¹ c} {y : P⁻¹ d}
{g : x ⟶[f] y} : 𝟙ₗ x  ≫ₗ g = g.cast (id_comp f).symm := by ext; simp only [cast_hom, DisplayStruct.comp_over, DisplayStruct.id_over, comp_hom, id_hom, id_comp]

@[simp]
lemma comp_id_cast {c d : C} {f : c ⟶ d} {x : P⁻¹ c} {y : P⁻¹ d} {g : x ⟶[f] y} : g ≫ₗ 𝟙ₗ y = g.cast (comp_id f).symm := by ext; simp only [cast_hom, DisplayStruct.comp_over, DisplayStruct.id_over, comp_hom, id_hom, comp_id]

@[simp]
lemma assoc {c' c d d' : C} {f₁ : c' ⟶ c} {f₂ : c ⟶ d} {f₃ : d ⟶ d'} {w : P⁻¹ c'}
{x : P⁻¹ c} {y : P⁻¹ d} {z : P⁻¹ d'} (g₁ : w ⟶[f₁] x) (g₂ : x ⟶[f₂] y) (g₃ : y ⟶[f₃] z) :  ((g₁ ≫ₗ  g₂) ≫ₗ g₃) = (g₁ ≫ₗ g₂ ≫ₗ g₃).cast (assoc f₁ f₂ f₃).symm  := by
  ext; simp only [cast_hom, DisplayStruct.comp_over, comp_hom, Category.assoc]

lemma hom_comp_cast  {c d d': C} {f₁ : c ⟶ d} {f₂ : d ⟶ d'} {f : c ⟶ d'}
{w : f = f₁ ≫ f₂} {x : P⁻¹ c} {y : P⁻¹ d} {z : P⁻¹ d'} {g₁ : x ⟶[f₁] y}
{g₂ : y ⟶[f₂] z} {g : x ⟶[f] z} :
g₁.hom ≫ g₂.hom = g.hom ↔ g₁ ≫ₗ g₂ = g.cast w  := by
  constructor
  intro; aesop
  intro h; aesop

@[simps]
def castOfeqToHom {c d : C} {f : c ⟶ d} {x : P⁻¹ c} {y : P⁻¹ d} :
(x ⟶[f] y) ≃ (x.1 ⟶[(eqToHom x.2) ≫ f] y) where
  toFun := fun g => ⟨g.hom, by simp [g.over]⟩
  invFun := fun g => ⟨g.hom, by simp [g.over]⟩
  left_inv := by aesop_cat
  right_inv := by aesop_cat

end BasedLift

/-- The display category of a functor `P : E ⥤ C`. -/
def instDisplayOfFunctor : Display (fun c => P⁻¹ c) where
  id_comp_cast := by simp  --simp_all only [BasedLift.comp, BasedLift.id, id_comp]; rfl
  comp_id_cast := by simp
  assoc_cast := by simp

variable {P}

/-- The type of iso-based-lifts of an isomorphism in the base with fixed source
and target. -/
class IsoBasedLift  {c d : C} (f : c ⟶ d) [IsIso f] (x : P⁻¹ c) (y : P⁻¹ d) extends BasedLift f x y where
  is_iso_hom : IsIso hom

notation x " ⟶[≅" f "] " y => IsoBasedLift f x y





end CategoryTheory
