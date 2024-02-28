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


universe u

namespace CategoryTheory
open Category Opposite BasedLift CartesianBasedLift Fib

variable {C E : Type*} [Category C] [Category E]


/-- A Cloven fibration provides for every morphism `c ⟶ P x` in the base a cartesian lift in the total category. -/
class ClovenFibration (P : E ⥤ C) where
lift {c d : C} (f : c ⟶ d) (y : P⁻¹ d) : CartesianLift (P:= P) f y

/-- An CoCloven fibration provides for every morphism `P x ⟶ c` in the base a cartesian lift in the total category. -/
class CoClovenFibration (P : E ⥤ C) where
colift {c d : C} (f : c ⟶ d) (x : P⁻¹ c) : CoCartesianLift (P:= P) f x

class Fibration (P : E ⥤ C) where
lift {c d : C} (f : c ⟶ d) (y : P⁻¹ d) : HasCartesianLift (P:= P) f y

class CoFibration (P : E ⥤ C) where
colift {c d : C} (f : c ⟶ d) (x : P⁻¹ c) : HasCoCartesianLift (P:= P) f x
--isOpFibration (P.op)

class Transport (P : E ⥤ C) where
  transport {c d : C} (f : c ⟶ d) (y : P⁻¹ d) : P⁻¹ c

class CoTransport (P : E ⥤ C) where
  cotransport {c d : C} (f : c ⟶ d) (x : P⁻¹ c) : P⁻¹ d

notation f " ⋆ " y  : 10 => Transport.transport f y
notation x " ⋆ " f  : 10 => CoTransport.cotransport f x

-- local infixl:50 " ⋆ " =>  fun f y ↦ Transport.transport f y
-- local infixl:40 " ⋆ " =>  fun x f ↦ CoTransport.cotransport f x

@[simp]
lemma transport_proj {P : E ⥤ C}[Transport P] (f : c ⟶ d) (y : P⁻¹ d) : P.obj (f ⋆ y) = c := by simp

@[simp]
lemma cotransport_proj {P : E ⥤ C}[CoTransport P] (f : c ⟶ d) (x : P⁻¹ c) : P.obj (x ⋆ f) = d := by simp

namespace ClovenFibration
variable {P : E ⥤ C} [ClovenFibration P]

@[simp]
instance instTransport : Transport P where
  transport := fun f x ↦ ⟨(lift f x).src , by simp only [Fib.over]⟩

@[simp]
def Transport (f : c ⟶ d) : (P⁻¹ d) → (P⁻¹ c) := fun y ↦ f ⋆ y

@[simp]
def BasedLiftOf (f : c ⟶ d) (y : P⁻¹ d) : (f ⋆ y) ⟶[f] y := (lift f y).lift

@[simp]
instance instCartesianBasedLift {f : c ⟶ d} {y : P⁻¹ d} : CartesianBasedLift (BasedLiftOf f y) := (lift f y).is_cart

@[simp]
def Hom (f : c ⟶ d) (y : P⁻¹ d) : (f ⋆ y : E) ⟶ (y : E) := (lift f y).lift.hom

@[simp]
lemma TransportHom_proj (f : c ⟶ d) (y : P⁻¹ d) : P.map (Hom (P:= P) f y) = (eqToHom (transport_proj (P:= P) f y)) ≫ f ≫ eqToHom ((Fib.over y).symm)   := by simp only [CoTransport, Fib.mk_coe, Hom, BasedLift.over_base]

@[simp]
instance CartesianLiftOf (f : c ⟶ d) (y : P⁻¹ d) : CartesianLift f y := (lift f y)

@[simp]
lemma transport_comp {c d₁ d₂ : C} {f₁ : c ⟶ d₁} {f₂ : d₁ ⟶ d₂} {y : P⁻¹ d₂} : ((f₁ ≫ f₂) ⋆ y) ≅ f₁ ⋆ (f₂ ⋆ y) where
  hom := gaplift (BasedLiftOf f₁ (f₂ ⋆ y)) (𝟙 c) (eqRebaseIdComp.invFun  (gaplift (BasedLiftOf f₂ y) f₁ (BasedLiftOf (f₁ ≫ f₂) y)))
  inv := gaplift (BasedLiftOf (f₁ ≫ f₂) y) (𝟙 c) (eqRebaseIdComp.invFun ((BasedLiftOf f₁ (f₂ ⋆ y)) ≫[l] (BasedLiftOf f₂ y)))
  hom_inv_id := by simp; rw [← comp_hom _ _, ← id_hom]; congr; simp; aesop--apply gaplift_uniq' (BasedLiftOf f₁ (f₂ ⋆ y)) _
  inv_hom_id := sorry


#exit


end ClovenFibration


namespace CoCloven

section
variable {P : E ⥤ C} [CoCloven P]

@[simp]
instance instCoTransport : CoTransport P where
  cotransport := fun f x ↦ ⟨ (colift f x).tgt , by aesop⟩

@[simp]
def CoTransport (f : c ⟶ d) : (P⁻¹ c) → (P⁻¹ d) := fun x ↦ x ⋆ f

@[simp]
def BasedLiftOf (f : c ⟶ d) (x : P⁻¹ c) : x ⟶[f] (x ⋆ f) :=
(colift f x).colift

@[simp]
instance {f : c ⟶ d} {x : P⁻¹ c} : isCoCartesianBasedLift f (BasedLift f x) := (colift f x).is_cart

@[simp]
def Hom (f : c ⟶ d) (x : P⁻¹ c) : (x : E) ⟶ (CoTransport f x : E) :=
(colift f x).lift.hom

@[simp]
lemma Hom_proj (f : c ⟶ d) (x : P⁻¹ c) : P.map (Hom f x) = eqToHom (by simp) ≫ f ≫ (eqToHom (cotransport_proj (P:= P) f x).symm) := by simp only [CoTransport, Fib.mk_coe, Hom, BasedLift.proj]

def map (f : c ⟶ d) : (P⁻¹ c) ⥤ (P⁻¹ d) where
  obj := CoTransport (P:= P) f
  map :=  @fun x y g ↦ by let g₁ : x ⟶[𝟙 c] y := ⟨g.1, by simp [g.2]⟩
                          let g₂ : y ⟶[f] CoTransport (P:= P) f y := (colift f y).lift
                          let g₃ : x ⟶[(𝟙 c) ≫ f] CoTransport (P:= P) f y := BasedLift.Comp g₁ g₂
                          let g₄ : x ⟶[f ≫ (𝟙 d)] CoTransport (P:= P) f y := BasedLift.EquivCompId.toFun (BasedLift.EquivIdComp.invFun g₃)
                          refine {
                            val := CoGapMap (g:= BasedLift f x) (𝟙 d) g₄   --((colift f x).is_cart.uniq_colift (𝟙 d) (g₄)).default.1.hom
                            property := by simp only [Transport, Fib.mk_coe, BasedLift.Comp, Equiv.toFun_as_coe, BasedLift.EquivCompId, BasedLift.Id,
                            comp_id, BasedLift.EquivIdComp, id_comp, Set.mem_setOf_eq, Equiv.invFun_as_coe, Equiv.coe_fn_symm_mk,
                            BasedLift.proj, Fib.proj, eqToHom_naturality, eqToHom_trans] -- aesop? generated proof
                          }
  map_id := by intro x; simp; symm; refine CoGapMap_uniq (BasedLift f x) (BasedLift.Comp (BasedLift f x) (BasedLift.Id x)  ) (BasedLift.Id (CoTransport (P:= P) f x)) ?_ -- apply Classical.choose_spec-- uniqueness of UP of lift
  --apply ((colift f x).is_cart.uniq_colift (𝟙 d) _).uniq ⟨(BasedLift.Id (CoTransport (P:= P) f x)), sorry⟩  -- apply Classical.choose_spec-- uniqueness of UP of lift
  map_comp := sorry -- uniquess of UP of lift

end

#check CoGapMap_uniq

end CoCloven





variable (F : C ⥤ Cat) (c : C)

@[simp]
lemma Grothendieck.fib_obj_base (x : (Grothendieck.forget F)⁻¹ c ): x.fiber.base = c := x.eq

@[simps]
def FibCatGrothendieckIso (c : C) : ((Grothendieck.forget F)⁻¹ c) ≅ F.obj c where
  hom := fun x =>  by erw [← Grothendieck.fib_obj_base F c x]; exact x.fiber.fiber -- was very useful to have tactic-term mix mode a
  inv := fun x => ⟨ ⟨c, x⟩ , rfl ⟩
  hom_inv_id := by ext x; simp; cases' x with p e; simp; cases' p with b q; simp; rw [← e]; simp
  inv_hom_id := by rfl

/-- The projection functor of a Grothendieck construction is a cloven Grothendieck Fibration. -/
instance ClovenOfGrothendieckConstruction : ClovenFibration (Grothendieck.forget F) where
  lift := fun c d f x ↦ {
    tgt :=  x |> (FibGrothendieckIso F c).hom |> (F.map f).obj |> (FibGrothendieckIso F d).inv
    hom := sorry
    eq := sorry
    cart := sorry
  }

end Cloven


variable {P : E ⥤ C} [isOpFibration P]

-- def toTransport (f : c ⟶ d) (x : Fib P c) : (x : E) ⟶ (Transport f x : E) :=

@[simp] noncomputable
def Transport (f : c ⟶ d) : (P⁻¹ c) → (P⁻¹ d) := fun x ↦ ⟨ (Classical.choice (isOpFibration.lift f x)).tgt , by aesop⟩

@[simp]
lemma proj_transport (f : c ⟶ d) (x : P⁻¹ c) : P.obj (Transport f x) = d := by simp

@[simp] noncomputable
def TransportHom (f : c ⟶ d) (x : P⁻¹ c) : (x : E) ⟶ (Transport f x : E) :=
(Classical.choice (isOpFibration.lift f x)).lift.hom

@[simp]
lemma isCartesianTransportHom (f : c ⟶ d) (x : P⁻¹ c) : isCartesianMorphism (P:= P) (TransportHom f x) :=
(Classical.choice (isOpFibration.lift f x)).cart

-- noncomputable
-- def map (f : c ⟶ d) : (P⁻¹ c) ⥤ (P⁻¹ d) where
--   obj := Transport f
--   map :=  @fun x y g ↦ {
--     val := (Classical.choice (Classical.choice (isCovFibration.lift f x)).cart).lift (g.1 ≫ (Classical.choice (HasCartesianLifts.lift c y f)).hom) (eqToHom (by simp) ≫ (𝟙 d) ≫ (eqToIso (by simp)).inv) (by aesop)
--     property := by simp; apply (Classical.choice (Classical.choice (isCovFibration.lift f x)).cart).lift_eq_proj;
--   } -- I'm not satisfied with this: it's ugly and too mnay `Classical.choice` why couldn't inferInstance the construction? way cleaner that way.
--   map_id := sorry -- uniqueness of UP of lift
--   map_comp := sorry -- uniquess of UP of lift



--variable {F : Type*} [Category F] {Q : F ⥤ C} [isCovFibration Q]


-- structure CartesianFunctor (E) (F)  : Prop where
-- over : U ⋙ Q = P -- equality of functors usually makes rewrite problems down the way
-- -- over (c : C) : Fib P c ⥤ Fib Q c
-- cart : ∀ ⦃ x y : E ⦄ (f : x ⟶ y ), (isCartesianMorphism P f) → isCartesianMorphism Q (U.map f)

-- @[simp]
-- lemma cartesian_functor_over_obj (U: CartesianFunctor (P:= P) (Q:= Q)  (U:= U)) : ∀ x : E, Q.obj (U.obj x) = P.obj x := by
-- intro x
-- change (U ⋙ Q).obj x = P.obj x
-- rw [CartesianFunctor.over (P:= P) (Q:= Q) (U:= U)]

-- lemma cartesian_functor_over_hom (U : E ⥤ F) [CartesianFunctor (P:= P) (Q:= Q) U] : ∀ (f: x ⟶ y), Q.map (U.map f) = (eqToHom (cartesian_functor_over_obj U x))  ≫ P.map f ≫ (eqToIso (cartesian_functor_over_obj U y)).inv := by
-- intro f
-- change (U ⋙ Q).map f = eqToHom (_ : Q.obj (U.obj x) = P.obj x) ≫ P.map f ≫ (eqToIso (_ : Q.obj (U.obj y) = P.obj y)).inv
-- rw [CartesianFunctor.over (P:= P) (Q:= Q) (U:= U)] -- we got stuck again due to bad rewriting along function equality


/-- Homomorphism of Grothendieck fibrations. -/
structure CartesianHom {E F : Type*} [Category E] [Category F] (P : E ⥤ C) (Q : F ⥤ C) [Fibration P] [Fibration Q]  where
obj (c : C) : (P⁻¹ c) → (Q⁻¹ c)
map {c d : C} (f : c ⟶ d) {x : (P⁻¹ c)} {y : (P⁻¹ d)} (g : CartBasedLift P f x y) : CartBasedLift Q f (obj c x) (obj d y)
-- G : E  ⥤ F
-- over : G ⋙ Q = P


-- #check PseudoFunctor

/- A homomorphism of Grothendieck fibrations induces a pseuod-functor on the fibers. -/
-- def CartesianHom.toPsFunctor {E F : Type*} [Category E] [Category F] (P : E ⥤ C) (Q : F ⥤ C) [isCovFibration P] [isCovFibration Q] (φ : CartesianHom P Q) (c: C) :  Pseudo

namespace CartesianHom

/-- A -/
def Comp {E F G : Type*} [Category E] [Category F] [Category G] {P : E ⥤ C} {Q : F ⥤ C} {R : G ⥤ C} [isCovFibration P] [isCovFibration Q] [isCovFibration R] (φ : CartesianHom P Q) (ψ : CartesianHom Q R) : CartesianHom P R where
  obj := sorry
  map := sorry


end CartesianHom
