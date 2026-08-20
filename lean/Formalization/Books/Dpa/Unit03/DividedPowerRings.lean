import Formalization.Books.Dpa.Unit02
import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.Algebra.Category.Ring.Colimits
import Mathlib.CategoryTheory.Limits.Creates
import Mathlib.CategoryTheory.Limits.Preserves.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.CategoryTheory.Yoneda
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Divided Power Algebra, Chapter 3: Divided power rings

This file formalizes the source section “Divided power rings”.  The
divided-power operations themselves are Mathlib's `DividedPowers`; this file
only bundles a ring, an ideal, and that existing structure into the category
used by the chapter.
-/

namespace Formalization.Books.Dpa.Unit03

open CategoryTheory CategoryTheory.Limits

universe u

noncomputable section

/-! ## Divided power rings and their homomorphisms -/

/-- A commutative ring equipped with an ideal and divided powers on it. -/
structure DividedPowerRing where
  toCommRing : CommRingCat.{u}
  ideal : Ideal (toCommRing : Type u)
  dividedPowers : DividedPowers ideal

namespace DividedPowerRing

instance : CoeSort (DividedPowerRing.{u}) (Type u) :=
  ⟨fun A => A.toCommRing⟩

/-- A homomorphism preserving the ideal and all divided-power operations. -/
structure Hom (A B : DividedPowerRing.{u}) where
  hom : (A : Type u) →+* (B : Type u)
  ideal_map : ∀ {x : A}, x ∈ A.ideal → hom x ∈ B.ideal
  dpow_comm : ∀ {n : ℕ} {x : A}, x ∈ A.ideal →
    B.dividedPowers.dpow n (hom x) = hom (A.dividedPowers.dpow n x)

@[ext]
theorem Hom.ext {A B : DividedPowerRing.{u}} {f g : Hom A B}
    (h : f.hom = g.hom) : f = g := by
  cases f
  cases g
  cases h
  rfl

instance : Category (DividedPowerRing.{u}) where
  Hom := Hom
  id A :=
    { hom := RingHom.id _
      ideal_map := by
        intro x hx
        simpa using hx
      dpow_comm := by
        intro n x hx
        simp }
  comp f g :=
    { hom := g.hom.comp f.hom
      ideal_map := by
        intro x hx
        exact g.ideal_map (f.ideal_map hx)
      dpow_comm := by
        intro n x hx
        simp only [RingHom.comp_apply]
        rw [g.dpow_comm (n := n) (x := f.hom x) (f.ideal_map hx),
          f.dpow_comm (n := n) (x := x) hx] }
  id_comp := by
    intro A B f
    apply Hom.ext
    ext x
    rfl
  comp_id := by
    intro A B f
    apply Hom.ext
    ext x
    rfl
  assoc := by
    intro A B C D f g h
    apply Hom.ext
    ext x
    rfl

end DividedPowerRing

open DividedPowerRing

/-- The underlying-ring forgetful functor. -/
def forget : DividedPowerRing.{u} ⥤ CommRingCat.{u} where
  obj A := A.toCommRing
  map f := CommRingCat.ofHom f.hom

/-- A divided-power algebra over `A` is a divided-power ring under `A`. -/
def IsDividedPowerAlgebra (A B : DividedPowerRing.{u}) : Prop :=
  Nonempty (A ⟶ B)

/-! ## Limits and Brown's representability criterion -/

/-- The source's assertion that the divided-power-ring category has all limits
and that the underlying ring limit is the ordinary ring limit. -/
theorem hasLimits_and_forget_creates_limits :
    HasLimits (DividedPowerRing.{u}) ∧ Nonempty (CreatesLimits (forget)) := by
  sorry

/-- The small-source hypothesis in the chapter's version of Brown's lemma. -/
def IsCardinallyGenerated
    (F : DividedPowerRing.{u} ⥤ Type u) (κ : Cardinal.{u}) : Prop :=
  ∀ (A : DividedPowerRing.{u}) (f : F.obj A),
    ∃ (A' : DividedPowerRing.{u}) (g : A' ⟶ A) (f' : F.obj A'),
      Cardinal.mk (A' : Type u) ≤ κ ∧ F.map g f' = f

/-- A covariant set-valued functor is representable by `B`. -/
def IsRepresentableBy (F : DividedPowerRing.{u} ⥤ Type u)
    (B : DividedPowerRing.{u}) : Prop :=
  Nonempty (F ≅ coyoneda.obj (Opposite.op B))

/-- Brown's criterion as stated for divided-power rings. -/
theorem representable_of_cardinallyGenerated_of_preservesLimits
    (F : DividedPowerRing.{u} ⥤ Type u) (κ : Cardinal.{u})
    (hsmall : IsCardinallyGenerated F κ)
    (hlim : PreservesLimits F) :
    ∃ B : DividedPowerRing.{u}, IsRepresentableBy F B := by
  sorry

/-! ## Colimits -/

/-- The category of divided-power rings has all colimits. -/
theorem hasColimits : HasColimits (DividedPowerRing.{u}) := by
  sorry

/-! ## Pushouts -/

/-- A pushout square in the category of divided-power rings, expressed by its
universal property.  This is the source's pushout diagram without choosing a
particular Mathlib pushout object. -/
structure PushoutData where
  base : DividedPowerRing.{u}
  leftObject : DividedPowerRing.{u}
  rightObject : DividedPowerRing.{u}
  pushoutObject : DividedPowerRing.{u}
  left : DividedPowerRing.Hom base leftObject
  right : DividedPowerRing.Hom base rightObject
  inl : DividedPowerRing.Hom leftObject pushoutObject
  inr : DividedPowerRing.Hom rightObject pushoutObject
  condition : inl.hom.comp left.hom = inr.hom.comp right.hom
  isPushout : ∀ (C : DividedPowerRing.{u})
    (f : DividedPowerRing.Hom leftObject C)
    (g : DividedPowerRing.Hom rightObject C),
    f.hom.comp left.hom = g.hom.comp right.hom →
      ∃! h : DividedPowerRing.Hom pushoutObject C,
        h.hom.comp inl.hom = f.hom ∧ h.hom.comp inr.hom = g.hom

/-- The underlying ring pushout, i.e. the tensor product of the two rings over
the common base, attached to a divided-power pushout square. -/
noncomputable def ringPushout (P : PushoutData) : CommRingCat.{u} :=
  pushout (CommRingCat.ofHom P.left.hom) (CommRingCat.ofHom P.right.hom)

/-- The ideal of the underlying ring pushout generated by the two input
divided-power ideals. -/
noncomputable def ringPushoutIdeal (P : PushoutData) :
    Ideal (ringPushout P : Type u) :=
  Ideal.map (pushout.inl (CommRingCat.ofHom P.left.hom)
      (CommRingCat.ofHom P.right.hom)).hom P.leftObject.ideal ⊔
    Ideal.map (pushout.inr (CommRingCat.ofHom P.left.hom)
      (CommRingCat.ofHom P.right.hom)).hom P.rightObject.ideal

/-!
The next comparison is the canonical ring map from the tensor-product
pushout to the chosen divided-power pushout.  Its existence is the ordinary
pushout universal property in `CommRingCat`.
-/
noncomputable def ringPushoutComparison (P : PushoutData) :
    ringPushout P ⟶ P.pushoutObject.toCommRing := by
  exact pushout.desc (CommRingCat.ofHom P.inl.hom) (CommRingCat.ofHom P.inr.hom)
    (by
      change CommRingCat.ofHom (P.inl.hom.comp P.left.hom) =
        CommRingCat.ofHom (P.inr.hom.comp P.right.hom)
      exact congrArg (fun q => CommRingCat.ofHom q) P.condition)

/-- The quotient of a divided-power ring by its divided-power ideal. -/
def quotientRing (A : DividedPowerRing.{u}) : CommRingCat.{u} :=
  CommRingCat.of ((A : Type u) ⧸ A.ideal)

/-! ## The three pushout consequences -/

/-- The quotient map induced by a divided-power-ring homomorphism. -/
noncomputable def quotientMap {A B : DividedPowerRing.{u}} (f : A ⟶ B) :
    quotientRing A ⟶ quotientRing B := by
  apply CommRingCat.ofHom
  apply Ideal.Quotient.lift A.ideal
    ((Ideal.Quotient.mk B.ideal).comp f.hom)
  intro x hx
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (f.ideal_map hx)

/-- The tensor product of the two quotient rings over the quotient base,
represented by the corresponding pushout in `CommRingCat`. -/
noncomputable def quotientRingPushout (P : PushoutData) : CommRingCat.{u} :=
  pushout (quotientMap P.left) (quotientMap P.right)

/-- The first assertion of the pushout remark, with tensor products expressed
by the canonical pushout objects in `CommRingCat`. -/
theorem pushout_quotient_iso (P : PushoutData) :
    Nonempty ((P.pushoutObject.toCommRing ⧸ P.pushoutObject.ideal) ≃+*
      (quotientRingPushout P : Type u)) := by
  sorry

/-- The second assertion of the pushout remark. -/
theorem pushout_ring_comparison_surjective (P : PushoutData) :
    Function.Surjective (ringPushoutComparison P).hom := by
  sorry

/-- The third assertion of the pushout remark: the image of the two input
ideals generates the ideal of the divided-power pushout. -/
theorem pushout_ideal_comparison_surjective (P : PushoutData) :
    Ideal.map (ringPushoutComparison P).hom (ringPushoutIdeal P) =
      P.pushoutObject.ideal := by
  sorry

/-! ## The explicit `ZMod 4` counterexample -/

def integerDividedPowerRing : DividedPowerRing :=
  { toCommRing := CommRingCat.of ℤ
    ideal := ⊥
    dividedPowers := dividedPowersBot ℤ }

def zmodFourIdeal : Ideal (ZMod 4) :=
  Ideal.span ({(2 : ZMod 4)} : Set (ZMod 4))

def zmodFourRing (δ : DividedPowers zmodFourIdeal) : DividedPowerRing :=
  { toCommRing := CommRingCat.of (ZMod 4)
    ideal := zmodFourIdeal
    dividedPowers := δ }

def zmodFourDpowTwoIsMap (δ : DividedPowers zmodFourIdeal) (v : ZMod 4) : Prop :=
  ∀ x : ZMod 4, x ∈ zmodFourIdeal →
    δ.dpow 2 x = if x = (2 : ZMod 4) then v else 0

def zmodFourDpowTwoData : Prop :=
  ∃ (δ δ' : DividedPowers zmodFourIdeal),
    zmodFourDpowTwoIsMap δ 2 ∧ zmodFourDpowTwoIsMap δ' 0

/-- The concrete values used in the source's two divided-power structures on
`2 ℤ/4ℤ`. -/
theorem zmodFourDpowTwoData_exists : zmodFourDpowTwoData := by
  sorry

theorem zmodFourDpowTwoIsMap_unique
    {v : ZMod 4} {δ δ' : DividedPowers zmodFourIdeal}
    (hδ : zmodFourDpowTwoIsMap δ v)
    (hδ' : zmodFourDpowTwoIsMap δ' v) :
    δ = δ' := by
  sorry

def ForgetPreservesColimits : Prop :=
  Nonempty (PreservesColimits
    (forget : DividedPowerRing.{u} ⥤ CommRingCat.{u}))

theorem forget_does_not_preserve_colimits : ¬ ForgetPreservesColimits := by
  sorry

/-- The source's explicit pushout counterexample is recorded as a property of
the two structures above: its divided-power pushout is `𝔽₂`, whereas the
underlying tensor-product pushout is not identified with it. -/
theorem forgetful_does_not_preserve_colimits_example :
    ∃ (δ δ' : DividedPowers zmodFourIdeal)
      (P : PushoutData),
      zmodFourDpowTwoIsMap δ 2 ∧
      zmodFourDpowTwoIsMap δ' 0 ∧
      P.base = integerDividedPowerRing ∧
      P.leftObject = zmodFourRing δ ∧
      P.rightObject = zmodFourRing δ' ∧
      Nonempty (P.pushoutObject.toCommRing ≅ CommRingCat.of (ZMod 2)) ∧
      P.pushoutObject.ideal = ⊥ ∧
      ¬ Nonempty (ringPushout P ≅ P.pushoutObject.toCommRing) := by
  sorry

end

end Formalization.Books.Dpa.Unit03
