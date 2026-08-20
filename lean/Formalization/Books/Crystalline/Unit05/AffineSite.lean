import Formalization.Books.Crystalline.Unit02.DividedPowerEnvelope
import Formalization.Books.Crystalline.Unit04
import Formalization.Books.Dpa.Unit02
import Formalization.Books.Dpa.Unit04
import Formalization.Books.Categories.Unit22
import Mathlib.Algebra.Category.CommAlgCat.Basic
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits
import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.RingTheory.Ideal.Quotient.Basic

/-!
# Crystalline Cohomology, Chapter 5: Affine crystalline site

This file formalizes the algebraic affine crystalline site. Divided-power
rings, divided-power morphisms, envelopes, completions, and quotient maps are
reused from the preceding chapters. Categorical existence claims are stated
as interfaces; their proofs belong to the proof stage.
-/

namespace Formalization.Books.Crystalline.Unit05

open CategoryTheory CategoryTheory.Limits
open Formalization.Books.Dpa.Unit02
open Formalization.Books.Dpa.Unit03
open Formalization.Books.Dpa.Unit03.DividedPowerRing
open Formalization.Books.Dpa.Unit04
open Formalization.Books.Crystalline.Unit02
open Formalization.Books.Crystalline.Unit04
open Formalization.Books.Categories.Unit22

universe u

noncomputable section

/-! ## The affine crystalline situation -/

/-- The hypotheses fixed in the affine crystalline site section. -/
structure AffineCrystallineSituation where
  p : ℕ
  hp : Nat.Prime p
  A : DividedPowerRing.{u}
  A_is_ZLocalized : IsZLocalizedAtPrime p (A : Type u)
  C : Type u
  [commRingC : CommRing C]
  AtoC : (A : Type u) →+* C
  IC_zero : Ideal.map AtoC A.ideal = ⊥
  p_nilpotent : IsNilpotent (p : C)

attribute [instance] AffineCrystallineSituation.commRingC

/-- The map A/I → C in the commutative square of the affine situation. -/
noncomputable def AffineCrystallineSituation.quotientToC
    (S : AffineCrystallineSituation.{u}) :
    (S.A : Type u) ⧸ S.A.ideal →+* S.C :=
  Ideal.Quotient.lift S.A.ideal S.AtoC (by
    intro x hx
    have hx' : S.AtoC x ∈ (⊥ : Ideal S.C) := by
      rw [← S.IC_zero]
      exact Ideal.mem_map_of_mem S.AtoC hx
    simpa using hx')

/-! ## Divided-power thickenings and their category -/

/-- A divided-power thickening of C over the fixed divided-power base. -/
structure AffineThickening (S : AffineCrystallineSituation.{u}) where
  B : DividedPowerRing.{u}
  base : DividedPowerRing.Hom S.A B
  p_nilpotent : IsNilpotent (S.p : (B : Type u))
  CtoQuotient : S.C →+* ((B : Type u) ⧸ B.ideal)
  commutes : CtoQuotient.comp S.AtoC =
    (Ideal.Quotient.mk B.ideal).comp base.hom

/-- The quotient ring map induced by a morphism of thickenings. -/
noncomputable def AffineThickening.quotientMap
    {S : AffineCrystallineSituation.{u}}
    {X Y : AffineThickening S} (f : X.B ⟶ Y.B) :
    ((X.B : Type u) ⧸ X.B.ideal) →+* ((Y.B : Type u) ⧸ Y.B.ideal) :=
  quotientMapOfIdealMap f.hom f.ideal_map

/-- A homomorphism of divided-power thickenings. -/
structure AffineThickening.Hom
    {S : AffineCrystallineSituation.{u}}
    (X Y : AffineThickening S) where
  hom : X.B ⟶ Y.B
  quotient_commutes :
    (AffineThickening.quotientMap hom).comp X.CtoQuotient = Y.CtoQuotient

namespace AffineThickening.Hom

@[ext]
theorem ext {S : AffineCrystallineSituation.{u}}
    {X Y : AffineThickening S} (f g : AffineThickening.Hom X Y)
    (h : f.hom = g.hom) : f = g := by
  cases f
  cases g
  cases h
  congr

end AffineThickening.Hom

instance (S : AffineCrystallineSituation.{u}) : Category (AffineThickening S) where
  Hom := AffineThickening.Hom
  id X :=
    { hom := 𝟙 X.B
      quotient_commutes := by sorry }
  comp f g :=
    { hom := f.hom ≫ g.hom
      quotient_commutes := by sorry }
  id_comp := by
    intro X Y f
    apply AffineThickening.Hom.ext _ _
    exact DividedPowerRing.Hom.ext (by ext x; rfl)
  comp_id := by
    intro X Y f
    apply AffineThickening.Hom.ext _ _
    exact DividedPowerRing.Hom.ext (by ext x; rfl)
  assoc := by
    intro W X Y Z f g h
    apply AffineThickening.Hom.ext _ _
    exact DividedPowerRing.Hom.ext (by ext x; rfl)

/-- The exact affine crystalline site, where C → B/J is an isomorphism. -/
def IsExact (X : AffineThickening S) : Prop := Function.Bijective X.CtoQuotient

def exactProperty (S : AffineCrystallineSituation.{u}) :
    ObjectProperty (AffineThickening S) :=
  fun X ↦ IsExact X

/-- Cris(C/A) as the full subcategory of exact affine thickenings. -/
abbrev Cris (S : AffineCrystallineSituation.{u}) :=
  (exactProperty S).FullSubcategory

/-- The quotient is canonically a commutative algebra over C. -/
noncomputable def quotientCAlgebra
    (S : AffineCrystallineSituation.{u}) (X : AffineThickening S) :
    CommAlgCat S.C := by
  letI : Algebra S.C ((X.B : Type u) ⧸ X.B.ideal) := X.CtoQuotient.toAlgebra
  exact CommAlgCat.of S.C ((X.B : Type u) ⧸ X.B.ideal)

/-- The source's quotient-to-C-algebra objectwise interface. -/
theorem quotientCAlgebra_exists
    (S : AffineCrystallineSituation.{u}) (X : AffineThickening S) :
    Nonempty (Algebra S.C ((X.B : Type u) ⧸ X.B.ideal)) := by
  exact ⟨X.CtoQuotient.toAlgebra⟩

/-- The canonical forgetful functor to commutative C-algebras. -/
noncomputable def quotientCAlgebraFunctor
    (S : AffineCrystallineSituation.{u}) :
    AffineThickening S ⥤ CommAlgCat S.C where
  obj X := quotientCAlgebra S X
  map {X Y} f := by
    letI : Algebra S.C ((X.B : Type u) ⧸ X.B.ideal) :=
      X.CtoQuotient.toAlgebra
    letI : Algebra S.C ((Y.B : Type u) ⧸ Y.B.ideal) :=
      Y.CtoQuotient.toAlgebra
    exact CommAlgCat.ofHom
      { toRingHom := AffineThickening.quotientMap f.hom
        commutes' := by
          intro c
          have h := congrArg (fun g => g c) f.quotient_commutes
          simpa [RingHom.algebraMap_toAlgebra] using h }
  map_id := by sorry
  map_comp := by sorry

/-- Every thickening has a locally nilpotent divided-power ideal. -/
theorem ideal_locally_nilpotent
    (S : AffineCrystallineSituation.{u}) (X : AffineThickening S) :
    ∀ x : X.B, x ∈ X.B.ideal → IsNilpotent x := by
  sorry

/-! ## Finite products and nonempty colimits -/

/-- Existence of products for an arbitrary family in a category. -/
def HasAllProducts (C : Type (u + 1)) [Category.{u} C] : Prop :=
  ∀ (I : Type u) (F : I → C),
    Nonempty (HasLimit (Discrete.functor F))

/-- Existence of all equalizers in a category. -/
def HasAllEqualizers (C : Type (u + 1)) [Category.{u} C] : Prop :=
  ∀ {X Y : C} (f g : X ⟶ Y),
    Nonempty (HasLimit (parallelPair f g))

/-- Existence of all pullbacks in a category. -/
def HasAllPullbacks (C : Type (u + 1)) [Category.{u} C] : Prop :=
  ∀ {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z),
    Nonempty (HasLimit (cospan f g))

/-- Existence of an initial object. -/
def HasInitialObject (C : Type (u + 1)) [Category.{u} C] : Prop :=
  ∃ X : C, Nonempty (IsInitial X)

/-- All finite nonempty diagrams admit colimits. -/
def HasFiniteNonemptyColimits (C : Type (u + 1)) [Category.{u} C] : Prop :=
  ∀ (J : Type u) [Finite J] [Nonempty J] [Category.{u} J]
    (F : J ⥤ C), Nonempty (HasColimit F)

/-- A functor preserves colimits of all finite nonempty diagrams. -/
def PreservesFiniteNonemptyColimits
    {C D : Type (u + 1)} [Category.{u} C] [Category.{u} D]
    (F : C ⥤ D) : Prop :=
  ∀ (J : Type u) [Finite J] [Nonempty J] [Category.{u} J],
    PreservesColimitsOfShape J F

/-- The quotient functor commutes with finite nonempty colimits. -/
def QuotientForgetPreservesFiniteNonemptyColimits
    (S : AffineCrystallineSituation.{u}) : Prop :=
  PreservesFiniteNonemptyColimits
    (C := AffineThickening S) (D := CommAlgCat S.C)
    (quotientCAlgebraFunctor S)

/-- The three categorical assertions of the source lemma. -/
/- This definition is placed before the assertion structure because it is one
of the fields of that structure. -/

def CrisInclusionPreservesFiniteNonemptyColimits
    (S : AffineCrystallineSituation.{u}) : Prop :=
  PreservesFiniteNonemptyColimits
    (exactProperty S).ι

structure AffineThickeningColimitAssertions
    (S : AffineCrystallineSituation.{u}) : Prop where
  hasFiniteProducts : HasFiniteProducts (AffineThickening S)
  notAllProducts : ¬ HasAllProducts (AffineThickening S)
  hasFiniteNonemptyColimits : HasFiniteNonemptyColimits (AffineThickening S)
  quotient_preserves : QuotientForgetPreservesFiniteNonemptyColimits S
  cris_hasFiniteNonemptyColimits : HasFiniteNonemptyColimits (Cris S)
  cris_inclusion_preserves : CrisInclusionPreservesFiniteNonemptyColimits S

theorem affineThickening_colimit_assertions
    (S : AffineCrystallineSituation.{u}) :
    AffineThickeningColimitAssertions S := by
  sorry

/-- The source's warning that equalizers, fibre products, and initial objects
are not available uniformly in this category. -/
structure AffineThickeningNonexistenceAssertions : Prop where
  notUniformlyEqualizers :
    ¬ ∀ (S : AffineCrystallineSituation.{u}), HasAllEqualizers (AffineThickening S)
  notUniformlyPullbacks :
    ¬ ∀ (S : AffineCrystallineSituation.{u}), HasAllPullbacks (AffineThickening S)
  notUniformlyInitial :
    ¬ ∀ (S : AffineCrystallineSituation.{u}), HasInitialObject (AffineThickening S)

theorem affineThickening_nonexistence_assertions :
    AffineThickeningNonexistenceAssertions := by
  sorry

/-! ## The completed affine site -/

/-- A completed affine crystalline thickening. The divided-power ideal is the
kernel of the displayed surjection to C; kernel_eq exposes the same ideal
as the ideal of the divided-power ring. -/
structure CompletedThickening (S : AffineCrystallineSituation.{u}) where
  B : DividedPowerRing.{u}
  toC : (B : Type u) →+* S.C
  surjective : Function.Surjective toC
  kernel_eq : RingHom.ker toC = B.ideal
  p_complete : IsAdicComplete (pAdicIdeal (B : Type u) S.p) (B : Type u)
  base : DividedPowerRing.Hom S.A B

structure CompletedThickening.Hom
    {S : AffineCrystallineSituation.{u}}
    (X Y : CompletedThickening S) where
  hom : X.B ⟶ Y.B
  commutes : Y.toC.comp hom.hom = X.toC

namespace CompletedThickening.Hom

@[ext]
theorem ext {S : AffineCrystallineSituation.{u}}
    {X Y : CompletedThickening S} (f g : CompletedThickening.Hom X Y)
    (h : f.hom = g.hom) : f = g := by
  cases f
  cases g
  cases h
  congr

end CompletedThickening.Hom

instance (S : AffineCrystallineSituation.{u}) : Category (CompletedThickening S) where
  Hom := CompletedThickening.Hom
  id X :=
    { hom := 𝟙 X.B
      commutes := by ext x; rfl }
  comp f g :=
    { hom := f.hom ≫ g.hom
      commutes := by sorry }
  id_comp := by
    intro X Y f
    apply CompletedThickening.Hom.ext _ _
    exact DividedPowerRing.Hom.ext (by ext x; rfl)
  comp_id := by
    intro X Y f
    apply CompletedThickening.Hom.ext _ _
    exact DividedPowerRing.Hom.ext (by ext x; rfl)
  assoc := by
    intro W X Y Z f g h
    apply CompletedThickening.Hom.ext _ _
    exact DividedPowerRing.Hom.ext (by ext x; rfl)

/-- The full subcategory of completed thickenings with nilpotent p. -/
def CompletedFiniteProperty
    (S : AffineCrystallineSituation.{u}) :
    ObjectProperty (CompletedThickening S) :=
  fun X ↦ IsNilpotent (S.p : (X.B : Type u))

abbrev CompletedFiniteSubcategory
    (S : AffineCrystallineSituation.{u}) :=
  (CompletedFiniteProperty S).FullSubcategory

/-- A nilpotent p-adic ring is complete for the p-adic ideal. -/
theorem isAdicComplete_of_p_nilpotent
    {B : Type u} [CommRing B] (p : ℕ)
    (h : IsNilpotent (p : B)) :
    IsAdicComplete (pAdicIdeal B p) B := by
  sorry

/-- The assertion that the exact site is the full subcategory of the
completed site on objects with nilpotent p. -/
def CrisIsCompletedFiniteSubcategory
    (S : AffineCrystallineSituation.{u}) : Prop :=
  Nonempty (Cris S ≌ CompletedFiniteSubcategory S)

/-- A source-facing description of a finite reduction B/p^eB of a
completed thickening. -/
def IsFiniteReduction
    {S : AffineCrystallineSituation.{u}}
    (X : CompletedThickening S) (e : ℕ) (Y : Cris S) : Prop :=
  Nonempty (Y.obj.B.toCommRing ≅
    CommRingCat.of ((X.B : Type u) ⧸ pAdicIdeal (X.B : Type u) S.p ^ e))

/-- The completed object is represented by the inverse system of its finite
reductions, and sufficiently large reductions are exact thickenings. -/
def CompletedIsLimitOfFiniteReductions
    {S : AffineCrystallineSituation.{u}}
    (X : CompletedThickening S) : Prop :=
  ∃ (F : (ℕᵒᵖ) ⥤ Cris S),
    (∀ e : ℕ, IsFiniteReduction X e (F.obj (Opposite.op e))) ∧
    (∃ e₀ : ℕ, ∀ e : ℕ, e₀ ≤ e →
      IsFiniteReduction X e (F.obj (Opposite.op e))) ∧
    Nonempty (ProCategory (Cris S))

theorem completed_site_assertions
    (S : AffineCrystallineSituation.{u}) :
    CrisIsCompletedFiniteSubcategory S ∧
      ∀ X : CompletedThickening S, CompletedIsLimitOfFiniteReductions X := by
  sorry

/-! ## Envelope presentations and the three generator statements -/

/-- A surjective affine presentation P → C over A. -/
structure AffinePresentation (S : AffineCrystallineSituation.{u}) where
  P : CommRingCat.{u}
  AtoP : (S.A : Type u) →+* (P : Type u)
  PtoC : (P : Type u) →+* S.C
  surjective : Function.Surjective PtoC
  commutes : PtoC.comp AtoP = S.AtoC

/-- The divided-power envelope associated to an affine presentation. -/
noncomputable def presentationEnvelope
    (Q : AffinePresentation S) :
    DividedPowerEnvelope S.A Q.AtoP (RingHom.ker Q.PtoC)
      (by
        rw [Ideal.map_le_iff_le_comap]
        intro x hx
        change Q.PtoC (Q.AtoP x) = 0
        have hxzero : S.AtoC x = 0 := by
          have hx' : S.AtoC x ∈ (⊥ : Ideal S.C) := by
            rw [← S.IC_zero]
            exact Ideal.mem_map_of_mem S.AtoC hx
          simpa using hx'
        rw [show Q.PtoC (Q.AtoP x) = S.AtoC x by
          exact congrArg (fun f => f x) Q.commutes]
        exact hxzero) :=
  dividedPowerEnvelope S.A Q.AtoP (RingHom.ker Q.PtoC) (by
    rw [Ideal.map_le_iff_le_comap]
    intro x hx
    change Q.PtoC (Q.AtoP x) = 0
    have hx' : S.AtoC x ∈ (⊥ : Ideal S.C) := by
      rw [← S.IC_zero]
      exact Ideal.mem_map_of_mem S.AtoC hx
    have hxzero : S.AtoC x = 0 := by simpa using hx'
    rw [show Q.PtoC (Q.AtoP x) = S.AtoC x by
      exact congrArg (fun f => f x) Q.commutes]
    exact hxzero)

/-- The source's notation D_{P, γ}(J) and its distinguished ideal. -/
abbrev presentationEnvelopeRing (Q : AffinePresentation S) : DividedPowerRing :=
  (presentationEnvelope Q).D

abbrev presentationEnvelopeIdeal (Q : AffinePresentation S) :
    Ideal (presentationEnvelopeRing Q : Type u) :=
  (presentationEnvelope Q).D.ideal

/-- A stage of the P/p^eP envelope construction. The stage is bundled with
the actual divided-power envelope supplied by the preceding chapter. -/
structure PresentationEnvelopeStage
    (Q : AffinePresentation S) (e : ℕ) where
  Pe : CommRingCat.{u}
  Pe_identification : Pe =
    CommRingCat.of ((Q.P : Type u) ⧸ pAdicIdeal (Q.P : Type u) S.p ^ e)
  AtoPe : (S.A : Type u) →+* (Pe : Type u)
  Pe_to_C : (Pe : Type u) →+* S.C
  Pe_to_C_surjective : Function.Surjective Pe_to_C
  commutes : Pe_to_C.comp AtoPe = S.AtoC
  base_ideal_le : Ideal.map AtoPe S.A.ideal ≤ RingHom.ker Pe_to_C
  envelope : DividedPowerEnvelope S.A AtoPe (RingHom.ker Pe_to_C) base_ideal_le
  object : Cris S
  object_equiv : DividedPowerRingEquiv object.obj.B envelope.D
  object_base_compatibility :
    object_equiv.hom.hom.comp object.obj.base.hom = envelope.base.hom

/-! The quotient divided-power ring used in the completion lemma from the
preceding divided-power chapter. -/

noncomputable def pAdicQuotient
    (R : DividedPowerRing.{u}) (p e : ℕ)
    (h : R.dividedPowers.IsSubDPIdeal
      (pAdicIdeal (R : Type u) p ^ e ⊓ R.ideal)) : DividedPowerRing.{u} :=
  { toCommRing := CommRingCat.of
      ((R : Type u) ⧸ pAdicIdeal (R : Type u) p ^ e)
    ideal := Ideal.map
      (Ideal.Quotient.mk (pAdicIdeal (R : Type u) p ^ e)) R.ideal
    dividedPowers := DividedPowers.Quotient.dividedPowers
      R.dividedPowers h }

/-- The list of properties in the source lemma, with finite envelope
stages and their inverse-limit comparison exposed as fields. -/
structure AffineEnvelopeListProperties
    (Q : AffinePresentation S)
    (Dhat : CompletedThickening S) where
  e₀ : ℕ
  D_power_le_ideal : ∀ e : ℕ, e₀ ≤ e →
    pAdicIdeal ((presentationEnvelope Q).D : Type u) S.p ^ e ≤
      (presentationEnvelope Q).D.ideal
  D_subDPIdeal : ∀ e : ℕ, e₀ ≤ e →
    (presentationEnvelope Q).D.dividedPowers.IsSubDPIdeal
      (pAdicIdeal ((presentationEnvelope Q).D : Type u) S.p ^ e ⊓
        (presentationEnvelope Q).D.ideal)
  Dhat_power_le_ideal : ∀ e : ℕ, e₀ ≤ e →
    pAdicIdeal (Dhat.B : Type u) S.p ^ e ≤ Dhat.B.ideal
  Dhat_subDPIdeal : ∀ e : ℕ, e₀ ≤ e →
    Dhat.B.dividedPowers.IsSubDPIdeal
      (pAdicIdeal (Dhat.B : Type u) S.p ^ e ⊓ Dhat.B.ideal)
  quotient_identification : ∀ e : ℕ, e₀ ≤ e →
    ∃ hD : (presentationEnvelope Q).D.dividedPowers.IsSubDPIdeal
        (pAdicIdeal ((presentationEnvelope Q).D : Type u) S.p ^ e ⊓
          (presentationEnvelope Q).D.ideal),
      ∃ stage : PresentationEnvelopeStage Q e,
      Nonempty (DividedPowerRingEquiv
        (pAdicQuotient (presentationEnvelope Q).D S.p e hD)
        stage.envelope.D)
  completed_quotient_identification : ∀ e : ℕ, e₀ ≤ e →
    ∃ hD : (presentationEnvelope Q).D.dividedPowers.IsSubDPIdeal
        (pAdicIdeal ((presentationEnvelope Q).D : Type u) S.p ^ e ⊓
          (presentationEnvelope Q).D.ideal),
      ∃ hDhat : Dhat.B.dividedPowers.IsSubDPIdeal
        (pAdicIdeal (Dhat.B : Type u) S.p ^ e ⊓ Dhat.B.ideal),
        ∃ stage : PresentationEnvelopeStage Q e,
          Nonempty (DividedPowerRingEquiv
            (pAdicQuotient (presentationEnvelope Q).D S.p e hD)
            stage.envelope.D) ∧
          Nonempty (DividedPowerRingEquiv
            (pAdicQuotient Dhat.B S.p e hDhat)
            stage.envelope.D)
  completion_is_limit : ∃ hpres : ∀ e : ℕ, e₀ ≤ e →
      (presentationEnvelope Q).D.dividedPowers.IsSubDPIdeal
        (pAdicIdeal ((presentationEnvelope Q).D : Type u) S.p ^ e ⊓
          (presentationEnvelope Q).D.ideal),
    IsPAdicQuotientLimit (presentationEnvelope Q).D.dividedPowers
      S.p e₀ hpres Dhat.B
  completion_underlying : Nonempty
    (Dhat.B.toCommRing ≅
      CommRingCat.of (pAdicCompletion
        ((presentationEnvelope Q).D : Type u) S.p))

/-- Eventual preservation of p^eD by divided powers, quotient
identifications, exactness of finite stages, the inverse-limit statement,
and membership of the completion in the completed site. -/
theorem presentation_envelope_list_properties
    (Q : AffinePresentation S) :
    ∃ Dhat : CompletedThickening S,
      Nonempty (AffineEnvelopeListProperties Q Dhat) := by
  sorry

/-- A polynomial presentation over A, as used in the set-of-generators
lemma. -/
structure PolynomialPresentation
    (S : AffineCrystallineSituation.{u}) (T : Type u) where
  PtoC : MvPolynomial T (S.A : Type u) →+* S.C
  surjective : Function.Surjective PtoC
  commutes : PtoC.comp (algebraMap (S.A : Type u)
      (MvPolynomial T (S.A : Type u))) = S.AtoC

/-- The polynomial presentation viewed as an affine presentation. -/
def PolynomialPresentation.toAffinePresentation
    {S : AffineCrystallineSituation.{u}} {T : Type u}
    (P : PolynomialPresentation S T) : AffinePresentation S where
  P := CommRingCat.of (MvPolynomial T (S.A : Type u))
  AtoP := algebraMap (S.A : Type u) (MvPolynomial T (S.A : Type u))
  PtoC := P.PtoC
  surjective := P.surjective
  commutes := P.commutes

/-- A finite stage is identified with the divided-power envelope of the
corresponding polynomial quotient. -/
def IsPolynomialEnvelopeStage
    {S : AffineCrystallineSituation.{u}} {T : Type u}
    (P : PolynomialPresentation S T) (e : ℕ)
    (D : AffineThickening S) : Prop :=
  ∃ stage : PresentationEnvelopeStage P.toAffinePresentation e,
    Nonempty (DividedPowerRingEquiv D.B stage.envelope.D)

/-- The source's assertion that every affine thickening receives a map from
some finite polynomial-envelope stage. -/
def PolynomialEnvelopeGenerates
    (P : PolynomialPresentation S T)
    (D : ℕ → AffineThickening S) : Prop :=
  (∀ e : ℕ, IsPolynomialEnvelopeStage P e (D e)) ∧
    ∀ X : AffineThickening S, ∃ e : ℕ,
      Nonempty (AffineThickening.Hom (D e) X)

theorem polynomial_envelope_set_generators
    (P : PolynomialPresentation S T)
    (D : ℕ → AffineThickening S)
    (hD : ∀ e : ℕ, IsPolynomialEnvelopeStage P e (D e)) :
    PolynomialEnvelopeGenerates P D := by
  refine ⟨hD, ?_⟩
  sorry

/-- A completed polynomial envelope and the property that it is the
p-adic completion of the ordinary envelope. -/
def IsCompletedPolynomialEnvelope
    (P : PolynomialPresentation S T)
    (D : CompletedThickening S) : Prop :=
  Nonempty
    (pAdicCompletion
        ((presentationEnvelope P.toAffinePresentation).D : Type u) S.p
      ≃+* (D.B : Type u))

/-- The completed envelope maps to every object of the completed affine site. -/
def CompletedPolynomialEnvelopeGenerates
    (P : PolynomialPresentation S T)
    (D : CompletedThickening S) : Prop :=
  IsCompletedPolynomialEnvelope P D ∧
    ∀ X : CompletedThickening S,
      Nonempty (CompletedThickening.Hom D X)

theorem polynomial_envelope_completion_generates
    (P : PolynomialPresentation S T)
    (D : CompletedThickening S)
    (hD : IsCompletedPolynomialEnvelope P D) :
    CompletedPolynomialEnvelopeGenerates P D := by
  refine ⟨hD, ?_⟩
  sorry

end
end Formalization.Books.Crystalline.Unit05
