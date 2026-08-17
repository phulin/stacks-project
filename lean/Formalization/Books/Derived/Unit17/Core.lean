import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.Algebra.Homology.DerivedCategory.Plus
import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT
import Formalization.Books.Derived.Unit06.Quotients
import Formalization.Books.Derived.Unit10.DistinguishedTriangles
import Formalization.Books.Derived.Unit11.DerivedCategories
import Formalization.Books.Homology.Unit10.SerreSubcategories

/-!
# Derived Categories, Chapter 17: triangulated subcategories

This file contains the canonical object-property and functor constructions
used by the source section.  The cohomology predicates are properties of the
ambient derived category; the bounded variants are also exposed by pulling
those predicates back along Mathlib's canonical bounded inclusions.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Preadditive
open CategoryTheory.Pretriangulated
open CategoryTheory.Triangulated
open Formalization.Books.Derived.Unit06
open Formalization.Books.Derived.Unit08
open Formalization.Books.Derived.Unit10
open Formalization.Books.Derived.Unit11
open Formalization.Books.Homology.Unit10
open scoped CategoryTheory.Pretriangulated.Opposite ZeroObject

universe w v u w' v' u'

namespace Formalization.Books.Derived.Unit17

/-! ## Cohomology subcategories -/

/-- The objects of `D(A)` whose cohomology objects all belong to `P`. -/
def derivedCohomologyProperty
    {A : Type u} [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A] (P : ObjectProperty A) :
    ObjectProperty (DerivedCategory A) :=
  fun X => ∀ n : ℤ, P ((derivedCohomologyFunctor A n).obj X)

/-- The intersection `D⁺(A) ∩ D_P(A)` as an object property of `D(A)`. -/
def derivedCohomologyPlusProperty
    {A : Type u} [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A] (P : ObjectProperty A) :
    ObjectProperty (DerivedCategory A) :=
  derivedPlusProperty A ⊓ derivedCohomologyProperty P

/-- The intersection `D⁻(A) ∩ D_P(A)` as an object property of `D(A)`. -/
def derivedCohomologyMinusProperty
    {A : Type u} [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A] (P : ObjectProperty A) :
    ObjectProperty (DerivedCategory A) :=
  derivedMinusProperty A ⊓ derivedCohomologyProperty P

/-- The intersection `Dᵇ(A) ∩ D_P(A)` as an object property of `D(A)`. -/
def derivedCohomologyBoundedProperty
    {A : Type u} [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A] (P : ObjectProperty A) :
    ObjectProperty (DerivedCategory A) :=
  derivedBoundedProperty A ⊓ derivedCohomologyProperty P

/-- The strictly full subcategory `D_P(A)`. -/
abbrev derivedCohomologySubcategory
    {A : Type u} [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A] (P : ObjectProperty A) : Type _ :=
  (derivedCohomologyProperty P).FullSubcategory

/-- The strictly full subcategory `D⁺_P(A)`. -/
abbrev derivedCohomologyPlusSubcategory
    {A : Type u} [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A] (P : ObjectProperty A) : Type _ :=
  (derivedCohomologyPlusProperty P).FullSubcategory

/-- The strictly full subcategory `D⁻_P(A)`. -/
abbrev derivedCohomologyMinusSubcategory
    {A : Type u} [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A] (P : ObjectProperty A) : Type _ :=
  (derivedCohomologyMinusProperty P).FullSubcategory

/-- The strictly full subcategory `Dᵇ_P(A)`. -/
abbrev derivedCohomologyBoundedSubcategory
    {A : Type u} [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A] (P : ObjectProperty A) : Type _ :=
  (derivedCohomologyBoundedProperty P).FullSubcategory

/- Mathlib supplies the categorical additive structures on the bounded
   derived categories, while the earlier chapters' localization interfaces
   use the combined additive-category class from Homology, Chapter 3. -/
noncomputable instance derivedPlus_additiveCategory
    {A : Type u} [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A] :
    Formalization.Books.Homology.Unit03.AdditiveCategory
      (DerivedCategory.Plus A) :=
  { toPreadditive := inferInstance
    toHasFiniteProducts := inferInstance }

noncomputable instance derivedMinus_additiveCategory
    {A : Type u} [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A] :
    Formalization.Books.Homology.Unit03.AdditiveCategory
      (DerivedCategory.Minus A) :=
  { toPreadditive := inferInstance
    toHasFiniteProducts := inferInstance }

noncomputable instance derivedBounded_additiveCategory
    {A : Type u} [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A] :
    Formalization.Books.Homology.Unit03.AdditiveCategory
      (DerivedCategory.Bounded A) :=
  { toPreadditive := inferInstance
    toHasFiniteProducts := inferInstance }

/- The following instances expose the triangulated structure proved in the
source lemma to later exact-functor interfaces.  Their propositions are the
corresponding source theorem interfaces; the proof is deferred with the rest
of the chapter. -/

noncomputable instance derivedCohomologyProperty_closedUnderIsomorphisms
    {A : Type u} [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A] (P : ObjectProperty A)
    [P.IsWeakSerreClass] :
    (derivedCohomologyProperty P).IsClosedUnderIsomorphisms := by
  sorry

noncomputable instance derivedCohomologyProperty_isTriangulated
    {A : Type u} [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A] (P : ObjectProperty A)
    [P.IsWeakSerreClass] :
    (derivedCohomologyProperty P).IsTriangulated := by
  sorry

/- A Serre class is, in particular, a weak Serre class in the source's
terminology.  This bridge lets the comparison interfaces below retain the
source's Serre-only hypotheses. -/
noncomputable instance serreClass_isWeakSerreClass
    {A : Type u} [Category.{v} A] [Abelian A]
    (P : ObjectProperty A) [P.IsSerreClass] :
    P.IsWeakSerreClass := by
  sorry

/-! ## Bounded versions as full subcategories of bounded derived categories -/

/-- The pullback of `D_P(A)` to `D⁺(A)`. -/
def derivedCohomologyPlusWithinProperty
    {A : Type u} [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A] (P : ObjectProperty A) :
    ObjectProperty (DerivedCategory.Plus A) :=
  (derivedCohomologyProperty P).inverseImage
    (DerivedCategory.Plus.ι (C := A))

/-- The pullback of `D_P(A)` to `D⁻(A)`. -/
def derivedCohomologyMinusWithinProperty
    {A : Type u} [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A] (P : ObjectProperty A) :
    ObjectProperty (DerivedCategory.Minus A) :=
  (derivedCohomologyProperty P).inverseImage
    (DerivedCategory.Minus.ι (C := A))

/-- The pullback of `D_P(A)` to `Dᵇ(A)`. -/
def derivedCohomologyBoundedWithinProperty
    {A : Type u} [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A] (P : ObjectProperty A) :
    ObjectProperty (DerivedCategory.Bounded A) :=
  (derivedCohomologyProperty P).inverseImage
    (DerivedCategory.Bounded.ι (C := A))

abbrev derivedCohomologyPlusWithinSubcategory
    {A : Type u} [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A] (P : ObjectProperty A) : Type _ :=
  (derivedCohomologyPlusWithinProperty P).FullSubcategory

abbrev derivedCohomologyMinusWithinSubcategory
    {A : Type u} [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A] (P : ObjectProperty A) : Type _ :=
  (derivedCohomologyMinusWithinProperty P).FullSubcategory

abbrev derivedCohomologyBoundedWithinSubcategory
    {A : Type u} [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A] (P : ObjectProperty A) : Type _ :=
  (derivedCohomologyBoundedWithinProperty P).FullSubcategory

/-! ## Exact functors on derived categories -/

/-- Mathlib's derived functor attached to a bundled exact functor. -/
noncomputable def exactDerivedFunctor
    {C : Type u} [Category.{v} C] [Abelian C]
    {D : Type u'} [Category.{v'} D] [Abelian D]
    [HasDerivedCategory.{w} C] [HasDerivedCategory.{w'} D]
    (F : C ⥤ₑ D) : DerivedCategory C ⥤ DerivedCategory D := by
  letI : F.obj.Additive :=
    (exactFunctor_le_additiveFunctor C D) F.obj F.property
  exact F.obj.mapDerivedCategory

/- A weak Serre class has the abelian full-subcategory and exact-inclusion
interfaces supplied by Homology, Chapter 10. -/
noncomputable instance weakSerreFullSubcategory_abelian
    {A : Type u} [Category.{v} A] [Abelian A]
    (P : ObjectProperty A) [P.IsWeakSerreClass] :
    Abelian P.FullSubcategory :=
  (weak_serre_subcategory_is_abelian_and_inclusion_exact P).1.some

noncomputable instance weakSerreInclusion_preservesFiniteLimits
    {A : Type u} [Category.{v} A] [Abelian A]
    (P : ObjectProperty A) [P.IsWeakSerreClass] :
    PreservesFiniteLimits P.ι :=
  (weak_serre_subcategory_is_abelian_and_inclusion_exact P).2.1

noncomputable instance weakSerreInclusion_preservesFiniteColimits
    {A : Type u} [Category.{v} A] [Abelian A]
    (P : ObjectProperty A) [P.IsWeakSerreClass] :
    PreservesFiniteColimits P.ι :=
  (weak_serre_subcategory_is_abelian_and_inclusion_exact P).2.2

noncomputable def weakSerreInclusionExactFunctor
    {A : Type u} [Category.{v} A] [Abelian A]
    (P : ObjectProperty A) [P.IsWeakSerreClass] :
    P.FullSubcategory ⥤ₑ A :=
  ExactFunctor.of P.ι

/-- The canonical derived functor induced by the exact inclusion. -/
noncomputable def derivedInclusionFunctor
    {A : Type u} [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A]
    (P : ObjectProperty A) [P.IsWeakSerreClass]
    [HasDerivedCategory.{w} P.FullSubcategory] :
    DerivedCategory P.FullSubcategory ⥤ DerivedCategory A :=
  exactDerivedFunctor (weakSerreInclusionExactFunctor P)

/-- Cohomology of the derived image of a complex made from `P`-objects lies
in `P`. -/
theorem derivedInclusion_cohomology_mem
    {A : Type u} [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A]
    (P : ObjectProperty A) [P.IsWeakSerreClass]
    [HasDerivedCategory.{w} P.FullSubcategory]
    (X : DerivedCategory P.FullSubcategory) :
    derivedCohomologyProperty P ((derivedInclusionFunctor P).obj X) := by
  sorry

/-- The comparison functor `D(P) ⥤ D_P(A)`. -/
noncomputable def derivedComparisonFunctor
    {A : Type u} [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A]
    (P : ObjectProperty A) [P.IsWeakSerreClass]
    [HasDerivedCategory.{w} P.FullSubcategory] :
    DerivedCategory P.FullSubcategory ⥤ derivedCohomologySubcategory P :=
  (derivedCohomologyProperty P).lift
    (derivedInclusionFunctor P) (derivedInclusion_cohomology_mem P)

/-! ### Restriction to bounded derived categories -/

theorem derivedInclusion_preserves_plus
    {A : Type u} [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A]
    (P : ObjectProperty A) [P.IsWeakSerreClass]
    [HasDerivedCategory.{w} P.FullSubcategory]
    (X : DerivedCategory.Plus P.FullSubcategory) :
    derivedPlusProperty A
      ((derivedInclusionFunctor P).obj
        ((DerivedCategory.Plus.ι (C := P.FullSubcategory)).obj X)) := by
  sorry

theorem derivedInclusion_preserves_minus
    {A : Type u} [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A]
    (P : ObjectProperty A) [P.IsWeakSerreClass]
    [HasDerivedCategory.{w} P.FullSubcategory]
    (X : DerivedCategory.Minus P.FullSubcategory) :
    derivedMinusProperty A
      ((derivedInclusionFunctor P).obj
        ((DerivedCategory.Minus.ι (C := P.FullSubcategory)).obj X)) := by
  sorry

theorem derivedInclusion_preserves_bounded
    {A : Type u} [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A]
    (P : ObjectProperty A) [P.IsWeakSerreClass]
    [HasDerivedCategory.{w} P.FullSubcategory]
    (X : DerivedCategory.Bounded P.FullSubcategory) :
    derivedBoundedProperty A
      ((derivedInclusionFunctor P).obj
        ((DerivedCategory.Bounded.ι (C := P.FullSubcategory)).obj X)) := by
  sorry

noncomputable def derivedInclusionPlusFunctor
    {A : Type u} [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A]
    (P : ObjectProperty A) [P.IsWeakSerreClass]
    [HasDerivedCategory.{w} P.FullSubcategory] :
    DerivedCategory.Plus P.FullSubcategory ⥤ DerivedCategory.Plus A :=
  (derivedPlusProperty A).lift
    ((DerivedCategory.Plus.ι (C := P.FullSubcategory)) ⋙
      derivedInclusionFunctor P)
    (derivedInclusion_preserves_plus P)

noncomputable def derivedInclusionMinusFunctor
    {A : Type u} [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A]
    (P : ObjectProperty A) [P.IsWeakSerreClass]
    [HasDerivedCategory.{w} P.FullSubcategory] :
    DerivedCategory.Minus P.FullSubcategory ⥤ DerivedCategory.Minus A :=
  (derivedMinusProperty A).lift
    ((DerivedCategory.Minus.ι (C := P.FullSubcategory)) ⋙
      derivedInclusionFunctor P)
    (derivedInclusion_preserves_minus P)

noncomputable def derivedInclusionBoundedFunctor
    {A : Type u} [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A]
    (P : ObjectProperty A) [P.IsWeakSerreClass]
    [HasDerivedCategory.{w} P.FullSubcategory] :
    DerivedCategory.Bounded P.FullSubcategory ⥤ DerivedCategory.Bounded A :=
  (derivedBoundedProperty A).lift
    ((DerivedCategory.Bounded.ι (C := P.FullSubcategory)) ⋙
      derivedInclusionFunctor P)
    (derivedInclusion_preserves_bounded P)

theorem derivedInclusionPlus_cohomology_mem
    {A : Type u} [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A]
    (P : ObjectProperty A) [P.IsWeakSerreClass]
    [HasDerivedCategory.{w} P.FullSubcategory]
    (X : DerivedCategory.Plus P.FullSubcategory) :
    derivedCohomologyPlusWithinProperty P
      ((derivedInclusionPlusFunctor P).obj X) := by
  sorry

theorem derivedInclusionMinus_cohomology_mem
    {A : Type u} [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A]
    (P : ObjectProperty A) [P.IsWeakSerreClass]
    [HasDerivedCategory.{w} P.FullSubcategory]
    (X : DerivedCategory.Minus P.FullSubcategory) :
    derivedCohomologyMinusWithinProperty P
      ((derivedInclusionMinusFunctor P).obj X) := by
  sorry

theorem derivedInclusionBounded_cohomology_mem
    {A : Type u} [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A]
    (P : ObjectProperty A) [P.IsWeakSerreClass]
    [HasDerivedCategory.{w} P.FullSubcategory]
    (X : DerivedCategory.Bounded P.FullSubcategory) :
    derivedCohomologyBoundedWithinProperty P
      ((derivedInclusionBoundedFunctor P).obj X) := by
  sorry

/-- The bounded-below version of the comparison functor. -/
noncomputable def derivedComparisonPlus
    {A : Type u} [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A]
    (P : ObjectProperty A) [P.IsWeakSerreClass]
    [HasDerivedCategory.{w} P.FullSubcategory] :
    DerivedCategory.Plus P.FullSubcategory ⥤
      derivedCohomologyPlusWithinSubcategory P :=
  (derivedCohomologyPlusWithinProperty P).lift
    (derivedInclusionPlusFunctor P) (derivedInclusionPlus_cohomology_mem P)

/-- The bounded-above version of the comparison functor. -/
noncomputable def derivedComparisonMinus
    {A : Type u} [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A]
    (P : ObjectProperty A) [P.IsWeakSerreClass]
    [HasDerivedCategory.{w} P.FullSubcategory] :
    DerivedCategory.Minus P.FullSubcategory ⥤
      derivedCohomologyMinusWithinSubcategory P :=
  (derivedCohomologyMinusWithinProperty P).lift
    (derivedInclusionMinusFunctor P) (derivedInclusionMinus_cohomology_mem P)

/-- The bounded version of the comparison functor. -/
noncomputable def derivedComparisonBounded
    {A : Type u} [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A]
    (P : ObjectProperty A) [P.IsWeakSerreClass]
    [HasDerivedCategory.{w} P.FullSubcategory] :
    DerivedCategory.Bounded P.FullSubcategory ⥤
      derivedCohomologyBoundedWithinSubcategory P :=
  (derivedCohomologyBoundedWithinProperty P).lift
    (derivedInclusionBoundedFunctor P)
    (derivedInclusionBounded_cohomology_mem P)

/-! ## Serre quotients and their derived functors -/

noncomputable instance serreQuotient_abelian
    {A : Type u} [Category.{v} A] [Abelian A]
    (P : ObjectProperty A) [P.IsSerreClass] :
    Abelian (serreQuotient P) :=
  serreQuotientAbelian P

/-- The exact functor `D(A) ⥤ D(A / P)`. -/
noncomputable def derivedSerreQuotientFunctor
    {A : Type u} [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A]
    (P : ObjectProperty A) [P.IsSerreClass]
    [HasDerivedCategory.{w'} (serreQuotient P)] :
    DerivedCategory A ⥤ DerivedCategory (serreQuotient P) :=
  exactDerivedFunctor (serreQuotientExactFunctor P)

/-- The kernel property of the derived Serre-quotient functor. -/
theorem derivedSerreQuotient_kernel_property
    {A : Type u} [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A]
    (P : ObjectProperty A) [P.IsSerreClass]
    [HasDerivedCategory.{w'} (serreQuotient P)] :
    functorKernel (derivedSerreQuotientFunctor P) =
      derivedCohomologyProperty P := by
  sorry

/-- The quotient morphisms attached to `D_P(A)`. -/
abbrev derivedSerreQuotientMorphismProperty
    {A : Type u} [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A]
    (P : ObjectProperty A) [P.IsSerreClass] :
    MorphismProperty (DerivedCategory A) :=
  quotientMorphismProperty (derivedCohomologyProperty P)

/-- The Verdier quotient `D(A) / D_P(A)`. -/
abbrev derivedSerreQuotientCategory
    {A : Type u} [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A]
    (P : ObjectProperty A) [P.IsSerreClass] : Type _ :=
  quotientCategory (derivedCohomologyProperty P)

/-- The derived Serre-quotient functor inverts the quotient morphisms. -/
theorem derivedSerreQuotient_inverts
    {A : Type u} [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A]
    (P : ObjectProperty A) [P.IsSerreClass]
    [HasDerivedCategory.{w'} (serreQuotient P)] :
    (derivedSerreQuotientMorphismProperty P).IsInvertedBy
      (derivedSerreQuotientFunctor P) := by
  sorry

/-- The canonical functor `D(A) / D_P(A) ⥤ D(A / P)`. -/
noncomputable def derivedSerreQuotientFactor
    {A : Type u} [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A]
    (P : ObjectProperty A) [P.IsSerreClass]
    [HasDerivedCategory.{w'} (serreQuotient P)] :
    derivedSerreQuotientCategory P ⥤
      DerivedCategory (serreQuotient P) :=
  quotientFactor (derivedCohomologyProperty P)
    (derivedSerreQuotientFunctor P) (derivedSerreQuotient_inverts P)

/-! ### Bounded quotient functors -/

abbrev derivedSerreQuotientPlusMorphismProperty
    {A : Type u} [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A]
    (P : ObjectProperty A) [P.IsSerreClass] :
    MorphismProperty (DerivedCategory.Plus A) :=
  quotientMorphismProperty (derivedCohomologyPlusWithinProperty P)

abbrev derivedSerreQuotientMinusMorphismProperty
    {A : Type u} [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A]
    (P : ObjectProperty A) [P.IsSerreClass] :
    MorphismProperty (DerivedCategory.Minus A) :=
  quotientMorphismProperty (derivedCohomologyMinusWithinProperty P)

abbrev derivedSerreQuotientBoundedMorphismProperty
    {A : Type u} [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A]
    (P : ObjectProperty A) [P.IsSerreClass] :
    MorphismProperty (DerivedCategory.Bounded A) :=
  quotientMorphismProperty (derivedCohomologyBoundedWithinProperty P)

abbrev derivedSerreQuotientPlusCategory
    {A : Type u} [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A]
    (P : ObjectProperty A) [P.IsSerreClass] : Type _ :=
  quotientCategory (derivedCohomologyPlusWithinProperty P)

abbrev derivedSerreQuotientMinusCategory
    {A : Type u} [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A]
    (P : ObjectProperty A) [P.IsSerreClass] : Type _ :=
  quotientCategory (derivedCohomologyMinusWithinProperty P)

abbrev derivedSerreQuotientBoundedCategory
    {A : Type u} [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A] (P : ObjectProperty A) [P.IsSerreClass] : Type _ :=
  quotientCategory (derivedCohomologyBoundedWithinProperty P)

theorem derivedSerreQuotient_preserves_plus
    {A : Type u} [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A]
    (P : ObjectProperty A) [P.IsSerreClass]
    [HasDerivedCategory.{w'} (serreQuotient P)]
    (X : DerivedCategory.Plus A) :
    derivedPlusProperty (serreQuotient P)
      ((derivedSerreQuotientFunctor P).obj
        ((DerivedCategory.Plus.ι (C := A)).obj X)) := by
  sorry

theorem derivedSerreQuotient_preserves_minus
    {A : Type u} [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A]
    (P : ObjectProperty A) [P.IsSerreClass]
    [HasDerivedCategory.{w'} (serreQuotient P)]
    (X : DerivedCategory.Minus A) :
    derivedMinusProperty (serreQuotient P)
      ((derivedSerreQuotientFunctor P).obj
        ((DerivedCategory.Minus.ι (C := A)).obj X)) := by
  sorry

theorem derivedSerreQuotient_preserves_bounded
    {A : Type u} [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A]
    (P : ObjectProperty A) [P.IsSerreClass]
    [HasDerivedCategory.{w'} (serreQuotient P)]
    (X : DerivedCategory.Bounded A) :
    derivedBoundedProperty (serreQuotient P)
      ((derivedSerreQuotientFunctor P).obj
        ((DerivedCategory.Bounded.ι (C := A)).obj X)) := by
  sorry

noncomputable def derivedSerreQuotientPlusFunctor
    {A : Type u} [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A]
    (P : ObjectProperty A) [P.IsSerreClass]
    [HasDerivedCategory.{w'} (serreQuotient P)] :
    DerivedCategory.Plus A ⥤ DerivedCategory.Plus (serreQuotient P) :=
  (derivedPlusProperty (serreQuotient P)).lift
    ((DerivedCategory.Plus.ι (C := A)) ⋙ derivedSerreQuotientFunctor P)
    (derivedSerreQuotient_preserves_plus P)

noncomputable def derivedSerreQuotientMinusFunctor
    {A : Type u} [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A]
    (P : ObjectProperty A) [P.IsSerreClass]
    [HasDerivedCategory.{w'} (serreQuotient P)] :
    DerivedCategory.Minus A ⥤ DerivedCategory.Minus (serreQuotient P) :=
  (derivedMinusProperty (serreQuotient P)).lift
    ((DerivedCategory.Minus.ι (C := A)) ⋙ derivedSerreQuotientFunctor P)
    (derivedSerreQuotient_preserves_minus P)

noncomputable def derivedSerreQuotientBoundedFunctor
    {A : Type u} [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A]
    (P : ObjectProperty A) [P.IsSerreClass]
    [HasDerivedCategory.{w'} (serreQuotient P)] :
    DerivedCategory.Bounded A ⥤ DerivedCategory.Bounded (serreQuotient P) :=
  (derivedBoundedProperty (serreQuotient P)).lift
    ((DerivedCategory.Bounded.ι (C := A)) ⋙ derivedSerreQuotientFunctor P)
    (derivedSerreQuotient_preserves_bounded P)

theorem derivedSerreQuotientPlus_inverts
    {A : Type u} [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A]
    (P : ObjectProperty A) [P.IsSerreClass]
    [HasDerivedCategory.{w'} (serreQuotient P)] :
    (derivedSerreQuotientPlusMorphismProperty P).IsInvertedBy
      (derivedSerreQuotientPlusFunctor P) := by
  sorry

theorem derivedSerreQuotientMinus_inverts
    {A : Type u} [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A]
    (P : ObjectProperty A) [P.IsSerreClass]
    [HasDerivedCategory.{w'} (serreQuotient P)] :
    (derivedSerreQuotientMinusMorphismProperty P).IsInvertedBy
      (derivedSerreQuotientMinusFunctor P) := by
  sorry

theorem derivedSerreQuotientBounded_inverts
    {A : Type u} [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A]
    (P : ObjectProperty A) [P.IsSerreClass]
    [HasDerivedCategory.{w'} (serreQuotient P)] :
    (derivedSerreQuotientBoundedMorphismProperty P).IsInvertedBy
      (derivedSerreQuotientBoundedFunctor P) := by
  sorry

noncomputable def derivedSerreQuotientPlusFactor
    {A : Type u} [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A]
    (P : ObjectProperty A) [P.IsSerreClass]
    [HasDerivedCategory.{w'} (serreQuotient P)] :
    derivedSerreQuotientPlusCategory P ⥤
      DerivedCategory.Plus (serreQuotient P) :=
  quotientFactor (derivedCohomologyPlusWithinProperty P)
    (derivedSerreQuotientPlusFunctor P) (by
      simpa [derivedSerreQuotientPlusMorphismProperty] using
        derivedSerreQuotientPlus_inverts P)

noncomputable def derivedSerreQuotientMinusFactor
    {A : Type u} [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A]
    (P : ObjectProperty A) [P.IsSerreClass]
    [HasDerivedCategory.{w'} (serreQuotient P)] :
    derivedSerreQuotientMinusCategory P ⥤
      DerivedCategory.Minus (serreQuotient P) :=
  quotientFactor (derivedCohomologyMinusWithinProperty P)
    (derivedSerreQuotientMinusFunctor P) (by
      simpa [derivedSerreQuotientMinusMorphismProperty] using
        derivedSerreQuotientMinus_inverts P)

noncomputable def derivedSerreQuotientBoundedFactor
    {A : Type u} [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A]
    (P : ObjectProperty A) [P.IsSerreClass]
    [HasDerivedCategory.{w'} (serreQuotient P)] :
    derivedSerreQuotientBoundedCategory P ⥤
      DerivedCategory.Bounded (serreQuotient P) :=
  quotientFactor (derivedCohomologyBoundedWithinProperty P)
    (derivedSerreQuotientBoundedFunctor P) (by
      simpa [derivedSerreQuotientBoundedMorphismProperty] using
        derivedSerreQuotientBounded_inverts P)

/-! ## The bounded-above lifting hypothesis and replacement data -/

/-- Every epimorphism onto a `P`-object can be covered by a `P`-subobject. -/
def SerreLiftingCondition
    {A : Type u} [Category.{v} A] [Abelian A]
    (P : ObjectProperty A) : Prop :=
  ∀ {X Y : A} (f : X ⟶ Y), Epi f → P Y →
    ∃ (X' : A) (i : X' ⟶ X) (g : X' ⟶ Y),
      P X' ∧ Mono i ∧ Epi g ∧ i ≫ f = g

/-- Data expressing the bounded-above subcomplex replacement claim in the
proof of the fully-faithful embedding lemma. -/
structure BoundedAboveSubcomplexReplacement
    {A : Type u} [Category.{v} A] [Abelian A]
    (P : ObjectProperty A) (X : CochainComplex A ℤ)
    (B : ℤ → A) (b : ∀ i : ℤ, B i ⟶ X.X i) where
  b_mem : ∀ i : ℤ, P (B i)
  b_mono : ∀ i : ℤ, Mono (b i)
  Y : CochainComplex A ℤ
  inclusion : Y ⟶ X
  inclusion_mono : ∀ i : ℤ, Mono (inclusion.f i)
  quasiIso : QuasiIso inclusion
  term_mem : ∀ i : ℤ, P (Y.X i)
  contains : ∀ i : ℤ, ∃ q : B i ⟶ Y.X i, q ≫ inclusion.f i = b i

end Formalization.Books.Derived.Unit17
