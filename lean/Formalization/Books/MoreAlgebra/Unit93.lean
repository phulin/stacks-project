import Formalization.Books.MoreAlgebra.Unit92
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-!
# More on Algebra, Chapter 93: The category of derived complete modules

This file records the category-level statements following the definition of
derived complete modules in Chapter 92.  The derived completion and
cohomology operations are the canonical interfaces from that chapter.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open Formalization.Books.MoreAlgebra.Unit67
open Formalization.Books.MoreAlgebra.Unit92

universe u v w

namespace Formalization.Books.MoreAlgebra.Unit93

abbrev Mod (A : Type u) [CommRing A] := ModuleCat.{u} A

abbrev D (A : Type u) [CommRing A]
    [HasDerivedCategory.{w} (Mod A)] := DerivedCategory (Mod A)

/-! ## The category and its inclusion -/

/- The inclusion is the canonical full-subcategory inclusion attached to the
 property defined in Chapter 92. -/
def derivedCompleteModuleInclusion {A : Type u} [CommRing A]
    [HasDerivedCategory.{w} (Mod A)] (I : Ideal A) :
    DerivedCompleteModuleCategory I ⥤ Mod A :=
  (derivedCompleteModuleProperty I).ι

/- The source's assertion that the full subcategory is abelian is installed as
 an instance so that the ordinary abelian-category API is available to users. -/
noncomputable instance derivedCompleteModuleCategory_abelian
    {A : Type u} [CommRing A] [HasDerivedCategory.{w} (Mod A)] (I : Ideal A) :
    Abelian (DerivedCompleteModuleCategory I) := by
  sorry

/- Products are included in the stronger arbitrary-limits statement below;
 the preservation statement records that they agree with module products. -/
theorem derivedCompleteModuleCategory_has_products
    {A : Type u} [CommRing A] [HasDerivedCategory.{w} (Mod A)] (I : Ideal A) :
    HasProducts (DerivedCompleteModuleCategory I) := by
  sorry

theorem derivedCompleteModuleCategory_has_limits
    {A : Type u} [CommRing A] [HasDerivedCategory.{w} (Mod A)] (I : Ideal A) :
    HasLimits (DerivedCompleteModuleCategory I) := by
  sorry

theorem derivedCompleteModuleInclusion_preserves_limits
    {A : Type u} [CommRing A] [HasDerivedCategory.{w} (Mod A)] (I : Ideal A) :
    PreservesLimits (derivedCompleteModuleInclusion I) := by
  sorry

/- Exactness of the inclusion is expressed using Mathlib's left- and
 right-exact interfaces, i.e. preservation of finite limits and colimits. -/
theorem derivedCompleteModuleInclusion_exact
    {A : Type u} [CommRing A] [HasDerivedCategory.{w} (Mod A)] (I : Ideal A) :
    PreservesFiniteLimits (derivedCompleteModuleInclusion I) ∧
      PreservesFiniteColimits (derivedCompleteModuleInclusion I) := by
  sorry

/-! ## The finite-generation adjunction -/

/-- The module underlying the source's `H⁰(M^ )`. -/
noncomputable def derivedCompleteModuleCompletionH0
    {A : Type u} [CommRing A] [HasDerivedCategory.{w} (Mod A)]
    (I : Ideal A) (hI : I.FG) (M : Mod A) : Mod A :=
  (derivedCohomology A 0).obj
    (completedObject I hI (Formalization.Books.MoreAlgebra.Unit67.moduleInDerived A M))

/- The positive cohomology vanishing used to identify maps out of `H⁰(M^ )`
 with maps out of the derived completion. -/
theorem derivedCompleteModuleCompletion_positive_cohomology_vanishes
    {A : Type u} [CommRing A] [HasDerivedCategory.{w} (Mod A)]
    (I : Ideal A) (hI : I.FG) (M : Mod A) :
    ∀ i : ℤ, 0 < i →
      IsZero ((derivedCohomology A i).obj
        (completedObject I hI
          (Formalization.Books.MoreAlgebra.Unit67.moduleInDerived A M))) := by
  sorry

/-- The left-adjoint interface for `M ↦ H⁰(M^ )`.

The object formula is recorded separately because the existing derived-category
API presents `moduleInDerived` as an object-level construction rather than as
a functor on `ModuleCat`. -/
structure DerivedCompleteModuleCompletionData
    {A : Type u} [CommRing A] [HasDerivedCategory.{w} (Mod A)]
    (I : Ideal A) (hI : I.FG) where
  completion : Mod A ⥤ DerivedCompleteModuleCategory I
  object_formula : ∀ M,
    (completion.obj M).obj = derivedCompleteModuleCompletionH0 I hI M
  adjunction : completion ⊣ derivedCompleteModuleInclusion I

theorem exists_derivedCompleteModuleCompletionData
    {A : Type u} [CommRing A] [HasDerivedCategory.{w} (Mod A)]
    (I : Ideal A) (hI : I.FG) :
    Nonempty (DerivedCompleteModuleCompletionData I hI) := by
  sorry

noncomputable def derivedCompleteModuleCompletionData
    {A : Type u} [CommRing A] [HasDerivedCategory.{w} (Mod A)]
    (I : Ideal A) (hI : I.FG) :
    DerivedCompleteModuleCompletionData I hI :=
  Classical.choice (exists_derivedCompleteModuleCompletionData I hI)

noncomputable abbrev derivedCompleteModuleCompletion
    {A : Type u} [CommRing A] [HasDerivedCategory.{w} (Mod A)]
    (I : Ideal A) (hI : I.FG) : Mod A ⥤ DerivedCompleteModuleCategory I :=
  (derivedCompleteModuleCompletionData I hI).completion

theorem derivedCompleteModuleCompletion_obj_formula
    {A : Type u} [CommRing A] [HasDerivedCategory.{w} (Mod A)]
    (I : Ideal A) (hI : I.FG) (M : Mod A) :
      ((derivedCompleteModuleCompletion I hI).obj M).obj =
      derivedCompleteModuleCompletionH0 I hI M := by
  exact (derivedCompleteModuleCompletionData I hI).object_formula M

noncomputable abbrev derivedCompleteModuleCompletionAdjunction
    {A : Type u} [CommRing A] [HasDerivedCategory.{w} (Mod A)]
    (I : Ideal A) (hI : I.FG) :
    derivedCompleteModuleCompletion I hI ⊣
      derivedCompleteModuleInclusion I :=
  (derivedCompleteModuleCompletionData I hI).adjunction

theorem derivedCompleteModuleCompletion_leftAdjoint
    {A : Type u} [CommRing A] [HasDerivedCategory.{w} (Mod A)]
    (I : Ideal A) (hI : I.FG) :
    Nonempty (derivedCompleteModuleCompletion I hI ⊣
      derivedCompleteModuleInclusion I) := by
  exact ⟨derivedCompleteModuleCompletionAdjunction I hI⟩

/-! ## Colimits -/

/- This is the source's colimit object: take the module colimit and then apply
 the finite-generation completion left adjoint. -/
noncomputable def derivedCompleteModuleColimit
    {A : Type u} [CommRing A] [HasDerivedCategory.{w} (Mod A)]
    (I : Ideal A) (hI : I.FG) {T : Type u} [Preorder T]
    (F : T ⥤ DerivedCompleteModuleCategory I) :
    DerivedCompleteModuleCategory I :=
  (derivedCompleteModuleCompletion I hI).obj
    (colimit (F ⋙ derivedCompleteModuleInclusion I))

noncomputable def derivedCompleteModuleColimitCocone
    {A : Type u} [CommRing A] [HasDerivedCategory.{w} (Mod A)]
    (I : Ideal A) (hI : I.FG) {T : Type u} [Preorder T]
    (F : T ⥤ DerivedCompleteModuleCategory I) : Cocone F where
  pt := derivedCompleteModuleColimit I hI F
  ι :=
    { app := fun t => ObjectProperty.homMk <|
        colimit.ι (F ⋙ derivedCompleteModuleInclusion I) t ≫
          (derivedCompleteModuleCompletionAdjunction I hI).unit.app
            (colimit (F ⋙ derivedCompleteModuleInclusion I))
      naturality := by
        intro i j hij
        apply ObjectProperty.hom_ext
        change
          (F ⋙ derivedCompleteModuleInclusion I).map hij ≫
              colimit.ι (F ⋙ derivedCompleteModuleInclusion I) j ≫
              (derivedCompleteModuleCompletionAdjunction I hI).unit.app
                (colimit (F ⋙ derivedCompleteModuleInclusion I)) =
            colimit.ι (F ⋙ derivedCompleteModuleInclusion I) i ≫
              (derivedCompleteModuleCompletionAdjunction I hI).unit.app
                (colimit (F ⋙ derivedCompleteModuleInclusion I))
        rw [← Category.assoc, colimit.w] }

theorem derivedCompleteModuleColimitCocone_isColimit
    {A : Type u} [CommRing A] [HasDerivedCategory.{w} (Mod A)]
    (I : Ideal A) (hI : I.FG) {T : Type u} [Preorder T]
    (F : T ⥤ DerivedCompleteModuleCategory I) :
    Nonempty (IsColimit (derivedCompleteModuleColimitCocone I hI F)) := by
  sorry

theorem derivedCompleteModuleCategory_has_colimits
    {A : Type u} [CommRing A] [HasDerivedCategory.{w} (Mod A)]
    (I : Ideal A) (hI : I.FG) :
    HasColimits (DerivedCompleteModuleCategory I) := by
  sorry

/- The source warns that the inclusion need not commute with colimits in
 general.  The existence of such an example is kept as an explicit
 chapter-owned interface; the concrete example is discussed later in the
 book and cannot be imported here. -/
structure DerivedCompleteModuleColimitFailureData where
  A : Type u
  [commRing : CommRing A]
  [hasDerivedCategory : HasDerivedCategory.{w} (ModuleCat.{u} A)]
  I : Ideal A
  not_preserves :
    ¬ PreservesColimits (derivedCompleteModuleInclusion I)
  not_grothendieck :
    ¬ IsGrothendieckAbelian.{u} (DerivedCompleteModuleCategory I)

theorem exists_derivedCompleteModuleColimitFailureData :
    Nonempty DerivedCompleteModuleColimitFailureData := by
  sorry

/-! ## Chapter summary -/

structure DerivedCompleteModuleCategoryProperties
    {A : Type u} [CommRing A] [HasDerivedCategory.{w} (Mod A)] (I : Ideal A) :
    Type (u + 1) where
  abelian : Abelian (DerivedCompleteModuleCategory I)
  hasLimits : HasLimits (DerivedCompleteModuleCategory I)
  inclusion_preserves_limits : PreservesLimits (derivedCompleteModuleInclusion I)
  inclusion_exact :
    PreservesFiniteLimits (derivedCompleteModuleInclusion I) ∧
      PreservesFiniteColimits (derivedCompleteModuleInclusion I)
  finite_generation : I.FG →
    HasColimits (DerivedCompleteModuleCategory I) ∧
      ∃ L : Mod A ⥤ DerivedCompleteModuleCategory I,
        Nonempty (L ⊣ derivedCompleteModuleInclusion I)

theorem derivedCompleteModuleCategory_properties
    {A : Type u} [CommRing A] [HasDerivedCategory.{w} (Mod A)] (I : Ideal A) :
    Nonempty (DerivedCompleteModuleCategoryProperties I) := by
  sorry

end Formalization.Books.MoreAlgebra.Unit93
