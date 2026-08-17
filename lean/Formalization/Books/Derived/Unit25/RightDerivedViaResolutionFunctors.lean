import Formalization.Books.Derived.Unit20.InjectiveResolutions
import Formalization.Books.Derived.Unit23.ResolutionFunctors

/-!
# Derived Categories, Chapter 25: right derived functors via resolution functors

The source section identifies a right derived functor with the functor obtained
by applying the original functor to a functorial injective resolution.  Unit23
supplies the resolution package and its quasi-inverse; this file records the
resulting derived functor, its objectwise computation, and the exact lift before
localizing the target.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Preadditive
open CategoryTheory.Pretriangulated
open Formalization.Books.Derived.Unit08
open Formalization.Books.Derived.Unit10
open Formalization.Books.Derived.Unit11
open Formalization.Books.Derived.Unit20
open Formalization.Books.Derived.Unit23
open scoped CategoryTheory.Pretriangulated.Opposite ZeroObject

universe w w' v u v' u'

namespace Formalization.Books.Derived.Unit25

/-! ## The functor on complexes of injectives -/

/- The arrow labelled `F` in the source diagram is the termwise application of
   `F`, followed by passage to the bounded-below derived category of `B`. -/
noncomputable def resolutionFunctorDerivedTarget
    {A : Type u} [Category.{v} A] [Abelian A]
    {B : Type u'} [Category.{v'} B] [Abelian B]
    [HasDerivedCategory.{w'} B]
    (F : A ⥤ B) [F.Additive] :
    KPlus (Formalization.Books.Derived.Unit23.InjectiveSubcategory A) ⥤ DPlus B :=
  injectiveHomotopyInclusion (A := A) ⋙
    additiveHomotopyPlusFunctor F ⋙ plusDerivedLocalizationFunctor B

/-! ## The quasi-inverse and the derived functor -/

/- The functor `j'` from the source is the chosen witness supplied by the
   preceding chapter's quasi-inverse theorem. -/
noncomputable def resolutionFunctorQuasiInverse
    {A : Type u} [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A]
    (R : ResolutionFunctorData A) (P : ResolutionFunctorPackage R) :
    DPlus A ⥤ KPlus (Formalization.Books.Derived.Unit23.InjectiveSubcategory A) :=
  Classical.choose (resolution_functor_quasi_inverse P)

theorem resolutionFunctorQuasiInverse_spec
    {A : Type u} [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A]
    (R : ResolutionFunctorData A) (P : ResolutionFunctorPackage R) :
    plusDerivedLocalizationFunctor A ⋙ resolutionFunctorQuasiInverse R P = P.functor ∧
      QuasiInverseOf
        (injectiveToDerivedFunctor (A := A))
        (resolutionFunctorQuasiInverse R P) := by
  exact (Classical.choose_spec (resolution_functor_quasi_inverse P)).1

/- The diagonal arrow in the source diagram is the composite along its upper
   and right-hand sides. -/
noncomputable def rightDerivedFunctorViaResolution
    {A : Type u} [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A]
    {B : Type u'} [Category.{v'} B] [Abelian B]
    [HasDerivedCategory.{w'} B]
    (F : A ⥤ B) [F.Additive]
    (R : ResolutionFunctorData A) (P : ResolutionFunctorPackage R) :
    DPlus A ⥤ DPlus B :=
  resolutionFunctorQuasiInverse R P ⋙ resolutionFunctorDerivedTarget F

theorem rightDerivedFunctorViaResolution_two_commutes
    {A : Type u} [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A]
    {B : Type u'} [Category.{v'} B] [Abelian B]
    [HasDerivedCategory.{w'} B]
    (F : A ⥤ B) [F.Additive]
    (R : ResolutionFunctorData A) (P : ResolutionFunctorPackage R) :
    Nonempty
      (rightDerivedFunctorViaResolution F R P ≅
        resolutionFunctorQuasiInverse R P ⋙ resolutionFunctorDerivedTarget F) := by
  exact ⟨Iso.refl _⟩

/- The source's computation `RF(K) = F(j(K))`, expressed as the canonical
   objectwise isomorphism available from the chosen quasi-inverse. -/
theorem rightDerivedFunctorViaResolution_on_resolution
    {A : Type u} [Category.{v} A] [Abelian A]
    [EnoughInjectives A] [HasDerivedCategory.{w} A]
    {B : Type u'} [Category.{v'} B] [Abelian B]
    [HasDerivedCategory.{w'} B]
    (F : A ⥤ B) [F.Additive]
    (R : ResolutionFunctorData A) (P : ResolutionFunctorPackage R)
    (K : KPlus A) :
    Nonempty
      ((rightDerivedFunctorViaResolution F R P).obj
          ((plusDerivedLocalizationFunctor A).obj K) ≅
        (resolutionFunctorDerivedTarget F).obj (R.j K)) := by
  sorry

/- The defining property of the right derived functor: its unit is a left Kan
   extension along the bounded-below quasi-isomorphism localization. -/
theorem rightDerivedFunctorViaResolution_isRightDerived
    {A : Type u} [Category.{v} A] [Abelian A]
    [EnoughInjectives A] [HasDerivedCategory.{w} A]
    {B : Type u'} [Category.{v'} B] [Abelian B]
    [HasDerivedCategory.{w'} B]
    (F : A ⥤ B) [F.Additive]
    (R : ResolutionFunctorData A) (P : ResolutionFunctorPackage R) :
    ∃ α : rightDerivedSourceFunctor F ⟶
        plusDerivedLocalizationFunctor A ⋙
          rightDerivedFunctorViaResolution F R P,
      (rightDerivedFunctorViaResolution F R P).IsRightDerivedFunctor α
        (quasiIsoPlusProperty A) := by
  sorry

/-! ## The exact lift before localizing the target -/

/- The source's lifted functor `F ∘ j'` still lands in the bounded-below
   homotopy category, before applying the target localization. -/
noncomputable def resolutionFunctorExactLift
    {A : Type u} [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A]
    {B : Type u'} [Category.{v'} B] [Abelian B]
    (F : A ⥤ B) [F.Additive]
    (R : ResolutionFunctorData A) (P : ResolutionFunctorPackage R) :
    DPlus A ⥤ KPlus B :=
  resolutionFunctorQuasiInverse R P ⋙
    injectiveHomotopyInclusion (A := A) ⋙ additiveHomotopyPlusFunctor F

theorem resolutionFunctorExactLift_isExact
    {A : Type u} [Category.{v} A] [Abelian A]
    [EnoughInjectives A] [HasDerivedCategory.{w} A]
    {B : Type u'} [Category.{v'} B] [Abelian B]
    (F : A ⥤ B) [F.Additive]
    (R : ResolutionFunctorData A) (P : ResolutionFunctorPackage R) :
    Nonempty (ExactTriangulatedFunctorData (resolutionFunctorExactLift F R P)) := by
  sorry

end Formalization.Books.Derived.Unit25
