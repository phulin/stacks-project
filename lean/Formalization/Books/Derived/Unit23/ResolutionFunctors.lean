import Mathlib.CategoryTheory.Preadditive.Injective.InjectiveObject
import Formalization.Books.Derived.Unit10.DistinguishedTriangles
import Formalization.Books.Derived.Unit18.InjectiveResolutions

/-!
# Derived Categories, Chapter 23: resolution functors

The source identifies the bounded-below derived category of an abelian
category with the bounded-below homotopy category of injectives.  The
objectwise resolution data and its functorial upgrade are kept separate: the
first is the source's definition, while the second records the uniquely
compatible functor and natural isomorphism supplied by the comparison
property of injective complexes.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Preadditive
open CategoryTheory.Pretriangulated
open Formalization.Books.Derived.Unit08
open Formalization.Books.Derived.Unit10
open Formalization.Books.Derived.Unit11
open Formalization.Books.Homology.Unit03
open scoped CategoryTheory.Pretriangulated.Opposite ZeroObject

universe w v u

namespace Formalization.Books.Derived.Unit23

/-! ## The category of injectives and its derived comparison -/

/- Mathlib's `InjectiveObject` is the strictly full subcategory whose
   objects are the injectives of an abelian category. -/
abbrev InjectiveSubcategory
    (A : Type u) [Category.{v} A] [Abelian A] : Type u :=
  CategoryTheory.InjectiveObject A

noncomputable instance injectiveSubcategory_additiveCategory
    {A : Type u} [Category.{v} A] [Abelian A] :
    AdditiveCategory (InjectiveSubcategory A) :=
  { toPreadditive := inferInstance
    toHasFiniteProducts := inferInstance }

/- The inclusion of complexes of injectives into complexes of `A`, followed
   by the bounded-below homotopy quotient, is the canonical model of
   `K⁺(I) ⥤ K⁺(A)`. -/
noncomputable def injectiveHomotopyInclusion
    {A : Type u} [Category.{v} A] [Abelian A] :
    KPlus (InjectiveSubcategory A) ⥤ KPlus A :=
  additiveHomotopyPlusFunctor (CategoryTheory.InjectiveObject.ι A)

/- The source's canonical functor `K⁺(I) ⥤ D⁺(A)`. -/
noncomputable def injectiveToDerivedFunctor
    {A : Type u} [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A] :
    KPlus (InjectiveSubcategory A) ⥤ DPlus A :=
  injectiveHomotopyInclusion (A := A) ⋙ plusDerivedLocalizationFunctor A

/- The proposition in the source is recorded with the established exact
   functor package and Mathlib's equivalence class.  The latter supplies the
   fully faithful and essentially-surjective assertions. -/
theorem injective_homotopy_to_derived_equivalence
    {A : Type u} [Category.{v} A] [Abelian A]
    [EnoughInjectives A] [HasDerivedCategory.{w} A] :
    Nonempty (ExactTriangulatedFunctorData (injectiveToDerivedFunctor (A := A))) ∧
      Functor.IsEquivalence (injectiveToDerivedFunctor (A := A)) := by
  sorry

/-! ## Objectwise resolution data -/

/-- The source's objectwise resolution choice on `K⁺(A)`: every object is
represented by a bounded-below complex of injectives and a quasi-isomorphism
from the original object. -/
structure ResolutionFunctorData
    (A : Type u) [Category.{v} A] [Abelian A] where
  /-- The chosen bounded-below homotopy object of injectives. -/
  j : ∀ _K : KPlus A, KPlus (InjectiveSubcategory A)
  /-- The chosen quasi-isomorphism into the resolution. -/
  i : ∀ K : KPlus A,
    K ⟶ (injectiveHomotopyInclusion (A := A)).obj (j K)
  /-- The chosen map is a quasi-isomorphism in `K⁺(A)`. -/
  i_quasiIso : ∀ K : KPlus A, quasiIsoPlusProperty A (i K)

/- The image in `D⁺(A)` of the chosen map `i_K`. -/
noncomputable def resolutionDerivedComponent
    {A : Type u} [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A]
    (R : ResolutionFunctorData A) (K : KPlus A) :
    (plusDerivedLocalizationFunctor A).obj K ⟶
      (injectiveToDerivedFunctor (A := A)).obj (R.j K) :=
  (plusDerivedLocalizationFunctor A).map (R.i K)

/-! ## The uniquely compatible functorial upgrade -/

/-- A functorial upgrade of objectwise resolution data.

The component equation makes the natural isomorphism the one induced by the
chosen maps `i_K`, rather than an unrelated natural isomorphism. -/
structure ResolutionFunctorPackage
    {A : Type u} [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A]
    (R : ResolutionFunctorData A) where
  /-- The functor `K⁺(A) ⥤ K⁺(I)`. -/
  functor : KPlus A ⥤ KPlus (InjectiveSubcategory A)
  /-- Its object function is the chosen object function of `R`. -/
  objectwise : ∀ K : KPlus A, functor.obj K = R.j K
  /-- The square with `D⁺(A)` commutes up to the comparison isomorphism. -/
  comparison :
    plusDerivedLocalizationFunctor A ≅
      functor ⋙ injectiveToDerivedFunctor (A := A)
  /-- The comparison isomorphism is induced by `i_K` in each component. -/
  comparison_component : ∀ K : KPlus A,
    comparison.hom.app K =
      (plusDerivedLocalizationFunctor A).map (R.i K) ≫
        eqToHom (congrArg
          (fun X : KPlus (InjectiveSubcategory A) =>
            (injectiveToDerivedFunctor (A := A)).obj X)
          (objectwise K).symm)

theorem resolution_functor_package_exists
    {A : Type u} [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A]
    (R : ResolutionFunctorData A) :
    Nonempty (ResolutionFunctorPackage R) := by
  sorry

theorem resolution_functor_package_unique
    {A : Type u} [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A]
    (R : ResolutionFunctorData A) :
    Subsingleton (ResolutionFunctorPackage R) := by
  sorry

/- A comparison between packages with different objectwise choices.  The
   compatibility equation is the precise meaning of “canonical” in the
   source's size remark. -/
structure ResolutionFunctorIso
    {A : Type u} [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A]
    {R S : ResolutionFunctorData A}
    (P : ResolutionFunctorPackage R)
    (Q : ResolutionFunctorPackage S) where
  /-- The unique natural isomorphism between the two resolution functors. -/
  iso : P.functor ≅ Q.functor
  /-- It is compatible with the two comparison isomorphisms to `D⁺(A)`. -/
  comm :
    P.comparison.hom ≫
        Functor.whiskerRight iso.hom (injectiveToDerivedFunctor (A := A)) =
      Q.comparison.hom

theorem resolution_functor_iso_exists_unique
    {A : Type u} [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A]
    {R S : ResolutionFunctorData A}
    (P : ResolutionFunctorPackage R) (Q : ResolutionFunctorPackage S) :
    Nonempty (ResolutionFunctorIso P Q) ∧
      Subsingleton (ResolutionFunctorIso P Q) := by
  sorry

/-! ## Existence and exactness -/

theorem resolution_functor_data_exists
    {A : Type u} [Category.{v} A] [Abelian A] [EnoughInjectives A] :
    Nonempty (ResolutionFunctorData A) := by
  sorry

/- The source's existence statement: the objectwise choices can be upgraded
   to a functor and a compatible `2`-isomorphism. -/
theorem resolution_functor_exists
    {A : Type u} [Category.{v} A] [Abelian A]
    [EnoughInjectives A] [HasDerivedCategory.{w} A] :
    ∃ R : ResolutionFunctorData A, Nonempty (ResolutionFunctorPackage R) := by
  sorry

/- The source says that any resolution functor is exact.  The package from
   `Unit10` is exactly the shift-compatible triangulated-functor interface. -/
theorem resolution_functor_is_exact
    {A : Type u} [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A]
    {R : ResolutionFunctorData A}
    (P : ResolutionFunctorPackage R) :
    Nonempty (ExactTriangulatedFunctorData P.functor) := by
  sorry

/- A quasi-inverse is recorded by the two standard natural isomorphisms;
   this is the source's “quasi-inverse to the canonical functor” language. -/
def QuasiInverseOf
    {C D : Type*} [Category* C] [Category* D]
    (F : C ⥤ D) (G : D ⥤ C) : Prop :=
  Nonempty (𝟭 C ≅ F ⋙ G) ∧ Nonempty (G ⋙ F ≅ 𝟭 D)

theorem resolution_functor_quasi_inverse
    {A : Type u} [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A]
    {R : ResolutionFunctorData A}
    (P : ResolutionFunctorPackage R) :
    ∃! j' : DPlus A ⥤ KPlus (InjectiveSubcategory A),
      plusDerivedLocalizationFunctor A ⋙ j' = P.functor ∧
        QuasiInverseOf (injectiveToDerivedFunctor (A := A)) j' := by
  sorry

/-! ## The canonical comparison of two choices -/

/- This is the objectwise comparison used in the source's final remark. -/
theorem resolution_comparison_exists_unique
    {A : Type u} [Category.{v} A] [Abelian A]
    {K : KPlus A} {I J : KPlus (InjectiveSubcategory A)}
    (i : K ⟶ (injectiveHomotopyInclusion (A := A)).obj I)
    (i' : K ⟶ (injectiveHomotopyInclusion (A := A)).obj J)
    (hi : quasiIsoPlusProperty A i)
    (hi' : quasiIsoPlusProperty A i') :
    ∃! a : I ⟶ J,
      i ≫ (injectiveHomotopyInclusion (A := A)).map a = i' := by
  sorry

end Formalization.Books.Derived.Unit23
