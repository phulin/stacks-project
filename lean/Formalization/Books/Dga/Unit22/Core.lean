import Formalization.Books.Dga.Unit21.IResolutions
import Formalization.Books.Derived.Unit06.Quotients

/-!
# Differential Graded Algebra, Chapter 22: the derived category

The preceding DGA chapters provide the differential graded modules, their
cohomology, and P- and I-resolutions.  They do not yet package the homotopy
category for the external graded-algebra presentation as a categorical
object.  `DgHomotopyCategoryModel` is the small bridge needed here: it keeps
the homotopy category, its quotient functor, the acyclic objects, the
quasi-isomorphisms, and the degree-zero cohomology functor explicit.  Once
that earlier interface is supplied, the derived category itself is
Mathlib's canonical localization.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open Formalization.Books.Dga.Unit14
open Formalization.Books.Dga.Unit20
open Formalization.Books.Dga.Unit21
open Formalization.Books.Categories.Unit27
open Formalization.Books.Derived.Unit06
open Formalization.Books.Homology.Unit03
open CategoryTheory.Pretriangulated
open CategoryTheory.Triangulated

universe u v w wk vk wi vc ve

namespace Formalization.Books.Dga.Unit22

variable {R : Type u} {A : ℤ → Type v}
  [CommRing R]
  [∀ i, AddCommGroup (A i)] [∀ i, Module R (A i)]
  [DirectSum.GSemiring A] [DirectSum.GAlgebra R A]

abbrev DGModule
    (D : DifferentialGradedAlgebraData R A) :=
  Unit21.DGModule D

abbrev DGMap
    {D : DifferentialGradedAlgebraData R A}
    (M N : DGModule D) := Unit21.DGMap M N

abbrev DgPResolution
    {D : DifferentialGradedAlgebraData R A}
    (M : DGModule D) := Unit20.PResolution M

abbrev DgIResolution
    {D : DifferentialGradedAlgebraData R A}
    (M : DGModule D) := Unit21.RightResolution M

abbrev DgAcyclic
    {D : DifferentialGradedAlgebraData R A}
    (M : DGModule D) : Prop :=
  Unit21.IsAcyclic M

abbrev DgQuasiIsomorphism
    {D : DifferentialGradedAlgebraData R A}
    {M N : DGModule D} (f : DGMap M N) : Prop :=
  Unit20.DgQuasiIsomorphism f

/-! ## The homotopy-category input -/

structure DgHomotopyCategoryModel
    (D : DifferentialGradedAlgebraData R A)
    (K : Type wk) [Category.{vk} K] [AdditiveCategory K]
    [HasShift K ℤ] [∀ n : ℤ, (shiftFunctor K n).Additive]
    [Pretriangulated K] where
  quotient : DifferentialGradedModuleCategory.{u, v, w} D ⥤ K
  acyclic : ObjectProperty K
  quasiIsomorphisms : MorphismProperty K
  cohomologyZero : K ⥤ ModuleCat.{u} R
  cohomologyZero_homological : cohomologyZero.IsHomological
  acyclic_eq_homologicalKernel :
    acyclic = homologicalFunctorKernel cohomologyZero
  acyclic_iff : ∀ M : DGModule.{u, v, w} D,
    acyclic (quotient.obj M) ↔ DgAcyclic M
  quasiIsomorphism_iff : ∀ {M N : DGModule.{u, v, w} D}
    (f : DGMap M N),
    quasiIsomorphisms (quotient.map f) ↔ DgQuasiIsomorphism f

abbrev DgHomotopyCategory
    {D : DifferentialGradedAlgebraData R A}
    {K : Type wk} [Category.{vk} K] [AdditiveCategory K]
    [HasShift K ℤ] [∀ n : ℤ, (shiftFunctor K n).Additive]
    [Pretriangulated K]
    (_ : DgHomotopyCategoryModel D K) := K

abbrev dgHomotopyQuotient
    {D : DifferentialGradedAlgebraData R A}
    {K : Type wk} [Category.{vk} K] [AdditiveCategory K]
    [HasShift K ℤ] [∀ n : ℤ, (shiftFunctor K n).Additive]
    [Pretriangulated K]
    (H : DgHomotopyCategoryModel D K) := H.quotient

abbrev dgAcyclicSubcategory
    {D : DifferentialGradedAlgebraData R A}
    {K : Type wk} [Category.{vk} K] [AdditiveCategory K]
    [HasShift K ℤ] [∀ n : ℤ, (shiftFunctor K n).Additive]
    [Pretriangulated K]
    (H : DgHomotopyCategoryModel D K) : ObjectProperty K :=
  H.acyclic

abbrev dgQuasiIsomorphisms
    {D : DifferentialGradedAlgebraData R A}
    {K : Type wk} [Category.{vk} K] [AdditiveCategory K]
    [HasShift K ℤ] [∀ n : ℤ, (shiftFunctor K n).Additive]
    [Pretriangulated K]
    (H : DgHomotopyCategoryModel D K) : MorphismProperty K :=
  H.quasiIsomorphisms

/-! ## Acyclics and the localization -/

abbrev DgAcyclicSubcategoryProperties
    {D : DifferentialGradedAlgebraData R A}
    {K : Type wk} [Category.{vk} K] [AdditiveCategory K]
    [HasShift K ℤ] [∀ n : ℤ, (shiftFunctor K n).Additive]
    [Pretriangulated K]
    (H : DgHomotopyCategoryModel D K) : Prop :=
  IsStrictlyFullSaturatedPretriangulated H.acyclic

theorem acyclic_subcategory_properties
    {D : DifferentialGradedAlgebraData R A}
    {K : Type wk} [Category.{vk} K] [AdditiveCategory K]
    [HasShift K ℤ] [∀ n : ℤ, (shiftFunctor K n).Additive]
    [Pretriangulated K]
    (H : DgHomotopyCategoryModel D K) :
  DgAcyclicSubcategoryProperties H := by
  letI : H.cohomologyZero.IsHomological := H.cohomologyZero_homological
  change IsStrictlyFullSaturatedPretriangulated H.acyclic
  rw [H.acyclic_eq_homologicalKernel]
  exact homologicalFunctorKernel_properties H.cohomologyZero

theorem quasi_isomorphisms_saturated_and_compatible
    {D : DifferentialGradedAlgebraData R A}
    {K : Type wk} [Category.{vk} K] [AdditiveCategory K]
    [HasShift K ℤ] [∀ n : ℤ, (shiftFunctor K n).Additive]
    [Pretriangulated K]
    (H : DgHomotopyCategoryModel D K) :
    SaturatedMultiplicativeSystem H.quasiIsomorphisms ∧
      MorphismProperty.IsCompatibleWithTriangulation H.quasiIsomorphisms := by
  sorry

abbrev DgDerivedCategory
    {D : DifferentialGradedAlgebraData R A}
    {K : Type wk} [Category.{vk} K] [AdditiveCategory K]
    [HasShift K ℤ] [∀ n : ℤ, (shiftFunctor K n).Additive]
    [Pretriangulated K]
    (H : DgHomotopyCategoryModel D K) :=
  H.quasiIsomorphisms.Localization

noncomputable abbrev dgDerivedLocalization
    {D : DifferentialGradedAlgebraData R A}
    {K : Type wk} [Category.{vk} K] [AdditiveCategory K]
    [HasShift K ℤ] [∀ n : ℤ, (shiftFunctor K n).Additive]
    [Pretriangulated K]
    (H : DgHomotopyCategoryModel D K) :
    K ⥤ DgDerivedCategory H :=
  H.quasiIsomorphisms.Q

abbrev dgAcyclicLocalization
    {D : DifferentialGradedAlgebraData R A}
    {K : Type wk} [Category.{vk} K] [AdditiveCategory K]
    [HasShift K ℤ] [∀ n : ℤ, (shiftFunctor K n).Additive]
    [Pretriangulated K]
    (H : DgHomotopyCategoryModel D K) :=
  H.acyclic.trW.Localization

theorem derived_category_is_acyclic_localization
    {D : DifferentialGradedAlgebraData R A}
    {K : Type wk} [Category.{vk} K] [AdditiveCategory K]
    [HasShift K ℤ] [∀ n : ℤ, (shiftFunctor K n).Additive]
    [Pretriangulated K]
    (H : DgHomotopyCategoryModel D K) :
    Nonempty (DgDerivedCategory H ≌ dgAcyclicLocalization H) := by
  sorry

structure DgDerivedCategoryTriangulatedData
    {D : DifferentialGradedAlgebraData R A}
    {K : Type wk} [Category.{vk} K] [AdditiveCategory K]
    [HasShift K ℤ] [∀ n : ℤ, (shiftFunctor K n).Additive]
    [Pretriangulated K]
    (H : DgHomotopyCategoryModel D K) where
  [preadditive : Preadditive (DgDerivedCategory H)]
  [hasZeroObject : HasZeroObject (DgDerivedCategory H)]
  [hasShift : HasShift (DgDerivedCategory H) ℤ]
  [shiftAdditive : ∀ n : ℤ, (shiftFunctor (DgDerivedCategory H) n).Additive]
  [pretriangulated : Pretriangulated (DgDerivedCategory H)]
  triangulated : CategoryTheory.IsTriangulated (DgDerivedCategory H)

theorem derived_category_is_triangulated
    {D : DifferentialGradedAlgebraData R A}
    {K : Type wk} [Category.{vk} K] [AdditiveCategory K]
    [HasShift K ℤ] [∀ n : ℤ, (shiftFunctor K n).Additive]
    [Pretriangulated K]
    (H : DgHomotopyCategoryModel D K) :
    Nonempty (DgDerivedCategoryTriangulatedData H) := by
  sorry

abbrev dgDerivedKernel
    {D : DifferentialGradedAlgebraData R A}
    {K : Type wk} [Category.{vk} K] [AdditiveCategory K]
    [HasShift K ℤ] [∀ n : ℤ, (shiftFunctor K n).Additive]
    [Pretriangulated K]
    (H : DgHomotopyCategoryModel D K) : ObjectProperty K :=
  fun X => IsZero ((dgDerivedLocalization H).obj X)

theorem derived_localization_kernel
    {D : DifferentialGradedAlgebraData R A}
    {K : Type wk} [Category.{vk} K] [AdditiveCategory K]
    [HasShift K ℤ] [∀ n : ℤ, (shiftFunctor K n).Additive]
    [Pretriangulated K]
    (H : DgHomotopyCategoryModel D K) :
    dgDerivedKernel H = H.acyclic := by
  sorry

structure DgDerivedCohomologyFactor
    {D : DifferentialGradedAlgebraData R A}
    {K : Type wk} [Category.{vk} K] [AdditiveCategory K]
    [HasShift K ℤ] [∀ n : ℤ, (shiftFunctor K n).Additive]
    [Pretriangulated K]
    (H : DgHomotopyCategoryModel D K) where
  factor : DgDerivedCategory H ⥤ ModuleCat.{u} R
  factorization : dgDerivedLocalization H ⋙ factor = H.cohomologyZero
  unique : ∀ (G : DgDerivedCategory H ⥤ ModuleCat.{u} R),
    dgDerivedLocalization H ⋙ G = H.cohomologyZero → G = factor

theorem derived_homology_zero_factors
    {D : DifferentialGradedAlgebraData R A}
    {K : Type wk} [Category.{vk} K] [AdditiveCategory K]
    [HasShift K ℤ] [∀ n : ℤ, (shiftFunctor K n).Additive]
    [Pretriangulated K]
    (H : DgHomotopyCategoryModel D K) :
    Nonempty (DgDerivedCohomologyFactor H) := by
  sorry

/-! ## Morphisms computed by resolutions -/

theorem derived_hom_via_PResolution
    {D : DifferentialGradedAlgebraData R A}
    {K : Type wk} [Category.{vk} K] [AdditiveCategory K]
    [HasShift K ℤ] [∀ n : ℤ, (shiftFunctor K n).Additive]
    [Pretriangulated K]
    (H : DgHomotopyCategoryModel D K)
    {M N : DGModule D} (P : DgPResolution M) :
    Nonempty
      ((H.quotient.obj P.object ⟶ H.quotient.obj N) ≃
        ((dgDerivedLocalization H).obj (H.quotient.obj M) ⟶
          (dgDerivedLocalization H).obj (H.quotient.obj N))) := by
  sorry

theorem derived_hom_via_IResolution
    {D : DifferentialGradedAlgebraData R A}
    {K : Type wk} [Category.{vk} K] [AdditiveCategory K]
    [HasShift K ℤ] [∀ n : ℤ, (shiftFunctor K n).Additive]
    [Pretriangulated K]
    (H : DgHomotopyCategoryModel D K)
    {M N : DGModule D} (I : DgIResolution N) :
    Nonempty
      ((H.quotient.obj M ⟶ H.quotient.obj I.totalization.object) ≃
        ((dgDerivedLocalization H).obj (H.quotient.obj M) ⟶
          (dgDerivedLocalization H).obj (H.quotient.obj N))) := by
  sorry

/-! ## Direct sums and products -/

structure DgDerivedProductsData
    {D : DifferentialGradedAlgebraData R A}
    {K : Type wk} [Category.{vk} K] [AdditiveCategory K]
    [HasShift K ℤ] [∀ n : ℤ, (shiftFunctor K n).Additive]
    [Pretriangulated K]
    (H : DgHomotopyCategoryModel D K) where
  directSum : ∀ {ι : Type wi} (F : ι → DGModule.{u, v, w} D),
    DgDirectSum.{u, v, w, wi, w} D F
  product : ∀ {ι : Type wi} (F : ι → DGModule.{u, v, w} D), DgProduct D F
  directSum_hom_equiv : ∀ {ι : Type wi} (F : ι → DGModule.{u, v, w} D)
    (Y : DgDerivedCategory H),
    Nonempty
      (((dgDerivedLocalization H).obj ((H.quotient).obj (directSum F).object) ⟶ Y) ≃
        (∀ i, (dgDerivedLocalization H).obj ((H.quotient).obj (F i)) ⟶ Y))
  product_hom_equiv : ∀ {ι : Type wi} (F : ι → DGModule.{u, v, w} D)
    (Y : DgDerivedCategory H),
    Nonempty
      ((Y ⟶ (dgDerivedLocalization H).obj ((H.quotient).obj (product F).object)) ≃
        (∀ i, Y ⟶ (dgDerivedLocalization H).obj ((H.quotient).obj (F i))))

theorem derived_products
    {D : DifferentialGradedAlgebraData R A}
    {K : Type wk} [Category.{vk} K] [AdditiveCategory K]
    [HasShift K ℤ] [∀ n : ℤ, (shiftFunctor K n).Additive]
    [Pretriangulated K]
    (H : DgHomotopyCategoryModel D K) :
    Nonempty (DgDerivedProductsData H) := by
  sorry

/-! The size warning in the source is represented by a tower of bounded
   universe-level models.  Its `exhaustive` field says that the ambient
   derived category is the union of the restricted pieces up to isomorphism,
   while `transition_fully_faithful` records the key Hom-set assertion. -/

structure DgDerivedCategorySizeData
    {D : DifferentialGradedAlgebraData R A}
    {K : Type wk} [Category.{vk} K] [AdditiveCategory K]
    [HasShift K ℤ] [∀ n : ℤ, (shiftFunctor K n).Additive]
    [Pretriangulated K]
    (H : DgHomotopyCategoryModel D K)
    (I : Type wi) [Preorder I]
    (C : I → Type wk) [∀ i, Category.{vc} (C i)]
    (E : Type wk) [Category.{ve} E] where
  transition : ∀ (i j : I), i ≤ j → C i ⥤ C j
  transition_fully_faithful : ∀ (i j : I) (h : i ≤ j),
    (transition i j h).FullyFaithful
  inclusion : ∀ i, C i ⥤ E
  inclusion_compatible : ∀ (i j : I) (h : i ≤ j),
    inclusion i ≅ transition i j h ⋙ inclusion j
  exhaustive : ∀ X : E, ∃ (i : I) (Y : C i),
    Nonempty ((inclusion i).obj Y ≅ X)

theorem size_tower_transition_fully_faithful
    {D : DifferentialGradedAlgebraData R A}
    {K : Type wk} [Category.{vk} K] [AdditiveCategory K]
    [HasShift K ℤ] [∀ n : ℤ, (shiftFunctor K n).Additive]
    [Pretriangulated K]
    (H : DgHomotopyCategoryModel D K)
    {I : Type wi} [Preorder I]
    {C : I → Type wk} [∀ i, Category.{vc} (C i)]
    {E : Type wk} [Category.{ve} E]
    (S : DgDerivedCategorySizeData H I C E) (i j : I) (h : i ≤ j) :
    Nonempty (S.transition i j h).FullyFaithful :=
  ⟨S.transition_fully_faithful i j h⟩

/-! ## The P-resolution generation remark -/

def DgDerivedProperty
    {D : DifferentialGradedAlgebraData R A}
    {K : Type wk} [Category.{vk} K] [AdditiveCategory K]
    [HasShift K ℤ] [∀ n : ℤ, (shiftFunctor K n).Additive]
    [Pretriangulated K]
    (H : DgHomotopyCategoryModel D K) :=
  DgDerivedCategory H → Prop

def DgDerivedTwoOfThreeClosed
    {D : DifferentialGradedAlgebraData R A}
    {K : Type wk} [Category.{vk} K] [AdditiveCategory K]
    [HasShift K ℤ] [∀ n : ℤ, (shiftFunctor K n).Additive]
    [Pretriangulated K]
    (H : DgHomotopyCategoryModel D K)
    [Preadditive (DgDerivedCategory H)]
    [HasZeroObject (DgDerivedCategory H)]
    [HasShift (DgDerivedCategory H) ℤ]
    [∀ n : ℤ, (shiftFunctor (DgDerivedCategory H) n).Additive]
    [Pretriangulated (DgDerivedCategory H)]
    (T : DgDerivedProperty H) : Prop :=
  ∀ (triangle : Triangle (DgDerivedCategory H)),
    triangle ∈ distTriang (DgDerivedCategory H) →
    (T triangle.obj₁ ∧ T triangle.obj₂ → T triangle.obj₃) ∧
    (T triangle.obj₁ ∧ T triangle.obj₃ → T triangle.obj₂) ∧
    (T triangle.obj₂ ∧ T triangle.obj₃ → T triangle.obj₁)

noncomputable def dgDerivedRegularShift
    {D : DifferentialGradedAlgebraData R A}
    {K : Type wk} [Category.{vk} K] [AdditiveCategory K]
    [HasShift K ℤ] [∀ n : ℤ, (shiftFunctor K n).Additive]
    [Pretriangulated K]
  (H : DgHomotopyCategoryModel D K) (k : ℤ) : DgDerivedCategory H :=
  (dgDerivedLocalization H).obj
    ((H.quotient).obj (differentialGradedAlgebraShift D k))

theorem property_holds_for_all_derived_objects
    {D : DifferentialGradedAlgebraData R A}
    {K : Type wk} [Category.{vk} K] [AdditiveCategory K]
    [HasShift K ℤ] [∀ n : ℤ, (shiftFunctor K n).Additive]
    [Pretriangulated K]
    (H : DgHomotopyCategoryModel D K)
    [Preadditive (DgDerivedCategory H)]
    [HasZeroObject (DgDerivedCategory H)]
    [HasShift (DgDerivedCategory H) ℤ]
    [∀ n : ℤ, (shiftFunctor (DgDerivedCategory H) n).Additive]
    [Pretriangulated (DgDerivedCategory H)]
    [HasCoproducts (DgDerivedCategory H)]
    (T : DgDerivedProperty H)
    (hTsum : ∀ {ι : Type wi} (X : ι → DgDerivedCategory H),
      (∀ i, T (X i)) → T (colimit (Discrete.functor X)))
    (hTtriangle : DgDerivedTwoOfThreeClosed H T)
    (hTshift : ∀ k : ℤ, T (dgDerivedRegularShift H k)) :
    ∀ X : DgDerivedCategory H, T X := by
  sorry

end Formalization.Books.Dga.Unit22
