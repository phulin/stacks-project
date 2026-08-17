import Formalization.Books.Derived.Unit05.Localization

/-!
# Derived Categories, Chapter 6: quotients of triangulated categories

The source's Verdier quotient is expressed with Mathlib's canonical
ObjectProperty.trW morphism property and the localization construction.
The declarations in this file keep the source's kernels, saturation
conditions, and universal properties visible without duplicating the
underlying categorical infrastructure.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Preadditive
open CategoryTheory.Pretriangulated
open Formalization.Books.Categories.Unit27
open Formalization.Books.Derived.Unit03
open Formalization.Books.Derived.Unit05
open Formalization.Books.Homology.Unit03
open scoped CategoryTheory.Pretriangulated.Opposite ZeroObject

universe v u

namespace Formalization.Books.Derived.Unit06

/-! ## Saturated subcategories -/

section SaturatedSubcategories

variable {C : Type u} [Category.{v} C] [AdditiveCategory C]
  [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C]

/- The source's phrase "isomorphic to an object of the subcategory" is
   represented by ObjectProperty.isoClosure, the canonical strictly-full
   closure operation. -/

/-- A full pretriangulated subcategory is saturated when it is closed under
direct summands, expressed through binary biproducts and isomorphism closure. -/
def IsSaturated (P : ObjectProperty C) : Prop :=
  ∀ ⦃X Y : C⦄, P.isoClosure (X ⊞ Y) →
    P.isoClosure X ∧ P.isoClosure Y

/-- The source's epaissse condition: in a distinguished triangle, if the
second and third objects belong to the subcategory up to isomorphism, then
so do the first and second objects. -/
def IsEpaissse (P : ObjectProperty C) : Prop :=
  ∀ ⦃X S Y T : C⦄ (a : X ⟶ S) (b : X ⟶ Y) (c : S ⟶ Y)
    (d : Y ⟶ T) (e : T ⟶ X⟦(1 : ℤ)⟧),
    a ≫ c = b → Triangle.mk b d e ∈ distTriang C →
    P.isoClosure S → P.isoClosure T →
    P.isoClosure X ∧ P.isoClosure Y

/- The source's strict-full saturated pretriangulated-subcategory package.
   When the ambient category is triangulated, the earlier
   `Derived.Unit03.TriangulatedSubcategory` interface supplies the remaining
   triangulated-subcategory assertion. -/
def IsStrictlyFullSaturatedPretriangulated (P : ObjectProperty C) : Prop :=
  P.IsClosedUnderIsomorphisms ∧ P.IsTriangulated ∧ IsSaturated P

/-- Saturation and the source's epaissse condition are equivalent. -/
theorem isSaturated_iff_isEpaissse (P : ObjectProperty C)
    [P.IsTriangulated] :
    IsSaturated P ↔ IsEpaissse P := by
  sorry

end SaturatedSubcategories

/-! ## Kernels of exact and homological functors -/

section ExactFunctorKernels

variable {C D : Type*} [Category* C] [Category* D]
  [AdditiveCategory C] [AdditiveCategory D]
  [HasShift C ℤ] [HasShift D ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive]
  [∀ n : ℤ, (shiftFunctor D n).Additive]
  [Pretriangulated C] [Pretriangulated D]

/-- The object property underlying the kernel of an exact functor. -/
def exactFunctorKernel (F : C ⥤ D) : ObjectProperty C :=
  fun X => IsZero (F.obj X)

/-- The kernel of an exact functor is strictly full, saturated, and
pretriangulated. -/
theorem exactFunctorKernel_properties
    (F : C ⥤ D) [F.CommShift ℤ] [F.IsTriangulated] :
    IsStrictlyFullSaturatedPretriangulated (exactFunctorKernel F) := by
  sorry

end ExactFunctorKernels

section HomologicalFunctorKernels

variable {C A : Type*} [Category* C] [Category* A]
  [AdditiveCategory C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C] [Abelian A]

/-- The canonical Mathlib kernel of a homological functor is the source's
subcategory on which every shifted value vanishes. -/
abbrev homologicalFunctorKernel (H : C ⥤ A) : ObjectProperty C :=
  H.homologicalKernel

/-- The kernel of a homological functor is strictly full, saturated, and
pretriangulated. -/
theorem homologicalFunctorKernel_properties
    (H : C ⥤ A) [H.IsHomological] :
    IsStrictlyFullSaturatedPretriangulated (homologicalFunctorKernel H) := by
  sorry

/-- Objects whose homology vanishes in all sufficiently negative degrees. -/
def homologicalKernelBelow (H : C ⥤ A) : ObjectProperty C :=
  fun X => ∃ N : ℤ, ∀ n : ℤ, n ≤ N → IsZero ((homologicalDegree H n).obj X)

/-- Objects whose homology vanishes in all sufficiently positive degrees. -/
def homologicalKernelAbove (H : C ⥤ A) : ObjectProperty C :=
  fun X => ∃ N : ℤ, ∀ n : ℤ, N ≤ n → IsZero ((homologicalDegree H n).obj X)

/-- Objects whose homology vanishes outside a bounded range. -/
def homologicalKernelBounded (H : C ⥤ A) : ObjectProperty C :=
  homologicalKernelBelow H ⊓ homologicalKernelAbove H

/-- The three boundedness kernels are strictly full, saturated, and
pretriangulated. -/
theorem homologicalKernel_bounded_properties
    (H : C ⥤ A) [H.IsHomological] :
    IsStrictlyFullSaturatedPretriangulated (homologicalKernelBelow H) ∧
      IsStrictlyFullSaturatedPretriangulated (homologicalKernelAbove H) ∧
      IsStrictlyFullSaturatedPretriangulated (homologicalKernelBounded H) := by
  sorry

end HomologicalFunctorKernels

/-! ## The kernel-category notation -/

section KernelCategory

variable {C D A : Type*} [Category* C] [Category* D] [Category* A]
  [AdditiveCategory C] [AdditiveCategory D]
  [HasShift C ℤ] [HasShift D ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive]
  [∀ n : ℤ, (shiftFunctor D n).Additive]
  [Pretriangulated C] [Pretriangulated D] [Abelian A]

/- The source's Ker(F) and Ker(H) are represented by the two canonical
object properties above: exactFunctorKernel F and
homologicalFunctorKernel H. -/

abbrev kernelOfExactFunctor (F : C ⥤ D) : ObjectProperty C :=
  exactFunctorKernel F

abbrev kernelOfHomologicalFunctor (H : C ⥤ A) : ObjectProperty C :=
  homologicalFunctorKernel H

end KernelCategory

/-! ## The cone morphism property and its saturation -/

section MultiplicativeSystem

variable {C : Type u} [Category.{v} C] [AdditiveCategory C]
  [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C]

/-- The source's multiplicative system attached to a subcategory, using
Mathlib's canonical cone-morphism property and the source's isomorphism
closure convention. -/
abbrev quotientMorphismProperty (P : ObjectProperty C) : MorphismProperty C :=
  P.isoClosure.trW

/-- Membership in the quotient morphism property is exactly the existence of
a distinguished triangle whose third object lies in the subcategory up to
isomorphism. -/
theorem quotientMorphismProperty_iff (P : ObjectProperty C)
    {X Y : C} (f : X ⟶ Y) :
    quotientMorphismProperty P f ↔
      ∃ (Z : C) (g : Y ⟶ Z) (h : Z ⟶ X⟦(1 : ℤ)⟧)
        (_ : Triangle.mk f g h ∈ distTriang C), P.isoClosure Z := by
  rfl

/-- The quotient morphism property is a compatible multiplicative system for
a full triangulated subcategory. -/
theorem quotientMorphismProperty_isMultiplicative
    (P : ObjectProperty C) [CategoryTheory.IsTriangulated C]
    [P.IsTriangulated] :
    MultiplicativeSystem (quotientMorphismProperty P) ∧
      CompatibleWithTriangulation (quotientMorphismProperty P) := by
  exact ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩

/-- Saturation of the cone-morphism system is equivalent to saturation of the
underlying triangulated subcategory. -/
theorem quotientMorphismProperty_isSaturated_iff
    (P : ObjectProperty C) [CategoryTheory.IsTriangulated C]
    [P.IsTriangulated] :
    SaturatedMultiplicativeSystem (quotientMorphismProperty P) ↔
      IsSaturated P := by
  sorry

end MultiplicativeSystem

/-! ## The Verdier quotient and its universal property -/

section QuotientCategory

variable {C : Type u} [Category.{v} C] [AdditiveCategory C]
  [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C]

/-- The quotient category by the full subcategory represented by P. -/
abbrev quotientCategory (P : ObjectProperty C) : Type _ :=
  (quotientMorphismProperty P).Localization

/-- The quotient functor into the Verdier quotient. -/
abbrev quotientFunctor (P : ObjectProperty C) : C ⥤ quotientCategory P :=
  (quotientMorphismProperty P).Q

/-- The quotient functor is exact. -/
theorem quotientFunctor_isExact (P : ObjectProperty C)
    [CategoryTheory.IsTriangulated C] [P.IsTriangulated] :
    (quotientFunctor P).IsTriangulated := by
  infer_instance

/-- A functor which inverts the quotient morphisms factors through the
quotient category. -/
noncomputable def quotientFactor {E : Type*} [Category* E]
    (P : ObjectProperty C) (F : C ⥤ E)
    (hF : (quotientMorphismProperty P).IsInvertedBy F) :
    quotientCategory P ⥤ E :=
  Localization.Construction.lift F hF

/-- The factorization supplied by the localization construction composes
with the quotient functor to the original functor. -/
theorem quotientFactor_fac {E : Type*} [Category* E]
    (P : ObjectProperty C) (F : C ⥤ E)
    (hF : (quotientMorphismProperty P).IsInvertedBy F) :
    quotientFunctor P ⋙ quotientFactor P F hF = F :=
  Localization.Construction.fac F hF

/-- The factorization through the quotient is unique as a functor. -/
theorem quotientFactor_unique {E : Type*} [Category* E]
    (P : ObjectProperty C) (F₁ F₂ : quotientCategory P ⥤ E)
    (h : quotientFunctor P ⋙ F₁ = quotientFunctor P ⋙ F₂) : F₁ = F₂ :=
  Localization.Construction.uniq F₁ F₂ h

/-- The Verdier quotient has the source's universal property for homological
functors and exact functors. -/
theorem quotient_universal_property
    {A D : Type*} [Category* A] [Category* D]
    [Abelian A] [AdditiveCategory D]
    [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive]
    [Pretriangulated D]
    (P : ObjectProperty C) [CategoryTheory.IsTriangulated C]
    [P.IsTriangulated]
    (H : C ⥤ A) [H.IsHomological]
    (hH : P ≤ homologicalFunctorKernel H) :
    ∃! H' : quotientCategory P ⥤ A,
      quotientFunctor P ⋙ H' = H ∧ H'.IsHomological := by
  sorry

theorem quotient_universal_property_exact
    {D : Type*} [Category* D] [Preadditive D] [HasZeroObject D]
    [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive]
    [Pretriangulated D]
    (P : ObjectProperty C) [CategoryTheory.IsTriangulated C]
    [P.IsTriangulated]
    (F : C ⥤ D) [F.CommShift ℤ] [F.IsTriangulated]
    (hF : P ≤ exactFunctorKernel F) :
    ∃! F' : quotientCategory P ⥤ D,
      quotientFunctor P ⋙ F' = F ∧
        IsExactLocalizationFactor
          (S := quotientMorphismProperty P) F' := by
  sorry

end QuotientCategory

/-! ## The kernel of the quotient functor -/

section QuotientKernel

variable {C : Type u} [Category.{v} C] [AdditiveCategory C]
  [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C]

/-- The source's explicit object property for the kernel of the quotient
functor: objects which become a direct summand of an object of P. -/
def quotientKernel (P : ObjectProperty C) : ObjectProperty C :=
  fun Z => ∃ Z' : C, P.isoClosure (Z ⊞ Z')

/-- The explicit object description of the quotient kernel. -/
theorem quotientFunctor_kernel_iff (P : ObjectProperty C)
    [CategoryTheory.IsTriangulated C] [P.IsTriangulated]
    (Z : C) :
    exactFunctorKernel (quotientFunctor P) Z ↔ quotientKernel P Z := by
  sorry

/-- The quotient kernel is the smallest strictly full saturated triangulated
subcategory containing the subcategory being quotiented out. -/
theorem quotientKernel_is_smallest (P : ObjectProperty C)
    [CategoryTheory.IsTriangulated C] [P.IsTriangulated] :
    IsStrictlyFullSaturatedPretriangulated (quotientKernel P) ∧
      P ≤ quotientKernel P ∧
      ∀ Q : ObjectProperty C,
        Q.IsClosedUnderIsomorphisms → Q.IsTriangulated → IsSaturated Q →
        quotientKernel P ≤ Q := by
  sorry

end QuotientKernel

/-! ## Operations on multiplicative systems and subcategories -/

section Operations

variable {C : Type u} [Category.{v} C] [AdditiveCategory C]
  [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C]

/-- The subcategory B(S) = Ker(Q) attached to a localization system. -/
abbrev localizationKernel (S : MorphismProperty C) : ObjectProperty C :=
  IsZeroAfterLocalization S

/-- The operation from full triangulated subcategories to cone-morphism
properties. -/
abbrev subcategoryOperation (P : ObjectProperty C) : MorphismProperty C :=
  quotientMorphismProperty P

/-- The operation from a morphism property to the arrows inverted by its
localization. -/
abbrev localizationOperation (S : MorphismProperty C) : MorphismProperty C :=
  invertedByLocalization S

/-- The two operations are order preserving. -/
theorem operations_monotone_subcategory
    {P Q : ObjectProperty C} (hPQ : P ≤ Q) :
    subcategoryOperation P ≤ subcategoryOperation Q := by
  unfold subcategoryOperation quotientMorphismProperty
  exact ObjectProperty.trW_monotone (ObjectProperty.monotone_isoClosure hPQ)

theorem operations_monotone_localization
    {S T : MorphismProperty C} [CategoryTheory.IsTriangulated C]
    [CompatibleWithTriangulation S] [CompatibleWithTriangulation T]
    (hS : MultiplicativeSystem S) (hT : MultiplicativeSystem T)
    (hST : S ≤ T) :
    localizationKernel S ≤ localizationKernel T := by
  sorry

/-- The first composite is the saturation of a multiplicative system. -/
theorem operations_morphismProperty_saturation
    {S : MorphismProperty C} [CategoryTheory.IsTriangulated C]
    [CompatibleWithTriangulation S] (hS : MultiplicativeSystem S) :
    subcategoryOperation (localizationKernel S) = saturationClosure S := by
  sorry

end Operations

section SaturationClosure

variable {C : Type u} [Category.{v} C]

/-- The saturation closure is the smallest saturated multiplicative system
containing the original one. -/
theorem operations_morphismProperty_saturation_smallest
    {S : MorphismProperty C} (hS : MultiplicativeSystem S) :
    S ≤ saturationClosure S ∧
      SaturatedMultiplicativeSystem (saturationClosure S) ∧
      ∀ V : MorphismProperty C, SaturatedMultiplicativeSystem V → S ≤ V →
        saturationClosure S ≤ V :=
  saturationClosure_is_smallest hS

end SaturationClosure

section Operations

variable {C : Type u} [Category.{v} C] [AdditiveCategory C]
  [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C]

/-- The second composite is the saturation of a triangulated subcategory. -/
theorem operations_subcategory_saturation
    (P : ObjectProperty C) [CategoryTheory.IsTriangulated C]
    [P.IsTriangulated] :
    localizationKernel (subcategoryOperation P) = quotientKernel P := by
  sorry

/- The source warns that the two operations are not mutually inverse before
   saturation; the saturation statements above and below record the precise
   inverse form. -/
/-- The two operations become inverse on saturated systems and saturated
strictly full triangulated subcategories. -/
theorem operations_restrict_to_saturated_inverse
    {S : MorphismProperty C} {P : ObjectProperty C}
    [CategoryTheory.IsTriangulated C] [P.IsTriangulated]
    [CompatibleWithTriangulation S]
    (hS : SaturatedMultiplicativeSystem S)
    (hP : IsStrictlyFullSaturatedPretriangulated P) :
    localizationOperation S = S ∧ quotientKernel P = P := by
  sorry

end Operations

/-! ## Acyclic objects and homological functors -/

section AcyclicFunctor

variable {C A : Type*} [Category* C] [Category* A]
  [AdditiveCategory C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C] [Abelian A]

/-- The homological-functor morphism property is a saturated compatible
multiplicative system. -/
theorem acyclic_morphismProperty_isSaturated
    (H : C ⥤ A) [H.IsHomological] :
    SaturatedMultiplicativeSystem (homologicalFunctorMorphismProperty H) ∧
      CompatibleWithTriangulation (homologicalFunctorMorphismProperty H) :=
  homologicalFunctorMorphismProperty_saturated H

/-- The cone-morphism system of the homological kernel is the class of maps
which are isomorphisms in every homological degree. -/
theorem acyclic_kernel_morphismProperty_eq
    (H : C ⥤ A) [CategoryTheory.IsTriangulated C] [H.IsHomological] :
    subcategoryOperation (homologicalFunctorKernel H) =
      homologicalFunctorMorphismProperty H := by
  sorry

/-- A homological functor factors through the quotient by its acyclic kernel. -/
theorem acyclic_homologicalFunctor_factors
    (H : C ⥤ A) [CategoryTheory.IsTriangulated C] [H.IsHomological] :
    ∃! H' : quotientCategory (homologicalFunctorKernel H) ⥤ A,
      quotientFunctor (homologicalFunctorKernel H) ⋙ H' = H ∧
        H'.IsHomological := by
  sorry

end AcyclicFunctor

end Formalization.Books.Derived.Unit06
