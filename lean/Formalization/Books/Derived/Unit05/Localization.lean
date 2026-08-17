import Mathlib.CategoryTheory.Localization.Triangulated
import Mathlib.CategoryTheory.Triangulated.HomologicalFunctor
import Formalization.Books.Categories.Unit27.Localization
import Formalization.Books.Derived.Unit04.ElementaryResults

/-!
# Derived Categories, Chapter 5: localization of triangulated categories

The source's localization process is expressed using Mathlib's canonical
morphism properties, calculus-of-fractions localizations, and induced
triangulated structures.  The declarations below record the source-facing
interfaces; substantive proofs are deferred to the proving stage.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Preadditive
open CategoryTheory.Pretriangulated
open Formalization.Books.Categories.Unit27
open Formalization.Books.Derived.Unit03
open Formalization.Books.Homology.Unit03
open scoped CategoryTheory.Pretriangulated.Opposite ZeroObject

universe v u v' u'

namespace Formalization.Books.Derived.Unit05

/-! ## Compatibility conditions -/

section Compatibility

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C]

/- Mathlib's `IsCompatibleWithTriangulation` is exactly the source's MS5/MS6
   interface, with MS5 expressed for every integer shift. -/
abbrev CompatibleWithTriangulation (S : MorphismProperty C) :=
  MorphismProperty.IsCompatibleWithTriangulation S

/- The source's LMS2 and RMS2 are not separate Mathlib classes: the calculus
   classes package them together with the corresponding cancellation axiom.
   These two predicates retain the exact displayed Ore-square statements. -/
def LeftOreCondition (S : MorphismProperty C) : Prop :=
  ∀ ⦃X Y Z W : C⦄ (t : X ⟶ Z) (g : X ⟶ Y), S t →
    ∃ (s : Y ⟶ W) (f : Z ⟶ W), S s ∧ t ≫ f = g ≫ s

def RightOreCondition (S : MorphismProperty C) : Prop :=
  ∀ ⦃X Y Z W : C⦄ (g : X ⟶ Y) (s : Y ⟶ W), S s →
    ∃ (t : X ⟶ Z) (f : Z ⟶ W), S t ∧ t ≫ f = g ≫ s

theorem localization_conditions_contains_isomorphisms
    {S : MorphismProperty C} [S.ContainsIdentities] [CompatibleWithTriangulation S] :
    MorphismProperty.isomorphisms C ≤ S := by
  sorry

theorem localization_conditions_ms2
    {S : MorphismProperty C} [S.IsMultiplicative]
    [CompatibleWithTriangulation S] :
    LeftOreCondition S ∧ RightOreCondition S := by
  sorry

/- The source's MS5 remark, recorded using the canonical shift-compatibility
   class and its equivalent one-way closure formulation under MS1 and MS6. -/
def AllIntegerShifts (S : MorphismProperty C) : Prop :=
  ∀ ⦃X Y : C⦄ (f : X ⟶ Y), S f → ∀ n : ℤ, S (f⟦n⟧')

theorem ms5_iff_all_integer_shifts
    {S : MorphismProperty C} [S.IsMultiplicative]
    [CompatibleWithTriangulation S] :
    AllIntegerShifts S ↔ MorphismProperty.IsCompatibleWithShift S ℤ := by
  sorry

end Compatibility

/-! ## Systems detected by exact and homological functors -/

section ExactFunctorLocalization

variable {C D : Type*} [Category* C] [Category* D]
  [AdditiveCategory C] [AdditiveCategory D]
  [HasShift C ℤ] [HasShift D ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive]
  [∀ n : ℤ, (shiftFunctor D n).Additive]
  [Pretriangulated C] [Pretriangulated D]

def exactFunctorMorphismProperty (F : C ⥤ D) : MorphismProperty C :=
  (MorphismProperty.isomorphisms D).inverseImage F

theorem exactFunctorMorphismProperty_saturated
    (F : C ⥤ D) [F.CommShift ℤ] [F.IsTriangulated] :
    SaturatedMultiplicativeSystem (exactFunctorMorphismProperty F) ∧
      CompatibleWithTriangulation (exactFunctorMorphismProperty F) := by
  sorry

end ExactFunctorLocalization

section HomologicalFunctorLocalization

variable {C A : Type*} [Category* C] [Category* A]
  [AdditiveCategory C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C] [Abelian A]

def homologicalFunctorMorphismProperty (H : C ⥤ A) : MorphismProperty C :=
  fun _ _ f => ∀ i : ℤ, IsIso ((homologicalDegree H i).map f)

theorem homologicalFunctorMorphismProperty_saturated
    (H : C ⥤ A) [H.IsHomological] :
    SaturatedMultiplicativeSystem (homologicalFunctorMorphismProperty H) ∧
      CompatibleWithTriangulation (homologicalFunctorMorphismProperty H) := by
  sorry

end HomologicalFunctorLocalization

/-! ## The localized pretriangulated structure and its universal property -/

section LocalizationConstruction

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C]
  {S : MorphismProperty C} [LeftMultiplicativeSystem S]
  [RightMultiplicativeSystem S] [CompatibleWithTriangulation S]

/- This predicate is the source's uniqueness condition: the canonical
   localized shift is used, and the localization functor is exact for the
   candidate pretriangulated structure. -/
def IsLocalizationPretriangulatedStructure
    (P : Pretriangulated S.Localization) : Prop :=
  letI : Pretriangulated S.Localization := P
  Functor.IsTriangulated S.Q

theorem localization_pretriangulated_exists_unique :
    ∃! P : Pretriangulated S.Localization,
      IsLocalizationPretriangulatedStructure (S := S) P := by
  sorry

@[instance_reducible]
noncomputable def localizationFunctorCommShift : S.Q.CommShift ℤ :=
  inferInstance

omit [RightMultiplicativeSystem S] in
theorem localizationFunctor_exact : S.Q.IsTriangulated := by
  infer_instance

omit [RightMultiplicativeSystem S] in
theorem localization_triangulated [CategoryTheory.IsTriangulated C] :
    CategoryTheory.IsTriangulated S.Localization := by
  infer_instance

/- The construction and its factorization maps use the canonical localization
   construction. -/
noncomputable def localizationFactor {E : Type*} [Category* E]
    (F : C ⥤ E) (hF : S.IsInvertedBy F) : S.Localization ⥤ E :=
  Localization.Construction.lift F hF

omit [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    [LeftMultiplicativeSystem S] [RightMultiplicativeSystem S]
    [CompatibleWithTriangulation S] in
theorem localizationFactor_fac {E : Type*} [Category* E]
    (F : C ⥤ E) (hF : S.IsInvertedBy F) :
    S.Q ⋙ localizationFactor (S := S) F hF = F :=
  Localization.Construction.fac F hF

omit [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    [LeftMultiplicativeSystem S] [RightMultiplicativeSystem S]
    [CompatibleWithTriangulation S] in
theorem localizationFactor_unique {E : Type*} [Category* E]
    (F₁ F₂ : S.Localization ⥤ E)
    (h : S.Q ⋙ F₁ = S.Q ⋙ F₂) : F₁ = F₂ :=
  Localization.Construction.uniq F₁ F₂ h

def IsExactLocalizationFactor {D : Type*} [Category* D]
    [Preadditive D] [HasZeroObject D] [HasShift D ℤ]
    [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
    (F : S.Localization ⥤ D) : Prop :=
  ∃ hF : F.CommShift ℤ,
    letI : F.CommShift ℤ := hF
    F.IsTriangulated

theorem homological_localizationFactor_isHomological
    {A : Type*} [Category* A] [Abelian A]
    (H : C ⥤ A) [H.IsHomological] (hH : S.IsInvertedBy H) :
    (localizationFactor (S := S) H hH).IsHomological := by
  sorry

theorem exact_localizationFactor_isExact
    {D : Type*} [Category* D] [Preadditive D] [HasZeroObject D]
    [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive]
    [Pretriangulated D]
    (F : C ⥤ D) [F.CommShift ℤ] [F.IsTriangulated]
    (hF : S.IsInvertedBy F) :
    IsExactLocalizationFactor
      (S := S) (localizationFactor (S := S) F hF) := by
  sorry

end LocalizationConstruction

/-! ## Localization and full triangulated subcategories -/

section LocalizationSubcategory

variable {C : Type u} [Category.{v} C] [AdditiveCategory C]
  [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C]

def restrictedMorphismProperty (S : MorphismProperty C)
    (P : ObjectProperty C) : MorphismProperty P.FullSubcategory :=
  S.inverseImage P.ι

theorem restrictedMorphismProperty_saturated
    {S : MorphismProperty C} [CompatibleWithTriangulation S]
    (hS : SaturatedMultiplicativeSystem S) (P : ObjectProperty C)
    [P.IsTriangulated] :
    SaturatedMultiplicativeSystem (restrictedMorphismProperty S P) := by
  sorry

theorem restrictedMorphismProperty_compatible
    {S : MorphismProperty C} [CompatibleWithTriangulation S]
    (P : ObjectProperty C) [P.IsTriangulated] :
    CompatibleWithTriangulation (restrictedMorphismProperty S P) := by
  sorry

noncomputable def fullSubcategoryLocalizationFunctor
    (S : MorphismProperty C) (P : ObjectProperty C) :
    (restrictedMorphismProperty S P).Localization ⥤ S.Localization :=
  Localization.Construction.lift (P.ι ⋙ S.Q) (by
    intro X Y f hf
    exact MorphismProperty.Q_inverts S (P.ι.map f) hf)

theorem fullSubcategoryLocalization_isEquivalence
    {S : MorphismProperty C} [CompatibleWithTriangulation S]
    (hS : SaturatedMultiplicativeSystem S) (P : ObjectProperty C)
    [P.IsTriangulated]
    (hP : ∀ X : C, ∃ (X' : P.FullSubcategory)
      (s : P.ι.obj X' ⟶ X), S s) :
    Functor.IsEquivalence (fullSubcategoryLocalizationFunctor S P) := by
  sorry

theorem fullSubcategoryLocalization_isExact
    {S : MorphismProperty C} [LeftMultiplicativeSystem S]
    [RightMultiplicativeSystem S] [CompatibleWithTriangulation S]
    (P : ObjectProperty C) [P.IsTriangulated]
    [LeftMultiplicativeSystem (restrictedMorphismProperty S P)]
    [RightMultiplicativeSystem (restrictedMorphismProperty S P)]
    [CompatibleWithTriangulation (restrictedMorphismProperty S P)] :
    IsExactLocalizationFactor (S := restrictedMorphismProperty S P)
      (fullSubcategoryLocalizationFunctor S P) := by
  sorry

end LocalizationSubcategory

/-! ## The kernel of the localization functor -/

section LocalizationKernel

variable {C : Type u} [Category.{v} C] [AdditiveCategory C]
  [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C]
  {S : MorphismProperty C} [LeftMultiplicativeSystem S]
  [RightMultiplicativeSystem S] [CompatibleWithTriangulation S]

def IsZeroAfterLocalization (S : MorphismProperty C) (Z : C) : Prop :=
  IsZero (S.Q.obj Z)

def KernelLocalizationOutgoingZero (S : MorphismProperty C) (Z : C) : Prop :=
  ∃ Z' : C, S (0 : Z ⟶ Z')

def KernelLocalizationIncomingZero (S : MorphismProperty C) (Z : C) : Prop :=
  ∃ Z' : C, S (0 : Z' ⟶ Z)

def KernelLocalizationBiproductTriangle (S : MorphismProperty C) (Z : C) : Prop :=
  ∃ (Z' X Y : C) (f : X ⟶ Y) (g : Y ⟶ Z ⊞ Z')
    (h : Z ⊞ Z' ⟶ X⟦(1 : ℤ)⟧),
    Triangle.mk f g h ∈ distTriang C ∧ S f

def KernelLocalizationZeroToObject (S : MorphismProperty C) (Z : C) : Prop :=
  S (0 : (0 : C) ⟶ Z)

def KernelLocalizationObjectToZero (S : MorphismProperty C) (Z : C) : Prop :=
  S (0 : Z ⟶ (0 : C))

def KernelLocalizationTriangle (S : MorphismProperty C) (Z : C) : Prop :=
  ∃ (X Y : C) (f : X ⟶ Y) (g : Y ⟶ Z)
    (h : Z ⟶ X⟦(1 : ℤ)⟧),
    Triangle.mk f g h ∈ distTriang C ∧ S f

theorem kernel_localization_characterization (Z : C) :
    (IsZeroAfterLocalization S Z ↔ KernelLocalizationOutgoingZero S Z) ∧
    (KernelLocalizationOutgoingZero S Z ↔ KernelLocalizationIncomingZero S Z) ∧
    (KernelLocalizationIncomingZero S Z ↔ KernelLocalizationBiproductTriangle S Z) ∧
    ∀ hS : SaturatedMultiplicativeSystem S,
      (IsZeroAfterLocalization S Z ↔ KernelLocalizationZeroToObject S Z) ∧
      (KernelLocalizationZeroToObject S Z ↔ KernelLocalizationObjectToZero S Z) ∧
      (KernelLocalizationObjectToZero S Z ↔ KernelLocalizationTriangle S Z) := by
  sorry

end LocalizationKernel

/-! ## Filtered categories of localized triangle morphisms -/

section LimitTriangles

variable {C : Type u} [Category.{v} C] [AdditiveCategory C]
  [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C]

def triangleMorphismProperty (S : MorphismProperty C) :
    MorphismProperty (Triangle C) :=
  fun _ _ φ => S φ.hom₁ ∧ S φ.hom₂ ∧ S φ.hom₃

abbrev TriangleLocalizationIndex (S : MorphismProperty C) (T : Triangle C) :=
  (triangleMorphismProperty S).Under
    (⊤ : MorphismProperty (Triangle C)) T

def triangleLocalizationIndexToObject₁
    (S : MorphismProperty C) (T : Triangle C) :
    TriangleLocalizationIndex S T ⥤ LeftDenominatorCategory S T.obj₁ where
  obj A :=
    MorphismProperty.Under.mk
      (P := S) (Q := (⊤ : MorphismProperty C)) (X := T.obj₁)
      A.hom.hom₁ A.prop.1
  map {A B} φ :=
    MorphismProperty.Under.homMk φ.right.hom₁ (by
      change A.hom.hom₁ ≫ φ.right.hom₁ = B.hom.hom₁
      exact congrArg (fun k => k.hom₁) (MorphismProperty.Under.w φ))
  map_id A := by
    apply MorphismProperty.Under.Hom.ext
    rfl
  map_comp f g := by
    apply MorphismProperty.Under.Hom.ext
    rfl

def triangleLocalizationIndexToObject₂
    (S : MorphismProperty C) (T : Triangle C) :
    TriangleLocalizationIndex S T ⥤ LeftDenominatorCategory S T.obj₂ where
  obj A :=
    MorphismProperty.Under.mk
      (P := S) (Q := (⊤ : MorphismProperty C)) (X := T.obj₂)
      A.hom.hom₂ A.prop.2.1
  map {A B} φ :=
    MorphismProperty.Under.homMk φ.right.hom₂ (by
      change A.hom.hom₂ ≫ φ.right.hom₂ = B.hom.hom₂
      exact congrArg (fun k => k.hom₂) (MorphismProperty.Under.w φ))
  map_id A := by
    apply MorphismProperty.Under.Hom.ext
    rfl
  map_comp f g := by
    apply MorphismProperty.Under.Hom.ext
    rfl

def triangleLocalizationIndexToObject₃
    (S : MorphismProperty C) (T : Triangle C) :
    TriangleLocalizationIndex S T ⥤ LeftDenominatorCategory S T.obj₃ where
  obj A :=
    MorphismProperty.Under.mk
      (P := S) (Q := (⊤ : MorphismProperty C)) (X := T.obj₃)
      A.hom.hom₃ A.prop.2.2
  map {A B} φ :=
    MorphismProperty.Under.homMk φ.right.hom₃ (by
      change A.hom.hom₃ ≫ φ.right.hom₃ = B.hom.hom₃
      exact congrArg (fun k => k.hom₃) (MorphismProperty.Under.w φ))
  map_id A := by
    apply MorphismProperty.Under.Hom.ext
    rfl
  map_comp f g := by
    apply MorphismProperty.Under.Hom.ext
    rfl

theorem triangleLocalizationIndex_filtered
    {S : MorphismProperty C} (hS : SaturatedMultiplicativeSystem S)
    [CompatibleWithTriangulation S] (T : Triangle C) :
    IsFiltered (TriangleLocalizationIndex S T) := by
  sorry

theorem triangleLocalizationIndex_evaluations_cofinal
    {S : MorphismProperty C} (hS : SaturatedMultiplicativeSystem S)
    [CompatibleWithTriangulation S] (T : Triangle C) :
    Functor.Final (triangleLocalizationIndexToObject₁ S T) ∧
      Functor.Final (triangleLocalizationIndexToObject₂ S T) ∧
      Functor.Final (triangleLocalizationIndexToObject₃ S T) := by
  sorry

end LimitTriangles

end Formalization.Books.Derived.Unit05
