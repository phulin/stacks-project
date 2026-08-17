import Formalization.Books.Cohomology.Unit02.CohomologyOfSheaves
import Formalization.Books.Derived.Unit24.FunctorialInjectiveResolutions

/-!
# Cohomology of Sheaves, Chapter 3: derived functors

The source introduces the bounded derived functor formalism used in the
cohomology constructions.  The declarations below use Mathlib's canonical
homotopy and derived categories, the earlier right-derived-functor package,
and the functorial injective-resolution interface from Derived Categories.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open Opposite
open TopologicalSpace
open Formalization.Books.Categories.Unit23
open Formalization.Books.Cohomology.Unit02
open Formalization.Books.Derived.Unit08
open Formalization.Books.Derived.Unit11
open Formalization.Books.Derived.Unit20
open Formalization.Books.Homology.Unit07
open Formalization.Books.Injectives.Unit05
open Formalization.Books.Modules.Unit03
open Formalization.Books.Sheaves.Unit10
open Formalization.Books.Sheaves.Unit22

universe v u v' u' w w'

namespace Formalization.Books.Cohomology.Unit03

/-! ## The categories used in the source notation -/

/-- The homotopy category `K(O_X)` of sheaves of modules. -/
abbrev ringedSpaceModuleK (X : RingedSpace.{v}) :=
  K (Mod X.structureSheaf)

/-- The bounded-below homotopy category `K⁺(O_X)`. -/
abbrev ringedSpaceModuleKPlus (X : RingedSpace.{v}) :=
  KPlus (Mod X.structureSheaf)

/-- The bounded-above homotopy category `K⁻(O_X)`. -/
abbrev ringedSpaceModuleKMinus (X : RingedSpace.{v}) :=
  KMinus (Mod X.structureSheaf)

/-- The bounded homotopy category `Kᵇ(O_X)`. -/
abbrev ringedSpaceModuleKBounded (X : RingedSpace.{v}) :=
  KBounded (Mod X.structureSheaf)

/-- The derived category `D(O_X)` of sheaves of modules. -/
abbrev ringedSpaceModuleD (X : RingedSpace.{v}) :=
  DerivedCategory (Mod X.structureSheaf)

/-- The bounded-below derived category `D⁺(O_X)`. -/
abbrev ringedSpaceModuleDPlus (X : RingedSpace.{v}) :=
  DPlus (Mod X.structureSheaf)

/-- The bounded-above derived category `D⁻(O_X)`. -/
abbrev ringedSpaceModuleDMinus (X : RingedSpace.{v}) :=
  DMinus (Mod X.structureSheaf)

/-- The bounded derived category `Dᵇ(O_X)`. -/
abbrev ringedSpaceModuleDBounded (X : RingedSpace.{v}) :=
  DBounded (Mod X.structureSheaf)

/-- The category of sheaves of modules on a ringed space is abelian. -/
theorem ringedSpaceModule_category_isAbelian (X : RingedSpace.{v}) :
    Nonempty (Abelian (Mod X.structureSheaf)) :=
  sheafModule_abelian X.structureSheaf

/-- The source notation `K(R)` for complexes of modules over a ring. -/
abbrev moduleK (R : Type v) [Ring R] :=
  K (ModuleCat.{v} R)

/-- The source notation `K⁺(R)` for bounded-below complexes of modules. -/
abbrev moduleKPlus (R : Type v) [Ring R] :=
  KPlus (ModuleCat.{v} R)

/-- The source notation `K⁻(R)` for bounded-above complexes of modules. -/
abbrev moduleKMinus (R : Type v) [Ring R] :=
  KMinus (ModuleCat.{v} R)

/-- The source notation `Kᵇ(R)` for bounded complexes of modules. -/
abbrev moduleKBounded (R : Type v) [Ring R] :=
  KBounded (ModuleCat.{v} R)

/-- The source notation `D(R)` for the derived category of modules. -/
abbrev moduleD (R : Type v) [Ring R] :=
  DerivedCategory (ModuleCat.{v} R)

/-- The source notation `D⁺(R)` for bounded-below derived modules. -/
abbrev moduleDPlus (R : Type v) [Ring R] :=
  DPlus (ModuleCat.{v} R)

/-- The source notation `D⁻(R)` for bounded-above derived modules. -/
abbrev moduleDMinus (R : Type v) [Ring R] :=
  DMinus (ModuleCat.{v} R)

/-- The source notation `Dᵇ(R)` for bounded derived modules. -/
abbrev moduleDBounded (R : Type v) [Ring R] :=
  DBounded (ModuleCat.{v} R)

/-! ## The injective resolution functor -/

/-- The strictly full subcategory of injective sheaves of modules. -/
abbrev ringedSpaceModuleInjectiveSubcategory (X : RingedSpace.{v}) :=
  Formalization.Books.Derived.Unit24.InjectiveSubcategory
    (Mod X.structureSheaf)

/-- The bounded-below homotopy category represented by termwise injective
complexes.  This is the source's `K⁺(I)`. -/
abbrev ringedSpaceModuleKPlusInjective (X : RingedSpace.{v}) :=
  Formalization.Books.Derived.Unit24.KPlusInjective
    (Mod X.structureSheaf)

/-- Functorial bounded-below injective resolutions exist for sheaves of
modules on a ringed space. -/
theorem ringedSpaceModule_resolutionFunctor_exists (X : RingedSpace.{v}) :
    Nonempty (ringedSpaceModuleKPlus X ⥤ ringedSpaceModuleKPlusInjective X) := by
  obtain ⟨inj, hsource⟩ :=
    Formalization.Books.Derived.Unit24.functorial_injective_resolution_exists
      (A := Mod X.structureSheaf)
      (sheafOfModules_has_enough_injectives X).2
  obtain ⟨compatibility⟩ :=
    Formalization.Books.Derived.Unit24.resolutionFunctorCompatibility_exists
      inj hsource
  exact ⟨compatibility.j⟩

/-- A chosen resolution functor `j_X : K⁺(O_X) ⥤ K⁺(I)`. -/
noncomputable def ringedSpaceModule_resolutionFunctor (X : RingedSpace.{v}) :
    ringedSpaceModuleKPlus X ⥤ ringedSpaceModuleKPlusInjective X :=
  Classical.choice (ringedSpaceModule_resolutionFunctor_exists X)

/-! ## Right derived functors -/

/-- The bounded-below right-derived functor attached to a left exact functor.

This is the canonical resolution-based functor on `D⁺`; it is the formal
version of the source's `RF = F ∘ j'_X`. -/
noncomputable def rightDerivedFunctorOfLeftExact
    {A : Type u} [Category.{v} A] [Abelian A] [EnoughInjectives A]
    {B : Type u'} [Category.{v'} B] [Abelian B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} B]
    (F : A ⥤ B) (hF : IsLeftExact F) : DPlus A ⥤ DPlus B := by
  letI : F.Additive := left_or_right_exact_additive F (Or.inl hF)
  exact F.rightDerivedFunctorPlus

/-- The same right-derived functor viewed on bounded-below complexes. -/
noncomputable def rightDerivedFunctorOfLeftExactOnComplexes
    {A : Type u} [Category.{v} A] [Abelian A] [EnoughInjectives A]
    {B : Type u'} [Category.{v'} B] [Abelian B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} B]
    (F : A ⥤ B) (hF : IsLeftExact F) : CompPlus A ⥤ DPlus B :=
  leftExactRightDerivedComplexFunctor F hF

/-- The same right-derived functor viewed on bounded-below homotopy objects. -/
noncomputable def rightDerivedFunctorOfLeftExactOnHomotopy
    {A : Type u} [Category.{v} A] [Abelian A] [EnoughInjectives A]
    {B : Type u'} [Category.{v'} B] [Abelian B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} B]
    (F : A ⥤ B) (hF : IsLeftExact F) : KPlus A ⥤ DPlus B := by
  letI : F.Additive := left_or_right_exact_additive F (Or.inl hF)
  exact rightDerivedHomotopyFunctor F

/-- The same construction viewed on objects of the source abelian category. -/
noncomputable def rightDerivedFunctorOfLeftExactOnObjects
    {A : Type u} [Category.{v} A] [Abelian A] [EnoughInjectives A]
    {B : Type u'} [Category.{v'} B] [Abelian B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} B]
    (F : A ⥤ B) (hF : IsLeftExact F) : A ⥤ DPlus B := by
  letI : F.Additive := left_or_right_exact_additive F (Or.inl hF)
  exact rightDerivedObjectFunctor F

/-- The higher right-derived functor is cohomology of the total right-derived
functor applied to the degree-zero stalk complex. -/
theorem higherRightDerivedFunctor_eq_cohomology_comp
    {A : Type u} [Category.{v} A] [Abelian A] [EnoughInjectives A]
    {B : Type u'} [Category.{v'} B] [Abelian B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} B]
    (F : A ⥤ B) (hF : IsLeftExact F) (i : ℤ) :
    higherRightDerivedFunctor F hF i =
      DerivedCategory.Plus.singleFunctor A 0 ⋙
        rightDerivedFunctorOfLeftExact F hF ⋙
        DerivedCategory.Plus.homologyFunctor B i := by
  rfl

/-- The right-derived functor is exact in the triangulated sense. -/
theorem rightDerivedFunctorOfLeftExact_isExact
    {A : Type u} [Category.{v} A] [Abelian A] [EnoughInjectives A]
    {B : Type u'} [Category.{v'} B] [Abelian B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} B]
    (F : A ⥤ B) (hF : IsLeftExact F) :
    ∃ hG : (rightDerivedFunctorOfLeftExact F hF).CommShift ℤ,
      letI : (rightDerivedFunctorOfLeftExact F hF).CommShift ℤ := hG
      (rightDerivedFunctorOfLeftExact F hF).IsTriangulated := by
  sorry

/-- The degree-zero higher right-derived functor is naturally isomorphic to
the original left exact functor. -/
noncomputable def rightDerivedFunctorOfLeftExact_zeroIso
    {A : Type u} [Category.{v} A] [Abelian A] [EnoughInjectives A]
    {B : Type u'} [Category.{v'} B] [Abelian B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} B]
    (F : A ⥤ B) (hF : IsLeftExact F) :
    higherRightDerivedFunctor F hF 0 ≅ F :=
  Classical.choice (higherRightDerivedFunctor_zero_iso F hF)

/-- The higher right-derived functors form the universal cohomological
δ-functor extending `F`. -/
theorem rightDerivedFunctorOfLeftExact_isUniversal
    {A : Type u} [Category.{v} A] [Abelian A] [EnoughInjectives A]
    {B : Type u'} [Category.{v'} B] [Abelian B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} B]
    (F : A ⥤ B) (hF : IsLeftExact F) :
    IsUniversalHigherRightDerivedDeltaFunctor F hF :=
  higherRightDerivedFunctor_universal F hF

/-! ## Derived sections on an open -/

/-- The sections functor `Γ(U, -)` on sheaves of modules. -/
noncomputable def ringedSpaceModuleSectionsFunctor
    (X : RingedSpace.{v}) (U : Opens X.carrier) :
    Mod X.structureSheaf ⥤
      ModuleCat.{v} (X.structureSheaf.obj.obj (op U)) :=
  SheafOfModules.evaluation X.structureSheaf (op U)

/-- Sections over an open are left exact. -/
theorem ringedSpaceModuleSectionsFunctor_isLeftExact
    (X : RingedSpace.{v}) (U : Opens X.carrier) :
    IsLeftExact (ringedSpaceModuleSectionsFunctor X U) := by
  sorry

/-- The total derived sections functor `RΓ(U, -)`. -/
noncomputable def ringedSpaceModuleTotalDerivedSections
    (X : RingedSpace.{v}) (U : Opens X.carrier) :
    DPlus (Mod X.structureSheaf) ⥤
      DPlus (ModuleCat.{v} (X.structureSheaf.obj.obj (op U))) :=
  rightDerivedFunctorOfLeftExact
    (ringedSpaceModuleSectionsFunctor X U)
    (ringedSpaceModuleSectionsFunctor_isLeftExact X U)

/-- The `i`th cohomology functor `Hⁱ(U, -) = RⁱΓ(U, -)`. -/
noncomputable def ringedSpaceModuleSectionsCohomology
    (X : RingedSpace.{v}) (U : Opens X.carrier) (i : ℤ) :
    Mod X.structureSheaf ⥤
      ModuleCat.{v} (X.structureSheaf.obj.obj (op U)) := by
  exact higherRightDerivedFunctor
    (ringedSpaceModuleSectionsFunctor X U)
    (ringedSpaceModuleSectionsFunctor_isLeftExact X U) i

/-- The value `Hⁱ(U, F)` of the derived sections functor. -/
noncomputable abbrev ringedSpaceModuleSectionsCohomologyObject
    (X : RingedSpace.{v}) (U : Opens X.carrier)
    (F : Mod X.structureSheaf) (i : ℤ) :
    ModuleCat.{v} (X.structureSheaf.obj.obj (op U)) :=
  (ringedSpaceModuleSectionsCohomology X U i).obj F

/-- At the top open, the sections functor is the global-sections functor from
Chapter 2. -/
theorem ringedSpaceModuleSectionsFunctor_top
    (X : RingedSpace.{v}) :
    ringedSpaceModuleSectionsFunctor X (⊤ : Opens X.carrier) =
      ringedSpaceModuleGlobalSections X := by
  rfl

/-- At the top open, derived sections recover the Chapter 2 cohomology
functors. -/
theorem ringedSpaceModuleSectionsCohomology_top
    (X : RingedSpace.{v}) (i : ℤ) :
    ringedSpaceModuleSectionsCohomology X (⊤ : Opens X.carrier) i =
      ringedSpaceModuleCohomology X i := by
  sorry

/-! ## Derived pushforward -/

/-- The derived pushforward `Rf_*` for a morphism of ringed spaces. -/
noncomputable def ringedSpaceModuleDerivedPushforward
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y) :
    DPlus (Mod X.structureSheaf) ⥤ DPlus (Mod Y.structureSheaf) :=
  rightDerivedFunctorOfLeftExact
    (sheafModuleRingedSpacePushforward f)
    (sheafModuleRingedSpacePushforward_isLeftExact f)

/-- The `i`th cohomology-sheaf functor of derived pushforward, denoted
`Rⁱf_*`. -/
noncomputable def ringedSpaceModuleDerivedPushforwardCohomology
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y) (i : ℤ) :
    DPlus (Mod X.structureSheaf) ⥤ Mod Y.structureSheaf :=
  ringedSpaceModuleDerivedPushforward f ⋙
    DerivedCategory.Plus.homologyFunctor (Mod Y.structureSheaf) i

/-- On a sheaf concentrated in degree zero, the derived pushforward
cohomology functor is the earlier higher direct-image functor. -/
theorem ringedSpaceModuleDerivedPushforwardCohomology_single
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y)
    (F : Mod X.structureSheaf) (i : ℤ) :
    (ringedSpaceModuleDerivedPushforwardCohomology f i).obj
        ((DerivedCategory.Plus.singleFunctor (Mod X.structureSheaf) 0).obj F) =
      (ringedSpaceModuleHigherDirectImage f i).obj F := by
  sorry

/-- The two total derived functors in this section are exact functors of
derived categories. -/
theorem ringedSpaceModuleTotalDerivedSections_isExact
    (X : RingedSpace.{v}) (U : Opens X.carrier) :
    ∃ hG : (ringedSpaceModuleTotalDerivedSections X U).CommShift ℤ,
      letI : (ringedSpaceModuleTotalDerivedSections X U).CommShift ℤ := hG
      (ringedSpaceModuleTotalDerivedSections X U).IsTriangulated := by
  sorry

theorem ringedSpaceModuleDerivedPushforward_isExact
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y) :
    ∃ hG : (ringedSpaceModuleDerivedPushforward f).CommShift ℤ,
      letI : (ringedSpaceModuleDerivedPushforward f).CommShift ℤ := hG
      (ringedSpaceModuleDerivedPushforward f).IsTriangulated := by
  sorry

/-! ## The representation convention and actual complex morphisms -/

/-- A derived object is represented by a complex when the canonical image of
that complex is isomorphic to the derived object.  This is the canonical
derived-category form of the source's quasi-isomorphism convention. -/
def representsInDerivedCategory
    {A : Type u} [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A]
    (F : DerivedCategory A) (I : BookComplex A) : Prop :=
  Nonempty ((DerivedCategory.Q (C := A)).obj I ≅ F)

/-- A complex is a bounded-below termwise-injective complex. -/
def isBoundedBelowInjectiveComplex
    {A : Type u} [Category.{v} A] [Abelian A]
    (I : BookComplex A) : Prop :=
  IsBoundedBelow I ∧ ∀ n : ℤ, Injective (I.X n)

/-- A bounded-below termwise-injective complex represents a derived object. -/
def representsByBoundedBelowInjectiveComplex
    {A : Type u} [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A]
    (F : DerivedCategory A) (I : BookComplex A) : Prop :=
  isBoundedBelowInjectiveComplex I ∧ representsInDerivedCategory F I

/-- A morphism of complexes induces the corresponding morphism in the
derived category. -/
noncomputable def derivedMorphismOfComplexMorphism
    {A : Type u} [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A]
    {K L : BookComplex A} (f : K ⟶ L) :
    (DerivedCategory.Q (C := A)).obj K ⟶
      (DerivedCategory.Q (C := A)).obj L :=
  (DerivedCategory.Q (C := A)).map f

/-- A derived morphism between the images of two complexes is represented by
an actual complex morphism when it is the image of that map under localization.
This keeps the source's distinction between derived morphisms and complex maps
explicit. -/
def derivedMorphismRepresentedByComplexMorphism
    {A : Type u} [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A]
    {K L : BookComplex A}
    (α : (DerivedCategory.Q (C := A)).obj K ⟶
      (DerivedCategory.Q (C := A)).obj L)
    (f : K ⟶ L) : Prop :=
  α = derivedMorphismOfComplexMorphism f

end Formalization.Books.Cohomology.Unit03
