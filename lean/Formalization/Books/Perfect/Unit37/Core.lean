import Mathlib.Algebra.Homology.CochainComplexPlus
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.Algebra.Homology.HomotopyCategory.Triangulated
import Mathlib.CategoryTheory.ObjectProperty.ClosedUnderIsomorphisms
import Mathlib.CategoryTheory.ObjectProperty.Retract
import Mathlib.CategoryTheory.Triangulated.Subcategory

/-!
# Derived Categories of Schemes, Chapter 37: shared interfaces

The preceding chapters of the Stacks Project develop schemes, sheaves, and
perfect complexes.  Those geometric APIs are not present in the current
Mathlib dependency or in the earlier formalized project chapters, so this
file records the smallest interface needed by Chapter 37.  The homological
and categorical parts use Mathlib's existing APIs directly.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Preadditive
open CategoryTheory.Triangulated

universe u

namespace Formalization.Books.Perfect.Unit37

/-- The abelian category of modules attached to a scheme in this chapter. -/
structure ModuleCategory where
  Carrier : Type u
  category : Category.{u} Carrier
  abelian : @Abelian Carrier category

instance (M : ModuleCategory) : Category M.Carrier := M.category

instance (M : ModuleCategory) : Abelian M.Carrier := M.abelian

/--
The scheme data used by this chapter.  `quasiCoherent`, `finiteType`, and
`finiteLocallyFree` are the corresponding object predicates on modules.
The perfect-object predicate is supplied separately by `PerfectObjects`, so
that it can use Mathlib's chosen derived category after the scheme interface
has installed its abelian-module instance.
-/
structure Scheme where
  modules : ModuleCategory
  quasiCompact : Prop
  quasiSeparated : Prop
  quasiCoherent : modules.Carrier → Prop
  finiteType : modules.Carrier → Prop
  finiteLocallyFree : modules.Carrier → Prop

abbrev Module (X : Scheme) := X.modules.Carrier

instance (X : Scheme) : Category (Module X) := X.modules.category

instance (X : Scheme) : Abelian (Module X) := X.modules.abelian

noncomputable instance (X : Scheme) : HasDerivedCategory (Module X) :=
  HasDerivedCategory.standard (Module X)

/-- The chosen predicate of perfect objects in `D(𝒪_X)`. -/
class PerfectObjects (X : Scheme) where
  property : ObjectProperty (DerivedCategory (Module X))

def isPerfect (X : Scheme) [PerfectObjects X] : ObjectProperty (DerivedCategory (Module X)) :=
  PerfectObjects.property

def IsPerfectObject (X : Scheme) [PerfectObjects X]
    (E : DerivedCategory (Module X)) : Prop :=
  isPerfect X E

/-- The source definition of the resolution property. -/
def HasResolutionProperty (X : Scheme) : Prop :=
  ∀ (F : Module X), X.quasiCoherent F → X.finiteType F →
    ∃ (E : Module X) (f : E ⟶ F),
      X.finiteLocallyFree E ∧ Epi f

abbrev BoundedBelowComplex (X : Scheme) := CochainComplex.Plus (Module X)

abbrev DerivedQ (X : Scheme) : CochainComplex (Module X) ℤ ⥤ DerivedCategory (Module X) :=
  DerivedCategory.Q

def Represents (X : Scheme) (F : CochainComplex (Module X) ℤ)
    (E : DerivedCategory (Module X)) : Prop :=
  E = (DerivedQ X).obj F

def RepresentsPerfect (X : Scheme) [PerfectObjects X]
    (F : BoundedBelowComplex X) : Prop :=
  IsPerfectObject X ((DerivedQ X).obj F.obj)

/-- A cochain complex is bounded when it is strictly supported in a finite interval. -/
def boundedComplexProperty (C : Type u) [Category.{u} C] [HasZeroMorphisms C] :
    ObjectProperty (CochainComplex C ℤ) :=
  fun K => ∃ a b : ℤ, K.IsStrictlyGE a ∧ K.IsStrictlyLE b

/-- Complexes whose terms are finite locally free modules and are bounded. -/
def finiteLocallyFreeComplexProperty (X : Scheme) :
    ObjectProperty (CochainComplex (Module X) ℤ) :=
  fun K =>
    (∀ i : ℤ, X.finiteLocallyFree (K.X i)) ∧ boundedComplexProperty (Module X) K

abbrev BoundedFiniteLocallyFreeComplex (X : Scheme) :=
  ObjectProperty.FullSubcategory (finiteLocallyFreeComplexProperty X)

/-- The additive category of finite locally free modules. -/
abbrev FiniteLocallyFreeModule (X : Scheme) :=
  ObjectProperty.FullSubcategory X.finiteLocallyFree

/-- The object property of bounded objects in a homotopy category. -/
def boundedHomotopyProperty (C : Type u) [Category.{u} C] [Preadditive C] :
    ObjectProperty (HomotopyCategory C (.up ℤ)) :=
  (boundedComplexProperty C).strictMap (HomotopyCategory.quotient C (.up ℤ))

/-- The homotopy category `K^b(𝒜)` of bounded complexes in `𝒜`. -/
abbrev Kb (X : Scheme) :=
  ObjectProperty.FullSubcategory (boundedHomotopyProperty (FiniteLocallyFreeModule X))

/-- The strictly full subcategory `D_perf(𝒪_X)`. -/
abbrev DPerf (X : Scheme) [PerfectObjects X] :=
  ObjectProperty.FullSubcategory (isPerfect X)

/-! ## Standard structural interfaces used by the source proposition -/

/-
Finite locally free modules are closed under finite biproducts, and bounded
complexes form a triangulated subcategory of the homotopy category.  The
geometric proofs belong to earlier chapters; these are declaration-stage
interfaces so the later definitions can use Mathlib's categorical structures.
-/
noncomputable instance finiteLocallyFree_hasFiniteBiproducts (X : Scheme) :
    HasFiniteBiproducts (FiniteLocallyFreeModule X) := by
  sorry

noncomputable instance finiteLocallyFree_hasBinaryBiproducts (X : Scheme) :
    HasBinaryBiproducts (FiniteLocallyFreeModule X) :=
  hasBinaryBiproducts_of_finite_biproducts (FiniteLocallyFreeModule X)

noncomputable instance boundedHomotopyProperty_isTriangulated (X : Scheme) :
    (boundedHomotopyProperty (FiniteLocallyFreeModule X)).IsTriangulated := by
  sorry

noncomputable instance isPerfect_isClosedUnderIsomorphisms
    (X : Scheme) [PerfectObjects X] :
    (isPerfect X).IsClosedUnderIsomorphisms := by
  sorry

noncomputable instance isPerfect_isStableUnderRetracts
    (X : Scheme) [PerfectObjects X] :
    (isPerfect X).IsStableUnderRetracts := by
  sorry

noncomputable instance isPerfect_isTriangulated
    (X : Scheme) [PerfectObjects X] :
    (isPerfect X).IsTriangulated := by
  sorry

/-- The functor from finite-module complexes to the ambient derived category. -/
noncomputable def finiteComplexToDerived (X : Scheme) :
    HomotopyCategory (FiniteLocallyFreeModule X) (.up ℤ) ⥤ DerivedCategory (Module X) :=
  (ObjectProperty.ι X.finiteLocallyFree).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh

/-- A bounded complex of finite locally free modules is perfect. -/
theorem perfect_of_bounded_finite_locally_free (X : Scheme) [PerfectObjects X]
    (K : CochainComplex (FiniteLocallyFreeModule X) ℤ)
    (hK : boundedComplexProperty (FiniteLocallyFreeModule X) K) :
    IsPerfectObject X
      ((finiteComplexToDerived X).obj ((HomotopyCategory.quotient _ _).obj K)) := by
  sorry

/-- The same perfectness assertion for an object of `K^b(𝒜)`. -/
theorem perfect_of_bounded_homotopy_object (X : Scheme) [PerfectObjects X]
    (K : Kb X) :
    IsPerfectObject X ((finiteComplexToDerived X).obj K.obj) := by
  sorry

/-- The obvious functor `K^b(𝒜) ⥤ D_perf(𝒪_X)`. -/
noncomputable def finiteComplexesToPerfect (X : Scheme) [PerfectObjects X] :
    Kb X ⥤ DPerf X :=
  ObjectProperty.lift (isPerfect X)
    (ObjectProperty.ι (boundedHomotopyProperty (FiniteLocallyFreeModule X)) ⋙
      finiteComplexToDerived X)
    (fun K => perfect_of_bounded_homotopy_object X K)

/-- The inclusion of `K^b(𝒜)` into the ambient homotopy category after forgetting finiteness. -/
noncomputable def finiteComplexHomotopyInclusion (X : Scheme) :
    Kb X ⥤ HomotopyCategory (Module X) (.up ℤ) :=
  ObjectProperty.ι (boundedHomotopyProperty (FiniteLocallyFreeModule X)) ⋙
    (ObjectProperty.ι X.finiteLocallyFree).mapHomotopyCategory (.up ℤ)

/-- The quasi-isomorphisms in `K^b(𝒜)`, detected in the ambient module category. -/
def QuasiIsomorphisms (X : Scheme) : MorphismProperty (Kb X) :=
  (HomotopyCategory.quasiIso (Module X) (.up ℤ)).inverseImage
    (finiteComplexHomotopyInclusion X)

noncomputable instance quasiIsomorphisms_hasLocalization (X : Scheme) :
    MorphismProperty.HasLocalization (QuasiIsomorphisms X) :=
  MorphismProperty.HasLocalization.standard _

abbrev LocalizedKb (X : Scheme) := (QuasiIsomorphisms X).Localization'

theorem finiteComplexesToPerfect_inverts_quasiIsomorphisms
    (X : Scheme) [PerfectObjects X] :
    (QuasiIsomorphisms X).IsInvertedBy (finiteComplexesToPerfect X) := by
  sorry

/-- The functor induced on the localization by the obvious functor. -/
noncomputable def localizedFiniteComplexesToPerfect
    (X : Scheme) [PerfectObjects X] : LocalizedKb X ⥤ DPerf X :=
  Localization.lift (finiteComplexesToPerfect X)
    (finiteComplexesToPerfect_inverts_quasiIsomorphisms X)
    (QuasiIsomorphisms X).Q'

/-- The canonical factorization isomorphism through the localization. -/
noncomputable def localizedFiniteComplexesToPerfect_factorization
    (X : Scheme) [PerfectObjects X] :
    (QuasiIsomorphisms X).Q' ⋙ localizedFiniteComplexesToPerfect X ≅
      finiteComplexesToPerfect X :=
  Localization.fac (finiteComplexesToPerfect X)
    (finiteComplexesToPerfect_inverts_quasiIsomorphisms X)
    (QuasiIsomorphisms X).Q'

end Formalization.Books.Perfect.Unit37
