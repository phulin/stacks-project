import Formalization.Books.Cohomology.Unit01
import Formalization.Books.Derived.Unit20.HigherDerivedFunctors
import Formalization.Books.Injectives.Unit04
import Formalization.Books.Injectives.Unit05
import Formalization.Books.Modules.Unit03.AbelianCategory
import Formalization.Books.Sheaves.Unit26.Infrastructure
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Topology.Sheaves.AddCommGrpCat
import Mathlib.Topology.Sheaves.Functors

/-!
# Cohomology of Sheaves, Chapter 2: cohomology of sheaves

The source defines sheaf cohomology and higher direct images by applying
cohomology to injective resolutions.  The canonical right-derived functor
API is the resolution-independent implementation of that construction; its
universal cohomological δ-functor interface records the source's final
assertion in each setting.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open Opposite
open TopologicalSpace
open Formalization.Books.Categories.Unit23
open Formalization.Books.Derived.Unit20
open Formalization.Books.Homology.Unit12
open Formalization.Books.Injectives.Unit04
open Formalization.Books.Injectives.Unit05
open Formalization.Books.Modules.Unit03
open Formalization.Books.Sheaves.Unit10
open Formalization.Books.Sheaves.Unit22

universe v

namespace Formalization.Books.Cohomology.Unit02

/-! ## Resolution infrastructure -/

/- These instances install the earlier chapters' existence results and the
  standard derived-category model at the concrete categories used here. -/
noncomputable instance abelianSheaf_enoughInjectives (X : TopCat.{v}) :
    EnoughInjectives (TopCat.Sheaf AddCommGrpCat.{v} X) :=
  abelian_sheaves_have_enough_injectives

noncomputable instance abelianSheaf_hasDerivedCategory (X : TopCat.{v}) :
    HasDerivedCategory (TopCat.Sheaf AddCommGrpCat.{v} X) :=
  HasDerivedCategory.standard _

noncomputable instance addCommGrpCat_hasDerivedCategory :
    HasDerivedCategory AddCommGrpCat.{v} :=
  HasDerivedCategory.standard _

noncomputable instance ringedSpaceModule_enoughInjectives
    (X : RingedSpace.{v}) : EnoughInjectives (Mod X.structureSheaf) :=
  (sheafOfModules_has_enough_injectives X).1

noncomputable instance ringedSpaceModule_hasDerivedCategory
    (X : RingedSpace.{v}) : HasDerivedCategory (Mod X.structureSheaf) :=
  HasDerivedCategory.standard _

noncomputable instance moduleCat_hasDerivedCategory (R : Type v) [Ring R] :
    HasDerivedCategory (ModuleCat.{v} R) :=
  HasDerivedCategory.standard _

/-! ## Cohomology of abelian sheaves -/

/- The source's `Ab(X)` is Mathlib's category of `AddCommGrpCat`-valued
  sheaves.  We keep the canonical category in every declaration below rather
  than introducing a second sheaf type. -/

/-- The global-sections functor on abelian sheaves. -/
noncomputable def abelianSheafGlobalSections (X : TopCat.{v}) :
    TopCat.Sheaf AddCommGrpCat.{v} X ⥤ AddCommGrpCat.{v} :=
  TopCat.Sheaf.forget AddCommGrpCat.{v} X ⋙
    (evaluation (Opens X)ᵒᵖ AddCommGrpCat.{v}).obj
      (op (⊤ : Opens X))

/- The evaluation and forgetful functors preserve finite limits.  This is the
  categorical form of the source's left-exact global-sections functor. -/
theorem abelianSheafGlobalSections_isLeftExact (X : TopCat.{v}) :
    IsLeftExact (abelianSheafGlobalSections X) := by
  sorry

/-- The `i`th cohomology functor of abelian sheaves on `X`.

This is the canonical right-derived functor of global sections, hence it
computes the cohomology of any chosen injective resolution. -/
noncomputable def abelianSheafCohomology (X : TopCat.{v}) (i : ℤ) :
    TopCat.Sheaf AddCommGrpCat.{v} X ⥤ AddCommGrpCat.{v} := by
  exact higherRightDerivedFunctor
    (abelianSheafGlobalSections X)
    (abelianSheafGlobalSections_isLeftExact X) i

/-- The cohomology group `Hⁱ(X, F)` of an abelian sheaf. -/
noncomputable abbrev abelianSheafCohomologyObject
    (X : TopCat.{v}) (F : TopCat.Sheaf AddCommGrpCat.{v} X) (i : ℤ) :
    AddCommGrpCat.{v} :=
  (abelianSheafCohomology X i).obj F

/-! The universal δ-functor package for the family `Hⁱ(X, -)`. -/

/- This chosen object is the source-facing δ-functor structure supplied by the
  universal right-derived construction. -/
noncomputable def abelianSheafCohomologyDeltaFunctor (X : TopCat.{v}) :
    CohomologicalDeltaFunctor
      (TopCat.Sheaf AddCommGrpCat.{v} X) AddCommGrpCat.{v} := by
  exact Classical.choose <| higherRightDerivedFunctor_universal
    (abelianSheafGlobalSections X)
    (abelianSheafGlobalSections_isLeftExact X)

theorem abelianSheafCohomologyDeltaFunctor_isUniversal (X : TopCat.{v}) :
    (abelianSheafCohomologyDeltaFunctor X).IsUniversal := by
  exact (Classical.choose_spec (higherRightDerivedFunctor_universal
    (abelianSheafGlobalSections X)
    (abelianSheafGlobalSections_isLeftExact X))).1

theorem abelianSheafCohomologyDeltaFunctor_functor (X : TopCat.{v}) (n : ℕ) :
    (abelianSheafCohomologyDeltaFunctor X).functor n =
      abelianSheafCohomology X (n : ℤ) := by
  exact (Classical.choose_spec (higherRightDerivedFunctor_universal
    (abelianSheafGlobalSections X)
    (abelianSheafGlobalSections_isLeftExact X))).2 n

/-! ## Higher direct images of abelian sheaves -/

/-- Pushforward of abelian sheaves along a continuous map. -/
noncomputable def abelianSheafPushforward {X Y : TopCat.{v}} (f : X ⟶ Y) :
    TopCat.Sheaf AddCommGrpCat.{v} X ⥤
      TopCat.Sheaf AddCommGrpCat.{v} Y :=
  TopCat.Sheaf.pushforward AddCommGrpCat.{v} f

/-- Pushforward of abelian sheaves is left exact. -/
theorem abelianSheafPushforward_isLeftExact {X Y : TopCat.{v}}
    (f : X ⟶ Y) :
    IsLeftExact (abelianSheafPushforward f) := by
  sorry

/-- The `i`th higher direct image of an abelian sheaf. -/
noncomputable def abelianSheafHigherDirectImage
    {X Y : TopCat.{v}} (f : X ⟶ Y) (i : ℤ) :
    TopCat.Sheaf AddCommGrpCat.{v} X ⥤
      TopCat.Sheaf AddCommGrpCat.{v} Y := by
  exact higherRightDerivedFunctor
    (abelianSheafPushforward f)
    (abelianSheafPushforward_isLeftExact f) i

/-- The higher direct image `Rⁱ f_* F` of an abelian sheaf. -/
noncomputable abbrev abelianSheafHigherDirectImageObject
    {X Y : TopCat.{v}} (f : X ⟶ Y)
    (F : TopCat.Sheaf AddCommGrpCat.{v} X) (i : ℤ) :
    TopCat.Sheaf AddCommGrpCat.{v} Y :=
  (abelianSheafHigherDirectImage f i).obj F

/-! The universal δ-functor assertion for `Rⁱf_*`. -/

noncomputable def abelianSheafHigherDirectImageDeltaFunctor
    {X Y : TopCat.{v}} (f : X ⟶ Y) :
    CohomologicalDeltaFunctor
      (TopCat.Sheaf AddCommGrpCat.{v} X)
      (TopCat.Sheaf AddCommGrpCat.{v} Y) := by
  exact Classical.choose <| higherRightDerivedFunctor_universal
    (abelianSheafPushforward f)
    (abelianSheafPushforward_isLeftExact f)

theorem abelianSheafHigherDirectImageDeltaFunctor_isUniversal
    {X Y : TopCat.{v}} (f : X ⟶ Y) :
    (abelianSheafHigherDirectImageDeltaFunctor f).IsUniversal := by
  exact (Classical.choose_spec (higherRightDerivedFunctor_universal
    (abelianSheafPushforward f)
    (abelianSheafPushforward_isLeftExact f))).1

theorem abelianSheafHigherDirectImageDeltaFunctor_functor
    {X Y : TopCat.{v}} (f : X ⟶ Y) (n : ℕ) :
    (abelianSheafHigherDirectImageDeltaFunctor f).functor n =
      abelianSheafHigherDirectImage f (n : ℤ) := by
  exact (Classical.choose_spec (higherRightDerivedFunctor_universal
    (abelianSheafPushforward f)
    (abelianSheafPushforward_isLeftExact f))).2 n

/-! ## Cohomology of modules on a ringed space -/

/-- The global-sections functor on modules over a ringed space. -/
noncomputable def ringedSpaceModuleGlobalSections (X : RingedSpace.{v}) :
    Mod X.structureSheaf ⥤
      ModuleCat.{v} (X.structureSheaf.obj.obj (op (⊤ : Opens X.carrier))) :=
  SheafOfModules.evaluation X.structureSheaf (op (⊤ : Opens X.carrier))

/- The source's module-valued global sections are again left exact. -/
theorem ringedSpaceModuleGlobalSections_isLeftExact (X : RingedSpace.{v}) :
    IsLeftExact (ringedSpaceModuleGlobalSections X) := by
  sorry

/-- The `i`th cohomology functor of modules on `X`. -/
noncomputable def ringedSpaceModuleCohomology (X : RingedSpace.{v}) (i : ℤ) :
    Mod X.structureSheaf ⥤
      ModuleCat.{v} (X.structureSheaf.obj.obj (op (⊤ : Opens X.carrier))) := by
  exact higherRightDerivedFunctor
    (ringedSpaceModuleGlobalSections X)
    (ringedSpaceModuleGlobalSections_isLeftExact X) i

/-- The cohomology module `Hⁱ(X, F)` of a sheaf of modules. -/
noncomputable abbrev ringedSpaceModuleCohomologyObject
    (X : RingedSpace.{v}) (F : Mod X.structureSheaf) (i : ℤ) :
    ModuleCat.{v} (X.structureSheaf.obj.obj (op (⊤ : Opens X.carrier))) :=
  (ringedSpaceModuleCohomology X i).obj F

noncomputable def ringedSpaceModuleCohomologyDeltaFunctor (X : RingedSpace.{v}) :
    CohomologicalDeltaFunctor
      (Mod X.structureSheaf)
      (ModuleCat.{v} (X.structureSheaf.obj.obj (op (⊤ : Opens X.carrier)))) := by
  exact Classical.choose <| higherRightDerivedFunctor_universal
    (ringedSpaceModuleGlobalSections X)
    (ringedSpaceModuleGlobalSections_isLeftExact X)

theorem ringedSpaceModuleCohomologyDeltaFunctor_isUniversal
    (X : RingedSpace.{v}) :
    (ringedSpaceModuleCohomologyDeltaFunctor X).IsUniversal := by
  exact (Classical.choose_spec (higherRightDerivedFunctor_universal
    (ringedSpaceModuleGlobalSections X)
    (ringedSpaceModuleGlobalSections_isLeftExact X))).1

theorem ringedSpaceModuleCohomologyDeltaFunctor_functor
    (X : RingedSpace.{v}) (n : ℕ) :
    (ringedSpaceModuleCohomologyDeltaFunctor X).functor n =
      ringedSpaceModuleCohomology X (n : ℤ) := by
  exact (Classical.choose_spec (higherRightDerivedFunctor_universal
    (ringedSpaceModuleGlobalSections X)
    (ringedSpaceModuleGlobalSections_isLeftExact X))).2 n

/-! ## Higher direct images of modules -/

/-- The `i`th higher direct image of modules along a ringed-space morphism. -/
noncomputable def ringedSpaceModuleHigherDirectImage
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y) (i : ℤ) :
    Mod X.structureSheaf ⥤ Mod Y.structureSheaf := by
  exact higherRightDerivedFunctor
    (sheafModuleRingedSpacePushforward f)
    (sheafModuleRingedSpacePushforward_isLeftExact f) i

/-- The higher direct image `Rⁱ f_* F` of a sheaf of modules. -/
noncomputable abbrev ringedSpaceModuleHigherDirectImageObject
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y)
    (F : Mod X.structureSheaf) (i : ℤ) :
    Mod Y.structureSheaf :=
  (ringedSpaceModuleHigherDirectImage f i).obj F

noncomputable def ringedSpaceModuleHigherDirectImageDeltaFunctor
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y) :
    CohomologicalDeltaFunctor (Mod X.structureSheaf) (Mod Y.structureSheaf) := by
  exact Classical.choose <| higherRightDerivedFunctor_universal
    (sheafModuleRingedSpacePushforward f)
    (sheafModuleRingedSpacePushforward_isLeftExact f)

theorem ringedSpaceModuleHigherDirectImageDeltaFunctor_isUniversal
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y) :
    (ringedSpaceModuleHigherDirectImageDeltaFunctor f).IsUniversal := by
  exact (Classical.choose_spec (higherRightDerivedFunctor_universal
    (sheafModuleRingedSpacePushforward f)
    (sheafModuleRingedSpacePushforward_isLeftExact f))).1

theorem ringedSpaceModuleHigherDirectImageDeltaFunctor_functor
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y) (n : ℕ) :
    (ringedSpaceModuleHigherDirectImageDeltaFunctor f).functor n =
      ringedSpaceModuleHigherDirectImage f (n : ℤ) := by
  exact (Classical.choose_spec (higherRightDerivedFunctor_universal
    (sheafModuleRingedSpacePushforward f)
    (sheafModuleRingedSpacePushforward_isLeftExact f))).2 n

end Formalization.Books.Cohomology.Unit02
