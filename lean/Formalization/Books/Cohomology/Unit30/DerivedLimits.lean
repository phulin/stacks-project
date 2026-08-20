import Formalization.Books.Cohomology.Unit21.UnboundedComplexes
import Formalization.Books.Cohomology.Unit25.KInjectiveProperties
import Formalization.Books.Cohomology.Unit29.InverseSystemsAndCohomology
import Formalization.Books.Derived.Unit34.DerivedLimits
import Mathlib.Algebra.Homology.ExactSequence
import Mathlib.CategoryTheory.Functor.OfSequence
import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT

/-!
# Cohomology of Sheaves, Chapter 30: derived limits

This file records the source-facing interfaces for derived limits of sheaves
of modules.  The existing derived-category, unbounded-section, truncation,
and sheafification APIs are used directly; the propositions whose proofs use
the spectral sequence or a long exact sequence are deferred to the prove
stage.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Preadditive
open CategoryTheory.Pretriangulated
open Opposite
open TopologicalSpace
open Formalization.Books.Cohomology.Unit03
open Formalization.Books.Cohomology.Unit21
open Formalization.Books.Cohomology.Unit25
open Formalization.Books.Derived.Unit34
open Formalization.Books.MoreAlgebra.Unit87
open Formalization.Books.Modules.Unit03
open Formalization.Books.Sheaves.Unit06
open Formalization.Books.Sheaves.Unit10
open Formalization.Books.Sheaves.Unit25
open scoped CategoryTheory.Pretriangulated.Opposite ZeroObject

universe v

namespace Formalization.Books.Cohomology.Unit30

/-! ## The source notation `D(O_X)`, `Rlim`, and open cohomology -/

abbrev RingedSpace := Formalization.Books.Sheaves.Unit25.RingedSpace

abbrev ModuleCategory (X : RingedSpace.{v}) := Mod X.structureSheaf

abbrev ModuleDerived (X : RingedSpace.{v}) :=
  Formalization.Books.Cohomology.Unit21.ModuleDerived X

abbrev DerivedModuleInverseSystem (X : RingedSpace.{v}) :=
  DerivedInverseSystem (ModuleDerived X)

abbrev OpenModuleCategory (X : RingedSpace.{v}) (U : Opens X.carrier) :=
  ModuleCat.{v} (X.structureSheaf.obj.obj (op U))

abbrev OpenDerivedModuleCategory (X : RingedSpace.{v})
    (U : Opens X.carrier) :=
  DerivedCategory (OpenModuleCategory X U)

/- The source's `Rlim` is the chosen derived limit from the canonical
   derived-limit presentation.  The product hypothesis is explicit because
   it is the exact input required by the established categorical API. -/
noncomputable def derivedLimit
    (X : RingedSpace.{v}) (F : DerivedModuleInverseSystem X)
    [HasProduct (fun n : ℕ => F.obj (Opposite.op n))] : ModuleDerived X :=
  Formalization.Books.Derived.Unit34.derivedLimit F
    (Formalization.Books.Derived.Unit34.exists_isDerivedLimit F)

noncomputable def derivedLimitPresentation
    (X : RingedSpace.{v}) (F : DerivedModuleInverseSystem X)
    [HasProduct (fun n : ℕ => F.obj (Opposite.op n))] :
    DerivedLimitPresentation F (derivedLimit X F) :=
  Classical.choice <|
    Formalization.Books.Derived.Unit34.derivedLimit_isDerivedLimit F
      (Formalization.Books.Derived.Unit34.exists_isDerivedLimit F)

noncomputable def openCohomologyModule
    (X : RingedSpace.{v}) (U : Opens X.carrier)
    (K : ModuleDerived X) (m : ℤ) : OpenModuleCategory X U :=
  (derivedSectionsCohomology X U m).obj K

abbrev openCohomologyGroup
    (X : RingedSpace.{v}) (U : Opens X.carrier)
    (K : ModuleDerived X) (m : ℤ) : AddCommGrpCat.{v} :=
  (forget₂ (OpenModuleCategory X U) AddCommGrpCat).obj
    (openCohomologyModule X U K m)

abbrev cohomologySheaf
    (X : RingedSpace.{v}) (K : ModuleDerived X) (m : ℤ) :
    ModuleCategory X :=
  (DerivedCategory.homologyFunctor (ModuleCategory X) m).obj K

abbrev openSheafCohomologyGroup
    (X : RingedSpace.{v}) (U : Opens X.carrier)
    (F : ModuleCategory X) (p : ℤ) : AddCommGrpCat.{v} :=
  (forget₂ (OpenModuleCategory X U) AddCommGrpCat).obj
    ((derivedSectionsCohomology X U p).obj
      ((DerivedCategory.singleFunctor (ModuleCategory X) 0).obj F))

noncomputable def openCohomologySystem
    (X : RingedSpace.{v}) (U : Opens X.carrier)
    (F : DerivedModuleInverseSystem X) (m : ℤ) :
    ℕᵒᵖ ⥤ AddCommGrpCat.{v} :=
  F ⋙ derivedSections X U ⋙
    DerivedCategory.homologyFunctor (OpenModuleCategory X U) m ⋙
    forget₂ (OpenModuleCategory X U) AddCommGrpCat

noncomputable def openSheafSectionsSystem
    (X : RingedSpace.{v}) (U : Opens X.carrier)
    (F : DerivedModuleInverseSystem X) (q : ℤ) :
    ℕᵒᵖ ⥤ AddCommGrpCat.{v} :=
  F ⋙ DerivedCategory.homologyFunctor (ModuleCategory X) q ⋙
    ringedSpaceModuleSectionsFunctor X U ⋙
    forget₂ (OpenModuleCategory X U) AddCommGrpCat

noncomputable def sheafCohomologySystem
    (X : RingedSpace.{v}) (U : Opens X.carrier)
    (F : ℕᵒᵖ ⥤ ModuleCategory X) (p : ℤ) :
    ℕᵒᵖ ⥤ AddCommGrpCat.{v} :=
  F ⋙ ringedSpaceModuleSectionsCohomology X U p ⋙
    forget₂ (OpenModuleCategory X U) AddCommGrpCat

noncomputable def cohomologySheafSystem
    (X : RingedSpace.{v}) (F : DerivedModuleInverseSystem X) (q : ℤ) :
    ℕᵒᵖ ⥤ ModuleCategory X :=
  F ⋙ DerivedCategory.homologyFunctor (ModuleCategory X) q

/-! ## Exact sequences over an open -/

def DerivedLimitCohomologyExactSequence
    (X : RingedSpace.{v}) (U : Opens X.carrier)
    (F : DerivedModuleInverseSystem X) (m : ℤ)
    [HasProduct (fun n : ℕ => F.obj (Opposite.op n))]
    [HasInjectiveResolutions (ℕᵒᵖ ⥤ AddCommGrpCat.{v})] : Prop :=
  ∃ α : derivedLimitGroup (openCohomologySystem X U F (m - 1)) 1 ⟶
      openCohomologyGroup X U (derivedLimit X F) m,
    ∃ β : openCohomologyGroup X U (derivedLimit X F) m ⟶
      limit (openCohomologySystem X U F m),
      (ComposableArrows.mk₄
        (0 : (0 : AddCommGrpCat.{v}) ⟶
          derivedLimitGroup (openCohomologySystem X U F (m - 1)) 1)
        α β
        (0 : limit (openCohomologySystem X U F m) ⟶
          (0 : AddCommGrpCat.{v}))).Exact

theorem derivedLimit_cohomology_exact_sequence
    (X : RingedSpace.{v}) (U : Opens X.carrier)
    (F : DerivedModuleInverseSystem X) (m : ℤ)
    [HasProduct (fun n : ℕ => F.obj (Opposite.op n))]
    [HasInjectiveResolutions (ℕᵒᵖ ⥤ AddCommGrpCat.{v})] :
    DerivedLimitCohomologyExactSequence X U F m := by
  sorry

/-! ## Commutation with derived limits -/

theorem derivedSections_commutes_with_derivedLimit
    (X : RingedSpace.{v}) (U : Opens X.carrier)
    (F : DerivedModuleInverseSystem X)
    [HasProduct (fun n : ℕ => F.obj (Opposite.op n))]
    [HasProduct (fun n : ℕ =>
      (derivedSections X U).obj (F.obj (Opposite.op n)))] :
    Nonempty
      ((derivedSections X U).obj (derivedLimit X F) ≅
        Formalization.Books.Derived.Unit34.derivedLimit
          (F ⋙ derivedSections X U)
          (Formalization.Books.Derived.Unit34.exists_isDerivedLimit
            (F ⋙ derivedSections X U))) := by
  sorry

theorem derivedPushforward_commutes_with_derivedLimit
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y)
    (F : DerivedModuleInverseSystem X)
    [HasProduct (fun n : ℕ => F.obj (Opposite.op n))]
    [HasProduct (fun n : ℕ =>
      (derivedPushforward f).obj (F.obj (Opposite.op n)))] :
    Nonempty
      ((derivedPushforward f).obj (derivedLimit X F) ≅
        Formalization.Books.Derived.Unit34.derivedLimit
          (F ⋙ derivedPushforward f)
          (Formalization.Books.Derived.Unit34.exists_isDerivedLimit
            (F ⋙ derivedPushforward f))) := by
  sorry

/-! ## The cohomology-sheaf and presheaf comparison -/

noncomputable def cohomologySheafificationData
    (X : RingedSpace.{v}) (K : ModuleDerived X) (m : ℤ) :
    SheafificationCohomologyData X K m :=
  Classical.choice (sheafification_of_unbounded_cohomology X K m)

noncomputable def cohomologyPresheaf
    (X : RingedSpace.{v}) (K : ModuleDerived X) (m : ℤ) :
    PMod X.structureSheaf.obj :=
  (cohomologySheafificationData X K m).presheaf

theorem cohomologyPresheaf_value_comparison
    (X : RingedSpace.{v}) (K : ModuleDerived X) (m : ℤ)
    (U : Opens X.carrier) :
    Nonempty
      ((cohomologyPresheaf X K m).obj (op U) ≅
        openCohomologyModule X U K m) := by
  exact (cohomologySheafificationData X K m).value_comparison U

theorem cohomologySheaf_is_sheafification
    (X : RingedSpace.{v}) (K : ModuleDerived X) (m : ℤ) :
    Nonempty
      ((PresheafOfModules.sheafification (𝟙 X.structureSheaf.obj)).obj
          (cohomologyPresheaf X K m) ≅ cohomologySheaf X K m) := by
  exact (cohomologySheafificationData X K m).sheafification_comparison

/- The source warns that sheafification need not commute with the inverse
   limit of the displayed presheaves.  Accordingly, the declarations above
   provide the individual sheafification comparisons but assert no spurious
   isomorphism between a limit of presheaves and a limit of sheaves. -/

/-! ## Ordinary and derived limits of systems of sheaves -/

noncomputable def sheafSystemDerivedLimit
    (X : RingedSpace.{v}) (F : ℕᵒᵖ ⥤ ModuleCategory X)
    [HasProduct (fun n : ℕ =>
      (DerivedCategory.singleFunctor (ModuleCategory X) 0).obj
        (F.obj (Opposite.op n)))] : ModuleDerived X :=
  derivedLimit X
    (F ⋙ DerivedCategory.singleFunctor (ModuleCategory X) 0)

def OpenCoveringBy
    (X : RingedSpace.{v}) (B : Set (Opens X.carrier)) : Prop :=
  ∀ U : Opens X.carrier, ∃ ι : Type v, ∃ V : ι → Opens X.carrier,
    (∀ i, V i ∈ B) ∧ (⋃ i, (V i : Set X.carrier)) = (U : Set X.carrier)

def FundamentalNeighborhoodSystem
    (X : RingedSpace.{v}) (x : X.carrier)
    (𝔘 : Set (Opens X.carrier)) : Prop :=
  (∀ U, U ∈ 𝔘 → x ∈ (U : Set X.carrier)) ∧
    ∀ U, x ∈ (U : Set X.carrier) → ∃ V, V ∈ 𝔘 ∧ V ≤ U

def OpenCohomologyVanishing
    (X : RingedSpace.{v}) (U : Opens X.carrier)
    (F : ModuleCategory X) (p : ℤ) : Prop :=
  IsZero (openSheafCohomologyGroup X U F p)

/- The quasi-coherent/surjective-system application mentioned before the
   source lemma is subsumed by the following more general interface. -/
theorem inverseLimit_is_derivedLimit
    (X : RingedSpace.{v}) (F : ℕᵒᵖ ⥤ ModuleCategory X)
    (B : Set (Opens X.carrier))
    [HasProduct (fun n : ℕ =>
      (DerivedCategory.singleFunctor (ModuleCategory X) 0).obj
        (F.obj (Opposite.op n)))]
    [HasInjectiveResolutions (ℕᵒᵖ ⥤ AddCommGrpCat.{v})] :
    (OpenCoveringBy X B) →
      (∀ U ∈ B, ∀ n : ℕ, ∀ p : ℤ, 0 < p →
        OpenCohomologyVanishing X U (F.obj (Opposite.op n)) p) →
      (∀ U ∈ B, IsZero (derivedLimitGroup
        (sheafCohomologySystem X U F 0) 1)) →
      Nonempty (sheafSystemDerivedLimit X F ≅
        (DerivedCategory.singleFunctor (ModuleCategory X) 0).obj (limit F)) ∧
      (∀ U ∈ B, ∀ p : ℤ, 0 < p →
        OpenCohomologyVanishing X U (limit F) p) := by
  sorry

/-! ## Stalk injectivity for a derived limit -/

noncomputable def derivedLimitCohomologyStalkMap
    (X : RingedSpace.{v}) (x : X.carrier)
    (F : DerivedModuleInverseSystem X) (m : ℤ) (n : ℕ)
    [HasProduct (fun n : ℕ => F.obj (Opposite.op n))] :
    (sheafModuleStalkFunctor X.structureSheaf x).obj
        (cohomologySheaf X (derivedLimit X F) m) ⟶
      (sheafModuleStalkFunctor X.structureSheaf x).obj
        (cohomologySheaf X (F.obj (Opposite.op n)) m) :=
  (sheafModuleStalkFunctor X.structureSheaf x).map
    ((DerivedCategory.homologyFunctor (ModuleCategory X) m).map
      ((derivedLimitPresentation X F).inclusion ≫
        (derivedLimitPresentation X F).product.projection n))

theorem cohomology_derivedLimit_stalk_mono
    (X : RingedSpace.{v}) (x : X.carrier)
    (F : DerivedModuleInverseSystem X) (m : ℤ) (n₀ : ℕ)
    (𝔘 : Set (Opens X.carrier))
    [HasProduct (fun n : ℕ => F.obj (Opposite.op n))]
    [HasInjectiveResolutions (ℕᵒᵖ ⥤ AddCommGrpCat.{v})]
    (h𝔘 : FundamentalNeighborhoodSystem X x 𝔘)
    (h₁ : ∀ U, U ∈ 𝔘 → IsZero
      (derivedLimitGroup (openCohomologySystem X U F (m - 1)) 1))
    (h₂ : ∀ n (hn : n₀ ≤ n), ∀ U, U ∈ 𝔘 →
      Mono ((openCohomologySystem X U F m).map
        (opHomOfLE hn))) :
    Mono (derivedLimitCohomologyStalkMap X x F m n₀) := by
  sorry

/-! ## Truncation systems and the local limit criterion -/

noncomputable def truncationInverseSystem
    (X : RingedSpace.{v}) (E : ModuleDerived X) :
    DerivedModuleInverseSystem X :=
  let t := DerivedCategory.TStructure.t (C := ModuleCategory X)
  Functor.ofOpSequence
    (X := fun n : ℕ => (t.truncGE (-((n : ℤ) + 1))).obj E)
    (fun n =>
      (t.natTransTruncGEOfLE (-((n : ℤ) + 2)) (-((n : ℤ) + 1))
        (by omega)).app E)

noncomputable def truncationCanonicalMap
    (X : RingedSpace.{v}) (E : ModuleDerived X) (n : ℕ) :
    E ⟶ (truncationInverseSystem X E).obj (Opposite.op n) :=
  let t := DerivedCategory.TStructure.t (C := ModuleCategory X)
  (t.truncGEπ (-((n : ℤ) + 1))).app E

noncomputable def truncationDerivedLimit
    (X : RingedSpace.{v}) (E : ModuleDerived X)
    [HasProduct (fun n : ℕ =>
      (truncationInverseSystem X E).obj (Opposite.op n))] : ModuleDerived X :=
  derivedLimit X (truncationInverseSystem X E)

noncomputable def truncationDerivedLimitPresentation
    (X : RingedSpace.{v}) (E : ModuleDerived X)
    [HasProduct (fun n : ℕ =>
      (truncationInverseSystem X E).obj (Opposite.op n))] :
    DerivedLimitPresentation (truncationInverseSystem X E)
      (truncationDerivedLimit X E) :=
  derivedLimitPresentation X (truncationInverseSystem X E)

def IsIsoToTruncationDerivedLimit
    (X : RingedSpace.{v}) (E : ModuleDerived X)
    [HasProduct (fun n : ℕ =>
      (truncationInverseSystem X E).obj (Opposite.op n))] : Prop :=
  ∃ c : E ⟶ truncationDerivedLimit X E,
    (∀ n, c ≫
        (truncationDerivedLimitPresentation X E).inclusion ≫
          (truncationDerivedLimitPresentation X E).product.projection n =
      truncationCanonicalMap X E n) ∧ IsIso c

abbrev openCohomologyOfCohomologySheaf
    (X : RingedSpace.{v}) (U : Opens X.carrier)
    (E : ModuleDerived X) (p q : ℤ) : AddCommGrpCat.{v} :=
  openSheafCohomologyGroup X U (cohomologySheaf X E q) p

theorem isIso_to_truncationDerivedLimit_of_pointwise_vanishing
    (X : RingedSpace.{v}) (E : ModuleDerived X)
    (p : X.carrier → ℤ → ℤ)
    (𝔘 : ∀ x : X.carrier, Set (Opens X.carrier))
    [HasProduct (fun n : ℕ =>
      (truncationInverseSystem X E).obj (Opposite.op n))]
    (h𝔘 : ∀ x, FundamentalNeighborhoodSystem X x (𝔘 x))
    (hvanish : ∀ x m U r, U ∈ 𝔘 x → r > p x m →
      IsZero (openCohomologyOfCohomologySheaf X U E r (m - r))) :
    IsIsoToTruncationDerivedLimit X E := by
  sorry

theorem isIso_to_truncationDerivedLimit_of_spaltenstein_vanishing
    (X : RingedSpace.{v}) (E : ModuleDerived X)
    (d : X.carrier → ℕ)
    (𝔘 : ∀ x : X.carrier, Set (Opens X.carrier))
    [HasProduct (fun n : ℕ =>
      (truncationInverseSystem X E).obj (Opposite.op n))]
    (h𝔘 : ∀ x, FundamentalNeighborhoodSystem X x (𝔘 x))
    (hvanish : ∀ x U r q, U ∈ 𝔘 x →
      d x < r → q < 0 →
      IsZero (openCohomologyOfCohomologySheaf X U E r q)) :
    IsIsoToTruncationDerivedLimit X E := by
  sorry

theorem isIso_to_truncationDerivedLimit_of_covering_vanishing
    (X : RingedSpace.{v}) (E : ModuleDerived X)
    (p : ℤ → ℤ) (B : Set (Opens X.carrier))
    [HasProduct (fun n : ℕ =>
      (truncationInverseSystem X E).obj (Opposite.op n))]
    (hcover : OpenCoveringBy X B)
    (hvanish : ∀ U m r, U ∈ B → r > p m →
      IsZero (openCohomologyOfCohomologySheaf X U E r (m - r))) :
    IsIsoToTruncationDerivedLimit X E := by
  sorry

theorem isIso_to_truncationDerivedLimit_of_basis_dimension_vanishing
    (X : RingedSpace.{v}) (E : ModuleDerived X)
    (d : ℕ) (B : Set (Opens X.carrier))
    [HasProduct (fun n : ℕ =>
      (truncationInverseSystem X E).obj (Opposite.op n))]
    (hB : Opens.IsBasis B)
    (hvanish : ∀ U r q, U ∈ B → d < r → q < 0 →
      IsZero (openCohomologyOfCohomologySheaf X U E r q)) :
    IsIsoToTruncationDerivedLimit X E := by
  sorry

/-! ## Cohomology computations -/

theorem cohomology_over_open_of_vanishing
    (X : RingedSpace.{v}) (K : ModuleDerived X)
    (B : Set (Opens X.carrier))
    (hcover : OpenCoveringBy X B)
    (hvanish : ∀ U p q, U ∈ B → 0 < p →
      IsZero (openSheafCohomologyGroup X U (cohomologySheaf X K q) p)) :
    ∀ U ∈ B, ∀ q : ℤ,
      Nonempty
        (openCohomologyModule X U K q ≅
          (ringedSpaceModuleSectionsFunctor X U).obj
            (cohomologySheaf X K q)) := by
  sorry

theorem derivedLimit_cohomology_sheaf_iso
    (X : RingedSpace.{v}) (F : DerivedModuleInverseSystem X)
    (B : Set (Opens X.carrier))
    [HasProduct (fun n : ℕ => F.obj (Opposite.op n))]
    [HasInjectiveResolutions (ℕᵒᵖ ⥤ AddCommGrpCat.{v})]
    (hcover : OpenCoveringBy X B)
    (hvanish : ∀ U q n p, U ∈ B → 0 < p →
      IsZero (openSheafCohomologyGroup X U
        (cohomologySheaf X (F.obj (Opposite.op n)) q) p))
    (hR1 : ∀ U q, U ∈ B → IsZero
      (derivedLimitGroup (openSheafSectionsSystem X U F q) 1)) :
    ∀ q : ℤ, Nonempty
      ((DerivedCategory.homologyFunctor (ModuleCategory X) q).obj
          (derivedLimit X F) ≅
        limit (cohomologySheafSystem X F q)) := by
  sorry

end Formalization.Books.Cohomology.Unit30
