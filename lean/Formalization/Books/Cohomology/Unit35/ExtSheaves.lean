import Formalization.Books.Cohomology.Unit34.InternalHom
import Formalization.Books.Homology.Unit24.FilteredComplexes
import Formalization.Books.Sheaves.Unit20.SheafificationOfPresheavesOfModules

/-!
# Cohomology of Sheaves, Chapter 35: Ext sheaves

This file formalizes the definition of sheaf Ext, its sectionwise
description, and the spectral-sequence statement in the source section.
-/

noncomputable section

open CategoryTheory
open Opposite
open TopologicalSpace
open Formalization.Books.Cohomology.Unit33
open Formalization.Books.Cohomology.Unit34
open Formalization.Books.Derived.Unit08
open Formalization.Books.Sheaves.Unit06

universe v

namespace Formalization.Books.Cohomology.Unit35

/-! ## The derived internal Hom and sheaf Ext -/

abbrev RingedSpace := Formalization.Books.Cohomology.Unit34.RingedSpace

abbrev Complex (X : RingedSpace.{v}) :=
  Formalization.Books.Cohomology.Unit34.Complex X

abbrev Derived (X : RingedSpace.{v}) :=
  Formalization.Books.Cohomology.Unit34.Derived X

/- The optional subscript `O_X` in the source is notation only; it does not
   define a second mathematical object. -/

/- The cohomology sheaf `Hⁿ(RSheafHom(K, L))`. -/
noncomputable abbrev sheafExt
    (X : RingedSpace.{v}) (K L : Derived X) (n : ℤ) :
    SheafModule X :=
  (DerivedCategory.homologyFunctor (SheafModule X) n).obj
    (derivedSheafHom X K L)

/- The global derived Hom group used for the abutment notation
   `Extⁿ_{D(O_X)}(K, L)`. -/
noncomputable abbrev derivedExtModule
    (X : RingedSpace.{v}) (K L : Derived X) (n : ℤ) :
    GlobalModule X :=
  (globalCohomologyObject X n).obj (derivedSheafHom X K L)

noncomputable abbrev derivedExtGroup
    (X : RingedSpace.{v}) (K L : Derived X) (n : ℤ) :
    AddCommGrpCat.{v} :=
  (forget₂ (GlobalModule X) AddCommGrpCat).obj
    (derivedExtModule X K L n)

/- The rule on an open obtained by taking the Ext group in the derived
   category of the restricted ringed space. -/
noncomputable abbrev localDerivedExtGroup
    (X : RingedSpace.{v}) (U : Opens X.carrier)
    (K L : Derived X) (n : ℤ) :
  AddCommGrpCat.{v} :=
  derivedExtGroup (Formalization.Books.Cohomology.Unit33.openSpace X U)
    ((derivedRestriction X U).obj K) ((derivedRestriction X U).obj L) n

/- The source's sectionwise rule is already the local Ext group. -/
noncomputable abbrev sheafExtSections
    (X : RingedSpace.{v}) (U : Opens X.carrier)
    (K L : Derived X) (n : ℤ) : AddCommGrpCat.{v} :=
  localDerivedExtGroup X U K L n

theorem sheafExtSections_iso_localDerivedExt
    (X : RingedSpace.{v}) (U : Opens X.carrier)
    (K L : Derived X) (n : ℤ) :
    Nonempty (sheafExtSections X U K L n ≅
      localDerivedExtGroup X U K L n) :=
  ⟨Iso.refl _⟩

/-! ## Sheafification of the sectionwise rule -/

structure SheafExtSheafificationData
    (X : RingedSpace.{v}) (K L : Derived X) (n : ℤ) where
  presheaf :
    Formalization.Books.Sheaves.Unit06.PMod
      (Formalization.Books.Sheaves.Unit17.commRingSheafToRingSheaf
        X.structureSheaf).obj
  value_comparison : ∀ U : Opens X.carrier, Nonempty
    ((forget₂ _ AddCommGrpCat).obj (presheaf.obj (op U)) ≅
      sheafExtSections X U K L n)
  sheafification_comparison : Nonempty
    ((PresheafOfModules.sheafification
      (𝟙 (Formalization.Books.Sheaves.Unit17.commRingSheafToRingSheaf
        X.structureSheaf).obj)).obj
        presheaf ≅ sheafExt X K L n)

theorem exists_sheafExtSheafificationData
    (X : RingedSpace.{v}) (K L : Derived X) (n : ℤ) :
    Nonempty (SheafExtSheafificationData X K L n) := by
  sorry

noncomputable def sheafExtPresheaf
    (X : RingedSpace.{v}) (K L : Derived X) (n : ℤ) :
    Formalization.Books.Sheaves.Unit06.PMod
      (Formalization.Books.Sheaves.Unit17.commRingSheafToRingSheaf
        X.structureSheaf).obj :=
  (Classical.choice (exists_sheafExtSheafificationData X K L n)).presheaf

theorem sheafExtPresheaf_value_comparison
    (X : RingedSpace.{v}) (K L : Derived X) (n : ℤ)
    (U : Opens X.carrier) :
    Nonempty ((forget₂ _ AddCommGrpCat).obj
      ((sheafExtPresheaf X K L n).obj (op U)) ≅
      sheafExtSections X U K L n) := by
  exact (Classical.choice
    (exists_sheafExtSheafificationData X K L n)).value_comparison U

theorem sheafExt_is_sheafification
    (X : RingedSpace.{v}) (K L : Derived X) (n : ℤ) :
    Nonempty
      ((PresheafOfModules.sheafification
        (𝟙 (Formalization.Books.Sheaves.Unit17.commRingSheafToRingSheaf
          X.structureSheaf).obj)).obj
          (sheafExtPresheaf X K L n) ≅ sheafExt X K L n) := by
  exact (Classical.choice
    (exists_sheafExtSheafificationData X K L n)).sheafification_comparison

/-! ## Boundedness hypotheses for the spectral sequence -/

def derivedIsBoundedBelow (X : RingedSpace.{v}) (K : Derived X) : Prop :=
  ∃ C : Complex X, Nonempty ((DerivedCategory.Q.obj C) ≅ K) ∧
    IsBoundedBelow C

def derivedIsBoundedAbove (X : RingedSpace.{v}) (K : Derived X) : Prop :=
  ∃ C : Complex X, Nonempty ((DerivedCategory.Q.obj C) ≅ K) ∧
    IsBoundedAbove C

def ExtSheafConvergenceHypotheses
    (X : RingedSpace.{v}) (K L : Derived X) : Prop :=
  derivedIsBoundedAbove X K ∧ derivedIsBoundedBelow X L

/-! ## The `E₂` page and abutment -/

noncomputable abbrev extSheafCohomologyGroup
    (X : RingedSpace.{v}) (K L : Derived X)
    (p q : ℤ) : AddCommGrpCat.{v} :=
  (forget₂ (GlobalModule X) AddCommGrpCat).obj
    ((globalCohomologyObject X p).obj
      ((DerivedCategory.singleFunctor (SheafModule X) 0).obj
        (sheafExt X K L q)))

abbrev ExtSheafFilteredComplex :=
  Formalization.Books.Homology.Unit24.FilteredComplex AddCommGrpCat.{v}

abbrev ExtSheafFilteredSpectralSequence
    (T : ExtSheafFilteredComplex) :=
  Formalization.Books.Homology.Unit24.FilteredComplexSpectralSequence T

structure ExtSheafSpectralSequenceData
    (X : RingedSpace.{v}) (K L : Derived X) where
  globalFiltered : ExtSheafFilteredComplex
  spectral : ExtSheafFilteredSpectralSequence globalFiltered
  e₂_page : ∀ p q : ℤ, Nonempty
    (spectral.page 2 (p, q) ≅ extSheafCohomologyGroup X K L p q)
  abutment_iso : ∀ n : ℤ, Nonempty
    (Formalization.Books.Homology.Unit24.filteredComplexCohomology
        globalFiltered n ≅ derivedExtGroup X K L n)
  converges_under_favorable_hypotheses :
    ExtSheafConvergenceHypotheses X K L →
      Formalization.Books.Homology.Unit24.filteredComplexConvergesAt
        globalFiltered spectral

theorem exists_extSheafSpectralSequence
    (X : RingedSpace.{v}) (K L : Derived X) :
    Nonempty (ExtSheafSpectralSequenceData X K L) := by
  sorry

noncomputable def extSheafSpectralSequence
    (X : RingedSpace.{v}) (K L : Derived X) :
    ExtSheafSpectralSequenceData X K L :=
  Classical.choice (exists_extSheafSpectralSequence X K L)

theorem extSheafSpectralSequence_e₂_page
    (X : RingedSpace.{v}) (K L : Derived X) (p q : ℤ) :
    Nonempty
      ((extSheafSpectralSequence X K L).spectral.page 2 (p, q) ≅
        extSheafCohomologyGroup X K L p q) :=
  (extSheafSpectralSequence X K L).e₂_page p q

theorem extSheafSpectralSequence_abutment_iso
    (X : RingedSpace.{v}) (K L : Derived X) (n : ℤ) :
    Nonempty
      (Formalization.Books.Homology.Unit24.filteredComplexCohomology
          (extSheafSpectralSequence X K L).globalFiltered n ≅
        derivedExtGroup X K L n) :=
  (extSheafSpectralSequence X K L).abutment_iso n

theorem extSheafSpectralSequence_converges
  (X : RingedSpace.{v}) (K L : Derived X)
    (hK : derivedIsBoundedAbove X K) (hL : derivedIsBoundedBelow X L) :
    Formalization.Books.Homology.Unit24.filteredComplexConvergesAt
      (extSheafSpectralSequence X K L).globalFiltered
      (extSheafSpectralSequence X K L).spectral :=
  (extSheafSpectralSequence X K L).converges_under_favorable_hypotheses
    ⟨hK, hL⟩

end Formalization.Books.Cohomology.Unit35
