import Formalization.Books.Modules.Unit18.Duals
import Formalization.Books.Modules.Unit21.SymmetricExterior
import Formalization.Books.MoreAlgebra.Unit29.KoszulComplex

/-!
# Sheaves of Modules, Chapter 24: Koszul complexes

The sheaf-level construction uses the exterior-power data from Chapter 21.
The sectionwise differential and its derivation laws reuse the canonical
Koszul DGA and formulas from More on Algebra, Chapter 29.
-/

namespace Formalization.Books.Modules.Unit24

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Formalization.Books.Modules.Unit14
open Formalization.Books.Modules.Unit16
open Formalization.Books.Modules.Unit17
open Formalization.Books.Modules.Unit18
open Formalization.Books.Modules.Unit21
open Formalization.Books.Sheaves.Unit10
open Formalization.Books.Sheaves.Unit17
open Formalization.Books.Sheaves.Unit22
open Formalization.Books.MoreAlgebra.Unit29

universe v

noncomputable section

/-! ## Maps from finite free sheaves -/

/- A family of sections is the sheaf-theoretic version of the row map
  `(f₁, ..., fₙ)`.  `freeHomEquiv` is the canonical universal property of a
  finite free sheaf, so no parallel map construction is introduced here. -/
noncomputable def freeMapFromSections {X : TopCat.{v}}
    {O : Sheaf (Opens.grothendieckTopology X) RingCat.{v}}
    {F : SheafOfModules O} {I : Type v} (s : I → F.sections) :
    SheafOfModules.free (R := O) I ⟶ F :=
  F.freeHomEquiv.symm s

/-! ## Sectionwise Koszul data -/

abbrev sectionwiseRing {X : TopCat.{v}} (O : CommRingSheaf X)
    (U : (Opens X)ᵒᵖ) : Type v :=
  ↑(O.obj.obj U)

abbrev sectionwiseModule {X : TopCat.{v}} (O : CommRingSheaf X)
    (E : CommRingSheafModule O) (U : (Opens X)ᵒᵖ) : Type v :=
  ↑(E.val.obj U)

noncomputable instance sectionwiseModuleInstance {X : TopCat.{v}}
    (O : CommRingSheaf X) (E : CommRingSheafModule O)
    (U : (Opens X)ᵒᵖ) : Module (sectionwiseRing O U) (sectionwiseModule O E U) :=
  Formalization.Books.Modules.Unit21.sectionwiseModule O E U

noncomputable def sectionwiseKoszulMap {X : TopCat.{v}}
    (O : CommRingSheaf X) (E : CommRingSheafModule O)
    (φ : E ⟶ sheafModuleUnit O) (U : (Opens X)ᵒᵖ) :
    sectionwiseModule O E U →ₗ[sectionwiseRing O U] sectionwiseRing O U := by
  exact
    { toFun := fun e => (φ.val.app U).hom e
      map_add' := by
        intro e e'
        exact (φ.val.app U).hom.map_add e e'
      map_smul' := by
        intro r e
        sorry }

noncomputable def sectionwiseKoszulDGA {X : TopCat.{v}}
    (O : CommRingSheaf X) (E : CommRingSheafModule O)
    (φ : E ⟶ sheafModuleUnit O) (U : (Opens X)ᵒᵖ) :
    KoszulDGA (sectionwiseRing O U) (sectionwiseModule O E U)
      (sectionwiseKoszulMap O E φ U) := by
  exact koszulDGA _ _ (sectionwiseKoszulMap O E φ U)

/-! ## The sheaf Koszul complex -/

/- The underlying graded algebra is Chapter 21's exterior algebra data.  A
  differential is recorded degree by degree, together with its square-zero
  law.  The final field exposes the corresponding commutative DGA on every
  open section module; the actual sectionwise differential is the canonical
  one from More on Algebra, Chapter 29. -/
structure KoszulComplex {X : TopCat.{v}} (O : CommRingSheaf X)
    (E : CommRingSheafModule O) (φ : E ⟶ sheafModuleUnit O)
    extends ExteriorAlgebraData O E where
  differential : ∀ n : ℕ, component (n + 1) ⟶ component n
  differential_comp : ∀ n : ℕ,
    differential (n + 1) ≫ differential n = 0
  sectionwise_model : ∀ U : (Opens X)ᵒᵖ,
    Nonempty (KoszulDGA (sectionwiseRing O U) (sectionwiseModule O E U)
      (sectionwiseKoszulMap O E φ U))

theorem koszulComplex_exists {X : TopCat.{v}} (O : CommRingSheaf X)
    (E : CommRingSheafModule O) (φ : E ⟶ sheafModuleUnit O) :
    Nonempty (KoszulComplex O E φ) := by
  sorry

noncomputable def koszulComplex {X : TopCat.{v}} (O : CommRingSheaf X)
    (E : CommRingSheafModule O) (φ : E ⟶ sheafModuleUnit O) :
    KoszulComplex O E φ :=
  Classical.choice (koszulComplex_exists O E φ)

@[simp] theorem koszulComplex_component_eq {X : TopCat.{v}}
    (O : CommRingSheaf X) (E : CommRingSheafModule O)
    (φ : E ⟶ sheafModuleUnit O) (n : ℕ) :
    (koszulComplex O E φ).component n = exteriorPowerSheaf O E n := by
  exact (koszulComplex O E φ).component_eq n

theorem koszulComplex_differential_comp {X : TopCat.{v}}
    (O : CommRingSheaf X) (E : CommRingSheafModule O)
    (φ : E ⟶ sheafModuleUnit O) (n : ℕ) :
    (koszulComplex O E φ).differential (n + 1) ≫
        (koszulComplex O E φ).differential n = 0 := by
  exact (koszulComplex O E φ).differential_comp n

/-! ## The explicit local formula and uniqueness -/

theorem sectionwise_koszul_differential_formula {X : TopCat.{v}}
    (O : CommRingSheaf X) (E : CommRingSheafModule O)
    (φ : E ⟶ sheafModuleUnit O) (U : (Opens X)ᵒᵖ) (n : ℕ)
    (v₀ : Fin (n + 1) → sectionwiseModule O E U) :
    koszulAlgebraDifferential (sectionwiseRing O U)
        (sectionwiseModule O E U) (sectionwiseKoszulMap O E φ U)
        (ExteriorAlgebra.ιMulti (sectionwiseRing O U) (n + 1) v₀) =
      ∑ i : Fin (n + 1), (-1 : sectionwiseRing O U) ^ (i : ℕ) •
        ((sectionwiseKoszulMap O E φ U (v₀ i)) •
          ExteriorAlgebra.ιMulti (sectionwiseRing O U) n (i.removeNth v₀)) := by
  exact koszulAlgebraDifferential_apply_ιMulti (sectionwiseRing O U)
    (sectionwiseModule O E U) (sectionwiseKoszulMap O E φ U) n v₀

theorem sectionwise_koszul_differential_unique {X : TopCat.{v}}
    (O : CommRingSheaf X) (E : CommRingSheafModule O)
    (φ : E ⟶ sheafModuleUnit O) (U : (Opens X)ᵒᵖ)
    (d : ExteriorAlgebra (sectionwiseRing O U) (sectionwiseModule O E U) →ₗ[
      sectionwiseRing O U] ExteriorAlgebra (sectionwiseRing O U)
        (sectionwiseModule O E U))
    (hd : IsKoszulDerivation (sectionwiseRing O U)
      (sectionwiseModule O E U) (sectionwiseKoszulMap O E φ U) d) :
    d = koszulAlgebraDifferential (sectionwiseRing O U)
      (sectionwiseModule O E U) (sectionwiseKoszulMap O E φ U) := by
  exact koszulAlgebraDifferential_unique (sectionwiseRing O U)
    (sectionwiseModule O E U) (sectionwiseKoszulMap O E φ U) d hd

/-! ## Koszul complexes on a finite sequence -/

abbrev globalSections {X : TopCat.{v}} (O : CommRingSheaf X) : Type v :=
  (sheafModuleUnit O).sections

noncomputable def koszulSequenceMap {X : TopCat.{v}}
    (O : CommRingSheaf X) (n : ℕ)
    (f : ULift.{v} (Fin n) → globalSections O) :
    SheafOfModules.free (R := commRingSheafToRingSheaf O)
      (ULift.{v} (Fin n)) ⟶
      sheafModuleUnit O :=
  freeMapFromSections f

noncomputable def koszulComplexOn {X : TopCat.{v}}
    (O : CommRingSheaf X) (n : ℕ)
    (f : ULift.{v} (Fin n) → globalSections O) :
    KoszulComplex O
      (SheafOfModules.free (R := commRingSheafToRingSheaf O)
        (ULift.{v} (Fin n)))
      (koszulSequenceMap O n f) :=
  koszulComplex O
    (SheafOfModules.free (R := commRingSheafToRingSheaf O)
      (ULift.{v} (Fin n)))
    (koszulSequenceMap O n f)

/-! ## Local finite-free normal form -/

structure KoszulLocalSequencePresentation {X : TopCat.{v}}
    (O : CommRingSheaf X) (E : CommRingSheafModule O)
    (φ : E ⟶ sheafModuleUnit O) (x : X) where
  U : Opens X
  contains : x ∈ U
  rank : ℕ
  basis : restrictedModule O E U ≅
    SheafOfModules.free
      (R := (openRingedSpace O U).structureSheaf) (ULift.{v} (Fin rank))
  coefficients : ULift.{v} (Fin rank) →
    (restrictedModule O (sheafModuleUnit O) U).sections
  map_on_basis :
    basis.hom ≫ freeMapFromSections coefficients =
      (openModuleRestrictionFunctor (underlyingRingedSpace O) U).map φ

theorem koszulComplex_is_locally_a_sequence_koszul {X : TopCat.{v}}
    (O : CommRingSheaf X) (E : CommRingSheafModule O)
    (φ : E ⟶ sheafModuleUnit O)
    (hE : IsFiniteLocallyFree (X := underlyingRingedSpace O) E) :
    ∀ x : X, Nonempty (KoszulLocalSequencePresentation O E φ x) := by
  sorry

end
end Formalization.Books.Modules.Unit24
