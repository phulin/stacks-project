import Formalization.Books.Dga.Unit20.IResolutions

/-!
# Differential Graded Algebra, Chapter 21: I-resolutions

This file gives the chapter-owned interface for complete decreasing
filtrations by products of character-dual shifts, the associated admissible
sequence, K-injectivity, good subobjects, and right resolutions.  The
underlying DG-module constructions are reused from the preceding project API.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open Formalization.Books.Dga.Unit14

universe u v w uι

namespace Formalization.Books.Dga.Unit21

variable {R : Type u} {A : ℤ → Type v}
  [CommRing R]
  [∀ i, AddCommGroup (A i)] [∀ i, Module R (A i)]
  [DirectSum.GSemiring A] [DirectSum.GAlgebra R A]

abbrev DGModule
    (D : DifferentialGradedAlgebraData (R := R) (A := A)) :=
  DifferentialGradedModuleData D

abbrev DGMap
    {D : DifferentialGradedAlgebraData (R := R) (A := A)}
    (M N : DGModule.{u, v, w} (D := D)) :=
  DifferentialGradedModuleHom M N

/-! ## Canonical prerequisites reused from the preceding DGA interface -/

abbrev IsAdmissibleMonomorphism
    {D : DifferentialGradedAlgebraData (R := R) (A := A)}
    {M N : DGModule.{u, v, w} (D := D)} (f : DGMap M N) : Prop :=
  Formalization.Books.Dga.Unit20.IsAdmissibleMonomorphism f

abbrev IsAdmissibleEpimorphism
    {D : DifferentialGradedAlgebraData (R := R) (A := A)}
    {M N : DGModule.{u, v, w} (D := D)} (f : DGMap M N) : Prop :=
  Formalization.Books.Dga.Unit20.IsAdmissibleEpimorphism f

abbrev IsExactPair
    {D : DifferentialGradedAlgebraData (R := R) (A := A)}
    {K L M : DGModule.{u, v, w} (D := D)} (f : DGMap K L) (g : DGMap L M) : Prop :=
  Formalization.Books.Dga.Unit20.IsExactPair f g

abbrev DgAdmissibleShortExact
    {D : DifferentialGradedAlgebraData (R := R) (A := A)}
    (K L M : DGModule.{u, v, w} (D := D)) :=
  Formalization.Books.Dga.Unit20.DgAdmissibleShortExact K L M

abbrev DgProduct
    {D : DifferentialGradedAlgebraData (R := R) (A := A)}
    {ι : Type uι} (F : ι → DGModule.{u, v, w} (D := D)) :=
  Formalization.Books.Dga.Unit20.DgProduct D F

abbrev DgInverseLimit
    {D : DifferentialGradedAlgebraData (R := R) (A := A)}
    (F : ℕ → DGModule.{u, v, w} (D := D))
    (transition : ∀ i, DGMap (F i.succ) (F i)) :=
  Formalization.Books.Dga.Unit20.DgInverseLimit D F transition

abbrev DgDualShiftSpec
    (D : DifferentialGradedAlgebraData (R := R) (A := A)) (k : ℤ) :=
  Formalization.Books.Dga.Unit20.DgDualShiftSpec D k

noncomputable abbrev dgaDualShift
    (D : DifferentialGradedAlgebraData (R := R) (A := A)) (k : ℤ) :
    DGModule.{u, v, w} (D := D) :=
  Formalization.Books.Dga.Unit20.dgaDualShift D k

abbrev IsDgProductOfDualShifts
    {D : DifferentialGradedAlgebraData (R := R) (A := A)}
    (I : DGModule.{u, v, w} (D := D)) : Prop :=
  Formalization.Books.Dga.Unit20.IsDgProductOfDualShifts I

abbrev IsAcyclic
    {D : DifferentialGradedAlgebraData (R := R) (A := A)}
    (N : DGModule.{u, v, w} (D := D)) : Prop :=
  Formalization.Books.Dga.Unit20.IsAcyclic N

abbrev HomotopyHomVanishes
    {D : DifferentialGradedAlgebraData (R := R) (A := A)}
    (M N : DGModule.{u, v, w} (D := D)) : Prop :=
  Formalization.Books.Dga.Unit20.HomotopyHomVanishes M N

/-! ## Property (I) -/

abbrev DgFiltrationICore
    {D : DifferentialGradedAlgebraData (R := R) (A := A)}
    (I : DGModule.{u, v, w} (D := D)) :=
  Formalization.Books.Dga.Unit20.DgFiltrationICore I

abbrev DgFiltrationI
    {D : DifferentialGradedAlgebraData (R := R) (A := A)}
    (I : DGModule.{u, v, w} (D := D)) :=
  Formalization.Books.Dga.Unit20.DgFiltrationI I

abbrev HasPropertyI
    {D : DifferentialGradedAlgebraData (R := R) (A := A)}
    (I : DGModule.{u, v, w} (D := D)) : Prop :=
  Formalization.Books.Dga.Unit20.HasPropertyI I

abbrev IsGradedProductOfDualShifts
    {D : DifferentialGradedAlgebraData (R := R) (A := A)}
    (I : DGModule.{u, v, w} (D := D)) : Prop :=
  Formalization.Books.Dga.Unit20.IsGradedProductOfDualShifts I

theorem dgaDualShiftSpec_nonempty
    (D : DifferentialGradedAlgebraData (R := R) (A := A)) (k : ℤ) :
    Nonempty (DgDualShiftSpec D k) := by
  exact Formalization.Books.Dga.Unit20.dgaDualShiftSpec_nonempty D k

theorem filtration_transition_admissible_of_dual_product_quotients
    {D : DifferentialGradedAlgebraData (R := R) (A := A)}
    {I : DGModule.{u, v, w} (D := D)} (F : DgFiltrationICore I) :
    ∀ i, IsAdmissibleEpimorphism (F.transition i) := by
  exact
    Formalization.Books.Dga.Unit20.filtration_transition_admissible_of_dual_product_quotients
      F

theorem property_I_underlying_graded_product_of_dual_shifts
    {D : DifferentialGradedAlgebraData (R := R) (A := A)}
    {I : DGModule.{u, v, w} (D := D)} (F : DgFiltrationI I) :
    IsGradedProductOfDualShifts I := by
  exact
    Formalization.Books.Dga.Unit20.property_I_underlying_graded_product_of_dual_shifts
      F

/-! ## The sequence attached to a filtration -/

abbrev PropertyISequence
    {D : DifferentialGradedAlgebraData (R := R) (A := A)}
    {I : DGModule.{u, v, w} (D := D)} (F : DgFiltrationI I) :=
  Formalization.Books.Dga.Unit20.PropertyISequence F

theorem property_I_sequence
    {D : DifferentialGradedAlgebraData (R := R) (A := A)}
    {I : DGModule.{u, v, w} (D := D)} (F : DgFiltrationI I) :
    Nonempty (PropertyISequence F) := by
  exact Formalization.Books.Dga.Unit20.property_I_sequence F

/-! ## K-injectivity -/

theorem property_I_K_injective
    {D : DifferentialGradedAlgebraData (R := R) (A := A)}
    {I : DGModule.{u, v, w} (D := D)} (hI : HasPropertyI I)
    (N : DGModule.{u, v, w} (D := D)) (hN : IsAcyclic N) :
    HomotopyHomVanishes N I := by
  exact Formalization.Books.Dga.Unit20.property_I_K_injective hI N hN

/-! ## Good subobjects -/

abbrev DgDegreewiseInjective
    {D : DifferentialGradedAlgebraData (R := R) (A := A)}
    {M N : DGModule.{u, v, w} (D := D)} (f : DGMap M N) : Prop :=
  Formalization.Books.Dga.Unit20.DgDegreewiseInjective f

abbrev dgCokernel
    {D : DifferentialGradedAlgebraData (R := R) (A := A)}
    (M : DGModule.{u, v, w} (D := D)) (n : ℤ) :=
  Formalization.Books.Dga.Unit20.dgCokernel M n

abbrev DgCokernelMapWitness
    {D : DifferentialGradedAlgebraData (R := R) (A := A)}
    {M N : DGModule.{u, v, w} (D := D)} (f : DGMap M N) (n : ℤ) : Prop :=
  Formalization.Books.Dga.Unit20.DgCokernelMapWitness f n

abbrev DgCokernelInjective
    {D : DifferentialGradedAlgebraData (R := R) (A := A)}
    {M N : DGModule.{u, v, w} (D := D)} (f : DGMap M N) : Prop :=
  Formalization.Books.Dga.Unit20.DgCokernelInjective f

theorem exists_good_subobject
    {D : DifferentialGradedAlgebraData (R := R) (A := A)}
    (M : DGModule.{u, v, w} (D := D)) :
    ∃ (I : DGModule.{u, v, w} (D := D)) (f : DGMap M I),
      DgDegreewiseInjective f ∧ DgCokernelInjective f ∧
      ∃ (I' I'' : DGModule.{u, v, w} (D := D)),
        IsDgProductOfDualShifts I' ∧ IsDgProductOfDualShifts I'' ∧
        Nonempty (DgAdmissibleShortExact I' I I'') := by
  exact Formalization.Books.Dga.Unit20.exists_good_subobject M

/-! ## Right resolutions and the total differential -/

abbrev RightResolutionSteps
    {D : DifferentialGradedAlgebraData (R := R) (A := A)}
    (M : DGModule.{u, v, w} (D := D)) :=
  Formalization.Books.Dga.Unit20.RightResolutionSteps M

abbrev DgRightResolutionTotalization
    {D : DifferentialGradedAlgebraData (R := R) (A := A)}
    {M : DGModule.{u, v, w} (D := D)} (S : RightResolutionSteps M) :=
  Formalization.Books.Dga.Unit20.DgRightResolutionTotalization S

abbrev rightTotalCoordinate
    {D : DifferentialGradedAlgebraData (R := R) (A := A)}
    {M : DGModule.{u, v, w} (D := D)}
    (S : RightResolutionSteps M) (n : ℤ)
    (x : ∀ i : ℕ, (S.term i).graded.component (n - (i : ℤ))) (i : ℕ) :
    (S.term i).graded.component (n + 1 - (i : ℤ)) :=
  Formalization.Books.Dga.Unit20.rightTotalCoordinate S n x i

theorem right_resolution_totalization_exists
    {D : DifferentialGradedAlgebraData (R := R) (A := A)}
    {M : DGModule.{u, v, w} (D := D)} (S : RightResolutionSteps M) :
    Nonempty (DgRightResolutionTotalization S) := by
  exact Formalization.Books.Dga.Unit20.right_resolution_totalization_exists S

abbrev RightResolution
    {D : DifferentialGradedAlgebraData (R := R) (A := A)}
    (M : DGModule.{u, v, w} (D := D)) :=
  Formalization.Books.Dga.Unit20.RightResolution M

theorem exists_RightResolution
    {D : DifferentialGradedAlgebraData (R := R) (A := A)}
    (M : DGModule.{u, v, w} (D := D)) :
    Nonempty (RightResolution M) := by
  exact Formalization.Books.Dga.Unit20.exists_RightResolution M

end Formalization.Books.Dga.Unit21
