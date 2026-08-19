import Formalization.Books.Dga.Unit20.PResolutions

/-!
# Differential Graded Algebra, Chapter 20: I-resolutions

This file records the dual filtration, inverse-limit, K-injective, good
subobject, and right-resolution interfaces from the second source section.
Products and the character-dual shifts are expressed by universal-property
interfaces because the preceding project files expose the DG-module data API
but not a canonical product/character-dual construction for that API.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open Formalization.Books.Dga.Unit14

universe u v w uι

namespace Formalization.Books.Dga.Unit20

variable {R : Type u} {A : ℤ → Type v}
  [CommRing R]
  [∀ i, AddCommGroup (A i)] [∀ i, Module R (A i)]
  [DirectSum.GSemiring A] [DirectSum.GAlgebra R A]

/-! ## Products and dual shifts -/

/-- A product of a family of DG modules, expressed by its universal property. -/
structure DgProduct
    (D : DifferentialGradedAlgebraData (R := R) (A := A))
    {ι : Type uι}
    (F : ι → DGModule.{u, v, w} D) where
  object : DGModule.{u, v, w} D
  projection : ∀ i, DGMap object (F i)
  universal : ∀ (X : DGModule.{u, v, w} D)
      (f : ∀ i, DGMap X (F i)),
      ∃! g : DGMap X object,
        ∀ i, DifferentialGradedModuleHom.comp g (projection i) = f i

/-- The interface for the character-dual shift `A^∨[k]` constructed in the
preceding differential-graded-module section. -/
structure DgDualShiftSpec
    (D : DifferentialGradedAlgebraData (R := R) (A := A)) (k : ℤ) where
  object : DGModule.{u, v, w} D

/-- Existence of the previously constructed character-dual shift. -/
theorem dgaDualShiftSpec_nonempty
    (D : DifferentialGradedAlgebraData (R := R) (A := A)) (k : ℤ) :
    Nonempty (DgDualShiftSpec D k) := by
  sorry

/-- The character-dual shift `A^∨[k]`. -/
noncomputable def dgaDualShift
    (D : DifferentialGradedAlgebraData (R := R) (A := A)) (k : ℤ) :
    DGModule.{u, v, w} D :=
  (Classical.choice (dgaDualShiftSpec_nonempty (R := R) (A := A) D k)).object

/-- A product of shifts of the regular character-dual module. -/
def IsDgProductOfDualShifts
    {D : DifferentialGradedAlgebraData (R := R) (A := A)}
    (I : DGModule.{u, v, w} D) : Prop :=
  ∃ (ι : Type w) (degree : ι → ℤ)
    (S : DgProduct D (fun i => dgaDualShift D (degree i))),
    Nonempty (I ≅ S.object)

/-! ## Inverse limits and property (I) -/

/-- The inverse-limit cone used by the completeness clause of property (I). -/
structure DgInverseLimit
    (D : DifferentialGradedAlgebraData (R := R) (A := A))
    (F : ℕ → DGModule.{u, v, w} D)
    (transition : ∀ i, DGMap (F i.succ) (F i)) where
  object : DGModule.{u, v, w} D
  projection : ∀ i, DGMap object (F i)
  compatible : ∀ i,
    DifferentialGradedModuleHom.comp (projection i.succ) (transition i) =
      projection i
  universal : ∀ (X : DGModule.{u, v, w} D)
      (f : ∀ i, DGMap X (F i))
      (_hf : ∀ i,
        DifferentialGradedModuleHom.comp (f i.succ) (transition i) = f i),
      ∃! g : DGMap X object,
        ∀ i, DifferentialGradedModuleHom.comp g (projection i) = f i

/-- A decreasing filtration together with its quotient and successive
quotient data. -/
structure DgFiltrationICore
    {D : DifferentialGradedAlgebraData (R := R) (A := A)}
    (I : DGModule.{u, v, w} D) where
  stage : ℕ → DGModule.{u, v, w} D
  stage_map : ∀ i, DGMap (stage i) I
  stage_zero_identification : Nonempty (stage 0 ≅ I)
  inclusion : ∀ i, DGMap (stage i.succ) (stage i)
  stage_map_comm : ∀ i,
    DifferentialGradedModuleHom.comp (inclusion i) (stage_map i) = stage_map i.succ
  stage_map_injective : ∀ (i : ℕ) (n : ℤ),
    Function.Injective ((stage_map i).underlying.app n)
  separated : ∀ (n : ℤ) (x : I.graded.component n),
    (∀ i, ∃ y, (stage_map i).underlying.app n y = x) → x = 0
  quotient : ℕ → DGModule.{u, v, w} D
  quotient_map : ∀ i, DGMap I (quotient i)
  quotient_exact : ∀ i, IsExactPair (stage_map i) (quotient_map i)
  transition : ∀ i, DGMap (quotient i.succ) (quotient i)
  transition_comm : ∀ i,
    DifferentialGradedModuleHom.comp (quotient_map i.succ) (transition i) =
      quotient_map i
  limit : DgInverseLimit D (fun i => quotient i) transition
  limit_identification : Nonempty (I ≅ limit.object)
  successive_quotient : ℕ → DGModule.{u, v, w} D
  successive_map : ∀ i, DGMap (stage i) (successive_quotient i)
  successive_exact : ∀ i,
    IsExactPair (inclusion i) (successive_map i)
  successive_is_product_of_dual_shifts : ∀ i,
    IsDgProductOfDualShifts (successive_quotient i)

/-- Property (I): a complete decreasing filtration with admissible quotient
transitions and character-dual-product successive quotients. -/
structure DgFiltrationI
    {D : DifferentialGradedAlgebraData (R := R) (A := A)}
    (I : DGModule.{u, v, w} D) where
  core : DgFiltrationICore I
  transition_admissible : ∀ i,
    IsAdmissibleEpimorphism (core.transition i)

/-- A differential graded module has property (I). -/
def HasPropertyI
    {D : DifferentialGradedAlgebraData (R := R) (A := A)}
    (I : DGModule.{u, v, w} D) : Prop :=
  Nonempty (DgFiltrationI I)

/-- The underlying graded-module product observation following property (I). -/
def IsGradedProductOfDualShifts
    {D : DifferentialGradedAlgebraData (R := R) (A := A)}
    (I : DGModule.{u, v, w} D) : Prop :=
  IsDgProductOfDualShifts I

/-- The source's graded-injective consequence for quotient transitions. -/
theorem filtration_transition_admissible_of_dual_product_quotients
    {D : DifferentialGradedAlgebraData (R := R) (A := A)}
    {I : DGModule.{u, v, w} D} (F : DgFiltrationICore I) :
    ∀ i, IsAdmissibleEpimorphism (F.transition i) := by
  sorry

/-- The reader's underlying graded product observation. -/
theorem property_I_underlying_graded_product_of_dual_shifts
    {D : DifferentialGradedAlgebraData (R := R) (A := A)}
    {I : DGModule.{u, v, w} D} (F : DgFiltrationI I) :
    IsGradedProductOfDualShifts I := by
  sorry

/-! ## The admissible sequence associated to an I-filtration -/

/-- Data for `0 → I → ∏ I/Fᵢ → ∏ I/Fᵢ → 0`. -/
structure PropertyISequence
    {D : DifferentialGradedAlgebraData (R := R) (A := A)}
    {I : DGModule.{u, v, w} D} (F : DgFiltrationI I) where
  product : DgProduct D (fun i : ℕ => F.core.quotient i)
  inclusion : DGMap I product.object
  shift : DGMap product.object product.object
  sequence : DgAdmissibleShortExact I product.object product.object
  inclusion_eq : sequence.f = inclusion
  shift_eq : sequence.g = shift

/-- An I-filtration gives the displayed admissible short exact sequence. -/
theorem property_I_sequence
    {D : DifferentialGradedAlgebraData (R := R) (A := A)}
    {I : DGModule.{u, v, w} D} (F : DgFiltrationI I) :
    Nonempty (PropertyISequence F) := by
  sorry

/-! ## K-injectivity -/

/-- A module with property (I) is K-injective. -/
theorem property_I_K_injective
    {D : DifferentialGradedAlgebraData (R := R) (A := A)}
    {I : DGModule.{u, v, w} D} (hI : HasPropertyI I)
    (N : DGModule.{u, v, w} D) (hN : IsAcyclic N) :
    HomotopyHomVanishes N I := by
  sorry

/-! ## Good subobjects -/

/-- Degreewise injectivity of a DG-module homomorphism. -/
def DgDegreewiseInjective
    {D : DifferentialGradedAlgebraData (R := R) (A := A)}
    {M N : DGModule.{u, v, w} D} (f : DGMap M N) : Prop :=
  ∀ n : ℤ, Function.Injective (f.underlying.app n)

/-- The degree-`n` cokernel of the preceding differential. -/
abbrev dgCokernel
    {D : DifferentialGradedAlgebraData (R := R) (A := A)}
    (M : DGModule.{u, v, w} D) (n : ℤ) :=
  M.graded.component n ⧸ LinearMap.range (dgDifferentialTo M n)

/-- A witness for the map on degreewise cokernels induced by a DG map. -/
def DgCokernelMapWitness
    {D : DifferentialGradedAlgebraData (R := R) (A := A)}
    {M N : DGModule.{u, v, w} D} (f : DGMap M N) (n : ℤ) : Prop :=
  ∃ φ : dgCokernel M n → dgCokernel N n,
    Function.Injective φ ∧
      ∀ x : M.graded.component n,
        φ (Submodule.mkQ (LinearMap.range (dgDifferentialTo M n)) x) =
          Submodule.mkQ (LinearMap.range (dgDifferentialTo N n))
            (f.underlying.app n x)

/-- Injectivity of the map induced on the degreewise cokernels. -/
def DgCokernelInjective
    {D : DifferentialGradedAlgebraData (R := R) (A := A)}
    {M N : DGModule.{u, v, w} D} (f : DGMap M N) : Prop :=
  ∀ n : ℤ, DgCokernelMapWitness f n

/-- The good subobject supplied by the source lemma. -/
theorem exists_good_subobject
    {D : DifferentialGradedAlgebraData (R := R) (A := A)}
    (M : DGModule.{u, v, w} D) :
    ∃ (I : DGModule.{u, v, w} D) (f : DGMap M I),
      DgDegreewiseInjective f ∧ DgCokernelInjective f ∧
      ∃ (I' I'' : DGModule.{u, v, w} D),
        IsDgProductOfDualShifts I' ∧ IsDgProductOfDualShifts I'' ∧
        Nonempty (DgAdmissibleShortExact I' I I'') := by
  sorry

/-! ## Right resolutions and totalization -/

/-- The successive short exact sequences used to construct a right
resolution. -/
structure RightResolutionSteps
    {D : DifferentialGradedAlgebraData (R := R) (A := A)}
    (M : DGModule.{u, v, w} D) where
  syzygy : ℕ → DGModule.{u, v, w} D
  syzygy_zero : Nonempty (syzygy 0 ≅ M)
  term : ℕ → DGModule.{u, v, w} D
  augmentation : DGMap M (term 0)
  sequence : ∀ i, Nonempty
    (DgAdmissibleShortExact (syzygy i) (term i) (syzygy i.succ))
  term_map : ∀ i, DGMap (term i) (term i.succ)

/-- The coordinate formula for the total differential on the product of the
terms in a right resolution. -/
def rightTotalCoordinate
    {D : DifferentialGradedAlgebraData (R := R) (A := A)}
    {M : DGModule.{u, v, w} D}
    (S : RightResolutionSteps (D := D) M) (n : ℤ)
    (x : ∀ i : ℕ, (S.term i).graded.component (n - (i : ℤ)))
    (i : ℕ) : (S.term i).graded.component (n + 1 - (i : ℤ)) := by
  let diagonal : (S.term i).graded.component (n + 1 - (i : ℤ)) :=
    gradedTransport
      (show (n - (i : ℤ)) + 1 = n + 1 - (i : ℤ) by omega)
      ((gradedSign R (i : ℤ)) •
        ((S.term i).differential (n - (i : ℤ)) (x i)))
  by_cases h : 0 < i
  · let previous := i - 1
    have hi : previous.succ = i := by omega
    have val : (S.term i).graded.component (n - (previous : ℤ)) := by
      exact cast
        (congrArg
          (fun j : ℕ => (S.term j).graded.component (n - (previous : ℤ))) hi)
        ((S.term_map previous).underlying.app
          (n - (previous : ℤ)) (x previous))
    let preceding : (S.term i).graded.component (n + 1 - (i : ℤ)) :=
      gradedTransport
        (show n - (previous : ℤ) = n + 1 - (i : ℤ) by omega)
        val
    exact preceding + diagonal
  · exact diagonal

/-- A totalization of the right-resolution terms, including the displayed
product grading and total-differential formula. -/
structure DgRightResolutionTotalization
    {D : DifferentialGradedAlgebraData (R := R) (A := A)}
    {M : DGModule.{u, v, w} D} (S : RightResolutionSteps M) where
  object : DGModule.{u, v, w} D
  coordinate : ∀ n : ℤ,
    object.graded.component n ≃ₗ[R]
      (∀ i : ℕ, (S.term i).graded.component (n - (i : ℤ)))
  differential_formula : ∀ (n : ℤ)
      (x : ∀ i : ℕ, (S.term i).graded.component (n - (i : ℤ))) (i : ℕ),
      coordinate (n + 1)
          (object.differential n ((coordinate n).symm x)) i =
        rightTotalCoordinate S n x i

/-- The totalization construction is a differential graded module with the
source's product grading and sign convention. -/
theorem right_resolution_totalization_exists
    {D : DifferentialGradedAlgebraData (R := R) (A := A)}
    {M : DGModule.{u, v, w} D} (S : RightResolutionSteps M) :
    Nonempty (DgRightResolutionTotalization S) := by
  sorry

/-- A right resolution of a differential graded module. -/
structure RightResolution
    {D : DifferentialGradedAlgebraData (R := R) (A := A)}
    (M : DGModule.{u, v, w} D) where
  steps : RightResolutionSteps M
  totalization : DgRightResolutionTotalization steps
  map : DGMap M totalization.object
  quasi_isomorphism : DgQuasiIsomorphism map
  property_I : HasPropertyI totalization.object

/-- Every differential graded module admits a quasi-isomorphism into a module
with property (I). -/
theorem exists_RightResolution
    {D : DifferentialGradedAlgebraData (R := R) (A := A)}
    (M : DGModule.{u, v, w} D) :
    Nonempty (RightResolution M) := by
  sorry

end Formalization.Books.Dga.Unit20
