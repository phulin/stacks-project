import Formalization.Books.Dga.Unit16.DifferentialGradedProjectives

/-!
# Differential Graded Algebra, Chapter 20: P-resolutions

This file records the filtration, exact-sequence, K-projectivity, good
quotient, and resolution interfaces in the source section.  The DG-module,
shift, cycle, boundary, and homotopy-category constructions are reused from
Unit16.  A direct sum is represented by its coproduct universal property in
the DG-module category; this avoids introducing a second direct-sum
construction whose only use would be this chapter's statements.
-/

noncomputable section

open CategoryTheory
open Formalization.Books.Dga.Unit14

universe u v w

namespace Formalization.Books.Dga.Unit20

variable {R : Type u} {A : ℤ → Type v}
  [CommRing R]
  [∀ i, AddCommGroup (A i)] [∀ i, Module R (A i)]
  [DirectSum.GSemiring A] [DirectSum.GAlgebra R A]

/-! ## Admissible maps and direct sums -/

/-- A graded left inverse for a homomorphism of differential graded modules. -/
def IsAdmissibleMonomorphism
    {D : DifferentialGradedAlgebraData (R := R) (A := A)}
    {M N : DifferentialGradedModuleData D}
    (f : DifferentialGradedModuleHom M N) : Prop :=
  ∃ r : GradedRightModuleHom N.graded M.graded,
    GradedRightModuleHom.comp f.underlying r = GradedRightModuleHom.id M.graded

/-- A degreewise exact pair of maps of differential graded modules.

Exactness is stated componentwise, which is the underlying exactness notion
used for complexes of modules. -/
def IsExactPair
    {D : DifferentialGradedAlgebraData (R := R) (A := A)}
    {K L M : DifferentialGradedModuleData D}
    (f : DifferentialGradedModuleHom K L)
    (g : DifferentialGradedModuleHom L M) : Prop :=
  ∀ n : ℤ,
    Set.range (f.underlying.app n) = LinearMap.ker (g.underlying.app n)

/-- An admissible short exact sequence of differential graded modules. -/
structure DgAdmissibleShortExact
    {D : DifferentialGradedAlgebraData (R := R) (A := A)}
    (K L M : DifferentialGradedModuleData D) where
  f : DifferentialGradedModuleHom K L
  g : DifferentialGradedModuleHom L M
  complex : ∀ (n : ℤ) (x : K.graded.component n),
    g.underlying.app n (f.underlying.app n x) = 0
  exact : IsExactPair f g
  splitting : ∃ (s : GradedRightModuleHom M.graded L.graded)
      (r : GradedRightModuleHom L.graded K.graded),
      GradedRightModuleHom.comp g.underlying s =
        GradedRightModuleHom.id M.graded ∧
      GradedRightModuleHom.comp f.underlying r =
        GradedRightModuleHom.id K.graded

/-- A coproduct of a family of DG modules, expressed by its universal
property. -/
structure DgDirectSum
    (D : DifferentialGradedAlgebraData (R := R) (A := A))
    {ι : Type w} (F : ι → DifferentialGradedModuleData D) where
  object : DifferentialGradedModuleData D
  inclusion : ∀ i, DifferentialGradedModuleHom (F i) object
  universal : ∀ (X : DifferentialGradedModuleData D)
      (f : ∀ i, DifferentialGradedModuleHom (F i) X),
      ∃! g : DifferentialGradedModuleHom object X,
        ∀ i, (inclusion i).comp g = f i

/-- A DG module is a direct sum of shifts of the regular DG module. -/
def IsDgShiftedFree
    {D : DifferentialGradedAlgebraData (R := R) (A := A)}
    (P : DifferentialGradedModuleData D) : Prop :=
  ∃ (ι : Type w) (degree : ι → ℤ)
    (S : DgDirectSum D (fun i => differentialGradedAlgebraShift D (degree i))),
    Nonempty (P ≅ S.object)

/-! ## The zero DG module and filtrations -/

/-- The zero differential graded module used to name the initial filtration
stage. -/
def dgZeroModule
    (D : DifferentialGradedAlgebraData (R := R) (A := A)) :
    DifferentialGradedModuleData D := by
  let G : GradedRightModule (R := R) (A := A) where
    component := fun _ => PUnit
    addCommGroup := fun _ => inferInstance
    module := fun _ => inferInstance
    action := fun _ _ => PUnit.unit
    action_zero_left := by intros; rfl
    action_add_left := by intros; rfl
    action_zero_right := by intros; rfl
    action_add_right := by intros; rfl
    action_smul_left := by intros; rfl
    action_smul_right := by intros; rfl
    one_action := by
      intro x
      cases x
      rfl
    mul_action := by
      intro x a
      cases x
      cases a
      rfl
  exact
    { graded := G
      differential := fun _ => 0
      differential_square := by intros; simp
      differential_leibniz := by intros; rfl }

/-! A filtration before adding the admissibility consequence. -/

structure DgFiltrationCore
    {D : DifferentialGradedAlgebraData (R := R) (A := A)}
    (P : DifferentialGradedModuleData D) where
  zeroStage : DifferentialGradedModuleData D
  zeroStage_is_zero : Nonempty (zeroStage ≅ dgZeroModule D)
  zero_inclusion : DifferentialGradedModuleHom zeroStage stage0
  stage0 : DifferentialGradedModuleData D
  stage : ℕ → DifferentialGradedModuleData D
  stage_zero : stage 0 = stage0
  inclusion : ∀ i, DifferentialGradedModuleHom (stage i) (stage (i + 1))
  stage_map : ∀ i, DifferentialGradedModuleHom (stage i) P
  stage_map_comm : ∀ i,
    (inclusion i).comp (stage_map (i + 1)) = stage_map i
  covers : ∀ (n : ℤ) (x : P.graded.component n),
    ∃ (i : ℕ) (y : (stage i).graded.component n),
      (stage_map i).underlying.app n y = x
  quotient : ℕ → DifferentialGradedModuleData D
  quotientMap : ∀ i,
    DifferentialGradedModuleHom (stage (i + 1)) (quotient i)
  successive : ∀ i, IsExactPair (inclusion i) (quotientMap i)
  quotient_is_shifted_free : ∀ i, IsDgShiftedFree (quotient i)

/-! The source includes the admissibility of every filtration inclusion. -/

structure DgFiltration
    {D : DifferentialGradedAlgebraData (R := R) (A := A)}
    (P : DifferentialGradedModuleData D) where
  core : DgFiltrationCore P
  inclusion_admissible : ∀ i,
    IsAdmissibleMonomorphism (core.inclusion i)

/-- Property (P): existence of a filtration with admissible inclusions and
successive quotients that are direct sums of shifts of `A`. -/
def HasPropertyP
    {D : DifferentialGradedAlgebraData (R := R) (A := A)}
    (P : DifferentialGradedModuleData D) : Prop :=
  Nonempty (DgFiltration P)

/-- The underlying graded module of a DG module is a direct sum of shifts of
the regular graded module. -/
def IsGradedShiftedFree
    {D : DifferentialGradedAlgebraData (R := R) (A := A)}
    (P : DifferentialGradedModuleData D) : Prop :=
  ∃ (ι : Type w) (degree : ι → ℤ)
    (h : HasCoproduct
      (fun i => gradedAlgebraShift (R := R) (A := A) (degree i))),
    Nonempty (P.graded ≅ gradedDirectSumOfShifts
      (R := R) (A := A) ι degree h)

/-! ## The first lemma and the two source remarks -/

/-- The graded-projective quotient consequence makes the filtration
inclusions admissible. -/
theorem filtration_inclusion_admissible_of_shifted_free_quotients
    {D : DifferentialGradedAlgebraData (R := R) (A := A)}
    {P : DifferentialGradedModuleData D} (F : DgFiltrationCore P) :
    ∀ i, IsAdmissibleMonomorphism (F.inclusion i) := by
  sorry

/-- The reader's graded-module observation following property (P). -/
theorem property_P_underlying_graded_shifted_free
    {D : DifferentialGradedAlgebraData (R := R) (A := A)}
    {P : DifferentialGradedModuleData D} (F : DgFiltration P) :
    IsGradedShiftedFree P := by
  sorry

/-! ## The admissible sequence associated to a P-filtration -/

/-- Data for the sequence
`0 → ⨁ FᵢP → ⨁ FᵢP → P → 0`. -/
structure PropertyPSequence
    {D : DifferentialGradedAlgebraData (R := R) (A := A)}
    {P : DifferentialGradedModuleData D} (F : DgFiltration P) where
  sum : DgDirectSum D (fun i => F.core.stage i)
  first : DifferentialGradedModuleHom sum.object sum.object
  augmentation : DifferentialGradedModuleHom sum.object P
  sequence : DgAdmissibleShortExact sum.object sum.object P
  first_eq : sequence.f = first
  augmentation_eq : sequence.g = augmentation

/-- A P-filtration gives the admissible short exact sequence displayed in the
source. -/
theorem property_P_sequence
    {D : DifferentialGradedAlgebraData (R := R) (A := A)}
    {P : DifferentialGradedModuleData D} (F : DgFiltration P) :
    Nonempty (PropertyPSequence F) := by
  sorry

/-! ## K-projectivity -/

/-- A DG module is acyclic when all of its cohomology modules are zero. -/
def IsAcyclic
    {D : DifferentialGradedAlgebraData (R := R) (A := A)}
    (N : DifferentialGradedModuleData D) : Prop :=
  ∀ n : ℤ, Subsingleton (dgCohomology N n)

/-- Vanishing of a hom-set in the homotopy category.  The current homotopy
category interface is a quotient hom-set without a chosen zero morphism, so
`Subsingleton` is the canonical representation of equality to zero. -/
def HomotopyHomVanishes
    {D : DifferentialGradedAlgebraData (R := R) (A := A)}
    (P N : DifferentialGradedModuleData D) : Prop :=
  Subsingleton (dgHomotopyCategoryHom P N)

/-- A DG module with property (P) is K-projective. -/
theorem property_P_K_projective
    {D : DifferentialGradedAlgebraData (R := R) (A := A)}
    {P : DifferentialGradedModuleData D} (hP : HasPropertyP P)
    (N : DifferentialGradedModuleData D) (hN : IsAcyclic N) :
    HomotopyHomVanishes P N := by
  sorry

/-! ## Good quotients -/

/-- Degreewise surjectivity of a DG-module homomorphism. -/
def DgDegreewiseSurjective
    {D : DifferentialGradedAlgebraData (R := R) (A := A)}
    {M N : DifferentialGradedModuleData D}
    (f : DifferentialGradedModuleHom M N) : Prop :=
  ∀ n : ℤ, Function.Surjective (f.underlying.app n)

/-- The map induced by a DG homomorphism on cycles in one degree. -/
def dgMapCycles
    {D : DifferentialGradedAlgebraData (R := R) (A := A)}
    {M N : DifferentialGradedModuleData D}
    (f : DifferentialGradedModuleHom M N) (n : ℤ) :
    dgCycles M n → dgCycles N n := fun x =>
  ⟨f.underlying.app n x,
    by simpa [x.property] using f.commutes_with_differential n x⟩

/-- Surjectivity on cycles, as required in the good-quotient lemma. -/
def DgCycleSurjective
    {D : DifferentialGradedAlgebraData (R := R) (A := A)}
    {M N : DifferentialGradedModuleData D}
    (f : DifferentialGradedModuleHom M N) : Prop :=
  ∀ n : ℤ, Function.Surjective (dgMapCycles f n)

/-- A cohomology-map specification for a DG homomorphism. -/
def DgCohomologyMapWitness
    {D : DifferentialGradedAlgebraData (R := R) (A := A)}
    {M N : DifferentialGradedModuleData D}
    (f : DifferentialGradedModuleHom M N) (n : ℤ) : Prop :=
  ∃ φ : dgCohomology M n → dgCohomology N n,
    (∀ x : dgCycles M n,
      φ ((dgBoundary M n).mkQ x) =
        (dgBoundary N n).mkQ (dgMapCycles f n x)) ∧
    Function.Bijective φ

/-- A DG homomorphism is a quasi-isomorphism when it induces bijections on
cohomology. -/
def DgQuasiIsomorphism
    {D : DifferentialGradedAlgebraData (R := R) (A := A)}
    {M N : DifferentialGradedModuleData D}
    (f : DifferentialGradedModuleHom M N) : Prop :=
  ∀ n : ℤ, DgCohomologyMapWitness f n

/-- The good quotient supplied by the source lemma. -/
theorem exists_good_quotient
    {D : DifferentialGradedAlgebraData (R := R) (A := A)}
    (M : DifferentialGradedModuleData D) :
    ∃ (P : DifferentialGradedModuleData D)
      (f : DifferentialGradedModuleHom P M),
      DgDegreewiseSurjective f ∧ DgCycleSurjective f ∧
      ∃ (P' P'' : DifferentialGradedModuleData D),
        IsDgShiftedFree P' ∧ IsDgShiftedFree P'' ∧
        Nonempty (DgAdmissibleShortExact P' P P'') := by
  sorry

/-! ## P-resolutions -/

/-- A P-resolution of a DG module. -/
structure PResolution
    {D : DifferentialGradedAlgebraData (R := R) (A := A)}
    (M : DifferentialGradedModuleData D) where
  object : DifferentialGradedModuleData D
  map : DifferentialGradedModuleHom object M
  quasi_isomorphism : DgQuasiIsomorphism map
  property_P : HasPropertyP object

/-- Every differential graded module admits a quasi-isomorphism from a DG
module with property (P). -/
theorem exists_PResolution
    {D : DifferentialGradedAlgebraData (R := R) (A := A)}
    (M : DifferentialGradedModuleData D) :
    Nonempty (PResolution M) := by
  sorry

end Formalization.Books.Dga.Unit20
