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
open CategoryTheory.Limits
open Formalization.Books.Dga.Unit14

universe u v w uι wF

namespace Formalization.Books.Dga.Unit20

variable {R : Type u} {A : ℤ → Type v}
  [CommRing R]
  [∀ i, AddCommGroup (A i)] [∀ i, Module R (A i)]
  [DirectSum.GSemiring A] [DirectSum.GAlgebra R A]

abbrev DGModule
    (D : DifferentialGradedAlgebraData (R := R) (A := A)) :=
  DifferentialGradedModuleData.{u, v, w} D

abbrev DGMap
    {D : DifferentialGradedAlgebraData (R := R) (A := A)}
    (M N : DGModule.{u, v, w} D) := DifferentialGradedModuleHom M N

abbrev GradedMap
    (M N : GradedRightModule.{u, v, w} (R := R) (A := A)) :=
  GradedRightModuleHom M N

/-! ## Admissible maps and direct sums -/

/-- A graded left inverse for a homomorphism of differential graded modules. -/
def IsAdmissibleMonomorphism
    {D : DifferentialGradedAlgebraData (R := R) (A := A)}
    {M N : DGModule.{u, v, w} D} (f : DGMap M N) : Prop :=
  ∃ r : GradedMap N.graded M.graded,
    GradedRightModuleHom.comp f.underlying r = GradedRightModuleHom.id M.graded

/-- A degreewise exact pair of maps of differential graded modules.

Exactness is stated componentwise, which is the underlying exactness notion
used for complexes of modules. -/
def IsExactPair
    {D : DifferentialGradedAlgebraData (R := R) (A := A)}
    {K L M : DGModule.{u, v, w} D} (f : DGMap K L) (g : DGMap L M) : Prop :=
  ∀ n : ℤ,
    Set.range (f.underlying.app n) = LinearMap.ker (g.underlying.app n)

/-- An admissible short exact sequence of differential graded modules. -/
structure DgAdmissibleShortExact
    {D : DifferentialGradedAlgebraData (R := R) (A := A)}
    (K L M : DGModule.{u, v, w} D) where
  f : DGMap K L
  g : DGMap L M
  complex : ∀ (n : ℤ) (x : K.graded.component n),
    g.underlying.app n (f.underlying.app n x) = 0
  exact : IsExactPair f g
  splitting : ∃ (s : GradedMap M.graded L.graded)
      (r : GradedMap L.graded K.graded),
      GradedRightModuleHom.comp s g.underlying =
        GradedRightModuleHom.id M.graded ∧
      GradedRightModuleHom.comp f.underlying r =
        GradedRightModuleHom.id K.graded

/-- A coproduct of a family of DG modules, expressed by its universal
property. -/
structure DgDirectSum
    (D : DifferentialGradedAlgebraData (R := R) (A := A))
    {ι : Type uι}
    (F : ι → DifferentialGradedModuleData.{u, v, wF} D) where
  object : DGModule.{u, v, w} D
  inclusion : ∀ i, DifferentialGradedModuleHom (F i) object
  universal : ∀ (X : DGModule.{u, v, w} D)
      (f : ∀ i, DifferentialGradedModuleHom (F i) X),
      ∃! g : DifferentialGradedModuleHom object X,
        ∀ i, DifferentialGradedModuleHom.comp (inclusion i) g = f i

/-- A DG module is a direct sum of shifts of the regular DG module. -/
def IsDgShiftedFree
    {D : DifferentialGradedAlgebraData (R := R) (A := A)}
    (P : DGModule.{u, v, w} D) : Prop :=
  ∃ (ι : Type w) (degree : ι → ℤ)
    (S : DgDirectSum D
      (fun i => differentialGradedAlgebraShift D (degree i))),
    Nonempty (P ≅ S.object)

/-! ## The zero DG module and filtrations -/

/-- The zero differential graded module used to name the initial filtration
stage. -/
def dgZeroModule
    (D : DifferentialGradedAlgebraData (R := R) (A := A)) :
    DGModule.{u, v, w} D := by
  let G : GradedRightModule.{u, v, w} (R := R) (A := A) :=
    { component := fun _ => PUnit
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
        cases x with
        | mk i x =>
          cases x
          simp [gradedRightAction] <;> rfl
      mul_action := by
        intro x a
        intro b
        cases x with
        | mk i x =>
          cases a with
          | mk j a =>
            cases b with
            | mk k b =>
              simp [gradedRightAction, GradedMonoid.fst_mul, add_assoc] <;> rfl }
  exact
    { graded := G
      differential := fun _ => 0
      differential_square := by intros; simp
      differential_leibniz := by
        intros
        simp [G, DifferentialGradedModuleLeibniz, gradedTransport] }

/-! A filtration before adding the admissibility consequence. -/

structure DgFiltrationCore
    {D : DifferentialGradedAlgebraData (R := R) (A := A)}
    (P : DGModule.{u, v, w} D) where
  zeroStage : DGModule.{u, v, w} D
  zeroStage_is_zero : Nonempty (zeroStage ≅ dgZeroModule D)
  stage : ℕ → DGModule.{u, v, w} D
  zero_inclusion : DGMap zeroStage (stage 0)
  inclusion : ∀ i, DGMap (stage i) (stage (i + 1))
  stage_map : ∀ i, DGMap (stage i) P
  stage_map_comm : ∀ i,
    DifferentialGradedModuleHom.comp (inclusion i) (stage_map (i + 1)) =
      stage_map i
  stage_map_injective : ∀ (i : ℕ) (n : ℤ),
    Function.Injective ((stage_map i).underlying.app n)
  covers : ∀ (n : ℤ) (x : P.graded.component n),
    ∃ (i : ℕ) (y : (stage i).graded.component n),
      (stage_map i).underlying.app n y = x
  zeroQuotient : DGModule.{u, v, w} D
  zeroQuotientMap : DGMap (stage 0) zeroQuotient
  zero_successive : IsExactPair zero_inclusion zeroQuotientMap
  zero_quotient_is_shifted_free : IsDgShiftedFree zeroQuotient
  quotient : ℕ → DGModule.{u, v, w} D
  quotientMap : ∀ i,
    DGMap (stage (i + 1)) (quotient i)
  successive : ∀ i, IsExactPair (inclusion i) (quotientMap i)
  quotient_is_shifted_free : ∀ i, IsDgShiftedFree (quotient i)

/-! The source includes the admissibility of every filtration inclusion. -/

structure DgFiltration
    {D : DifferentialGradedAlgebraData (R := R) (A := A)}
    (P : DGModule.{u, v, w} D) where
  core : DgFiltrationCore P
  zero_inclusion_admissible :
    IsAdmissibleMonomorphism core.zero_inclusion
  inclusion_admissible : ∀ i,
    IsAdmissibleMonomorphism (core.inclusion i)

/-- Property (P): existence of a filtration with admissible inclusions and
successive quotients that are direct sums of shifts of `A`. -/
def HasPropertyP
    {D : DifferentialGradedAlgebraData (R := R) (A := A)}
    (P : DGModule.{u, v, w} D) : Prop :=
  Nonempty (DgFiltration P)

/-- The source's underlying graded-module observation, recorded by the
stronger DG shifted-free presentation already used for the successive
quotients. -/
def IsGradedShiftedFree
    {D : DifferentialGradedAlgebraData (R := R) (A := A)}
    (P : DGModule.{u, v, w} D) : Prop :=
  IsDgShiftedFree P

/-! ## The first lemma and the two source remarks -/

/-- The graded-projective quotient consequence makes the filtration
inclusions admissible. -/
theorem filtration_inclusion_admissible_of_shifted_free_quotients
    {D : DifferentialGradedAlgebraData (R := R) (A := A)}
    {P : DGModule.{u, v, w} D} (F : DgFiltrationCore P) :
    IsAdmissibleMonomorphism F.zero_inclusion ∧
      ∀ i, IsAdmissibleMonomorphism (F.inclusion i) := by
  sorry

/-- The reader's graded-module observation following property (P). -/
theorem property_P_underlying_graded_shifted_free
    {D : DifferentialGradedAlgebraData (R := R) (A := A)}
    {P : DGModule.{u, v, w} D} (F : DgFiltration P) :
    IsGradedShiftedFree P := by
  sorry

/-! ## The admissible sequence associated to a P-filtration -/

/-- Data for the sequence
`0 → ⨁ FᵢP → ⨁ FᵢP → P → 0`. -/
structure PropertyPSequence
    {D : DifferentialGradedAlgebraData (R := R) (A := A)}
    {P : DGModule.{u, v, w} D} (F : DgFiltration P) where
  sum : DgDirectSum D (fun i => F.core.stage i)
  first : DGMap sum.object sum.object
  augmentation : DGMap sum.object P
  sequence : DgAdmissibleShortExact sum.object sum.object P
  first_eq : sequence.f = first
  augmentation_eq : sequence.g = augmentation

/-- A P-filtration gives the admissible short exact sequence displayed in the
source. -/
theorem property_P_sequence
    {D : DifferentialGradedAlgebraData (R := R) (A := A)}
    {P : DGModule.{u, v, w} D} (F : DgFiltration P) :
    Nonempty (PropertyPSequence F) := by
  sorry

/-! ## K-projectivity -/

/-- A DG module is acyclic when all of its cohomology modules are zero. -/
def IsAcyclic
    {D : DifferentialGradedAlgebraData (R := R) (A := A)}
    (N : DGModule.{u, v, w} D) : Prop :=
  ∀ n : ℤ, Subsingleton (dgCohomology N n)

/-- Vanishing of a hom-set in the homotopy category.  The current homotopy
category interface is a quotient hom-set without a chosen zero morphism, so
`Subsingleton` is the canonical representation of equality to zero. -/
def HomotopyHomVanishes
    {D : DifferentialGradedAlgebraData (R := R) (A := A)}
    (P N : DGModule.{u, v, w} D) : Prop :=
  Subsingleton (dgHomotopyCategoryHom P N)

/-- A DG module with property (P) is K-projective. -/
theorem property_P_K_projective
    {D : DifferentialGradedAlgebraData (R := R) (A := A)}
    {P : DGModule.{u, v, w} D} (hP : HasPropertyP P)
    (N : DGModule.{u, v, w} D) (hN : IsAcyclic N) :
    HomotopyHomVanishes P N := by
  sorry

/-! ## Good quotients -/

/-- Degreewise surjectivity of a DG-module homomorphism. -/
def DgDegreewiseSurjective
    {D : DifferentialGradedAlgebraData (R := R) (A := A)}
    {M N : DGModule.{u, v, w} D} (f : DGMap M N) : Prop :=
  ∀ n : ℤ, Function.Surjective (f.underlying.app n)

/-- The map induced by a DG homomorphism on cycles in one degree. -/
def dgMapCycles
    {D : DifferentialGradedAlgebraData (R := R) (A := A)}
    {M N : DGModule.{u, v, w} D} (f : DGMap M N) (n : ℤ) :
    dgCycles M n → dgCycles N n := fun x =>
  ⟨f.underlying.app n x,
    by simpa [x.property] using f.commutes_with_differential n x⟩

/-- Surjectivity on cycles, as required in the good-quotient lemma. -/
def DgCycleSurjective
    {D : DifferentialGradedAlgebraData (R := R) (A := A)}
    {M N : DGModule.{u, v, w} D} (f : DGMap M N) : Prop :=
  ∀ n : ℤ, Function.Surjective (dgMapCycles f n)

/-- A cohomology-map specification for a DG homomorphism. -/
def DgCohomologyMapWitness
    {D : DifferentialGradedAlgebraData (R := R) (A := A)}
    {M N : DGModule.{u, v, w} D} (f : DGMap M N) (n : ℤ) : Prop :=
  ∃ φ : dgCohomology M n → dgCohomology N n,
    (∀ x : dgCycles M n,
      φ ((dgBoundary M n).mkQ x) =
        (dgBoundary N n).mkQ (dgMapCycles f n x)) ∧
    Function.Bijective φ

/-- A DG homomorphism is a quasi-isomorphism when it induces bijections on
cohomology. -/
def DgQuasiIsomorphism
    {D : DifferentialGradedAlgebraData (R := R) (A := A)}
    {M N : DGModule.{u, v, w} D} (f : DGMap M N) : Prop :=
  ∀ n : ℤ, DgCohomologyMapWitness f n

/-- The good quotient supplied by the source lemma. -/
theorem exists_good_quotient
    {D : DifferentialGradedAlgebraData (R := R) (A := A)}
    (M : DGModule.{u, v, w} D) :
    ∃ (P : DGModule.{u, v, w} D) (f : DGMap P M),
      DgDegreewiseSurjective f ∧ DgCycleSurjective f ∧
      ∃ (P' P'' : DGModule.{u, v, w} D),
        IsDgShiftedFree P' ∧ IsDgShiftedFree P'' ∧
        Nonempty (DgAdmissibleShortExact P' P P'') := by
  sorry

/-! ## P-resolutions -/

/-- A P-resolution of a DG module. -/
structure PResolution
    {D : DifferentialGradedAlgebraData (R := R) (A := A)}
    (M : DGModule.{u, v, w} D) where
  object : DGModule.{u, v, w} D
  map : DGMap object M
  quasi_isomorphism : DgQuasiIsomorphism map
  property_P : HasPropertyP object

/-- Every differential graded module admits a quasi-isomorphism from a DG
module with property (P). -/
theorem exists_PResolution
    {D : DifferentialGradedAlgebraData (R := R) (A := A)}
    (M : DGModule.{u, v, w} D) :
    Nonempty (PResolution M) := by
  sorry

end Formalization.Books.Dga.Unit20
