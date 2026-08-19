import Formalization.Books.Algebra.Unit72
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.DirectSum.Module
import Mathlib.LinearAlgebra.ExteriorPower.Basic
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.RingTheory.Artinian.Ring
import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.Regular.RegularSequence

/-!
# Commutative Algebra, Chapter 102: What makes a complex exact?

The source works with finite complexes
`0 → R^{n_e} → ⋯ → R^{n_0}`.  A `FiniteFreeComplex` below records the
coordinate finite-free terms and extends the differentials by zero beyond the
last term.  This makes the source's indexing by positive integers explicit
while keeping the square-zero condition and exactness predicates usable.
-/

namespace Formalization.Books.Algebra.Unit102

open Set
open DirectSum
open scoped BigOperators

universe u

noncomputable section

/-! ## Finite free complexes and trivial summands -/

/-- A finite complex of finite free modules in the standard coordinate model.

`differential i` is the map from the term in degree `i + 1` to the term in
degree `i`.  The fields `termRank_zero` and `differential_zero` extend the
finite complex by zero in degrees beyond `length`; this is only bookkeeping
and does not add mathematical hypotheses to the source situation.
-/
structure FiniteFreeComplex (R : Type u) [CommRing R] (length : ℕ) where
  termRank : ℕ → ℕ
  termRank_zero : ∀ i, length < i → termRank i = 0
  differential : ∀ i : ℕ,
    (Fin (termRank (i + 1)) → R) →ₗ[R] (Fin (termRank i) → R)
  differential_zero : ∀ i, length ≤ i → differential i = 0
  differential_comp : ∀ i,
    (differential i).comp (differential (i + 1)) = 0

/-- The differential ending in degree `i`, with its source reindexed from
`i - 1 + 1` to `i`. -/
def FiniteFreeComplex.previousDifferential
    {R : Type u} [CommRing R] {length : ℕ}
    (C : FiniteFreeComplex R length) (i : ℕ) (hi : 0 < i) :
    (Fin (C.termRank i) → R) →ₗ[R] (Fin (C.termRank (i - 1)) → R) := by
  have h : i - 1 + 1 = i := Nat.sub_add_cancel hi
  exact h ▸ C.differential (i - 1)

/-- Exactness at one degree of a finite free complex.

Degree zero is the right endpoint and is not among the degrees at which the
source asks for exactness.  At the left endpoint exactness means injectivity;
at an interior positive degree it means `Function.Exact` for the two adjacent
differentials.
-/
def FiniteFreeComplex.IsExactAt
    {R : Type u} [CommRing R] {length : ℕ}
    (C : FiniteFreeComplex R length) (i : ℕ) : Prop :=
  if hi0 : i = 0 then
    True
  else if _hiL : i = length then
    length ≠ 0 ∧ Function.Injective
      (C.previousDifferential i (Nat.pos_of_ne_zero hi0))
  else if _hi_lt : i < length then
    Function.Exact (C.differential i)
      (C.previousDifferential i (Nat.pos_of_ne_zero hi0))
  else
    True

/-- Exactness at all positive terms of the displayed finite complex. -/
def FiniteFreeComplex.IsExact
    {R : Type u} [CommRing R] {length : ℕ}
    (C : FiniteFreeComplex R length) : Prop :=
  ∀ i, C.IsExactAt i

/-- All matrix coefficients of all differentials lie in an ideal. -/
def FiniteFreeComplex.MatrixEntriesInIdeal
    {R : Type u} [CommRing R] {length : ℕ}
    (C : FiniteFreeComplex R length) (I : Ideal R) : Prop :=
  ∀ i, i < length →
    ∀ a b,
      (LinearMap.toMatrix' (C.differential i)) a b ∈ I

/-- The identity map between the two coordinate rank-one modules.

The heterogeneous equality records that the source and target have both been
identified with `R`, so the map is literally the identity after those
identifications.
-/
def IsIdentityMap
    {R : Type u} [CommRing R] {m n : ℕ}
    (f : (Fin m → R) →ₗ[R] (Fin n → R)) : Prop :=
  m = 1 ∧ n = 1 ∧
    HEq f (LinearMap.id : (Fin 1 → R) →ₗ[R] (Fin 1 → R))

/-- A complex of one of the two trivial forms in the source.

The first disjunct is an identity `R → R` in two adjacent degrees and zero
elsewhere.  The second is a single copy of `R` in degree zero and zero in all
positive degrees.
-/
def FiniteFreeComplex.IsTrivial
    {R : Type u} [CommRing R] {length : ℕ}
    (C : FiniteFreeComplex R length) : Prop :=
  (∃ i : ℕ, ∃ hi : 1 ≤ i,
      i ≤ length ∧ C.termRank i = 1 ∧ C.termRank (i - 1) = 1 ∧
        (∀ j, j ≠ i → j ≠ i - 1 → C.termRank j = 0) ∧
        IsIdentityMap (C.previousDifferential i hi) ∧
        ∀ j, j ≠ i - 1 → C.differential j = 0) ∨
    (C.termRank 0 = 1 ∧
      (∀ j, 0 < j → C.termRank j = 0) ∧
      ∀ j, C.differential j = 0)

/-! The direct-sum interface is expressed using Mathlib's canonical direct sum
of modules.  This records an actual degreewise linear equivalence commuting
with the differentials, rather than introducing a second notion of a complex.
-/

/-- The differential on the direct sum of a finite family of complexes. -/
noncomputable def directSumDifferential
    {R : Type u} [CommRing R] {length k : ℕ}
    (T : Fin k → FiniteFreeComplex R length) (i : ℕ) :
    (⨁ j : Fin k, (Fin ((T j).termRank (i + 1)) → R)) →ₗ[R]
      (⨁ j : Fin k, (Fin ((T j).termRank i) → R)) :=
  DirectSum.lmap (fun j => (T j).differential i)

/-- A degreewise isomorphism from a complex to a direct sum of complexes. -/
structure DirectSumDecomposition
    {R : Type u} [CommRing R] {length k : ℕ}
    (C : FiniteFreeComplex R length)
    (T : Fin k → FiniteFreeComplex R length) where
  component : ∀ i,
    (Fin (C.termRank i) → R) ≃ₗ[R]
      (⨁ j : Fin k, (Fin ((T j).termRank i) → R))
  commute : ∀ i,
    (component i).toLinearMap.comp (C.differential i) =
      (directSumDifferential T i).comp (component (i + 1)).toLinearMap

/-- A finite free complex is a direct sum of trivial complexes. -/
def FiniteFreeComplex.IsDirectSumOfTrivial
    {R : Type u} [CommRing R] {length : ℕ}
    (C : FiniteFreeComplex R length) : Prop :=
  ∃ k : ℕ, ∃ T : Fin k → FiniteFreeComplex R length,
    (∀ j, (T j).IsTrivial) ∧ Nonempty (DirectSumDecomposition C T)

/-- Prepend one complex to a family of summands. -/
def prependSummand
    {R : Type u} [CommRing R] {length k : ℕ}
    (D : FiniteFreeComplex R length)
    (T : Fin k → FiniteFreeComplex R length) :
    Fin (k + 1) → FiniteFreeComplex R length :=
  Fin.cases D (fun j => T j)

/-- Being isomorphic, up to adding trivial direct summands. -/
def IsomorphicUpToTrivialSummands
    {R : Type u} [CommRing R] {length : ℕ}
    (C D : FiniteFreeComplex R length) : Prop :=
  ∃ k : ℕ, ∃ T : Fin k → FiniteFreeComplex R length,
    (∀ j, (T j).IsTrivial) ∧
      Nonempty (DirectSumDecomposition C (prependSummand D T))

/-- The rank vector of the complex after removing an identity summand at `i`.

Only degrees at most `length` are relevant; the predicate is deliberately
stated as an equality of the displayed ranks, matching the source's
`n_i - 1` and `n_{i-1} - 1` notation.
-/
def IsReducedAt
    {R : Type u} [CommRing R] {length : ℕ}
    (C D : FiniteFreeComplex R length) (i : ℕ) : Prop :=
  ∀ j, j ≤ length →
    D.termRank j =
      C.termRank j - (if j = i then 1 else 0) -
        (if j = i - 1 then 1 else 0)

/-! An invertible matrix coefficient permits removal of an identity summand. -/
theorem lemma_add_trivial_complex
    {R : Type u} [CommRing R] {length : ℕ}
    (C : FiniteFreeComplex R length) {i : ℕ}
    (hi : 1 ≤ i) (hi' : i ≤ length)
    (hunit : ∃ a : Fin (C.termRank (i - 1)),
      ∃ b : Fin (C.termRank i),
        IsUnit ((LinearMap.toMatrix'
          (C.previousDifferential i hi)) a b)) :
    ∃ D : FiniteFreeComplex R length,
      IsReducedAt C D i ∧
        ∃ T : FiniteFreeComplex R length,
          T.IsTrivial ∧
            Nonempty
              (DirectSumDecomposition C
                (prependSummand D (fun _ : Fin 1 => T))) := by
  sorry

/-- Repeatedly removing unit coefficients leaves a representative whose
differentials have all coefficients in the maximal ideal, up to trivial
summands. -/
theorem local_reduction_to_maximalIdeal
    {R : Type u} [CommRing R] [IsLocalRing R]
    {length : ℕ} (C : FiniteFreeComplex R length) :
    ∃ D : FiniteFreeComplex R length,
      D.MatrixEntriesInIdeal (IsLocalRing.maximalIdeal R) ∧
        IsomorphicUpToTrivialSummands C D := by
  sorry

/-! ## Depth-zero and Artinian local complexes -/

/-- In a local Noetherian ring, the maximal ideal is associated to `R` exactly
when the local depth of `R` is zero. -/
theorem maximalIdeal_mem_associatedPrimes_iff_localDepth_eq_zero
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R] :
    IsLocalRing.maximalIdeal R ∈ _root_.associatedPrimes R R ↔
      Formalization.Books.Algebra.Unit72.localDepth R R = 0 := by
  rw [Formalization.Books.Algebra.Unit72.depth_eq_zero_iff]
  constructor
  · intro hm
    rcases subsingleton_or_nontrivial R with hsub | hnontr
    · exfalso
      have hprime : (IsLocalRing.maximalIdeal R).IsPrime :=
        (AssociatedPrimes.mem_iff.mp hm).isPrime
      apply hprime.ne_top
      ext x
      have hx : x = 0 := @Subsingleton.elim R hsub _ _
      simp [hx]
    · refine ⟨hnontr, ?_⟩
      intro hreg
      rcases hreg with ⟨x, hx, hxr⟩
      have hx' : x ∈ ((⋃ p ∈ _root_.associatedPrimes R R, (p : Set R)) : Set R) := by
        exact Set.mem_iUnion_of_mem (IsLocalRing.maximalIdeal R)
          (Set.mem_iUnion_of_mem hm hx)
      rw [biUnion_associatedPrimes_eq_compl_regular R R] at hx'
      exact hx' hxr
  · rintro ⟨hnontr, hno⟩
    have hmem_union :
        ((IsLocalRing.maximalIdeal R : Set R) ⊆
          ⋃ p ∈ _root_.associatedPrimes R R, (p : Set R)) ↔
          IsLocalRing.maximalIdeal R ∈ _root_.associatedPrimes R R := by
      apply (Ideal.subset_iUnion_iff_mem_of_isMaximal_of_finite
        (M := IsLocalRing.maximalIdeal R)
        (S := _root_.associatedPrimes R R)
        (_root_.associatedPrimes.finite R R) (⊥ : Ideal R) (⊥ : Ideal R)
        ?_ bot_ne_top bot_ne_top)
      intro I hI _ _
      exact (AssociatedPrimes.mem_iff.mp hI).isPrime
    apply hmem_union.mp
    rw [biUnion_associatedPrimes_eq_compl_regular R R]
    intro x hx
    have hxr : ¬ IsSMulRegular R x := by
      intro hxr
      exact hno ⟨x, hx, hxr⟩
    exact hxr

/-- An exact finite free complex over a local Noetherian ring of depth zero
is a direct sum of trivial complexes. -/
theorem lemma_exact_depth_zero_local
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    {length : ℕ} (C : FiniteFreeComplex R length)
    (hmax : IsLocalRing.maximalIdeal R ∈ _root_.associatedPrimes R R)
    (hC : C.IsExact) :
    C.IsDirectSumOfTrivial := by
  sorry

/-- A local Artinian ring has depth zero. -/
theorem artinian_local_depth_zero
    {R : Type u} [CommRing R] [IsLocalRing R] [IsArtinianRing R] :
    Formalization.Books.Algebra.Unit72.localDepth R R = 0 := by
  rw [Formalization.Books.Algebra.Unit72.depth_eq_zero_iff]
  refine ⟨inferInstance, ?_⟩
  rintro ⟨f, hf, hreg⟩
  obtain ⟨n, hn⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := R)
  have hmax : IsLocalRing.maximalIdeal R = Ideal.jacobson (⊥ : Ideal R) := by
    exact (Ideal.jacobson_bot.trans
      (IsLocalRing.ringJacobson_eq_maximalIdeal R)).symm
  have hfn : f ^ n = 0 := by
    have hmem : f ^ n ∈ (Ideal.jacobson (⊥ : Ideal R)) ^ n := by
      rw [← hmax]
      exact Ideal.pow_mem_pow hf n
    rw [hn] at hmem
    exact hmem
  have hnilpow : ∀ m : ℕ, f ^ m = 0 → False := by
    intro m
    induction m with
    | zero =>
        intro hm
        have hzero : (1 : R) = 0 := by
          simpa only [pow_zero] using hm
        exact one_ne_zero hzero
    | succ m ih =>
        intro hm
        apply ih
        apply hreg.right_eq_zero_of_smul
        simpa [smul_eq_mul, pow_succ, mul_comm] using hm
  exact hnilpow n hfn

/-- An exact finite free complex over an Artinian local ring is a direct sum
of trivial complexes. -/
theorem lemma_exact_artinian_local
    {R : Type u} [CommRing R] [IsLocalRing R] [IsArtinianRing R]
    {length : ℕ} (C : FiniteFreeComplex R length)
    (hC : C.IsExact) :
    C.IsDirectSumOfTrivial := by
  sorry

/-! ## Rank and the ideal of maximal minors -/

/-- The source's rank: the largest exterior power on which a map is nonzero. -/
noncomputable def rank
    {R : Type u} [CommRing R] {m n : ℕ}
    (φ : (Fin m → R) →ₗ[R] (Fin n → R)) : ℕ :=
  sSup {r : ℕ | exteriorPower.map r φ ≠ 0}

/-- The ideal generated by the maximal minors of a coordinate matrix. -/
noncomputable def rankIdeal
    {R : Type u} [CommRing R] {m n : ℕ}
    (φ : (Fin m → R) →ₗ[R] (Fin n → R)) : Ideal R :=
  Ideal.span (Set.range fun p :
      (Fin (rank φ) ↪ Fin n) × (Fin (rank φ) ↪ Fin m) =>
    ((LinearMap.toMatrix' φ).submatrix p.1 p.2).det)

/-- The rank-zero assertion and the associated unit ideal at rank zero. -/
theorem rank_eq_zero_iff
    {R : Type u} [CommRing R] [Nontrivial R] {m n : ℕ}
    (φ : (Fin m → R) →ₗ[R] (Fin n → R)) :
    rank φ = 0 ↔ φ = 0 := by
  sorry

theorem rankIdeal_eq_top_of_rank_eq_zero
    {R : Type u} [CommRing R] [Nontrivial R] {m n : ℕ}
    (φ : (Fin m → R) →ₗ[R] (Fin n → R))
    (hφ : rank φ = 0) :
    rankIdeal φ = ⊤ := by
  sorry

/-- The alternating sum occurring in the source's rank formula. -/
def alternatingRank
    {R : Type u} [CommRing R] {length : ℕ}
    (C : FiniteFreeComplex R length) (i : ℕ) : ℕ :=
    Int.toNat
      (Finset.sum (Finset.Icc i length)
        (fun j => (-1 : ℤ) ^ (j - i) * (C.termRank j : ℤ)))

/-- The rank formula in the Buchsbaum--Eisenbud criterion. -/
def BuchsbaumEisenbudRankCondition
    {R : Type u} [CommRing R] {length : ℕ}
  (C : FiniteFreeComplex R length) : Prop :=
  ∀ i, ∀ (hi : 1 ≤ i), i ≤ length →
    rank (C.previousDifferential i hi) = alternatingRank C i

/-- An ideal contains a regular sequence of the indicated length. -/
def ContainsRegularSequence
    {R : Type u} [CommRing R] (I : Ideal R) (length : ℕ) : Prop :=
  ∃ xs : List R,
    xs.length = length ∧
      (∀ x ∈ xs, x ∈ I) ∧
        RingTheory.Sequence.IsRegular R xs

/-- The grade/minors condition in the source's criterion. -/
def BuchsbaumEisenbudIdealCondition
    {R : Type u} [CommRing R] {length : ℕ}
  (C : FiniteFreeComplex R length) : Prop :=
  ∀ i, ∀ (hi : 1 ≤ i), i ≤ length →
    rankIdeal (C.previousDifferential i hi) = (⊤ : Ideal R) ∨
      ContainsRegularSequence (rankIdeal (C.previousDifferential i hi)) i

/-- The two conditions in the Buchsbaum--Eisenbud exactness criterion. -/
def BuchsbaumEisenbudConditions
    {R : Type u} [CommRing R] {length : ℕ}
    (C : FiniteFreeComplex R length) : Prop :=
  BuchsbaumEisenbudRankCondition C ∧ BuchsbaumEisenbudIdealCondition C

/-- For a direct sum of trivial complexes, the ranks and maximal-minor ideals
have the values listed in the source. -/
theorem lemma_trivial_case_exact
    {R : Type u} [CommRing R] [Nontrivial R] {length : ℕ}
    (C : FiniteFreeComplex R length)
    (hC : C.IsDirectSumOfTrivial) :
      (BuchsbaumEisenbudRankCondition C) ∧
      (∀ i, ∀ (hi : 1 ≤ i), i < length →
        rank (C.differential i) + rank (C.previousDifferential i hi) =
          C.termRank i) ∧
      (∀ i, ∀ (hi : 1 ≤ i), i ≤ length →
        rankIdeal (C.previousDifferential i hi) = (⊤ : Ideal R)) := by
  sorry

/-! ## Quotienting by a nonzerodivisor -/

/-- Scalar extension of a coordinate linear map along a ring homomorphism. -/
noncomputable def mapCoordinateLinearMap
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) {m n : ℕ}
    (φ : (Fin m → R) →ₗ[R] (Fin n → R)) :
    (Fin m → S) →ₗ[S] (Fin n → S) :=
  Matrix.toLin' ((LinearMap.toMatrix' φ).map f)

/-- The differential of the complex after quotienting by `xR`. -/
noncomputable def quotientDifferential
    {R : Type u} [CommRing R] {length : ℕ}
    (C : FiniteFreeComplex R length) (x : R) (i : ℕ) :
    (Fin (C.termRank (i + 1)) → R ⧸ Ideal.span ({x} : Set R)) →ₗ[
      R ⧸ Ideal.span ({x} : Set R)]
        (Fin (C.termRank i) → R ⧸ Ideal.span ({x} : Set R)) :=
  mapCoordinateLinearMap (Ideal.Quotient.mk (Ideal.span ({x} : Set R)))
    (C.differential i)

/-- The quotient differential ending in a positive degree. -/
noncomputable def quotientPreviousDifferential
    {R : Type u} [CommRing R] {length : ℕ}
    (C : FiniteFreeComplex R length) (x : R) (i : ℕ) (hi : 0 < i) :
    (Fin (C.termRank i) → R ⧸ Ideal.span ({x} : Set R)) →ₗ[
      R ⧸ Ideal.span ({x} : Set R)]
        (Fin (C.termRank (i - 1)) → R ⧸ Ideal.span ({x} : Set R)) := by
  have h : i - 1 + 1 = i := Nat.sub_add_cancel hi
  exact h ▸ quotientDifferential C x (i - 1)

/-- The quotient differentials still form a complex. -/
theorem quotientDifferential_comp
    {R : Type u} [CommRing R] {length : ℕ}
    (C : FiniteFreeComplex R length) (x : R) (i : ℕ) :
    (quotientDifferential C x i).comp (quotientDifferential C x (i + 1)) = 0 := by
  sorry

/-- Exactness at a positive degree after quotienting by `xR`. -/
def IsExactAtAfterQuotient
    {R : Type u} [CommRing R] {length : ℕ}
    (C : FiniteFreeComplex R length) (x : R) (i : ℕ) : Prop :=
  if hi0 : i = 0 then
    True
  else if _hiL : i = length then
    length ≠ 0 ∧ Function.Injective
      (quotientPreviousDifferential C x i (Nat.pos_of_ne_zero hi0))
  else if _hi_lt : i < length then
    Function.Exact (quotientDifferential C x i)
      (quotientPreviousDifferential C x i (Nat.pos_of_ne_zero hi0))
  else
    True

/-- Quotienting an exact complex by a nonzerodivisor lowers the range of
degrees in which exactness is asserted by one. -/
theorem lemma_div_x_exact_one_less
    {R : Type u} [CommRing R] [IsLocalRing R]
    {length : ℕ} (C : FiniteFreeComplex R length)
    (hC : C.IsExact) (x : R)
    (hx : x ∈ IsLocalRing.maximalIdeal R)
    (hreg : x ∈ nonZeroDivisors R) :
    ∀ i, 2 ≤ i → i ≤ length → IsExactAtAfterQuotient C x i := by
  sorry

/-! ## The acyclicity lemma -/

/-- A finite complex of finite modules, represented in the module category. -/
structure FiniteModuleComplex (R : Type u) [CommRing R] (length : ℕ) where
  term : ℕ → ModuleCat.{u} R
  term_finite : ∀ i, Module.Finite R (term i)
  differential : ∀ i, term (i + 1) ⟶ term i
  differential_zero : ∀ i, length ≤ i → differential i = 0
  differential_comp : ∀ i,
    (differential i).hom.comp (differential (i + 1)).hom = 0

/-- The differential ending in degree `i` for a finite module complex. -/
def FiniteModuleComplex.previousDifferential
    {R : Type u} [CommRing R] {length : ℕ}
    (C : FiniteModuleComplex R length) (i : ℕ) (hi : 0 < i) :
    (↑(C.term i)) →ₗ[R] (↑(C.term (i - 1))) := by
  have h : i - 1 + 1 = i := Nat.sub_add_cancel hi
  exact h ▸ (C.differential (i - 1)).hom

/-- Exactness at one degree of a finite module complex. -/
def FiniteModuleComplex.IsExactAt
    {R : Type u} [CommRing R] {length : ℕ}
    (C : FiniteModuleComplex R length) (i : ℕ) : Prop :=
  if hi0 : i = 0 then
    True
  else if _hiL : i = length then
    length ≠ 0 ∧ Function.Injective
      (C.previousDifferential i (Nat.pos_of_ne_zero hi0))
  else if _hi_lt : i < length then
    Function.Exact (C.differential i).hom
      (C.previousDifferential i (Nat.pos_of_ne_zero hi0))
  else
    True

/-- The local depth of a finite term. -/
noncomputable def FiniteModuleComplex.termDepth
    {R : Type u} [CommRing R] [IsLocalRing R] {length : ℕ}
    (C : FiniteModuleComplex R length) (i : ℕ) : ℕ∞ :=
  letI : Module.Finite R (C.term i) := C.term_finite i
  Formalization.Books.Algebra.Unit72.depth
    (IsLocalRing.maximalIdeal R) (C.term i)

/-- The kernel/image quotient at a positive term of a module complex. -/
noncomputable def FiniteModuleComplex.homologyModule
    {R : Type u} [CommRing R] {length : ℕ}
  (C : FiniteModuleComplex R length) (i : ℕ) (hi : 0 < i) : Type u :=
  let K : Submodule R (C.term i) := (C.previousDifferential i hi).ker
  K ⧸ (LinearMap.range (C.differential i).hom).comap K.subtype

/-- The local depth of the kernel/image quotient. -/
noncomputable def FiniteModuleComplex.homologyDepth
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    {length : ℕ} (C : FiniteModuleComplex R length) (i : ℕ) (hi : 0 < i) : ℕ∞ :=
  letI : Module.Finite R (C.term i) := C.term_finite i
  let K : Submodule R (C.term i) :=
    (C.previousDifferential i hi).ker
  letI : IsNoetherian R (C.term i) := inferInstance
  letI : IsNoetherian R K :=
    isNoetherian_of_submodule_of_noetherian R (C.term i) K inferInstance
  letI : Module.Finite R K := inferInstance
  let L : Submodule R K :=
    (LinearMap.range (C.differential i).hom).comap K.subtype
  letI : Module.Finite R (K ⧸ L) := Module.Finite.quotient R L
  Formalization.Books.Algebra.Unit72.depth
    (IsLocalRing.maximalIdeal R) (K ⧸ L)

/-- **Acyclicity lemma.**  If the term depths dominate the indices, the
largest non-exact positive term has a kernel/image quotient of depth at least
one. -/
theorem lemma_acyclic
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    {length : ℕ} (C : FiniteModuleComplex R length)
    (hdepth : ∀ j, C.termDepth j ≥ (j : ℕ∞))
    (i : ℕ) (hi : 0 < i) (hi' : i ≤ length)
    (hnot : ¬ C.IsExactAt i)
    (hmax : ∀ j, i < j → C.IsExactAt j) :
    C.homologyDepth i hi ≥ 1 := by
  sorry

/-! ## The Buchsbaum--Eisenbud criterion -/

/-- **What makes a complex exact?**  The source's rank and regular-sequence
conditions are equivalent to exactness of the finite free complex. -/
theorem proposition_what_exact
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    {length : ℕ} (C : FiniteFreeComplex R length) :
    C.IsExact ↔ BuchsbaumEisenbudConditions C := by
  sorry

/-- If the equivalent conditions hold, the ideals of maximal minors become
the unit ideal at a threshold and remain the unit ideal afterwards. -/
theorem remark_what_exact
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    {length : ℕ} (C : FiniteFreeComplex R length)
    (h : C.IsExact ∧ BuchsbaumEisenbudConditions C) :
    ∃ j : ℕ, ∀ i, ∀ (hi : 1 ≤ i), i ≤ length →
      (rankIdeal (C.previousDifferential i hi) = (⊤ : Ideal R) ↔ j ≤ i) := by
  sorry

end

end Formalization.Books.Algebra.Unit102
