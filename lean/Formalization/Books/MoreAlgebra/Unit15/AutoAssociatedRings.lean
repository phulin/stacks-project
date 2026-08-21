import Formalization.Books.Algebra.Unit15.Miscellany
import Formalization.Books.Algebra.Unit24.GlueingFunctions
import Formalization.Books.Algebra.Unit66.WeaklyAssociatedPrimes
import Formalization.Books.Algebra.Unit82.UniversallyInjective
import Formalization.Books.Algebra.Unit84.TransfiniteDevissage
import Formalization.Books.Algebra.Unit88.MittagLefflerModules
import Formalization.Books.Algebra.Unit91.ExamplesAndNonExamples
import Formalization.Books.Algebra.Unit102.WhatMakesAComplexExact
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Matrix.Nonsingular
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# More on Algebra, Chapter 15: Auto-associated rings

This file records the definitions and theorem interfaces in the section
“Auto-associated rings”.  Weak association, universal injectivity, finite
generation, projectivity, and Mittag--Lefflerness use the canonical APIs from
the earlier algebra chapters.
-/

namespace Formalization.Books.MoreAlgebra.Unit15

open Formalization.Books.Algebra.Unit66
open Formalization.Books.Algebra.Unit82
open Formalization.Books.Algebra.Unit88
open scoped TensorProduct

universe u v w

noncomputable section

/-! ## Auto-associated rings -/

/-- A ring is auto-associated when it is local and its maximal ideal is weakly
associated to the ring itself. -/
def AutoAssociated (R : Type u) [CommRing R] : Prop :=
  ∃ hR : IsLocalRing R,
    letI : IsLocalRing R := hR
    IsLocalRing.closedPoint R ∈ weaklyAssociatedPrimes R R

/-- The annihilator of an ideal is nonzero. -/
def HasPropertyP (R : Type u) [CommRing R] : Prop :=
  ∀ I : Ideal R, I ≠ ⊤ → I.FG → Module.annihilator R I ≠ ⊥

/-- Every proper finitely generated ideal in an auto-associated ring has a
nonzero annihilator. -/
theorem autoAssociated_hasPropertyP
    {R : Type u} [CommRing R] (hR : AutoAssociated R) :
    HasPropertyP R := by
  rcases hR with ⟨hR, hweak⟩
  letI : IsLocalRing R := hR
  change ∃ x : R,
    (IsLocalRing.closedPoint R).asIdeal ∈
      ((⊥ : Submodule R R).colon ({x} : Set R)).minimalPrimes at hweak
  rcases hweak with ⟨x, hx⟩
  let J : Ideal R := (⊥ : Submodule R R).colon ({x} : Set R)
  have hJne : J ≠ ⊤ := by
    intro hJ
    have hle : (⊤ : Ideal R) ≤ (IsLocalRing.closedPoint R).asIdeal := by
      rw [← hJ]
      exact hx.1.2
    exact hx.1.1.ne_top (top_le_iff.mp hle)
  have hrad : J.radical = IsLocalRing.maximalIdeal R := by
    have hmax (K : Ideal R) :
        IsLocalRing.maximalIdeal R ∈ K.minimalPrimes ↔
          K.radical = IsLocalRing.maximalIdeal R := by
      constructor
      · intro hK
        apply le_antisymm
        · exact (Ideal.IsPrime.radical_le_iff
            (IsLocalRing.maximalIdeal.isMaximal R).isPrime).mpr hK.1.2
        · rw [Ideal.radical_eq_sInf]
          refine le_sInf ?_
          intro q hq
          exact hK.2 ⟨hq.2, hq.1⟩
            (@IsLocalRing.le_maximalIdeal_of_isPrime R _ _ q hq.2)
      · intro hK
        refine ⟨⟨(IsLocalRing.maximalIdeal.isMaximal R).isPrime, ?_⟩, ?_⟩
        · rw [← hK]
          exact Ideal.le_radical
        · intro q hq hqmax
          rw [← hK]
          exact hq.1.radical_le_iff.mpr hq.2
    apply (hmax J).mp
    simpa [IsLocalRing.closedPoint, J] using hx
  have hxne : x ≠ 0 := by
    intro hx0
    apply hJne
    simp [J, hx0]
  intro I hItop hIFG
  obtain ⟨n, f, hf⟩ := Submodule.fg_iff_exists_fin_generating_family.mp hIFG
  have hIle : I ≤ IsLocalRing.maximalIdeal R :=
    IsLocalRing.le_maximalIdeal hItop
  have hloc : ∀ i : Fin n,
      LocalizedModule.mkLinearMap (Submonoid.powers (f i)) R x = 0 := by
    intro i
    have hfi : f i ∈ J.radical := by
      rw [hrad]
      apply hIle
      rw [← hf]
      exact Ideal.subset_span ⟨i, rfl⟩
    obtain ⟨e, he⟩ := Ideal.mem_radical_iff.mp hfi
    change LocalizedModule.mk x (1 : Submonoid.powers (f i)) = 0
    rw [IsLocalizedModule.mk_eq_mk', IsLocalizedModule.mk'_eq_zero']
    refine ⟨⟨(f i) ^ e, ⟨e, rfl⟩⟩, ?_⟩
    change (f i) ^ e • x = 0
    have he' : (f i) ^ e • x = 0 := by
      simpa [J, Submodule.mem_colon_singleton, smul_eq_mul] using he
    exact he'
  have hα : Formalization.Books.Algebra.Unit24.standardCoverModuleAlpha f R x = 0 := by
    ext i
    exact hloc i
  have hμnot : ¬ Function.Injective
      (Formalization.Books.Algebra.Unit24.standardCoverMultiplicationMap f R) := by
    intro hμ
    have hαinj := (Formalization.Books.Algebra.Unit24.injective_covering_iff f R).2 hμ
    apply hxne
    apply hαinj
    simpa [hα]
  obtain ⟨a, b, habmap, hab⟩ := Function.not_injective_iff.mp hμnot
  let y : R := a - b
  have hyne : y ≠ 0 := by
    dsimp [y]
    exact sub_ne_zero.mpr hab
  have hyfi : ∀ i : Fin n, f i • y = 0 := by
    intro i
    have hi := congrFun habmap i
    change f i * a = f i * b at hi
    calc
      f i • y = f i • (a - b) := by rfl
      _ = f i • a - f i • b := by rw [smul_sub]
      _ = 0 := sub_eq_zero.mpr (by simpa [smul_eq_mul] using hi)
  let K : Ideal R := (⊥ : Submodule R R).colon ({y} : Set R)
  have hIK : I ≤ K := by
    rw [← hf, Ideal.span_le]
    intro z hz
    obtain ⟨i, rfl⟩ := hz
    apply Submodule.mem_colon_singleton.mpr
    simpa [K, smul_eq_mul, mul_comm] using hyfi i
  have hyann : y ∈ Module.annihilator R I := by
    rw [Module.mem_annihilator]
    intro z
    apply Subtype.ext
    change y * (z : R) = 0
    have hzK : (z : R) ∈ K := hIK z.2
    have hzK' := Submodule.mem_colon_singleton.mp hzK
    simpa [K, smul_eq_mul, mul_comm] using hzK'
  intro hzero
  have hybot : y ∈ (⊥ : Ideal R) := by simpa [hzero] using hyann
  exact hyne (by simpa using hybot)

/-- The projective-module formulation of property (P). -/
def ProjectiveInjectivityCondition (R : Type u) [CommRing R] : Prop :=
  ∀ {N : Type v} {M : Type w} [AddCommGroup N] [Module R N]
    [AddCommGroup M] [Module R M]
    [Module.Projective R N] [Module.Projective R M]
    (u : N →ₗ[R] M), Function.Injective u → universallyInjective u

/-- For a fixed map of projective modules over a ring with property (P),
universal injectivity is equivalent to injectivity. -/
theorem universallyInjective_iff_injective_of_hasPropertyP
    {R : Type u} [CommRing R] (hP : HasPropertyP R)
    {N : Type v} {M : Type w} [AddCommGroup N] [Module R N]
    [AddCommGroup M] [Module R M]
    [Module.Projective R N] [Module.Projective R M]
    (u : N →ₗ[R] M) :
    universallyInjective u ↔ Function.Injective u := by
  sorry

/-- The finite-projective cokernel formulation of property (P). -/
def FiniteProjectiveCokernelCondition (R : Type u) [CommRing R] : Prop :=
  ∀ {N : Type v} {M : Type w} [AddCommGroup N] [Module R N]
    [AddCommGroup M] [Module R M]
    [Module.Finite R N] [Module.Projective R N]
    [Module.Finite R M] [Module.Projective R M]
    (u : N →ₗ[R] M), Function.Injective u →
      Module.Finite R (M ⧸ LinearMap.range u) ∧
        Module.Projective R (M ⧸ LinearMap.range u)

/-- The direct-summand formulation of property (P). -/
def FiniteProjectiveDirectSummandCondition (R : Type u) [CommRing R] : Prop :=
  ∀ {M : Type v} [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Module.Projective R M]
    (N : Submodule R M),
    Module.Finite R N → Module.Projective R N →
      IsComplemented N

/-- The split-injection formulation of property (P). -/
def FreeRankOneSplitCondition (R : Type u) [CommRing R] : Prop :=
  ∀ (n : ℕ) (u : R →ₗ[R] (Fin n → R)),
    Function.Injective u →
      ∃ g : (Fin n → R) →ₗ[R] R,
        g.comp u = LinearMap.id

/-- Property (P) is equivalent to the four finite-projective and split-map
formulations in the source lemma. -/
theorem hasPropertyP_iff_finiteProjective_conditions
    {R : Type u} [CommRing R] :
    HasPropertyP R ↔
      (ProjectiveInjectivityCondition R ∧
        FiniteProjectiveCokernelCondition R ∧
        FiniteProjectiveDirectSummandCondition R ∧
        FreeRankOneSplitCondition R) := by
  sorry

/-! ### The countable square-zero example -/

/-! The source indexes the variables and basis vectors by the positive
integers; this file uses `ℕ`, reindexing the first source index to `0`. -/

/-- The polynomial relations imposing `x_i ^ 2 = 0` for every variable. -/
def squareZeroRelations (k : Type u) [CommRing k] : Set (MvPolynomial ℕ k) :=
  Set.range (fun i : ℕ => (MvPolynomial.X i : MvPolynomial ℕ k) ^ 2)

/-- Membership in the square-zero relation ideal is detected monomial by
monomial: every supported exponent vector must contain a square. -/
theorem mem_span_squareZeroRelations_iff
    (k : Type u) [Field k] (f : MvPolynomial ℕ k) :
    f ∈ Ideal.span (squareZeroRelations k) ↔
      ∀ d ∈ f.support, ∃ i : ℕ, Finsupp.single i 2 ≤ d := by
  have hgen : squareZeroRelations k =
      (fun d : ℕ →₀ ℕ => MvPolynomial.monomial d (1 : k)) ''
        Set.range (fun i : ℕ => Finsupp.single i 2) := by
    ext z
    constructor
    · rintro ⟨i, rfl⟩
      refine ⟨Finsupp.single i 2, ⟨i, rfl⟩, ?_⟩
      exact (MvPolynomial.X_pow_eq_monomial
        (R := k) (σ := ℕ) (e := 2) (n := i)).symm
    · rintro ⟨d, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, MvPolynomial.X_pow_eq_monomial
        (R := k) (σ := ℕ) (e := 2) (n := i)⟩
  rw [hgen, MvPolynomial.mem_ideal_span_monomial_image]
  simp only [Set.mem_range]
  constructor
  · intro h d hd
    obtain ⟨si, ⟨i, rfl⟩, hsi⟩ := h d hd
    exact ⟨i, hsi⟩
  · intro h d hd
    obtain ⟨i, hi⟩ := h d hd
    exact ⟨Finsupp.single i 2, ⟨i, rfl⟩, hi⟩

/-- A squarefree monomial remains nonzero in the square-zero quotient. -/
theorem squareZeroMonomial_ne_zero
    (k : Type u) [Field k] (d : ℕ →₀ ℕ) (hd : ∀ i, d i ≤ 1) :
    Ideal.Quotient.mk (Ideal.span (squareZeroRelations k))
      (MvPolynomial.monomial d (1 : k)) ≠ 0 := by
  intro hzero
  have hmem : MvPolynomial.monomial d (1 : k) ∈
      Ideal.span (squareZeroRelations k) :=
    Ideal.Quotient.eq_zero_iff_mem.mp hzero
  have hsupp : d ∈ (MvPolynomial.monomial d (1 : k)).support := by simp
  obtain ⟨i, hi⟩ := (mem_span_squareZeroRelations_iff k _).mp hmem d hsupp
  have hi' : 2 ≤ d i := by simpa using hi i
  have hi'' : d i ≤ 1 := hd i
  omega

/-- The polynomial ring `k[x_1, x_2, ...]/(x_i^2)`, with the source's positive
indices reindexed by `ℕ`. -/
abbrev squareZeroRing (k : Type u) [CommRing k] :=
  MvPolynomial ℕ k ⧸ Ideal.span (squareZeroRelations k)

/-- The image of the `i`-th polynomial variable in the square-zero ring. -/
def squareZeroVariable (k : Type u) [CommRing k] (i : ℕ) : squareZeroRing k :=
  Ideal.Quotient.mk (Ideal.span (squareZeroRelations k)) (MvPolynomial.X i)

@[simp]
theorem squareZeroVariable_sq
    (k : Type u) [CommRing k] (i : ℕ) : squareZeroVariable k i ^ 2 = 0 := by
  rw [squareZeroVariable, ← map_pow, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.subset_span (Set.mem_range_self i)

/-- The quotient endomorphism which erases one square-zero variable. -/
def squareZeroEraseMap (k : Type u) [CommRing k] (n : ℕ) :
    squareZeroRing k →+* squareZeroRing k :=
  Ideal.Quotient.lift (Ideal.span (squareZeroRelations k))
    (MvPolynomial.eval₂Hom
      ((Ideal.Quotient.mk (Ideal.span (squareZeroRelations k))).comp MvPolynomial.C)
      (fun i : ℕ => if i = n then 0 else squareZeroVariable k i)) (by
        intro a ha
        apply (show Ideal.span (squareZeroRelations k) ≤
          RingHom.ker (MvPolynomial.eval₂Hom
            ((Ideal.Quotient.mk (Ideal.span (squareZeroRelations k))).comp MvPolynomial.C)
            (fun i : ℕ => if i = n then 0 else squareZeroVariable k i)) from ?_) ha
        rw [Ideal.span_le]
        rintro _ ⟨i, rfl⟩
        simp [squareZeroVariable_sq])

@[simp]
theorem squareZeroEraseMap_variable_same
    (k : Type u) [CommRing k] (n : ℕ) :
    squareZeroEraseMap k n (squareZeroVariable k n) = 0 := by
  simp [squareZeroEraseMap, squareZeroVariable]

@[simp]
theorem squareZeroEraseMap_variable_of_ne
    (k : Type u) [CommRing k] {n i : ℕ} (h : i ≠ n) :
    squareZeroEraseMap k n (squareZeroVariable k i) = squareZeroVariable k i := by
  simp [squareZeroEraseMap, squareZeroVariable, h]

/-- Every quotient element is fixed by erasing some sufficiently late variable. -/
theorem exists_squareZeroEraseMap_eq
    (k : Type u) [Field k] (a : squareZeroRing k) (start : ℕ) :
    ∃ n ≥ start, squareZeroEraseMap k n a = a := by
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective a
  let n : ℕ := max start (f.vars.sup id + 1)
  refine ⟨n, le_max_left _ _, ?_⟩
  change MvPolynomial.eval₂Hom
      ((Ideal.Quotient.mk (Ideal.span (squareZeroRelations k))).comp MvPolynomial.C)
      (fun i : ℕ => if i = n then 0 else squareZeroVariable k i) f =
    Ideal.Quotient.mk (Ideal.span (squareZeroRelations k)) f
  apply MvPolynomial.hom_congr_vars
  · ext c
    simp
  · intro i hi _
    have hin : i ≠ n := by
      have hle : i ≤ f.vars.sup id := Finset.le_sup (f := id) hi
      have hlt : f.vars.sup id < n := by
        exact lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_right _ _)
      exact ne_of_lt (lt_of_le_of_lt hle hlt)
    simp [hin, squareZeroVariable]
  · rfl

/-- Every finite product of distinct square-zero variables is nonzero. -/
theorem squareZeroVariables_prod_ne_zero
    (k : Type u) [Field k] (n : ℕ) :
    (∏ i ∈ Finset.range n, squareZeroVariable k i) ≠ 0 := by
  let d : ℕ →₀ ℕ := ∑ i ∈ Finset.range n, Finsupp.single i 1
  have hpoly : (∏ i ∈ Finset.range n,
      (MvPolynomial.X i : MvPolynomial ℕ k)) =
      MvPolynomial.monomial d 1 := by
    dsimp [d]
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.prod_range_succ, Finset.sum_range_succ, ih]
      simp [MvPolynomial.X, MvPolynomial.monomial_mul]
  have hd (i : ℕ) : d i ≤ 1 := by
    simp [d, Finsupp.single_apply]
    split <;> omega
  change (∏ i ∈ Finset.range n,
    Ideal.Quotient.mk (Ideal.span (squareZeroRelations k))
      (MvPolynomial.X i)) ≠ 0
  rw [← map_prod, hpoly]
  exact squareZeroMonomial_ne_zero k d hd

/-- The residue map which sends every polynomial variable to zero. -/
def squareZeroResidueMap (k : Type u) [CommRing k] : squareZeroRing k →+* k :=
  Ideal.Quotient.lift (Ideal.span (squareZeroRelations k))
    (MvPolynomial.eval₂Hom (RingHom.id k) (fun _ : ℕ => 0)) (by
      change Ideal.span (squareZeroRelations k) ≤
        RingHom.ker (MvPolynomial.eval₂Hom (RingHom.id k) (fun _ : ℕ => 0))
      rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      simp)

/-- The map on the countable free module sending `e_i` to
`f_i - x_i f_(i+1)` (with the source's positive indices reindexed by `ℕ`). -/
def squareZeroMap (k : Type u) [CommRing k] :
    (ℕ →₀ squareZeroRing k) →ₗ[squareZeroRing k] (ℕ →₀ squareZeroRing k) :=
  Finsupp.linearCombination (squareZeroRing k)
    (fun i : ℕ =>
      Finsupp.single i (1 : squareZeroRing k) -
        squareZeroVariable k i • Finsupp.single (i + 1) (1 : squareZeroRing k))

/-- The finite restriction of the square-zero map. -/
def squareZeroFiniteMap (k : Type u) [CommRing k] (n : ℕ) :
    (Fin n →₀ squareZeroRing k) →ₗ[squareZeroRing k] (ℕ →₀ squareZeroRing k) :=
  Finsupp.linearCombination (squareZeroRing k)
    (fun i : Fin n =>
      Finsupp.single i.1 (1 : squareZeroRing k) -
        squareZeroVariable k i.1 • Finsupp.single (i.1 + 1) (1 : squareZeroRing k))

@[simp]
theorem squareZeroMap_apply_zero
    (k : Type u) [Field k] (x : ℕ →₀ squareZeroRing k) :
    squareZeroMap k x 0 = x 0 := by
  induction x using Finsupp.induction with
  | zero => simp
  | @single_add i a x hi ha ih =>
    rw [map_add, Finsupp.add_apply, Finsupp.add_apply, ih]
    simp [squareZeroMap, Finsupp.single_apply]

@[simp]
theorem squareZeroMap_apply_succ
    (k : Type u) [Field k] (x : ℕ →₀ squareZeroRing k) (j : ℕ) :
    squareZeroMap k x (j + 1) =
      x (j + 1) - squareZeroVariable k j * x j := by
  induction x using Finsupp.induction with
  | zero => simp
  | @single_add i a x hi ha ih =>
    have hmap := (squareZeroMap k).map_add (Finsupp.single i a) x
    rw [hmap]
    change squareZeroMap k (Finsupp.single i a) (j + 1) +
        squareZeroMap k x (j + 1) =
      Finsupp.single i a (j + 1) + x (j + 1) -
        squareZeroVariable k j * (Finsupp.single i a j + x j)
    rw [ih]
    by_cases hij : i = j
    · subst i
      simp [squareZeroMap, Finsupp.single_apply, mul_add, add_sub] <;> ring
    · by_cases his : i = j + 1
      · subst i
        simp [squareZeroMap, Finsupp.single_apply, hij, mul_add] <;> ring
      · have hsucc : i + 1 ≠ j + 1 := by omega
        simp [squareZeroMap, Finsupp.single_apply, hij, his, hsucc, mul_add] <;> ring

/-- The countable square-zero ring is auto-associated. -/
theorem squareZeroRing_autoAssociated
    (k : Type u) [Field k] :
    AutoAssociated (squareZeroRing k) := by
  sorry

/-- Every finite restriction of the displayed map is injective. -/
theorem squareZeroFiniteMap_injective
    (k : Type u) [Field k] (n : ℕ) :
    Function.Injective (squareZeroFiniteMap k n) := by
  intro x y h
  change Finsupp.linearCombination (squareZeroRing k) _ x =
    Finsupp.linearCombination (squareZeroRing k) _ y at h
  let v : Fin n → (ℕ →₀ squareZeroRing k) := fun i =>
    Finsupp.single i.1 (1 : squareZeroRing k) -
      squareZeroVariable k i.1 • Finsupp.single (i.1 + 1) (1 : squareZeroRing k)
  let z : Fin n →₀ squareZeroRing k := x - y
  have hz : Finsupp.linearCombination (squareZeroRing k) v z = 0 := by
    dsimp [z, v]
    rw [map_sub, h]
    exact sub_self _
  by_contra hne
  have hzne : z ≠ 0 := by
    intro hz0
    apply hne
    exact sub_eq_zero.mp (by simpa [z] using hz0)
  have hsn : z.support.Nonempty := Finsupp.support_nonempty_iff.mpr hzne
  let j : Fin n := z.support.min' hsn
  have hj : j ∈ z.support := by
    dsimp [j]
    exact Finset.min'_mem _ _
  have hjcoord : (Finsupp.linearCombination (squareZeroRing k) v z) j.1 = z j := by
    rw [Finsupp.linearCombination_apply, Finsupp.sum_apply, Finsupp.sum]
    rw [Finset.sum_eq_single j]
    · simp [v]
    · intro i hi hij
      have hle : j ≤ i := by
        dsimp [j]
        exact Finset.min'_le z.support i hi
      have hle' : j.1 ≤ i.1 := hle
      have hneNat : i.1 ≠ j.1 := by
        intro heq
        apply hij
        exact Fin.ext heq
      have hsucc' : i.1 + 1 ≠ j.1 := by omega
      simp [v, hneNat, hsucc']
    · intro hjnot
      exact (hjnot hj).elim
  have hzj : z j = 0 := by
    rw [← hjcoord]
    rw [hz]
    rfl
  exact (Finsupp.notMem_support_iff.mpr hzj) hj

/-- The displayed finite images are linearly independent. -/
theorem squareZeroFiniteMap_linearIndependent
    (k : Type u) [Field k] (n : ℕ) :
    LinearIndependent (squareZeroRing k)
      (fun i : Fin n =>
        Finsupp.single i.1 (1 : squareZeroRing k) -
          squareZeroVariable k i.1 •
            Finsupp.single (i.1 + 1) (1 : squareZeroRing k)) := by
  apply linearIndependent_iff_injective_finsuppLinearCombination.mpr
  exact squareZeroFiniteMap_injective k n

/-- The displayed map on the countable free module is injective. -/
theorem squareZeroMap_injective
    (k : Type u) [Field k] : Function.Injective (squareZeroMap k) := by
  intro x y h
  change Finsupp.linearCombination (squareZeroRing k) _ x =
    Finsupp.linearCombination (squareZeroRing k) _ y at h
  let v : ℕ → (ℕ →₀ squareZeroRing k) := fun i =>
    Finsupp.single i (1 : squareZeroRing k) -
      squareZeroVariable k i • Finsupp.single (i + 1) (1 : squareZeroRing k)
  let z : ℕ →₀ squareZeroRing k := x - y
  have hz : Finsupp.linearCombination (squareZeroRing k) v z = 0 := by
    dsimp [z, v]
    rw [map_sub, h]
    exact sub_self _
  by_contra hne
  have hzne : z ≠ 0 := by
    intro hz0
    apply hne
    exact sub_eq_zero.mp (by simpa [z] using hz0)
  have hsn : z.support.Nonempty := Finsupp.support_nonempty_iff.mpr hzne
  let j : ℕ := z.support.min' hsn
  have hj : j ∈ z.support := by
    dsimp [j]
    exact Finset.min'_mem _ _
  have hjcoord : (Finsupp.linearCombination (squareZeroRing k) v z) j = z j := by
    rw [Finsupp.linearCombination_apply, Finsupp.sum_apply, Finsupp.sum]
    rw [Finset.sum_eq_single j]
    · simp [v]
    · intro i hi hij
      have hle : j ≤ i := by
        dsimp [j]
        exact Finset.min'_le z.support i hi
      have hsucc : i + 1 ≠ j := by omega
      simp [v, hij, hsucc]
    · intro hjnot
      exact (hjnot hj).elim
  have hzj : z j = 0 := by
    rw [← hjcoord, hz]
    rfl
  exact (Finsupp.notMem_support_iff.mpr hzj) hj

/-- The displayed map is universally injective. -/
theorem squareZeroMap_universallyInjective
    (k : Type u) [Field k] : universallyInjective (squareZeroMap k) := by
  apply (universallyInjective_iff_injective_of_hasPropertyP
    (autoAssociated_hasPropertyP (squareZeroRing_autoAssociated k))
    (squareZeroMap k)).2
  exact squareZeroMap_injective k

/-- The residue-field tensor of the displayed map is bijective; the ring map
to the coefficient field supplies the scalar restriction used for the tensor. -/
theorem squareZeroMap_residueTensor_bijective
    (k : Type u) [Field k] :
    letI : Module (squareZeroRing k) k :=
      Module.compHom k (squareZeroResidueMap k)
    Function.Bijective ((squareZeroMap k).rTensor k) := by
  letI : Module (squareZeroRing k) k :=
    Module.compHom k (squareZeroResidueMap k)
  have hvar (i : ℕ) (q : k) : squareZeroVariable k i • q = 0 := by
    change squareZeroResidueMap k (squareZeroVariable k i) * q = 0
    simp [squareZeroVariable, squareZeroResidueMap]
  have hmap : (squareZeroMap k).rTensor k = LinearMap.id := by
    apply LinearMap.ext
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul x q =>
      induction x using Finsupp.induction with
      | zero => simp
      | @single_add i a x hi ha ih =>
        rw [TensorProduct.add_tmul, map_add, ih]
        simp only [squareZeroMap, LinearMap.rTensor_tmul,
          Finsupp.linearCombination_single, LinearMap.id_apply]
        congr 1
        rw [TensorProduct.smul_tmul, TensorProduct.sub_tmul]
        simp only [Finsupp.smul_single, smul_eq_mul, mul_one]
        rw [show Finsupp.single (i + 1) (squareZeroVariable k i) =
          squareZeroVariable k i •
            Finsupp.single (i + 1) (1 : squareZeroRing k) by simp]
        rw [TensorProduct.smul_tmul (R := squareZeroRing k)
          (squareZeroVariable k i)
          (Finsupp.single (i + 1) (1 : squareZeroRing k)) (a • q), hvar]
        simp
        have hs : a • Finsupp.single i (1 : squareZeroRing k) =
            Finsupp.single i a := by
          ext j
          simp [Finsupp.single_apply]
        change a •
            (Finsupp.single i (1 : squareZeroRing k) ⊗ₜ[squareZeroRing k] q) =
          Finsupp.single i a ⊗ₜ[squareZeroRing k] q
        rw [TensorProduct.smul_tmul' (R := squareZeroRing k), hs]
    | add x y hx hy => simp [hx, hy]
  rw [hmap]
  exact Function.bijective_id

/-- The first basis vector has no preimage under the displayed map. -/
theorem squareZeroMap_firstBasis_no_preimage
    (k : Type u) [Field k] :
    ¬ ∃ x : ℕ →₀ squareZeroRing k,
      squareZeroMap k x = Finsupp.single 0 (1 : squareZeroRing k) := by
  rintro ⟨x, hx⟩
  have hx0 : x 0 = 1 := by
    have h := congrArg (fun y : ℕ →₀ squareZeroRing k => y 0) hx
    simpa using h
  have hrec (j : ℕ) : x (j + 1) = squareZeroVariable k j * x j := by
    have h := congrArg (fun y : ℕ →₀ squareZeroRing k => y (j + 1)) hx
    rw [squareZeroMap_apply_succ] at h
    have hrhs : Finsupp.single 0 (1 : squareZeroRing k) (j + 1) = 0 := by
      simp [Finsupp.single_apply]
    rw [hrhs] at h
    exact sub_eq_zero.mp h
  have hprod (n : ℕ) :
      x n = ∏ i ∈ Finset.range n, squareZeroVariable k i := by
    induction n with
    | zero => simpa using hx0
    | succ n ih =>
      rw [hrec, ih, Finset.prod_range_succ]
      exact mul_comm _ _
  have hsupp : x.support.Nonempty := by
    refine ⟨0, ?_⟩
    apply Finsupp.mem_support_iff.mpr
    rw [hx0]
    simpa using squareZeroVariables_prod_ne_zero k 0
  let m : ℕ := x.support.max' hsupp
  have hmout : m + 1 ∉ x.support := by
    intro hm
    have hle : m + 1 ≤ m := by
      dsimp [m]
      exact Finset.le_max' x.support (m + 1) hm
    omega
  have hxout : x (m + 1) = 0 := Finsupp.notMem_support_iff.mp hmout
  apply squareZeroVariables_prod_ne_zero k (m + 1)
  rw [← hprod, hxout]

/-- The displayed map is not surjective. -/
theorem squareZeroMap_not_surjective
    (k : Type u) [Field k] : ¬ Function.Surjective (squareZeroMap k) := by
  intro hsurjective
  apply squareZeroMap_firstBasis_no_preimage k
  exact hsurjective (Finsupp.single 0 (1 : squareZeroRing k))

/-- A splitting of the displayed map would make it surjective. -/
theorem squareZeroMap_split_implies_surjective
    (k : Type u) [Field k]
    (g : (ℕ →₀ squareZeroRing k) →ₗ[squareZeroRing k] (ℕ →₀ squareZeroRing k))
    (hg : g.comp (squareZeroMap k) = LinearMap.id) :
    Function.Surjective (squareZeroMap k) := by
  let u := squareZeroMap k
  let h : (ℕ →₀ squareZeroRing k) →ₗ[squareZeroRing k]
      (ℕ →₀ squareZeroRing k) := LinearMap.id - u.comp g
  have hhu : h.comp u = 0 := by
    apply LinearMap.ext
    intro x
    have hx := congrArg (fun f => f x) hg
    change u x - u (g (u x)) = 0
    apply sub_eq_zero.mpr
    exact (congrArg u hx).symm
  have hrec (i : ℕ) :
      h (Finsupp.single i (1 : squareZeroRing k)) =
        squareZeroVariable k i •
          h (Finsupp.single (i + 1) (1 : squareZeroRing k)) := by
    have hi := congrArg (fun f => f (Finsupp.single i (1 : squareZeroRing k))) hhu
    change h (u (Finsupp.single i (1 : squareZeroRing k))) = 0 at hi
    have hui : u (Finsupp.single i (1 : squareZeroRing k)) =
        Finsupp.single i 1 - squareZeroVariable k i •
          Finsupp.single (i + 1) 1 := by
      simp [u, squareZeroMap]
    rw [hui, map_sub, map_smul] at hi
    exact sub_eq_zero.mp hi
  have hiter (i t : ℕ) :
      h (Finsupp.single i (1 : squareZeroRing k)) =
        (∏ j ∈ Finset.range t, squareZeroVariable k (i + j)) •
          h (Finsupp.single (i + t) (1 : squareZeroRing k)) := by
    induction t with
    | zero => simp
    | succ t iht =>
      rw [iht, hrec (i + t), Finset.prod_range_succ]
      calc
        _ = ((∏ j ∈ Finset.range t, squareZeroVariable k (i + j)) *
              squareZeroVariable k (i + t)) •
            h (Finsupp.single (i + t + 1) 1) :=
          (mul_smul
            (∏ j ∈ Finset.range t, squareZeroVariable k (i + j) : squareZeroRing k)
            (squareZeroVariable k (i + t) : squareZeroRing k)
            (h (Finsupp.single (i + t + 1) 1) : ℕ →₀ squareZeroRing k)).symm
        _ = _ := by
          congr 2 <;> omega
  have hbasis (i : ℕ) :
      h (Finsupp.single i (1 : squareZeroRing k)) = 0 := by
    apply Finsupp.ext
    intro l
    let a : squareZeroRing k := h (Finsupp.single i 1) l
    obtain ⟨n, hin, herase⟩ := exists_squareZeroEraseMap_eq k a i
    have hdiv := congrArg (fun z : ℕ →₀ squareZeroRing k => z l)
      (hiter i (n - i + 1))
    change a =
      (∏ j ∈ Finset.range (n - i + 1), squareZeroVariable k (i + j)) *
        h (Finsupp.single (i + (n - i + 1)) 1) l at hdiv
    have hzero : squareZeroEraseMap k n
        (∏ j ∈ Finset.range (n - i + 1), squareZeroVariable k (i + j)) = 0 := by
      rw [map_prod]
      apply Finset.prod_eq_zero (Finset.mem_range.mpr (by omega) : n - i ∈
        Finset.range (n - i + 1))
      have hadd : i + (n - i) = n := Nat.add_sub_of_le hin
      simp [hadd]
    have herased := congrArg (squareZeroEraseMap k n) hdiv
    rw [herase, map_mul, hzero, zero_mul] at herased
    exact herased
  have hh : h = 0 := by
    apply LinearMap.ext
    intro x
    induction x using Finsupp.induction with
    | zero => simp
    | @single_add i a x hi ha ih =>
      rw [map_add, ih]
      simp only [LinearMap.zero_apply, add_zero]
      have hs : Finsupp.single i a =
          a • Finsupp.single i (1 : squareZeroRing k) := by
        ext j
        simp [Finsupp.single_apply]
      rw [hs, map_smul, hbasis, smul_zero]
  intro y
  refine ⟨g y, ?_⟩
  have hy := congrArg (fun f => f y) hh
  change y - u (g y) = 0 at hy
  exact (sub_eq_zero.mp hy).symm

/-- The cokernel of the displayed map is flat. -/
theorem squareZeroMap_cokernel_flat
    (k : Type u) [Field k] :
    Module.Flat (squareZeroRing k)
      ((ℕ →₀ squareZeroRing k) ⧸ LinearMap.range (squareZeroMap k)) := by
  apply Formalization.Books.Algebra.Unit39.flat_quotient_of_ideal_quotient_injective
    (squareZeroMap k) inferInstance
  intro I hI
  exact ((universallyInjective_into_flat_iff (squareZeroMap k) inferInstance).mp
    (squareZeroMap_universallyInjective k)) I hI

/-- The cokernel of the displayed map is countably generated. -/
theorem squareZeroMap_cokernel_countablyGenerated
    (k : Type u) [Field k] :
    Formalization.Books.Algebra.Unit84.Module.IsCountablyGenerated
      (squareZeroRing k)
      ((ℕ →₀ squareZeroRing k) ⧸ LinearMap.range (squareZeroMap k)) := by
  let b : Module.Basis ℕ (squareZeroRing k) (ℕ →₀ squareZeroRing k) :=
    Finsupp.basisSingleOne
  let q : (ℕ →₀ squareZeroRing k) →ₗ[squareZeroRing k]
      ((ℕ →₀ squareZeroRing k) ⧸ LinearMap.range (squareZeroMap k)) :=
    Submodule.mkQ (LinearMap.range (squareZeroMap k))
  refine ⟨q '' Set.range b, Set.countable_range b |>.image q, ?_⟩
  rw [← Submodule.map_span, b.span_eq]
  rw [Submodule.map_top]
  exact LinearMap.range_eq_top.mpr (by
    simpa [q] using
      (Submodule.mkQ_surjective
        (p := LinearMap.range (squareZeroMap k))))

/-- The cokernel of the displayed map is not projective. -/
theorem squareZeroMap_cokernel_not_projective
    (k : Type u) [Field k] :
    ¬ Module.Projective (squareZeroRing k)
      ((ℕ →₀ squareZeroRing k) ⧸ LinearMap.range (squareZeroMap k)) := by
  intro hprojective
  letI : Module.Projective (squareZeroRing k)
      ((ℕ →₀ squareZeroRing k) ⧸ LinearMap.range (squareZeroMap k)) :=
    hprojective
  let u := squareZeroMap k
  let q : (ℕ →₀ squareZeroRing k) →ₗ[squareZeroRing k]
      ((ℕ →₀ squareZeroRing k) ⧸ LinearMap.range u) :=
    Submodule.mkQ (LinearMap.range u)
  obtain ⟨s, hs⟩ := Module.projective_lifting_property q LinearMap.id
    (Submodule.mkQ_surjective (p := LinearMap.range u))
  let p : (ℕ →₀ squareZeroRing k) →ₗ[squareZeroRing k]
      (ℕ →₀ squareZeroRing k) := LinearMap.id - s.comp q
  have hp0 : q.comp p = 0 := by
    apply LinearMap.ext
    intro x
    dsimp [p]
    have hx := congrArg (fun f => f (q x)) hs
    have hx' : q (s (q x)) = q x := by
      simpa [LinearMap.comp_apply] using hx
    simp only [map_sub, hx']
    exact sub_self (q x)
  have hp_mem (x : ℕ →₀ squareZeroRing k) : p x ∈ LinearMap.range u := by
    rw [← Submodule.ker_mkQ (p := LinearMap.range u)]
    exact congrArg (fun f => f x) hp0
  have hu : Function.Injective u := squareZeroMap_injective k
  let e : (ℕ →₀ squareZeroRing k) ≃ₗ[squareZeroRing k] LinearMap.range u :=
    LinearEquiv.ofInjective u hu
  let r : (ℕ →₀ squareZeroRing k) →ₗ[squareZeroRing k]
      (ℕ →₀ squareZeroRing k) := e.symm.toLinearMap.comp
        (p.codRestrict (LinearMap.range u) hp_mem)
  have hur : u.comp r = p := by
    apply LinearMap.ext
    intro x
    change u (e.symm (p.codRestrict (LinearMap.range u) hp_mem x)) = p x
    exact congrArg Subtype.val (e.apply_symm_apply _)
  have hpu : p.comp u = u := by
    apply LinearMap.ext
    intro x
    have hqu : q (u x) = 0 := by
      apply Quotient.sound
      exact (Submodule.quotientRel_def (LinearMap.range u)).2
        ⟨x, by simp⟩
    simp [p, LinearMap.comp_apply, hqu]
  have hru : r.comp u = LinearMap.id := by
    apply LinearMap.ext
    intro x
    apply hu
    have h₁ := congrArg (fun f => f (u x)) hur
    have h₂ := congrArg (fun f => f x) hpu
    exact h₁.trans h₂
  exact squareZeroMap_not_surjective k
    (squareZeroMap_split_implies_surjective k r (by simpa [u] using hru))

/-- The cokernel of the displayed map is flat, countably generated, and not
projective; consequently it is not Mittag--Leffler. -/
theorem squareZeroMap_cokernel_properties
    (k : Type u) [Field k] :
    Module.Flat (squareZeroRing k)
        ((ℕ →₀ squareZeroRing k) ⧸ LinearMap.range (squareZeroMap k)) ∧
      Formalization.Books.Algebra.Unit84.Module.IsCountablyGenerated
        (squareZeroRing k)
        ((ℕ →₀ squareZeroRing k) ⧸ LinearMap.range (squareZeroMap k)) ∧
      ¬ Module.Projective (squareZeroRing k)
        ((ℕ →₀ squareZeroRing k) ⧸ LinearMap.range (squareZeroMap k)) ∧
      ¬ IsMittagLefflerModule
        (ModuleCat.of (squareZeroRing k)
          ((ℕ →₀ squareZeroRing k) ⧸ LinearMap.range (squareZeroMap k))) := by
  have hflat := squareZeroMap_cokernel_flat k
  have hcount := squareZeroMap_cokernel_countablyGenerated k
  have hnotproj := squareZeroMap_cokernel_not_projective k
  exact ⟨hflat, hcount, hnotproj,
    Formalization.Books.Algebra.Unit91.flat_countablyGenerated_nonprojective_not_mittagLeffler
        hflat hcount hnotproj⟩

/-! ### Maps of finite free modules -/

/-- For a map of finite free modules, injectivity is equivalent to full rank
and zero annihilator of its determinantal ideal. -/
theorem exactLengthOne_iff
    {R : Type u} [CommRing R] [IsLocalRing R] {m n : ℕ}
    (φ : (Fin m → R) →ₗ[R] (Fin n → R)) :
    Function.Injective φ ↔
      Formalization.Books.Algebra.Unit102.rank φ = m ∧
        Module.annihilator R
            (Formalization.Books.Algebra.Unit102.rankIdeal φ) = ⊥ := by
  sorry

/-- In the Noetherian local case, the nonzerodivisor formulation is equivalent
to the two preceding formulations. -/
theorem exactLengthOne_noetherian_tfae
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    {m n : ℕ} (φ : (Fin m → R) →ₗ[R] (Fin n → R)) :
    List.TFAE [
      Function.Injective φ,
      Formalization.Books.Algebra.Unit102.rank φ = m ∧
        Module.annihilator R
            (Formalization.Books.Algebra.Unit102.rankIdeal φ) = ⊥,
      Formalization.Books.Algebra.Unit102.rank φ = m ∧
        (Formalization.Books.Algebra.Unit102.rankIdeal φ = ⊤ ∨
          ∃ x : R, x ∈ Formalization.Books.Algebra.Unit102.rankIdeal φ ∧
            x ∈ nonZeroDivisors R)] := by
  sorry

/-- The dual of the cokernel of an injective endomorphism of a finite free
module is zero. -/
theorem coker_injective_free_dual_eq_zero
    {R : Type u} [CommRing R] {n : ℕ}
    (φ : (Fin n → R) →ₗ[R] (Fin n → R)) (hφ : Function.Injective φ) :
    ∀ f : ((Fin n → R) ⧸ LinearMap.range φ) →ₗ[R] R, f = 0 := by
  intro f
  let q : (Fin n → R) →ₗ[R] ((Fin n → R) ⧸ LinearMap.range φ) :=
    (LinearMap.range φ).mkQ
  let l : (Fin n → R) →ₗ[R] R := f.comp q
  let A : Matrix (Fin n) (Fin n) R := LinearMap.toMatrix' φ
  have hAinj : Function.Injective A.mulVec := by
    intro x y hxy
    apply hφ
    simpa only [A, LinearMap.toMatrix'_mulVec] using hxy
  have hAns : A.Nonsingular :=
    Matrix.Nonsingular.of_linearIndependent_col
      (Matrix.mulVec_injective_iff.mp hAinj)
  let c : Fin n → R := fun i => l (Pi.single i 1)
  have hlφ : l.comp φ = 0 := by
    apply LinearMap.ext
    intro x
    change f (q (φ x)) = 0
    rw [show q (φ x) = 0 by
      apply LinearMap.mem_ker.mp
      change φ x ∈ LinearMap.ker (LinearMap.range φ).mkQ
      rw [Submodule.ker_mkQ]
      exact ⟨x, rfl⟩]
    exact f.map_zero
  have hl_apply (x : Fin n → R) : l x = ∑ i, x i * c i := by
    conv_lhs => rw [← (Pi.basisFun R (Fin n)).sum_repr x]
    rw [map_sum]
    simp only [map_smul, Pi.basisFun_repr, Pi.basisFun_apply, c, smul_eq_mul]
  have hcA : Matrix.vecMul c A = 0 := by
    funext j
    have hj := LinearMap.congr_fun hlφ (Pi.single j 1)
    rw [LinearMap.comp_apply, LinearMap.zero_apply, hl_apply] at hj
    simpa only [A, LinearMap.toMatrix'_apply, c, Matrix.vecMul, dotProduct,
      Pi.zero_apply, mul_comm] using hj
  have hc : c = 0 := by
    apply (Matrix.vecMul_injective_iff.mpr hAns.linearIndependent_row)
    simpa using hcA
  have hl : l = 0 := by
    apply LinearMap.ext
    intro x
    rw [hl_apply, hc]
    simp
  apply LinearMap.ext
  intro y
  induction y using Submodule.Quotient.induction_on with
  | _ x => exact LinearMap.congr_fun hl x

end

end Formalization.Books.MoreAlgebra.Unit15
