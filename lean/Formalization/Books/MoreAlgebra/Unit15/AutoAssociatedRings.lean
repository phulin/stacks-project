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

/-- The polynomial ring `k[x_1, x_2, ...]/(x_i^2)`, with the source's positive
indices reindexed by `ℕ`. -/
abbrev squareZeroRing (k : Type u) [CommRing k] :=
  MvPolynomial ℕ k ⧸ Ideal.span (squareZeroRelations k)

/-- The image of the `i`-th polynomial variable in the square-zero ring. -/
def squareZeroVariable (k : Type u) [CommRing k] (i : ℕ) : squareZeroRing k :=
  Ideal.Quotient.mk (Ideal.span (squareZeroRelations k)) (MvPolynomial.X i)

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
  sorry

/-- The displayed map is universally injective. -/
theorem squareZeroMap_universallyInjective
    (k : Type u) [Field k] : universallyInjective (squareZeroMap k) := by
  sorry

/-- The residue-field tensor of the displayed map is bijective; the ring map
to the coefficient field supplies the scalar restriction used for the tensor. -/
theorem squareZeroMap_residueTensor_bijective
    (k : Type u) [Field k] :
    letI : Module (squareZeroRing k) k :=
      Module.compHom k (squareZeroResidueMap k)
    Function.Bijective ((squareZeroMap k).rTensor k) := by
  sorry

/-- The displayed map is not surjective. -/
theorem squareZeroMap_not_surjective
    (k : Type u) [Field k] : ¬ Function.Surjective (squareZeroMap k) := by
  sorry

/-- The first basis vector has no preimage under the displayed map. -/
theorem squareZeroMap_firstBasis_no_preimage
    (k : Type u) [Field k] :
    ¬ ∃ x : ℕ →₀ squareZeroRing k,
      squareZeroMap k x = Finsupp.single 0 (1 : squareZeroRing k) := by
  sorry

/-- A splitting of the displayed map would make it surjective. -/
theorem squareZeroMap_split_implies_surjective
    (k : Type u) [Field k]
    (g : (ℕ →₀ squareZeroRing k) →ₗ[squareZeroRing k] (ℕ →₀ squareZeroRing k))
    (hg : g.comp (squareZeroMap k) = LinearMap.id) :
    Function.Surjective (squareZeroMap k) := by
  sorry

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
  sorry

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
  sorry

end

end Formalization.Books.MoreAlgebra.Unit15
