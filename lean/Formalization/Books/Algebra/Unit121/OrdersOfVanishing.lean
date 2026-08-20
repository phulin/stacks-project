import Formalization.Books.Algebra.Unit03.BasicNotions
import Formalization.Books.Algebra.Unit52.Length
import Mathlib.Algebra.Algebra.RestrictScalars
import Mathlib.Algebra.Module.Lattice
import Mathlib.Algebra.Module.Equiv.Basic
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.LinearAlgebra.Transvection.Generation
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.RingTheory.Length
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Localization.AsSubring
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Mathlib.RingTheory.Norm.Basic
import Mathlib.RingTheory.OrderOfVanishing.Basic
import Mathlib.RingTheory.RingHom.Finite
import Mathlib.RingTheory.Spectrum.Maximal.Basic

/-!
# Commutative Algebra, Chapter 121: Orders of vanishing

The order of vanishing on a one-dimensional fraction field is the integer-valued
form of Mathlib's `Ring.ordFrac`.  Lattices are represented by finite submodules
whose `K`-span is the whole ambient vector space, and finite colengths use
canonical submodule quotients.
-/

namespace Formalization.Books.Algebra.Unit121

open Set
open scoped BigOperators Pointwise

universe u v

noncomputable section

/-! ## Orders of vanishing -/

/- Mathlib's `Ring.ord` is the canonical extended-natural length of a principal
   quotient.  This natural-valued wrapper is used for the finite lengths in the
   source. -/
def principalQuotientLength
    (R : Type u) [CommRing R] (a : R) : ℕ :=
  (Ring.ord R a).toNat

def principalQuotientHasFiniteLength
    (R : Type u) [CommRing R] (a : R) : Prop :=
  IsFiniteLength R (R ⧸ Ideal.span ({a} : Set R))

theorem principal_smul_span_eq
    {R : Type u} [CommRing R] (a b : R) :
    (({b} : Set R) • Ideal.span ({a} : Set R)) =
      Ideal.span ({a * b} : Set R) := by
  simp [← Ideal.submodule_span_eq, Submodule.set_smul_span, mul_comm]

/- The source's exact sequence is already the canonical Mathlib sequence.  Its
   middle term is written `R ⧸ (b • I)`, with `principal_smul_span_eq`
   providing the source's identification with `R/(ab)`. -/
theorem principal_quotient_short_exact
    {R : Type u} [CommRing R] {a b : R}
    (_ha : a ∈ nonZeroDivisors R) (hb : b ∈ nonZeroDivisors R) :
    Function.Injective (Ideal.mulQuot b (Ideal.span ({a} : Set R))) ∧
      Function.Surjective (Ideal.quotOfMul b (Ideal.span ({a} : Set R))) ∧
        Function.Exact (Ideal.mulQuot b (Ideal.span ({a} : Set R)))
          (Ideal.quotOfMul b (Ideal.span ({a} : Set R))) ∧
      (({b} : Set R) • Ideal.span ({a} : Set R)) =
        Ideal.span ({a * b} : Set R) := by
  exact ⟨Ideal.mulQuot_injective (Ideal.span ({a} : Set R)) hb,
    Ideal.quotOfMul_surjective (Ideal.span ({a} : Set R)),
    Ideal.exact_mulQuot_quotOfMul (Ideal.span ({a} : Set R)),
    principal_smul_span_eq a b⟩

theorem principal_quotient_length_additive
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    (_hsemilocal : Formalization.Books.Algebra.Unit03.IsSemilocalRing R)
    (hdim : ringKrullDim R = 1) (a b : R)
    (ha : a ∈ nonZeroDivisors R) (hb : b ∈ nonZeroDivisors R) :
    principalQuotientHasFiniteLength R a ∧
      principalQuotientHasFiniteLength R b ∧
        principalQuotientHasFiniteLength R (a * b) ∧
          Module.length R (R ⧸ Ideal.span ({a * b} : Set R)) =
            Module.length R (R ⧸ Ideal.span ({a} : Set R)) +
              Module.length R (R ⧸ Ideal.span ({b} : Set R)) := by
  let _ : Ring.KrullDimLE 1 R := Ring.krullDimLE_iff.mpr hdim.le
  have hfa : principalQuotientHasFiniteLength R a :=
    isFiniteLength_quotient_span_singleton R ha
  have hfb : principalQuotientHasFiniteLength R b :=
    isFiniteLength_quotient_span_singleton R hb
  have hab : principalQuotientHasFiniteLength R (a * b) :=
    isFiniteLength_quotient_span_singleton R ((mul_mem_nonZeroDivisors).2 ⟨ha, hb⟩)
  refine ⟨hfa, hfb, hab, ?_⟩
  have hlen := Module.length_eq_add_of_exact
    (Ideal.mulQuot b (Ideal.span ({a} : Set R)))
    (Ideal.quotOfMul b (Ideal.span ({a} : Set R)))
    (Ideal.mulQuot_injective (Ideal.span ({a} : Set R)) hb)
    (Ideal.quotOfMul_surjective (Ideal.span ({a} : Set R)))
    (Ideal.exact_mulQuot_quotOfMul (Ideal.span ({a} : Set R)))
  have hideal : (({b} : Set R) • Ideal.span ({a} : Set R)) =
      Ideal.span ({b * a} : Set R) := by
    simpa [mul_comm] using principal_smul_span_eq a b
  have hsmul : (({b} : Set R) • Ideal.span ({a} : Set R)) =
      b • Ideal.span ({a} : Set R) :=
    Submodule.singleton_set_smul (Ideal.span ({a} : Set R)) b
  rw [hsmul] at hideal
  rw [hideal, mul_comm] at hlen
  exact hlen

/- The dimension hypothesis is supplied as a source-facing equality.  The
   canonical fraction-field API needs the corresponding `KrullDimLE 1`
   instance, which is installed locally in this definition. -/
noncomputable def orderOfVanishing
    {R : Type u} {K : Type v} [CommRing R] [IsLocalRing R] [IsDomain R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (hnoetherian : IsNoetherianRing R)
    (hdim : ringKrullDim R = 1) : Kˣ → ℤ :=
  letI : IsNoetherianRing R := hnoetherian
  letI : Ring.KrullDimLE 1 R := Ring.krullDimLE_iff.mpr hdim.le
  fun x => WithZero.log (Ring.ordFrac R (x : K))

noncomputable def fractionUnit
    {R : Type u} {K : Type v} [CommRing R] [IsDomain R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (x y : R) (hx : x ∈ nonZeroDivisors R)
    (hy : y ∈ nonZeroDivisors R) : Kˣ :=
  Units.mk0 (algebraMap R K x / algebraMap R K y)
    (div_ne_zero
      (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hx)
      (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hy))

theorem orderOfVanishing_fractionUnit
    {R : Type u} {K : Type v} [CommRing R] [IsLocalRing R] [IsDomain R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (hnoetherian : IsNoetherianRing R) (hdim : ringKrullDim R = 1)
    (x y : R) (hx : x ∈ nonZeroDivisors R)
    (hy : y ∈ nonZeroDivisors R) :
    orderOfVanishing hnoetherian hdim
        (fractionUnit (R := R) (K := K) x y hx hy) =
      (principalQuotientLength R x : ℤ) - principalQuotientLength R y := by
  let _ : IsNoetherianRing R := hnoetherian
  let _ : Ring.KrullDimLE 1 R := Ring.krullDimLE_iff.mpr hdim.le
  change WithZero.log
      (Ring.ordFrac R (algebraMap R K x / algebraMap R K y)) =
    (principalQuotientLength R x : ℤ) - principalQuotientLength R y
  rw [← IsFractionRing.mk'_eq_div (A := R) ⟨y, hy⟩]
  rw [Ring.ordFrac_eq_div (R := R) ⟨x, hx⟩ ⟨y, hy⟩]
  have hox : Ring.ord R x = (Ring.ord R x).toNat :=
    (ENat.natCast_toNat (Ring.ord_ne_top hx)).symm
  have hoy : Ring.ord R y = (Ring.ord R y).toNat :=
    (ENat.natCast_toNat (Ring.ord_ne_top hy)).symm
  have hcx := Ring.ordMonoidWithZeroHom_eq_coe (R := R) hx hox
  have hcy := Ring.ordMonoidWithZeroHom_eq_coe (R := R) hy hoy
  have hnx : Ring.ordMonoidWithZeroHom R x ≠ 0 := by
    rw [hcx]
    exact WithZero.exp_ne_zero
  have hny : Ring.ordMonoidWithZeroHom R y ≠ 0 := by
    rw [hcy]
    exact WithZero.exp_ne_zero
  rw [WithZero.log_div hnx hny]
  rw [hcx, hcy]
  rfl

@[simp]
theorem orderOfVanishing_mul
    {R : Type u} {K : Type v} [CommRing R] [IsLocalRing R] [IsDomain R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (hnoetherian : IsNoetherianRing R) (hdim : ringKrullDim R = 1)
    (x y : Kˣ) :
    orderOfVanishing hnoetherian hdim (x * y) =
      orderOfVanishing hnoetherian hdim x +
        orderOfVanishing hnoetherian hdim y := by
  let _ : IsNoetherianRing R := hnoetherian
  let _ : Ring.KrullDimLE 1 R := Ring.krullDimLE_iff.mpr hdim.le
  change WithZero.log (Ring.ordFrac R ((x * y : Kˣ) : K)) =
    WithZero.log (Ring.ordFrac R (x : K)) +
      WithZero.log (Ring.ordFrac R (y : K))
  rw [Units.val_mul]
  rw [map_mul]
  have hnx : Ring.ordFrac R (x : K) ≠ 0 :=
    (IsUnit.map (Ring.ordFrac R) x.isUnit).ne_zero
  have hny : Ring.ordFrac R (y : K) ≠ 0 :=
    (IsUnit.map (Ring.ordFrac R) y.isUnit).ne_zero
  rw [WithZero.log_mul hnx hny]

/-! ## Lattices and their finite colengths -/

/- This records the source's warning about the DVR case as a usable theorem:
   the non-DVR freeness caution is deliberately not strengthened into a
   universal counterexample assertion. -/
theorem lattice_free_over_dvr
    {R : Type u} {K : Type v} {V : Type v}
    [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [AddCommGroup V] [Module K V] [Module R V]
    [IsScalarTower R K V] [Module.Finite K V] (M : Submodule R V)
    (hM : Submodule.IsLattice K M) : Module.Free R (M : Type v) := by
  exact @Submodule.IsLattice.free R _ K _ _ V _ _ _ _ _ _ _ M hM

abbrev latticeQuotient
    (R : Type u) {V : Type v} [CommRing R]
    [AddCommGroup V] [Module R V]
    (N M : Submodule R V) : Type v :=
  M ⧸ Submodule.comap M.subtype N

def latticeLengthNat
    (R : Type u) {V : Type v} [CommRing R]
    [AddCommGroup V] [Module R V]
    (N M : Submodule R V) : ℕ :=
  (Module.length R (latticeQuotient R N M)).toNat

def latticeQuotientHasFiniteLength
    (R : Type u) {V : Type v} [CommRing R]
    [AddCommGroup V] [Module R V]
    (N M : Submodule R V) : Prop :=
  IsFiniteLength R (latticeQuotient R N M)

def latticeLengthInt
    (R : Type u) {V : Type v} [CommRing R]
    [AddCommGroup V] [Module R V]
    (N M : Submodule R V) : ℤ :=
  latticeLengthNat R N M

private theorem exists_nonzero_smul_mem_of_isLattice
    {R : Type u} {K : Type v} {V : Type v}
    [CommRing R] [IsDomain R] [Field K] [Algebra R K]
    [AddCommGroup V] [Module K V] [Module R V]
    [IsScalarTower R K V] [IsFractionRing R K]
    (M : Submodule R V) (hM : Submodule.IsLattice K M) (x : V) :
    ∃ a : R, a ≠ 0 ∧ a • x ∈ M := by
  let P : Submodule K V := Submodule.span K (M : Set V)
  have hx : x ∈ P := by
    change x ∈ Submodule.span K (M : Set V)
    rw [hM.span_eq_top]
    exact Submodule.mem_top
  let Q : V → Prop := fun y => ∃ a : R, a ≠ 0 ∧ a • y ∈ M
  have hQ : ∀ y, y ∈ P → Q y := by
    intro y hy
    change y ∈ Submodule.span K (M : Set V) at hy
    refine Submodule.span_induction (fun z hz => ?_) ?_
      (fun z w _ _ hz hw => ?_) (fun a z _ hz => ?_) hy
    ·
      exact ⟨1, one_ne_zero, by simpa using hz⟩
    · exact ⟨1, one_ne_zero, by simp⟩
    · rcases hz with ⟨a, ha, hay⟩
      rcases hw with ⟨b, hb, hbz⟩
      refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
      rw [smul_add]
      apply M.add_mem
      · rw [mul_comm, mul_smul]
        exact M.smul_mem b hay
      · rw [mul_smul]
        exact M.smul_mem a hbz
    · rcases hz with ⟨b, hb, hby⟩
      obtain ⟨c, d, hcd⟩ := IsLocalization.exists_mk'_eq
        (S := K) (nonZeroDivisors R) a
      have had : algebraMap R K d * a = algebraMap R K c := by
        rw [← hcd]
        exact IsLocalization.mk'_spec' K c d
      refine ⟨d * b, mul_ne_zero (mem_nonZeroDivisors_iff_ne_zero.mp d.2) hb, ?_⟩
      have heq : (d * b) • (a • z) = c • (b • z) := by
        calc
          (d * b) • (a • z) =
              (algebraMap R K (d * b) * a) • z := by
                rw [← IsScalarTower.algebraMap_smul (R := R) K (M := V),
                  ← IsScalarTower.smul_assoc]
                simp [smul_eq_mul]
          _ = (algebraMap R K c * algebraMap R K b) • z := by
                congr 1
                rw [map_mul]
                calc
                  algebraMap R K (↑d) * algebraMap R K b * a =
                      (algebraMap R K (↑d) * a) * algebraMap R K b := by ring
                  _ = algebraMap R K c * algebraMap R K b := by rw [had]
          _ = c • (b • z) := by
                simp only [mul_smul,
                  IsScalarTower.algebraMap_smul (R := R) K (M := V)]
      rw [heq]
      exact M.smul_mem c hby
  exact hQ x hx

private theorem exists_nonzero_smul_mem_of_finset
    {R : Type u} {K : Type v} {V : Type v}
    [CommRing R] [IsDomain R] [Field K] [Algebra R K]
    [AddCommGroup V] [Module K V] [Module R V]
    [IsScalarTower R K V] [IsFractionRing R K]
    (M : Submodule R V) (hM : Submodule.IsLattice K M) (s : Finset V) :
    ∃ a : R, a ≠ 0 ∧ ∀ x ∈ s, a • x ∈ M := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, one_ne_zero, by simp⟩
  | @insert x s hxs ih =>
      rcases ih with ⟨a, ha, has⟩
      rcases exists_nonzero_smul_mem_of_isLattice M hM x with ⟨b, hb, hbx⟩
      refine ⟨b * a, mul_ne_zero hb ha, ?_⟩
      intro y hy
      simp only [Finset.mem_insert] at hy
      rcases hy with rfl | hy
      · rw [mul_comm, mul_smul]
        exact M.smul_mem a hbx
      · rw [mul_smul]
        exact M.smul_mem b (has y hy)

private theorem not_isFiniteLength_self
    {R : Type u} [CommRing R] [IsLocalRing R] [IsDomain R]
    [IsNoetherianRing R] (hdim : ringKrullDim R = 1) :
    ¬ IsFiniteLength R R := by
  intro h
  letI : IsArtinianRing R := (isFiniteLength_iff_isNoetherian_isArtinian.mp h).2
  have hfield : IsField R := IsArtinianRing.isField_of_isReduced_of_isLocalRing R
  have hz := ringKrullDim_eq_zero_of_isField (F := R) hfield
  rw [hdim] at hz
  exact one_ne_zero hz

private theorem finiteLength_isTorsion
    {R : Type u} {Q : Type v}
    [CommRing R] [IsLocalRing R] [IsDomain R] [IsNoetherianRing R]
    [AddCommGroup Q] [Module R Q] (hdim : ringKrullDim R = 1)
    (hQ : IsFiniteLength R Q) : Module.IsTorsion R Q := by
  have hQ' := isFiniteLength_iff_isNoetherian_isArtinian.mp hQ
  letI : IsNoetherian R Q := hQ'.1
  letI : IsArtinian R Q := hQ'.2
  intro q
  have hcyc : IsFiniteLength R (R ∙ q) := by
    rw [isFiniteLength_iff_isNoetherian_isArtinian]
    exact ⟨inferInstance, inferInstance⟩
  have hquot : IsFiniteLength R (R ⧸ Ideal.torsionOf R Q q) :=
    hcyc.of_injective (Ideal.quotTorsionOfEquivSpanSingleton R Q q).injective
  have hT : Ideal.torsionOf R Q q ≠ ⊥ := by
    intro hT
    have hR : IsFiniteLength R R := by
      apply hquot.of_injective (f := (Ideal.torsionOf R Q q).mkQ)
      apply LinearMap.ker_eq_bot.mp
      rw [Submodule.ker_mkQ, hT]
    exact not_isFiniteLength_self hdim hR
  obtain ⟨a, haT, ha⟩ : ∃ a : R, a ∈ Ideal.torsionOf R Q q ∧ a ≠ 0 := by
    by_contra h
    apply hT
    apply (Submodule.eq_bot_iff _).mpr
    intro a haT'
    by_contra ha'
    exact h ⟨a, haT', ha'⟩
  exact ⟨⟨a, mem_nonZeroDivisors_iff_ne_zero.mpr ha⟩,
    (Ideal.mem_torsionOf_iff q a).mp haT⟩

private theorem latticeQuotient_finiteLength_of_finite
    {R : Type u} {K : Type v} {V : Type v}
    [CommRing R] [IsLocalRing R] [IsDomain R] [IsNoetherianRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [AddCommGroup V] [Module K V] [Module R V]
    [IsScalarTower R K V] [Module.Finite K V] (hdim : ringKrullDim R = 1)
    (M M' : Submodule R V) (hM : Submodule.IsLattice K M) (hMM' : M ≤ M')
    [Module.Finite R (M' : Type v)] :
    IsFiniteLength R (latticeQuotient R M M') := by
  classical
  let _ : Ring.KrullDimLE 1 R := Ring.krullDimLE_iff.mpr hdim.le
  obtain ⟨n, s, hs⟩ := Module.Finite.exists_fin (R := R) (M := (M' : Type v))
  obtain ⟨a, ha, has⟩ := exists_nonzero_smul_mem_of_finset M hM
    (Finset.univ.image fun i : Fin n => (s i : V))
  have hgen : ∀ x : M', a • (x : V) ∈ M := by
    intro x
    let L : (M' : Type v) →ₗ[R] V := M'.subtype
    let P : Submodule R (M' : Type v) :=
      M.comap ((DistribSMul.toLinearMap R V a).comp L)
    have hP : Submodule.span R (Set.range s) ≤ P := by
      apply Submodule.span_le.2
      rintro _ ⟨i, rfl⟩
      change a • (s i : V) ∈ M
      exact has _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
    have hxP : x ∈ P := hP (by rw [hs]; exact Submodule.mem_top)
    exact hxP
  have hQ : Module.IsTorsionBy R (latticeQuotient R M M') a := by
    rw [Module.isTorsionBy_quotient_iff]
    intro x
    exact hgen x
  have hQset : Module.IsTorsionBySet R (latticeQuotient R M M')
      (Ideal.span ({a} : Set R)) := by
    rw [← Module.isTorsionBySet_iff_is_torsion_by_span,
      Module.isTorsionBySet_singleton_iff]
    exact hQ
  letI : Module.IsTorsionBySet R (latticeQuotient R M M')
      (Ideal.span ({a} : Set R)) := hQset
  letI : Module (R ⧸ Ideal.span ({a} : Set R))
      (latticeQuotient R M M') := hQset.module
  letI : Module.Finite (R ⧸ Ideal.span ({a} : Set R))
      (latticeQuotient R M M') :=
    Module.Finite.of_restrictScalars_finite R (R ⧸ Ideal.span ({a} : Set R)) _
  have hSart : IsArtinianRing (R ⧸ Ideal.span ({a} : Set R)) := by
    rw [isArtinianRing_iff_krullDimLE_zero, Ring.KrullDimLE, Order.krullDimLE_iff,
      ← ENat.WithBot.add_le_add_one_right_iff, Nat.cast_zero, zero_add]
    exact (ringKrullDim_quotient_succ_le_of_nonZeroDivisor
      (mem_nonZeroDivisors_iff_ne_zero.mpr ha)).trans
        (Order.KrullDimLE.krullDim_le)
  letI : IsArtinianRing (R ⧸ Ideal.span ({a} : Set R)) := hSart
  have hArtQ : IsArtinian R (latticeQuotient R M M') := by
    exact isArtinian_of_surjective_algebraMap
      (R := R ⧸ Ideal.span ({a} : Set R)) (S := R)
      (M := latticeQuotient R M M')
      (Ideal.Quotient.mk_surjective (I := Ideal.span ({a} : Set R)))
  exact isFiniteLength_iff_isNoetherian_isArtinian.mpr ⟨inferInstance, hArtQ⟩

theorem lattice_comparison_upper
    {R : Type u} {K : Type v} {V : Type v}
    [CommRing R] [IsLocalRing R] [IsDomain R] [IsNoetherianRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [AddCommGroup V] [Module K V] [Module R V]
    [IsScalarTower R K V] [Module.Finite K V] (hdim : ringKrullDim R = 1)
    (M M' : Submodule R V) (hM : Submodule.IsLattice K M) (hMM' : M ≤ M') :
    List.TFAE
      [ Submodule.IsLattice K M',
        latticeQuotientHasFiniteLength R M M',
        Module.Finite R (M' : Type v) ] := by
  tfae_have 1 → 2 := by
    intro hM'
    letI : Submodule.IsLattice K M' := hM'
    exact latticeQuotient_finiteLength_of_finite hdim M M' hM hMM'
  tfae_have 2 → 3 := by
    intro hQ
    letI : Submodule.IsLattice K M := hM
    letI : IsFiniteLength R (latticeQuotient R M M') := hQ
    let N : Submodule R (M' : Type v) := Submodule.comap M'.subtype M
    letI : IsNoetherian R (M' ⧸ N) := by
      change IsNoetherian R (latticeQuotient R M M')
      exact (isFiniteLength_iff_isNoetherian_isArtinian.mp hQ).1
    letI : Module.Finite R (M' ⧸ N) := by
      constructor
      exact (isNoetherian_submodule.mp inferInstance) ⊤ le_top
    have hexact : Function.Exact (M.inclusion hMM') N.mkQ := by
      rw [LinearMap.exact_iff]
      ext x
      constructor
      · intro hx
        change (Submodule.Quotient.mk x : (M' : Type v) ⧸ N) = 0 at hx
        rw [Submodule.Quotient.mk_eq_zero] at hx
        have hxM : (x : V) ∈ M := hx
        refine ⟨⟨(x : V), hxM⟩, ?_⟩
        apply Subtype.ext
        rfl
      · rintro ⟨y, hy⟩
        change N.mkQ x = 0
        calc
          N.mkQ x = N.mkQ ((M.inclusion hMM') y) := congrArg N.mkQ hy.symm
          _ = 0 := by
            change (Submodule.Quotient.mk ((M.inclusion hMM') y) :
              (M' : Type v) ⧸ N) = 0
            rw [Submodule.Quotient.mk_eq_zero]
            exact y.property
    exact Module.Finite.of_exact hexact N.mkQ_surjective
  tfae_have 3 → 1 := by
    intro hM'
    letI : Submodule.IsLattice K M := hM
    exact Submodule.IsLattice.of_le_of_isLattice_of_fg K hMM'
      ((Module.Finite.iff_fg).mp hM')
  tfae_finish

theorem lattice_comparison_lower
    {R : Type u} {K : Type v} {V : Type v}
    [CommRing R] [IsLocalRing R] [IsDomain R] [IsNoetherianRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [AddCommGroup V] [Module K V] [Module R V]
    [IsScalarTower R K V] [Module.Finite K V] (hdim : ringKrullDim R = 1)
    (M M' : Submodule R V) (hM : Submodule.IsLattice K M) (hM'M : M' ≤ M) :
    Submodule.IsLattice K M' ↔ latticeQuotientHasFiniteLength R M' M := by
  constructor
  · intro hM'
    letI : Submodule.IsLattice K M' := hM'
    letI : Submodule.IsLattice K M := hM
    exact latticeQuotient_finiteLength_of_finite hdim M' M hM' hM'M
  · intro hQ
    letI : Submodule.IsLattice K M := hM
    letI : IsFiniteLength R (latticeQuotient R M' M) := hQ
    have hfg : M'.FG := by
      exact (isNoetherian_submodule.mp inferInstance) M' hM'M
    have hspan : Submodule.span K (M' : Set V) = ⊤ := by
      apply le_antisymm le_top
      rw [← hM.span_eq_top]
      apply Submodule.span_le.2
      intro x hx
      let q : latticeQuotient R M' M := Submodule.Quotient.mk ⟨x, hx⟩
      have htors : Module.IsTorsion R (latticeQuotient R M' M) :=
        finiteLength_isTorsion hdim hQ
      have htq := htors (x := q)
      rcases htq with ⟨a, hak⟩
      have hax : a • x ∈ M' := by
        have hak' : (Submodule.Quotient.mk ((a : R) • (⟨x, hx⟩ : M)) :
            latticeQuotient R M' M) = 0 := by
          rw [Submodule.Quotient.mk_smul]
          exact hak
        rw [Submodule.Quotient.mk_eq_zero] at hak'
        exact hak'
      have hamap : algebraMap R K (a : R) ≠ 0 :=
        IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors a.2
      have hxeq : x = (algebraMap R K (a : R))⁻¹ • ((a : R) • x) := by
        calc
          x = 1 • x := by simp
          _ = ((algebraMap R K (a : R))⁻¹ * algebraMap R K (a : R)) • x := by
            simp [inv_mul_cancel₀ hamap]
          _ = (algebraMap R K (a : R))⁻¹ • (algebraMap R K (a : R) • x) := by
            rw [mul_smul]
          _ = (algebraMap R K (a : R))⁻¹ • ((a : R) • x) := by
            rw [IsScalarTower.algebraMap_smul]
      rw [hxeq]
      exact Submodule.smul_mem _ _ (Submodule.subset_span hax)
    exact ⟨hfg, hspan⟩

theorem lattice_intersection_and_sum
    {R : Type u} {K : Type v} {V : Type v}
    [CommRing R] [IsLocalRing R] [IsDomain R] [IsNoetherianRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [AddCommGroup V] [Module K V] [Module R V]
    [IsScalarTower R K V] [Module.Finite K V] (hdim : ringKrullDim R = 1)
    (M M' : Submodule R V) (hM : Submodule.IsLattice K M)
    (hM' : Submodule.IsLattice K M') :
    Submodule.IsLattice K (M ⊓ M') ∧ Submodule.IsLattice K (M ⊔ M') := by
  letI : Submodule.IsLattice K M := hM
  letI : Submodule.IsLattice K M' := hM'
  have hfg : (M ⊓ M').FG := by
    have hnoethI : IsNoetherian R ↥(M ⊓ M') := isNoetherian_of_le inf_le_left
    exact (isNoetherian_submodule.mp hnoethI) (M ⊓ M') le_rfl
  have hspan : Submodule.span K ((M ⊓ M' : Submodule R V) : Set V) = ⊤ := by
    apply le_antisymm le_top
    rw [← hM.span_eq_top]
    apply Submodule.span_le.2
    intro x hx
    obtain ⟨a, ha, hax⟩ := exists_nonzero_smul_mem_of_isLattice M' hM' x
    have hax' : a • x ∈ M ⊓ M' := ⟨M.smul_mem a hx, hax⟩
    have hmem : a • x ∈ Submodule.span K ((M ⊓ M' : Submodule R V) : Set V) :=
      Submodule.subset_span hax'
    have hamap : algebraMap R K a ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors
        (mem_nonZeroDivisors_iff_ne_zero.mpr ha)
    have hxeq : x = (algebraMap R K a)⁻¹ • (a • x) := by
      calc
        x = 1 • x := by simp
        _ = ((algebraMap R K a)⁻¹ * algebraMap R K a) • x := by
          simp [inv_mul_cancel₀ hamap]
        _ = (algebraMap R K a)⁻¹ • (algebraMap R K a • x) := by
          rw [mul_smul]
        _ = (algebraMap R K a)⁻¹ • (a • x) := by
          rw [IsScalarTower.algebraMap_smul]
    rw [hxeq]
    exact Submodule.smul_mem _ _ hmem
  refine ⟨⟨hfg, hspan⟩, ?_⟩
  infer_instance

theorem lattice_length_additive
    {R : Type u} {K : Type v} {V : Type v}
    [CommRing R] [IsLocalRing R] [IsDomain R] [IsNoetherianRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [AddCommGroup V] [Module K V] [Module R V]
    [IsScalarTower R K V] [Module.Finite K V] (hdim : ringKrullDim R = 1)
    (M M' M'' : Submodule R V) (hM : Submodule.IsLattice K M)
    (hM' : Submodule.IsLattice K M') (hM'' : Submodule.IsLattice K M'')
    (hMM' : M ≤ M') (hM'M'' : M' ≤ M'') :
    latticeLengthNat R M M'' =
      latticeLengthNat R M M' + latticeLengthNat R M' M'' := by
  letI : Submodule.IsLattice K M := hM
  letI : Submodule.IsLattice K M' := hM'
  letI : Submodule.IsLattice K M'' := hM''
  let N : Submodule R (M' : Type v) := Submodule.comap M'.subtype M
  let N' : Submodule R (M'' : Type v) := Submodule.comap M''.subtype M
  let P : Submodule R (M'' : Type v) := Submodule.comap M''.subtype M'
  have hNN' : N ≤ (N'.comap (M'.inclusion hM'M'')) := by
    intro x hx
    exact hx
  have hN'P : N' ≤ P := by
    intro x hx
    exact hMM' hx
  let f : (M' ⧸ N) →ₗ[R] (M'' ⧸ N') :=
    N.mapQ N' (M'.inclusion hM'M'') hNN'
  let g : (M'' ⧸ N') →ₗ[R] (M'' ⧸ P) := Submodule.factor hN'P
  have hf : Function.Injective f := by
    apply LinearMap.ker_eq_bot.mp
    apply (Submodule.eq_bot_iff _).mpr
    intro z hz
    obtain ⟨x, rfl⟩ := N.mkQ_surjective z
    change f (N.mkQ x) = 0 at hz
    have hxN' : (M'.inclusion hM'M'') x ∈ N' := by
      have hx : (Submodule.Quotient.mk ((M'.inclusion hM'M'') x) :
          (M'' : Type v) ⧸ N') = 0 := by
        simpa [f] using hz
      rw [Submodule.Quotient.mk_eq_zero] at hx
      exact hx
    change (Submodule.Quotient.mk x : (M' : Type v) ⧸ N) = 0
    rw [Submodule.Quotient.mk_eq_zero]
    exact hxN'
  have hg : Function.Surjective g := Submodule.factor_surjective hN'P
  have hex : Function.Exact f g := by
    rw [LinearMap.exact_iff]
    ext z
    constructor
    · intro hz
      change g z = 0 at hz
      obtain ⟨x, rfl⟩ := N'.mkQ_surjective z
      have hxP : x ∈ P := by
        have hx : (Submodule.Quotient.mk x : (M'' : Type v) ⧸ P) = 0 := by
          simpa [g] using hz
        rw [Submodule.Quotient.mk_eq_zero] at hx
        exact hx
      refine ⟨N.mkQ ⟨(x : V), hxP⟩, ?_⟩
      rfl
    · rintro ⟨y, hy⟩
      change g z = 0
      rw [← hy]
      obtain ⟨w, rfl⟩ := N.mkQ_surjective y
      have hwP : (M'.inclusion hM'M'') w ∈ P := by
        exact w.property
      have hw : (Submodule.Quotient.mk ((M'.inclusion hM'M'') w) :
          (M'' : Type v) ⧸ P) = 0 := by
        rw [Submodule.Quotient.mk_eq_zero]
        exact hwP
      simpa [f, g] using hw
  have hQ : IsFiniteLength R (latticeQuotient R M M'') := by
    exact latticeQuotient_finiteLength_of_finite hdim M M'' hM
      (hMM'.trans hM'M'')
  have hQ' : IsFiniteLength R (latticeQuotient R M M') :=
    latticeQuotient_finiteLength_of_finite hdim M M' hM hMM'
  have hQ'' : IsFiniteLength R (latticeQuotient R M' M'') :=
    latticeQuotient_finiteLength_of_finite hdim M' M'' hM' hM'M''
  have hlen := Module.length_eq_add_of_exact f g hf hg hex
  have hlen' := congrArg ENat.toNat hlen
  rw [ENat.toNat_add
    (Module.length_ne_top_iff.mpr hQ') (Module.length_ne_top_iff.mpr hQ'')] at hlen'
  simpa [latticeLengthNat, latticeQuotient, N, N', P] using hlen'

private theorem lattice_length_additive_int
    {R : Type u} {K : Type v} {V : Type v}
    [CommRing R] [IsLocalRing R] [IsDomain R] [IsNoetherianRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [AddCommGroup V] [Module K V] [Module R V]
    [IsScalarTower R K V] [Module.Finite K V] (hdim : ringKrullDim R = 1)
    (M M' M'' : Submodule R V) (hM : Submodule.IsLattice K M)
    (hM' : Submodule.IsLattice K M') (hM'' : Submodule.IsLattice K M'')
    (hMM' : M ≤ M') (hM'M'' : M' ≤ M'') :
    latticeLengthInt R M M'' =
      latticeLengthInt R M M' + latticeLengthInt R M' M'' := by
  have h := lattice_length_additive hdim M M' M'' hM hM' hM'' hMM' hM'M''
  change (latticeLengthNat R M M'' : ℤ) =
    (latticeLengthNat R M M' : ℤ) + (latticeLengthNat R M' M'' : ℤ)
  exact_mod_cast h

theorem lattice_length_comparison
    {R : Type u} {K : Type v} {V : Type v}
    [CommRing R] [IsLocalRing R] [IsDomain R] [IsNoetherianRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [AddCommGroup V] [Module K V] [Module R V]
    [IsScalarTower R K V] [Module.Finite K V] (hdim : ringKrullDim R = 1)
    (M M' N N' : Submodule R V)
    (hM : Submodule.IsLattice K M) (hM' : Submodule.IsLattice K M')
    (hN : Submodule.IsLattice K N) (hN' : Submodule.IsLattice K N')
    (hNM : N ≤ M ⊓ M') (hMM'N' : M ⊔ M' ≤ N') :
    latticeLengthInt R (M ⊓ M') M - latticeLengthInt R (M ⊓ M') M' =
        latticeLengthInt R N M - latticeLengthInt R N M' ∧
      latticeLengthInt R N M - latticeLengthInt R N M' =
        latticeLengthInt R M' (M ⊔ M') - latticeLengthInt R M (M ⊔ M') ∧
      latticeLengthInt R M' (M ⊔ M') - latticeLengthInt R M (M ⊔ M') =
        latticeLengthInt R M' N' - latticeLengthInt R M N' := by
  have hAS := lattice_intersection_and_sum hdim M M' hM hM'
  have hA : Submodule.IsLattice K (M ⊓ M') := hAS.1
  have hS : Submodule.IsLattice K (M ⊔ M') := hAS.2
  have h1 := lattice_length_additive_int hdim N (M ⊓ M') M
    hN hA hM hNM inf_le_left
  have h2 := lattice_length_additive_int hdim N (M ⊓ M') M'
    hN hA hM' hNM inf_le_right
  have h3 := lattice_length_additive_int hdim N M (M ⊔ M')
    hN hM hS (hNM.trans inf_le_left) le_sup_left
  have h4 := lattice_length_additive_int hdim N M' (M ⊔ M')
    hN hM' hS (hNM.trans inf_le_right) le_sup_right
  have h5 := lattice_length_additive_int hdim M' (M ⊔ M') N'
    hM' hS hN' le_sup_right hMM'N'
  have h6 := lattice_length_additive_int hdim M (M ⊔ M') N'
    hM hS hN' le_sup_left hMM'N'
  constructor
  · omega
  constructor
  · omega
  · omega

def latticeDistance
    (R : Type u) {V : Type v} [CommRing R]
    [AddCommGroup V] [Module R V]
    (M M' : Submodule R V) : ℤ :=
  latticeLengthInt R (M ⊓ M') M - latticeLengthInt R (M ⊓ M') M'

theorem latticeDistance_of_le
    {R : Type u} {K : Type v} {V : Type v}
    [CommRing R] [IsLocalRing R] [IsDomain R] [IsNoetherianRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [AddCommGroup V] [Module K V] [Module R V]
    [IsScalarTower R K V] [Module.Finite K V] (hdim : ringKrullDim R = 1)
    (M M' : Submodule R V) (hM : Submodule.IsLattice K M)
    (hM' : Submodule.IsLattice K M') (hM'M : M' ≤ M) :
    latticeDistance R M M' = latticeLengthInt R M' M := by
  have hinf : M ⊓ M' = M' := inf_eq_right.mpr hM'M
  rw [latticeDistance, hinf]
  simp [latticeLengthInt, latticeLengthNat, latticeQuotient]

theorem latticeDistance_additive
    {R : Type u} {K : Type v} {V : Type v}
    [CommRing R] [IsLocalRing R] [IsDomain R] [IsNoetherianRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [AddCommGroup V] [Module K V] [Module R V]
    [IsScalarTower R K V] [Module.Finite K V] (hdim : ringKrullDim R = 1)
    (M M' M'' : Submodule R V)
    (hM : Submodule.IsLattice K M) (hM' : Submodule.IsLattice K M')
    (hM'' : Submodule.IsLattice K M'') :
    latticeDistance R M M'' =
      latticeDistance R M M' + latticeDistance R M' M'' := by
  sorry

theorem latticeDistance_antisymm
    {R : Type u} {K : Type v} {V : Type v}
    [CommRing R] [IsLocalRing R] [IsDomain R] [IsNoetherianRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [AddCommGroup V] [Module K V] [Module R V]
    [IsScalarTower R K V] [Module.Finite K V] (hdim : ringKrullDim R = 1)
    (M M' : Submodule R V) (hM : Submodule.IsLattice K M)
    (hM' : Submodule.IsLattice K M') :
    latticeDistance R M M' = -latticeDistance R M' M := by
  sorry

/-! ## Transport by linear isomorphisms and determinants -/

def latticeMap
    {R : Type u} {K : Type v} {V : Type v}
    [CommRing R] [Field K] [Algebra R K]
    [AddCommGroup V] [Module K V] [Module R V]
    [IsScalarTower R K V] (φ : V ≃ₗ[K] V) (M : Submodule R V) :
    Submodule R V :=
  M.map (φ.restrictScalars R).toLinearMap

theorem isLattice_latticeMap
    {R : Type u} {K : Type v} {V : Type v}
    [CommRing R] [IsLocalRing R] [IsDomain R] [IsNoetherianRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [AddCommGroup V] [Module K V] [Module R V]
    [IsScalarTower R K V] [Module.Finite K V] (hdim : ringKrullDim R = 1)
    (φ : V ≃ₗ[K] V) (M : Submodule R V) (hM : Submodule.IsLattice K M) :
    Submodule.IsLattice K (latticeMap φ M) := by
  sorry

theorem latticeDistance_latticeMap_pair
    {R : Type u} {K : Type v} {V : Type v}
    [CommRing R] [IsLocalRing R] [IsDomain R] [IsNoetherianRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [AddCommGroup V] [Module K V] [Module R V]
    [IsScalarTower R K V] [Module.Finite K V] (hdim : ringKrullDim R = 1)
    (φ : V ≃ₗ[K] V) (M M' : Submodule R V)
    (hM : Submodule.IsLattice K M) (hM' : Submodule.IsLattice K M') :
    latticeDistance R (latticeMap φ M) (latticeMap φ M') =
      latticeDistance R M M' := by
  sorry

theorem latticeDistance_map_independent
    {R : Type u} {K : Type v} {V : Type v}
    [CommRing R] [IsLocalRing R] [IsDomain R] [IsNoetherianRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [AddCommGroup V] [Module K V] [Module R V]
    [IsScalarTower R K V] [Module.Finite K V] (hdim : ringKrullDim R = 1)
    (φ : V ≃ₗ[K] V) (M M' : Submodule R V)
    (hM : Submodule.IsLattice K M) (hM' : Submodule.IsLattice K M') :
    latticeDistance R M (latticeMap φ M) =
      latticeDistance R M' (latticeMap φ M') := by
  sorry

theorem latticeDistance_comp_decomposition
    {R : Type u} {K : Type v} {V : Type v}
    [CommRing R] [IsLocalRing R] [IsDomain R] [IsNoetherianRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [AddCommGroup V] [Module K V] [Module R V]
    [IsScalarTower R K V] [Module.Finite K V] (hdim : ringKrullDim R = 1)
    (φ ψ : V ≃ₗ[K] V) (M : Submodule R V) (hM : Submodule.IsLattice K M) :
    latticeDistance R M (latticeMap (ψ.trans φ) M) =
        latticeDistance R M (latticeMap ψ M) +
          latticeDistance R (latticeMap ψ M) (latticeMap (ψ.trans φ) M) ∧
      latticeDistance R (latticeMap ψ M) (latticeMap (ψ.trans φ) M) =
        latticeDistance R M (latticeMap φ M) := by
  sorry

theorem orderOfVanishing_det_comp
    {R : Type u} {K : Type v} {V : Type v}
    [CommRing R] [IsLocalRing R] [IsDomain R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [AddCommGroup V] [Module K V] [Module.Finite K V]
    (hnoetherian : IsNoetherianRing R) (hdim : ringKrullDim R = 1)
    (φ ψ : V ≃ₗ[K] V) :
    orderOfVanishing hnoetherian hdim (LinearEquiv.det (ψ.trans φ)) =
      orderOfVanishing hnoetherian hdim (LinearEquiv.det φ) +
        orderOfVanishing hnoetherian hdim (LinearEquiv.det ψ) := by
  sorry

theorem latticeDistance_map_eq_orderOfVanishing
    {R : Type u} {K : Type v} {V : Type v}
    [CommRing R] [IsLocalRing R] [IsDomain R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [AddCommGroup V] [Module K V] [Module R V]
    [IsScalarTower R K V] [Module.Finite K V]
    (hnoetherian : IsNoetherianRing R) (hdim : ringKrullDim R = 1)
    (M : Submodule R V) (hM : Submodule.IsLattice K M) (φ : V ≃ₗ[K] V) :
    latticeDistance R M (latticeMap φ M) =
      orderOfVanishing hnoetherian hdim (LinearEquiv.det φ) := by
  sorry

/- The source's elementary matrices are represented by Mathlib's canonical
   rank-one transvections and dilatransvections. -/
theorem generalLinearEquiv_mem_generated_dilatransvections
    {K : Type v} {V : Type v} [Field K] [AddCommGroup V] [Module K V]
    [Module.Finite K V] (φ : V ≃ₗ[K] V) :
    ∃ n : ℕ, φ ∈ (LinearEquiv.dilatransvections K V) ^ n := by
  sorry

theorem exists_fin_basis_equiv
    {K : Type v} {V : Type v} [Field K] [AddCommGroup V]
    [Module K V] [Module.Finite K V] :
    ∃ n : ℕ, Nonempty ((Fin n → K) ≃ₗ[K] V) := by
  sorry

theorem latticeDistance_transvection
    {R : Type u} {K : Type v} {V : Type v}
    [CommRing R] [IsLocalRing R] [IsDomain R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [AddCommGroup V] [Module K V] [Module R V]
    [IsScalarTower R K V] [Module.Finite K V]
    (hnoetherian : IsNoetherianRing R) (hdim : ringKrullDim R = 1)
    (M : Submodule R V) (hM : Submodule.IsLattice K M)
    {f : Module.Dual K V} {v : V} (hfv : f v = 0) :
    latticeDistance R M
        (latticeMap (LinearEquiv.transvection hfv) M) = 0 := by
  sorry

noncomputable def elementaryDiagonal
    {K : Type v} [Field K] (n : ℕ) (i : Fin n) (a : Kˣ) :
    (Fin n → K) ≃ₗ[K] (Fin n → K) :=
  LinearEquiv.piCongrRight (fun j =>
    if _h : j = i then a.mulLeftLinearEquiv K K else LinearEquiv.refl K K)

theorem latticeDistance_elementaryDiagonal
    {R : Type u} {K : Type v} [CommRing R] [IsLocalRing R]
    [IsDomain R] [IsNoetherianRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] (hnoetherian : IsNoetherianRing R)
    (hdim : ringKrullDim R = 1) (n : ℕ) (i : Fin n) (a : Kˣ)
    (M : Submodule R (Fin n → K))
    (hM : Submodule.IsLattice K M) :
    latticeDistance R M (latticeMap (elementaryDiagonal n i a) M) =
      orderOfVanishing hnoetherian hdim a := by
  sorry

/-! ## Finite extensions and norm formulas -/

noncomputable def localizedFractionRingAt
    {B : Type u} {L : Type v} [CommRing B] [IsDomain B]
    [Field L] [Algebra B L] [IsFractionRing B L]
    (q : MaximalSpectrum B) : Subalgebra B L :=
  Localization.subalgebra.ofField L q.asIdeal.primeCompl
    q.asIdeal.primeCompl_le_nonZeroDivisors

noncomputable def residueFieldDegreeAt
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [IsLocalRing A]
    (f : A →+* B) (q : MaximalSpectrum B)
    (hq : IsLocalRing.maximalIdeal A = q.asIdeal.comap f) : ℕ :=
  letI : Algebra (IsLocalRing.maximalIdeal A).ResidueField
      q.asIdeal.ResidueField :=
    (Ideal.ResidueField.map (IsLocalRing.maximalIdeal A) q.asIdeal f hq).toAlgebra
  Module.finrank (IsLocalRing.maximalIdeal A).ResidueField
    q.asIdeal.ResidueField

noncomputable def localizedOrderOfVanishing
    {B : Type u} {L : Type v} [CommRing B] [IsDomain B]
    [Field L] [Algebra B L] [IsFractionRing B L]
    (q : MaximalSpectrum B)
    (hnoetherian : IsNoetherianRing
      (localizedFractionRingAt (B := B) (L := L) q))
    (hdim : ringKrullDim (localizedFractionRingAt (B := B) (L := L) q) = 1)
    (y : Lˣ) : ℤ :=
  letI : IsLocalization q.asIdeal.primeCompl
      (localizedFractionRingAt (B := B) (L := L) q) := by
    unfold localizedFractionRingAt
    infer_instance
  letI : IsLocalRing (localizedFractionRingAt (B := B) (L := L) q) :=
    IsLocalization.AtPrime.isLocalRing
      (localizedFractionRingAt (B := B) (L := L) q) q.asIdeal
  orderOfVanishing hnoetherian hdim y

theorem norm_eq_det_multiplication
    {K : Type u} {L : Type v} [Field K] [Field L]
    [Algebra K L] [Module.Finite K L] (y : L) :
    Algebra.norm K y = LinearMap.det (Algebra.lmul K L y) := by
  rfl

/- The local quotient-length identity used in the finite-extension proof is
   exactly the earlier Chapter 52 pushdown theorem, with the canonical
   `MaximalSpectrum` indexing and `Fintype.ofFinite` enumeration. -/
theorem finite_extension_local_length_sum
    {A B M : Type u} [CommRing A] [CommRing B] [IsLocalRing A]
    [Algebra A B] [AddCommGroup M] [Module B M] [Module A M]
    [IsScalarTower A B M] [Finite (MaximalSpectrum B)]
    (h_over : ∀ q : MaximalSpectrum B,
      q.asIdeal.comap (algebraMap A B) = IsLocalRing.maximalIdeal A)
    (hfinite : ∀ q : MaximalSpectrum B,
      Module.Finite A q.asIdeal.ResidueField)
    (hM : IsFiniteLength B M) :
    letI := Fintype.ofFinite (MaximalSpectrum B)
    Module.length A M =
        ∑ q : MaximalSpectrum B,
          Module.length A q.asIdeal.ResidueField *
            Module.length (Localization.AtPrime q.asIdeal)
              (LocalizedModule.AtPrime q.asIdeal M) ∧
      Module.length A M < ⊤ := by
  exact Formalization.Books.Algebra.Unit52.length_pushdown h_over hfinite hM

theorem finite_extension_order_formula
    {A B K L : Type u} [CommRing A] [CommRing B]
    [IsDomain A] [IsDomain B] [IsLocalRing A] [IsNoetherianRing A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    [Field L] [Algebra B L] [IsFractionRing B L]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    [Module.Finite K L] (f : A →+* B)
    (hinjective : Function.Injective f) (hfinite : RingHom.Finite f)
    (hcompat : (algebraMap K L).comp (algebraMap A K) =
      (algebraMap B L).comp f)
    (hdim : ringKrullDim A = 1) :
    ∃ hsemilocal : Finite (MaximalSpectrum B),
      letI := hsemilocal
      ∃ hmax : ∀ q : MaximalSpectrum B,
          IsLocalRing.maximalIdeal A = q.asIdeal.comap f,
        ∃ hlocal : ∀ q : MaximalSpectrum B,
            IsNoetherianRing (localizedFractionRingAt (B := B) (L := L) q) ∧
              ringKrullDim (localizedFractionRingAt (B := B) (L := L) q) = 1,
          letI := Fintype.ofFinite (MaximalSpectrum B)
          ∀ y : Lˣ,
            orderOfVanishing (inferInstance : IsNoetherianRing A) hdim
                (Units.map (Algebra.norm K) y) =
              ∑ q : MaximalSpectrum B,
                residueFieldDegreeAt f q (hmax q) *
                  localizedOrderOfVanishing (B := B) (L := L) q
                    (hlocal q).1 (hlocal q).2 y := by
  sorry

end

end Formalization.Books.Algebra.Unit121
