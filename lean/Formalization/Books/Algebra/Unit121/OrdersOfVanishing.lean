import Formalization.Books.Algebra.Unit03.BasicNotions
import Formalization.Books.Algebra.Unit52.Length
import Mathlib.Algebra.Algebra.RestrictScalars
import Mathlib.Algebra.Module.Lattice
import Mathlib.Algebra.Module.Equiv.Basic
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.Quotient.Pi
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
    (hb : b ∈ nonZeroDivisors R) :
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
    IsFiniteLength R (R ⧸ Ideal.span ({a} : Set R)) ∧
      IsFiniteLength R (R ⧸ Ideal.span ({b} : Set R)) ∧
        IsFiniteLength R (R ⧸ Ideal.span ({a * b} : Set R)) ∧
          Module.length R (R ⧸ Ideal.span ({a * b} : Set R)) =
            Module.length R (R ⧸ Ideal.span ({a} : Set R)) +
              Module.length R (R ⧸ Ideal.span ({b} : Set R)) := by
  let _ : Ring.KrullDimLE 1 R := Ring.krullDimLE_iff.mpr hdim.le
  have hfa : IsFiniteLength R (R ⧸ Ideal.span ({a} : Set R)) :=
    isFiniteLength_quotient_span_singleton R ha
  have hfb : IsFiniteLength R (R ⧸ Ideal.span ({b} : Set R)) :=
    isFiniteLength_quotient_span_singleton R hb
  have hab : IsFiniteLength R (R ⧸ Ideal.span ({a * b} : Set R)) :=
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
  let : IsArtinianRing R := (isFiniteLength_iff_isNoetherian_isArtinian.mp h).2
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
  let : IsNoetherian R Q := hQ'.1
  let : IsArtinian R Q := hQ'.2
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
    (M M' : Submodule R V) (hM : Submodule.IsLattice K M) (_hMM' : M ≤ M')
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
  let : Module.IsTorsionBySet R (latticeQuotient R M M')
      (Ideal.span ({a} : Set R)) := hQset
  let : Module (R ⧸ Ideal.span ({a} : Set R))
      (latticeQuotient R M M') := hQset.module
  let : Module.Finite (R ⧸ Ideal.span ({a} : Set R))
      (latticeQuotient R M M') :=
    Module.Finite.of_restrictScalars_finite R (R ⧸ Ideal.span ({a} : Set R)) _
  have hSart : IsArtinianRing (R ⧸ Ideal.span ({a} : Set R)) := by
    rw [isArtinianRing_iff_krullDimLE_zero, Ring.KrullDimLE, Order.krullDimLE_iff,
      ← ENat.WithBot.add_le_add_one_right_iff, Nat.cast_zero, zero_add]
    exact (ringKrullDim_quotient_succ_le_of_nonZeroDivisor
      (mem_nonZeroDivisors_iff_ne_zero.mpr ha)).trans
        (Order.KrullDimLE.krullDim_le)
  let : IsArtinianRing (R ⧸ Ideal.span ({a} : Set R)) := hSart
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
        IsFiniteLength R (latticeQuotient R M M'),
        Module.Finite R (M' : Type v) ] := by
  tfae_have 1 → 2 := by
    intro hM'
    let : Submodule.IsLattice K M' := hM'
    exact latticeQuotient_finiteLength_of_finite hdim M M' hM hMM'
  tfae_have 2 → 3 := by
    intro hQ
    let : Submodule.IsLattice K M := hM
    let : IsFiniteLength R (latticeQuotient R M M') := hQ
    let N : Submodule R (M' : Type v) := Submodule.comap M'.subtype M
    let : IsNoetherian R (M' ⧸ N) := by
      change IsNoetherian R (latticeQuotient R M M')
      exact (isFiniteLength_iff_isNoetherian_isArtinian.mp hQ).1
    let : Module.Finite R (M' ⧸ N) := by
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
    let : Submodule.IsLattice K M := hM
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
    Submodule.IsLattice K M' ↔
      IsFiniteLength R (latticeQuotient R M' M) := by
  constructor
  · intro hM'
    let : Submodule.IsLattice K M' := hM'
    let : Submodule.IsLattice K M := hM
    exact latticeQuotient_finiteLength_of_finite hdim M' M hM' hM'M
  · intro hQ
    let : Submodule.IsLattice K M := hM
    let : IsFiniteLength R (latticeQuotient R M' M) := hQ
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
            simp
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
  have _ := hdim
  let : Submodule.IsLattice K M := hM
  let : Submodule.IsLattice K M' := hM'
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
  let : Submodule.IsLattice K M := hM
  let : Submodule.IsLattice K M' := hM'
  let : Submodule.IsLattice K M'' := hM''
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
  have _ := hdim
  have _ := hM
  have _ := hM'
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
  have h12 := lattice_intersection_and_sum hdim M M' hM hM'
  have h23 := lattice_intersection_and_sum hdim M' M'' hM' hM''
  have h13 := lattice_intersection_and_sum hdim M M'' hM hM''
  let N := (M ⊓ M') ⊓ M''
  have hN : Submodule.IsLattice K N :=
    (lattice_intersection_and_sum hdim (M ⊓ M') M'' h12.1 hM'').1
  have hN12 : N ≤ M ⊓ M' := inf_le_left
  have hN23 : N ≤ M' ⊓ M'' := by
    exact le_inf (inf_le_left.trans inf_le_right) inf_le_right
  have hN13 : N ≤ M ⊓ M'' := by
    exact le_inf (inf_le_left.trans inf_le_left) inf_le_right
  have ha := lattice_length_additive_int hdim N (M ⊓ M') M
    hN h12.1 hM hN12 inf_le_left
  have hb := lattice_length_additive_int hdim N (M ⊓ M') M'
    hN h12.1 hM' hN12 inf_le_right
  have hc := lattice_length_additive_int hdim N (M' ⊓ M'') M'
    hN h23.1 hM' hN23 inf_le_left
  have hd := lattice_length_additive_int hdim N (M' ⊓ M'') M''
    hN h23.1 hM'' hN23 inf_le_right
  have he := lattice_length_additive_int hdim N (M ⊓ M'') M
    hN h13.1 hM hN13 inf_le_left
  have hf := lattice_length_additive_int hdim N (M ⊓ M'') M''
    hN h13.1 hM'' hN13 inf_le_right
  change latticeLengthInt R (M ⊓ M'') M - latticeLengthInt R (M ⊓ M'') M'' =
    (latticeLengthInt R (M ⊓ M') M - latticeLengthInt R (M ⊓ M') M') +
      (latticeLengthInt R (M' ⊓ M'') M' - latticeLengthInt R (M' ⊓ M'') M'')
  omega

theorem latticeDistance_antisymm
    {R : Type u} {K : Type v} {V : Type v}
    [CommRing R] [IsLocalRing R] [IsDomain R] [IsNoetherianRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [AddCommGroup V] [Module K V] [Module R V]
    [IsScalarTower R K V] [Module.Finite K V] (hdim : ringKrullDim R = 1)
    (M M' : Submodule R V) (hM : Submodule.IsLattice K M)
    (hM' : Submodule.IsLattice K M') :
    latticeDistance R M M' = -latticeDistance R M' M := by
  have _ := hdim
  have _ := hM
  have _ := hM'
  change latticeLengthInt R (M ⊓ M') M - latticeLengthInt R (M ⊓ M') M' =
    -(latticeLengthInt R (M' ⊓ M) M' - latticeLengthInt R (M' ⊓ M) M)
  rw [inf_comm M' M]
  ring

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
  have _ := hdim
  change Submodule.IsLattice K (M.map (φ.restrictScalars R).toLinearMap)
  refine ⟨hM.fg.map _, ?_⟩
  apply le_antisymm le_top
  intro x hx
  have hspan : (Submodule.span K (M : Set V)).map φ.toLinearMap ≤
      Submodule.span K (M.map (φ.restrictScalars R).toLinearMap : Set V) := by
    rw [Submodule.map_span]
    apply Submodule.span_mono
    rintro z ⟨y, hy, rfl⟩
    apply (Submodule.mem_map (f := (φ.restrictScalars R).toLinearMap)).mpr
    exact ⟨y, hy, rfl⟩
  have hy : φ (φ.symm x) ∈ (Submodule.span K (M : Set V)).map φ.toLinearMap := by
    refine Submodule.mem_map.mpr ⟨φ.symm x, ?_, rfl⟩
    rw [hM.span_eq_top]
    exact Submodule.mem_top
  simpa using hspan hy

private theorem latticeLengthNat_latticeMap_of_le
    {R : Type u} {K : Type v} {V : Type v}
    [CommRing R] [Field K] [Algebra R K]
    [AddCommGroup V] [Module K V] [Module R V]
    [IsScalarTower R K V] (φ : V ≃ₗ[K] V)
    (N M : Submodule R V) (hNM : N ≤ M) :
    latticeLengthNat R (latticeMap φ N) (latticeMap φ M) =
      latticeLengthNat R N M := by
  let e : M ≃ₗ[R] latticeMap φ M :=
    Submodule.equivMapOfInjective (φ.restrictScalars R).toLinearMap
      (φ.restrictScalars R).injective M
  let P : Submodule R (M : Type v) := Submodule.comap M.subtype N
  let Q : Submodule R (latticeMap φ M : Type v) :=
    Submodule.comap (latticeMap φ M).subtype (latticeMap φ N)
  have hPQ : P.map (e : (M : Type v) →ₗ[R] (latticeMap φ M : Type v)) = Q := by
    ext z
    constructor
    · rintro ⟨y, hy, rfl⟩
      change φ (y : V) ∈ latticeMap φ N
      exact ⟨(y : V), hy, rfl⟩
    · intro hz
      change (z : V) ∈ latticeMap φ N at hz
      rcases hz with ⟨y, hy, hzy⟩
      let y' : M := ⟨y, hNM hy⟩
      refine ⟨y', hy, ?_⟩
      apply Subtype.ext
      exact hzy
  have hquot := Submodule.Quotient.equiv P Q e hPQ
  have hlength := LinearEquiv.length_eq hquot
  simpa [latticeLengthNat, latticeQuotient, P, Q] using
    (congrArg ENat.toNat hlength).symm

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
  have _ := hdim
  have _ := hM
  have _ := hM'
  have hmap_inf : latticeMap φ (M ⊓ M') =
      latticeMap φ M ⊓ latticeMap φ M' := by
    ext x
    constructor
    · intro hx
      rcases hx with ⟨y, hy, hxy⟩
      exact ⟨⟨y, hy.1, hxy⟩, ⟨y, hy.2, hxy⟩⟩
    · intro hx
      rcases hx with ⟨hy, hz⟩
      rcases hy with ⟨y, hy, hxy⟩
      rcases hz with ⟨z, hz, hzx⟩
      have hyz : y = z := φ.injective (hxy.trans hzx.symm)
      subst z
      exact ⟨y, ⟨hy, hz⟩, hxy⟩
  have hleft := latticeLengthNat_latticeMap_of_le φ (M ⊓ M') M inf_le_left
  have hright := latticeLengthNat_latticeMap_of_le φ (M ⊓ M') M' inf_le_right
  change latticeLengthInt R (latticeMap φ M ⊓ latticeMap φ M')
      (latticeMap φ M) - latticeLengthInt R
        (latticeMap φ M ⊓ latticeMap φ M') (latticeMap φ M') =
    latticeLengthInt R (M ⊓ M') M - latticeLengthInt R (M ⊓ M') M'
  rw [← hmap_inf]
  change (latticeLengthNat R (latticeMap φ (M ⊓ M')) (latticeMap φ M) : ℤ) -
      latticeLengthNat R (latticeMap φ (M ⊓ M')) (latticeMap φ M') =
    (latticeLengthNat R (M ⊓ M') M : ℤ) -
      latticeLengthNat R (M ⊓ M') M'
  rw [hleft, hright]

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
  have hφM := isLattice_latticeMap hdim φ M hM
  have hφM' := isLattice_latticeMap hdim φ M' hM'
  have h1 := latticeDistance_additive hdim M M' (latticeMap φ M)
    hM hM' hφM
  have h2 := latticeDistance_additive hdim M' (latticeMap φ M') (latticeMap φ M)
    hM' hφM' hφM
  have h3 := latticeDistance_latticeMap_pair hdim φ M' M hM' hM
  have h4 := latticeDistance_antisymm hdim M' M hM' hM
  rw [h1, h2, h3, h4]
  ring

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
  have hψM := isLattice_latticeMap hdim ψ M hM
  have hψφM := isLattice_latticeMap hdim (ψ.trans φ) M hM
  have hfirst := latticeDistance_additive hdim M (latticeMap ψ M)
    (latticeMap (ψ.trans φ) M) hM hψM hψφM
  have hsecond := latticeDistance_map_independent hdim φ M (latticeMap ψ M)
    hM hψM
  have hcomp : latticeMap (ψ.trans φ) M = latticeMap φ (latticeMap ψ M) := by
    ext x
    constructor
    · intro hx
      rcases hx with ⟨y, hy, hxy⟩
      exact ⟨ψ y, ⟨y, hy, rfl⟩, by simpa using hxy⟩
    · intro hx
      rcases hx with ⟨z, hz, hzx⟩
      rcases hz with ⟨y, hy, hyz⟩
      exact ⟨y, hy, by
        change φ (ψ y) = x
        have hyz' : ψ y = z := by simpa using hyz
        have hzx' : φ z = x := by simpa using hzx
        rw [hyz']
        exact hzx'⟩
  constructor
  · exact hfirst
  · rw [hcomp]
    exact hsecond.symm

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
  simpa only [LinearEquiv.det_trans] using
    orderOfVanishing_mul hnoetherian hdim (LinearEquiv.det φ) (LinearEquiv.det ψ)

private noncomputable def coordinateLattice
    {R : Type u} {K : Type v} [CommRing R] [IsDomain R]
    [Field K] [Algebra R K] [IsFractionRing R K] (n : ℕ) :
    Submodule R (Fin n → K) :=
  LinearMap.range (LinearMap.piMap (fun _ : Fin n => Algebra.linearMap R K))

private theorem coordinateLattice_isLattice
    {R : Type u} {K : Type v} [CommRing R] [IsDomain R]
    [Field K] [Algebra R K] [IsFractionRing R K] (n : ℕ) :
    Submodule.IsLattice K (coordinateLattice (R := R) (K := K) n) := by
  let f : (Fin n → R) →ₗ[R] (Fin n → K) :=
    LinearMap.piMap (fun _ : Fin n => Algebra.linearMap R K)
  have hf : Function.Injective f := by
    intro x y hxy
    funext i
    have h := congrArg (fun z : Fin n → K => z i) hxy
    simpa [f, LinearMap.piMap, Algebra.linearMap] using h
  have hfg : (LinearMap.range f).FG := by
    rw [← Module.Finite.iff_fg]
    exact Module.Finite.range f
  have hspan : Submodule.span K (LinearMap.range f : Set (Fin n → K)) = ⊤ := by
    apply top_unique
    intro x hx
    rw [pi_eq_sum_univ x]
    apply Submodule.sum_mem
    intro i hi
    apply Submodule.smul_mem
    · exact Submodule.subset_span ⟨Pi.single i 1, by
        ext j
        by_cases hji : i = j <;>
          simp [f, LinearMap.piMap, Algebra.linearMap, hji]⟩
  exact ⟨hfg, hspan⟩

private theorem coordinateLattice_length_smul
    {R : Type u} {K : Type v} [CommRing R] [IsDomain R]
    [Field K] [Algebra R K] [IsFractionRing R K] (n : ℕ) (c : R)
    (_hc : c ≠ 0) :
    latticeLengthInt R
        (LinearMap.range
          ((LinearMap.piMap (fun _ : Fin n => Algebra.linearMap R K)).comp
            (LinearMap.lsmul R (Fin n → R) c)))
        (coordinateLattice (R := R) (K := K) n) =
      (n : ℤ) * principalQuotientLength R c := by
  let f : (Fin n → R) →ₗ[R] (Fin n → K) :=
    LinearMap.piMap (fun _ : Fin n => Algebra.linearMap R K)
  let g : (Fin n → R) →ₗ[R] (Fin n → K) :=
    f.comp (LinearMap.lsmul R (Fin n → R) c)
  let U : Submodule R (Fin n → K) := LinearMap.range f
  let N : Submodule R (Fin n → K) := LinearMap.range g
  let Q : Submodule R (Fin n → R) :=
    Submodule.pi Set.univ (fun _ : Fin n => Ideal.span ({c} : Set R))
  have hf : Function.Injective f := by
    intro x y hxy
    funext i
    have h := congrArg (fun z : Fin n → K => z i) hxy
    simpa [f, LinearMap.piMap, Algebra.linearMap] using h
  have hQ : Q = LinearMap.range (LinearMap.lsmul R (Fin n → R) c) := by
    ext x
    constructor
    · intro hx
      rw [Submodule.mem_pi] at hx
      choose y hy using fun i =>
        (Submodule.mem_span_singleton.mp (hx i (Set.mem_univ i)))
      refine ⟨y, ?_⟩
      ext i
      simpa [LinearMap.lsmul_apply, smul_eq_mul, mul_comm] using hy i
    · rintro ⟨y, rfl⟩
      rw [Submodule.mem_pi]
      intro i hi
      apply Submodule.mem_span_singleton.mpr
      refine ⟨y i, ?_⟩
      simp [LinearMap.lsmul_apply, smul_eq_mul, mul_comm]
  have hN_le_U : N ≤ U := by
    intro z hz
    rcases hz with ⟨y, rfl⟩
    exact ⟨LinearMap.lsmul R (Fin n → R) c y, rfl⟩
  let fU : (Fin n → R) →ₗ[R] U := f.codRestrict U (by
    intro x
    exact ⟨x, rfl⟩)
  have hfU : Function.Bijective fU := by
    constructor
    · intro x y hxy
      exact hf (Subtype.ext_iff.mp hxy)
    · intro z
      rcases z.property with ⟨x, hx⟩
      refine ⟨x, ?_⟩
      apply Subtype.ext
      exact hx
  let e : (Fin n → R) ≃ₗ[R] U := LinearEquiv.ofBijective fU hfU
  let P : Submodule R U := N.comap U.subtype
  have hmap : Q.map e.toLinearMap = P := by
    have he_apply (w : Fin n → R) : (e w : Fin n → K) = f w := by
      change (fU w : Fin n → K) = f w
      rfl
    ext z
    constructor
    · rintro ⟨y, hy, rfl⟩
      change (e y : Fin n → K) ∈ N
      rw [hQ] at hy
      rcases hy with ⟨w, rfl⟩
      exact ⟨w, by rw [he_apply]; rfl⟩
    · intro hz
      change (z : Fin n → K) ∈ N at hz
      rcases hz with ⟨y, hy⟩
      refine ⟨LinearMap.lsmul R (Fin n → R) c y, ?_, ?_⟩
      · rw [hQ]
        exact ⟨y, rfl⟩
      · apply Subtype.ext
        calc
          (e (LinearMap.lsmul R (Fin n → R) c y) : Fin n → K) =
              f (LinearMap.lsmul R (Fin n → R) c y) := he_apply _
          _ = g y := by rfl
          _ = (z : Fin n → K) := hy
  have hquot :
      Module.length R (U ⧸ P) = Module.length R ((Fin n → R) ⧸ Q) := by
    have h := LinearEquiv.length_eq (Submodule.Quotient.equiv Q P e hmap)
    exact h.symm
  have hquot_pi :
      Module.length R ((Fin n → R) ⧸ Q) =
        ∑ i : Fin n, Module.length R (R ⧸ Ideal.span ({c} : Set R)) := by
    rw [show Q = Submodule.pi Set.univ
      (fun _ : Fin n => Ideal.span ({c} : Set R)) from rfl]
    rw [LinearEquiv.length_eq
      (Submodule.quotientPi (fun _ : Fin n => Ideal.span ({c} : Set R)))]
    rw [Module.length_pi_of_fintype]
  have hlength : Module.length R (U ⧸ P) = (n : ℕ∞) * Ring.ord R c := by
    rw [hquot, hquot_pi]
    simp [Ring.ord]
  change (latticeLengthNat R N U : ℤ) = _
  rw [show latticeLengthNat R N U = (Module.length R (U ⧸ P)).toNat by rfl,
    hlength]
  simp [principalQuotientLength, ENat.toNat_mul]

private theorem coordinateLattice_length_diagonal
    {R : Type u} {K : Type v} [CommRing R] [IsDomain R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (hnoetherian : IsNoetherianRing R) (hdim : ringKrullDim R = 1)
    (n : ℕ) (d : Fin n → R)
    (hd : ∀ i, d i ≠ 0) :
    latticeLengthInt R
        (LinearMap.range
          ((LinearMap.piMap (fun _ : Fin n => Algebra.linearMap R K)).comp
            (LinearMap.piMap (fun i : Fin n =>
              LinearMap.lsmul R R (d i)))))
        (coordinateLattice (R := R) (K := K) n) =
      ∑ i : Fin n, principalQuotientLength R (d i) := by
  let _ : IsNoetherianRing R := hnoetherian
  let _ : Ring.KrullDimLE 1 R := Ring.krullDimLE_iff.mpr hdim.le
  let f : (Fin n → R) →ₗ[R] (Fin n → K) :=
    LinearMap.piMap (fun _ : Fin n => Algebra.linearMap R K)
  let s : (Fin n → R) →ₗ[R] (Fin n → R) :=
    LinearMap.piMap (fun i : Fin n => LinearMap.lsmul R R (d i))
  let g : (Fin n → R) →ₗ[R] (Fin n → K) := f.comp s
  let U : Submodule R (Fin n → K) := LinearMap.range f
  let N : Submodule R (Fin n → K) := LinearMap.range g
  let Q : Submodule R (Fin n → R) :=
    Submodule.pi Set.univ (fun i : Fin n => Ideal.span ({d i} : Set R))
  have hf : Function.Injective f := by
    intro x y hxy
    funext i
    have h := congrArg (fun z : Fin n → K => z i) hxy
    simpa [f, LinearMap.piMap, Algebra.linearMap] using h
  have hQ : Q = LinearMap.range s := by
    ext x
    constructor
    · intro hx
      rw [Submodule.mem_pi] at hx
      choose y hy using fun i =>
        (Submodule.mem_span_singleton.mp (hx i (Set.mem_univ i)))
      refine ⟨y, ?_⟩
      ext i
      simpa [s, LinearMap.piMap, LinearMap.lsmul_apply, smul_eq_mul, mul_comm] using
        hy i
    · rintro ⟨y, rfl⟩
      rw [Submodule.mem_pi]
      intro i hi
      apply Submodule.mem_span_singleton.mpr
      refine ⟨y i, ?_⟩
      simp [s, LinearMap.piMap, LinearMap.lsmul_apply, smul_eq_mul, mul_comm]
  let fU : (Fin n → R) →ₗ[R] U := f.codRestrict U (by
    intro x
    exact ⟨x, rfl⟩)
  have hfU : Function.Bijective fU := by
    constructor
    · intro x y hxy
      exact hf (Subtype.ext_iff.mp hxy)
    · intro z
      rcases z.property with ⟨x, hx⟩
      refine ⟨x, ?_⟩
      apply Subtype.ext
      exact hx
  let e : (Fin n → R) ≃ₗ[R] U := LinearEquiv.ofBijective fU hfU
  let P : Submodule R U := N.comap U.subtype
  have hmap : Q.map e.toLinearMap = P := by
    have he_apply (w : Fin n → R) : (e w : Fin n → K) = f w := by
      change (fU w : Fin n → K) = f w
      rfl
    ext z
    constructor
    · rintro ⟨y, hy, rfl⟩
      change (e y : Fin n → K) ∈ N
      rw [hQ] at hy
      rcases hy with ⟨w, rfl⟩
      exact ⟨w, by rw [he_apply]; rfl⟩
    · intro hz
      change (z : Fin n → K) ∈ N at hz
      rcases hz with ⟨y, hy⟩
      refine ⟨s y, ?_, ?_⟩
      · rw [hQ]
        exact ⟨y, rfl⟩
      · apply Subtype.ext
        calc
          (e (s y) : Fin n → K) = f (s y) := he_apply _
          _ = g y := by rfl
          _ = (z : Fin n → K) := hy
  have hquot :
      Module.length R (U ⧸ P) = Module.length R ((Fin n → R) ⧸ Q) := by
    have h := LinearEquiv.length_eq (Submodule.Quotient.equiv Q P e hmap)
    exact h.symm
  have hquot_pi :
      Module.length R ((Fin n → R) ⧸ Q) =
        ∑ i : Fin n, Module.length R (R ⧸ Ideal.span ({d i} : Set R)) := by
    rw [LinearEquiv.length_eq
      (Submodule.quotientPi (fun i : Fin n => Ideal.span ({d i} : Set R)))]
    rw [Module.length_pi_of_fintype]
  have hlength : Module.length R (U ⧸ P) =
      ∑ i : Fin n, Ring.ord R (d i) := by
    rw [hquot, hquot_pi]
    simp [Ring.ord]
  change (latticeLengthNat R N U : ℤ) = _
  rw [show latticeLengthNat R N U = (Module.length R (U ⧸ P)).toNat by rfl,
    hlength]
  simp only [principalQuotientLength]
  rw [ENat.toNat_sum (fun i _ => Ring.ord_ne_top
    (mem_nonZeroDivisors_iff_ne_zero.mpr (hd i)))]

private noncomputable def coordinateDiagonal
    {K : Type v} [Field K] (n : ℕ) (i : Fin n) (a : Kˣ) :
    (Fin n → K) ≃ₗ[K] (Fin n → K) :=
  LinearEquiv.piCongrRight (fun j =>
    if _h : j = i then a.mulLeftLinearEquiv K K else LinearEquiv.refl K K)

private theorem coordinateDiagonal_matrix
    {K : Type u} {n : ℕ} [Field K] (i : Fin n) (a : Kˣ) :
    (coordinateDiagonal n i a).toLinearMap =
        Matrix.toLin' (Matrix.diagonal (Function.update 1 i (a : K))) := by
  ext x j
  by_cases hj : j = i <;>
    simp [coordinateDiagonal, Matrix.toLin'_apply, Matrix.diagonal,
      Matrix.mulVec, dotProduct, hj]

private theorem latticeDistance_coordinateDiagonal
    {R : Type u} {K : Type v} [CommRing R] [IsLocalRing R]
    [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
    (hnoetherian : IsNoetherianRing R) (hdim : ringKrullDim R = 1)
    (n : ℕ) (i : Fin n) (a : Kˣ) (M : Submodule R (Fin n → K))
    (hM : Submodule.IsLattice K M) :
    latticeDistance R M (latticeMap (coordinateDiagonal n i a) M) =
      orderOfVanishing hnoetherian hdim a := by
  let _ : Ring.KrullDimLE 1 R := Ring.krullDimLE_iff.mpr hdim.le
  let D := coordinateDiagonal n i a
  let U : Submodule R (Fin n → K) := coordinateLattice (R := R) (K := K) n
  have hU : Submodule.IsLattice K U := coordinateLattice_isLattice n
  have hDU : Submodule.IsLattice K (latticeMap D U) :=
    isLattice_latticeMap hdim D U hU
  have hdist := latticeDistance_map_independent hdim D M U hM hU
  obtain ⟨x, y, hy, hxy⟩ := IsFractionRing.div_surjective (A := R) (a : K)
  have hx : x ≠ 0 := by
    intro hx
    have hz : (a : K) = 0 := by
      rw [← hxy]
      simp [hx]
    exact a.ne_zero hz
  have hyK : (algebraMap R K) y ≠ 0 := by
    intro h
    apply mem_nonZeroDivisors_iff_ne_zero.mp hy
    apply IsFractionRing.injective R K
    simpa using h
  have hxy' : (a : K) * (algebraMap R K) y = (algebraMap R K) x := by
    rw [← hxy]
    field_simp [hyK]
  let c : R := x * y
  let d : Fin n → R := fun j => if j = i then y ^ 2 else c
  let f : (Fin n → R) →ₗ[R] (Fin n → K) :=
    LinearMap.piMap (fun _ : Fin n => Algebra.linearMap R K)
  let U' : Submodule R (Fin n → K) := LinearMap.range f
  let N : Submodule R (Fin n → K) :=
    LinearMap.range (f.comp (LinearMap.lsmul R (Fin n → R) c))
  let N' : Submodule R (Fin n → K) :=
    LinearMap.range (f.comp (LinearMap.piMap (fun j : Fin n =>
      LinearMap.lsmul R R (d j))))
  have hc : c ≠ 0 := mul_ne_zero hx (mem_nonZeroDivisors_iff_ne_zero.mp hy)
  have hd : ∀ j, d j ≠ 0 := by
    intro j
    by_cases hji : j = i
    · simp [d, hji, mem_nonZeroDivisors_iff_ne_zero.mp hy]
    · simp [d, hji, hc]
  have hU_eq : U' = U := by rfl
  have hN_le_U : N ≤ U := by
    intro z hz
    rcases hz with ⟨w, rfl⟩
    exact ⟨LinearMap.lsmul R (Fin n → R) c w, rfl⟩
  have hN_le_DU : N ≤ latticeMap D U := by
    intro z hz
    rcases hz with ⟨w, rfl⟩
    refine ⟨f (fun j => if j = i then y ^ 2 * w j else c * w j), ?_, ?_⟩
    · exact ⟨_, rfl⟩
    · ext j
      by_cases hji : j = i
      · subst j
        simp [D, coordinateDiagonal, f, LinearMap.piMap,
          LinearMap.lsmul_apply, c, Algebra.linearMap]
        calc
          (a : K) * ((algebraMap R K y) ^ 2 * (algebraMap R K (w i))) =
              ((a : K) * algebraMap R K y) *
                (algebraMap R K y * algebraMap R K (w i)) := by ring
          _ = (algebraMap R K x) *
                (algebraMap R K y * algebraMap R K (w i)) := by rw [hxy']
          _ = _ := by
            rw [Algebra.smul_def, map_mul]
            have h := mul_assoc ((algebraMap R K) x) ((algebraMap R K) y)
              ((algebraMap R K) (w i))
            exact h.symm
      · simp [D, f, LinearMap.piMap, LinearMap.lsmul_apply, c, hji,
          coordinateDiagonal, Algebra.linearMap, Algebra.smul_def, map_mul,
          mul_assoc]
  have hN'_eq : latticeMap D.symm N = N' := by
    ext z
    constructor
    · rintro ⟨w, ⟨v, rfl⟩, rfl⟩
      refine ⟨v, ?_⟩
      ext j
      by_cases hji : j = i
      · subst j
        simp [D, coordinateDiagonal, f, LinearMap.piMap,
          LinearMap.lsmul_apply, c, d, Algebra.linearMap]
        rw [Units.symm_mulLeftLinearEquiv_apply]
        rw [Algebra.smul_def, map_mul, ← hxy']
        field_simp
        rw [Units.val_inv_eq_inv_val]
        simp [a.ne_zero]
      · simp [D, coordinateDiagonal, f, LinearMap.piMap,
          LinearMap.lsmul_apply, c, d, hji, Algebra.linearMap,
          Algebra.smul_def, map_mul, mul_assoc]
    · rintro ⟨v, rfl⟩
      refine ⟨f ((LinearMap.lsmul R (Fin n → R) c) v),
        ⟨v, rfl⟩, ?_⟩
      ext j
      by_cases hji : j = i
      · subst j
        simp [D, coordinateDiagonal, f, LinearMap.piMap,
          LinearMap.lsmul_apply, c, d, Algebra.linearMap]
        rw [Units.symm_mulLeftLinearEquiv_apply]
        rw [Algebra.smul_def, map_mul, ← hxy']
        field_simp
        rw [Units.val_inv_eq_inv_val]
        simp [a.ne_zero]
      · simp [D, coordinateDiagonal, f, LinearMap.piMap,
          LinearMap.lsmul_apply, c, d, hji, Algebra.linearMap,
          Algebra.smul_def, map_mul, mul_assoc]
  have hcomp : latticeMap D.symm (latticeMap D U) = U := by
    ext z
    constructor
    · rintro ⟨w, hw, hzw⟩
      rcases hw with ⟨v, hv, hvw⟩
      change D.symm w = z at hzw
      change D v = w at hvw
      have hvz : v = z := by
        calc
          v = D.symm (D v) := by simp
          _ = D.symm w := by rw [hvw]
          _ = z := hzw
      rw [← hvz]
      exact hv
    · intro hz
      refine ⟨D z, ⟨z, hz, rfl⟩, ?_⟩
      simp
  have hlenN : latticeLengthInt R N U =
      (n : ℤ) * principalQuotientLength R c := by
    simpa [N, U, U', f] using coordinateLattice_length_smul n c hc
  have hlenN' : latticeLengthInt R N' U =
      ∑ j : Fin n, principalQuotientLength R (d j) := by
    simpa [N', U, U', f] using
      coordinateLattice_length_diagonal hnoetherian hdim n d hd
  have hN : Submodule.IsLattice K N := by
    have hfg : N.FG := by
      rw [← Module.Finite.iff_fg]
      exact Module.Finite.range _
    have hspan : Submodule.span K (N : Set (Fin n → K)) = ⊤ := by
      apply top_unique
      intro z hz
      rw [pi_eq_sum_univ z]
      apply Submodule.sum_mem
      intro j hj
      apply Submodule.smul_mem
      · have hmem : f (Pi.single j c) ∈ N := by
          refine ⟨Pi.single j 1, ?_⟩
          ext k
          by_cases hkj : k = j
          · subst k
            simp [f, LinearMap.comp_apply, LinearMap.piMap,
              LinearMap.lsmul_apply, Algebra.linearMap]
            rw [Algebra.smul_def]
            simp
          · simp [f, LinearMap.comp_apply, LinearMap.piMap,
              LinearMap.lsmul_apply, Algebra.linearMap, hkj]
        have hcK : (algebraMap R K) c ≠ 0 := by
          intro hcK
          apply hc
          apply IsFractionRing.injective R K
          simpa using hcK
        have hmem' : f (Pi.single j c) ∈
            Submodule.span K (N : Set (Fin n → K)) :=
          Submodule.subset_span hmem
        have heq : (Pi.single j 1 : Fin n → K) =
            ((algebraMap R K) c)⁻¹ • f (Pi.single j c) := by
          ext k
          by_cases hkj : k = j <;>
            simp [f, LinearMap.piMap, Algebra.linearMap, hkj,
              smul_eq_mul, hcK]
        have hsingle : (Pi.single j 1 : Fin n → K) ∈
            Submodule.span K (N : Set (Fin n → K)) := by
          rw [heq]
          exact Submodule.smul_mem _ _ hmem'
        rw [show (fun j_1 : Fin n => if j = j_1 then (1 : K) else 0) =
            (Pi.single j 1 : Fin n → K) by
              funext k
              by_cases hkj : k = j
              · subst k
                simp
              · have hkj' : j ≠ k := Ne.symm hkj
                simp [hkj, hkj']]
        exact hsingle
    exact ⟨hfg, hspan⟩
  have hlenmap := latticeLengthNat_latticeMap_of_le D.symm N (latticeMap D U)
    hN_le_DU
  have hlenDU : latticeLengthInt R N (latticeMap D U) =
      latticeLengthInt R N' U := by
    have hlenmap_int : latticeLengthInt R N (latticeMap D U) =
        latticeLengthInt R (latticeMap D.symm N)
          (latticeMap D.symm (latticeMap D U)) := by
      change (latticeLengthNat R N (latticeMap D U) : ℤ) =
        (latticeLengthNat R (latticeMap D.symm N)
          (latticeMap D.symm (latticeMap D U)) : ℤ)
      exact_mod_cast hlenmap.symm
    rw [hN'_eq, hcomp] at hlenmap_int
    exact hlenmap_int
  have hsup : Submodule.IsLattice K (U ⊔ latticeMap D U) :=
    lattice_intersection_and_sum hdim U (latticeMap D U) hU hDU |>.2
  have hcompare := lattice_length_comparison hdim U (latticeMap D U) N
    (U ⊔ latticeMap D U) hU hDU hN hsup
    (by
      intro z hz
      exact ⟨hN_le_U hz, hN_le_DU hz⟩) (by exact le_rfl)
  rw [hdist]
  change latticeLengthInt R (U ⊓ latticeMap D U) U -
      latticeLengthInt R (U ⊓ latticeMap D U) (latticeMap D U) = _
  rw [hcompare.1, hlenN, hlenDU]
  have hpc : principalQuotientLength R c =
      principalQuotientLength R x + principalQuotientLength R y := by
    have hx' : x ∈ nonZeroDivisors R :=
      mem_nonZeroDivisors_iff_ne_zero.mpr hx
    have hy' : y ∈ nonZeroDivisors R :=
      mem_nonZeroDivisors_iff_ne_zero.mpr
        (mem_nonZeroDivisors_iff_ne_zero.mp hy)
    have h := congrArg ENat.toNat (Ring.ord_mul R (a := x) (b := y) hy')
    rw [ENat.toNat_add (Ring.ord_ne_top hx') (Ring.ord_ne_top hy')] at h
    simpa [principalQuotientLength, c] using h
  have hpy : principalQuotientLength R (y ^ 2) =
      2 * principalQuotientLength R y := by
    have hy' : y ∈ nonZeroDivisors R :=
      mem_nonZeroDivisors_iff_ne_zero.mpr
        (mem_nonZeroDivisors_iff_ne_zero.mp hy)
    have h := congrArg ENat.toNat
      (Ring.ord_mul R (a := y) (b := y) hy')
    rw [ENat.toNat_add (Ring.ord_ne_top hy') (Ring.ord_ne_top hy')] at h
    simpa [pow_two, principalQuotientLength, two_mul] using h
  have hsum : ∑ j : Fin n, (principalQuotientLength R (d j) : ℤ) =
      (principalQuotientLength R (y ^ 2) : ℤ) +
        ((n : ℤ) - 1) * principalQuotientLength R c := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
    congr 1
    · simp [d]
    · calc
        (Finset.univ.erase i).sum (fun j =>
            (principalQuotientLength R (d j) : ℤ)) =
            (Finset.univ.erase i).sum (fun j =>
              (principalQuotientLength R c : ℤ)) := by
          apply Finset.sum_congr rfl
          intro j hj
          have hji : j ≠ i := (Finset.mem_erase.mp hj).1
          simp [d, hji]
        _ = (Finset.card (Finset.univ.erase i) : ℤ) *
            principalQuotientLength R c := by
          rw [Finset.sum_const]
          simp
        _ = ((n : ℤ) - 1) * principalQuotientLength R c := by
          rw [Finset.card_erase_of_mem (Finset.mem_univ i)]
          rw [Finset.card_univ]
          simp only [Fintype.card_fin]
          have hi : (i : ℕ) < n := i.isLt
          have hn : 1 ≤ n := by omega
          rw [Nat.cast_sub hn]
          norm_num
  have hfinal : (n : ℤ) * principalQuotientLength R c -
      ∑ j : Fin n, (principalQuotientLength R (d j) : ℤ) =
      principalQuotientLength R x - principalQuotientLength R y := by
    rw [hsum, hpc, hpy]
    push_cast
    ring
  rw [hlenN']
  push_cast
  rw [hfinal]
  have ha : a = fractionUnit (R := R) (K := K) x y
      (mem_nonZeroDivisors_iff_ne_zero.mpr hx) hy := by
    apply Units.ext
    change (a : K) = algebraMap R K x / algebraMap R K y
    exact hxy.symm
  rw [ha]
  exact (orderOfVanishing_fractionUnit hnoetherian hdim x y
    (mem_nonZeroDivisors_iff_ne_zero.mpr hx) hy).symm

private theorem transvection_square_add_pre
    {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V]
    {f : Module.Dual K V} {v : V} (hfv : f v = 0) (x : V) :
    LinearEquiv.transvection hfv (LinearEquiv.transvection hfv x) =
      LinearEquiv.transvection hfv x + LinearEquiv.transvection hfv x - x := by
  simp [LinearMap.transvection.apply]
  rw [hfv]
  module

private theorem latticeDistance_transvection_pre
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
  let e := LinearEquiv.transvection hfv
  let L := M ⊔ latticeMap e M
  have heM : Submodule.IsLattice K (latticeMap e M) :=
    isLattice_latticeMap hdim e M hM
  have hL : Submodule.IsLattice K L :=
    (lattice_intersection_and_sum hdim M (latticeMap e M) hM heM).2
  have hmap_sup (N P : Submodule R V) :
      latticeMap e (N ⊔ P) = latticeMap e N ⊔ latticeMap e P := by
    change (N ⊔ P).map (e.restrictScalars R).toLinearMap =
      N.map (e.restrictScalars R).toLinearMap ⊔
        P.map (e.restrictScalars R).toLinearMap
    rw [Submodule.map_sup]
  have hpow (x : V) : e (e x) = e x + e x - x := by
    exact transvection_square_add_pre hfv x
  have he2 : latticeMap e (latticeMap e M) ≤ L := by
    intro x hx
    rcases hx with ⟨y, hy, rfl⟩
    rcases hy with ⟨z, hz, rfl⟩
    have hez : e z ∈ L :=
      (show latticeMap e M ≤ L from le_sup_right) ⟨z, hz, rfl⟩
    have hzL : z ∈ L := (show M ≤ L from le_sup_left) hz
    have hxy : e (e z) ∈ L := by
      rw [hpow]
      exact sub_mem (add_mem hez hez) hzL
    exact hxy
  have heL : latticeMap e L = L := by
    rw [hmap_sup]
    apply le_antisymm
    · exact sup_le le_sup_right he2
    · apply sup_le
      · intro x hx
        have hx₁ : e x ∈ latticeMap e M ⊔ latticeMap e (latticeMap e M) :=
          (show latticeMap e M ≤ latticeMap e M ⊔ latticeMap e (latticeMap e M)
            from le_sup_left) ⟨x, hx, rfl⟩
        have hx₂ : e (e x) ∈ latticeMap e M ⊔ latticeMap e (latticeMap e M) := by
          exact (show latticeMap e (latticeMap e M) ≤
              latticeMap e M ⊔ latticeMap e (latticeMap e M) from le_sup_right)
            (⟨e x, ⟨x, hx, rfl⟩, rfl⟩)
        have hxe : x = e x + e x - e (e x) := by
          rw [hpow]
          abel
        rw [hxe]
        exact sub_mem (add_mem hx₁ hx₁) hx₂
      · intro x hx
        rcases hx with ⟨y, hy, rfl⟩
        exact (show latticeMap e M ≤ latticeMap e M ⊔ latticeMap e (latticeMap e M)
          from le_sup_left) ⟨y, hy, rfl⟩
  calc
    latticeDistance R M (latticeMap e M) =
        latticeDistance R L (latticeMap e L) :=
      latticeDistance_map_independent hdim e M L hM hL
    _ = 0 := by rw [heL]; simp [latticeDistance]

private theorem coordinate_transvection_explicit
    {K : Type u} {n : Type v} [Field K] [Fintype n] [DecidableEq n]
    (t : Matrix.TransvectionStruct n K) :
    ∃ (e : (n → K) ≃ₗ[K] (n → K)) (f : Module.Dual K (n → K))
      (w : n → K) (hfw : f w = 0),
      e = LinearEquiv.transvection hfw ∧
        e.toLinearMap = Matrix.toLin' t.toMatrix := by
  let f : Module.Dual K (n → K) := LinearMap.proj t.j
  let w : n → K := t.c • Pi.single t.i 1
  have hfw : f w = 0 := by
    simp [f, w, t.hij]
  refine ⟨LinearEquiv.transvection hfw, f, w, hfw, rfl, ?_⟩
  ext x j
  change (LinearMap.transvection f w (Pi.single x 1)) j = _
  rw [LinearMap.transvection.apply]
  simp [f, w, Matrix.toLin'_apply, Matrix.TransvectionStruct.toMatrix,
    Matrix.transvection, LinearMap.proj, Matrix.single_apply]
  split_ifs <;> simp_all [Pi.single_apply]

private theorem coordinate_diagonal_product_pre
    {K : Type u} {n : ℕ} [CommRing K] (D : Fin n → K) :
    Finset.noncommProd (Finset.univ : Finset (Fin n))
        (fun i => Matrix.diagonal (Function.update 1 i (D i))) (by
          intro i _ j _ _
          exact Matrix.commute_diagonal _ _) = Matrix.diagonal D := by
  let f : Fin n → (Fin n → K) := fun i => Function.update 1 i (D i)
  have hdiagprod :
      ∀ (s : Finset (Fin n)) (g : Fin n → (Fin n → K))
        (comm : (s : Set (Fin n)).Pairwise
          (fun i j => Commute
            (Matrix.diagonal (g i) : Matrix (Fin n) (Fin n) K)
            (Matrix.diagonal (g j) : Matrix (Fin n) (Fin n) K))),
        Finset.noncommProd s
            (fun i => (Matrix.diagonal (g i) : Matrix (Fin n) (Fin n) K)) comm =
          (Matrix.diagonal (Finset.prod s g) : Matrix (Fin n) (Fin n) K) := by
    intro s
    induction s using Finset.cons_induction_on with
    | empty =>
        intro g comm
        simp
    | cons i s hi ih =>
        intro g comm
        rw [Finset.noncommProd_cons]
        rw [ih g (comm.mono fun _ h => Finset.mem_cons.2 (Or.inr h))]
        rw [Matrix.diagonal_mul_diagonal]
        congr 1
        ext j
        rw [Finset.prod_apply]
        rw [Finset.cons_eq_insert, Finset.prod_insert hi]
        simp [Finset.prod_apply]
  calc
    _ = Matrix.diagonal (Finset.prod (Finset.univ : Finset (Fin n)) f) := by
      simpa [f] using hdiagprod (Finset.univ : Finset (Fin n)) f (by
        intro i _ j _ _
        exact Matrix.commute_diagonal _ _)
    _ = Matrix.diagonal D := by
      congr 1
      ext j
      rw [Finset.prod_apply]
      change (Finset.univ : Finset (Fin n)).prod
        (fun c => Function.update (1 : Fin n → K) c (D c) j) = D j
      simpa [f] using
        (Finset.prod_eq_single (s := (Finset.univ : Finset (Fin n)))
          (f := fun c => Function.update (1 : Fin n → K) c (D c) j) j
          (by
            intro i _ hij
            simp [Function.update, Ne.symm hij])
          (by simp [Function.update]))

private theorem basis_coordinate_matrix_pre
    {K : Type u} {V : Type v} {n : ℕ} [Field K]
    [AddCommGroup V] [Module K V] (b : Module.Basis (Fin n) K V) (φ : V ≃ₗ[K] V) :
    LinearMap.toMatrix (Pi.basisFun K (Fin n)) (Pi.basisFun K (Fin n))
        ((b.equivFun.symm.trans φ).trans b.equivFun).toLinearMap =
      LinearMap.toMatrix b b φ.toLinearMap := by
  simp only [LinearMap.toMatrix]
  ext x
  simp [LinearEquiv.trans_apply]

private theorem isLattice_equivMap
    {R : Type u} {K : Type v} {V : Type v} {W : Type v}
    [CommRing R] [IsLocalRing R] [IsDomain R] [IsNoetherianRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [AddCommGroup V] [Module K V] [Module R V]
    [AddCommGroup W] [Module K W] [Module R W]
    [IsScalarTower R K V] [IsScalarTower R K W] [Module.Finite K V]
    [Module.Finite K W] (hdim : ringKrullDim R = 1)
    (e : V ≃ₗ[K] W) (M : Submodule R V) (hM : Submodule.IsLattice K M) :
    Submodule.IsLattice K (M.map (e.restrictScalars R).toLinearMap) := by
  have _ := hdim
  refine ⟨hM.fg.map _, ?_⟩
  have hspan : (Submodule.span K (M : Set V)).map e.toLinearMap ≤
      Submodule.span K (M.map (e.restrictScalars R).toLinearMap : Set W) := by
    rw [Submodule.map_span]
    apply Submodule.span_mono
    rintro z ⟨y, hy, rfl⟩
    apply (Submodule.mem_map (f := (e.restrictScalars R).toLinearMap)).mpr
    exact ⟨y, hy, rfl⟩
  apply le_antisymm le_top
  intro x hx
  have hy : e (e.symm x) ∈ (Submodule.span K (M : Set V)).map e.toLinearMap := by
    refine Submodule.mem_map.mpr ⟨e.symm x, ?_, rfl⟩
    rw [hM.span_eq_top]
    exact Submodule.mem_top
  simpa using hspan hy

private theorem latticeLengthNat_equivMap_of_le
    {R : Type u} {K : Type v} {V : Type v} {W : Type v}
    [CommRing R] [Field K] [Algebra R K]
    [AddCommGroup V] [Module K V] [Module R V]
    [AddCommGroup W] [Module K W] [Module R W]
    [IsScalarTower R K V] [IsScalarTower R K W]
    (e : V ≃ₗ[K] W) (N M : Submodule R V) (hNM : N ≤ M) :
    latticeLengthNat R (N.map (e.restrictScalars R).toLinearMap)
        (M.map (e.restrictScalars R).toLinearMap) =
      latticeLengthNat R N M := by
  let eM : M ≃ₗ[R] M.map (e.restrictScalars R).toLinearMap :=
    Submodule.equivMapOfInjective (e.restrictScalars R).toLinearMap
      (e.restrictScalars R).injective M
  let P : Submodule R (M : Type v) := Submodule.comap M.subtype N
  let Q : Submodule R (M.map (e.restrictScalars R).toLinearMap : Type v) :=
    Submodule.comap (M.map (e.restrictScalars R).toLinearMap).subtype
      (N.map (e.restrictScalars R).toLinearMap)
  have hPQ : P.map (eM : (M : Type v) →ₗ[R]
      (M.map (e.restrictScalars R).toLinearMap : Type v)) = Q := by
    ext z
    constructor
    · rintro ⟨y, hy, rfl⟩
      change e (y : V) ∈ N.map (e.restrictScalars R).toLinearMap
      exact ⟨(y : V), hy, rfl⟩
    · intro hz
      change (z : W) ∈ N.map (e.restrictScalars R).toLinearMap at hz
      rcases hz with ⟨y, hy, hzy⟩
      let y' : M := ⟨y, hNM hy⟩
      refine ⟨y', ?_, ?_⟩
      · change y ∈ N
        exact hy
      apply Subtype.ext
      simpa [eM, y'] using hzy
  have hquot := Submodule.Quotient.equiv P Q eM hPQ
  have hlength := LinearEquiv.length_eq hquot
  simpa [latticeLengthNat, latticeQuotient, P, Q] using
    (congrArg ENat.toNat hlength).symm

private theorem latticeDistance_equivMap_pair
    {R : Type u} {K : Type v} {V : Type v} {W : Type v}
    [CommRing R] [IsLocalRing R] [IsDomain R] [IsNoetherianRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [AddCommGroup V] [Module K V] [Module R V]
    [AddCommGroup W] [Module K W] [Module R W]
    [IsScalarTower R K V] [IsScalarTower R K W] [Module.Finite K V]
    [Module.Finite K W] (_hdim : ringKrullDim R = 1) (e : V ≃ₗ[K] W)
    (M M' : Submodule R V) (_hM : Submodule.IsLattice K M)
    (_hM' : Submodule.IsLattice K M') :
    latticeDistance R (M.map (e.restrictScalars R).toLinearMap)
        (M'.map (e.restrictScalars R).toLinearMap) =
      latticeDistance R M M' := by
  have hmap_inf : (M ⊓ M').map (e.restrictScalars R).toLinearMap =
      M.map (e.restrictScalars R).toLinearMap ⊓
        M'.map (e.restrictScalars R).toLinearMap := by
    ext x
    constructor
    · rintro ⟨y, hy, hxy⟩
      exact ⟨⟨y, hy.1, hxy⟩, ⟨y, hy.2, hxy⟩⟩
    · rintro ⟨⟨y, hy, hxy⟩, ⟨z, hz, hzx⟩⟩
      have hyz : y = z := e.injective (hxy.trans hzx.symm)
      subst z
      exact ⟨y, ⟨hy, hz⟩, hxy⟩
  have hleft := latticeLengthNat_equivMap_of_le e (M ⊓ M') M inf_le_left
  have hright := latticeLengthNat_equivMap_of_le e (M ⊓ M') M' inf_le_right
  change latticeLengthInt R
      (M.map (e.restrictScalars R).toLinearMap ⊓
        M'.map (e.restrictScalars R).toLinearMap)
      (M.map (e.restrictScalars R).toLinearMap) -
      latticeLengthInt R
        (M.map (e.restrictScalars R).toLinearMap ⊓
          M'.map (e.restrictScalars R).toLinearMap)
        (M'.map (e.restrictScalars R).toLinearMap) =
    latticeLengthInt R (M ⊓ M') M - latticeLengthInt R (M ⊓ M') M'
  rw [← hmap_inf]
  change (latticeLengthNat R ((M ⊓ M').map (e.restrictScalars R).toLinearMap)
      (M.map (e.restrictScalars R).toLinearMap) : ℤ) -
      latticeLengthNat R ((M ⊓ M').map (e.restrictScalars R).toLinearMap)
        (M'.map (e.restrictScalars R).toLinearMap) =
    (latticeLengthNat R (M ⊓ M') M : ℤ) -
      latticeLengthNat R (M ⊓ M') M'
  rw [hleft, hright]

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
  let b := Module.finBasis K V
  let q : (Fin (Module.finrank K V) → K) ≃ₗ[K] V := b.equivFun.symm
  let M0 : Submodule R (Fin (Module.finrank K V) → K) :=
    M.map (q.symm.restrictScalars R).toLinearMap
  have hM0 : Submodule.IsLattice K M0 :=
    isLattice_equivMap hdim q.symm M hM
  let A := LinearMap.toMatrix b b φ.toLinearMap
  have hA : A.det ≠ 0 := by
    change (LinearMap.toMatrix b b φ.toLinearMap).det ≠ 0
    rw [LinearMap.det_toMatrix]
    simpa only [LinearEquiv.coe_det] using (LinearEquiv.det φ).ne_zero
  let P : Matrix (Fin (Module.finrank K V)) (Fin (Module.finrank K V)) K → Prop :=
    fun B => ∃ e : (Fin (Module.finrank K V) → K) ≃ₗ[K]
        (Fin (Module.finrank K V) → K),
      e.toLinearMap = Matrix.toLin' B ∧
        latticeDistance R M0 (latticeMap e M0) =
          orderOfVanishing hnoetherian hdim (LinearEquiv.det e)
  have hPA : P A := by
    apply Matrix.diagonal_transvection_induction_of_det_ne_zero P A hA
    · intro D hD
      have hDi : ∀ i : Fin (Module.finrank K V), D i ≠ 0 := by
        intro i hi
        apply hD
        rw [Matrix.det_diagonal]
        exact Finset.prod_eq_zero (Finset.mem_univ i) hi
      have hPprod : P (Finset.noncommProd
          (Finset.univ : Finset (Fin (Module.finrank K V)))
          (fun i => Matrix.diagonal (Function.update 1 i (D i))) (by
            intro i _ j _ _
            exact Matrix.commute_diagonal _ _)) := by
        apply Finset.noncommProd_induction
        · intro B C hB hC
          rcases hB with ⟨e, he, hde⟩
          rcases hC with ⟨f, hf, hdf⟩
          refine ⟨f.trans e, ?_, ?_⟩
          · rw [show (f.trans e).toLinearMap = e.toLinearMap.comp f.toLinearMap by rfl,
              Matrix.toLin'_mul, he, hf]
          · have hcomp := latticeDistance_comp_decomposition hdim e f M0 hM0
            have hord := orderOfVanishing_det_comp hnoetherian hdim e f
            calc
              latticeDistance R M0 (latticeMap (f.trans e) M0) =
                  latticeDistance R M0 (latticeMap f M0) +
                    latticeDistance R (latticeMap f M0)
                      (latticeMap (f.trans e) M0) := hcomp.1
              _ = orderOfVanishing hnoetherian hdim (LinearEquiv.det f) +
                    orderOfVanishing hnoetherian hdim (LinearEquiv.det e) := by
                rw [hdf, hcomp.2, hde]
              _ = orderOfVanishing hnoetherian hdim
                    (LinearEquiv.det (f.trans e)) := by
                rw [hord]
                ring
        · refine ⟨LinearEquiv.refl K _, ?_, ?_⟩
          · rw [Matrix.toLin'_one]
            rfl
          · simp [latticeDistance, latticeMap, orderOfVanishing]
        · intro i hi
          let ai : Kˣ := Units.mk0 (D i) (hDi i)
          let e := coordinateDiagonal (Module.finrank K V) i ai
          have he : e.toLinearMap = Matrix.toLin'
              (Matrix.diagonal (Function.update 1 i (D i))) := by
            simpa [e, ai] using coordinateDiagonal_matrix i ai
          have hdet : LinearEquiv.det e = ai := by
            apply Units.ext
            rw [LinearEquiv.coe_det]
            rw [he, LinearMap.det_toLin', Matrix.det_diagonal]
            rw [Finset.prod_eq_single i]
            · simp [ai]
            · intro j _ hji
              simp [Function.update_of_ne hji]
            · simp
          refine ⟨e, he, ?_⟩
          rw [hdet]
          exact latticeDistance_coordinateDiagonal hnoetherian hdim
            (Module.finrank K V) i ai M0 hM0
      rw [coordinate_diagonal_product_pre] at hPprod
      assumption
    · intro t
      rcases coordinate_transvection_explicit t with
        ⟨e, f, w, hfw, he, hmatrix⟩
      refine ⟨e, hmatrix, ?_⟩
      rw [he]
      rw [latticeDistance_transvection_pre hnoetherian hdim M0 hM0 hfw]
      simp [orderOfVanishing]
    · intro B C hBdet hCdet hB hC
      rcases hB with ⟨e, he, hde⟩
      rcases hC with ⟨f, hf, hdf⟩
      refine ⟨f.trans e, ?_, ?_⟩
      · rw [show (f.trans e).toLinearMap = e.toLinearMap.comp f.toLinearMap by rfl,
          Matrix.toLin'_mul, he, hf]
      · have hcomp := latticeDistance_comp_decomposition hdim e f M0 hM0
        have hord := orderOfVanishing_det_comp hnoetherian hdim e f
        calc
          latticeDistance R M0 (latticeMap (f.trans e) M0) =
              latticeDistance R M0 (latticeMap f M0) +
                latticeDistance R (latticeMap f M0)
                  (latticeMap (f.trans e) M0) := hcomp.1
          _ = orderOfVanishing hnoetherian hdim (LinearEquiv.det f) +
                orderOfVanishing hnoetherian hdim (LinearEquiv.det e) := by
            rw [hdf, hcomp.2, hde]
          _ = orderOfVanishing hnoetherian hdim
                (LinearEquiv.det (f.trans e)) := by
            rw [hord]
            ring
  rcases hPA with ⟨e, he, hdistance⟩
  have hecoord : e = (q.trans φ).trans q.symm := by
    apply LinearEquiv.toLinearMap_injective
    apply LinearMap.toMatrix'.injective
    rw [he, LinearMap.toMatrix'_toLin']
    simpa [q, LinearMap.toMatrix_eq_toMatrix'] using
      (basis_coordinate_matrix_pre b φ).symm
  have hmap :
      (latticeMap φ M).map (q.symm.restrictScalars R).toLinearMap =
        latticeMap e M0 := by
    rw [hecoord]
    ext z
    constructor
    · rintro ⟨w, ⟨x, hx, rfl⟩, rfl⟩
      refine ⟨q.symm x, ?_, ?_⟩
      · exact ⟨x, hx, rfl⟩
      · change q.symm (φ (q (q.symm x))) = q.symm (φ x)
        simp
    · rintro ⟨x, hx, rfl⟩
      rcases hx with ⟨y, hy, hxy⟩
      refine ⟨φ y, ⟨y, hy, rfl⟩, ?_⟩
      change q.symm (φ y) = q.symm (φ (q x))
      rw [← hxy]
      simp
  have hdistmap := latticeDistance_equivMap_pair hdim q.symm M
    (latticeMap φ M) hM (isLattice_latticeMap hdim φ M hM)
  have hdetcoord : LinearEquiv.det e = LinearEquiv.det φ := by
    rw [hecoord]
    simp [q]
  calc
    latticeDistance R M (latticeMap φ M) =
        latticeDistance R M0
          ((latticeMap φ M).map (q.symm.restrictScalars R).toLinearMap) :=
      hdistmap.symm
    _ = latticeDistance R M0 (latticeMap e M0) := by rw [hmap]
    _ = orderOfVanishing hnoetherian hdim (LinearEquiv.det e) := hdistance
    _ = orderOfVanishing hnoetherian hdim (LinearEquiv.det φ) := by rw [hdetcoord]

private theorem coordinate_transvection
    {K : Type u} {n : Type v} [Field K] [Fintype n] [DecidableEq n]
    (t : Matrix.TransvectionStruct n K) :
    ∃ e : (n → K) ≃ₗ[K] (n → K),
      e.toLinearMap = Matrix.toLin' t.toMatrix ∧
        e ∈ LinearEquiv.dilatransvections K (n → K) := by
  let f : Module.Dual K (n → K) := LinearMap.proj t.j
  let w : n → K := t.c • Pi.single t.i 1
  have hfw : f w = 0 := by
    simp [f, w, t.hij]
  refine ⟨LinearEquiv.transvection hfw, ?_, ?_⟩
  · ext x j
    change (LinearMap.transvection f w (Pi.single x 1)) j = _
    rw [LinearMap.transvection.apply]
    simp [f, w, Matrix.toLin'_apply, Matrix.TransvectionStruct.toMatrix,
      Matrix.transvection, LinearMap.proj, Matrix.single_apply]
    split_ifs <;> simp_all [Pi.single_apply]
  · exact LinearEquiv.transvection_mem_dilatransvections hfw

private theorem coordinate_diagonal
    {K : Type u} {n : ℕ} [Field K] (i : Fin n) (a : Kˣ) :
    (LinearEquiv.piCongrRight (fun j : Fin n =>
      if _h : j = i then a.mulLeftLinearEquiv K K else LinearEquiv.refl K K)).toLinearMap =
        Matrix.toLin' (Matrix.diagonal (Function.update 1 i (a : K))) := by
  ext x j
  by_cases hj : j = i <;>
    simp [Matrix.toLin'_apply, Matrix.diagonal, Matrix.mulVec, dotProduct, hj]

private theorem coordinate_diagonal_mem
    {K : Type u} {n : ℕ} [Field K] (i : Fin n) (a : Kˣ) :
    (LinearEquiv.piCongrRight (fun j : Fin n =>
      if _h : j = i then a.mulLeftLinearEquiv K K else LinearEquiv.refl K K)) ∈
        LinearEquiv.dilatransvections K (Fin n → K) := by
  let f : Module.Dual K (Fin n → K) := LinearMap.proj i
  let w : Fin n → K := ((a : K) - 1) • Pi.single i 1
  refine ⟨f, w, ?_⟩
  ext x j
  by_cases hj : j = i
  · subst j
    simp [f, w, LinearMap.transvection.apply]
    ring
  · simp [f, w, LinearMap.transvection.apply, hj]

private theorem coordinate_diagonal_product
    {K : Type u} {n : ℕ} [CommRing K] (D : Fin n → K) :
    Finset.noncommProd (Finset.univ : Finset (Fin n))
        (fun i => Matrix.diagonal (Function.update 1 i (D i))) (by
          intro i _ j _ _
          exact Matrix.commute_diagonal _ _ ) = Matrix.diagonal D := by
  let f : Fin n → (Fin n → K) := fun i => Function.update 1 i (D i)
  have hdiagprod :
      ∀ (s : Finset (Fin n)) (g : Fin n → (Fin n → K))
        (comm : (s : Set (Fin n)).Pairwise
          (fun i j => Commute
            (Matrix.diagonal (g i) : Matrix (Fin n) (Fin n) K)
            (Matrix.diagonal (g j) : Matrix (Fin n) (Fin n) K))),
        Finset.noncommProd s
            (fun i => (Matrix.diagonal (g i) : Matrix (Fin n) (Fin n) K)) comm =
          (Matrix.diagonal (Finset.prod s g) :
            Matrix (Fin n) (Fin n) K) := by
    intro s
    induction s using Finset.cons_induction_on with
    | empty =>
        intro g comm
        simp
    | cons i s hi ih =>
        intro g comm
        rw [Finset.noncommProd_cons]
        rw [ih g (comm.mono fun _ h => Finset.mem_cons.2 (Or.inr h))]
        rw [Matrix.diagonal_mul_diagonal]
        congr 1
        ext j
        rw [Finset.prod_apply]
        rw [Finset.cons_eq_insert, Finset.prod_insert hi]
        simp [Finset.prod_apply]
  calc
    _ = Matrix.diagonal (Finset.prod (Finset.univ : Finset (Fin n)) f) := by
      simpa [f] using hdiagprod (Finset.univ : Finset (Fin n)) f (by
        intro i _ j _ _
        exact Matrix.commute_diagonal _ _)
    _ = Matrix.diagonal D := by
      congr 1
      ext j
      rw [Finset.prod_apply]
      change (Finset.univ : Finset (Fin n)).prod
        (fun c => Function.update (1 : Fin n → K) c (D c) j) = D j
      simpa [f] using
        (Finset.prod_eq_single (s := (Finset.univ : Finset (Fin n)))
          (f := fun c => Function.update (1 : Fin n → K) c (D c) j) j
          (by
            intro i _ hij
            simp [Function.update, Ne.symm hij])
          (by simp [Function.update]))

private theorem conjugate_dilatransvection
    {K : Type u} {V : Type v} {W : Type v} [Field K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (q : W ≃ₗ[K] V) {e : W ≃ₗ[K] W}
    (he : e ∈ LinearEquiv.dilatransvections K W) :
    (q.symm.trans e).trans q ∈ LinearEquiv.dilatransvections K V := by
  rcases he with ⟨f, w, h⟩
  refine ⟨f.comp q.symm.toLinearMap, q w, ?_⟩
  ext x
  change q (e.toLinearMap (q.symm x)) = _
  rw [h]
  simp [LinearMap.transvection.apply, LinearMap.comp_apply]

private theorem basis_coordinate_matrix
    {K : Type u} {V : Type v} {n : ℕ} [Field K]
    [AddCommGroup V] [Module K V] (b : Module.Basis (Fin n) K V) (φ : V ≃ₗ[K] V) :
    LinearMap.toMatrix (Pi.basisFun K (Fin n)) (Pi.basisFun K (Fin n))
        ((b.equivFun.symm.trans φ).trans b.equivFun).toLinearMap =
      LinearMap.toMatrix b b φ.toLinearMap := by
  simp only [LinearMap.toMatrix]
  ext x
  simp [LinearEquiv.trans_apply]

private theorem conjugate_dilatransvection_pow
    {K : Type u} {V : Type v} {W : Type v} [Field K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (q : W ≃ₗ[K] V) {e : W ≃ₗ[K] W} (m : ℕ)
    (he : e ∈ (LinearEquiv.dilatransvections K W) ^ m) :
    (q.symm.trans e).trans q ∈ (LinearEquiv.dilatransvections K V) ^ m := by
  induction m generalizing e with
  | zero =>
      change (q.symm.trans e).trans q ∈
        ({1} : Set (V ≃ₗ[K] V))
      change e ∈ ({1} : Set (W ≃ₗ[K] W)) at he
      rw [Set.mem_singleton_iff]
      have hq : (q.symm.trans (1 : W ≃ₗ[K] W)).trans q = 1 := by
        ext x
        simp [LinearEquiv.trans_apply]
      rw [← hq]
      exact congrArg (fun x : W ≃ₗ[K] W => (q.symm.trans x).trans q)
        (Set.mem_singleton_iff.mp he)
  | succ m ih =>
      rw [pow_succ] at he ⊢
      rcases Set.mem_mul.mp he with ⟨e₁, he₁, e₂, he₂, rfl⟩
      have h₁ := ih he₁
      have h₂ := conjugate_dilatransvection q he₂
      have hmul : (q.symm.trans (e₁ * e₂)).trans q =
          (q.symm.trans e₁).trans q * (q.symm.trans e₂).trans q := by
        ext x
        simp [LinearEquiv.trans_apply, LinearEquiv.mul_apply]
      rw [hmul]
      exact Set.mul_mem_mul h₁ h₂

private theorem coordinate_general_linear_generation
    {K : Type u} {n : ℕ} [Field K] :
    ∀ A : Matrix (Fin n) (Fin n) K, A.det ≠ 0 →
      ∃ m : ℕ, ∃ e : (Fin n → K) ≃ₗ[K] (Fin n → K),
        e.toLinearMap = Matrix.toLin' A ∧
          e ∈ (LinearEquiv.dilatransvections K (Fin n → K)) ^ m := by
  intro A hA
  let P : Matrix (Fin n) (Fin n) K → Prop := fun B =>
    ∃ m : ℕ, ∃ e : (Fin n → K) ≃ₗ[K] (Fin n → K),
      e.toLinearMap = Matrix.toLin' B ∧
        e ∈ (LinearEquiv.dilatransvections K (Fin n → K)) ^ m
  apply Matrix.diagonal_transvection_induction_of_det_ne_zero P A hA
  · intro D hD
    have hDi : ∀ i : Fin n, D i ≠ 0 := by
      intro i hi
      apply hD
      rw [Matrix.det_diagonal]
      exact Finset.prod_eq_zero (Finset.mem_univ i) hi
    have hPprod : P (Finset.noncommProd (Finset.univ : Finset (Fin n))
        (fun i => Matrix.diagonal (Function.update 1 i (D i))) (by
          intro i _ j _ _
          exact Matrix.commute_diagonal _ _)) := by
      apply Finset.noncommProd_induction
      · intro B C hB hC
        rcases hB with ⟨m, e, he, hme⟩
        rcases hC with ⟨k, f, hf, hkf⟩
        refine ⟨m + k, e * f, ?_, ?_⟩
        · rw [show (e * f).toLinearMap = e.toLinearMap.comp f.toLinearMap by rfl,
            Matrix.toLin'_mul, he, hf]
        · simpa [pow_add] using Set.mul_mem_mul hme hkf
      · refine ⟨0, LinearEquiv.refl K (Fin n → K), ?_, ?_⟩
        · simp [Matrix.toLin'_one]
        · ext x
          rfl
      · intro i hi
        let a : Kˣ := Units.mk0 (D i) (hDi i)
        let e := LinearEquiv.piCongrRight (fun j : Fin n =>
          if _h : j = i then a.mulLeftLinearEquiv K K else LinearEquiv.refl K K)
        refine ⟨1, e, ?_, ?_⟩
        · simpa [e, a] using coordinate_diagonal i a
        · simpa [e] using coordinate_diagonal_mem i a
    simpa [coordinate_diagonal_product] using hPprod
  · intro t
    rcases coordinate_transvection t with ⟨e, he, hme⟩
    exact ⟨1, e, he, by simpa using hme⟩
  · intro B C hB hC hPB hPC
    rcases hPB with ⟨m, e, he, hme⟩
    rcases hPC with ⟨k, f, hf, hkf⟩
    refine ⟨m + k, e * f, ?_, ?_⟩
    · rw [show (e * f).toLinearMap = e.toLinearMap.comp f.toLinearMap by rfl,
        Matrix.toLin'_mul, he, hf]
    · simpa [pow_add] using Set.mul_mem_mul hme hkf

private theorem transvection_square_add
    {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V]
    {f : Module.Dual K V} {v : V} (hfv : f v = 0) (x : V) :
    LinearEquiv.transvection hfv (LinearEquiv.transvection hfv x) =
      LinearEquiv.transvection hfv x + LinearEquiv.transvection hfv x - x := by
  simp [LinearMap.transvection.apply]
  rw [hfv]
  module

/- The source's elementary matrices are represented by Mathlib's canonical
   rank-one transvections and dilatransvections. -/
theorem generalLinearEquiv_mem_generated_dilatransvections
    {K : Type v} {V : Type v} [Field K] [AddCommGroup V] [Module K V]
    [Module.Finite K V] (φ : V ≃ₗ[K] V) :
    ∃ n : ℕ, φ ∈ (LinearEquiv.dilatransvections K V) ^ n := by
  let b := Module.finBasis K V
  let q : (Fin (Module.finrank K V) → K) ≃ₗ[K] V := b.equivFun.symm
  let A := LinearMap.toMatrix b b φ.toLinearMap
  have hA : A.det ≠ 0 := by
    change (LinearMap.toMatrix b b φ.toLinearMap).det ≠ 0
    rw [LinearMap.det_toMatrix]
    simpa only [LinearEquiv.coe_det] using (LinearEquiv.det φ).ne_zero
  rcases coordinate_general_linear_generation A hA with ⟨m, e, he, hme⟩
  have hcoord : e = (q.trans φ).trans q.symm := by
    apply LinearEquiv.toLinearMap_injective
    apply LinearMap.toMatrix'.injective
    rw [he, LinearMap.toMatrix'_toLin']
    simpa [q, LinearMap.toMatrix_eq_toMatrix'] using
      (basis_coordinate_matrix b φ).symm
  have hconj : (q.symm.trans e).trans q = φ := by
    rw [hcoord]
    ext x
    simp [LinearEquiv.trans_apply]
  refine ⟨m, ?_⟩
  simpa [hconj] using conjugate_dilatransvection_pow q m hme

theorem exists_fin_basis_equiv
    {K : Type v} {V : Type v} [Field K] [AddCommGroup V]
    [Module K V] [Module.Finite K V] :
    ∃ n : ℕ, Nonempty ((Fin n → K) ≃ₗ[K] V) := by
  exact ⟨Module.finrank K V, ⟨(Module.finBasis K V).equivFun.symm⟩⟩

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
  let e := LinearEquiv.transvection hfv
  let L := M ⊔ latticeMap e M
  have heM : Submodule.IsLattice K (latticeMap e M) :=
    isLattice_latticeMap hdim e M hM
  have hL : Submodule.IsLattice K L :=
    (lattice_intersection_and_sum hdim M (latticeMap e M) hM heM).2
  have hmap_sup (N P : Submodule R V) :
      latticeMap e (N ⊔ P) = latticeMap e N ⊔ latticeMap e P := by
    change (N ⊔ P).map (e.restrictScalars R).toLinearMap =
      N.map (e.restrictScalars R).toLinearMap ⊔
        P.map (e.restrictScalars R).toLinearMap
    rw [Submodule.map_sup]
  have hpow (x : V) : e (e x) = e x + e x - x := by
    exact transvection_square_add hfv x
  have he2 : latticeMap e (latticeMap e M) ≤ L := by
    intro x hx
    rcases hx with ⟨y, hy, rfl⟩
    rcases hy with ⟨z, hz, rfl⟩
    have hez : e z ∈ L :=
      (show latticeMap e M ≤ L from le_sup_right) ⟨z, hz, rfl⟩
    have hzL : z ∈ L := (show M ≤ L from le_sup_left) hz
    have hxy : e (e z) ∈ L := by
      rw [hpow]
      exact sub_mem (add_mem hez hez) hzL
    exact hxy
  have heL : latticeMap e L = L := by
    rw [hmap_sup]
    apply le_antisymm
    · exact sup_le le_sup_right he2
    · apply sup_le
      · intro x hx
        have hx₁ : e x ∈ latticeMap e M ⊔ latticeMap e (latticeMap e M) :=
          (show latticeMap e M ≤ latticeMap e M ⊔ latticeMap e (latticeMap e M)
            from le_sup_left) ⟨x, hx, rfl⟩
        have hx₂ : e (e x) ∈ latticeMap e M ⊔ latticeMap e (latticeMap e M) := by
          exact (show latticeMap e (latticeMap e M) ≤
              latticeMap e M ⊔ latticeMap e (latticeMap e M) from le_sup_right)
            (⟨e x, ⟨x, hx, rfl⟩, rfl⟩)
        have hxe : x = e x + e x - e (e x) := by
          rw [hpow]
          abel
        rw [hxe]
        exact sub_mem (add_mem hx₁ hx₁) hx₂
      · intro x hx
        rcases hx with ⟨y, hy, rfl⟩
        exact (show latticeMap e M ≤ latticeMap e M ⊔ latticeMap e (latticeMap e M)
          from le_sup_left) ⟨y, hy, rfl⟩
  calc
    latticeDistance R M (latticeMap e M) =
        latticeDistance R L (latticeMap e L) :=
      latticeDistance_map_independent hdim e M L hM hL
    _ = 0 := by rw [heL]; simp [latticeDistance]

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
  have hdet : LinearEquiv.det (elementaryDiagonal n i a) = a := by
    apply Units.ext
    rw [LinearEquiv.coe_det]
    have hmatrix : (elementaryDiagonal n i a).toLinearMap =
        Matrix.toLin' (Matrix.diagonal (Function.update 1 i (a : K))) := by
      ext x j
      by_cases hj : j = i <;>
        simp [elementaryDiagonal, Matrix.toLin'_apply, Matrix.diagonal,
          Matrix.mulVec, dotProduct, hj]
    rw [hmatrix, LinearMap.det_toLin', Matrix.det_diagonal]
    rw [Finset.prod_eq_single i]
    · simp
    · intro j _ hji
      simp [Function.update, hji]
    · simp
  rw [latticeDistance_map_eq_orderOfVanishing hnoetherian hdim M hM
    (elementaryDiagonal n i a), hdet]

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
