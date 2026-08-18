import Formalization.Books.Algebra.Unit37.NormalRings
import Mathlib.Algebra.Colimit.DirectLimit
import Mathlib.Algebra.Order.GroupWithZero.Range
import Mathlib.Algebra.Order.Group.Units
import Mathlib.Algebra.Order.Monoid.Submonoid
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Valuation.LocalSubring
import Mathlib.RingTheory.Valuation.ValuationSubring

/-!
# Commutative Algebra, Chapter 50: Valuation rings

The textbook's valuation rings are represented by Mathlib's `ValuationSubring`
when they are subrings of a specified field, and by the canonical
`ValuationRing` class for abstract rings.  The domination order on local
subrings is Mathlib's order on `LocalSubring`.
-/

namespace Formalization.Books.Algebra.Unit50

open Set

universe u v w

noncomputable section

/-! ## Definitions and first properties -/

/-- `B` dominates `A` in the sense of the source when `A ≤ B` in the
domination order on local subrings. -/
def Dominates {K : Type u} [Field K] (B A : LocalSubring K) : Prop := A ≤ B

theorem dominates_iff {K : Type u} [Field K] {B A : LocalSubring K} :
    Dominates B A ↔
      ∃ h : A.toSubring ≤ B.toSubring, IsLocalHom (Subring.inclusion h) :=
  LocalSubring.le_def

/- The source's definition of a valuation ring as a maximal local subring is
   represented by `ValuationSubring` and `LocalSubring.isMax_iff`. -/

/-- A valuation subring is centered on `R` when it contains `R`. -/
def CenteredOn {K : Type u} [Field K] (A : ValuationSubring K) (R : Subring K) : Prop :=
  R ≤ A.toSubring

theorem centeredOn_iff {K : Type u} [Field K] (A : ValuationSubring K) (R : Subring K) :
    CenteredOn A R ↔ R ≤ A.toSubring :=
  Iff.rfl

/-- A field, regarded as a ring, is a valuation ring. -/
theorem field_isValuationRing (K : Type u) [Field K] : ValuationRing K := by
  infer_instance

/-- A valuation subring is maximal in the domination order. -/
theorem valuationSubring_isMaximal {K : Type u} [Field K] (A : ValuationSubring K) :
    IsMax A.toLocalSubring :=
  A.isMax_toLocalSubring

/-- Maximal local subrings of a field are precisely its valuation subrings. -/
theorem localSubring_isMax_iff_valuationSubring {K : Type u} [Field K]
    {A : LocalSubring K} :
    IsMax A ↔ ∃ B : ValuationSubring K, B.toLocalSubring = A :=
  LocalSubring.isMax_iff

/-- Every local subring of a field is dominated by a valuation subring. -/
theorem exists_valuationSubring_dominating {K : Type u} [Field K]
    (A : LocalSubring K) :
    ∃ B : ValuationSubring K, Dominates B.toLocalSubring A := by
  simpa [Dominates] using LocalSubring.exists_le_valuationSubring A

/-! ## Normality and the `x` or `x⁻¹` criterion -/

/-- A valuation ring is a normal domain. -/
theorem valuationRing_isNormalDomain
    {A : Type u} [CommRing A] [IsDomain A] [ValuationRing A] :
    Formalization.Books.Algebra.Unit37.IsNormalDomain A := by
  change IsDomain A ∧ IsIntegrallyClosed A
  constructor <;> infer_instance

/-- The `x` or `x⁻¹` property for a valuation subring of a field. -/
theorem valuationSubring_mem_or_inv_mem {K : Type u} [Field K]
    (A : ValuationSubring K) (x : K) :
    x ∈ A ∨ x⁻¹ ∈ A :=
  A.mem_or_inv_mem x

/-- The same criterion for an abstract valuation ring, expressed through the
canonical fraction-ring notion of an integer. -/
theorem valuationRing_isInteger_or_isInteger
    {A : Type u} [CommRing A] [IsDomain A] [ValuationRing A]
    {K : Type v} [Field K] [Algebra A K] [IsFractionRing A K] (x : K) :
    IsLocalization.IsInteger A x ∨ IsLocalization.IsInteger A x⁻¹ :=
  ValuationRing.isInteger_or_isInteger A x

/-- A subring of a field satisfying the `x` or `x⁻¹` criterion is a valuation
subring, hence its underlying ring is a valuation ring. -/
theorem valuationRing_of_mem_or_inv_mem {K : Type u} [Field K]
    (R : Subring K) (hR : ∀ x : K, x ∈ R ∨ x⁻¹ ∈ R) :
    ValuationRing (ValuationSubring.ofSubring R hR) := by
  infer_instance

/-- Such a subring has the field as its fraction ring. -/
theorem valuationRing_of_mem_or_inv_mem_isFractionRing {K : Type u} [Field K]
    (R : Subring K) (hR : ∀ x : K, x ∈ R ∨ x⁻¹ ∈ R) :
    IsFractionRing (ValuationSubring.ofSubring R hR) K := by
  infer_instance

/-! ## Directed colimits and intersections with subfields -/

/-- A directed colimit of domains is a domain.  The explicit theorem is useful
because the generic direct-limit API does not install this instance. -/
theorem directLimit_isDomain
    {ι : Type u} [Preorder ι] [Nonempty ι] [IsDirectedOrder ι]
    {A : ι → Type v} [∀ i, CommRing (A i)] [∀ i, IsDomain (A i)]
    (f : ∀ i j, i ≤ j → A i →+* A j)
    [DirectedSystem A (f · · ·)] :
    IsDomain (DirectLimit A f) := by
  refine { mul_left_cancel_of_ne_zero := ?_, mul_right_cancel_of_ne_zero := ?_ }
  · intro a ha b c h
    obtain ⟨i, x, y, z, rfl, rfl, rfl⟩ := DirectLimit.exists_eq_mk₃ f a b c
    change (⟦⟨i, x⟩⟧ : DirectLimit A f) * ⟦⟨i, y⟩⟧ =
      ⟦⟨i, x⟩⟧ * ⟦⟨i, z⟩⟧ at h
    rw [DirectLimit.mul_def, DirectLimit.mul_def] at h
    obtain ⟨j, hij, hij', hEq⟩ := Quotient.eq.mp h
    have hxj : f i j hij x ≠ 0 := by
      intro hxj
      apply ha
      calc
        (⟦⟨i, x⟩⟧ : DirectLimit A f) =
            ⟦⟨j, f i j hij x⟩⟧ := DirectLimit.eq_of_le (f := f) ⟨i, x⟩ j hij
        _ = 0 := by rw [hxj, ← DirectLimit.zero_def j]
    have hEq' : f i j hij x * f i j hij y = f i j hij x * f i j hij z := by
      simpa only [map_mul] using hEq
    have hyz : f i j hij y = f i j hij z := mul_left_cancel₀ hxj hEq'
    apply Quotient.sound
    exact ⟨j, hij, hij', by simpa using hyz⟩
  · intro a ha b c h
    obtain ⟨i, x, y, z, rfl, rfl, rfl⟩ := DirectLimit.exists_eq_mk₃ f a b c
    change (⟦⟨i, y⟩⟧ : DirectLimit A f) * ⟦⟨i, x⟩⟧ =
      ⟦⟨i, z⟩⟧ * ⟦⟨i, x⟩⟧ at h
    rw [DirectLimit.mul_def, DirectLimit.mul_def] at h
    obtain ⟨j, hij, hij', hEq⟩ := Quotient.eq.mp h
    have hxj : f i j hij x ≠ 0 := by
      intro hxj
      apply ha
      calc
        (⟦⟨i, x⟩⟧ : DirectLimit A f) =
            ⟦⟨j, f i j hij x⟩⟧ := DirectLimit.eq_of_le (f := f) ⟨i, x⟩ j hij
        _ = 0 := by rw [hxj, ← DirectLimit.zero_def j]
    have hEq' : f i j hij y * f i j hij x = f i j hij z * f i j hij x := by
      simpa only [map_mul] using hEq
    have hyz : f i j hij y = f i j hij z := mul_right_cancel₀ hxj hEq'
    apply Quotient.sound
    exact ⟨j, hij, hij', by simpa using hyz⟩

/-- A directed colimit of valuation rings has the divisibility condition of a
valuation ring. -/
theorem directLimit_isPreValuationRing
    {ι : Type u} [Preorder ι] [Nonempty ι] [IsDirectedOrder ι]
    {A : ι → Type v} [∀ i, CommRing (A i)] [∀ i, IsDomain (A i)]
    (f : ∀ i j, i ≤ j → A i →+* A j)
    [DirectedSystem A (f · · ·)] [∀ i, ValuationRing (A i)] :
    PreValuationRing (DirectLimit A f) := by
  refine ⟨?_⟩
  intro a b
  obtain ⟨i, x, y, rfl, rfl⟩ := DirectLimit.exists_eq_mk₂ f a b
  obtain ⟨c, hc | hc⟩ := ValuationRing.cond x y
  · exact ⟨⟦⟨i, c⟩⟧, Or.inl (by rw [DirectLimit.mul_def, hc])⟩
  · exact ⟨⟦⟨i, c⟩⟧, Or.inr (by rw [DirectLimit.mul_def, hc])⟩

/-- A directed colimit of valuation rings is a valuation ring. -/
theorem directLimit_isValuationRing
    {ι : Type u} [Preorder ι] [Nonempty ι] [IsDirectedOrder ι]
    {A : ι → Type v} [∀ i, CommRing (A i)] [∀ i, IsDomain (A i)]
    (f : ∀ i j, i ≤ j → A i →+* A j)
    [DirectedSystem A (f · · ·)] [∀ i, ValuationRing (A i)] :
    letI : IsDomain (DirectLimit A f) := directLimit_isDomain f
    ValuationRing (DirectLimit A f) := by
  let : IsDomain (DirectLimit A f) := directLimit_isDomain f
  exact { toPreValuationRing := directLimit_isPreValuationRing f }

/-- The intersection of a valuation subring with a subfield is a valuation
subring of that subfield. -/
theorem fieldIntersection_isValuationRing
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    (B : ValuationSubring L) :
    ValuationRing (B.comap (algebraMap K L)) := by
  infer_instance

/-- The intersection in the preceding theorem has the expected fraction ring. -/
theorem fieldIntersection_isFractionRing
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    (B : ValuationSubring L) :
    IsFractionRing (B.comap (algebraMap K L)) K := by
  infer_instance

/-- In an algebraic field extension, a non-field valuation ring remains a
non-field after intersection with the base field. -/
theorem algebraicFieldIntersection_not_isField
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    [Algebra.IsAlgebraic K L] (B : ValuationSubring L) (hB : ¬ IsField B) :
    ¬ IsField (B.comap (algebraMap K L)) := by
  intro hA
  have hsurj : Function.Surjective
      (algebraMap (B.comap (algebraMap K L)) K) :=
    IsFractionRing.surjective_iff_isField.mpr hA
  let C : Subalgebra K L :=
    { B.toSubring with
      algebraMap_mem' := fun k => by
        obtain ⟨a, ha⟩ := hsurj k
        have ha' : (a : K) = k := ha
        rw [← ha']
        exact a.property }
  have hC : IsField C := Subalgebra.isField_of_algebraic C
  let e : C ≃+* B :=
    { toFun := fun a => ⟨a.1, a.2⟩
      invFun := fun b => ⟨b.1, b.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl
      map_add' := fun _ _ => rfl }
  exact hB (e.symm.toMulEquiv.isField hC)

/-! ## Quotients, localizations, and residue fields -/

/-- The quotient of a valuation ring by a prime ideal is a valuation ring. -/
theorem quotient_valuationRing
    {A : Type u} [CommRing A] [IsDomain A] [ValuationRing A]
    (p : Ideal A) [p.IsPrime] :
    ValuationRing (A ⧸ p) := by
  exact Function.Surjective.valuationRing (Ideal.Quotient.mk p) Ideal.Quotient.mk_surjective

/-- Localization at a prime ideal preserves the valuation-ring property. -/
theorem localizationAtPrime_valuationRing
    {A : Type u} [CommRing A] [IsDomain A] [ValuationRing A]
    (p : Ideal A) [p.IsPrime] :
    ValuationRing (Localization.AtPrime p) := by
  let : PreValuationRing (Localization.AtPrime p) := by
    refine { cond' := ?_ }
    intro x y
    obtain ⟨a, s, rfl⟩ := IsLocalization.exists_mk'_eq p.primeCompl x
    obtain ⟨b, t, rfl⟩ := IsLocalization.exists_mk'_eq p.primeCompl y
    obtain ⟨c, hc | hc⟩ := ValuationRing.cond a b
    · refine ⟨IsLocalization.mk' _ (c * s) t, Or.inl ?_⟩
      apply IsLocalization.eq_mk'_iff_mul_eq.mpr
      calc
        _ = (IsLocalization.mk' _ a s * algebraMap A _ (s : A)) *
              algebraMap A _ c := by
          rw [mul_assoc, IsLocalization.mk'_spec, map_mul]
          ac_rfl
        _ = algebraMap A _ a * algebraMap A _ c := by
          rw [IsLocalization.mk'_spec]
        _ = algebraMap A _ b := by rw [← map_mul, hc]
    · refine ⟨IsLocalization.mk' _ (c * t) s, Or.inr ?_⟩
      apply IsLocalization.eq_mk'_iff_mul_eq.mpr
      calc
        _ = (IsLocalization.mk' _ b t * algebraMap A _ (t : A)) *
              algebraMap A _ c := by
          rw [mul_assoc, IsLocalization.mk'_spec, map_mul]
          ac_rfl
        _ = algebraMap A _ b * algebraMap A _ c := by
          rw [IsLocalization.mk'_spec]
        _ = algebraMap A _ a := by rw [← map_mul, hc]
  exact { toPreValuationRing := inferInstance }

/- The source also allows an arbitrary localization.  Mathlib's
   `ValuationRing` class requires a domain, so the unrestricted statement is
   recorded at the corresponding pre-valuation level; the domain-preserving
   case below recovers the full class. -/
theorem localization_preValuationRing
    {A : Type u} [CommRing A] [IsDomain A] [ValuationRing A]
    (S : Submonoid A) :
    PreValuationRing (Localization S) := by
  refine { cond' := ?_ }
  intro x y
  obtain ⟨a, s, rfl⟩ := IsLocalization.exists_mk'_eq S x
  obtain ⟨b, t, rfl⟩ := IsLocalization.exists_mk'_eq S y
  obtain ⟨c, hc | hc⟩ := ValuationRing.cond a b
  · refine ⟨IsLocalization.mk' _ (c * s) t, Or.inl ?_⟩
    apply IsLocalization.eq_mk'_iff_mul_eq.mpr
    calc
      _ = (IsLocalization.mk' _ a s * algebraMap A _ (s : A)) *
            algebraMap A _ c := by
        rw [mul_assoc, IsLocalization.mk'_spec, map_mul]
        ac_rfl
      _ = algebraMap A _ a * algebraMap A _ c := by
        rw [IsLocalization.mk'_spec]
      _ = algebraMap A _ b := by rw [← map_mul, hc]
  · refine ⟨IsLocalization.mk' _ (c * t) s, Or.inr ?_⟩
    apply IsLocalization.eq_mk'_iff_mul_eq.mpr
    calc
      _ = (IsLocalization.mk' _ b t * algebraMap A _ (t : A)) *
            algebraMap A _ c := by
        rw [mul_assoc, IsLocalization.mk'_spec, map_mul]
        ac_rfl
      _ = algebraMap A _ b * algebraMap A _ c := by
        rw [IsLocalization.mk'_spec]
      _ = algebraMap A _ a := by rw [← map_mul, hc]

/-- Localization at any multiplicative set of non-zero-divisors preserves the
valuation-ring property. -/
theorem localization_valuationRing
    {A : Type u} [CommRing A] [IsDomain A] [ValuationRing A]
    (S : Submonoid A) (hS : S ≤ nonZeroDivisors A) :
    letI : IsDomain (Localization S) := IsLocalization.isDomain_localization hS
    ValuationRing (Localization S) := by
  sorry

/-- The pullback of a valuation ring in a residue field along the residue map.
This is the ring denoted `C` in the source. -/
def residueFieldPullback
    {L : Type u} [Field L] (A' : ValuationSubring L)
    (A : ValuationSubring (IsLocalRing.ResidueField A')) : Subring A' :=
  A.toSubring.comap (IsLocalRing.residue A')

/-- Stacking a valuation ring in the residue field of another one gives a
valuation ring. -/
theorem residueFieldPullback_isValuationRing
    {L : Type u} [Field L] (A' : ValuationSubring L)
    (A : ValuationSubring (IsLocalRing.ResidueField A')) :
    ValuationRing (residueFieldPullback A' A) := by
  sorry

/-! ## Separation by valuation rings -/

/-- An integrally closed subring of a field is contained in a valuation
subring avoiding any prescribed element outside it. -/
theorem exists_valuationSubring_avoiding
    {K : Type u} [Field K] (R : Subring K) [IsIntegrallyClosedIn R K]
    {x : K} (hx : x ∉ R) :
    ∃ V : ValuationSubring K, R ≤ V.toSubring ∧ x ∉ V :=
  R.exists_le_valuationSubring_of_isIntegrallyClosedIn hx

/-- If the subring is local, the valuation subring can be chosen to dominate
it. -/
theorem exists_valuationSubring_dominating_avoiding
    {K : Type u} [Field K] (R : LocalSubring K)
    [IsIntegrallyClosedIn R.toSubring K] {x : K} (hx : x ∉ R.toSubring) :
    ∃ V : ValuationSubring K, R ≤ V.toLocalSubring ∧ x ∉ V :=
  R.exists_le_valuationSubring_of_isIntegrallyClosedIn hx

/-- An integrally closed subring of a field is the intersection of all
valuation subrings containing it. -/
theorem subring_eq_iInf_valuationSubrings
    {K : Type u} [Field K] (R : Subring K) [IsIntegrallyClosedIn R K] :
    R = ⨅ V : {V : ValuationSubring K // R ≤ V.toSubring}, V.1.toSubring :=
  R.eq_iInf_of_isIntegrallyClosedIn

/-- The analogous intersection formula for a local subring uses domination. -/
theorem localSubring_eq_iInf_valuationSubrings
    {K : Type u} [Field K] (R : LocalSubring K)
    [IsIntegrallyClosedIn R.toSubring K] :
    R.toSubring =
      ⨅ V : {V : ValuationSubring K // R ≤ V.toLocalSubring}, V.1.toSubring :=
  R.eq_iInf_of_isIntegrallyClosedIn

/-! ## Ordered value groups and valuations -/

/- The source's “totally ordered abelian group” is represented by Mathlib's
   split assumptions `[AddCommGroup Γ] [LinearOrder Γ]
   [IsOrderedAddMonoid Γ]`; there is deliberately no parallel bundled class.
   The order dual below makes Lean's `≤` represent the source's `≥`. -/

/-- The nonzero value group associated to a valuation ring, written additively
using Mathlib's canonical subgroup of units. -/
abbrev ValueGroup
    {A : Type u} [CommRing A] [IsDomain A] [ValuationRing A]
    {K : Type v} [Field K] [Algebra A K] [IsFractionRing A K] :=
  Additive (OrderDual (MonoidWithZeroHom.valueGroup
    (ValuationRing.valuation A K).toMonoidWithZeroHom))

/-- The canonical value group with zero used internally by Mathlib. -/
abbrev ValueGroupWithZero
    {A : Type u} [CommRing A] [IsDomain A] [ValuationRing A]
    {K : Type v} [Field K] [Algebra A K] [IsFractionRing A K] :=
  ValuationRing.ValueGroup A K

/-- The canonical valuation on the fraction field. -/
abbrev fractionFieldValuation
    {A : Type u} [CommRing A] [IsDomain A] [ValuationRing A]
    {K : Type v} [Field K] [Algebra A K] [IsFractionRing A K] :=
  ValuationRing.valuation A K

/-- A valuation ring is discrete exactly when its nonzero value group is
ordered-additively isomorphic to the integers. -/
theorem isDiscreteValuationRing_iff_valueGroup_int
    {A : Type u} [CommRing A] [IsDomain A] [ValuationRing A]
    {K : Type v} [Field K] [Algebra A K] [IsFractionRing A K] :
    IsDiscreteValuationRing A ↔
      Nonempty (ValueGroup (A := A) (K := K) ≃+ ℤ) := by
  sorry

/-- For a discrete value group, the order-preserving normalization with the
usual order on the integers is unique. -/
theorem valueGroup_int_orderIso_unique
    {A : Type u} [CommRing A] [IsDomain A] [ValuationRing A]
    {K : Type v} [Field K] [Algebra A K] [IsFractionRing A K]
    [IsDiscreteValuationRing A] :
    Nonempty (ValueGroup (A := A) (K := K) ≃+o ℤ) ∧
      ∀ e₁ e₂ : ValueGroup (A := A) (K := K) ≃+o ℤ, e₁ = e₂ := by
  sorry

/- The source fixes the order-preserving normalization of an isomorphism with
   `ℤ`; the ordered-additive-isomorphism API records that normalization. -/

/-! ## Valuation identities -/

/-- The value of an element of a valuation subring is one exactly when it is a
unit. -/
theorem valuationSubring_eq_one_iff_isUnit
    {K : Type u} [Field K] (A : ValuationSubring K) (a : A) :
    A.valuation a = 1 ↔ IsUnit a :=
  (A.valuation_eq_one_iff a).symm

/-- Multiplicativity of the valuation on a valuation subring. -/
theorem valuationSubring_map_mul
    {K : Type u} [Field K] (A : ValuationSubring K) (a b : A) :
    A.valuation (a * b) = A.valuation a * A.valuation b :=
  A.valuation.map_mul a b

/-- The ultrametric inequality for the valuation on a valuation subring. -/
theorem valuationSubring_map_add_le_max
    {K : Type u} [Field K] (A : ValuationSubring K) (a b : A) :
    A.valuation (a + b) ≤ max (A.valuation a) (A.valuation b) :=
  map_add_le_max A.valuation (a : K) (b : K)

/-- The corresponding abstract fraction-field identity for products. -/
theorem fractionFieldValuation_map_mul
    {A : Type u} [CommRing A] [IsDomain A] [ValuationRing A]
    {K : Type v} [Field K] [Algebra A K] [IsFractionRing A K] (a b : A) :
    fractionFieldValuation (A := A) (K := K) (algebraMap A K (a * b)) =
      fractionFieldValuation (A := A) (K := K) (algebraMap A K a) *
        fractionFieldValuation (A := A) (K := K) (algebraMap A K b) := by
  simp [fractionFieldValuation]

/-- The valuation of a nonzero sum is bounded by the maximum of the two
summands (the multiplicative normalization of the source's minimum inequality). -/
theorem fractionFieldValuation_map_add_le_max
    {A : Type u} [CommRing A] [IsDomain A] [ValuationRing A]
    {K : Type v} [Field K] [Algebra A K] [IsFractionRing A K]
    (a b : A) (hab : a + b ≠ 0) :
    fractionFieldValuation (A := A) (K := K) (algebraMap A K (a + b)) ≤
      max (fractionFieldValuation (A := A) (K := K) (algebraMap A K a))
        (fractionFieldValuation (A := A) (K := K) (algebraMap A K b)) := by
  sorry

/-! ## Constructing valuation rings from ordered valuations -/

/-- A valuation's ring of integers is a valuation ring. -/
theorem valuation_valuationSubring_isValuationRing
    {K : Type u} [Field K] {Γ : Type v}
    [LinearOrderedCommGroupWithZero Γ] (v : Valuation K Γ) :
    ValuationRing v.valuationSubring := by
  infer_instance

/-- The maximal ideal of the valuation ring obtained from `v` consists of the
elements of strictly smaller value than one. -/
theorem valuation_valuationSubring_maximalIdeal_iff
    {K : Type u} [Field K] {Γ : Type v}
    [LinearOrderedCommGroupWithZero Γ] (v : Valuation K Γ)
    {a : v.valuationSubring} :
    a ∈ IsLocalRing.maximalIdeal v.valuationSubring ↔ v a < 1 :=
  Valuation.mem_maximalIdeal_iff (K := K) (Γ := Γ) v

/-- The units of the valuation ring obtained from `v` are exactly the elements
of value one. -/
theorem valuation_valuationSubring_unit_iff
    {K : Type u} [Field K] {Γ : Type v}
    [LinearOrderedCommGroupWithZero Γ] (v : Valuation K Γ) (x : Kˣ) :
    x ∈ v.valuationSubring.unitGroup ↔ v x = 1 :=
  Valuation.mem_unitGroup_iff (K := K) (Γ := Γ) v x

/-! ## Ideals in an ordered value group -/

/-- A value-group ideal is a set of nonnegative elements which is upward
closed. -/
def IsValueGroupIdeal
    {Γ : Type u} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
    (I : Set Γ) : Prop :=
  (∀ γ ∈ I, 0 ≤ γ) ∧
    ∀ γ ∈ I, ∀ γ' : Γ, γ ≤ γ' → γ' ∈ I

/-- The subtype of ideals in an ordered additive value group. -/
def ValueGroupIdeal (Γ : Type u) [AddCommGroup Γ] [LinearOrder Γ]
    [IsOrderedAddMonoid Γ] :=
  {I : Set Γ // IsValueGroupIdeal I}

instance ValueGroupIdeal.instPartialOrder
    (Γ : Type u) [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ] :
    PartialOrder (ValueGroupIdeal Γ) where
  le I J := I.1 ⊆ J.1
  le_refl I := subset_rfl
  le_trans _ _ _ hI J := hI.trans J
  le_antisymm I J hI hJ := Subtype.ext (Set.Subset.antisymm hI hJ)

/-- Primality for a value-group ideal. -/
def IsValueGroupPrimeIdeal
    {Γ : Type u} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
    (I : Set Γ) : Prop :=
  IsValueGroupIdeal I ∧
    0 ∉ I ∧
      ∀ γ γ', 0 ≤ γ → 0 ≤ γ' → γ + γ' ∈ I → γ ∈ I ∨ γ' ∈ I

def ValueGroupIdeal.IsPrime
    {Γ : Type u} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
    (I : ValueGroupIdeal Γ) : Prop :=
  IsValueGroupPrimeIdeal I.1

/-- Ideals of a valuation ring are in inclusion-preserving bijection with
ideals of its additive value group; prime ideals correspond to prime
value-group ideals. -/
theorem ideals_equiv_valueGroupIdeals
    {A : Type u} [CommRing A] [IsDomain A] [ValuationRing A]
    {K : Type v} [Field K] [Algebra A K] [IsFractionRing A K] :
    ∃ e : Ideal A ≃ ValueGroupIdeal (ValueGroup (A := A) (K := K)),
      (∀ I J : Ideal A, I ≤ J ↔ e I ≤ e J) ∧
        (∀ I : Ideal A, I.IsPrime ↔ ValueGroupIdeal.IsPrime (e I)) := by
  sorry

/-! ## Noetherian valuation rings -/

/-- The finitely-generated-principal characterization of valuation rings is
Mathlib's local Bézout-domain equivalence. -/
theorem valuationRing_iff_local_and_fg_ideals_principal
    {A : Type u} [CommRing A] [IsDomain A] :
    ValuationRing A ↔ IsLocalRing A ∧ IsBezout A :=
  ValuationRing.iff_local_bezout_domain

/-- A valuation ring is Noetherian exactly when it is a DVR or a field. -/
theorem valuationRing_isNoetherian_iff_isDiscreteValuationRing_or_isField
    {A : Type u} [CommRing A] [IsDomain A] [ValuationRing A] :
    IsNoetherianRing A ↔ IsDiscreteValuationRing A ∨ IsField A := by
  sorry

end

end Formalization.Books.Algebra.Unit50
