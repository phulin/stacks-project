import Formalization.Books.Algebra.Unit37.NormalRings
import Mathlib.Algebra.Colimit.DirectLimit
import Mathlib.Algebra.Order.GroupWithZero.Range
import Mathlib.Algebra.Order.Group.Units
import Mathlib.Algebra.Order.Monoid.Submonoid
import Mathlib.GroupTheory.ArchimedeanDensely
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Valuation.Discrete.Basic
import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing
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
  let hDomain : IsDomain (DirectLimit A f) := directLimit_isDomain f
  exact @ValuationRing.mk (DirectLimit A f) _ hDomain
    (directLimit_isPreValuationRing f)

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
  refine { toPreValuationRing := ?_ }
  · refine { cond' := ?_ }
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
  let hDomain : IsDomain (Localization S) := IsLocalization.isDomain_localization hS
  exact { toPreValuationRing := localization_preValuationRing S }

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
  have hC : ∀ c : A', c ∈ residueFieldPullback A' A ∨
      ∃ d : residueFieldPullback A' A, (c : A') * d = 1 := by
    intro c
    by_cases hc : IsUnit c
    · let d : A' := (hc.unit⁻¹ : A'ˣ)
      have hd : c * d = 1 := by
        calc
          c * d = (hc.unit : A') * (hc.unit⁻¹ : A'ˣ) := by rw [hc.unit_spec]
          _ = 1 := hc.unit.val_inv
      have hresd : IsLocalRing.residue A' d =
          (IsLocalRing.residue A' c)⁻¹ := by
        apply eq_inv_of_mul_eq_one_left
        rw [← map_mul, mul_comm, hd, map_one]
      obtain h | h := A.mem_or_inv_mem (IsLocalRing.residue A' c)
      · left
        exact h
      · right
        refine ⟨⟨d, ?_⟩, hd⟩
        change IsLocalRing.residue A' d ∈ A.toSubring
        rw [hresd]
        exact h
    · left
      have hzero : IsLocalRing.residue A' c = 0 := by
        rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal,
          mem_nonunits_iff]
        exact hc
      change IsLocalRing.residue A' c ∈ A.toSubring
      rw [hzero]
      exact A.zero_mem
  refine { cond' := ?_ }
  intro x y
  obtain ⟨c, hc | hc⟩ := ValuationRing.cond (x : A') (y : A')
  · obtain h | ⟨d, hd⟩ := hC c
    · exact ⟨⟨c, h⟩, Or.inl (Subtype.ext hc)⟩
    · refine ⟨d, Or.inr ?_⟩
      apply Subtype.ext
      calc
        (y : A') * d = ((x : A') * c) * d := by rw [hc]
        _ = (x : A') * (c * d) := by rw [mul_assoc]
        _ = x := by rw [hd, mul_one]
  · obtain h | ⟨d, hd⟩ := hC c
    · exact ⟨⟨c, h⟩, Or.inr (Subtype.ext hc)⟩
    · refine ⟨d, Or.inl ?_⟩
      apply Subtype.ext
      calc
        (x : A') * d = ((y : A') * c) * d := by rw [hc]
        _ = (y : A') * (c * d) := by rw [mul_assoc]
        _ = y := by rw [hd, mul_one]

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

private theorem nonempty_orderAddEquiv_int
    {G : Type*} [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]
    [hN : Nontrivial G] [hC : IsAddCyclic G] :
    Nonempty (G ≃+o ℤ) :=
  (LinearOrderedAddCommGroup.isAddCyclic_iff_nonempty_equiv_int
    (A := G)).mp hC

private theorem valueGroup_int_of_isDiscreteValuationRing
    {A : Type u} [CommRing A] [IsDomain A] [ValuationRing A]
    {K : Type v} [Field K] [Algebra A K] [IsFractionRing A K]
    [hD : IsDiscreteValuationRing A] :
    Nonempty (ValueGroup (A := A) (K := K) ≃+ ℤ) := by
  let v : Valuation K (ValuationRing.ValueGroup A K) :=
    ValuationRing.valuation A K
  let w := (IsDiscreteValuationRing.maximalIdeal A).valuation K
  have hsub : v.valuationSubring = w.valuationSubring := by
    ext x
    constructor
    · intro hx
      change v x ≤ 1 at hx
      change w x ≤ 1
      obtain ⟨a, ha⟩ := (ValuationRing.mem_integer_iff A K x).mp hx
      rw [← ha]
      exact IsDedekindDomain.HeightOneSpectrum.valuation_le_one
        (IsDiscreteValuationRing.maximalIdeal A) a
    · intro hx
      change w x ≤ 1 at hx
      have hx' : x ∈ w.valuationSubring.toSubring := hx
      rw [← IsDiscreteValuationRing.map_algebraMap_eq_valuationSubring] at hx'
      obtain ⟨a, -, ha⟩ := Subring.mem_map.mp hx'
      change v x ≤ 1
      rw [← ha]
      exact (ValuationRing.mem_integer_iff A K _).mpr ⟨a, rfl⟩
  have hvw : v.IsEquiv w :=
    (Valuation.isEquiv_iff_valuationSubring v w).mpr hsub
  let G := MonoidWithZeroHom.valueGroup (.ofClass v)
  let H := MonoidWithZeroHom.valueGroup (.ofClass w)
  let eg : G ≃* H :=
    ((WithZero.unitsWithZeroEquiv (α := G)).symm.trans
      hvw.orderMonoidIso.unitsCongr.toMulEquiv).trans
      (WithZero.unitsWithZeroEquiv (α := H))
  have hcycH : IsCyclic H := inferInstance
  have hnontrivH : Nontrivial H := by
    rw [Subgroup.nontrivial_iff_exists_ne_one]
    let g := Valuation.IsRankOneDiscrete.generator' w
    exact ⟨(g : H), ⟨g.property, ne_of_lt
      (Valuation.IsRankOneDiscrete.generator'_lt_one w)⟩⟩
  have hcycG : IsCyclic G := eg.isCyclic.mpr hcycH
  have hnontrivG : Nontrivial G := eg.toEquiv.nontrivial
  have hcycDual : IsCyclic (OrderDual G) := by
    rcases hcycG with ⟨g, hg⟩
    exact ⟨g, hg⟩
  have hnontrivDual : Nontrivial (Additive (OrderDual G)) := hnontrivG
  have hAddCyc : IsAddCyclic (Additive (OrderDual G)) :=
    isAddCyclic_additive_iff.mpr hcycDual
  exact ⟨(nonempty_orderAddEquiv_int (G := Additive (OrderDual G))
    (hN := hnontrivDual) (hC := hAddCyc)).some.toAddEquiv⟩

private theorem isDiscreteValuationRing_of_valueGroup_cyclic
    {A : Type u} [CommRing A] [IsDomain A] [ValuationRing A]
    {K : Type v} [Field K] [Algebra A K] [IsFractionRing A K]
    [hC : IsCyclic (MonoidWithZeroHom.valueGroup
      (.ofClass (ValuationRing.valuation A K)))]
    [hN : Nontrivial (MonoidWithZeroHom.valueGroup
      (.ofClass (ValuationRing.valuation A K)))] :
    IsDiscreteValuationRing A := by
  let v := ValuationRing.valuation A K
  have hDvrSub : IsDiscreteValuationRing v.valuationSubring :=
    Valuation.valuationSubring_isDiscreteValuationRing v
  let f : v.integer →+* v.valuationSubring :=
    { toFun := fun x => ⟨x.1, x.2⟩
      map_one' := rfl
      map_mul' := by intros; rfl
      map_zero' := rfl
      map_add' := by intros; rfl }
  have hf : Function.Bijective f := by
    constructor
    · intro x y hxy
      exact Subtype.ext (congrArg Subtype.val hxy)
    · intro y
      exact ⟨⟨y.1, y.2⟩, rfl⟩
  let ef : v.integer ≃+* v.valuationSubring := RingEquiv.ofBijective f hf
  exact @IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing
    v.valuationSubring A (v.valuationSubring ≃+* A) _ _ _ _ hDvrSub _ _
      (ef.symm.trans (ValuationRing.equivInteger A K).symm)

/-- A valuation ring is discrete exactly when its nonzero value group is
ordered-additively isomorphic to the integers. -/
theorem isDiscreteValuationRing_iff_valueGroup_int
    {A : Type u} [CommRing A] [IsDomain A] [ValuationRing A]
    {K : Type v} [Field K] [Algebra A K] [IsFractionRing A K] :
    IsDiscreteValuationRing A ↔
      Nonempty (ValueGroup (A := A) (K := K) ≃+ ℤ) := by
  constructor
  · intro hD
    exact valueGroup_int_of_isDiscreteValuationRing (A := A) (K := K) (hD := hD)
  · rintro ⟨e⟩
    let G := MonoidWithZeroHom.valueGroup
      (ValuationRing.valuation A K).toMonoidWithZeroHom
    have hneValue : Nontrivial (Additive (OrderDual G)) := e.toEquiv.nontrivial
    have hAddCyc : IsAddCyclic (Additive (OrderDual G)) :=
      isAddCyclic_of_surjective e.symm e.symm.surjective
    have hcycDual : IsCyclic (OrderDual G) :=
      isAddCyclic_additive_iff.mp hAddCyc
    have hcycG : IsCyclic G := by
      rcases hcycDual with ⟨g, hg⟩
      exact ⟨g, hg⟩
    have hnontrivG : Nontrivial G := hneValue
    let v := ValuationRing.valuation A K
    have hvhom : (ValuationRing.valuation A K).toMonoidWithZeroHom =
        MonoidWithZeroHom.ofClass v := by
      ext x
      rfl
    have hcycV : IsCyclic (MonoidWithZeroHom.valueGroup (.ofClass v)) := by
      rw [← hvhom]
      exact hcycG
    have hnontrivV : Nontrivial (MonoidWithZeroHom.valueGroup (.ofClass v)) := by
      rw [← hvhom]
      exact hnontrivG
    exact isDiscreteValuationRing_of_valueGroup_cyclic (A := A) (K := K)
      (hC := hcycV) (hN := hnontrivV)

/-- For a discrete value group, the order-preserving normalization with the
usual order on the integers is unique. -/
theorem valueGroup_int_orderIso_unique
    {A : Type u} [CommRing A] [IsDomain A] [ValuationRing A]
    {K : Type v} [Field K] [Algebra A K] [IsFractionRing A K]
    [IsDiscreteValuationRing A] :
    Nonempty (ValueGroup (A := A) (K := K) ≃+o ℤ) ∧
      ∀ e₁ e₂ : ValueGroup (A := A) (K := K) ≃+o ℤ, e₁ = e₂ := by
  constructor
  · let e : ValueGroup (A := A) (K := K) ≃+ ℤ :=
      ((isDiscreteValuationRing_iff_valueGroup_int (A := A) (K := K)).mp
        (inferInstance : IsDiscreteValuationRing A)).some
    have hnontriv : Nontrivial (ValueGroup (A := A) (K := K)) := e.toEquiv.nontrivial
    have hAddCyc : IsAddCyclic (ValueGroup (A := A) (K := K)) := by
      exact isAddCyclic_of_surjective e.symm e.symm.surjective
    exact ⟨(nonempty_orderAddEquiv_int (G := ValueGroup (A := A) (K := K))
      (hN := hnontriv) (hC := hAddCyc)).some⟩
  · intro h e₂
    have hf : h.symm.trans e₂ = OrderAddMonoidIso.refl ℤ :=
      Subsingleton.elim _ _
    have hcomp := congrArg (fun e : ℤ ≃+o ℤ => h.trans e) hf
    calc
      h = h.trans (h.symm.trans e₂) := hcomp.symm
      _ = e₂ := by
        ext x
        simp

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
  have _ := hab
  simpa only [map_add] using
    (map_add_le_max (ValuationRing.valuation A K) (algebraMap A K a)
      (algebraMap A K b))

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
  let H := MonoidWithZeroHom.valueGroup
    ((ValuationRing.valuation A K).toMonoidWithZeroHom)
  let toValue : ValueGroup (A := A) (K := K) → ValueGroupWithZero (A := A) (K := K) :=
    fun γ => (((OrderDual.ofDual γ.toMul : H) :
      (ValueGroupWithZero (A := A) (K := K))ˣ))
  let val : {x : A // x ≠ 0} → ValueGroup (A := A) (K := K) := fun x =>
    Additive.ofMul (OrderDual.toDual
      (⟨Units.mk0 ((ValuationRing.valuation A K) (algebraMap A K x.1)) (by
          rw [(ValuationRing.valuation A K).ne_zero_iff]
          exact IsFractionRing.to_map_eq_zero_iff.not.mpr x.2),
        MonoidWithZeroHom.mem_valueGroup
          ((ValuationRing.valuation A K).toMonoidWithZeroHom) ⟨algebraMap A K x.1, rfl⟩⟩))
  let hv : (ValuationRing.valuation A K).Integers A :=
    { hom_inj := IsFractionRing.injective A K
      map_le_one := fun x => by
        change (ValuationRing.valuation A K) (algebraMap A K x) ≤ 1
        exact (ValuationRing.mem_integer_iff A K (algebraMap A K x)).mpr ⟨x, rfl⟩
      exists_of_le_one := fun {r} h => by
        apply (ValuationRing.mem_integer_iff A K r).mp
        exact h }
  have htoValue_nonneg {γ : ValueGroup (A := A) (K := K)} (hγ : 0 ≤ γ) :
      toValue γ ≤ 1 := by
    change (((OrderDual.ofDual γ.toMul : H) :
        (ValueGroupWithZero (A := A) (K := K))ˣ)) ≤ 1
    change (OrderDual.ofDual γ.toMul : H) ≤ 1 at hγ
    exact hγ
  have htoValue_le {γ δ : ValueGroup (A := A) (K := K)} (hγδ : γ ≤ δ) :
      toValue δ ≤ toValue γ := by
    change (((OrderDual.ofDual δ.toMul : H) :
        (ValueGroupWithZero (A := A) (K := K))ˣ)) ≤
      (((OrderDual.ofDual γ.toMul : H) :
        (ValueGroupWithZero (A := A) (K := K))ˣ))
    change (OrderDual.ofDual δ.toMul : H) ≤
        (OrderDual.ofDual γ.toMul : H) at hγδ
    exact hγδ
  have htoValue_val {x : A} (hx : x ≠ 0) :
      toValue (val ⟨x, hx⟩) =
        (ValuationRing.valuation A K) (algebraMap A K x) := by
    rfl
  have hval_le {x y : A} (hx : x ≠ 0) (hy : y ≠ 0) :
      val ⟨x, hx⟩ ≤ val ⟨y, hy⟩ ↔ x ∣ y := by
    change
      (ValuationRing.valuation A K) (algebraMap A K y) ≤
        (ValuationRing.valuation A K) (algebraMap A K x) ↔ x ∣ y
    exact (Valuation.Integers.dvd_iff_le hv (x := x) (y := y)).symm
  have hval_zero {x : A} (hx : x ≠ 0) :
      val ⟨x, hx⟩ = 0 ↔ IsUnit x := by
    change
      (⟨Units.mk0 ((ValuationRing.valuation A K) (algebraMap A K x)) (by
          rw [(ValuationRing.valuation A K).ne_zero_iff]
          exact IsFractionRing.to_map_eq_zero_iff.not.mpr hx),
        MonoidWithZeroHom.mem_valueGroup
          ((ValuationRing.valuation A K).toMonoidWithZeroHom) ⟨algebraMap A K x, rfl⟩⟩ :
        MonoidWithZeroHom.valueGroup ((ValuationRing.valuation A K).toMonoidWithZeroHom)) = 1 ↔
      IsUnit x
    constructor
    · intro h
      have h' := congrArg Units.val (congrArg Subtype.val h)
      have hvx : (ValuationRing.valuation A K) (algebraMap A K x) = 1 := by
        simpa using h'
      exact hv.isUnit_iff_valuation_eq_one.mpr hvx
    · intro h
      apply Subtype.ext
      apply Units.ext
      exact hv.isUnit_iff_valuation_eq_one.mp h
  have hval_mul {x y : A} (hx : x ≠ 0) (hy : y ≠ 0) :
      val ⟨x * y, mul_ne_zero hx hy⟩ = val ⟨x, hx⟩ + val ⟨y, hy⟩ := by
    apply Additive.ofMul.injective
    apply OrderDual.toDual.injective
    apply Subtype.ext
    ext
    change
      (ValuationRing.valuation A K) (algebraMap A K (x * y)) =
        (ValuationRing.valuation A K) (algebraMap A K x) *
          (ValuationRing.valuation A K) (algebraMap A K y)
    rw [(algebraMap A K).map_mul, (ValuationRing.valuation A K).map_mul]
  have hval_le_general' {x : A} (hx : x ≠ 0)
      {γ : ValueGroup (A := A) (K := K)} :
      γ ≤ val ⟨x, hx⟩ ↔
        (ValuationRing.valuation A K) (algebraMap A K x) ≤
          toValue γ := by
    change
      (OrderDual.ofDual (val ⟨x, hx⟩).toMul : H) ≤
        (OrderDual.ofDual γ.toMul : H) ↔
      (ValuationRing.valuation A K) (algebraMap A K x) ≤ toValue γ
    change
      (OrderDual.ofDual (val ⟨x, hx⟩).toMul : H) ≤
        (OrderDual.ofDual γ.toMul : H) ↔
      (Units.mk0 ((ValuationRing.valuation A K) (algebraMap A K x)) (by
          rw [(ValuationRing.valuation A K).ne_zero_iff]
          exact IsFractionRing.to_map_eq_zero_iff.not.mpr hx)) ≤
        (((OrderDual.ofDual γ.toMul : H) :
          (ValueGroupWithZero (A := A) (K := K))ˣ))
    rw [← Units.val_le_val]
    rfl
  have hexists {γ : ValueGroup (A := A) (K := K)} (hγ : 0 ≤ γ) :
      ∃ x : A, x ≠ 0 ∧ ∃ hx : x ≠ 0, val ⟨x, hx⟩ = γ := by
    obtain ⟨z, hz⟩ : ∃ z : K, (ValuationRing.valuation A K) z = toValue γ := by
      change ∃ z : K, Quotient.mk'' z = toValue γ
      exact Quotient.mk_surjective _
    have hz0 : z ≠ 0 := by
      intro hzero
      subst z
      have htv0 : toValue γ ≠ 0 := by
        change (((OrderDual.ofDual γ.toMul : H) :
          (ValueGroupWithZero (A := A) (K := K))ˣ) :
            ValueGroupWithZero (A := A) (K := K)) ≠ 0
        exact Units.ne_zero
          ((OrderDual.ofDual γ.toMul : H) :
            (ValueGroupWithZero (A := A) (K := K))ˣ)
      exact htv0 (by simpa using hz)
    obtain ⟨x, hx⟩ := hv.exists_of_le_one (by
      rw [hz]
      exact htoValue_nonneg hγ)
    have hx0 : x ≠ 0 := by
      intro hzero
      apply hz0
      rw [← hx, hzero, map_zero]
    refine ⟨x, hx0, hx0, ?_⟩
    apply Additive.toMul.injective
    apply OrderDual.toDual.injective
    apply Subtype.ext
    apply Units.ext
    change (ValuationRing.valuation A K) (algebraMap A K x) = toValue γ
    rw [hx, hz]
  let cutIdeal : ValueGroup (A := A) (K := K) → Ideal A := fun γ =>
    { carrier := {x | (ValuationRing.valuation A K) (algebraMap A K x) ≤ toValue γ}
      zero_mem' := by simp
      add_mem' := by
        intro x y hx hy
        change (ValuationRing.valuation A K) (algebraMap A K (x + y)) ≤ toValue γ
        rw [(algebraMap A K).map_add]
        exact ((ValuationRing.valuation A K).map_add _ _).trans (max_le hx hy)
      smul_mem' := by
        intro r x hx
        change (ValuationRing.valuation A K) (algebraMap A K (r * x)) ≤ toValue γ
        rw [(algebraMap A K).map_mul, (ValuationRing.valuation A K).map_mul]
        exact mul_le_of_le_one_of_le
          ((ValuationRing.mem_integer_iff A K (algebraMap A K r)).mpr ⟨r, rfl⟩) hx }
  have hcut_mono {γ δ : ValueGroup (A := A) (K := K)} (hγδ : γ ≤ δ) :
      cutIdeal δ ≤ cutIdeal γ := by
    intro x hx
    change (ValuationRing.valuation A K) (algebraMap A K x) ≤ toValue δ at hx
    change (ValuationRing.valuation A K) (algebraMap A K x) ≤ toValue γ
    exact hx.trans (htoValue_le hγδ)
  have hcut_mem_of_mem (I : Ideal A) {x : A} (hx0 : x ≠ 0) (hxI : x ∈ I) :
      cutIdeal (val ⟨x, hx0⟩) ≤ I := by
    intro y hy
    by_cases hy0 : y = 0
    · subst y
      exact I.zero_mem
    · change (ValuationRing.valuation A K) (algebraMap A K y) ≤
        toValue (val ⟨x, hx0⟩) at hy
      rw [htoValue_val hx0] at hy
      exact I.mem_of_dvd (hv.dvd_of_le hy) hxI
  have hval_nonneg {x : A} (hx0 : x ≠ 0) :
      0 ≤ val ⟨x, hx0⟩ := by
    have hone : val ⟨(1 : A), one_ne_zero⟩ = 0 :=
      (hval_zero one_ne_zero).mpr isUnit_one
    rw [← hone]
    exact (hval_le one_ne_zero hx0).mpr (one_dvd x)
  let eFun : Ideal A → ValueGroupIdeal (ValueGroup (A := A) (K := K)) := fun I =>
    ⟨{γ | 0 ≤ γ ∧ cutIdeal γ ≤ I}, by
      constructor
      · intro γ hγ
        change 0 ≤ γ ∧ cutIdeal γ ≤ I at hγ
        exact hγ.1
      · intro γ hγ δ hδ
        change 0 ≤ γ ∧ cutIdeal γ ≤ I at hγ
        change 0 ≤ δ ∧ cutIdeal δ ≤ I
        exact ⟨hγ.1.trans hδ, fun x hx => hx.trans (htoValue_le hδ)⟩⟩
  let invFun : ValueGroupIdeal (ValueGroup (A := A) (K := K)) → Ideal A := fun S =>
    { carrier := {x | x = 0 ∨ ∃ γ, γ ∈ S.1 ∧ x ∈ cutIdeal γ}
      zero_mem' := Or.inl rfl
      add_mem' := by
        intro x y hx hy
        rcases hx with rfl | ⟨γ, hγ, hx⟩
        · simpa using hy
        rcases hy with rfl | ⟨δ, hδ, hy⟩
        · simpa using hx
        rcases le_total γ δ with hγδ | hδγ
        · exact Or.inr ⟨γ, hγ, (cutIdeal γ).add_mem hx ((hcut_mono hγδ) hy)⟩
        · exact Or.inr ⟨δ, hδ, (cutIdeal δ).add_mem ((hcut_mono hδγ) hx) hy⟩
      smul_mem' := by
        intro r x hx
        rcases hx with rfl | ⟨γ, hγ, hx⟩
        · exact Or.inl (mul_zero r)
        · exact Or.inr ⟨γ, hγ, (cutIdeal γ).smul_mem r hx⟩ }
  have heFun_order (I J : Ideal A) : I ≤ J ↔ eFun I ≤ eFun J := by
    constructor
    · intro hIJ γ hγ
      change 0 ≤ γ ∧ cutIdeal γ ≤ I at hγ
      exact ⟨hγ.1, hγ.2.trans hIJ⟩
    · intro hIJ x hx
      by_cases hx0 : x = 0
      · subst x
        exact J.zero_mem
      · have hγI : val ⟨x, hx0⟩ ∈ (eFun I).1 :=
          ⟨hval_nonneg hx0, hcut_mem_of_mem I hx0 hx⟩
        have hγJ := hIJ hγI
        change 0 ≤ val ⟨x, hx0⟩ ∧ cutIdeal (val ⟨x, hx0⟩) ≤ J at hγJ
        exact hγJ.2 (by
          change (ValuationRing.valuation A K) (algebraMap A K x) ≤
            toValue (val ⟨x, hx0⟩)
          rw [htoValue_val hx0])
  have hinv_eFun (S : ValueGroupIdeal (ValueGroup (A := A) (K := K))) :
      eFun (invFun S) = S := by
    apply Subtype.ext
    ext γ
    change (0 ≤ γ ∧ cutIdeal γ ≤ invFun S) ↔ γ ∈ S.1
    constructor
    · intro hγ
      obtain ⟨x, hx0, hxval⟩ := hexists hγ.1
      have hxcut : x ∈ cutIdeal γ := by
        change (ValuationRing.valuation A K) (algebraMap A K x) ≤ toValue γ
        rw [← hxval, htoValue_val hx0]
      have hxinv := hγ.2 hxcut
      change x = 0 ∨ ∃ δ, δ ∈ S.1 ∧ x ∈ cutIdeal δ at hxinv
      rcases hxinv with hxzero | ⟨δ, hδ, hxδ⟩
      · exact (hx0 hxzero).elim
      · apply S.2.2 δ hδ γ
        exact (hval_le_general' hx0).mp hxδ |>.trans_eq hxval.symm
    · intro hγ
      refine ⟨S.2.1 γ hγ, ?_⟩
      intro x hx
      exact Or.inr ⟨γ, hγ, hx⟩
  have heFun_invFun (I : Ideal A) : invFun (eFun I) = I := by
    ext x
    change (x = 0 ∨ ∃ γ, γ ∈ (eFun I).1 ∧ x ∈ cutIdeal γ) ↔ x ∈ I
    constructor
    · intro hx
      rcases hx with hxzero | ⟨γ, hγ, hxcut⟩
      · simpa [hxzero] using I.zero_mem
      · exact hγ.2 hxcut
    · intro hx
      by_cases hx0 : x = 0
      · exact Or.inl hx0
        · refine Or.inr ⟨val ⟨x, hx0⟩, ?_, ?_⟩
        · exact ⟨hval_nonneg hx0, hcut_mem_of_mem I hx0 hx⟩
        · change (ValuationRing.valuation A K) (algebraMap A K x) ≤
            toValue (val ⟨x, hx0⟩)
          rw [htoValue_val hx0]
  let e : Ideal A ≃ ValueGroupIdeal (ValueGroup (A := A) (K := K)) :=
    { toFun := eFun
      invFun := invFun
      left_inv := heFun_invFun
      right_inv := hinv_eFun }
  refine ⟨e, ?_, ?_⟩
  · intro I J
    exact heFun_order I J
  · intro I
    constructor
    · intro hI
      change IsValueGroupPrimeIdeal (eFun I).1
      constructor
      · exact (eFun I).2
      constructor
      · intro hzero
        apply hI.ne_top
        apply Ideal.eq_top_iff_one.mpr
        exact hzero.2 (by
          change (ValuationRing.valuation A K) (algebraMap A K (1 : A)) ≤ toValue 0
          change (ValuationRing.valuation A K) (algebraMap A K (1 : A)) ≤ 1
          simp)
      · intro γ δ hγ hδ hsum
        obtain ⟨x, hx0, hxval⟩ := hexists hγ
        obtain ⟨y, hy0, hyval⟩ := hexists hδ
        have hxycut : x * y ∈ cutIdeal (γ + δ) := by
          change (ValuationRing.valuation A K) (algebraMap A K (x * y)) ≤ toValue (γ + δ)
          rw [← htoValue_val (mul_ne_zero hx0 hy0), hval_mul hx0 hy0, hxval, hyval]
        have hxyI := hsum.2 hxycut
        rcases hI.2 hxyI with hxI | hyI
        · exact Or.inl ⟨hγ, hcut_mem_of_mem I hx0 hxI⟩
        · exact Or.inr ⟨hδ, hcut_mem_of_mem I hy0 hyI⟩
    · intro hS
      change I.IsPrime
      refine ⟨?_, ?_⟩
      · intro htop
        apply hS.2.1
        rw [htop]
        exact ⟨zero_le, le_top⟩
      · intro x y hxy
        by_cases hx0 : x = 0
        · exact Or.inl hx0
        by_cases hy0 : y = 0
        · exact Or.inr hy0
        have hsum : val ⟨x, hx0⟩ + val ⟨y, hy0⟩ ∈ eFun I := by
          refine ⟨add_nonneg (hval_nonneg hx0) (hval_nonneg hy0), ?_⟩
          simpa [hval_mul hx0 hy0] using
            (hcut_mem_of_mem I (mul_ne_zero hx0 hy0) hxy)
        rcases hS.2.2 (val ⟨x, hx0⟩) (val ⟨y, hy0⟩)
          (hval_nonneg hx0) (hval_nonneg hy0) hsum with hγ | hδ
        · left
          exact hγ.2 (by
            change (ValuationRing.valuation A K) (algebraMap A K x) ≤
              toValue (val ⟨x, hx0⟩)
            rw [htoValue_val hx0])
        · right
          exact hδ.2 (by
            change (ValuationRing.valuation A K) (algebraMap A K y) ≤
              toValue (val ⟨y, hy0⟩)
            rw [htoValue_val hy0])

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
  constructor
  · intro hN
    by_cases hF : IsField A
    · exact Or.inr hF
    · letI : IsNoetherianRing A := hN
      exact Or.inl (((IsDiscreteValuationRing.TFAE A hF).out 1 0).mp
        (inferInstance : ValuationRing A))
  · rintro (hD | hF)
    · letI : IsDiscreteValuationRing A := hD
      infer_instance
    · letI : IsField A := hF
      letI := hF.toField
      infer_instance

end

end Formalization.Books.Algebra.Unit50
