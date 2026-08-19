import Mathlib.Algebra.Field.Subfield.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Algebra.ZMod
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.MvPolynomial.Expand
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.FieldTheory.Perfect
import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.MvPowerSeries.Expand
import Mathlib.RingTheory.MvPowerSeries.NoZeroDivisors

/-!
# More Algebra, Chapter 46: Field extensions, revisited

This chapter records the source's characteristic-`p` results on `p`-bases,
intersections of subfields, and the power-series example.  The p-power
compositum is represented by `IntermediateField.adjoin`; Kähler differentials
and ordinary `Module.Basis` are used for the differential formulation.
-/

namespace Formalization.Books.MoreAlgebra.Unit46

open Set
open scoped BigOperators

noncomputable section

universe u v w

/-! ## p-bases -/

/-- The compositum of `k` and the subfield of `p`-th powers in `K`.

The ambient field `K` is used as the source's common overfield, while the
resulting intermediate field is the scalar field for the p-monomials.
-/
def pPowerCompositum
    (p : ℕ) (k : Type u) (K : Type v) [Field k] [Field K] [Algebra k K] :
    IntermediateField k K :=
  IntermediateField.adjoin k (Set.range (fun x : K => x ^ p))

/-- The p-monomial belonging to a finitely supported exponent function.

Using finitely supported natural exponents bounded by `p` makes the source's
multi-index notation precise even when
the p-independent collection is infinite.
-/
def PExponent (p : ℕ) (s : Set K) :=
  {e : s →₀ ℕ // ∀ x, e x < p}

def pMonomial
    (p : ℕ) {K : Type u} [Field K] (s : Set K) (e : PExponent p s) : K :=
  e.1.support.prod (fun x => (x : K) ^ e.1 x)

/-- A collection is p-independent over `k` when its p-monomials are linearly
independent over the compositum `kK^p`.
-/
def PIndependent
  (p : ℕ) {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]
    (s : Set K) : Prop :=
  LinearIndependent (pPowerCompositum p k K)
    (fun e : PExponent p s => pMonomial p s e)

/-- A chosen p-basis is represented by a `Module.Basis` whose vectors are the
source's p-monomials.
-/
def PBasis
  (p : ℕ) {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]
    (s : Set K) : Prop :=
  ∃ b : Module.Basis (PExponent p s) (pPowerCompositum p k K) K,
    ∀ e, b e = pMonomial p s e

/-- The source's assertion that a subspace contains a nonzero vector whose
coordinates lie in an intermediate field.
-/
def HasNonzeroVectorOver
    {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]
    (n : ℕ) (V : Submodule K (Fin n → K))
    (L : IntermediateField k K) : Prop :=
  ∃ x, x ≠ 0 ∧ x ∈ V ∧ ∀ i, x i ∈ L

/-- The p-basis definition from the source. -/
theorem pBasis_definition
    (p : ℕ) {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]
    (s : Set K) :
    PIndependent (k := k) (K := K) p s ↔
      LinearIndependent (pPowerCompositum p k K)
        (fun e : PExponent p s => pMonomial p s e) := by
  rfl

/-- p-independence is equivalent to linear independence of the differentials. -/
theorem pIndependent_iff_differential_linearIndependent
    (p : ℕ) (hp : p.Prime) {k : Type u} {K : Type v}
    [Field k] [Field K] [Algebra k K] [CharP k p]
    (s : Set K) :
    PIndependent (k := k) (K := K) p s ↔
      LinearIndependent K (fun x : s => KaehlerDifferential.D k K (x : K)) := by
  sorry

/-- Every p-independent collection extends to a p-basis. -/
theorem exists_pBasis_superset
    (p : ℕ) (hp : p.Prime) {k : Type u} {K : Type v}
    [Field k] [Field K] [Algebra k K] [CharP k p]
    {s : Set K} (hs : PIndependent (k := k) (K := K) p s) :
    ∃ t : Set K, s ⊆ t ∧ PBasis (k := k) (K := K) p t := by
  sorry

/-- Every field extension in characteristic `p` has a p-basis. -/
theorem exists_pBasis
    (p : ℕ) (hp : p.Prime) {k : Type u} {K : Type v}
    [Field k] [Field K] [Algebra k K] [CharP k p] :
    ∃ s : Set K, PBasis (k := k) (K := K) p s := by
  sorry

/-- A collection is a p-basis exactly when its differentials form a basis. -/
theorem pBasis_iff_differential_basis
    (p : ℕ) (hp : p.Prime) {k : Type u} {K : Type v}
    [Field k] [Field K] [Algebra k K] [CharP k p]
    (s : Set K) :
    PBasis (k := k) (K := K) p s ↔
      ∃ b : Module.Basis s K (KaehlerDifferential k K),
        ∀ x, b x = KaehlerDifferential.D k K (x : K) := by
  sorry

/-! ## Intersections of subfields -/

/-- The vector-space intersection criterion for a directed family of
intermediate fields.

The bottom intermediate field is the embedded copy of `k`, so the equality
`⋂ Kα = k` is written in Mathlib's lattice language as `iInf Kα = ⊥`.
-/
theorem vectorSubspace_intersection_iff
    {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]
    (A : Type w) (Kα : A → IntermediateField k K)
    (hinter : ⨅ α, Kα α = ⊥)
    (hdirected : ∀ α α', ∃ α'', Kα α'' ≤ Kα α ⊓ Kα α')
    (n : ℕ) (hn : 1 ≤ n) (V : Submodule K (Fin n → K)) :
    HasNonzeroVectorOver (k := k) (K := K) n V ⊥ ↔
      ∀ α, HasNonzeroVectorOver (k := k) (K := K) n V (Kα α) := by
  sorry

/-! ## p-power intersections -/

/-- The subfield of `p`-th powers, represented by the range of Frobenius. -/
def pthPowerSubfield
    (p : ℕ) (hp : p.Prime) (K : Type u) [Field K] [CharP K p] : Subfield K :=
  letI : Fact p.Prime := ⟨hp⟩
  (frobenius K p).fieldRange

/-- The compositum of the p-th powers of `L` with a subfield of `K`. -/
def pthPowerCompositum
    (p : ℕ) (hp : p.Prime) {K : Type u} {L : Type v} [Field K] [Field L]
    [Algebra K L] [CharP L p] (S : Subfield K) : Subfield L :=
  pthPowerSubfield p hp L ⊔ S.map (algebraMap K L)

/-- The base-change map from differentials over `𝔽ₚ` to differentials over an
intermediate subfield. -/
noncomputable def pDifferentialBaseChange
    (p : ℕ) [Fact p.Prime] {K : Type u} [Field K] [Algebra (ZMod p) K]
    (S : IntermediateField (ZMod p) K) :
    KaehlerDifferential (ZMod p) K →ₗ[K] KaehlerDifferential S K :=
  KaehlerDifferential.map (ZMod p) S K K

/-- Under the intersection hypotheses, the kernels of the differential maps
have zero intersection. -/
theorem pPowerSubfields_differential_ker_iInf
    (p : ℕ) (hp : p.Prime) [Fact p.Prime] {K : Type u} [Field K] [CharP K p]
    [Algebra (ZMod p) K]
    (A : Type v) (Kα : A → IntermediateField (ZMod p) K)
    (hcontains : ∀ α, pthPowerSubfield p hp K ≤ (Kα α).toSubfield)
    (hinter : ⨅ α, (Kα α).toSubfield = pthPowerSubfield p hp K)
    (hdirected : ∀ α α', ∃ α'', Kα α'' ≤ Kα α ⊓ Kα α') :
    ∀ η : KaehlerDifferential (ZMod p) K,
      (∀ α, pDifferentialBaseChange p (Kα α) η = 0) → η = 0 := by
  sorry

/-- The p-power intersection formula remains true after any finite field
extension. -/
theorem pPowerSubfields_finiteExtension_iInf
    (p : ℕ) (hp : p.Prime) [Fact p.Prime] {K : Type u} [Field K] [CharP K p]
    [Algebra (ZMod p) K]
    (A : Type v) (Kα : A → IntermediateField (ZMod p) K)
    (hcontains : ∀ α, pthPowerSubfield p hp K ≤ (Kα α).toSubfield)
    (hinter : ⨅ α, (Kα α).toSubfield = pthPowerSubfield p hp K)
    (hdirected : ∀ α α', ∃ α'', Kα α'' ≤ Kα α ⊓ Kα α')
    {L : Type w} [Field L] [Algebra K L] [FiniteDimensional K L] :
    letI : CharP L p := charP_of_injective_algebraMap (algebraMap K L).injective p
    pthPowerSubfield p hp L =
      ⨅ α, pthPowerCompositum p hp (S := (Kα α).toSubfield) (L := L) := by
  sorry

/-! ## The power-series example -/

/-- The ring `k[[x₁, ..., xₙ]][y₁, ..., yₘ]` in the source. -/
abbrev powerSeriesPolynomialRing (k : Type u) [Field k] (n m : ℕ) :=
  MvPolynomial (Fin m) (MvPowerSeries (Fin n) k)

/-- Its fraction field. -/
abbrev powerSeriesFractionField (k : Type u) [Field k] (n m : ℕ) :=
  FractionRing (powerSeriesPolynomialRing k n m)

/-- The coefficient field `k_J`, generated by `k^p` and p-basis elements
outside the finite subset `J`. -/
def powerSeriesCoefficientField
    (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [Algebra (ZMod p) k]
    (s : Set k) (J : Finset s) : IntermediateField (ZMod p) k :=
  IntermediateField.adjoin (ZMod p)
    (Set.range (fun x : k => x ^ p) ∪
      Set.range (fun x : {x : s // x ∉ (J : Set s)} => (x.1 : k)))

/-- The ring `A_J = k_J[[x₁^p, ..., xₙ^p]][y₁^p, ..., yₘ^p]`, represented
by the corresponding polynomial ring over multivariate power series. -/
abbrev powerSeriesSubfieldRing
    (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [Algebra (ZMod p) k]
    (n m : ℕ) (s : Set k) (J : Finset s) :=
  MvPolynomial (Fin m)
    (MvPowerSeries (Fin n) (powerSeriesCoefficientField p k s J))

/-- The canonical embedding of `A_J` into `A`: coefficient maps are followed
by power-series expansion, and the polynomial variables are expanded as well.
-/
noncomputable def powerSeriesSubfieldToAmbient
    (p : ℕ) (hp : p.Prime) [Fact p.Prime]
    (k : Type u) [Field k] [Algebra (ZMod p) k]
    (n m : ℕ) (s : Set k) (J : Finset s) :
    powerSeriesSubfieldRing p k n m s J →+*
      powerSeriesPolynomialRing k n m :=
  (MvPolynomial.expand p).toRingHom.comp
    (MvPolynomial.map
      ((MvPowerSeries.expand p hp.ne_zero).toRingHom.comp
        (MvPowerSeries.map
          (powerSeriesCoefficientField p k s J).val.toRingHom)))

/-- A ring map is finite when its target is a finite module over the source
through the displayed map. -/
def IsFiniteRingExtension
    (R S : Type*) [CommRing R] [CommRing S] (f : R →+* S) : Prop :=
  letI : Algebra R S := f.toAlgebra
  Module.Finite R S

/-- A precise interface for the fraction fields `K_J ⊂ K` in the source.

The ring maps and fraction-field equivalences are fields of the interface so
that the theorem below records both the subfield realization and the finite
ring extensions without introducing a second, noncanonical notion of
fraction field.
-/
structure PowerSeriesSubfieldFamily
    (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [Algebra (ZMod p) k]
    (n m : ℕ) (s : Set k) where
  subfield : Finset s → Subfield (powerSeriesFractionField k n m)
  toSubfield : ∀ J,
    powerSeriesSubfieldRing p k n m s J →+* (subfield J)
  fractionFieldEquiv : ∀ J,
    FractionRing (powerSeriesSubfieldRing p k n m s J) ≃+* (subfield J)
  fractionField_commutes : ∀ J x,
    fractionFieldEquiv J (algebraMap
      (powerSeriesSubfieldRing p k n m s J)
      (FractionRing (powerSeriesSubfieldRing p k n m s J)) x) =
      toSubfield J x
  ambient_commutes : ∀ J x,
    algebraMap (powerSeriesPolynomialRing k n m)
        (powerSeriesFractionField k n m)
        (powerSeriesSubfieldToAmbient p Fact.out k n m s J x) =
      algebraMap (subfield J) (powerSeriesFractionField k n m) (toSubfield J x)
  isFinite : ∀ J,
    IsFiniteRingExtension
      (powerSeriesSubfieldRing p k n m s J)
      (powerSeriesPolynomialRing k n m)
      (powerSeriesSubfieldToAmbient p Fact.out k n m s J)

/-- The power-series subfields satisfy the intersection and directedness
properties of the preceding p-power lemma, and every `A_J ⊂ A` is finite. -/
theorem exists_powerSeriesSubfieldFamily
    (p : ℕ) (hp : p.Prime) [Fact p.Prime] (k : Type u) [Field k] [CharP k p]
    [Algebra (ZMod p) k]
    (n m : ℕ) (s : Set k)
    (hs : PBasis (k := ZMod p) (K := k) p s) :
    let f : k →+* powerSeriesPolynomialRing k n m :=
      (MvPolynomial.C :
        MvPowerSeries (Fin n) k →+* powerSeriesPolynomialRing k n m).comp
        (algebraMap k (MvPowerSeries (Fin n) k))
    letI : CharP (MvPowerSeries (Fin n) k) p :=
      charP_of_injective_algebraMap
        (algebraMap k (MvPowerSeries (Fin n) k)).injective p
    let hf : Function.Injective f := by
      intro x y hxy
      apply (algebraMap k (MvPowerSeries (Fin n) k)).injective
      exact (MvPolynomial.C_injective (Fin m) (MvPowerSeries (Fin n) k)) hxy
    letI : CharP (powerSeriesPolynomialRing k n m) p :=
      charP_of_injective_ringHom hf p
    letI : CharP (powerSeriesFractionField k n m) p :=
      IsFractionRing.charP_of_isFractionRing (powerSeriesPolynomialRing k n m) p
    ∃ F : PowerSeriesSubfieldFamily p k n m s,
      (⨅ J, (F.subfield J : Subfield (powerSeriesFractionField k n m))) =
          pthPowerSubfield p hp (powerSeriesFractionField k n m) ∧
      (∀ J, pthPowerSubfield p hp (powerSeriesFractionField k n m) ≤ F.subfield J) ∧
      (∀ J J', ∃ J'', F.subfield J'' ≤ F.subfield J ⊓ F.subfield J') := by
  sorry

end

end Formalization.Books.MoreAlgebra.Unit46
