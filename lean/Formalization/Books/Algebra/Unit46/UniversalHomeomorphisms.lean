import Formalization.Books.Algebra.Unit03.BasicNotions
import Formalization.Books.Algebra.Unit14.BaseChange
import Formalization.Books.Algebra.Unit30.MoreOnImages
import Formalization.Books.Algebra.Unit36.FiniteIntegralRingExtensions
import Mathlib.Algebra.Algebra.ZMod
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Data.Nat.Choose.Factorization
import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.FieldTheory.PurelyInseparable.PerfectClosure
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.Perfect
import Mathlib.NumberTheory.NumberField.Units.Basic
import Mathlib.RingTheory.Adjoin.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Mathlib.RingTheory.Spectrum.Prime.Homeomorph
import Mathlib.RingTheory.Spectrum.Prime.RingHom
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.TensorProduct.Nontrivial
import Mathlib.Topology.Maps.Basic

/-!
# Commutative Algebra, Chapter 46: Universal homeomorphisms

The source's ring-map conditions are expressed using Mathlib's canonical
`PrimeSpectrum.comap`, `RingHom.IsIntegral`, tensor-product maps, residue
fields, and `IsPurelyInseparable`.  The elementwise locally nilpotent-kernel
condition reuses Chapter 3's `locallyNilpotentIdeal`.
-/

namespace Formalization.Books.Algebra.Unit46

open Set
open _root_.Topology
open scoped TensorProduct
open Formalization.Books.Algebra.Unit14

universe u v w

noncomputable section

/-! ## Source-facing predicates and maps -/

/- The source's locally nilpotent kernel is exactly the earlier chapter's
   elementwise locally nilpotent ideal predicate applied to `RingHom.ker`. -/
/-- The kernel of a ring map is locally nilpotent elementwise. -/
def locallyNilpotentKernel {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) : Prop :=
  Formalization.Books.Algebra.Unit03.locallyNilpotentIdeal (RingHom.ker f)

/- The source repeatedly says that a ring is generated as an algebra by a
   specified set.  `Algebra.adjoin` is the canonical construction; the
   algebra structure here is the one induced by the ring map. -/
/-- The target is generated over the source by a set of elements. -/
def generatedBy {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (s : Set S) : Prop :=
  letI : Algebra R S := f.toAlgebra
  Algebra.adjoin R s = ⊤

/-- Every target element has a positive power in the image of a ring map. -/
def powerSurjective {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) : Prop :=
  ∀ x : S, ∃ n : ℕ, 0 < n ∧ x ^ n ∈ f.range

/-- The source's ``square and cube in the image'' generation condition. -/
def twoThreeGenerated {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) : Prop :=
  generatedBy f {x : S | x ^ 2 ∈ f.range ∧ x ^ 3 ∈ f.range}

/-- The source's positive-characteristic generation condition for a ring map. -/
def pPowerGenerated {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (p : ℕ) : Prop :=
  generatedBy f
    {x : S | ∃ n : ℕ, 0 < n ∧
      x ^ (p ^ n) ∈ f.range ∧ (p ^ n : S) * x ∈ f.range}

/- `ZMod p` is Mathlib's canonical prime field.  The characteristic witness
   is explicit because `ZMod.algebra` is intentionally not a global instance. -/
/-- Algebraicity over the prime field of characteristic `p`. -/
def isAlgebraicOverPrimeField (p : ℕ) (K : Type*) [Field K]
    (hK : CharP K p) : Prop :=
  letI : CharP K p := hK
  letI : Algebra (ZMod p) K := ZMod.algebra K p
  Algebra.IsAlgebraic (ZMod p) K

/-- The first condition in the source's powers-field lemma. -/
def fieldPowerProperty {k k' : Type*} [Field k] [Field k']
    [Algebra k k'] : Prop :=
  ∀ x : k', ∃ n : ℕ, 0 < n ∧ x ^ n ∈ (algebraMap k k').range

/-- The classification condition in the source's powers-field lemma. -/
def fieldPowerClassification {k k' : Type*} [Field k] [Field k']
    [Algebra k k'] : Prop :=
  Function.Surjective (algebraMap k k') ∨
    ∃ p : ℕ, p.Prime ∧
      ∃ hk : CharP k p, ∃ hk' : CharP k' p,
        IsPurelyInseparable k k' ∨
          (isAlgebraicOverPrimeField p k hk ∧
            isAlgebraicOverPrimeField p k' hk')

/-- The source's positive-characteristic generation condition for a field extension. -/
def pPowerFieldGenerated {k k' : Type*} [Field k] [Field k']
    [Algebra k k'] (p : ℕ) : Prop :=
  IntermediateField.adjoin k
      {x : k' | ∃ n : ℕ, 0 < n ∧
        x ^ (p ^ n) ∈ (algebraMap k k').range ∧
          (p ^ n : k') * x ∈ (algebraMap k k').range} = ⊤

/-- The corrected positive-characteristic classification in the source's
    `p`-power field lemma. -/
def pPowerFieldClassification {k k' : Type*} [Field k] [Field k']
    [Algebra k k'] (p : ℕ) : Prop :=
  Function.Surjective (algebraMap k k') ∨
    ∃ _hk : CharP k p, ∃ _hk' : CharP k' p, IsPurelyInseparable k k'

/- The source's `Z[x^(p^n), p^n x, ...]` is represented by the canonical
   subalgebra of a two-variable integer polynomial ring. -/
/-- The integer polynomial subalgebra used in the auxiliary powers lemma. -/
def helpWithPowersSubalgebra (p n m : ℕ) :
    Subalgebra ℤ (MvPolynomial (Fin 2) ℤ) :=
  Algebra.adjoin ℤ
    { (MvPolynomial.X (0 : Fin 2)) ^ (p ^ n),
      (p ^ n : MvPolynomial (Fin 2) ℤ) * MvPolynomial.X (0 : Fin 2),
      (MvPolynomial.X (1 : Fin 2)) ^ (p ^ m),
      (p ^ m : MvPolynomial (Fin 2) ℤ) * MvPolynomial.X (1 : Fin 2) }

/- The map between residue fields at a prime and its inverse image is the
   canonical Mathlib map. -/
/-- The residue-field map induced by a ring map at a target prime. -/
noncomputable def residueFieldMap {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (q : PrimeSpectrum S) :
    (PrimeSpectrum.comap f q).asIdeal.ResidueField →+* q.asIdeal.ResidueField :=
  Ideal.ResidueField.map (PrimeSpectrum.comap f q).asIdeal q.asIdeal f rfl

/-- Every residue-field map induced by `f` is bijective. -/
def residueFieldMapsBijective {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) : Prop :=
  ∀ q : PrimeSpectrum S, Function.Bijective (residueFieldMap f q)

/-- Every residue-field extension induced by `f` is purely inseparable. -/
def residueFieldExtensionsPurelyInseparable {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) : Prop :=
  ∀ q : PrimeSpectrum S,
    letI : Algebra ((PrimeSpectrum.comap f q).asIdeal.ResidueField)
        (q.asIdeal.ResidueField) := (residueFieldMap f q).toAlgebra
    IsPurelyInseparable ((PrimeSpectrum.comap f q).asIdeal.ResidueField)
      (q.asIdeal.ResidueField)

/-- The two equivalent powers-field conditions for every residue-field extension. -/
def residueFieldPowerProperties {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) : Prop :=
  ∀ q : PrimeSpectrum S,
    letI : Algebra ((PrimeSpectrum.comap f q).asIdeal.ResidueField)
        (q.asIdeal.ResidueField) := (residueFieldMap f q).toAlgebra
    fieldPowerProperty (k := (PrimeSpectrum.comap f q).asIdeal.ResidueField)
        (k' := q.asIdeal.ResidueField) ∧
      fieldPowerClassification (k := (PrimeSpectrum.comap f q).asIdeal.ResidueField)
        (k' := q.asIdeal.ResidueField)

/-- The two equivalent `p`-power conditions for every residue-field extension. -/
def pResidueFieldProperties {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (p : ℕ) : Prop :=
  ∀ q : PrimeSpectrum S,
    letI : Algebra ((PrimeSpectrum.comap f q).asIdeal.ResidueField)
        (q.asIdeal.ResidueField) := (residueFieldMap f q).toAlgebra
    pPowerFieldGenerated (k := (PrimeSpectrum.comap f q).asIdeal.ResidueField)
        (k' := q.asIdeal.ResidueField) p ∧
      pPowerFieldClassification (k := (PrimeSpectrum.comap f q).asIdeal.ResidueField)
        (k' := q.asIdeal.ResidueField) p

/-- The polynomial-generation condition in the final source lemma. -/
def universallyBijectiveGenerated {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) : Prop :=
  generatedBy f
    {x : S | ∃ n : ℕ, 0 < n ∧ ∃ P : Polynomial R,
      P.map f = (Polynomial.X - Polynomial.C x) ^ n}

/-! ## Universal homeomorphisms -/

/-- Tensoring an algebraically purely inseparable field extension with an
    algebra induces a homeomorphism on spectra. -/
theorem tensorProduct_spectrum_homeomorph_of_isPurelyInseparable
    {k K R : Type*} [Field k] [Field K] [CommRing R]
    [Algebra k K] [Algebra k R] [IsPurelyInseparable k K] :
    IsHomeomorph (PrimeSpectrum.comap
      (Algebra.TensorProduct.includeRight : R →ₐ[k] K ⊗[k] R).toRingHom) := by
  let e := Algebra.TensorProduct.comm k R K
  have he : e.toAlgHom.comp
      (Algebra.TensorProduct.includeLeft : R →ₐ[k] R ⊗[k] K) =
      (Algebra.TensorProduct.includeRight : R →ₐ[k] K ⊗[k] R) := by
    exact Algebra.TensorProduct.comm_comp_includeLeft k R K
  rw [← he]
  simp only [AlgHom.toRingHom_eq_coe, AlgHom.comp_toRingHom,
    AlgEquiv.toAlgHom_toRingHom, PrimeSpectrum.comap_comp]
  exact (PrimeSpectrum.isHomeomorph_comap_of_isPurelyInseparable k K R).comp
    (PrimeSpectrum.isHomeomorph_comap_of_bijective e.bijective)

/-- The source's powers-field criterion: every element has a positive power in
    the base field exactly in the classified cases. -/
/- Proof roadmap (`fieldPowerProperty_iff_classification`).

The statement is the trichotomy in `books/algebra.tex`, Lemma
`lemma-powers-field`; in particular, the last alternative really requires both
fields to be algebraic over `ZMod p`, rather than algebraicity of `k' / k`.

* First turn `hpow : fieldPowerProperty` into
  `halg : Algebra.IsAlgebraic k k'`.  For `x : k'`, unpack
  `hpow x` as `⟨n, hn, a, ha⟩`; `x ^ n` is integral because `ha` identifies it
  with `algebraMap k k' a`, and `IsIntegral.of_pow hn` then makes `x`
  integral.  The relevant declaration is in
  `Mathlib/RingTheory/IntegralClosure/IsIntegral/Basic.lean`.
* Split on surjectivity of `algebraMap k k'`.  The surjective case is the first
  disjunct.  Otherwise inspect `separableClosure k k'`.
  `separableClosure.eq_bot_iff` in
  `Mathlib/FieldTheory/PurelyInseparable/Basic.lean`, instantiated using
  `halg`, closes the purely inseparable case.  In the other case choose
  `x : k'` in `separableClosure k k' \ ⊥`; use
  `mem_separableClosure_iff` for `IsSeparable k x` and the description of
  membership in `⊥` to record `x ∉ (algebraMap k k').range`.
* Formalize the conjugates argument from the source for this `x`.  Put
  `Kx := k⟨x⟩` and `Ω := AlgebraicClosure k`.  Give `Kx` its finite-dimensional
  instance with `IntermediateField.adjoin.finiteDimensional`.  Since `x` is
  separable and not in the base, its minimal polynomial has degree greater
  than one.  Use `IntermediateField.card_algHom_adjoin_integral` (and
  `IntermediateField.fintypeOfAlgHomAdjoinIntegral` when converting
  `Nat.card` to `Fintype.card`) from
  `Mathlib/FieldTheory/IntermediateField/Adjoin/Basic.lean`, together with the
  splitting instance for `AlgebraicClosure k` from
  `Mathlib/FieldTheory/IsAlgClosed/AlgebraicClosure.lean`, to choose distinct
  `σ τ : Kx →ₐ[k] Ω` with different values on
  `AdjoinSimple.gen k x`.
* For every `a : k`, apply `hpow (x + algebraMap k k' a)`.  The two embeddings
  fix `k`, so their values have equal positive powers.  Their denominator is
  nonzero because `x` is not in the base.  Thus
  `ζ a := σ(x + a) / τ(x + a)` satisfies a positive power equal to one;
  `IsAlgebraic.of_pow` from
  `Mathlib/RingTheory/Algebraic/Basic.lean` makes every `ζ a` algebraic over
  any chosen prime subfield.  Distinctness of `σ` and `τ` also gives
  `ζ a ≠ 1`.  With `ζ := ζ 0` and `ζ' := ζ 1`, use
  `τ(x) = (1 - ζ') / (ζ' - ζ)` and then
  `( ζ a - 1) * a = (ζ - ζ a) * τ(x)`.  Closure of algebraic
  elements under `add`, `sub`, `mul`, and `inv` is provided by the
  `IsAlgebraic` lemmas in
  `Mathlib/RingTheory/Algebraic/Integral.lean`.  Reflect algebraicity along the
  injective tower map `IsScalarTower.toAlgHom` using
  `Algebra.IsAlgebraic.of_injective`; this proves that `k` is algebraic over
  the selected prime subfield.
* Use `CharP.exists' k` from `Mathlib/Algebra/CharP/Defs.lean`.  In the
  positive-characteristic branch unpack `p`, install the returned
  `CharP k p`, transport it to `k'` with `Algebra.charP_iff k k' p`, and
  install `ZMod.algebra k p` and `ZMod.algebra k' p`.  The preceding
  conjugates argument with prime subfield `ZMod p` gives algebraicity of `k`;
  combine it with `halg` using `Algebra.IsAlgebraic.trans` from
  `Mathlib/RingTheory/Algebraic/Integral.lean` to get algebraicity of `k'`.
  Package these two instances with the explicit `CharP` witnesses required by
  `isAlgebraicOverPrimeField`.
* The characteristic-zero branch must be eliminated, not silently folded into
  the algebraic alternative.  Apply the same construction over `ℚ`.  All
  `ζ a` for `a : ℚ` lie in the fixed intermediate field
  `N := IntermediateField.adjoin ℚ {ζ, ζ'}`.  Give `N` a
  `FiniteDimensional ℚ N` instance via
  `IntermediateField.finiteDimensional_adjoin` and hence a `NumberField N`
  instance.  A positive-power-equals-one element defines a unit of the ring
  of integers of `N` (use `IsIntegral.of_pow` for integrality and
  `Units.mkOfMulEqOne` for the inverse), lying in
  `NumberField.Units.torsion N`.  That subgroup is finite
  by the instance in
  `Mathlib/NumberTheory/NumberField/Units/Basic.lean`.  The identity defining
  `ζ a` shows that `a ↦ ζ a` is injective: equality for two parameters
  forces `ζ a = 1`.  `Finite.of_injective` would then make `ℚ` finite, the
  required contradiction.  Add the two focused AlgebraicClosure and
  NumberField imports when implementing this step.
* For the reverse implication, split the classification.  Surjectivity uses
  exponent `1`.  In the purely inseparable branch install the explicit
  `CharP` witnesses, `ExpChar k p := ExpChar.prime hp`, and the
  `IsPurelyInseparable` instance, then use `IsPurelyInseparable.pow_mem k p x`
  and positivity of `p ^ n`.  In the algebraic-over-`ZMod p` branch, for each
  nonzero `x : k'` put `E := (ZMod p)⟨x⟩`.  The instance
  `IntermediateField.adjoin.finiteDimensional` and
  `Module.finite_of_finite (ZMod p)` make `E` finite.  Apply
  `isOfFinOrder_of_finite` to the unit defined by the nonzero generator and
  `IsOfFinOrder.exists_pow_eq_one`; coercing back gives `x ^ n = 1`, which is
  in `(algebraMap k k').range`.  Handle `x = 0` with exponent `1`.
-/
private theorem charZero_integral_closure_rep
    {k : Type*} [Field k] [CharZero k]
    (N : IntermediateField ℚ (AlgebraicClosure k)) [NumberField N]
    (z : N) (hzint : IsIntegral ℤ z) :
    ∃ v : NumberField.RingOfIntegers N,
      algebraMap (NumberField.RingOfIntegers N) N v = z := by
  exact (IsIntegralClosure.isIntegral_iff (R := ℤ)
    (A := NumberField.RingOfIntegers N) (B := N)).mp hzint

private theorem unit_of_pow_eq_one
    {R : Type*} [CommRing R] (v : R) (n : ℕ) (hn : 0 < n)
    (hvpow : v ^ n = 1) :
    ∃ u : Rˣ, (u : R) = v ∧ (u : R) ^ n = 1 := by
  let u : Rˣ := Units.mkOfMulEqOne v (v ^ (n - 1)) (by
    rw [← pow_succ', Nat.sub_add_cancel hn, hvpow])
  refine ⟨u, ?_, ?_⟩
  · simp [u, Units.val_mkOfMulEqOne]
  · rw [← Units.val_pow_eq_pow_val]
    simp [u, Units.val_mkOfMulEqOne, hvpow]

private theorem charZero_root_unit_of_integral
    {k : Type*} [Field k] [CharZero k]
    (N : IntermediateField ℚ (AlgebraicClosure k)) [NumberField N]
    (z : N) (v : NumberField.RingOfIntegers N)
    (hv : algebraMap (NumberField.RingOfIntegers N) N v = z)
    (n : ℕ) (hn : 0 < n) (hzpow : z ^ n = 1) :
    ∃ u : (NumberField.RingOfIntegers N)ˣ,
      algebraMap (NumberField.RingOfIntegers N) N u = z ∧
        (u : NumberField.RingOfIntegers N) ^ n = 1 := by
  have hvpow : v ^ n = 1 := by
    apply NumberField.RingOfIntegers.coe_injective
    rw [map_pow, map_one, hv]
    exact hzpow
  obtain ⟨u, huv, hu_pow⟩ := unit_of_pow_eq_one v n hn hvpow
  refine ⟨u, ?_, ?_⟩
  · rw [huv, hv]
  · exact hu_pow

private theorem charZero_integral_root_unit
    {k : Type*} [Field k] [CharZero k]
    (N : IntermediateField ℚ (AlgebraicClosure k)) [NumberField N]
    (z : N) (n : ℕ) (hn : 0 < n) (hzpow : z ^ n = 1) :
    ∃ u : (NumberField.RingOfIntegers N)ˣ,
      algebraMap (NumberField.RingOfIntegers N) N u = z ∧
        (u : NumberField.RingOfIntegers N) ^ n = 1 := by
  have hzint : IsIntegral ℤ z := by
    apply IsIntegral.of_pow hn
    rw [hzpow]
    exact isIntegral_one
  obtain ⟨v, hv⟩ := charZero_integral_closure_rep N z hzint
  exact charZero_root_unit_of_integral N z v hv n hn hzpow

private theorem charZero_root_of_unity_torsion
    {k : Type*} [Field k] [CharZero k]
    (N : IntermediateField ℚ (AlgebraicClosure k)) [NumberField N]
    (z : N) (n : ℕ) (hn : 0 < n) (hzpow : z ^ n = 1) :
    ∃ u : NumberField.Units.torsion N,
      algebraMap N (AlgebraicClosure k)
          (algebraMap (NumberField.RingOfIntegers N) N
            (u : (NumberField.RingOfIntegers N)ˣ)) = z := by
  obtain ⟨u, hu, hu_pow⟩ := charZero_integral_root_unit N z n hn hzpow
  have hu_tors : u ∈ NumberField.Units.torsion N := by
    rw [NumberField.Units.torsion, CommGroup.mem_torsion,
      isOfFinOrder_iff_pow_eq_one]
    refine ⟨n, hn, ?_⟩
    apply Units.ext
    exact hu_pow
  refine ⟨⟨u, hu_tors⟩, ?_⟩
  change algebraMap N (AlgebraicClosure k)
      (algebraMap (NumberField.RingOfIntegers N) N
        (u : (NumberField.RingOfIntegers N)ˣ)) = z
  rw [hu]
  rfl
private theorem charZero_torsion_range_finite
    {k : Type*} [Field k] [CharZero k]
    (N : IntermediateField ℚ (AlgebraicClosure k)) [NumberField N]
    (ζq : ℚ → AlgebraicClosure k)
    (hζq_mem : ∀ q : ℚ, ζq q ∈ N)
    (hζqpow : ∀ q : ℚ, ∃ n : ℕ, 0 < n ∧ (ζq q) ^ n = 1) :
    (Set.range ζq).Finite := by
  have hex (q : ℚ) :
      ∃ u : NumberField.Units.torsion N,
        algebraMap N (AlgebraicClosure k)
            (algebraMap (NumberField.RingOfIntegers N) N
              (u : (NumberField.RingOfIntegers N)ˣ)) = ζq q := by
    obtain ⟨n, hn, hpow⟩ := hζqpow q
    let zN : N := ⟨ζq q, hζq_mem q⟩
    have hzpow : zN ^ n = 1 := by
      apply Subtype.ext
      exact hpow
    obtain ⟨u, hu⟩ := charZero_root_of_unity_torsion N zN n hn hzpow
    refine ⟨u, ?_⟩
    calc
      algebraMap N (AlgebraicClosure k)
          (algebraMap (NumberField.RingOfIntegers N) N
            (u : (NumberField.RingOfIntegers N)ˣ)) = zN := hu
      _ = ζq q := rfl
  let φ : NumberField.Units.torsion N → AlgebraicClosure k := fun u =>
    algebraMap N (AlgebraicClosure k)
      (algebraMap (NumberField.RingOfIntegers N) N
        (u : (NumberField.RingOfIntegers N)ˣ))
  let g : ℚ → NumberField.Units.torsion N := fun q => Classical.choose (hex q)
  have hg (q : ℚ) : φ (g q) = ζq q := Classical.choose_spec (hex q)
  have hfinite : (Set.range g).Finite := Set.toFinite _
  have himage : (φ '' Set.range g).Finite := hfinite.image φ
  have hζrange : Set.range ζq ⊆ φ '' Set.range g := by
    rintro _ ⟨q, rfl⟩
    exact ⟨g q, ⟨q, rfl⟩, hg q⟩
  exact himage.subset hζrange

private theorem rational_scalarTower_of_charZero
    {k : Type*} [Field k] [CharZero k] :
    IsScalarTower ℚ k (AlgebraicClosure k) := inferInstance

private theorem charZero_ratio_contradiction
    {k : Type*} [Field k] [CharZero k]
    [IsScalarTower ℚ k (AlgebraicClosure k)]
    (ζ : k → AlgebraicClosure k)
    (s t : AlgebraicClosure k)
    (hζpow : ∀ a : k, ∃ n : ℕ, 0 < n ∧ (ζ a) ^ n = 1)
    (hζneone : ∀ a : k, ζ a ≠ 1)
    (hrel : ∀ a : k,
        s + algebraMap k (AlgebraicClosure k) a =
          ζ a * (t + algebraMap k (AlgebraicClosure k) a))
    (hden : ∀ a : k, t + algebraMap k (AlgebraicClosure k) a ≠ 0) :
    False := by
  let ζq : ℚ → AlgebraicClosure k := fun q => ζ (algebraMap ℚ k q)
  have hζqpow (q : ℚ) : ∃ n : ℕ, 0 < n ∧ (ζq q) ^ n = 1 := by
    exact hζpow (algebraMap ℚ k q)
  have hζqneone (q : ℚ) : ζq q ≠ 1 := by
    exact hζneone (algebraMap ℚ k q)
  have hrelq (q : ℚ) :
      s + algebraMap ℚ (AlgebraicClosure k) q =
        ζq q * (t + algebraMap ℚ (AlgebraicClosure k) q) := by
    simpa [ζq, IsScalarTower.algebraMap_apply ℚ k (AlgebraicClosure k)] using
      hrel (algebraMap ℚ k q)
  have hrelq0 : s = ζq 0 * t := by
    simpa using hrelq 0
  have hrelq1 : s + 1 = ζq 1 * (t + 1) := by
    simpa using hrelq 1
  have hτrelq : t * (ζq 1 - ζq 0) = 1 - ζq 1 := by
    have h1 : ζq 1 * t = s + 1 - ζq 1 := by
      have := (sub_eq_iff_eq_add.mpr (by simpa [mul_add] using hrelq1)).symm
      simpa [add_assoc] using this
    have h0 : ζq 0 * t = s := hrelq0.symm
    calc
      t * (ζq 1 - ζq 0) = ζq 1 * t - ζq 0 * t := by ring
      _ = (s + 1 - ζq 1) - s := by rw [h1, h0]
      _ = 1 - ζq 1 := by ring
  have hζqdiff : ζq 1 - ζq 0 ≠ 0 := by
    intro hdiff
    have hone : 1 - ζq 1 = 0 := by
      calc
        1 - ζq 1 = t * (ζq 1 - ζq 0) := hτrelq.symm
        _ = 0 := by rw [hdiff, mul_zero]
    exact hζqneone 1 (sub_eq_zero.mp hone).symm
  have hτformulaq : t = (1 - ζq 1) / (ζq 1 - ζq 0) := by
    apply (eq_div_iff hζqdiff).2
    exact hτrelq
  have hζqint (q : ℚ) : IsIntegral ℚ (ζq q) := by
    obtain ⟨n, hn, hpow⟩ := hζqpow q
    apply IsIntegral.of_pow hn
    rw [hpow]
    exact isIntegral_one
  let N : IntermediateField ℚ (AlgebraicClosure k) :=
    IntermediateField.adjoin ℚ ({ζq 0, ζq 1} : Set (AlgebraicClosure k))
  let inst_finiteDimensional_rat_N : FiniteDimensional ℚ N := by
    simpa [N] using
      (IntermediateField.finiteDimensional_adjoin_pair
        (K := ℚ) (x := ζq 0) (y := ζq 1) (hζqint 0) (hζqint 1))
  let inst_numberField_N : NumberField N := NumberField.of_module_finite ℚ N
  have hζq0N : ζq 0 ∈ N := by
    exact IntermediateField.subset_adjoin ℚ _ (by simp)
  have hζq1N : ζq 1 ∈ N := by
    exact IntermediateField.subset_adjoin ℚ _ (by simp)
  have htN : t ∈ N := by
    rw [hτformulaq]
    exact N.div_mem (N.sub_mem N.one_mem hζq1N)
      (N.sub_mem hζq1N hζq0N)
  have hsN : s ∈ N := by
    rw [hrelq0]
    exact N.mul_mem hζq0N htN
  have hζq_mem (q : ℚ) : ζq q ∈ N := by
    have hformula : ζq q =
        (s + algebraMap ℚ (AlgebraicClosure k) q) /
          (t + algebraMap ℚ (AlgebraicClosure k) q) := by
      apply (eq_div_iff (hden (algebraMap ℚ k q))).2
      exact (hrelq q).symm
    rw [hformula]
    exact N.div_mem (N.add_mem hsN (by simp))
      (N.add_mem htN (by simp))
  have hζq_inj : Function.Injective ζq := by
    intro a b hab
    have hzero :
        (1 - ζq a) *
            (algebraMap ℚ (AlgebraicClosure k) a -
              algebraMap ℚ (AlgebraicClosure k) b) = 0 := by
      calc
        (1 - ζq a) *
              (algebraMap ℚ (AlgebraicClosure k) a -
                algebraMap ℚ (AlgebraicClosure k) b) =
            (s + algebraMap ℚ (AlgebraicClosure k) a -
              (s + algebraMap ℚ (AlgebraicClosure k) b)) -
              ζq a *
                (t + algebraMap ℚ (AlgebraicClosure k) a -
                  (t + algebraMap ℚ (AlgebraicClosure k) b)) := by ring
        _ = 0 := by rw [hrelq a, hrelq b, hab]; ring
    have hneq : 1 - ζq a ≠ 0 := sub_ne_zero.mpr (hζqneone a).symm
    have heq : algebraMap ℚ (AlgebraicClosure k) a =
        algebraMap ℚ (AlgebraicClosure k) b := by
      exact sub_eq_zero.mp ((mul_eq_zero.mp hzero).resolve_left hneq)
    exact (algebraMap ℚ (AlgebraicClosure k)).injective heq
  exact (Set.infinite_range_of_injective hζq_inj)
    (charZero_torsion_range_finite N ζq hζq_mem hζqpow)

private theorem zmod_algebraic_to_prime
    {K : Type*} [Field K] (p : ℕ) (hK : CharP K p)
    (A : Algebra (ZMod p) K)
    (h : @Algebra.IsAlgebraic (ZMod p) K _ _ A) :
    isAlgebraicOverPrimeField p K hK := by
  dsimp [isAlgebraicOverPrimeField]
  exact (Subsingleton.elim A (ZMod.algebra K p)) ▸ h

private theorem algebraic_isIntegral
    {R A : Type*} [Field R] [Field A] [Algebra R A]
    (h : Algebra.IsAlgebraic R A) (x : A) : IsIntegral R x := by
  let inst_algebraic : Algebra.IsAlgebraic R A := h
  exact (Algebra.IsAlgebraic.isIntegral (K := R) (A := A)).isIntegral x

private theorem pure_inseparable_surjective_of_charZero
    {k k' : Type*} [Field k] [Field k'] [Algebra k k']
    (hchar : CharZero k) (hpi : IsPurelyInseparable k k') :
    Function.Surjective (algebraMap k k') := by
  let inst_charZero : CharZero k := hchar
  let inst_purelyInseparable : IsPurelyInseparable k k' := hpi
  exact IsPurelyInseparable.surjective_algebraMap_of_isSeparable k k'

private theorem pure_inseparable_power_mem
    {k k' : Type*} [Field k] [Field k'] [Algebra k k']
    (p : ℕ) (hp : p.Prime) (hk : CharP k p) (hk' : CharP k' p)
    (hpi : IsPurelyInseparable k k') (x : k') :
    ∃ n : ℕ, ∃ y : k, algebraMap k k' y = x ^ (p ^ n) := by
  let inst_charP_k : CharP k p := hk
  let inst_charP_k' : CharP k' p := hk'
  let inst_expChar : ExpChar k p := ExpChar.prime hp
  let inst_purelyInseparable : IsPurelyInseparable k k' := hpi
  obtain ⟨n, y, hy⟩ := IsPurelyInseparable.pow_mem k p x
  exact ⟨n, y, hy⟩

private theorem fieldPowerProperty_to_classification
    {k k' : Type*} [Field k] [Field k'] [Algebra k k'] :
    fieldPowerProperty (k := k) (k' := k') →
      fieldPowerClassification (k := k) (k' := k') := by
  classical
  intro h
  change ∀ x : k', ∃ n : ℕ, 0 < n ∧ x ^ n ∈ (algebraMap k k').range at h
  have halg : Algebra.IsAlgebraic k k' := by
    constructor
    intro x
    obtain ⟨n, hn, ⟨a, ha⟩⟩ := h x
    apply IsAlgebraic.of_pow hn
    rw [← ha]
    exact isAlgebraic_algebraMap (R := k) (A := k') a
  by_cases hsurj : Function.Surjective (algebraMap k k')
  · exact Or.inl hsurj
  by_cases hsep : separableClosure k k' = ⊥
  · have hpi : IsPurelyInseparable k k' :=
      (separableClosure.eq_bot_iff).mp hsep
    obtain hchar | ⟨p, hpfact, hk⟩ := CharP.exists' k
    · exact False.elim (hsurj
        (pure_inseparable_surjective_of_charZero hchar hpi))
    · have hp : p.Prime := hpfact.out
      have hk' : CharP k' p := (Algebra.charP_iff k k' p).mp hk
      exact Or.inr ⟨p, hp, hk, hk', Or.inl hpi⟩
  · have hnotle : ¬ separableClosure k k' ≤ (⊥ : IntermediateField k k') := by
      intro hle
      exact hsep (le_antisymm hle bot_le)
    have hnotforall : ¬ ∀ x : k', x ∈ separableClosure k k' →
        x ∈ (⊥ : IntermediateField k k') := by
      intro hle
      exact hnotle hle
    push Not at hnotforall
    obtain ⟨x, hxsep, hxbot⟩ := hnotforall
    have hxseparable : IsSeparable k x := mem_separableClosure_iff.mp hxsep
    have hxinbase : x ∉ (algebraMap k k').range := by
      intro hx
      exact hxbot ((IntermediateField.mem_bot).2 hx)
    have hxi : IsIntegral k x := algebraic_isIntegral halg x
    have hmin : 2 ≤ (minpoly k x).natDegree :=
      (minpoly.two_le_natDegree_iff hxi).2 hxinbase
    have hcard : 2 ≤ Fintype.card ((minpoly k x).rootSet (AlgebraicClosure k)) := by
      rw [Polynomial.card_rootSet_eq_natDegree hxseparable (IsAlgClosed.splits _)]
      exact hmin
    obtain ⟨y, z, hyz⟩ := Fintype.exists_pair_of_one_lt_card
      (lt_of_lt_of_le Nat.one_lt_two hcard)
    let yroot : { w // w ∈ (minpoly k x).aroots (AlgebraicClosure k) } :=
      ⟨y, (Polynomial.mem_aroots).2
        ⟨minpoly.ne_zero hxi, (Polynomial.mem_rootSet.mp y.property).2⟩⟩
    let zroot : { w // w ∈ (minpoly k x).aroots (AlgebraicClosure k) } :=
      ⟨z, (Polynomial.mem_aroots).2
        ⟨minpoly.ne_zero hxi, (Polynomial.mem_rootSet.mp z.property).2⟩⟩
    let Kx : IntermediateField k k' :=
      IntermediateField.adjoin k ({x} : Set k')
    let hxK : x ∈ Kx := IntermediateField.subset_adjoin k ({x} : Set k') (by simp)
    let σ : Kx →ₐ[k] AlgebraicClosure k :=
      (IntermediateField.algHomAdjoinIntegralEquiv k hxi).symm yroot
    let τ : Kx →ₐ[k] AlgebraicClosure k :=
      (IntermediateField.algHomAdjoinIntegralEquiv k hxi).symm zroot
    have hgen : (⟨x, hxK⟩ : Kx) = IntermediateField.AdjoinSimple.gen k x := by
      apply Subtype.ext
      rfl
    have hσ : σ ⟨x, hxK⟩ = y := by
      rw [hgen]
      simpa [σ, yroot] using
        (IntermediateField.algHomAdjoinIntegralEquiv_symm_apply_gen k hxi yroot)
    have hτ : τ ⟨x, hxK⟩ = z := by
      rw [hgen]
      simpa [τ, zroot] using
        (IntermediateField.algHomAdjoinIntegralEquiv_symm_apply_gen k hxi zroot)
    have hgen_ne : σ ⟨x, hxK⟩ ≠ τ ⟨x, hxK⟩ := by
      intro heq
      apply hyz
      apply Subtype.ext
      rw [hσ, hτ] at heq
      exact heq
    let u : k → Kx := fun a =>
      ⟨x + algebraMap k k' a, Kx.add_mem hxK (Kx.algebraMap_mem a)⟩
    have hu_eq (a : k) : u a = ⟨x, hxK⟩ + algebraMap k Kx a := by
      apply Subtype.ext
      simp [u]
    let ζ : k → AlgebraicClosure k := fun a =>
      σ (u a) / τ (u a)
    have hζpow (a : k) : ∃ n : ℕ, 0 < n ∧ (ζ a) ^ n = 1 := by
      obtain ⟨n, hn, ⟨b, hb⟩⟩ := h (x + algebraMap k k' a)
      have hua : u a ≠ 0 := by
        intro hua
        have hzero : x + algebraMap k k' a = 0 :=
          congrArg (fun z : Kx => (z : k')) hua
        apply hxinbase
        refine ⟨-a, ?_⟩
        rw [map_neg]
        exact (add_eq_zero_iff_eq_neg.mp hzero).symm
      have hpowK : (u a) ^ n = algebraMap k Kx b := by
        apply Subtype.ext
        change (x + algebraMap k k' a) ^ n = algebraMap k k' b
        exact hb.symm
      have hτu : τ (u a) ≠ 0 := (map_ne_zero τ).2 hua
      have hpowστ : (σ (u a)) ^ n = (τ (u a)) ^ n := by
        calc
          (σ (u a)) ^ n = σ ((u a) ^ n) := (map_pow σ (u a) n).symm
          _ = σ (algebraMap k Kx b) := congrArg σ hpowK
          _ = algebraMap k (AlgebraicClosure k) b := σ.commutes b
          _ = τ (algebraMap k Kx b) := (τ.commutes b).symm
          _ = τ ((u a) ^ n) := congrArg τ hpowK.symm
          _ = (τ (u a)) ^ n := map_pow τ (u a) n
      refine ⟨n, hn, ?_⟩
      dsimp [ζ]
      rw [div_pow, div_eq_one_iff_eq (pow_ne_zero n hτu)]
      exact hpowστ
    have hζneone (a : k) : ζ a ≠ 1 := by
      intro hza
      have hua : u a ≠ 0 := by
        intro hua
        have hzero : x + algebraMap k k' a = 0 :=
          congrArg (fun z : Kx => (z : k')) hua
        apply hxinbase
        refine ⟨-a, ?_⟩
        rw [map_neg]
        exact (add_eq_zero_iff_eq_neg.mp hzero).symm
      have heq : σ (u a) = τ (u a) := by
        apply (div_eq_one_iff_eq ((map_ne_zero τ).2 hua)).mp
        exact hza
      apply hgen_ne
      rw [hu_eq, map_add, map_add, σ.commutes, τ.commutes] at heq
      exact add_right_cancel heq
    have hrel (a : k) :
        σ ⟨x, hxK⟩ + algebraMap k (AlgebraicClosure k) a =
          ζ a * (τ ⟨x, hxK⟩ + algebraMap k (AlgebraicClosure k) a) := by
      have hua : u a ≠ 0 := by
        intro hua
        have hzero : x + algebraMap k k' a = 0 :=
          congrArg (fun z : Kx => (z : k')) hua
        apply hxinbase
        refine ⟨-a, ?_⟩
        rw [map_neg]
        exact (add_eq_zero_iff_eq_neg.mp hzero).symm
      have hτu : τ (u a) ≠ 0 := (map_ne_zero τ).2 hua
      calc
        σ ⟨x, hxK⟩ + algebraMap k (AlgebraicClosure k) a =
            σ (⟨x, hxK⟩ + algebraMap k Kx a) := by
              rw [map_add, σ.commutes]
        _ = σ (u a) := by rw [← hu_eq a]
        _ = (σ (u a) / τ (u a)) * τ (u a) := by
              rw [div_mul_cancel₀ _ hτu]
        _ = ζ a * τ (u a) := by rfl
        _ = ζ a * τ (⟨x, hxK⟩ + algebraMap k Kx a) := by rw [hu_eq a]
        _ = ζ a * (τ ⟨x, hxK⟩ + algebraMap k (AlgebraicClosure k) a) := by
              rw [map_add, τ.commutes]
    obtain hchar | ⟨p, hpfact, hk⟩ := CharP.exists' k
    ·
      have hden (a : k) :
          τ ⟨x, hxK⟩ + algebraMap k (AlgebraicClosure k) a ≠ 0 := by
        have hua : u a ≠ 0 := by
          intro hua
          have hzero : x + algebraMap k k' a = 0 :=
            congrArg (fun z : Kx => (z : k')) hua
          apply hxinbase
          refine ⟨-a, ?_⟩
          rw [map_neg]
          exact (add_eq_zero_iff_eq_neg.mp hzero).symm
        have hτu : τ (u a) ≠ 0 := (map_ne_zero τ).2 hua
        rw [hu_eq, map_add, τ.commutes] at hτu
        exact hτu
      exact False.elim (@charZero_ratio_contradiction k _ hchar
        (@rational_scalarTower_of_charZero k _ hchar) ζ
        (σ ⟨x, hxK⟩) (τ ⟨x, hxK⟩) hζpow hζneone hrel hden)
    · have hp : p.Prime := hpfact.out
      have hk' : CharP k' p := (Algebra.charP_iff k k' p).mp hk
      let inst_charP_k : CharP k p := hk
      let inst_charP_k' : CharP k' p := hk'
      let inst_fact_prime : Fact p.Prime := hpfact
      let inst_neZero_p : NeZero p := ⟨hp.ne_zero⟩
      let inst_alg_zmod_k : Algebra (ZMod p) k := ZMod.algebra k p
      let inst_alg_zmod_k' : Algebra (ZMod p) k' := ZMod.algebra k' p
      let inst_scalarTower_zmod_k_closure :
          IsScalarTower (ZMod p) k (AlgebraicClosure k) := inferInstance
      have hζalg (a : k) : IsAlgebraic (ZMod p) (ζ a) := by
        obtain ⟨n, hn, hpow⟩ := hζpow a
        apply IsAlgebraic.of_pow hn
        rw [hpow]
        exact isAlgebraic_one
      have hrel0 :
          σ ⟨x, hxK⟩ = ζ 0 * τ ⟨x, hxK⟩ := by
        simpa using hrel 0
      have hrel1 :
          σ ⟨x, hxK⟩ + 1 = ζ 1 * (τ ⟨x, hxK⟩ + 1) := by
        simpa using hrel 1
      have hrel1' :
          σ ⟨x, hxK⟩ + 1 = ζ 1 * τ ⟨x, hxK⟩ + ζ 1 := by
        simpa [mul_add] using hrel1
      have hrel0' : σ ⟨x, hxK⟩ = ζ 0 * τ ⟨x, hxK⟩ := hrel0
      have hτrel :
          τ ⟨x, hxK⟩ * (ζ 1 - ζ 0) = 1 - ζ 1 := by
        have h1 : ζ 1 * τ ⟨x, hxK⟩ =
            σ ⟨x, hxK⟩ + 1 - ζ 1 :=
          (sub_eq_iff_eq_add.mpr hrel1').symm
        have h0 : ζ 0 * τ ⟨x, hxK⟩ = σ ⟨x, hxK⟩ := hrel0'.symm
        calc
          τ ⟨x, hxK⟩ * (ζ 1 - ζ 0) =
              ζ 1 * τ ⟨x, hxK⟩ - ζ 0 * τ ⟨x, hxK⟩ := by ring
          _ = (σ ⟨x, hxK⟩ + 1 - ζ 1) - σ ⟨x, hxK⟩ := by rw [h1, h0]
          _ = 1 - ζ 1 := by ring
      have hζdiff : ζ 1 - ζ 0 ≠ 0 := by
        intro hdiff
        have hone : 1 - ζ 1 = 0 := by
          calc
            1 - ζ 1 = τ ⟨x, hxK⟩ * (ζ 1 - ζ 0) := hτrel.symm
            _ = 0 := by rw [hdiff, mul_zero]
        exact hζneone 1 (sub_eq_zero.mp hone).symm
      have hτformula :
          τ ⟨x, hxK⟩ = (1 - ζ 1) / (ζ 1 - ζ 0) := by
        apply (eq_div_iff hζdiff).2
        exact hτrel
      have hnum : IsAlgebraic (ZMod p) (1 - ζ 1) := by
        exact (isAlgebraic_one.isIntegral.sub (hζalg 1).isIntegral).isAlgebraic
      have hden : IsAlgebraic (ZMod p) (ζ 1 - ζ 0) := by
        exact ((hζalg 1).isIntegral.sub (hζalg 0).isIntegral).isAlgebraic
      have hτalg : IsAlgebraic (ZMod p) (τ ⟨x, hxK⟩) := by
        rw [hτformula]
        simpa [div_eq_mul_inv] using
          (hnum.isIntegral.mul hden.isIntegral.inv).isAlgebraic
      have hK : Algebra.IsAlgebraic (ZMod p) k := by
        constructor
        intro a
        have hrelA :
            σ ⟨x, hxK⟩ + algebraMap k (AlgebraicClosure k) a =
              ζ a * τ ⟨x, hxK⟩ + ζ a * algebraMap k (AlgebraicClosure k) a := by
          simpa [mul_add] using hrel a
        have hA : algebraMap k (AlgebraicClosure k) a =
            (ζ a - ζ 0) * τ ⟨x, hxK⟩ +
              ζ a * algebraMap k (AlgebraicClosure k) a := by
          calc
            algebraMap k (AlgebraicClosure k) a =
                (σ ⟨x, hxK⟩ + algebraMap k (AlgebraicClosure k) a) -
                  σ ⟨x, hxK⟩ := by ring
            _ = (ζ a * τ ⟨x, hxK⟩ + ζ a * algebraMap k (AlgebraicClosure k) a) -
                  ζ 0 * τ ⟨x, hxK⟩ := by rw [hrelA, hrel0']
            _ = (ζ a - ζ 0) * τ ⟨x, hxK⟩ +
                  ζ a * algebraMap k (AlgebraicClosure k) a := by ring
        have hdiffrel :
            (ζ a - 1) * algebraMap k (AlgebraicClosure k) a =
              (ζ 0 - ζ a) * τ ⟨x, hxK⟩ := by
          calc
            (ζ a - 1) * algebraMap k (AlgebraicClosure k) a =
                ζ a * algebraMap k (AlgebraicClosure k) a -
                  algebraMap k (AlgebraicClosure k) a := by ring
            _ = ζ a * algebraMap k (AlgebraicClosure k) a -
                  ((ζ a - ζ 0) * τ ⟨x, hxK⟩ +
                    ζ a * algebraMap k (AlgebraicClosure k) a) :=
              congrArg (fun q => ζ a * algebraMap k (AlgebraicClosure k) a - q) hA
            _ = (ζ 0 - ζ a) * τ ⟨x, hxK⟩ := by ring
        have haeq : algebraMap k (AlgebraicClosure k) a =
            ((ζ 0 - ζ a) * τ ⟨x, hxK⟩) / (ζ a - 1) := by
          apply (eq_div_iff (sub_ne_zero.mpr (hζneone a))).2
          calc
            algebraMap k (AlgebraicClosure k) a * (ζ a - 1) =
                (ζ a - 1) * algebraMap k (AlgebraicClosure k) a :=
              mul_comm _ _
            _ = (ζ 0 - ζ a) * τ ⟨x, hxK⟩ := hdiffrel
        have hnuma : IsIntegral (ZMod p)
            ((ζ 0 - ζ a) * τ ⟨x, hxK⟩) :=
          (hζalg 0).isIntegral.sub (hζalg a).isIntegral
            |>.mul hτalg.isIntegral
        have hdena : IsIntegral (ZMod p) (ζ a - 1) :=
          (hζalg a).isIntegral.sub isAlgebraic_one.isIntegral
        have haalg : IsAlgebraic (ZMod p)
            (algebraMap k (AlgebraicClosure k) a) := by
          rw [haeq]
          simpa [div_eq_mul_inv] using (hnuma.mul hdena.inv).isAlgebraic
        let f : k →ₐ[ZMod p] AlgebraicClosure k :=
          IsScalarTower.toAlgHom (ZMod p) k (AlgebraicClosure k)
        have hf : IsAlgebraic (ZMod p) (f a) := by
          change IsAlgebraic (ZMod p) (algebraMap k (AlgebraicClosure k) a)
          exact haalg
        exact (isAlgebraic_algHom_iff f f.injective).mp hf
      let inst_scalarTower_zmod_k_k' : IsScalarTower (ZMod p) k k' := by
        apply IsScalarTower.of_algebraMap_eq'
        ext a
        obtain ⟨n, rfl⟩ := ZMod.natCast_zmod_surjective a
        simp
      let inst_algebraic_zmod_k : Algebra.IsAlgebraic (ZMod p) k := hK
      have hK' : Algebra.IsAlgebraic (ZMod p) k' :=
        Algebra.IsAlgebraic.trans (ZMod p) k k'
      have hKdef : isAlgebraicOverPrimeField p k hk :=
        zmod_algebraic_to_prime p hk (inferInstance : Algebra (ZMod p) k) hK
      have hK'def : isAlgebraicOverPrimeField p k' hk' :=
        zmod_algebraic_to_prime p hk' (inferInstance : Algebra (ZMod p) k') hK'
      exact Or.inr ⟨p, hp, hk, hk', Or.inr ⟨hKdef, hK'def⟩⟩

private theorem fieldPowerClassification_to_fieldPowerProperty
    {k k' : Type*} [Field k] [Field k'] [Algebra k k'] :
    fieldPowerClassification (k := k) (k' := k') →
      fieldPowerProperty (k := k) (k' := k') := by
  classical
  intro h
  change
    (Function.Surjective (algebraMap k k') ∨
      ∃ p : ℕ, p.Prime ∧
        ∃ hk : CharP k p, ∃ hk' : CharP k' p,
          IsPurelyInseparable k k' ∨
            (isAlgebraicOverPrimeField p k hk ∧
              isAlgebraicOverPrimeField p k' hk')) at h
  change ∀ x : k', ∃ n : ℕ, 0 < n ∧ x ^ n ∈ (algebraMap k k').range
  rcases h with hsurj | ⟨p, hp, hk, hk', hcase⟩
  · intro x
    obtain ⟨y, rfl⟩ := hsurj x
    exact ⟨1, Nat.zero_lt_one, by simp⟩
  · rcases hcase with hpi | ⟨hK, hK'⟩
    · intro x
      obtain ⟨n, y, hy⟩ := pure_inseparable_power_mem p hp hk hk' hpi x
      exact ⟨p ^ n, Nat.pow_pos hp.pos, ⟨y, hy⟩⟩
    · let inst_charP_k : CharP k p := hk
      let inst_charP_k' : CharP k' p := hk'
      let inst_fact_prime : Fact p.Prime := ⟨hp⟩
      let inst_neZero_p : NeZero p := ⟨hp.ne_zero⟩
      let inst_alg_zmod_k' : Algebra (ZMod p) k' := ZMod.algebra k' p
      have hK'alg : @Algebra.IsAlgebraic (ZMod p) k' _ _ (ZMod.algebra k' p) := by
        dsimp [isAlgebraicOverPrimeField] at hK'
        exact hK'
      have hK'alg_current : @Algebra.IsAlgebraic (ZMod p) k' _ _
          (inferInstance : Algebra (ZMod p) k') := by
        exact (Subsingleton.elim (ZMod.algebra k' p)
          (inferInstance : Algebra (ZMod p) k')) ▸ hK'alg
      intro x
      by_cases hx : x = 0
      · subst x
        exact ⟨1, Nat.zero_lt_one, ⟨0, by simp⟩⟩
      · let E : IntermediateField (ZMod p) k' :=
          IntermediateField.adjoin (ZMod p) ({x} : Set k')
        let inst_finiteDimensional_zmod_E : FiniteDimensional (ZMod p) E :=
          IntermediateField.finiteDimensional_adjoin (S := ({x} : Set k'))
            (fun y hy => by
              have : y = x := by simpa using hy
              subst y
              let inst_alg_is_algebraic_k' : Algebra.IsAlgebraic (ZMod p) k' :=
                hK'alg_current
              exact (Algebra.IsAlgebraic.isIntegral (K := ZMod p)
                (A := k')).isIntegral x)
        let inst_finite_E : Finite E := Module.finite_of_finite (ZMod p)
        let ux : Eˣ := Units.mk0 ⟨x, IntermediateField.subset_adjoin (ZMod p)
          ({x} : Set k') (by simp)⟩ (by
            intro hzero
            apply hx
            exact congrArg (fun z : E => (z : k')) hzero)
        obtain ⟨n, hn, hux⟩ := (isOfFinOrder_of_finite ux).exists_pow_eq_one
        refine ⟨n, hn, ⟨1, ?_⟩⟩
        have hux' := congrArg (fun z : Eˣ => (z : E)) hux
        have hux'' := congrArg (fun z : E => (z : k')) hux'
        simpa [ux] using hux''.symm

theorem fieldPowerProperty_iff_classification
    {k k' : Type*} [Field k] [Field k'] [Algebra k k'] :
    fieldPowerProperty (k := k) (k' := k') ↔
      fieldPowerClassification (k := k) (k' := k') := by
  constructor
  · exact fieldPowerProperty_to_classification
  · exact fieldPowerClassification_to_fieldPowerProperty

/-- A surjective map with locally nilpotent kernel is a homeomorphism on
    spectra, isomorphic on residue fields, and retains these kernel facts
    after arbitrary base change. -/
theorem surjective_locallyNilpotentKernel
    {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (hf : Function.Surjective f) (hker : locallyNilpotentKernel f) :
    IsHomeomorph (PrimeSpectrum.comap f) ∧
      residueFieldMapsBijective f ∧
      ∀ (R' : Type*) [CommRing R'] (g : R →+* R'),
          Function.Surjective (baseChangeRingMap f g) ∧
            locallyNilpotentKernel (baseChangeRingMap f g) := by
  let hker' : RingHom.ker f ≤ nilradical R := by
    intro x hx
    exact (mem_nilradical).2 (hker x hx)
  refine ⟨PrimeSpectrum.isHomeomorph_comap f (fun x => ?_) hker', ?_, ?_⟩
  · obtain ⟨y, rfl⟩ := hf x
    exact ⟨1, by simp, y, by simp⟩
  · intro q
    exact RingHom.SurjectiveOnStalks.residueFieldMap_bijective
      (RingHom.surjectiveOnStalks_of_surjective hf) _ _ rfl
  · intro R' _ g
    let : Algebra R S := f.toAlgebra
    let : Algebra R R' := g.toAlgebra
    constructor
    · exact Algebra.TensorProduct.includeRight_surjective (T := R') hf
    · intro x hx
      let fa : R →ₐ[R] S := AlgHom.mk' f (by
        intro c y
        simp [Algebra.smul_def, RingHom.algebraMap_toAlgebra])
      let b : R ⊗[R] R' →ₐ[R] S ⊗[R] R' :=
        Algebra.TensorProduct.map fa (AlgHom.id R R')
      let a : R' →ₐ[R] R ⊗[R] R' := Algebra.TensorProduct.includeRight
      have hbker : RingHom.ker b.toRingHom ≤ nilradical (R ⊗[R] R') := by
        change RingHom.ker ((Algebra.TensorProduct.map fa (AlgHom.id R R')).toRingHom) ≤
          nilradical (R ⊗[R] R')
        have hEq : RingHom.ker ((Algebra.TensorProduct.map fa (AlgHom.id R R')).toRingHom) =
            (RingHom.ker fa).map
              (Algebra.TensorProduct.includeLeft : R →ₐ[R] R ⊗[R] R') := by
          have hmap : RingHom.ker ((Algebra.TensorProduct.map fa (AlgHom.id R R')).toRingHom) =
              RingHom.ker (Algebra.TensorProduct.map fa (AlgHom.id R R')) := by
            ext y
            rfl
          rw [hmap]
          exact Algebra.TensorProduct.rTensor_ker
            (R := R) (S := R) (A := R) (B := S) (C := R') fa hf
        rw [hEq]
        rw [Ideal.map_le_iff_le_comap]
        intro y hy
        have hy' : IsNilpotent y := (mem_nilradical).1 (hker' hy)
        exact (mem_nilradical).2 (hy'.map
          (Algebra.TensorProduct.includeLeft : R →ₐ[R] R ⊗[R] R').toRingHom)
      have hcomp : b.toRingHom.comp a.toRingHom = baseChangeRingMap f g := by
        ext y
        simp [b, a, fa, baseChangeRingMap]
      have hax : a.toRingHom x ∈ RingHom.ker b.toRingHom := by
        change b (a x) = 0
        change (b.toRingHom.comp a.toRingHom) x = 0
        rw [hcomp]
        exact hx
      have ha : Function.Injective a :=
        (Algebra.TensorProduct.includeRight_bijective
          (R := R) (A := R) (B := R') ⟨by intro x y h; exact h, by intro x; exact ⟨x, rfl⟩⟩).injective
      exact (IsNilpotent.map_iff (f := a.toRingHom) ha).mp ((mem_nilradical).1 (hbker hax))

/-- The powers criterion gives a homeomorphism on spectra and the source's
    powers-field description of all residue-field extensions. -/
theorem powerSurjective_locallyNilpotentKernel
    {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (hpower : powerSurjective f) (hker : locallyNilpotentKernel f) :
    IsHomeomorph (PrimeSpectrum.comap f) ∧ residueFieldPowerProperties f := by
  let hker' : RingHom.ker f ≤ nilradical R := by
    intro x hx
    exact (mem_nilradical).2 (hker x hx)
  refine ⟨PrimeSpectrum.isHomeomorph_comap f (fun x => ?_) hker', ?_⟩
  · simpa [powerSurjective] using hpower x
  · intro q
    let : Algebra ((PrimeSpectrum.comap f q).asIdeal.ResidueField)
        (q.asIdeal.ResidueField) := (residueFieldMap f q).toAlgebra
    have hfield : fieldPowerProperty
        (k := (PrimeSpectrum.comap f q).asIdeal.ResidueField)
        (k' := q.asIdeal.ResidueField) := by
      intro z
      obtain ⟨a, b, hb, hz⟩ :=
        IsFractionRing.div_surjective (S ⧸ q.asIdeal) z
      obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective a
      obtain ⟨w, hw⟩ := Ideal.Quotient.mk_surjective b
      obtain ⟨n, hn, r, hr⟩ := hpower y
      obtain ⟨m, hm, s, hs⟩ := hpower w
      refine ⟨n * m, Nat.mul_pos hn hm, ?_⟩
      refine ⟨algebraMap R ((PrimeSpectrum.comap f q).asIdeal.ResidueField) r ^ m /
          algebraMap R ((PrimeSpectrum.comap f q).asIdeal.ResidueField) s ^ n, ?_⟩
      have hY : residueFieldMap f q
          (algebraMap R ((PrimeSpectrum.comap f q).asIdeal.ResidueField) r) =
          algebraMap S (q.asIdeal.ResidueField) y ^ n := by
        calc
          residueFieldMap f q
              (algebraMap R ((PrimeSpectrum.comap f q).asIdeal.ResidueField) r) =
              algebraMap S (q.asIdeal.ResidueField) (f r) := by
                simpa [residueFieldMap] using
                  (Ideal.ResidueField.map_algebraMap
                    (PrimeSpectrum.comap f q).asIdeal q.asIdeal f rfl r)
          _ = algebraMap S (q.asIdeal.ResidueField) (y ^ n) := by rw [hr]
          _ = algebraMap S (q.asIdeal.ResidueField) y ^ n := by rw [map_pow]
      have hW : residueFieldMap f q
          (algebraMap R ((PrimeSpectrum.comap f q).asIdeal.ResidueField) s) =
          algebraMap S (q.asIdeal.ResidueField) w ^ m := by
        calc
          residueFieldMap f q
              (algebraMap R ((PrimeSpectrum.comap f q).asIdeal.ResidueField) s) =
              algebraMap S (q.asIdeal.ResidueField) (f s) := by
                simpa [residueFieldMap] using
                  (Ideal.ResidueField.map_algebraMap
                    (PrimeSpectrum.comap f q).asIdeal q.asIdeal f rfl s)
          _ = algebraMap S (q.asIdeal.ResidueField) (w ^ m) := by rw [hs]
          _ = algebraMap S (q.asIdeal.ResidueField) w ^ m := by rw [map_pow]
      have hz' : algebraMap S (q.asIdeal.ResidueField) y /
          algebraMap S (q.asIdeal.ResidueField) w = z := by
        simpa [Ideal.algebraMap_quotient_residueField_mk, ← hy, ← hw] using hz
      calc
        residueFieldMap f q
              (algebraMap R ((PrimeSpectrum.comap f q).asIdeal.ResidueField) r ^ m /
                algebraMap R ((PrimeSpectrum.comap f q).asIdeal.ResidueField) s ^ n) =
            (algebraMap S (q.asIdeal.ResidueField) y ^ n) ^ m /
              (algebraMap S (q.asIdeal.ResidueField) w ^ m) ^ n := by
                rw [map_div₀, map_pow, map_pow, hY, hW]
        _ = (algebraMap S (q.asIdeal.ResidueField) y /
              algebraMap S (q.asIdeal.ResidueField) w) ^ (n * m) := by
                rw [div_pow, ← pow_mul, ← pow_mul, Nat.mul_comm m n]
        _ = z ^ (n * m) := by rw [hz']
    exact ⟨hfield, (fieldPowerProperty_iff_classification
      (k := (PrimeSpectrum.comap f q).asIdeal.ResidueField)
      (k' := q.asIdeal.ResidueField)).mp hfield⟩

private theorem range_of_sq_cube_of_field
    {K L : Type*} [Field K] [Field L] (h : K →+* L) (x : L)
    (hx2 : x ^ 2 ∈ h.range) (hx3 : x ^ 3 ∈ h.range) : x ∈ h.range := by
  by_cases hx : x = 0
  · exact ⟨0, by simp [hx]⟩
  obtain ⟨a, ha⟩ := hx2
  obtain ⟨b, hb⟩ := hx3
  refine ⟨b / a, ?_⟩
  rw [map_div₀, ha, hb]
  have ha0 : a ≠ 0 := by
    intro ha0
    apply hx
    have : x ^ 2 = 0 := by rw [← ha, ha0, map_zero]
    simpa using this
  field_simp [ha0, hx]

private theorem residueFieldMap_surjective_of_twoThreeGenerated
    {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (hgen : twoThreeGenerated f) :
    ∀ q : PrimeSpectrum S, Function.Surjective (residueFieldMap f q) := by
  letI : Algebra R S := f.toAlgebra
  let U : Set S := {x : S | x ^ 2 ∈ f.range ∧ x ^ 3 ∈ f.range}
  have hgen' : Algebra.adjoin R U = ⊤ := by
    simpa [U, twoThreeGenerated, generatedBy] using hgen
  intro q
  let K := (PrimeSpectrum.comap f q).asIdeal.ResidueField
  let L := q.asIdeal.ResidueField
  let hq := residueFieldMap f q
  letI : Algebra K L := hq.toAlgebra
  have hS : ∀ s : S, algebraMap S L s ∈ hq.range := by
    intro s
    have hs : s ∈ Algebra.adjoin R U := by rw [hgen']; trivial
    refine Algebra.adjoin_induction (p := fun x _ => algebraMap S L x ∈ hq.range)
      ?_ ?_ ?_ ?_ hs
    · intro x hx
      refine range_of_sq_cube_of_field hq (algebraMap S L x) ?_ ?_
      · obtain ⟨r, hr⟩ := hx.1
        refine ⟨algebraMap R K r, ?_⟩
        calc
          hq (algebraMap R K r) = algebraMap S L (f r) := by
            simpa [K, L, hq, residueFieldMap] using
              (Ideal.ResidueField.map_algebraMap
                (PrimeSpectrum.comap f q).asIdeal q.asIdeal f rfl r)
          _ = algebraMap S L (x ^ 2) := by rw [hr]
          _ = algebraMap S L x ^ 2 := by rw [map_pow]
      · obtain ⟨r, hr⟩ := hx.2
        refine ⟨algebraMap R K r, ?_⟩
        calc
          hq (algebraMap R K r) = algebraMap S L (f r) := by
            simpa [K, L, hq, residueFieldMap] using
              (Ideal.ResidueField.map_algebraMap
                (PrimeSpectrum.comap f q).asIdeal q.asIdeal f rfl r)
          _ = algebraMap S L (x ^ 3) := by rw [hr]
          _ = algebraMap S L x ^ 3 := by rw [map_pow]
    · intro r
      refine ⟨algebraMap R K r, ?_⟩
      calc
        hq (algebraMap R K r) = algebraMap S L (f r) := by
          simpa [K, L, hq, residueFieldMap] using
            (Ideal.ResidueField.map_algebraMap
              (PrimeSpectrum.comap f q).asIdeal q.asIdeal f rfl r)
        _ = algebraMap S L (algebraMap R S r) := by
          simp [RingHom.algebraMap_toAlgebra]
    · intro x y hx hy hxp hyp
      rcases hxp with ⟨a, ha⟩
      rcases hyp with ⟨b, hb⟩
      refine ⟨a + b, ?_⟩
      calc
        hq (a + b) = hq a + hq b := map_add hq a b
        _ = algebraMap S L x + algebraMap S L y := by rw [ha, hb]
        _ = algebraMap S L (x + y) := (map_add (algebraMap S L) x y).symm
    · intro x y hx hy hxp hyp
      rcases hxp with ⟨a, ha⟩
      rcases hyp with ⟨b, hb⟩
      refine ⟨a * b, ?_⟩
      calc
        hq (a * b) = hq a * hq b := map_mul hq a b
        _ = algebraMap S L x * algebraMap S L y := by rw [ha, hb]
        _ = algebraMap S L (x * y) := (map_mul (algebraMap S L) x y).symm
  have hz : Function.Surjective hq := by
    intro z
    obtain ⟨aa, bb, hbb, hz⟩ := IsFractionRing.div_surjective (S ⧸ q.asIdeal) z
    obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective aa
    obtain ⟨w, hw⟩ := Ideal.Quotient.mk_surjective bb
    obtain ⟨r, hr⟩ := hS y
    obtain ⟨s, hs⟩ := hS w
    refine ⟨r / s, ?_⟩
    rw [map_div₀, hr, hs]
    simpa [K, L, Ideal.algebraMap_quotient_residueField_mk, ← hy, ← hw] using hz
  simpa [K, L, hq] using hz

/-- The square-and-cube criterion gives a universal homeomorphism with
    residue-field isomorphisms. -/
/- Proof roadmap (`twoThreeGenerated_locallyNilpotentKernel`).

The hypotheses match `books/algebra.tex`, Lemma `lemma-2-3-ring-map`.
In particular, `locallyNilpotentKernel` is the elementwise condition needed
here: turn it into `RingHom.ker f ≤ nilradical R` with
`mem_nilradical`, and recover the elementwise condition after base change by
the same lemma in the reverse direction.

1. Install `f.toAlgebra`, set
   `U := {x : S | x ^ 2 ∈ f.range ∧ x ^ 3 ∈ f.range}`, and unfold
   `hgen` to `hgen' : Algebra.adjoin R U = ⊤`.  Prove
   `hint : Algebra.IsIntegral R S`: each generator is integral by
   `IsIntegral.of_pow (n := 2)` and `isIntegral_algebraMap`, and
   `Algebra.IsIntegral.adjoin` makes `Algebra.adjoin R U` integral.  Transport
   along `hgen'` as in the proof scaffold below, then package this as
   `hfint : f.IsIntegral`.
2. Prove surjectivity of `PrimeSpectrum.comap f`.  Let
   `hker' : RingHom.ker f ≤ nilradical R`.  The quotient map has bijective
   comap by
   `PrimeSpectrum.comap_quotientMk_bijective_of_le_nilradical hker'`, while
   `hfint.kerLift.comap_surjective f.kerLift_injective` supplies primes above
   the quotient; compose the two surjections.
3. Prove `hresSurj : ∀ q, Function.Surjective (residueFieldMap f q)`.
   For fixed `q`, abbreviate
   `K := (PrimeSpectrum.comap f q).asIdeal.ResidueField`,
   `L := q.asIdeal.ResidueField`, and `hq := residueFieldMap f q`, with
   `Algebra K L := hq.toAlgebra`.  Use `Algebra.adjoin_induction` on
   `hgen'` to show `algebraMap S L s ∈ hq.range` for every `s : S`.
   The generator case is exactly `range_of_sq_cube_of_field hq`; obtain its
   two range witnesses via `Ideal.ResidueField.map_algebraMap`.  The scalar,
   addition, and multiplication cases use closure of `RingHom.range`.
   Finally write an arbitrary `z : L` as a quotient with
   `IsFractionRing.div_surjective`, lift numerator and denominator through
   `Ideal.Quotient.mk_surjective`, and divide their two preimages.  Since a
   nonzero ring hom between fields is injective, set
   `hres q := ⟨RingHom.injective _, hresSurj q⟩`.
4. Prove injectivity of `PrimeSpectrum.comap f`.  Given `q`, `q'` with the
   same contraction `I`, form the residue-field equivalences
   `e₁ : I.ResidueField ≃+* q.asIdeal.ResidueField` and
   `e₂ : I.ResidueField ≃+* q'.asIdeal.ResidueField` using
   `RingEquiv.ofBijective` and step 3, and put `e := e₁.symm.trans e₂`.
   By another `Algebra.adjoin_induction`, prove
   `e (algebraMap S _ s) = algebraMap S _ s` for every `s : S`.  For a
   generator, its two images have equal squares and equal cubes because both
   powers come from `R`.  The elementary field calculation already expanded
   in the scaffold below proves equality: split on the second image being
   zero; otherwise use
   `(alpha - beta) * beta ^ 2 = alpha ^ 3 - beta ^ 3` and cancel
   `beta ^ 2`.  Then use
   `Ideal.algebraMap_residueField_eq_zero` in both directions to get
   `q.asIdeal = q'.asIdeal`, followed by `PrimeSpectrum.ext`.
5. Assemble
   `hhome : IsHomeomorph (PrimeSpectrum.comap f)` with
   `isHomeomorph_iff_continuous_isClosedMap_bijective.mpr`.  Its three inputs
   are `PrimeSpectrum.continuous_comap f`,
   `PrimeSpectrum.isClosedMap_comap_of_isIntegral f hfint`, and the
   injectivity/surjectivity from steps 2 and 4.  This is the missing terminal
   assembly after the scaffold below.
6. For a base ring `R' : Type*` and `g : R →+* R'`, install
   `g.toAlgebra` and abbreviate
   `bc : R' →+* S ⊗[R] R' := baseChangeRingMap f g` and
   `a : S →+* S ⊗[R] R' := baseChangeAlgebraMap f g`.  Let
   `U' := {z | z ^ 2 ∈ bc.range ∧ z ^ 3 ∈ bc.range}`.  Prove
   `a.comp f = bc.comp g` using
   `Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap`.  Induction on
   `hgen'` then shows every `a s` lies in `Algebra.adjoin R' U'`: for a
   generator, map its square/cube witnesses across the displayed composite;
   base scalars lie in the adjoin automatically.  Finish with
   `TensorProduct.induction_on`: a pure tensor is
   `a s * bc r'`, hence belongs to the adjoin.  This proves
   `twoThreeGenerated bc` after unfolding `generatedBy`.
7. For the base-changed kernel, do not try to tensor the elementwise
   nilpotence witness directly.  Apply
   `Formalization.Books.Algebra.Unit30.spectrum_surjective_radical_ideal_conditions_baseChange`
   from `Formalization/Books/Algebra/Unit30/MoreOnImages.lean` to
   `hhome.surjective` and `g`.  It gives surjectivity of comap for
   `algebraMap R' (R' ⊗[R] S)`.  Transport this through
   `e : (R' ⊗[R] S) ≃+* (S ⊗[R] R') :=
     (Algebra.TensorProduct.comm R R' S).toRingEquiv`; prove
   `e.toRingHom.comp (algebraMap R' (R' ⊗[R] S)) = bc` by extensionality
   and `simp [baseChangeRingMap]`.  Surjectivity of `PrimeSpectrum.comap bc`
   makes its range dense, so
   `PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical bc` gives
   `RingHom.ker bc ≤ nilradical R'`.  Apply `mem_nilradical.1` pointwise to
   obtain `locallyNilpotentKernel bc`.

Known dead ends: `surjective_locallyNilpotentKernel` is unusable because `f`
need not be surjective, and `twoThreeGenerated f` does not imply
`powerSurjective f` (the positive-power property is not preserved by the
algebra-generation operations in characteristic zero).  The direct spectrum
and residue-field route above is therefore necessary.
-/
theorem twoThreeGenerated_locallyNilpotentKernel
    {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (hgen : twoThreeGenerated f) (hker : locallyNilpotentKernel f) :
    IsHomeomorph (PrimeSpectrum.comap f) ∧
      residueFieldMapsBijective f ∧
      ∀ (R' : Type*) [CommRing R'] (g : R →+* R'),
            twoThreeGenerated (baseChangeRingMap f g) ∧
            locallyNilpotentKernel (baseChangeRingMap f g) := by
  letI : Algebra R S := f.toAlgebra
  let U : Set S := {x : S | x ^ 2 ∈ f.range ∧ x ^ 3 ∈ f.range}
  have hgen' : Algebra.adjoin R U = ⊤ := by
    simpa [U, twoThreeGenerated, generatedBy] using hgen
  have hint : Algebra.IsIntegral R S := by
    let hsub : Algebra.IsIntegral R (Algebra.adjoin R U) :=
      Algebra.IsIntegral.adjoin (by
        intro x hx
        obtain ⟨r, hr⟩ := hx.1
        apply IsIntegral.of_pow (n := 2) (by norm_num)
        rw [← hr]
        simpa [RingHom.algebraMap_toAlgebra] using
          (isIntegral_algebraMap (R := R) (A := S) (x := r)))
    constructor
    intro x
    have hx : x ∈ Algebra.adjoin R U := by rw [hgen']; trivial
    have hi := hsub.isIntegral (⟨x, hx⟩ : Algebra.adjoin R U)
    change IsIntegral R ((⟨x, hx⟩ : Algebra.adjoin R U) : S)
    exact hi.algebraMap
  have hfint : f.IsIntegral := by
    intro x
    change IsIntegral R x
    exact hint.isIntegral x
  have hker' : RingHom.ker f ≤ nilradical R := by
    intro x hx
    exact (mem_nilradical).2 (hker x hx)
  have hsurj : Function.Surjective (PrimeSpectrum.comap f) := by
    exact (PrimeSpectrum.comap_quotientMk_bijective_of_le_nilradical hker').2.comp
      (hfint.kerLift.comap_surjective f.kerLift_injective)
  have hres_surj := residueFieldMap_surjective_of_twoThreeGenerated f hgen
  have hres : residueFieldMapsBijective f := by
    intro q
    refine ⟨RingHom.injective _, hres_surj q⟩
  have hres_surj' : ∀ (q : PrimeSpectrum S) (I : Ideal R) [I.IsPrime]
      (hI : I = q.asIdeal.comap f),
      Function.Surjective (Ideal.ResidueField.map I q.asIdeal f hI) := by
    intro q I _ hI
    cases hI
    exact hres_surj q
  have hcomap_inj : Function.Injective (PrimeSpectrum.comap f) := by
    intro q q' hqq'
    have hI : q.asIdeal.comap f = q'.asIdeal.comap f := by
      simpa using congrArg PrimeSpectrum.asIdeal hqq'
    let I := q.asIdeal.comap f
    letI : I.IsPrime := (PrimeSpectrum.comap f q).isPrime
    let K := I.ResidueField
    let L := q.asIdeal.ResidueField
    let L' := q'.asIdeal.ResidueField
    let hq := Ideal.ResidueField.map I q.asIdeal f rfl
    let hq' := Ideal.ResidueField.map I q'.asIdeal f hI
    let e₁ : K ≃+* L := RingEquiv.ofBijective hq
      ⟨RingHom.injective _, hres_surj' q I rfl⟩
    let e₂ : K ≃+* L' := RingEquiv.ofBijective hq'
      ⟨RingHom.injective _, hres_surj' q' I hI⟩
    let e : L ≃+* L' := e₁.symm.trans e₂
    have hebase : ∀ r : R,
        e (hq (algebraMap R K r)) = algebraMap S L' (f r) := by
      intro r
      have hecomp : e.toRingHom.comp hq = hq' := by
        apply RingHom.ext
        intro z
        change e₂ (e₁.symm (e₁ z)) = e₂ z
        rw [e₁.symm_apply_apply]
      calc
        e (hq (algebraMap R K r)) = (e.toRingHom.comp hq)
            (algebraMap R K r) := rfl
        _ = hq' (algebraMap R K r) := by rw [hecomp]
        _ = algebraMap S L' (f r) := by
          simpa [I, K, L', hq'] using
            (Ideal.ResidueField.map_algebraMap I q'.asIdeal f hI r)
    have hmap : ∀ s : S, e (algebraMap S L s) = algebraMap S L' s := by
      intro s
      have hs : s ∈ Algebra.adjoin R U := by rw [hgen']; trivial
      refine Algebra.adjoin_induction (p := fun x _ =>
        e (algebraMap S L x) = algebraMap S L' x) ?_ ?_ ?_ ?_ hs
      · intro x hx
        obtain ⟨r₂, hr₂⟩ := hx.1
        obtain ⟨r₃, hr₃⟩ := hx.2
        have hsq : e (algebraMap S L x) ^ 2 =
            algebraMap S L' x ^ 2 := by
          calc
            e (algebraMap S L x) ^ 2 =
                e ((algebraMap S L x) ^ 2) := (map_pow e _ 2).symm
            _ = e (algebraMap S L (x ^ 2)) :=
              congrArg e ((map_pow (algebraMap S L) x 2).symm)
            _ = e (hq (algebraMap R K r₂)) := by
              congr 1
              calc
                algebraMap S L (x ^ 2) = algebraMap S L (f r₂) := by rw [hr₂]
                _ = hq (algebraMap R K r₂) := by
                  symm
                  simpa [K, L, hq] using
                    (Ideal.ResidueField.map_algebraMap
                      I q.asIdeal f rfl r₂)
            _ = algebraMap S L' (f r₂) := hebase r₂
            _ = algebraMap S L' (x ^ 2) := by rw [hr₂]
            _ = algebraMap S L' x ^ 2 := by rw [map_pow]
        have hcu : e (algebraMap S L x) ^ 3 =
            algebraMap S L' x ^ 3 := by
          calc
            e (algebraMap S L x) ^ 3 =
                e ((algebraMap S L x) ^ 3) := (map_pow e _ 3).symm
            _ = e (algebraMap S L (x ^ 3)) :=
              congrArg e ((map_pow (algebraMap S L) x 3).symm)
            _ = e (hq (algebraMap R K r₃)) := by
              congr 1
              calc
                algebraMap S L (x ^ 3) = algebraMap S L (f r₃) := by rw [hr₃]
                _ = hq (algebraMap R K r₃) := by
                  symm
                  simpa [K, L, hq] using
                    (Ideal.ResidueField.map_algebraMap
                      I q.asIdeal f rfl r₃)
            _ = algebraMap S L' (f r₃) := hebase r₃
            _ = algebraMap S L' (x ^ 3) := by rw [hr₃]
            _ = algebraMap S L' x ^ 3 := by rw [map_pow]
        let α := e (algebraMap S L x)
        let β := algebraMap S L' x
        have hab : α = β := by
          by_cases hβ : β = 0
          · have hα : α ^ 2 = 0 := by simpa [α, β, hβ] using hsq
            have hα' : α * α = 0 := by simpa [pow_two] using hα
            rcases mul_eq_zero.mp hα' with hα' | hα'
            · rw [hβ]
              exact hα'
            · rw [hβ]
              exact hα'
          · have hprod : (α - β) * β ^ 2 = 0 := by
              have hsq' : α ^ 2 = β ^ 2 := by simpa [α, β] using hsq
              have hcu' : α ^ 3 = β ^ 3 := by simpa [α, β] using hcu
              calc
                (α - β) * β ^ 2 = α * β ^ 2 - β ^ 3 := by ring
                _ = α * α ^ 2 - β ^ 3 := by rw [← hsq']
                _ = α ^ 3 - β ^ 3 := by ring
                _ = 0 := sub_eq_zero.mpr hcu'
            exact sub_eq_zero.mp
              ((mul_eq_zero.mp hprod).resolve_right (pow_ne_zero 2 hβ))
        exact hab
      · intro r
        simpa [RingHom.algebraMap_toAlgebra, K, L, hq, residueFieldMap] using hebase r
      · intro x y hx hy hxp hyp
        simpa only [map_add] using congrArg₂ (· + ·) hxp hyp
      · intro x y hx hy hxp hyp
        simpa only [map_mul] using congrArg₂ (· * ·) hxp hyp
    have hqeq : q.asIdeal = q'.asIdeal := by
      ext x
      constructor
      · intro hx
        apply Ideal.algebraMap_residueField_eq_zero.mp
        rw [← hmap x]
        rw [Ideal.algebraMap_residueField_eq_zero.mpr hx]
        exact map_zero e
      · intro hx
        apply Ideal.algebraMap_residueField_eq_zero.mp
        have hz : e (algebraMap S L x) = 0 := by
          rw [hmap x, Ideal.algebraMap_residueField_eq_zero.mpr hx]
        apply e.injective
        simpa only [map_zero] using hz
    exact PrimeSpectrum.ext hqeq
  have hhome : IsHomeomorph (PrimeSpectrum.comap f) :=
    (isHomeomorph_iff_continuous_isClosedMap_bijective).2
      ⟨PrimeSpectrum.continuous_comap f,
        PrimeSpectrum.isClosedMap_comap_of_isIntegral f hfint,
        ⟨hcomap_inj, hsurj⟩⟩
  refine ⟨hhome, hres, ?_⟩
  intro R' _ g
  let : Algebra R R' := g.toAlgebra
  let bc : R' →+* S ⊗[R] R' := baseChangeRingMap f g
  let : Algebra R' (S ⊗[R] R') := bc.toAlgebra
  let a : S →+* S ⊗[R] R' := baseChangeAlgebraMap f g
  let U' : Set (S ⊗[R] R') := {z | z ^ 2 ∈ bc.range ∧ z ^ 3 ∈ bc.range}
  let D : Subalgebra R' (S ⊗[R] R') := Algebra.adjoin R' U'
  have hcomp : a.comp f = bc.comp g := by
    change Algebra.TensorProduct.includeLeftRingHom.comp f =
      Algebra.TensorProduct.includeRight.toRingHom.comp g
    exact Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap
  have hleft : ∀ s : S, a s ∈ D := by
    intro s
    have hs : s ∈ Algebra.adjoin R U := by rw [hgen']; trivial
    refine Algebra.adjoin_induction (p := fun x _ => a x ∈ D) ?_ ?_ ?_ ?_ hs
    · intro x hx
      apply Algebra.subset_adjoin
      refine ⟨?_, ?_⟩
      · obtain ⟨r, hr⟩ := hx.1
        refine ⟨g r, ?_⟩
        calc
          bc (g r) = a (f r) := by
            exact congrArg (fun h : R →+* S ⊗[R] R' => h r) hcomp.symm
          _ = a (x ^ 2) := by rw [hr]
          _ = a x ^ 2 := by rw [map_pow]
      · obtain ⟨r, hr⟩ := hx.2
        refine ⟨g r, ?_⟩
        calc
          bc (g r) = a (f r) := by
            exact congrArg (fun h : R →+* S ⊗[R] R' => h r) hcomp.symm
          _ = a (x ^ 3) := by rw [hr]
          _ = a x ^ 3 := by rw [map_pow]
    · intro r
      apply Algebra.subset_adjoin
      refine ⟨?_, ?_⟩
      · refine ⟨(g r) ^ 2, ?_⟩
        have hcr : bc (g r) = a (algebraMap R S r) := by
          exact congrArg (fun h : R →+* S ⊗[R] R' => h r) hcomp.symm
        rw [map_pow, hcr]
      · refine ⟨(g r) ^ 3, ?_⟩
        have hcr : bc (g r) = a (algebraMap R S r) := by
          exact congrArg (fun h : R →+* S ⊗[R] R' => h r) hcomp.symm
        rw [map_pow, hcr]
    · intro x y hx hy hxp hyp
      simpa only [map_add] using D.add_mem hxp hyp
    · intro x y hx hy hxp hyp
      simpa only [map_mul] using D.mul_mem hxp hyp
  have hD : D = ⊤ := by
    apply top_unique
    intro z _
    refine TensorProduct.induction_on z ?_ ?_ ?_
    · exact D.zero_mem
    · intro s r'
      have hmul := D.mul_mem (hleft s) (D.algebraMap_mem r')
      change a s * bc r' ∈ D at hmul
      have hbc : bc r' = (1 : S) ⊗ₜ[R] r' := by
        simp [bc, baseChangeRingMap]
      rw [hbc] at hmul
      have ha : a s = s ⊗ₜ[R] (1 : R') := by
        simp [a, baseChangeAlgebraMap]
      rw [ha] at hmul
      simpa [Algebra.TensorProduct.tmul_mul_tmul] using hmul
    · intro x y hx hy
      exact D.add_mem hx hy
  have hgen_bc : twoThreeGenerated bc := by
    change Algebra.adjoin R' U' = ⊤
    exact hD
  have hsurj0 : Function.Surjective (PrimeSpectrum.comap
      (algebraMap R' (R' ⊗[R] S))) :=
    (Formalization.Books.Algebra.Unit30.spectrum_surjective_radical_ideal_conditions_baseChange
      f hhome.surjective g).2
  let e : (R' ⊗[R] S) ≃+* (S ⊗[R] R') :=
    (Algebra.TensorProduct.comm R R' S).toRingEquiv
  have heq : e.toRingHom.comp (algebraMap R' (R' ⊗[R] S)) = bc := by
    ext r'
    simp [e, bc, baseChangeRingMap]
  have hsurj_bc : Function.Surjective (PrimeSpectrum.comap bc) := by
    rw [← heq, PrimeSpectrum.comap_comp]
    exact hsurj0.comp
      (PrimeSpectrum.isHomeomorph_comap_of_bijective e.bijective).surjective
  have hker_bc : RingHom.ker bc ≤ nilradical R' :=
    (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical bc).1 hsurj_bc.denseRange
  refine ⟨hgen_bc, ?_⟩
  intro x hx
  exact mem_nilradical.1 (hker_bc hx)
/- Existing proof scaffold for roadmap steps 1--4; it deliberately stops
before the homeomorphism assembly and the base-change argument.
  letI : Algebra R S := f.toAlgebra
  let U : Set S := {x : S | x ^ 2 ∈ f.range ∧ x ^ 3 ∈ f.range}
  have hgen' : Algebra.adjoin R U = ⊤ := by
    simpa [U, twoThreeGenerated, generatedBy] using hgen
  have hint : Algebra.IsIntegral R S := by
    let hsub : Algebra.IsIntegral R (Algebra.adjoin R U) :=
      Algebra.IsIntegral.adjoin (by
        intro x hx
        obtain ⟨r, hr⟩ := hx.1
        apply IsIntegral.of_pow (n := 2) (by norm_num)
        rw [← hr]
        simpa [RingHom.algebraMap_toAlgebra] using
          (isIntegral_algebraMap (R := R) (A := S) (x := r)))
    constructor
    intro x
    have hx : x ∈ Algebra.adjoin R U := by rw [hgen']; trivial
    have hi := hsub.isIntegral (⟨x, hx⟩ : Algebra.adjoin R U)
    change IsIntegral R ((⟨x, hx⟩ : Algebra.adjoin R U) : S)
    exact hi.algebraMap
  have hfint : f.IsIntegral := by
    intro x
    change IsIntegral R x
    exact hint.isIntegral x
  have hker' : RingHom.ker f ≤ nilradical R := by
    intro x hx
    exact (mem_nilradical).2 (hker x hx)
  have hsurj : Function.Surjective (PrimeSpectrum.comap f) := by
    exact (PrimeSpectrum.comap_quotientMk_bijective_of_le_nilradical hker').2.comp
      (hfint.kerLift.comap_surjective f.kerLift_injective)
  have hres_surj : ∀ q : PrimeSpectrum S, Function.Surjective (residueFieldMap f q) := by
    intro q
    let K := (PrimeSpectrum.comap f q).asIdeal.ResidueField
    let L := q.asIdeal.ResidueField
    let hq := residueFieldMap f q
    letI : Algebra K L := hq.toAlgebra
    have hS : ∀ s : S, algebraMap S L s ∈ hq.range := by
      intro s
      have hs : s ∈ Algebra.adjoin R U := by rw [hgen']; trivial
      refine Algebra.adjoin_induction (p := fun x _ => algebraMap S L x ∈ hq.range)
        ?_ ?_ ?_ ?_ hs
      · intro x hx
        refine range_of_sq_cube_of_field hq (algebraMap S L x) ?_ ?_
        · obtain ⟨r, hr⟩ := hx.1
          refine ⟨algebraMap R K r, ?_⟩
          calc
            hq (algebraMap R K r) = algebraMap S L (f r) := by
              simpa [K, L, hq, residueFieldMap] using
                (Ideal.ResidueField.map_algebraMap
                  (PrimeSpectrum.comap f q).asIdeal q.asIdeal f rfl r)
            _ = algebraMap S L (x ^ 2) := by rw [hr]
            _ = algebraMap S L x ^ 2 := by rw [map_pow]
        · obtain ⟨r, hr⟩ := hx.2
          refine ⟨algebraMap R K r, ?_⟩
          calc
            hq (algebraMap R K r) = algebraMap S L (f r) := by
              simpa [K, L, hq, residueFieldMap] using
                (Ideal.ResidueField.map_algebraMap
                  (PrimeSpectrum.comap f q).asIdeal q.asIdeal f rfl r)
            _ = algebraMap S L (x ^ 3) := by rw [hr]
            _ = algebraMap S L x ^ 3 := by rw [map_pow]
      · intro r
        refine ⟨algebraMap R K r, ?_⟩
        calc
          hq (algebraMap R K r) = algebraMap S L (f r) := by
            simpa [K, L, hq, residueFieldMap] using
              (Ideal.ResidueField.map_algebraMap
                (PrimeSpectrum.comap f q).asIdeal q.asIdeal f rfl r)
          _ = algebraMap S L (algebraMap R S r) := by
            simp [RingHom.algebraMap_toAlgebra]
      · intro x y hx hy hxp hyp
        rcases hxp with ⟨a, ha⟩
        rcases hyp with ⟨b, hb⟩
        refine ⟨a + b, ?_⟩
        calc
          hq (a + b) = hq a + hq b := map_add hq a b
          _ = algebraMap S L x + algebraMap S L y := by rw [ha, hb]
          _ = algebraMap S L (x + y) := (map_add (algebraMap S L) x y).symm
      · intro x y hx hy hxp hyp
        rcases hxp with ⟨a, ha⟩
        rcases hyp with ⟨b, hb⟩
        refine ⟨a * b, ?_⟩
        calc
          hq (a * b) = hq a * hq b := map_mul hq a b
          _ = algebraMap S L x * algebraMap S L y := by rw [ha, hb]
          _ = algebraMap S L (x * y) := (map_mul (algebraMap S L) x y).symm
    have hz : Function.Surjective hq := by
      intro z
      obtain ⟨aa, bb, hbb, hz⟩ := IsFractionRing.div_surjective (S ⧸ q.asIdeal) z
      obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective aa
      obtain ⟨w, hw⟩ := Ideal.Quotient.mk_surjective bb
      obtain ⟨r, hr⟩ := hS y
      obtain ⟨s, hs⟩ := hS w
      refine ⟨r / s, ?_⟩
      rw [map_div₀, hr, hs]
      simpa [K, L, Ideal.algebraMap_quotient_residueField_mk, ← hy, ← hw] using hz
    simpa [K, L, hq] using hz
  have hres : residueFieldMapsBijective f := by
    intro q
    refine ⟨RingHom.injective _, hres_surj q⟩
  have hres_surj' : ∀ (q : PrimeSpectrum S) (I : Ideal R) [I.IsPrime]
      (hI : I = q.asIdeal.comap f),
      Function.Surjective (Ideal.ResidueField.map I q.asIdeal f hI) := by
    intro q I _ hI
    subst I
    have hh : hI = rfl := Subsingleton.elim _ _
    cases hh
    exact hres_surj q
  have hcomap_inj : Function.Injective (PrimeSpectrum.comap f) := by
    intro q q' hqq'
    have hI : q.asIdeal.comap f = q'.asIdeal.comap f := by
      simpa using congrArg PrimeSpectrum.asIdeal hqq'
    let I := q.asIdeal.comap f
    letI : I.IsPrime := (PrimeSpectrum.comap f q).isPrime
    let K := I.ResidueField
    let L := q.asIdeal.ResidueField
    let L' := q'.asIdeal.ResidueField
    let hq := Ideal.ResidueField.map I q.asIdeal f rfl
    let hq' := Ideal.ResidueField.map I q'.asIdeal f hI
    let e₁ : K ≃+* L := RingEquiv.ofBijective hq
      ⟨RingHom.injective _, hres_surj' q I rfl⟩
    let e₂ : K ≃+* L' := RingEquiv.ofBijective hq'
      ⟨RingHom.injective _, hres_surj' q' I hI⟩
    let e : L ≃+* L' := e₁.symm.trans e₂
    have hebase : ∀ r : R,
        e (hq (algebraMap R K r)) = algebraMap S L' (f r) := by
      intro r
      have hecomp : e.toRingHom.comp hq = hq' := by
        ext z
        change e₂ (e₁.symm (hq z)) = hq' z
        rw [e₁.symm_apply_apply]
        rfl
      calc
        e (hq (algebraMap R K r)) = (e.toRingHom.comp hq)
            (algebraMap R K r) := rfl
        _ = hq' (algebraMap R K r) := by rw [hecomp]
        _ = algebraMap S L' (f r) := by
          simpa [I, K, L', hq'] using
            (Ideal.ResidueField.map_algebraMap I q'.asIdeal f hI r)
    have hmap : ∀ s : S, e (algebraMap S L s) = algebraMap S L' s := by
      intro s
      have hs : s ∈ Algebra.adjoin R U := by rw [hgen']; trivial
      refine Algebra.adjoin_induction (p := fun x _ =>
        e (algebraMap S L x) = algebraMap S L' x) ?_ ?_ ?_ ?_ hs
      · intro x hx
        obtain ⟨r₂, hr₂⟩ := hx.1
        obtain ⟨r₃, hr₃⟩ := hx.2
        have hsq : e (algebraMap S L x) ^ 2 =
            algebraMap S L' x ^ 2 := by
          calc
            e (algebraMap S L x) ^ 2 =
                e ((algebraMap S L x) ^ 2) := (map_pow e _ 2).symm
            _ = e (algebraMap S L (x ^ 2)) :=
              congrArg e ((map_pow (algebraMap S L) x 2).symm)
            _ = e (hq (algebraMap R K r₂)) := by
              congr 1
              calc
                algebraMap S L (x ^ 2) = algebraMap S L (f r₂) := by rw [hr₂]
                _ = hq (algebraMap R K r₂) := by
                  symm
                  simpa [K, L, hq] using
                    (Ideal.ResidueField.map_algebraMap
                      I q.asIdeal f rfl r₂)
            _ = algebraMap S L' (f r₂) := hebase r₂
            _ = algebraMap S L' (x ^ 2) := by rw [hr₂]
            _ = algebraMap S L' x ^ 2 := by rw [map_pow]
        have hcu : e (algebraMap S L x) ^ 3 =
            algebraMap S L' x ^ 3 := by
          calc
            e (algebraMap S L x) ^ 3 =
                e ((algebraMap S L x) ^ 3) := (map_pow e _ 3).symm
            _ = e (algebraMap S L (x ^ 3)) :=
              congrArg e ((map_pow (algebraMap S L) x 3).symm)
            _ = e (hq (algebraMap R K r₃)) := by
              congr 1
              calc
                algebraMap S L (x ^ 3) = algebraMap S L (f r₃) := by rw [hr₃]
                _ = hq (algebraMap R K r₃) := by
                  symm
                  simpa [K, L, hq] using
                    (Ideal.ResidueField.map_algebraMap
                      I q.asIdeal f rfl r₃)
            _ = algebraMap S L' (f r₃) := hebase r₃
            _ = algebraMap S L' (x ^ 3) := by rw [hr₃]
            _ = algebraMap S L' x ^ 3 := by rw [map_pow]
        let α := e (algebraMap S L x)
        let β := algebraMap S L' x
        have hab : α = β := by
          by_cases hβ : β = 0
          · have hα : α ^ 2 = 0 := by simpa [α, β, hβ] using hsq
            have hα' : α * α = 0 := by simpa [pow_two] using hα
            rcases mul_eq_zero.mp hα' with hα' | hα'
            · rw [hβ]
              exact hα'
            · rw [hβ]
              exact hα'
          · have hprod : (α - β) * β ^ 2 = 0 := by
              have hsq' : α ^ 2 = β ^ 2 := by simpa [α, β] using hsq
              have hcu' : α ^ 3 = β ^ 3 := by simpa [α, β] using hcu
              calc
                (α - β) * β ^ 2 = α ^ 3 - β ^ 3 := by
                  rw [← hsq']
                  ring
                _ = 0 := sub_eq_zero.mpr hcu'
            exact sub_eq_zero.mp
              ((mul_eq_zero.mp hprod).resolve_right (pow_ne_zero 2 hβ))
        exact hab
      · intro r
        simpa [RingHom.algebraMap_toAlgebra, K, L, hq, residueFieldMap] using hebase r
      · intro x y hx hy hxp hyp
        simpa only [map_add] using congrArg₂ (· + ·) hxp hyp
      · intro x y hx hy hxp hyp
        simpa only [map_mul] using congrArg₂ (· * ·) hxp hyp
    have hqeq : q.asIdeal = q'.asIdeal := by
      ext x
      constructor
      · intro hx
        apply Ideal.algebraMap_residueField_eq_zero.mp
        rw [← hmap x]
        rw [Ideal.algebraMap_residueField_eq_zero.mpr hx, map_zero]
      · intro hx
        apply Ideal.algebraMap_residueField_eq_zero.mp
        have hz : e (algebraMap S L x) = 0 := by
          rw [hmap x, Ideal.algebraMap_residueField_eq_zero.mpr hx, map_zero]
        exact e.injective hz
    exact PrimeSpectrum.ext hqeq -/

/-- The auxiliary powers lemma for integer polynomials in two variables. -/
theorem exists_helpWithPowers_exponent
    (p n m : ℕ) (hp : p.Prime) (hn : 0 < n) (hm : 0 < m) :
    ∃ a : ℕ,
      (MvPolynomial.X (0 : Fin 2) + MvPolynomial.X (1 : Fin 2)) ^ (p ^ a) ∈
          helpWithPowersSubalgebra p n m ∧
        (p ^ a : MvPolynomial (Fin 2) ℤ) *
            (MvPolynomial.X (0 : Fin 2) + MvPolynomial.X (1 : Fin 2)) ∈
          helpWithPowersSubalgebra p n m := by
  refine ⟨n * p ^ n + m * p ^ m + n + m, ?_, ?_⟩
  · let a : ℕ := n * p ^ n + m * p ^ m + n + m
    let A := helpWithPowersSubalgebra p n m
    change (MvPolynomial.X (0 : Fin 2) + MvPolynomial.X (1 : Fin 2)) ^ (p ^ a) ∈ A
    rw [(Commute.all (MvPolynomial.X (0 : Fin 2)) (MvPolynomial.X (1 : Fin 2))).add_pow]
    apply A.sum_mem
    intro i hi
    have hiN : i ≤ p ^ a := by
      exact Nat.le_of_lt_succ (Finset.mem_range.1 hi)
    let j : ℕ := p ^ a - i
    let r : ℕ := i % p ^ n
    let s : ℕ := j % p ^ m
    have hp_pos : 0 < p := hp.pos
    have hj : j + i = p ^ a := by
      dsimp [j]
      omega
    have hrlt : r < p ^ n := by
      exact Nat.mod_lt _ (by positivity)
    have hslt : s < p ^ m := by
      exact Nat.mod_lt _ (by positivity)
    have hidecomp : i = p ^ n * (i / p ^ n) + r := by
      have hmod := Nat.mod_add_div i (p ^ n)
      dsimp [r]
      omega
    have hjdecomp : j = p ^ m * (j / p ^ m) + s := by
      have hmod := Nat.mod_add_div j (p ^ m)
      dsimp [s]
      omega
    have hchoose : p ^ (n * r + m * s) ∣ (p ^ a).choose i := by
      by_cases hri : r = 0
      · by_cases hsj : s = 0
        · simp [hri, hsj]
        · have hjpos : 0 < j := by
            by_contra hj0
            have hjz : j = 0 := Nat.eq_zero_of_not_pos hj0
            apply hsj
            simp [s, hjz]
          have hfacj : j.factorization p < m := by
            by_contra hfac
            have hdvd : p ^ m ∣ j :=
              (hp.pow_dvd_iff_le_factorization (Nat.ne_of_gt hjpos)).2
                (Nat.le_of_not_gt hfac)
            exact hsj (by simpa [s] using Nat.mod_eq_zero_of_dvd hdvd)
          have hchoosefac :
              ((p ^ a).choose j).factorization p = a - j.factorization p :=
            Nat.factorization_choose_prime_pow hp (by omega) (Nat.ne_of_gt hjpos)
          have hchooseeq : (p ^ a).choose i = (p ^ a).choose j := by
            dsimp [j]
            exact (Nat.choose_symm hiN).symm
          apply (hp.pow_dvd_iff_le_factorization (Nat.choose_ne_zero hiN)).2
          rw [hchooseeq, hchoosefac]
          have hsle : s ≤ p ^ m - 1 := by omega
          have hms : m * s ≤ m * (p ^ m - 1) := Nat.mul_le_mul_left _ hsle
          have hmuln : n * (p ^ n - 1) = n * p ^ n - n := by
            rw [Nat.mul_sub_left_distrib]
            simp
          have hmulm : m * (p ^ m - 1) = m * p ^ m - m := by
            rw [Nat.mul_sub_left_distrib]
            simp
          dsimp [a]
          simp [hri] at *
          omega
      · have hipos : 0 < i := by
          by_contra hi0
          have hiz : i = 0 := Nat.eq_zero_of_not_pos hi0
          apply hri
          simp [r, hiz]
        have hfaci : i.factorization p < n := by
          by_contra hfac
          have hdvd : p ^ n ∣ i :=
            (hp.pow_dvd_iff_le_factorization (Nat.ne_of_gt hipos)).2
              (Nat.le_of_not_gt hfac)
          exact hri (by simpa [r] using Nat.mod_eq_zero_of_dvd hdvd)
        have hchoosefac :
            ((p ^ a).choose i).factorization p = a - i.factorization p :=
          Nat.factorization_choose_prime_pow hp hiN (Nat.ne_of_gt hipos)
        apply (hp.pow_dvd_iff_le_factorization (Nat.choose_ne_zero hiN)).2
        rw [hchoosefac]
        have hrle : r ≤ p ^ n - 1 := by omega
        have hsle : s ≤ p ^ m - 1 := by omega
        have hnr : n * r ≤ n * (p ^ n - 1) := Nat.mul_le_mul_left _ hrle
        have hms : m * s ≤ m * (p ^ m - 1) := Nat.mul_le_mul_left _ hsle
        have hmuln : n * (p ^ n - 1) = n * p ^ n - n := by
          rw [Nat.mul_sub_left_distrib]
          simp
        have hmulm : m * (p ^ m - 1) = m * p ^ m - m := by
          rw [Nat.mul_sub_left_distrib]
          simp
        dsimp [a]
        omega
    have hxp : MvPolynomial.X (0 : Fin 2) ^ (p ^ n) ∈ A :=
      Algebra.subset_adjoin (by simp)
    have hyp : MvPolynomial.X (1 : Fin 2) ^ (p ^ m) ∈ A :=
      Algebra.subset_adjoin (by simp)
    have hxr : (p ^ n : MvPolynomial (Fin 2) ℤ) * MvPolynomial.X (0 : Fin 2) ∈ A :=
      Algebra.subset_adjoin (by simp)
    have hyr : (p ^ m : MvPolynomial (Fin 2) ℤ) * MvPolynomial.X (1 : Fin 2) ∈ A :=
      Algebra.subset_adjoin (by simp)
    have hxterm : (p ^ (n * r) : MvPolynomial (Fin 2) ℤ) *
        MvPolynomial.X (0 : Fin 2) ^ i ∈ A := by
      have hpow : (MvPolynomial.X (0 : Fin 2) : MvPolynomial (Fin 2) ℤ) ^ i =
          (MvPolynomial.X (0 : Fin 2) : MvPolynomial (Fin 2) ℤ) ^ r *
            (MvPolynomial.X (0 : Fin 2) : MvPolynomial (Fin 2) ℤ) ^
              (p ^ n * (i / p ^ n)) := by
        calc
          _ = (MvPolynomial.X (0 : Fin 2) : MvPolynomial (Fin 2) ℤ) ^
              (p ^ n * (i / p ^ n) + r) := congrArg _ hidecomp
          _ = _ := by rw [pow_add]; ac_rfl
      have hmem := A.mul_mem (A.pow_mem hxr r) (A.pow_mem hxp (i / p ^ n))
      convert hmem using 1
      rw [hpow]
      simp only [pow_mul]
      ring
    have hyterm : (p ^ (m * s) : MvPolynomial (Fin 2) ℤ) *
        MvPolynomial.X (1 : Fin 2) ^ j ∈ A := by
      have hpow : (MvPolynomial.X (1 : Fin 2) : MvPolynomial (Fin 2) ℤ) ^ j =
          (MvPolynomial.X (1 : Fin 2) : MvPolynomial (Fin 2) ℤ) ^ s *
            (MvPolynomial.X (1 : Fin 2) : MvPolynomial (Fin 2) ℤ) ^
              (p ^ m * (j / p ^ m)) := by
        calc
          _ = (MvPolynomial.X (1 : Fin 2) : MvPolynomial (Fin 2) ℤ) ^
              (p ^ m * (j / p ^ m) + s) := congrArg _ hjdecomp
          _ = _ := by rw [pow_add]; ac_rfl
      have hmem := A.mul_mem (A.pow_mem hyr s) (A.pow_mem hyp (j / p ^ m))
      convert hmem using 1
      rw [hpow]
      simp only [pow_mul]
      ring
    obtain ⟨d, hd⟩ := hchoose
    have hterm := A.mul_mem (A.algebraMap_mem d) (A.mul_mem hxterm hyterm)
    simpa [hd, Nat.cast_mul, Nat.cast_pow, pow_add, mul_assoc, mul_comm, mul_left_comm] using hterm
  · let A := helpWithPowersSubalgebra p n m
    have hx : (p ^ n : MvPolynomial (Fin 2) ℤ) * MvPolynomial.X (0 : Fin 2) ∈ A :=
      Algebra.subset_adjoin (by simp)
    have hy : (p ^ m : MvPolynomial (Fin 2) ℤ) * MvPolynomial.X (1 : Fin 2) ∈ A :=
      Algebra.subset_adjoin (by simp)
    have hpn : (p ^ (n * p ^ n + m * p ^ m + n + m) :
        MvPolynomial (Fin 2) ℤ) * MvPolynomial.X (0 : Fin 2) ∈ A := by
      have hna : n ≤ n * p ^ n + m * p ^ m + n + m := by omega
      rw [← Nat.add_sub_of_le hna, pow_add]
      simpa [mul_assoc, mul_comm, mul_left_comm] using
        A.mul_mem hx (A.algebraMap_mem (p ^ (n * p ^ n + m * p ^ m + n + m - n)))
    have hpm : (p ^ (n * p ^ n + m * p ^ m + n + m) :
        MvPolynomial (Fin 2) ℤ) * MvPolynomial.X (1 : Fin 2) ∈ A := by
      have hma : m ≤ n * p ^ n + m * p ^ m + n + m := by omega
      rw [← Nat.add_sub_of_le hma, pow_add]
      simpa [mul_assoc, mul_comm, mul_left_comm] using
        A.mul_mem hy (A.algebraMap_mem (p ^ (n * p ^ n + m * p ^ m + n + m - m)))
    rw [mul_add]
    exact A.add_mem hpn hpm

/-- The corrected field-extension classification for the `p`-power
    generation condition. -/
theorem pPowerFieldGenerated_iff
    {k k' : Type*} [Field k] [Field k'] [Algebra k k']
    (p : ℕ) (hp : p.Prime) :
    pPowerFieldGenerated (k := k) (k' := k') p ↔
      Function.Surjective (algebraMap k k') ∨
        ∃ _ : CharP k p, ∃ _ : CharP k' p, IsPurelyInseparable k k' := by
  classical
  let T : Set k' := {x : k' | ∃ n : ℕ, 0 < n ∧
    x ^ (p ^ n) ∈ (algebraMap k k').range ∧
      (p ^ n : k') * x ∈ (algebraMap k k').range}
  change IntermediateField.adjoin k T = ⊤ ↔ _
  constructor
  · intro hgen
    by_cases hsurj : Function.Surjective (algebraMap k k')
    · exact Or.inl hsurj
    · have hchar' : CharP k' p := by
        apply (CharP.charP_iff_prime_eq_zero hp).2
        by_contra hp0
        have hT : T ⊆ (⊥ : IntermediateField k k') := by
          intro x hx
          obtain ⟨n, hn, _hxpow, ⟨y, hy⟩⟩ := hx
          change ∃ z : k, algebraMap k k' z = x
          refine ⟨(p ^ n : k)⁻¹ * y, ?_⟩
          rw [map_mul, map_inv₀, map_pow, map_natCast, hy]
          field_simp
        have hle : IntermediateField.adjoin k T ≤ (⊥ : IntermediateField k k') :=
          IntermediateField.adjoin_le_iff.mpr hT
        have htop : (⊤ : IntermediateField k k') ≤ (⊥ : IntermediateField k k') := by
          rw [← hgen]
          exact hle
        apply hsurj
        intro x
        have hx : x ∈ (⊥ : IntermediateField k k') := htop trivial
        exact hx
      have hchar : CharP k p := (Algebra.charP_iff k k' p).mpr hchar'
      let : CharP k p := hchar
      let : ExpChar k p := ExpChar.prime hp
      have hpureAdjoin : IsPurelyInseparable k (IntermediateField.adjoin k T) :=
        (IntermediateField.isPurelyInseparable_adjoin_iff_pow_mem k k' p).2
          (fun x hx ↦ by
            obtain ⟨n, hn, ⟨y, hy⟩, _hxmul⟩ := hx
            exact ⟨n, y, hy⟩)
      have hpureTop : IsPurelyInseparable k (⊤ : IntermediateField k k') := by
        rw [← hgen]
        exact hpureAdjoin
      let : IsPurelyInseparable k (⊤ : IntermediateField k k') := hpureTop
      exact Or.inr ⟨hchar, hchar', IntermediateField.topEquiv.isPurelyInseparable⟩
  · rintro (hsurj | ⟨hk, hk', hpure⟩)
    · apply top_unique
      intro x _
      obtain ⟨y, hy⟩ := hsurj (x ^ p)
      obtain ⟨z, hz⟩ := hsurj ((p : k') * x)
      exact IntermediateField.subset_adjoin k _ ⟨1, by simp, ⟨y, by simpa using hy⟩,
        ⟨z, by simpa using hz⟩⟩
    · let : CharP k p := hk
      let : CharP k' p := hk'
      let : ExpChar k p := ExpChar.prime hp
      let : IsPurelyInseparable k k' := hpure
      apply top_unique
      intro x _
      obtain ⟨n, y, hy⟩ := IsPurelyInseparable.pow_mem k p x
      by_cases hn : 0 < n
      · have hp0 : (p : k') = 0 := CharP.cast_eq_zero k' p
        have hpn : (p : k') ^ n = 0 := by rw [hp0, zero_pow hn.ne']
        exact IntermediateField.subset_adjoin k _ ⟨n, hn, ⟨y, hy⟩,
          ⟨0, by rw [hpn, zero_mul]; simp⟩⟩
      · have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
        subst n
        exact IntermediateField.subset_adjoin k _ ⟨1, by simp, ⟨y ^ p, by
          rw [map_pow, hy]
          simp⟩, ⟨0, by simp⟩⟩

/-- The `p`-power ring-map criterion, including its residue-field statement
    and stability under arbitrary base change. -/
theorem pPowerGenerated_locallyNilpotentKernel
    {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (p : ℕ)
    (hp : p.Prime) (hgen : pPowerGenerated f p) (hker : locallyNilpotentKernel f) :
    IsHomeomorph (PrimeSpectrum.comap f) ∧ pResidueFieldProperties f p ∧
      ∀ (R' : Type*) [CommRing R'] (g : R →+* R'),
        pPowerGenerated (baseChangeRingMap f g) p ∧
          locallyNilpotentKernel (baseChangeRingMap f g) := by
  let : Algebra R S := f.toAlgebra
  let T : Set S := {x : S | ∃ n : ℕ, 0 < n ∧
    x ^ (p ^ n) ∈ f.range ∧ (p ^ n : S) * x ∈ f.range}
  have hgen' : Algebra.adjoin R T = ⊤ := by
    simpa [T, pPowerGenerated, generatedBy] using hgen
  let B : Subalgebra R S :=
    { carrier := T
      zero_mem' := by
        refine ⟨1, by simp, ?_, ?_⟩
        · exact ⟨0, by simp [hp.ne_zero]⟩
        · exact ⟨0, by simp⟩
      one_mem' := by
        refine ⟨1, by simp, ?_, ?_⟩
        · exact ⟨1, by simp⟩
        · exact ⟨p, by simp⟩
      add_mem' := by
        rintro x y ⟨n, hn, hxn, hnx⟩ ⟨m, hm, hym, hmy⟩
        obtain ⟨a, ha1, ha2⟩ := exists_helpWithPowers_exponent p n m hp hn hm
        let C : Subalgebra ℤ S :=
          { carrier := f.range
            zero_mem' := ⟨0, by simp⟩
            one_mem' := ⟨1, by simp⟩
            add_mem' := by
              rintro _ _ ⟨u, rfl⟩ ⟨v, rfl⟩
              exact ⟨u + v, by simp⟩
            mul_mem' := by
              rintro _ _ ⟨u, rfl⟩ ⟨v, rfl⟩
              exact ⟨u * v, by simp⟩
            algebraMap_mem' := by
              intro z
              exact ⟨z, by simp⟩ }
        let e : MvPolynomial (Fin 2) ℤ →ₐ[ℤ] S :=
          { MvPolynomial.eval₂Hom (Int.castRingHom S)
              (fun i : Fin 2 => if i = 0 then x else y) with
            commutes' := by intro z; simp }
        have he : ∀ z ∈ helpWithPowersSubalgebra p n m, e z ∈ C := by
          intro z hz
          have hle : helpWithPowersSubalgebra p n m ≤ C.comap e :=
            Algebra.adjoin_le (by
              rintro z (rfl | rfl | rfl | rfl)
              · simpa [e, C] using hxn
              · simpa [e, C] using hnx
              · simpa [e, C] using hym
              · simpa [e, C] using hmy)
          exact hle hz
        refine ⟨a + 1, by omega, ?_, ?_⟩
        · have hz := C.pow_mem (he _ ha1) p
          have hz' : ((x + y) ^ (p ^ a)) ^ p ∈ f.range := by
            simpa [e, C] using hz
          change (x + y) ^ (p ^ (a + 1)) ∈ f.range
          simpa [pow_succ, pow_mul] using hz'
        · have hz := C.mul_mem (C.algebraMap_mem p) (he _ ha2)
          simpa [e, C, pow_succ, mul_comm, mul_left_comm, mul_assoc] using hz
      mul_mem' := by
        rintro x y ⟨n, hn, hxn, hnx⟩ ⟨m, hm, hym, hmy⟩
        refine ⟨n + m, by omega, ?_, ?_⟩
        · obtain ⟨u, hu⟩ := hxn
          obtain ⟨v, hv⟩ := hym
          refine ⟨u ^ (p ^ m) * v ^ (p ^ n), ?_⟩
          simp only [map_mul, map_pow, hu, hv]
          rw [← pow_mul, ← pow_mul, pow_add, mul_pow]
          simp [Nat.mul_comm (p ^ m) (p ^ n)]
        · obtain ⟨u, hu⟩ := hnx
          obtain ⟨v, hv⟩ := hmy
          refine ⟨u * v, ?_⟩
          rw [map_mul, hu, hv]
          simp [pow_add, mul_comm, mul_left_comm, mul_assoc]
      algebraMap_mem' := by
        intro r
        refine ⟨1, by simp, ?_, ?_⟩
        · exact ⟨r ^ (p ^ 1), by simp [RingHom.algebraMap_toAlgebra]⟩
        · exact ⟨(p ^ 1 : R) * r, by simp [RingHom.algebraMap_toAlgebra]⟩ }
  have hBT : B = ⊤ := by
    apply top_unique
    rw [← hgen']
    exact Algebra.adjoin_le (by intro x hx; exact hx)
  have hpower : ∀ x : S, ∃ n : ℕ, 0 < n ∧ x ^ (p ^ n) ∈ f.range ∧
      (p ^ n : S) * x ∈ f.range := by
    intro x
    have hx : x ∈ B := by rw [hBT]; trivial
    exact hx
  have hpower' : powerSurjective f := by
    intro x
    obtain ⟨n, hn, ⟨r, hr⟩, _⟩ := hpower x
    exact ⟨p ^ n, pow_pos hp.pos n, r, hr⟩
  have hmain := powerSurjective_locallyNilpotentKernel f hpower' hker
  refine ⟨hmain.1, ?_, ?_⟩
  · intro q
    let K := (PrimeSpectrum.comap f q).asIdeal.ResidueField
    let L := q.asIdeal.ResidueField
    let : Algebra K L := (residueFieldMap f q).toAlgebra
    have hgenq : pPowerFieldGenerated (k := K) (k' := L) p := by
      change IntermediateField.adjoin K
        {z : L | ∃ n : ℕ, 0 < n ∧ z ^ (p ^ n) ∈
          (algebraMap K L).range ∧ (p ^ n : L) * z ∈ (algebraMap K L).range} = ⊤
      apply top_unique
      intro z hz
      obtain ⟨aa, bb, hbb, hzdiv⟩ := IsFractionRing.div_surjective (S ⧸ q.asIdeal) z
      obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective aa
      obtain ⟨w, hw⟩ := Ideal.Quotient.mk_surjective bb
      obtain ⟨n, hn, ⟨r, hr⟩, ⟨r₁, hr₁⟩⟩ := hpower y
      obtain ⟨m, hm, ⟨s, hs⟩, ⟨s₁, hs₁⟩⟩ := hpower w
      have hY : residueFieldMap f q (algebraMap R K r) =
          algebraMap S L y ^ (p ^ n) := by
        calc
          residueFieldMap f q (algebraMap R K r) =
              algebraMap S L (f r) := by
                simpa [K, L, residueFieldMap] using
                  (Ideal.ResidueField.map_algebraMap
                    (PrimeSpectrum.comap f q).asIdeal q.asIdeal f rfl r)
          _ = algebraMap S L (y ^ (p ^ n)) := by rw [hr]
          _ = algebraMap S L y ^ (p ^ n) := by rw [map_pow]
      have hW : residueFieldMap f q (algebraMap R K s) =
          algebraMap S L w ^ (p ^ m) := by
        calc
          residueFieldMap f q (algebraMap R K s) =
              algebraMap S L (f s) := by
                simpa [K, L, residueFieldMap] using
                  (Ideal.ResidueField.map_algebraMap
                    (PrimeSpectrum.comap f q).asIdeal q.asIdeal f rfl s)
          _ = algebraMap S L (w ^ (p ^ m)) := by rw [hs]
          _ = algebraMap S L w ^ (p ^ m) := by rw [map_pow]
      have hYr : residueFieldMap f q (algebraMap R K r₁) =
          (p ^ n : L) * algebraMap S L y := by
        calc
          residueFieldMap f q (algebraMap R K r₁) =
              algebraMap S L (f r₁) := by
                simpa [K, L, residueFieldMap] using
                  (Ideal.ResidueField.map_algebraMap
                    (PrimeSpectrum.comap f q).asIdeal q.asIdeal f rfl r₁)
          _ = algebraMap S L ((p ^ n : S) * y) := by rw [hr₁]
          _ = (p ^ n : L) * algebraMap S L y := by simp [map_mul, map_natCast]
      have hWr : residueFieldMap f q (algebraMap R K s₁) =
          (p ^ m : L) * algebraMap S L w := by
        calc
          residueFieldMap f q (algebraMap R K s₁) =
              algebraMap S L (f s₁) := by
                simpa [K, L, residueFieldMap] using
                  (Ideal.ResidueField.map_algebraMap
                    (PrimeSpectrum.comap f q).asIdeal q.asIdeal f rfl s₁)
          _ = algebraMap S L ((p ^ m : S) * w) := by rw [hs₁]
          _ = (p ^ m : L) * algebraMap S L w := by simp [map_mul, map_natCast]
      have hz' : algebraMap S L y / algebraMap S L w = z := by
        simpa [K, L, Ideal.algebraMap_quotient_residueField_mk, ← hy, ← hw] using hzdiv
      have hw0 : algebraMap S L w ≠ 0 := by
        have hq0 : Ideal.Quotient.mk q.asIdeal w ≠ 0 := by
          intro hzero
          have hbb0 : bb ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hbb
          apply hbb0
          rw [← hw]
          exact hzero
        intro hzero
        apply hq0
        apply (Ideal.injective_algebraMap_quotient_residueField)
        simpa only [Ideal.algebraMap_quotient_residueField_mk, map_zero] using hzero
      refine IntermediateField.subset_adjoin K _ ⟨n + m, by omega, ?_, ?_⟩
      · refine ⟨(algebraMap R K r) ^ (p ^ m) /
          (algebraMap R K s) ^ (p ^ n), ?_⟩
        calc
          residueFieldMap f q
              ((algebraMap R K r) ^ (p ^ m) /
                (algebraMap R K s) ^ (p ^ n)) =
              (algebraMap S L y ^ (p ^ n)) ^ (p ^ m) /
                (algebraMap S L w ^ (p ^ m)) ^ (p ^ n) := by
                  rw [map_div₀, map_pow, map_pow, hY, hW]
          _ = (algebraMap S L y / algebraMap S L w) ^
                (p ^ n * p ^ m) := by
                  rw [← pow_mul, ← pow_mul, div_pow]
                  rw [Nat.mul_comm (p ^ m) (p ^ n)]
          _ = z ^ (p ^ (n + m)) := by rw [hz', pow_add]
      · by_cases hpL : (p : L) = 0
        · refine ⟨0, ?_⟩
          have hnm : 0 < n + m := by omega
          have hpow : (p : L) ^ (n + m) = 0 := by
            rw [hpL, zero_pow hnm.ne']
          rw [map_zero, hpow, zero_mul]
        · refine ⟨(algebraMap R K r₁) * (p ^ m : K) ^ 2 /
              algebraMap R K s₁, ?_⟩
          change residueFieldMap f q
              ((algebraMap R K r₁) * (p ^ m : K) ^ 2 /
                algebraMap R K s₁) = (p ^ (n + m) : L) * z
          rw [map_div₀, map_mul, map_pow, hYr, hWr, map_pow, map_natCast]
          have hyz : algebraMap S L y = z * algebraMap S L w :=
            (div_eq_iff hw0).mp hz'
          field_simp [hpL, hw0]
          rw [hyz]
          rw [pow_add]
          ring
    exact ⟨hgenq, (pPowerFieldGenerated_iff p hp).mp hgenq⟩
  · intro R' _ g
    let : Algebra R R' := g.toAlgebra
    let bc : R' →+* S ⊗[R] R' := baseChangeRingMap f g
    let : Algebra R' (S ⊗[R] R') := bc.toAlgebra
    let T' : Set (S ⊗[R] R') := {x : S ⊗[R] R' | ∃ n : ℕ, 0 < n ∧
      x ^ (p ^ n) ∈ bc.range ∧ (p ^ n : S ⊗[R] R') * x ∈ bc.range}
    let D : Subalgebra R' (S ⊗[R] R') :=
      { carrier := T'
        zero_mem' := by
          refine ⟨1, by simp, ?_, ?_⟩
          · exact ⟨0, by simp [hp.ne_zero]⟩
          · exact ⟨0, by simp⟩
        one_mem' := by
          refine ⟨1, by simp, ?_, ?_⟩
          · exact ⟨1, by simp⟩
          · exact ⟨p, by simp⟩
        add_mem' := by
          rintro x y ⟨n, hn, hxn, hnx⟩ ⟨m, hm, hym, hmy⟩
          obtain ⟨a, ha1, ha2⟩ := exists_helpWithPowers_exponent p n m hp hn hm
          let C : Subalgebra ℤ (S ⊗[R] R') :=
            { carrier := bc.range
              zero_mem' := ⟨0, by simp⟩
              one_mem' := ⟨1, by simp⟩
              add_mem' := by
                rintro _ _ ⟨u, rfl⟩ ⟨v, rfl⟩
                exact ⟨u + v, by simp⟩
              mul_mem' := by
                rintro _ _ ⟨u, rfl⟩ ⟨v, rfl⟩
                exact ⟨u * v, by simp⟩
              algebraMap_mem' := by
                intro z
                exact ⟨z, by simp⟩ }
          let e : MvPolynomial (Fin 2) ℤ →ₐ[ℤ] (S ⊗[R] R') :=
            { MvPolynomial.eval₂Hom (Int.castRingHom (S ⊗[R] R'))
                (fun i : Fin 2 => if i = 0 then x else y) with
              commutes' := by intro z; simp }
          have he : ∀ z ∈ helpWithPowersSubalgebra p n m, e z ∈ C := by
            intro z hz
            have hle : helpWithPowersSubalgebra p n m ≤ C.comap e :=
              Algebra.adjoin_le (by
                rintro z (rfl | rfl | rfl | rfl)
                · simpa [e, C] using hxn
                · simpa [e, C] using hnx
                · simpa [e, C] using hym
                · simpa [e, C] using hmy)
            exact hle hz
          refine ⟨a + 1, by omega, ?_, ?_⟩
          · have hz := C.pow_mem (he _ ha1) p
            have hz' : ((x + y) ^ (p ^ a)) ^ p ∈ bc.range := by
              simpa [e, C] using hz
            change (x + y) ^ (p ^ (a + 1)) ∈ bc.range
            simpa [pow_succ, pow_mul] using hz'
          · have hz := C.mul_mem (C.algebraMap_mem p) (he _ ha2)
            simpa [e, C, pow_succ, mul_comm, mul_left_comm, mul_assoc] using hz
        mul_mem' := by
          rintro x y ⟨n, hn, hxn, hnx⟩ ⟨m, hm, hym, hmy⟩
          refine ⟨n + m, by omega, ?_, ?_⟩
          · obtain ⟨u, hu⟩ := hxn
            obtain ⟨v, hv⟩ := hym
            refine ⟨u ^ (p ^ m) * v ^ (p ^ n), ?_⟩
            simp only [map_mul, map_pow, hu, hv]
            rw [← pow_mul, ← pow_mul, pow_add, mul_pow]
            simp [Nat.mul_comm (p ^ m) (p ^ n)]
          · obtain ⟨u, hu⟩ := hnx
            obtain ⟨v, hv⟩ := hmy
            refine ⟨u * v, ?_⟩
            rw [map_mul, hu, hv]
            simp [pow_add, mul_comm, mul_left_comm, mul_assoc]
        algebraMap_mem' := by
          intro r
          refine ⟨1, by simp, ?_, ?_⟩
          · exact ⟨r ^ (p ^ 1), by simp [RingHom.algebraMap_toAlgebra]⟩
          · exact ⟨(p ^ 1 : R') * r, by simp [RingHom.algebraMap_toAlgebra]⟩ }
    let a : S →+* S ⊗[R] R' := baseChangeAlgebraMap f g
    have hcomp : a.comp f = bc.comp g := by
      change Algebra.TensorProduct.includeLeftRingHom.comp f =
        Algebra.TensorProduct.includeRight.toRingHom.comp g
      exact Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap
    have hleft : ∀ s : S, a s ∈ D := by
      intro s
      have hs : s ∈ Algebra.adjoin R T := by rw [hgen']; trivial
      refine Algebra.adjoin_induction (p := fun x _ => a x ∈ D) ?_ ?_ ?_ ?_ hs
      · intro x hx
        rcases hx with ⟨n, hn, hxn, hnx⟩
        refine ⟨n, hn, ?_, ?_⟩
        · obtain ⟨r, hr⟩ := hxn
          refine ⟨g r, ?_⟩
          calc
            bc (g r) = a (f r) := by
              exact congrArg (fun h : R →+* S ⊗[R] R' => h r) hcomp.symm
            _ = a (x ^ (p ^ n)) := by rw [hr]
            _ = a x ^ (p ^ n) := by rw [map_pow]
        · obtain ⟨r, hr⟩ := hnx
          refine ⟨g r, ?_⟩
          calc
            bc (g r) = a (f r) := by
              exact congrArg (fun h : R →+* S ⊗[R] R' => h r) hcomp.symm
            _ = a ((p ^ n : S) * x) := by rw [hr]
            _ = (p ^ n : S ⊗[R] R') * a x := by
              simp [map_mul, map_natCast]
      · intro r
        refine ⟨1, by simp, ?_, ?_⟩
        · exact ⟨(g r) ^ p, by
            have hcr : bc (g r) = a (algebraMap R S r) := by
              exact congrArg (fun h : R →+* S ⊗[R] R' => h r) hcomp.symm
            rw [map_pow, hcr]
            simp⟩
        · exact ⟨(p : R') * g r, by
            have hcr : bc (g r) = a (algebraMap R S r) := by
              exact congrArg (fun h : R →+* S ⊗[R] R' => h r) hcomp.symm
            rw [map_mul, hcr]
            simp⟩
      · intro x y hx hy hxp hyp
        simpa only [map_add] using D.add_mem hxp hyp
      · intro x y hx hy hxp hyp
        simpa only [map_mul] using D.mul_mem hxp hyp
    have hD : D = ⊤ := by
      apply top_unique
      intro z _
      refine TensorProduct.induction_on z ?_ ?_ ?_
      · exact D.zero_mem
      · intro s r'
        have hbc : bc r' = (1 : S) ⊗ₜ[R] r' := by
          simp [bc, baseChangeRingMap]
        have hmul := D.mul_mem (hleft s) (D.algebraMap_mem r')
        change a s * bc r' ∈ D at hmul
        rw [hbc] at hmul
        have ha : a s = s ⊗ₜ[R] (1 : R') := by
          simp [a, baseChangeAlgebraMap]
        rw [ha] at hmul
        simpa [Algebra.TensorProduct.tmul_mul_tmul] using hmul
      · intro x y hx hy
        exact D.add_mem hx hy
    have hpgen : pPowerGenerated bc p := by
      change Algebra.adjoin R' T' = ⊤
      apply top_unique
      intro z hz
      have hzD : z ∈ D := by rw [hD]; exact hz
      exact Algebra.subset_adjoin hzD
    refine ⟨hpgen, ?_⟩
    have hsurj0 : Function.Surjective (PrimeSpectrum.comap
        (algebraMap R' (R' ⊗[R] S))) :=
      (Formalization.Books.Algebra.Unit30.spectrum_surjective_radical_ideal_conditions_baseChange
        f hmain.1.surjective g).2
    let e : (R' ⊗[R] S) ≃+* (S ⊗[R] R') :=
      (Algebra.TensorProduct.comm R R' S).toRingEquiv
    have heq : e.toRingHom.comp (algebraMap R' (R' ⊗[R] S)) = bc := by
      ext r'
      simp [e, bc, baseChangeRingMap]
    have hsurj : Function.Surjective (PrimeSpectrum.comap bc) := by
      rw [← heq, PrimeSpectrum.comap_comp]
      exact hsurj0.comp
        (PrimeSpectrum.isHomeomorph_comap_of_bijective e.bijective).surjective
    have hker' : RingHom.ker bc ≤ nilradical R' :=
      (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical bc).1 hsurj.denseRange
    intro x hx
    exact (mem_nilradical.1 (hker' hx))

/-- Injectivity on spectra and purely inseparable residue fields are stable
    under arbitrary base change. -/
theorem radicial_baseChange
    {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (hinj : Function.Injective (PrimeSpectrum.comap f))
    (hres : residueFieldExtensionsPurelyInseparable f) :
    ∀ (R' : Type*) [CommRing R'] (g : R →+* R'),
      Function.Injective (PrimeSpectrum.comap (baseChangeRingMap f g)) ∧
        residueFieldExtensionsPurelyInseparable (baseChangeRingMap f g) := by
  intro R' _ g
  let : Algebra R S := f.toAlgebra
  let : Algebra R R' := g.toAlgebra
  let bc : R' →+* S ⊗[R] R' := baseChangeRingMap f g
  let a : S →+* S ⊗[R] R' := baseChangeAlgebraMap f g
  have hcomp : a.comp f = bc.comp g := by
    change Algebra.TensorProduct.includeLeftRingHom.comp f =
      Algebra.TensorProduct.includeRight.toRingHom.comp g
    exact Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap
  refine ⟨?_, ?_⟩
  · intro q q' hqq'
    have hbase (z : PrimeSpectrum (S ⊗[R] R')) :
        PrimeSpectrum.comap f (PrimeSpectrum.comap a z) =
          PrimeSpectrum.comap g (PrimeSpectrum.comap bc z) := by
      rw [← PrimeSpectrum.comap_comp_apply, ← PrimeSpectrum.comap_comp_apply, hcomp]
    have hqS : PrimeSpectrum.comap a q = PrimeSpectrum.comap a q' := by
      apply hinj
      calc
        PrimeSpectrum.comap f (PrimeSpectrum.comap a q) =
            PrimeSpectrum.comap g (PrimeSpectrum.comap bc q) := hbase q
        _ = PrimeSpectrum.comap g (PrimeSpectrum.comap bc q') := by rw [hqq']
        _ = PrimeSpectrum.comap f (PrimeSpectrum.comap a q') := (hbase q').symm
    let qS : PrimeSpectrum S := PrimeSpectrum.comap a q
    let p' : PrimeSpectrum R' := PrimeSpectrum.comap bc q
    let p : PrimeSpectrum R := PrimeSpectrum.comap f qS
    have hfp : p.asIdeal = p'.asIdeal.comap g := by
      have hp := congrArg PrimeSpectrum.asIdeal (hbase q)
      simpa [p, p', qS] using hp
    let k := p.asIdeal.ResidueField
    let K := p'.asIdeal.ResidueField
    let L := qS.asIdeal.ResidueField
    let kmap := Ideal.ResidueField.map p.asIdeal p'.asIdeal g hfp
    let lmap := residueFieldMap f qS
    let : Algebra k K := kmap.toAlgebra
    let : Algebra k L := lmap.toAlgebra
    let : SMul R K :=
      (Module.compHom K ((algebraMap R' K).comp g)).toSMul
    let : Module R K := Module.compHom K ((algebraMap R' K).comp g)
    let : SMul R L :=
      (Module.compHom L ((algebraMap S L).comp f)).toSMul
    let : Module R L := Module.compHom L ((algebraMap S L).comp f)
    let : Algebra R K :=
      ((algebraMap R' K).comp g).toAlgebra
    let : Algebra R L :=
      ((algebraMap S L).comp f).toAlgebra
    have hpure : IsPurelyInseparable k L := by
      change IsPurelyInseparable (PrimeSpectrum.comap f qS).asIdeal.ResidueField L
      exact hres qS
    have hscalarL (r : R) :
        lmap (algebraMap R k r) = algebraMap S L (f r) := by
      simpa [k, L, lmap, residueFieldMap, p] using
        (Ideal.ResidueField.map_algebraMap
          (PrimeSpectrum.comap f qS).asIdeal qS.asIdeal f rfl r)
    have hscalarK (r : R) :
        kmap (algebraMap R k r) = algebraMap R' K (g r) := by
      simp [k, K, kmap]
    let F := K ⊗[k] L
    let : Algebra R F :=
      ((algebraMap k F).comp (algebraMap R k)).toAlgebra
    let smap : S →+* F :=
      (Algebra.TensorProduct.includeRight : L →ₐ[k] F).toRingHom.comp
        (algebraMap S L)
    let rmap : R' →+* F :=
      (Algebra.TensorProduct.includeLeft : K →ₐ[k] F).toRingHom.comp
        (algebraMap R' K)
    let smapAlg : S →ₐ[R] F := AlgHom.mk' smap (by
      intro r x
      change (1 : K) ⊗ₜ[k]
          (algebraMap S L ((algebraMap R S r) * x)) =
        (algebraMap k F (algebraMap R k r)) *
          ((1 : K) ⊗ₜ[k] algebraMap S L x)
      rw [RingHom.algebraMap_toAlgebra f, map_mul, ← hscalarL r]
      change (1 : K) ⊗ₜ[k]
          (lmap (algebraMap R k r) * algebraMap S L x) =
        (kmap (algebraMap R k r) ⊗ₜ[k] (1 : L)) *
          ((1 : K) ⊗ₜ[k] algebraMap S L x)
      have htmul :
          kmap (algebraMap R k r) ⊗ₜ[k] (1 : L) =
            (1 : K) ⊗ₜ[k] lmap (algebraMap R k r) := by
        change (algebraMap k K (algebraMap R k r)) ⊗ₜ[k] (1 : L) =
          (1 : K) ⊗ₜ[k] algebraMap k L (algebraMap R k r)
        exact Algebra.TensorProduct.tmul_one_eq_one_tmul _
      calc
        (1 : K) ⊗ₜ[k]
              (lmap (algebraMap R k r) * algebraMap S L x) =
            ((1 : K) ⊗ₜ[k] lmap (algebraMap R k r)) *
              ((1 : K) ⊗ₜ[k] algebraMap S L x) := by
                simp
        _ = (kmap (algebraMap R k r) ⊗ₜ[k] (1 : L)) *
              ((1 : K) ⊗ₜ[k] algebraMap S L x) := by
                rw [htmul]
    )
    let rmapAlg : R' →ₐ[R] F := AlgHom.mk' rmap (by
      intro r x
      simp [rmap, F, k, K, kmap, hscalarK r, Algebra.smul_def,
        RingHom.algebraMap_toAlgebra])
    let : IsScalarTower R R F := ⟨by
      intro r s x
      exact smul_assoc r s x⟩
    let : IsScalarTower R R S := ⟨by
      intro r s x
      exact smul_assoc r s x⟩
    let dmap : (S ⊗[R] R') →ₐ[R] F :=
      Algebra.TensorProduct.lift (R := R) (S := R) (A := S) (B := R') (C := F)
        smapAlg rmapAlg (by
        intro r s
        exact Commute.all _ _)
    let Q := q.asIdeal.ResidueField
    let qK : K →+* Q :=
      Ideal.ResidueField.map p'.asIdeal q.asIdeal bc rfl
    let qL : L →+* Q :=
      Ideal.ResidueField.map qS.asIdeal q.asIdeal a rfl
    let : Algebra K Q := qK.toAlgebra
    let : Algebra k Q :=
      ((algebraMap K Q).comp (algebraMap k K)).toAlgebra
    have hbaseQ : qK.comp kmap = qL.comp lmap := by
      ext c
      change qK (kmap (algebraMap R k c)) =
        qL (lmap (algebraMap R k c))
      calc
        qK (kmap (algebraMap R k c)) =
            qK (algebraMap R' K (g c)) := by rw [hscalarK]
        _ = algebraMap (S ⊗[R] R') Q (bc (g c)) := by
          simpa [Q, qK] using
            (Ideal.ResidueField.map_algebraMap
              p'.asIdeal q.asIdeal bc rfl (g c))
        _ = algebraMap (S ⊗[R] R') Q (a (f c)) := by
          congr 1
          exact congrArg (fun h : R →+* S ⊗[R] R' => h c) hcomp.symm
        _ = qL (algebraMap S L (f c)) := by
          simpa [Q, qL] using
            (Ideal.ResidueField.map_algebraMap
              qS.asIdeal q.asIdeal a rfl (f c)).symm
        _ = qL (lmap (algebraMap R k c)) := by rw [hscalarL]
    let qKAlg : K →ₐ[k] Q := AlgHom.mk' qK (by
      intro c x
      change qK (algebraMap k K c * x) =
        algebraMap k Q c * qK x
      rw [map_mul]
      congr 1)
    let qLAlg : L →ₐ[k] Q := AlgHom.mk' qL (by
      intro c x
      change qL (algebraMap k L c * x) =
        algebraMap k Q c * qL x
      rw [map_mul]
      have hc : qL (algebraMap k L c) = algebraMap k Q c := by
        change qL (lmap c) = qK (kmap c)
        exact (congrArg (fun h : k →+* Q => h c) hbaseQ).symm
      rw [hc])
    let hcomm : ∀ x y, Commute (qKAlg x) (qLAlg y) := by
      intro x y
      exact Commute.all _ _
    let qF : F →ₐ[k] Q := Algebra.TensorProduct.lift qKAlg qLAlg hcomm
    have hqF (x : S ⊗[R] R') :
        qF (dmap x) = algebraMap (S ⊗[R] R') Q x := by
      have heq : qF.toRingHom.comp dmap.toRingHom =
          algebraMap (S ⊗[R] R') Q := by
        apply Algebra.TensorProduct.ringHom_ext
        · ext s
          change qF (dmap (Algebra.TensorProduct.includeLeftRingHom s)) = _
          change qF (dmap (s ⊗ₜ[R] (1 : R'))) = _
          rw [show dmap (s ⊗ₜ[R] (1 : R')) = smapAlg s * rmapAlg 1 by rfl]
          simp only [map_one, mul_one]
          have hqFs : qF (smapAlg s) =
              algebraMap (S ⊗[R] R') Q (a s) := by
            change qF (1 ⊗ₜ[k] algebraMap S L s) = _
            dsimp [qF]
            rw [Algebra.TensorProduct.lift_tmul]
            simpa [qKAlg, qLAlg, qL, Q] using
              (Ideal.ResidueField.map_algebraMap
                qS.asIdeal q.asIdeal a rfl s)
          simpa [a, baseChangeAlgebraMap, bc, baseChangeRingMap,
            RingHom.algebraMap_toAlgebra] using hqFs
        · ext r'
          change qF (dmap (Algebra.TensorProduct.includeRight r')) = _
          change qF (dmap ((1 : S) ⊗ₜ[R] r')) = _
          rw [show dmap ((1 : S) ⊗ₜ[R] r') = smapAlg 1 * rmapAlg r' by rfl]
          simp only [map_one, one_mul]
          have hqFr : qF (rmapAlg r') =
              algebraMap (S ⊗[R] R') Q (bc r') := by
            change qF (algebraMap R' K r' ⊗ₜ[k] 1) = _
            dsimp [qF]
            rw [Algebra.TensorProduct.lift_tmul]
            simpa [qKAlg, qLAlg, qK, Q] using
              (Ideal.ResidueField.map_algebraMap
                p'.asIdeal q.asIdeal bc rfl r')
          simpa [bc, baseChangeRingMap, RingHom.algebraMap_toAlgebra] using hqFr
      exact congrArg (fun h : (S ⊗[R] R') →+* Q => h x) heq
    have hqS' : qS.asIdeal = q'.asIdeal.comap a := by
      have h := congrArg PrimeSpectrum.asIdeal hqS
      simpa [qS] using h
    have hp' : p'.asIdeal = q'.asIdeal.comap bc := by
      have h := congrArg PrimeSpectrum.asIdeal hqq'
      simpa [p'] using h
    let Q' := q'.asIdeal.ResidueField
    let qK' : K →+* Q' :=
      Ideal.ResidueField.map p'.asIdeal q'.asIdeal bc hp'
    let qL' : L →+* Q' :=
      Ideal.ResidueField.map qS.asIdeal q'.asIdeal a hqS'
    let : Algebra K Q' := qK'.toAlgebra
    let : Algebra k Q' :=
      ((algebraMap K Q').comp (algebraMap k K)).toAlgebra
    have hbaseQ' : qK'.comp kmap = qL'.comp lmap := by
      ext c
      change qK' (kmap (algebraMap R k c)) =
        qL' (lmap (algebraMap R k c))
      calc
        qK' (kmap (algebraMap R k c)) =
            qK' (algebraMap R' K (g c)) := by rw [hscalarK]
        _ = algebraMap (S ⊗[R] R') Q' (bc (g c)) := by
          simpa only [Q', qK'] using
            (Ideal.ResidueField.map_algebraMap
              p'.asIdeal q'.asIdeal bc hp' (g c))
        _ = algebraMap (S ⊗[R] R') Q' (a (f c)) := by
          congr 1
          exact congrArg (fun h : R →+* S ⊗[R] R' => h c) hcomp.symm
        _ = qL' (algebraMap S L (f c)) := by
          simpa only [Q', qL'] using
            (Ideal.ResidueField.map_algebraMap
              qS.asIdeal q'.asIdeal a hqS' (f c)).symm
        _ = qL' (lmap (algebraMap R k c)) := by rw [hscalarL]
    let qKAlg' : K →ₐ[k] Q' := AlgHom.mk' qK' (by
      intro c x
      change qK' (algebraMap k K c * x) =
        algebraMap k Q' c * qK' x
      rw [map_mul]
      congr 1)
    let qLAlg' : L →ₐ[k] Q' := AlgHom.mk' qL' (by
      intro c x
      change qL' (algebraMap k L c * x) =
        algebraMap k Q' c * qL' x
      rw [map_mul]
      have hc : qL' (algebraMap k L c) = algebraMap k Q' c := by
        change qL' (lmap c) = qK' (kmap c)
        exact (congrArg (fun h : k →+* Q' => h c) hbaseQ').symm
      rw [hc])
    let hcomm' : ∀ x y, Commute (qKAlg' x) (qLAlg' y) := by
      intro x y
      exact Commute.all _ _
    let qF' : F →ₐ[k] Q' := Algebra.TensorProduct.lift qKAlg' qLAlg' hcomm'
    have hqF' (x : S ⊗[R] R') :
        qF' (dmap x) = algebraMap (S ⊗[R] R') Q' x := by
      have heq : qF'.toRingHom.comp dmap.toRingHom =
          algebraMap (S ⊗[R] R') Q' := by
        apply Algebra.TensorProduct.ringHom_ext
        · ext s
          change qF' (dmap (Algebra.TensorProduct.includeLeftRingHom s)) = _
          change qF' (dmap (s ⊗ₜ[R] (1 : R'))) = _
          rw [show dmap (s ⊗ₜ[R] (1 : R')) = smapAlg s * rmapAlg 1 by rfl]
          simp only [map_one, mul_one]
          have hqFs' : qF' (smapAlg s) =
              algebraMap (S ⊗[R] R') Q' (a s) := by
            change qF' (1 ⊗ₜ[k] algebraMap S L s) = _
            dsimp [qF']
            rw [Algebra.TensorProduct.lift_tmul]
            change qKAlg' 1 * qLAlg' (algebraMap S L s) = _
            rw [map_one, one_mul]
            change qL' (algebraMap S L s) = _
            exact Ideal.ResidueField.map_algebraMap
              qS.asIdeal q'.asIdeal a hqS' s
          simpa [a, baseChangeAlgebraMap, bc, baseChangeRingMap,
            RingHom.algebraMap_toAlgebra] using hqFs'
        · ext r'
          change qF' (dmap (Algebra.TensorProduct.includeRight r')) = _
          change qF' (dmap ((1 : S) ⊗ₜ[R] r')) = _
          rw [show dmap ((1 : S) ⊗ₜ[R] r') = smapAlg 1 * rmapAlg r' by rfl]
          simp only [map_one, one_mul]
          have hqFr' : qF' (rmapAlg r') =
              algebraMap (S ⊗[R] R') Q' (bc r') := by
            change qF' (algebraMap R' K r' ⊗ₜ[k] 1) = _
            dsimp [qF']
            rw [Algebra.TensorProduct.lift_tmul]
            change qKAlg' (algebraMap R' K r') * qLAlg' 1 = _
            rw [map_one, mul_one]
            change qK' (algebraMap R' K r') = _
            exact Ideal.ResidueField.map_algebraMap
              p'.asIdeal q'.asIdeal bc hp' r'
          simpa [bc, baseChangeRingMap, RingHom.algebraMap_toAlgebra] using hqFr'
      exact congrArg (fun h : (S ⊗[R] R') →+* Q' => h x) heq
    have hqFalg (y : K) : qF (algebraMap K F y) = qK y := by
      change qF ((Algebra.TensorProduct.includeLeft : K →ₐ[k] F) y) = qK y
      change (Algebra.TensorProduct.lift qKAlg qLAlg hcomm)
          ((Algebra.TensorProduct.includeLeft : K →ₐ[k] F) y) = qK y
      change ((Algebra.TensorProduct.lift qKAlg qLAlg hcomm).comp
          (Algebra.TensorProduct.includeLeft : K →ₐ[k] F)) y = qKAlg y
      rw [Algebra.TensorProduct.lift_comp_includeLeft]
    have hqFalg' (y : K) : qF' (algebraMap K F y) = qK' y := by
      change qF' ((Algebra.TensorProduct.includeLeft : K →ₐ[k] F) y) = qK' y
      change (Algebra.TensorProduct.lift qKAlg' qLAlg' hcomm')
          ((Algebra.TensorProduct.includeLeft : K →ₐ[k] F) y) = qK' y
      change ((Algebra.TensorProduct.lift qKAlg' qLAlg' hcomm').comp
          (Algebra.TensorProduct.includeLeft : K →ₐ[k] F)) y = qKAlg' y
      rw [Algebra.TensorProduct.lift_comp_includeLeft]
    have hmem : ∀ x : S ⊗[R] R', x ∈ q.asIdeal → x ∈ q'.asIdeal := by
      intro x hx
      obtain ⟨n, hn, y, hy⟩ :=
        IsPurelyInseparable.exists_pow_mem_range_tensorProduct
          (k := k) (K := L) (R := K) (dmap x)
      have hzero : qF (dmap x) = 0 := by
        rw [hqF, Ideal.algebraMap_residueField_eq_zero.mpr hx]
      have hqpow : algebraMap (S ⊗[R] R') Q' (x ^ n) = 0 := by
        calc
          algebraMap (S ⊗[R] R') Q' (x ^ n) =
              qF' (dmap (x ^ n)) := (hqF' (x ^ n)).symm
          _ = qF' ((dmap x) ^ n) := by rw [map_pow]
          _ = qF' (algebraMap K F y) := by rw [← hy]
          _ = qK' y := hqFalg' y
          _ = 0 := by
            have hqKy : qK y = 0 := by
              have hqpow0 : qF (algebraMap K F y) = 0 := by
                calc
                  qF (algebraMap K F y) = qF ((dmap x) ^ n) := by rw [hy]
                  _ = qF (dmap x) ^ n := by rw [map_pow]
                  _ = 0 := by rw [hzero, zero_pow hn.ne']
              exact hqFalg y ▸ hqpow0
            have : y = 0 := (RingHom.injective qK) (by simpa using hqKy)
            rw [this, map_zero]
      apply (q'.2.pow_mem_iff_mem _ hn).mp
      exact Ideal.algebraMap_residueField_eq_zero.mp hqpow
    have hmem' : ∀ x : S ⊗[R] R', x ∈ q'.asIdeal → x ∈ q.asIdeal := by
      intro x hx
      obtain ⟨n, hn, y, hy⟩ :=
        IsPurelyInseparable.exists_pow_mem_range_tensorProduct
          (k := k) (K := L) (R := K) (dmap x)
      have hzero : qF' (dmap x) = 0 := by
        rw [hqF', Ideal.algebraMap_residueField_eq_zero.mpr hx]
      have hqpow : algebraMap (S ⊗[R] R') Q (x ^ n) = 0 := by
        calc
          algebraMap (S ⊗[R] R') Q (x ^ n) =
              qF (dmap (x ^ n)) := (hqF (x ^ n)).symm
          _ = qF ((dmap x) ^ n) := by rw [map_pow]
          _ = qF (algebraMap K F y) := by rw [← hy]
          _ = qK y := hqFalg y
          _ = 0 := by
            have hqKy : qK' y = 0 := by
              have hqpow0 : qF' (algebraMap K F y) = 0 := by
                calc
                  qF' (algebraMap K F y) = qF' ((dmap x) ^ n) := by rw [hy]
                  _ = qF' (dmap x) ^ n := by rw [map_pow]
                  _ = 0 := by rw [hzero, zero_pow hn.ne']
              exact hqFalg' y ▸ hqpow0
            have : y = 0 := (RingHom.injective qK') (by simpa using hqKy)
            rw [this, map_zero]
      apply (q.2.pow_mem_iff_mem _ hn).mp
      exact Ideal.algebraMap_residueField_eq_zero.mp hqpow
    apply PrimeSpectrum.ext
    ext x
    exact ⟨hmem x, hmem' x⟩
  · intro q
    have hbase (z : PrimeSpectrum (S ⊗[R] R')) :
        PrimeSpectrum.comap f (PrimeSpectrum.comap a z) =
          PrimeSpectrum.comap g (PrimeSpectrum.comap bc z) := by
      rw [← PrimeSpectrum.comap_comp_apply, ← PrimeSpectrum.comap_comp_apply, hcomp]
    let qS : PrimeSpectrum S := PrimeSpectrum.comap a q
    let p' : PrimeSpectrum R' := PrimeSpectrum.comap bc q
    let p : PrimeSpectrum R := PrimeSpectrum.comap f qS
    have hfp : p.asIdeal = p'.asIdeal.comap g := by
      have hp := congrArg PrimeSpectrum.asIdeal (hbase q)
      simpa [p, p', qS] using hp
    let k := p.asIdeal.ResidueField
    let K := p'.asIdeal.ResidueField
    let L := qS.asIdeal.ResidueField
    let kmap := Ideal.ResidueField.map p.asIdeal p'.asIdeal g hfp
    let lmap := residueFieldMap f qS
    let : Algebra k K := kmap.toAlgebra
    let : Algebra k L := lmap.toAlgebra
    let : SMul R K :=
      (Module.compHom K ((algebraMap R' K).comp g)).toSMul
    let : Module R K := Module.compHom K ((algebraMap R' K).comp g)
    let : SMul R L :=
      (Module.compHom L ((algebraMap S L).comp f)).toSMul
    let : Module R L := Module.compHom L ((algebraMap S L).comp f)
    let : Algebra R K :=
      ((algebraMap R' K).comp g).toAlgebra
    let : Algebra R L :=
      ((algebraMap S L).comp f).toAlgebra
    have hpure : IsPurelyInseparable k L := by
      change IsPurelyInseparable (PrimeSpectrum.comap f qS).asIdeal.ResidueField L
      exact hres qS
    have hscalarL (r : R) :
        lmap (algebraMap R k r) = algebraMap S L (f r) := by
      simpa [k, L, lmap, residueFieldMap, p] using
        (Ideal.ResidueField.map_algebraMap
          (PrimeSpectrum.comap f qS).asIdeal qS.asIdeal f rfl r)
    have hscalarK (r : R) :
        kmap (algebraMap R k r) = algebraMap R' K (g r) := by
      simp [k, K, kmap]
    let F := K ⊗[k] L
    let : Algebra R F :=
      ((algebraMap k F).comp (algebraMap R k)).toAlgebra
    let smap : S →+* F :=
      (Algebra.TensorProduct.includeRight : L →ₐ[k] F).toRingHom.comp
        (algebraMap S L)
    let rmap : R' →+* F :=
      (Algebra.TensorProduct.includeLeft : K →ₐ[k] F).toRingHom.comp
        (algebraMap R' K)
    let smapAlg : S →ₐ[R] F := AlgHom.mk' smap (by
      intro r x
      change (1 : K) ⊗ₜ[k]
          (algebraMap S L ((algebraMap R S r) * x)) =
        (algebraMap k F (algebraMap R k r)) *
          ((1 : K) ⊗ₜ[k] algebraMap S L x)
      rw [RingHom.algebraMap_toAlgebra f, map_mul, ← hscalarL r]
      change (1 : K) ⊗ₜ[k]
          (lmap (algebraMap R k r) * algebraMap S L x) =
        (kmap (algebraMap R k r) ⊗ₜ[k] (1 : L)) *
          ((1 : K) ⊗ₜ[k] algebraMap S L x)
      have htmul :
          kmap (algebraMap R k r) ⊗ₜ[k] (1 : L) =
            (1 : K) ⊗ₜ[k] lmap (algebraMap R k r) := by
        change (algebraMap k K (algebraMap R k r)) ⊗ₜ[k] (1 : L) =
          (1 : K) ⊗ₜ[k] algebraMap k L (algebraMap R k r)
        exact Algebra.TensorProduct.tmul_one_eq_one_tmul _
      calc
        (1 : K) ⊗ₜ[k]
              (lmap (algebraMap R k r) * algebraMap S L x) =
            ((1 : K) ⊗ₜ[k] lmap (algebraMap R k r)) *
              ((1 : K) ⊗ₜ[k] algebraMap S L x) := by
                simp
        _ = (kmap (algebraMap R k r) ⊗ₜ[k] (1 : L)) *
              ((1 : K) ⊗ₜ[k] algebraMap S L x) := by
                rw [htmul]
    )
    let rmapAlg : R' →ₐ[R] F := AlgHom.mk' rmap (by
      intro r x
      simp [rmap, F, k, K, kmap, hscalarK r, Algebra.smul_def,
        RingHom.algebraMap_toAlgebra])
    let : IsScalarTower R R F := ⟨by
      intro r s x
      exact smul_assoc r s x⟩
    let : IsScalarTower R R S := ⟨by
      intro r s x
      exact smul_assoc r s x⟩
    let dmap : (S ⊗[R] R') →ₐ[R] F :=
      Algebra.TensorProduct.lift (R := R) (S := R) (A := S) (B := R') (C := F)
        smapAlg rmapAlg (by
        intro r s
        exact Commute.all _ _)
    let Q := q.asIdeal.ResidueField
    let qK : K →+* Q :=
      Ideal.ResidueField.map p'.asIdeal q.asIdeal bc rfl
    let qL : L →+* Q :=
      Ideal.ResidueField.map qS.asIdeal q.asIdeal a rfl
    let : Algebra K Q := qK.toAlgebra
    let : Algebra k Q :=
      ((algebraMap K Q).comp (algebraMap k K)).toAlgebra
    have hbaseQ : qK.comp kmap = qL.comp lmap := by
      ext c
      change qK (kmap (algebraMap R k c)) =
        qL (lmap (algebraMap R k c))
      calc
        qK (kmap (algebraMap R k c)) =
            qK (algebraMap R' K (g c)) := by rw [hscalarK]
        _ = algebraMap (S ⊗[R] R') Q (bc (g c)) := by
          simpa [Q, qK] using
            (Ideal.ResidueField.map_algebraMap
              p'.asIdeal q.asIdeal bc rfl (g c))
        _ = algebraMap (S ⊗[R] R') Q (a (f c)) := by
          congr 1
          exact congrArg (fun h : R →+* S ⊗[R] R' => h c) hcomp.symm
        _ = qL (algebraMap S L (f c)) := by
          simpa [Q, qL] using
            (Ideal.ResidueField.map_algebraMap
              qS.asIdeal q.asIdeal a rfl (f c)).symm
        _ = qL (lmap (algebraMap R k c)) := by rw [hscalarL]
    let qKAlg : K →ₐ[k] Q := AlgHom.mk' qK (by
      intro c x
      change qK (algebraMap k K c * x) =
        algebraMap k Q c * qK x
      rw [map_mul]
      congr 1)
    let qLAlg : L →ₐ[k] Q := AlgHom.mk' qL (by
      intro c x
      change qL (algebraMap k L c * x) =
        algebraMap k Q c * qL x
      rw [map_mul]
      have hc : qL (algebraMap k L c) = algebraMap k Q c := by
        change qL (lmap c) = qK (kmap c)
        exact (congrArg (fun h : k →+* Q => h c) hbaseQ).symm
      rw [hc])
    let hcomm : ∀ x y, Commute (qKAlg x) (qLAlg y) := by
      intro x y
      exact Commute.all _ _
    let qF : F →ₐ[k] Q := Algebra.TensorProduct.lift qKAlg qLAlg hcomm
    have hqF (x : S ⊗[R] R') :
        qF (dmap x) = algebraMap (S ⊗[R] R') Q x := by
      have heq : qF.toRingHom.comp dmap.toRingHom =
          algebraMap (S ⊗[R] R') Q := by
        apply Algebra.TensorProduct.ringHom_ext
        · ext s
          change qF (dmap (Algebra.TensorProduct.includeLeftRingHom s)) = _
          change qF (dmap (s ⊗ₜ[R] (1 : R'))) = _
          rw [show dmap (s ⊗ₜ[R] (1 : R')) = smapAlg s * rmapAlg 1 by rfl]
          simp only [map_one, mul_one]
          have hqFs : qF (smapAlg s) =
              algebraMap (S ⊗[R] R') Q (a s) := by
            change qF (1 ⊗ₜ[k] algebraMap S L s) = _
            dsimp [qF]
            rw [Algebra.TensorProduct.lift_tmul]
            simpa [qKAlg, qLAlg, qL, Q] using
              (Ideal.ResidueField.map_algebraMap
                qS.asIdeal q.asIdeal a rfl s)
          simpa [a, baseChangeAlgebraMap, bc, baseChangeRingMap,
            RingHom.algebraMap_toAlgebra] using hqFs
        · ext r'
          change qF (dmap (Algebra.TensorProduct.includeRight r')) = _
          change qF (dmap ((1 : S) ⊗ₜ[R] r')) = _
          rw [show dmap ((1 : S) ⊗ₜ[R] r') = smapAlg 1 * rmapAlg r' by rfl]
          simp only [map_one, one_mul]
          have hqFr : qF (rmapAlg r') =
              algebraMap (S ⊗[R] R') Q (bc r') := by
            change qF (algebraMap R' K r' ⊗ₜ[k] 1) = _
            dsimp [qF]
            rw [Algebra.TensorProduct.lift_tmul]
            simpa [qKAlg, qLAlg, qK, Q] using
              (Ideal.ResidueField.map_algebraMap
                p'.asIdeal q.asIdeal bc rfl r')
          simpa [bc, baseChangeRingMap, RingHom.algebraMap_toAlgebra] using hqFr
      exact congrArg (fun h : (S ⊗[R] R') →+* Q => h x) heq
    have hqFalg (y : K) : qF (algebraMap K F y) = qK y := by
      change qF ((Algebra.TensorProduct.includeLeft : K →ₐ[k] F) y) = qK y
      change (Algebra.TensorProduct.lift qKAlg qLAlg hcomm)
          ((Algebra.TensorProduct.includeLeft : K →ₐ[k] F) y) = qK y
      change ((Algebra.TensorProduct.lift qKAlg qLAlg hcomm).comp
          (Algebra.TensorProduct.includeLeft : K →ₐ[k] F)) y = qKAlg y
      rw [Algebra.TensorProduct.lift_comp_includeLeft]
    change IsPurelyInseparable K Q
    rw [isPurelyInseparable_iff_pow_mem K (ringExpChar K)]
    intro z
    let : ExpChar k (ringExpChar K) :=
      (algebraMap k K).expChar (algebraMap k K).injective (ringExpChar K)
    obtain ⟨aa, bb, hbb, hz⟩ :=
      IsFractionRing.div_surjective ((S ⊗[R] R') ⧸ q.asIdeal) z
    obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective aa
    obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective bb
    have hyq : y ∉ q.asIdeal := by
      intro hyq
      apply (mem_nonZeroDivisors_iff_ne_zero.mp hbb)
      rw [← hy]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr hyq
    have hqden : qF (dmap y) ≠ 0 := by
      intro hzero
      apply hyq
      apply Ideal.algebraMap_residueField_eq_zero.mp
      rw [← hqF]
      exact hzero
    have hz' : qF (dmap x) / qF (dmap y) = z := by
      rw [hqF, hqF]
      simpa [Q, Ideal.algebraMap_quotient_residueField_mk, ← hx, ← hy] using hz
    obtain ⟨n, u, hu⟩ :=
      IsPurelyInseparable.exists_pow_pow_mem_range_tensorProduct_of_expChar
        (q := ringExpChar K)
        (k := k) (K := L) (R := K) (dmap x)
    obtain ⟨m, v, hv⟩ :=
      IsPurelyInseparable.exists_pow_pow_mem_range_tensorProduct_of_expChar
        (q := ringExpChar K)
        (k := k) (K := L) (R := K) (dmap y)
    have hqxpow : qF (dmap x) ^ ringExpChar K ^ n = qK u := by
      calc
        qF (dmap x) ^ ringExpChar K ^ n =
            qF ((dmap x) ^ ringExpChar K ^ n) := by rw [map_pow]
        _ = qF (algebraMap K F u) := by rw [hu]
        _ = qK u := hqFalg u
    have hqypow : qF (dmap y) ^ ringExpChar K ^ m = qK v := by
      calc
        qF (dmap y) ^ ringExpChar K ^ m =
            qF ((dmap y) ^ ringExpChar K ^ m) := by rw [map_pow]
        _ = qF (algebraMap K F v) := by rw [hv]
        _ = qK v := hqFalg v
    have hqv : qK v ≠ 0 := by
      intro hv0
      apply (pow_ne_zero (ringExpChar K ^ m) hqden)
      rw [hqypow, hv0]
    refine ⟨n + m, ?_⟩
    refine ⟨u ^ ringExpChar K ^ m / v ^ ringExpChar K ^ n, ?_⟩
    change qK (u ^ ringExpChar K ^ m / v ^ ringExpChar K ^ n) =
      z ^ ringExpChar K ^ (n + m)
    calc
      qK (u ^ ringExpChar K ^ m / v ^ ringExpChar K ^ n) =
          qK u ^ ringExpChar K ^ m /
            qK v ^ ringExpChar K ^ n := by
              rw [map_div₀, map_pow, map_pow]
      _ = (qF (dmap x) ^ ringExpChar K ^ n) ^ ringExpChar K ^ m /
            (qF (dmap y) ^ ringExpChar K ^ m) ^ ringExpChar K ^ n := by
              rw [hqxpow, hqypow]
      _ = (qF (dmap x) / qF (dmap y)) ^
            (ringExpChar K ^ n * ringExpChar K ^ m) := by
              rw [← pow_mul, ← pow_mul, div_pow]
              rw [Nat.mul_comm (ringExpChar K ^ m) (ringExpChar K ^ n)]
      _ = z ^ ringExpChar K ^ (n + m) := by
              rw [hz', pow_add]

/-- An integral radicial map is a closed embedding on spectra, and its three
    defining properties survive arbitrary base change. -/
theorem integral_radicial_baseChange
    {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (hint : f.IsIntegral)
    (hinj : Function.Injective (PrimeSpectrum.comap f))
    (hres : residueFieldExtensionsPurelyInseparable f) :
    IsClosedMap (PrimeSpectrum.comap f) ∧
      ∀ (R' : Type*) [CommRing R'] (g : R →+* R'),
        (baseChangeRingMap f g).IsIntegral ∧
          Function.Injective (PrimeSpectrum.comap (baseChangeRingMap f g)) ∧
            residueFieldExtensionsPurelyInseparable (baseChangeRingMap f g) := by
  refine ⟨PrimeSpectrum.isClosedMap_comap_of_isIntegral f hint, ?_⟩
  intro R' _ g
  have hrad := radicial_baseChange f hinj hres R' g
  exact ⟨Formalization.Books.Algebra.Unit36.integral_base_change f g hint,
    hrad.1, hrad.2⟩

/-- An integral radicial map that is bijective on spectra is a homeomorphism,
    and its three defining properties survive arbitrary base change. -/
theorem integral_radicial_bijective_baseChange
    {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (hint : f.IsIntegral)
    (hbij : Function.Bijective (PrimeSpectrum.comap f))
    (hres : residueFieldExtensionsPurelyInseparable f) :
    IsHomeomorph (PrimeSpectrum.comap f) ∧
      ∀ (R' : Type*) [CommRing R'] (g : R →+* R'),
        (baseChangeRingMap f g).IsIntegral ∧
          Function.Injective (PrimeSpectrum.comap (baseChangeRingMap f g)) ∧
            residueFieldExtensionsPurelyInseparable (baseChangeRingMap f g) := by
  refine ⟨isHomeomorph_iff_continuous_isClosedMap_bijective.mpr ⟨PrimeSpectrum.continuous_comap f,
    PrimeSpectrum.isClosedMap_comap_of_isIntegral f hint, hbij⟩, ?_⟩
  intro R' _ g
  have hrad := radicial_baseChange f hbij.1 hres R' g
  exact ⟨Formalization.Books.Algebra.Unit36.integral_base_change f g hint,
    hrad.1, hrad.2⟩

private theorem universallyBijectiveGenerated_baseChange
    {R S R' : Type*} [CommRing R] [CommRing S] [CommRing R']
    (f : R →+* S) (g : R →+* R')
    (hgen : universallyBijectiveGenerated f) :
    universallyBijectiveGenerated (baseChangeRingMap f g) := by
  let : Algebra R S := f.toAlgebra
  let U : Set S := {x : S | ∃ n : ℕ, 0 < n ∧ ∃ P : Polynomial R,
    P.map f = (Polynomial.X - Polynomial.C x) ^ n}
  have hgen' : Algebra.adjoin R U = ⊤ := by
    simpa [U, universallyBijectiveGenerated, generatedBy] using hgen
  let : Algebra R R' := g.toAlgebra
  let bc : R' →+* S ⊗[R] R' := baseChangeRingMap f g
  let : Algebra R' (S ⊗[R] R') := bc.toAlgebra
  let a : S →+* S ⊗[R] R' := baseChangeAlgebraMap f g
  have hcomp : a.comp f = bc.comp g := by
    change Algebra.TensorProduct.includeLeftRingHom.comp f =
      Algebra.TensorProduct.includeRight.toRingHom.comp g
    exact Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap
  let A : Subalgebra R' (S ⊗[R] R') := Algebra.adjoin R'
    {z : S ⊗[R] R' | ∃ n : ℕ, 0 < n ∧ ∃ P : Polynomial R',
      P.map bc = (Polynomial.X - Polynomial.C z) ^ n}
  have hleft : ∀ s : S, a s ∈ A := by
    intro s
    have hs : s ∈ Algebra.adjoin R U := by rw [hgen']; trivial
    refine Algebra.adjoin_induction (p := fun x _ => a x ∈ A) ?_ ?_ ?_ ?_ hs
    · intro x hx
      rcases hx with ⟨n, hn, P, hP⟩
      apply Algebra.subset_adjoin
      refine ⟨n, hn, P.map g, ?_⟩
      calc
        (P.map g).map bc = P.map (bc.comp g) := by rw [Polynomial.map_map]
        _ = P.map (a.comp f) := by rw [hcomp]
        _ = (P.map f).map a := by rw [Polynomial.map_map]
        _ = ((Polynomial.X - Polynomial.C x) ^ n).map a := by rw [hP]
        _ = (Polynomial.X - Polynomial.C (a x)) ^ n := by simp
    · intro r
      have hr : a (f r) = bc (g r) := by
        exact congrArg (fun h : R →+* S ⊗[R] R' => h r) hcomp
      simpa [RingHom.algebraMap_toAlgebra] using hr ▸ A.algebraMap_mem (g r)
    · intro x y hx hy hxp hyp
      simpa only [map_add] using A.add_mem hxp hyp
    · intro x y hx hy hxp hyp
      simpa only [map_mul] using A.mul_mem hxp hyp
  change A = ⊤
  apply top_unique
  intro z hz
  refine TensorProduct.induction_on z ?_ ?_ ?_
  · exact A.zero_mem
  · intro s r'
    have hmul := A.mul_mem (hleft s) (A.algebraMap_mem r')
    simpa [a, baseChangeAlgebraMap, bc, baseChangeRingMap,
      RingHom.algebraMap_toAlgebra, Algebra.TensorProduct.tmul_mul_tmul] using hmul
  · intro x y hx hy
    exact A.add_mem hx hy

private theorem universallyBijective_residueField
    {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (hgen : universallyBijectiveGenerated f) :
    residueFieldExtensionsPurelyInseparable f := by
  let : Algebra R S := f.toAlgebra
  let U : Set S := {x : S | ∃ n : ℕ, 0 < n ∧ ∃ P : Polynomial R,
    P.map f = (Polynomial.X - Polynomial.C x) ^ n}
  have hgen' : Algebra.adjoin R U = ⊤ := by
    simpa [U, universallyBijectiveGenerated, generatedBy] using hgen
  intro q
  let K := (PrimeSpectrum.comap f q).asIdeal.ResidueField
  let L := q.asIdeal.ResidueField
  let hq : K →+* L := residueFieldMap f q
  let : Algebra K L := hq.toAlgebra
  have hmapr (r : R) :
      algebraMap K L (algebraMap R K r) = algebraMap S L (f r) := by
    change hq (algebraMap R K r) = algebraMap S L (f r)
    simpa [K, L, hq, residueFieldMap] using
      (Ideal.ResidueField.map_algebraMap
        (PrimeSpectrum.comap f q).asIdeal q.asIdeal f rfl r)
  let V : Set L := {z : L | ∃ x ∈ U, algebraMap S L x = z}
  let A : IntermediateField K L := IntermediateField.adjoin K V
  have hleft (s : S) : algebraMap S L s ∈ A := by
    have hs : s ∈ Algebra.adjoin R U := by
      simp only [Algebra.mem_top, hgen']
    refine Algebra.adjoin_induction (p := fun x _ => algebraMap S L x ∈ A)
      ?_ ?_ ?_ ?_ hs
    · intro x hx
      exact IntermediateField.subset_adjoin K V ⟨x, hx, rfl⟩
    · intro r
      simpa only [RingHom.algebraMap_toAlgebra] using
        (hmapr r).symm ▸ A.algebraMap_mem (algebraMap R K r)
    · intro x y hx hy hxp hyp
      simpa only [map_add] using A.add_mem hxp hyp
    · intro x y hx hy hxp hyp
      simpa only [map_mul] using A.mul_mem hxp hyp
  have htop : A = ⊤ := by
    apply top_unique
    intro z hz
    obtain ⟨aa, bb, hbb, hzdiv⟩ := IsFractionRing.div_surjective (S ⧸ q.asIdeal) z
    obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective aa
    obtain ⟨w, hw⟩ := Ideal.Quotient.mk_surjective bb
    have hw0 : algebraMap S L w ≠ 0 := by
      have hq0 : Ideal.Quotient.mk q.asIdeal w ≠ 0 := by
        intro hzero
        have hbb0 : bb ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hbb
        apply hbb0
        rw [← hw]
        exact hzero
      intro hzero
      apply hq0
      apply Ideal.injective_algebraMap_quotient_residueField
      simpa only [Ideal.algebraMap_quotient_residueField_mk, map_zero] using hzero
    have hz' : algebraMap S L y / algebraMap S L w = z := by
      simpa [L, Ideal.algebraMap_quotient_residueField_mk, ← hy, ← hw] using hzdiv
    rw [← hz']
    exact A.div_mem (hleft y) (hleft w)
  have hsimple (x : S) (hx : x ∈ U) :
      IsPurelyInseparable K
        (IntermediateField.adjoin K {algebraMap S L x}) := by
    obtain ⟨n, hn, P, hP⟩ := hx
    let Q : Polynomial K := P.map (algebraMap R K)
    have hcomp : (algebraMap K L).comp (algebraMap R K) =
        (algebraMap S L).comp f := by
      ext r
      exact hmapr r
    have hQ : Q.map (algebraMap K L) =
        (Polynomial.X - Polynomial.C (algebraMap S L x)) ^ n := by
      calc
        Q.map (algebraMap K L) =
            P.map ((algebraMap K L).comp (algebraMap R K)) := by
              simp [Q, Polynomial.map_map]
        _ = P.map ((algebraMap S L).comp f) := by rw [hcomp]
        _ = (P.map f).map (algebraMap S L) := by rw [Polynomial.map_map]
        _ = ((Polynomial.X - Polynomial.C x) ^ n).map (algebraMap S L) := by rw [hP]
        _ = (Polynomial.X - Polynomial.C (algebraMap S L x)) ^ n := by simp
    have hQmonic : Q.Monic := by
      apply Polynomial.monic_of_injective (algebraMap K L).injective
      rw [hQ]
      exact (Polynomial.monic_X_sub_C _).pow n
    have hroot : Polynomial.aeval (algebraMap S L x) Q = 0 := by
      have hroot' : (Q.map (algebraMap K L)).eval₂ (RingHom.id L)
          (algebraMap S L x) = 0 := by
        rw [hQ]
        simp [hn.ne']
      rw [Polynomial.eval₂_map] at hroot'
      simpa [Polynomial.aeval_def] using hroot'
    have hi : IsIntegral K (algebraMap S L x) := ⟨Q, hQmonic, hroot⟩
    have hd := minpoly.dvd K (algebraMap S L x) hroot
    have hdmap : (minpoly K (algebraMap S L x)).map (algebraMap K L) ∣
        (Polynomial.X - Polynomial.C (algebraMap S L x)) ^ n := by
      rw [← hQ]
      exact (Polynomial.map_dvd_map (algebraMap K L)
        (algebraMap K L).injective (minpoly.monic hi)).2 hd
    have hle : (minpoly K (algebraMap S L x)).natSepDegree ≤ 1 := by
      have hnonzero :
          ((Polynomial.X - Polynomial.C (algebraMap S L x)) ^ n) ≠ 0 :=
        ((Polynomial.monic_X_sub_C _).pow n).ne_zero
      have hle' := Polynomial.natSepDegree_le_of_dvd
        (f := (minpoly K (algebraMap S L x)).map (algebraMap K L))
        ((Polynomial.X - Polynomial.C (algebraMap S L x)) ^ n) hdmap hnonzero
      rw [Polynomial.natSepDegree_map] at hle'
      simpa [hn.ne'] using hle'
    have hpos : 0 < (minpoly K (algebraMap S L x)).natSepDegree :=
      Nat.pos_of_ne_zero ((Polynomial.natSepDegree_ne_zero_iff _).2
        (minpoly.natDegree_pos hi).ne')
    have hnat : (minpoly K (algebraMap S L x)).natSepDegree = 1 := by omega
    exact (IntermediateField.isPurelyInseparable_adjoin_simple_iff_natSepDegree_eq_one
      K L).2 hnat
  have hpureA : IsPurelyInseparable K A := by
    rw [IntermediateField.isPurelyInseparable_adjoin_iff_pow_mem K L (ringExpChar K)]
    intro z hz
    obtain ⟨x, hx, rfl⟩ := hz
    exact (IntermediateField.isPurelyInseparable_adjoin_simple_iff_pow_mem
      K L (ringExpChar K)).1 (hsimple x hx)
  have hpureTop : IsPurelyInseparable K (⊤ : IntermediateField K L) := by
    rw [← htop]
    exact hpureA
  exact IntermediateField.topEquiv.isPurelyInseparable

private theorem universallyBijective_integral
    {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (hgen : universallyBijectiveGenerated f) : f.IsIntegral := by
  let : Algebra R S := f.toAlgebra
  let U : Set S := {x : S | ∃ n : ℕ, 0 < n ∧ ∃ P : Polynomial R,
    P.map f = (Polynomial.X - Polynomial.C x) ^ n}
  have hgen' : Algebra.adjoin R U = ⊤ := by
    simpa [U, universallyBijectiveGenerated, generatedBy] using hgen
  let I := RingHom.ker f
  let k : R →+* R ⧸ I := Ideal.Quotient.mk I
  let f₀ : R ⧸ I →+* S := f.kerLift
  let : Algebra (R ⧸ I) S := f₀.toAlgebra
  let A : Subalgebra (R ⧸ I) S := Algebra.adjoin (R ⧸ I) U
  have hgen₀ : A = ⊤ := by
    apply top_unique
    intro s hs
    have hs' : s ∈ Algebra.adjoin R U := by
      simp only [Algebra.mem_top, hgen']
    refine Algebra.adjoin_induction (p := fun x _ => x ∈ A)
      ?_ ?_ ?_ ?_ hs'
    · intro x hx
      exact Algebra.mem_adjoin_of_mem hx
    · intro r
      simpa [A, I, k, f₀, RingHom.algebraMap_toAlgebra] using
        A.algebraMap_mem (k r)
    · intro x y hx hy hxp hyp
      exact A.add_mem hxp hyp
    · intro x y hx hy hxp hyp
      exact A.mul_mem hxp hyp
  have hsub : Algebra.IsIntegral (R ⧸ I) A :=
    Algebra.IsIntegral.adjoin (by
      intro x hx
      obtain ⟨n, hn, P, hP⟩ := hx
      let Q : Polynomial (R ⧸ I) := P.map k
      have hcomp : f₀.comp k = f := by
        ext r
        simp [f₀, k, I]
      have hQ : Q.map f₀ =
          (Polynomial.X - Polynomial.C x) ^ n := by
        calc
          Q.map f₀ = P.map (f₀.comp k) := by simp [Q, Polynomial.map_map]
          _ = P.map f := by rw [hcomp]
          _ = (Polynomial.X - Polynomial.C x) ^ n := hP
      have hQmonic : Q.Monic := by
        apply Polynomial.monic_of_injective (RingHom.kerLift_injective f)
        rw [hQ]
        exact (Polynomial.monic_X_sub_C _).pow n
      have hroot : Polynomial.aeval x Q = 0 := by
        have hroot' : (Q.map f₀).eval₂ (RingHom.id S) x = 0 := by
          rw [hQ]
          simp [hn.ne']
        rw [Polynomial.eval₂_map] at hroot'
        change Polynomial.aeval x Q = 0
        exact hroot'
      exact ⟨Q, hQmonic, hroot⟩)
  have hf₀ : f₀.IsIntegral := by
    intro x
    have hx : x ∈ A := by
      simp [hgen₀]
    have hi := hsub.isIntegral (⟨x, hx⟩ : A)
    change IsIntegral (R ⧸ I) x
    exact hi.algebraMap
  have hk : k.IsIntegral := by
    intro x
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
    refine ⟨(Polynomial.X - Polynomial.C r : Polynomial R),
      Polynomial.monic_X_sub_C _, ?_⟩
    simp
    change (Ideal.Quotient.mk I r - Ideal.Quotient.mk I r) = 0
    simp
  have hcomp : f₀.comp k = f := by
    ext r
    simp [f₀, k, I]
  rw [← hcomp]
  exact RingHom.IsIntegral.trans k f₀ hk hf₀

private theorem universallyBijective_comap_injective
    {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (hgen : universallyBijectiveGenerated f) :
    Function.Injective (PrimeSpectrum.comap f) := by
  let : Algebra R S := f.toAlgebra
  let U : Set S := {x : S | ∃ n : ℕ, 0 < n ∧ ∃ P : Polynomial R,
    P.map f = (Polynomial.X - Polynomial.C x) ^ n}
  have hgen' : Algebra.adjoin R U = ⊤ := by
    exact hgen
  intro q q' hqq'
  have hI : q.asIdeal.comap f = q'.asIdeal.comap f := by
    simpa using congrArg PrimeSpectrum.asIdeal hqq'
  let I := q.asIdeal.comap f
  let K := I.ResidueField
  let L := q.asIdeal.ResidueField
  let L' := q'.asIdeal.ResidueField
  let hq : K →+* L := Ideal.ResidueField.map I q.asIdeal f rfl
  let hq' : K →+* L' := Ideal.ResidueField.map I q'.asIdeal f hI
  let : Algebra K L := hq.toAlgebra
  let : Algebra K L' := hq'.toAlgebra
  let T := L ⊗[K] L'
  let : Nontrivial T :=
    Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_isDomain
      K L L' (RingHom.injective _) (RingHom.injective _)
  obtain ⟨M, hM⟩ := Ideal.exists_maximal T
  let : M.IsMaximal := hM
  let Q := T ⧸ M
  let : Field Q := Ideal.Quotient.field M
  let m : T →+* Q := Ideal.Quotient.mk M
  let jL : L →+* Q := m.comp
    (Algebra.TensorProduct.includeLeft : L →ₐ[K] T).toRingHom
  let jL' : L' →+* Q := m.comp
    (Algebra.TensorProduct.includeRight : L' →ₐ[K] T).toRingHom
  have hjL : Function.Injective jL := RingHom.injective _
  have hjL' : Function.Injective jL' := RingHom.injective _
  let : Algebra R L := ((algebraMap S L).comp f).toAlgebra
  let : Algebra R L' := ((algebraMap S L').comp f).toAlgebra
  let : Algebra R T :=
    ((algebraMap K T).comp (algebraMap R K)).toAlgebra
  let : Algebra R Q :=
    ((m.comp (algebraMap K T)).comp (algebraMap R K)).toAlgebra
  have hscalar (r : R) :
      hq (algebraMap R K r) = algebraMap S L (f r) := by
    exact Ideal.ResidueField.map_algebraMap I q.asIdeal f rfl r
  have hscalar' (r : R) :
      hq' (algebraMap R K r) = algebraMap S L' (f r) := by
    exact Ideal.ResidueField.map_algebraMap I q'.asIdeal f hI r
  let φ : S →+* Q := jL.comp (algebraMap S L)
  let ψ : S →+* Q := jL'.comp (algebraMap S L')
  have hφ (r : R) : φ (f r) = algebraMap R Q r := by
    change jL (algebraMap S L (f r)) = algebraMap R Q r
    rw [← hscalar r]
    change m (algebraMap K T (algebraMap R K r)) = algebraMap R Q r
    rfl
  have hψ (r : R) : ψ (f r) = algebraMap R Q r := by
    change jL' (algebraMap S L' (f r)) = algebraMap R Q r
    rw [← hscalar' r]
    change m ((1 : L) ⊗ₜ[K] hq' (algebraMap R K r)) = algebraMap R Q r
    have htmul :
        (1 : L) ⊗ₜ[K] hq' (algebraMap R K r) =
          hq (algebraMap R K r) ⊗ₜ[K] (1 : L') := by
      change (1 : L) ⊗ₜ[K] algebraMap K L' (algebraMap R K r) =
        algebraMap K L (algebraMap R K r) ⊗ₜ[K] (1 : L')
      exact Eq.symm (Algebra.TensorProduct.tmul_one_eq_one_tmul ((algebraMap R K) r))
    rw [htmul]
    change m (algebraMap K T (algebraMap R K r)) = algebraMap R Q r
    rfl
  have hbase : φ.comp f = ψ.comp f := by
    ext r
    change φ (f r) = ψ (f r)
    simp only [hφ, hψ]
  have hmap (s : S) : φ s = ψ s := by
    have hs : s ∈ Algebra.adjoin R U := by
      simp only [Algebra.mem_top, hgen']
    refine Algebra.adjoin_induction (p := fun x _ => φ x = ψ x)
      ?_ ?_ ?_ ?_ hs
    · intro x hx
      obtain ⟨n, hn, P, hP⟩ := hx
      have hpoly : (P.map f).map φ = (P.map f).map ψ := by
        rw [Polynomial.map_map, Polynomial.map_map, hbase]
      have heval := congrArg
        (fun W : Polynomial Q => W.eval₂ (RingHom.id Q) (φ x)) hpoly
      rw [hP] at heval
      apply sub_eq_zero.mp
      simpa [hn.ne'] using heval.symm
    · intro r
      change φ (f r) = ψ (f r)
      exact congrArg (fun h : R →+* Q => h r) hbase
    · intro x y hx hy hxp hyp
      simp only [map_add, hxp, hyp]
    · intro x y hx hy hxp hyp
      simp only [map_mul, hxp, hyp]
  have hqeq : q.asIdeal = q'.asIdeal := by
    ext x
    constructor
    · intro hx
      have hzero : algebraMap S L (x) = 0 :=
        Ideal.algebraMap_residueField_eq_zero.mpr hx
      have hz : algebraMap S L' x = 0 := by
        apply hjL'
        have hz' : ψ x = 0 := by
          rw [← hmap x]
          change jL (algebraMap S L x) = 0
          rw [hzero, map_zero]
        calc
          jL' (algebraMap S L' x) = 0 := by
            change ψ x = 0
            exact hz'
          _ = jL' 0 := (map_zero jL').symm
      exact Ideal.algebraMap_residueField_eq_zero.mp hz
    · intro hx
      have hzero : algebraMap S L' (x) = 0 :=
        Ideal.algebraMap_residueField_eq_zero.mpr hx
      have hz : algebraMap S L x = 0 := by
        apply hjL
        have hz' : φ x = 0 := by
          rw [hmap x]
          change jL' (algebraMap S L' x) = 0
          rw [hzero, map_zero]
        calc
          jL (algebraMap S L x) = 0 := by
            change φ x = 0
            exact hz'
          _ = jL 0 := (map_zero jL).symm
      exact Ideal.algebraMap_residueField_eq_zero.mp hz
  exact PrimeSpectrum.ext hqeq

/-- The final universally bijective criterion: a locally nilpotent kernel and
    polynomial powers of algebra generators imply a universal homeomorphism
    with purely inseparable residue fields. -/
theorem universallyBijective
    {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (hker : locallyNilpotentKernel f)
    (hgen : universallyBijectiveGenerated f) :
    IsHomeomorph (PrimeSpectrum.comap f) ∧
      residueFieldExtensionsPurelyInseparable f ∧
      ∀ (R' : Type*) [CommRing R'] (g : R →+* R'),
          locallyNilpotentKernel (baseChangeRingMap f g) ∧
            universallyBijectiveGenerated (baseChangeRingMap f g) := by
  let : Algebra R S := f.toAlgebra
  have hint : f.IsIntegral := universallyBijective_integral f hgen
  have hinj : Function.Injective (PrimeSpectrum.comap f) :=
    universallyBijective_comap_injective f hgen
  have hres : residueFieldExtensionsPurelyInseparable f :=
    universallyBijective_residueField f hgen
  have hker' : RingHom.ker f ≤ nilradical R :=
    fun x hx => mem_nilradical.mpr (hker x hx)
  have hsurj : Function.Surjective (PrimeSpectrum.comap f) := by
    exact (PrimeSpectrum.comap_quotientMk_bijective_of_le_nilradical hker').2.comp
      (hint.kerLift.comap_surjective f.kerLift_injective)
  have hhomeo : IsHomeomorph (PrimeSpectrum.comap f) :=
    isHomeomorph_iff_continuous_isClosedMap_bijective.mpr
      ⟨PrimeSpectrum.continuous_comap f,
        PrimeSpectrum.isClosedMap_comap_of_isIntegral f hint,
        ⟨hinj, hsurj⟩⟩
  refine ⟨hhomeo, hres, ?_⟩
  intro R' _ g
  have hgenbc := universallyBijectiveGenerated_baseChange f g hgen
  refine ⟨?_, hgenbc⟩
  let : Algebra R R' := g.toAlgebra
  let bc : R' →+* S ⊗[R] R' := baseChangeRingMap f g
  have hsurj0 : Function.Surjective (PrimeSpectrum.comap
      (algebraMap R' (R' ⊗[R] S))) :=
    (Formalization.Books.Algebra.Unit30.spectrum_surjective_radical_ideal_conditions_baseChange
      f hhomeo.surjective g).2
  let e : (R' ⊗[R] S) ≃+* (S ⊗[R] R') :=
    (Algebra.TensorProduct.comm R R' S).toRingEquiv
  have heq : e.toRingHom.comp (algebraMap R' (R' ⊗[R] S)) = bc := by
    rfl
  have hsurj : Function.Surjective (PrimeSpectrum.comap bc) := by
    rw [← heq, PrimeSpectrum.comap_comp]
    exact hsurj0.comp
      (PrimeSpectrum.isHomeomorph_comap_of_bijective e.bijective).surjective
  have hkerbc : RingHom.ker bc ≤ nilradical R' :=
    (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical bc).1 hsurj.denseRange
  exact fun x hx => mem_nilradical.mp (hkerbc hx)

end

end Formalization.Books.Algebra.Unit46
