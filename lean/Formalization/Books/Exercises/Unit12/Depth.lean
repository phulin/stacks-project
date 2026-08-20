import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Module.Torsion.PrimaryComponent
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.Length
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.Regular.RegularSequence
import Mathlib.RingTheory.Spectrum.Prime.Module
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.Topology.Connected.Basic

/-!
# Exercises, Chapter 12: Depth

The source defines depth as a supremum of lengths of regular sequences, with
the value `∞` when the ideal generates the whole module.  Mathlib supplies
the regular-sequence, torsion, support, localization, quotient, and exact
sequence APIs used below, but does not expose this numerical depth interface.
-/

namespace Formalization.Books.Exercises.Unit12

open CategoryTheory
open scoped ZeroObject

universe u v

noncomputable section

/-! ## The source's depth interface -/

/-- An `M`-regular sequence of length `n` contained in `I`, or the vacuous
condition used when `I • M = M`, as in the source definition of depth. -/
def DepthAtLeast {R : Type*} [CommRing R] (I : Ideal R) (M : Type*)
    [AddCommGroup M] [Module R M] [Module.Finite R M] (n : ℕ) : Prop :=
  I • (⊤ : Submodule R M) = ⊤ ∨
    ∃ rs : List R,
      rs.length = n ∧
        (∀ r ∈ rs, r ∈ I) ∧
          RingTheory.Sequence.IsRegular M rs

/-- The `I`-depth of a finite module, valued in `ℕ∞` so that the source's
convention `depth_I(M) = ∞` when `I • M = M` is represented literally. -/
noncomputable def depth {R : Type*} [CommRing R] (I : Ideal R) (M : Type*)
    [AddCommGroup M] [Module R M] [Module.Finite R M] : WithTop ℕ := by
  classical
  exact
  sSup (Set.range fun n : ℕ =>
    if DepthAtLeast I M n then (n : WithTop ℕ) else 0)

/-! ## Exercise: compute depths -/

abbrev integerDepthRing : Type := ℤ

def integerDepthIdeal : Ideal integerDepthRing :=
  Ideal.span ({(30 : ℤ)} : Set ℤ)

abbrev integerDepthModule : Type := ℤ

abbrev integerDepthTorsionModule : Type := ZMod 300

abbrev integerDepthResidueModule : Type := ZMod 7

def integerDepthResidueIdeal : Ideal ℤ :=
  Ideal.span ({(30 : ℤ)} : Set ℤ)

abbrev depthThreeVariablePolynomialRing (k : Type u) [Field k] :=
  MvPolynomial (Fin 3) k

def depthThreeVariableQuadric (k : Type u) [Field k] :
    depthThreeVariablePolynomialRing k :=
  MvPolynomial.X 0 ^ 2 + MvPolynomial.X 1 ^ 2 + MvPolynomial.X 2 ^ 2

abbrev depthQuadricRing (k : Type u) [Field k] :=
  depthThreeVariablePolynomialRing k ⧸
    Ideal.span ({depthThreeVariableQuadric k} : Set (depthThreeVariablePolynomialRing k))

def depthQuadricIdeal (k : Type u) [Field k] : Ideal (depthQuadricRing k) :=
  Ideal.span
    ({Ideal.Quotient.mk _ (MvPolynomial.X 0),
      Ideal.Quotient.mk _ (MvPolynomial.X 1),
      Ideal.Quotient.mk _ (MvPolynomial.X 2)} : Set (depthQuadricRing k))

abbrev depthFourVariablePolynomialRing (k : Type u) [Field k] :=
  MvPolynomial (Fin 4) k

def depthFourVariableRelations (k : Type u) [Field k] :
    Set (depthFourVariablePolynomialRing k) :=
  {MvPolynomial.X 0 * MvPolynomial.X 2,
    MvPolynomial.X 0 * MvPolynomial.X 3,
    MvPolynomial.X 1 * MvPolynomial.X 2,
    MvPolynomial.X 1 * MvPolynomial.X 3}

abbrev depthFourComponentRing (k : Type u) [Field k] :=
  depthFourVariablePolynomialRing k ⧸
    Ideal.span (depthFourVariableRelations k)

def depthFourComponentIdeal (k : Type u) [Field k] : Ideal (depthFourComponentRing k) :=
  Ideal.span
    ({Ideal.Quotient.mk _ (MvPolynomial.X 0),
      Ideal.Quotient.mk _ (MvPolynomial.X 1),
      Ideal.Quotient.mk _ (MvPolynomial.X 2),
      Ideal.Quotient.mk _ (MvPolynomial.X 3)} : Set (depthFourComponentRing k))

/-- The five values requested in the first exercise. -/
theorem compute_depth_examples (k : Type u) [Field k] :
    depth integerDepthIdeal integerDepthModule = 1 ∧
      depth integerDepthIdeal integerDepthTorsionModule = 0 ∧
      depth integerDepthResidueIdeal integerDepthResidueModule = ⊤ ∧
      depth (depthQuadricIdeal k) (depthQuadricRing k) = 2 ∧
      depth (depthFourComponentIdeal k) (depthFourComponentRing k) = 1 := by
  sorry

/-! ## Exercise: depth is not inherited by localization -/

def localizedIdeal {R : Type*} [CommRing R] (p : Ideal R) [p.IsPrime] :
    Ideal (Localization.AtPrime p) :=
  Ideal.map (algebraMap R (Localization.AtPrime p)) p

/-- The existence statement in the localization exercise, with the residue
field omitted because it is only named and never used in the assertions. -/
theorem exists_depth_not_inherited_localization :
    ∃ (R : CommRingCat) (m : Ideal R) (p : PrimeSpectrum R),
      IsNoetherianRing R ∧
        IsLocalRing R ∧
        m.IsMaximal ∧
        depth m R ≥ 1 ∧
        depth (localizedIdeal p.asIdeal) (Localization.AtPrime p.asIdeal) = 0 ∧
        1 ≤ ringKrullDim (Localization.AtPrime p.asIdeal) := by
  sorry

/-! ## Exercise: torsion-free finite modules -/

theorem depth_torsion_free_at_least_one
    {R M : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    [IsDomain R] [AddCommGroup M] [Module R M] [Module.Finite R M]
    [Module.IsTorsionFree R M] :
    depth (IsLocalRing.maximalIdeal R) M ≥ 1 := by
  sorry

abbrev oneVariablePolynomialRing (k : Type u) [Field k] := Polynomial k

def oneVariableOriginIdeal (k : Type u) [Field k] :
    Ideal (oneVariablePolynomialRing k) :=
  Ideal.span ({Polynomial.X} : Set (oneVariablePolynomialRing k))

instance oneVariableOriginIdeal_isPrime (k : Type u) [Field k] :
    (oneVariableOriginIdeal k).IsPrime := by
  apply (Ideal.span_singleton_prime (by simp)).mpr
  exact Polynomial.prime_X

abbrev oneVariableLocalRing (k : Type u) [Field k] :=
  Localization.AtPrime (oneVariableOriginIdeal k)

def oneVariableLocalMaximalIdeal (k : Type u) [Field k] :
    Ideal (oneVariableLocalRing k) :=
  IsLocalRing.maximalIdeal (oneVariableLocalRing k)

/-- The standard one-dimensional localized polynomial ring supplies the
depth-one example requested in the second part. -/
theorem one_variable_local_depth_one (k : Type u) [Field k] :
    IsNoetherianRing (oneVariableLocalRing k) ∧
      IsLocalRing (oneVariableLocalRing k) ∧
        IsDomain (oneVariableLocalRing k) ∧
          Module.Finite (oneVariableLocalRing k) (oneVariableLocalRing k) ∧
            Module.IsTorsionFree (oneVariableLocalRing k) (oneVariableLocalRing k) ∧
              depth (oneVariableLocalMaximalIdeal k) (oneVariableLocalRing k) = 1 := by
  sorry

/- The dimension hypothesis in the localization exercise rules out the easy
choice of the generic point of a one-dimensional local domain: its
localization is a field and therefore has depth zero and dimension zero. -/
theorem easy_localization_without_dimension_condition (k : Type u) [Field k] :
    depth (oneVariableLocalMaximalIdeal k) (oneVariableLocalRing k) = 1 ∧
      depth
          (localizedIdeal (⊥ : PrimeSpectrum (oneVariableLocalRing k)).asIdeal)
          (Localization.AtPrime
            (⊥ : PrimeSpectrum (oneVariableLocalRing k)).asIdeal) = 0 ∧
        ringKrullDim
            (Localization.AtPrime
              (⊥ : PrimeSpectrum (oneVariableLocalRing k)).asIdeal) = 0 := by
  sorry

/-! ## Exercise: prescribed dimension and depth -/

theorem exists_local_noetherian_ring_dimension_depth
    (m n : ℕ) (hnm : n ≤ m) :
    ∃ (R : CommRingCat) (mIdeal : Ideal R),
      IsNoetherianRing R ∧
        IsLocalRing R ∧
        mIdeal.IsMaximal ∧
        ringKrullDim R = m ∧
        depth mIdeal R = n := by
  sorry

/-! ## Exercise: the canonical depth-one quotient -/

/-- The canonical submodule of elements supported at the closed point. -/
def depthOneKernel {R : Type*} [CommRing R] (m : Ideal R) (M : Type*)
    [AddCommGroup M] [Module R M] : Submodule R M :=
  Ideal.primaryComponent M m

abbrev depthOneQuotient {R : Type*} [CommRing R] (m : Ideal R) (M : Type*)
    [AddCommGroup M] [Module R M] :=
  M ⧸ depthOneKernel m M

def depthOneInclusion {R : Type*} [CommRing R] (m : Ideal R) (M : Type*)
    [AddCommGroup M] [Module R M] : depthOneKernel m M →ₗ[R] M :=
  (depthOneKernel m M).subtype

def depthOneProjection {R : Type*} [CommRing R] (m : Ideal R) (M : Type*)
    [AddCommGroup M] [Module R M] : M →ₗ[R] depthOneQuotient m M :=
  (depthOneKernel m M).mkQ

def depthOneShortComplex {R : Type*} [CommRing R] (m : Ideal R) (M : Type*)
    [AddCommGroup M] [Module R M] : ShortComplex (ModuleCat R) :=
  ShortComplex.mk
    (ModuleCat.ofHom (depthOneInclusion m M))
    (ModuleCat.ofHom (depthOneProjection m M))
    (by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      simp [depthOneInclusion, depthOneProjection])

theorem depth_one_canonical_short_exact
    {R M : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M] :
    (depthOneShortComplex (IsLocalRing.maximalIdeal R) M).ShortExact := by
  sorry

theorem depth_one_canonical_properties
    {R M : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M] :
    depth (IsLocalRing.maximalIdeal R)
        (depthOneQuotient (IsLocalRing.maximalIdeal R) M) ≥ 1 ∧
      (depthOneKernel (IsLocalRing.maximalIdeal R) M = ⊥ ∨
        Module.support R (depthOneKernel (IsLocalRing.maximalIdeal R) M) =
          {IsLocalRing.closedPoint R}) ∧
      Module.length R (depthOneKernel (IsLocalRing.maximalIdeal R) M) < ⊤ := by
  sorry

/-! ## Exercise: a submodule of a module of depth at least two -/

theorem depth_two_submodule_properties
    {R M : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M]
    (hM : depth (IsLocalRing.maximalIdeal R) M ≥ 2)
    (N : Submodule R M) (hN : N ≠ ⊥) :
    depth (IsLocalRing.maximalIdeal R) N ≥ 1 ∧
      (depth (IsLocalRing.maximalIdeal R) N = 1 ↔
        depth (IsLocalRing.maximalIdeal R) (M ⧸ N) = 0) ∧
      ∃ N' : Submodule R M,
        N ≤ N' ∧
          Module.length R (N' ⧸ N.comap N'.subtype) < ⊤ ∧
          depth (IsLocalRing.maximalIdeal R) N' ≥ 2 := by
  sorry

/-! ## Exercise: the reduced two-minimal-prime exact sequence -/

def reducedTwoPrimeFirstMap {R : Type*} [CommRing R]
    (p q : Ideal R) : R →ₗ[R] (R ⧸ p) × (R ⧸ q) :=
  (Ideal.Quotient.mkₐ R p).toLinearMap.prod (Ideal.Quotient.mkₐ R q).toLinearMap

def quotientFactorLinearMap {R : Type*} [CommRing R]
    {p q : Ideal R} (hpq : p ≤ q) : (R ⧸ p) →ₗ[R] (R ⧸ q) :=
  { toFun := Ideal.Quotient.factor hpq
    map_add' := map_add _
    map_smul' := by
      intro a x
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
      change Ideal.Quotient.factor hpq (Ideal.Quotient.mk p (a * x)) =
        Ideal.Quotient.mk q (a * x)
      rw [Ideal.Quotient.factor_mk] }

def reducedTwoPrimeSecondMap {R : Type*} [CommRing R]
    (p q : Ideal R) : (R ⧸ p) × (R ⧸ q) →ₗ[R] R ⧸ (p ⊔ q) :=
  (quotientFactorLinearMap le_sup_left).comp
      (LinearMap.fst R (R ⧸ p) (R ⧸ q)) -
    (quotientFactorLinearMap le_sup_right).comp
      (LinearMap.snd R (R ⧸ p) (R ⧸ q))

def reducedTwoPrimeShortComplex {R : Type*} [CommRing R]
    (p q : Ideal R) : ShortComplex (ModuleCat R) :=
  ShortComplex.mk
    (ModuleCat.ofHom (reducedTwoPrimeFirstMap p q))
    (ModuleCat.ofHom (reducedTwoPrimeSecondMap p q))
    (by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      simp [reducedTwoPrimeFirstMap, reducedTwoPrimeSecondMap,
        quotientFactorLinearMap])

theorem reduced_two_prime_exact_sequence
    {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    [IsReduced R] (p q : Ideal R)
    (hp : p ∈ minimalPrimes R) (hq : q ∈ minimalPrimes R) (hpq : p ≠ q) :
    (reducedTwoPrimeShortComplex p q).ShortExact := by
  sorry

theorem reduced_two_prime_quotient_dimension_at_least_one
    {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    [IsReduced R] (p q : Ideal R)
    (hp : p ∈ minimalPrimes R) (hq : q ∈ minimalPrimes R) (hpq : p ≠ q)
    (hdepth : depth (IsLocalRing.maximalIdeal R) R ≥ 2) :
    1 ≤ ringKrullDim (R ⧸ (p ⊔ q)) := by
  sorry

def puncturedSpectrum {R : Type*} [CommSemiring R] [IsLocalRing R] :
    Set (PrimeSpectrum R) :=
  {x | x ≠ IsLocalRing.closedPoint R}

theorem reduced_punctured_spectrum_connected
    {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    [IsReduced R] (p q : Ideal R)
    (hp : p ∈ minimalPrimes R) (hq : q ∈ minimalPrimes R) (hpq : p ≠ q)
    (hdepth : depth (IsLocalRing.maximalIdeal R) R ≥ 2) :
    _root_.IsConnected (puncturedSpectrum (R := R)) := by
  sorry

/-! ## Exercise: the monomial relation for a regular sequence of length two -/

theorem regular_sequence_depth_two_monomial_relation
    {R : Type*} [CommRing R] [IsLocalRing R]
    (x y : R) (hx : x ∈ IsLocalRing.maximalIdeal R)
    (hy : y ∈ IsLocalRing.maximalIdeal R)
    (hxy : RingTheory.Sequence.IsRegular R [x, y]) (n : ℕ) (hn : 2 ≤ n) :
    ¬ ∃ a b : R, x ^ (n - 1) * y ^ (n - 1) = a * x ^ n + b * y ^ n := by
  sorry

end

end Formalization.Books.Exercises.Unit12
