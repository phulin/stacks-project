import Mathlib.Algebra.Field.ULift
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.MvPowerSeries.Equiv

/-!
# Exercises, Chapter 57: Hilbert functions

The source's successive quotients are represented by a canonical submodule
quotient.  The denominator is written as the maximal ideal acting on the
`n`th-power submodule so Mathlib supplies the required residue-field module
structure; this is the source-facing quotient needed by `Module.finrank`.
-/

namespace Formalization.Books.Exercises.Unit57

universe u

noncomputable section

/-- The `n`th associated-graded piece `𝔪^n / 𝔪^(n+1)` of a local ring. -/
abbrev hilbertGradedPiece
    (R : Type u) [CommRing R] [IsLocalRing R] (n : ℕ) : Type u :=
  let m : Ideal R := IsLocalRing.maximalIdeal R
  let N : Submodule R R := m ^ n • (⊤ : Submodule R R)
  N ⧸ (m • (⊤ : Submodule R N))

/-- The Hilbert function `φ_R(n) = dim_κ(𝔪^n / 𝔪^(n+1))`. -/
def hilbertFunction
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (n : ℕ) : ℕ :=
  Module.finrank (R ⧸ IsLocalRing.maximalIdeal R) (hilbertGradedPiece R n)

/-
Proof roadmap (two-variable formal power series).

* Take `k := ULift.{u} ℚ` and
  `R := MvPowerSeries (Fin 2) k`.  The universe lift is essential: using `ℚ`
  directly does not elaborate when the theorem's `u` is nonzero.
  `Mathlib/Algebra/Field/ULift.lean` supplies the field instance,
  `MvPowerSeries.isNoetherianRing` is in
  `Mathlib/RingTheory/MvPowerSeries/Equiv.lean`, and the local-ring instance
  and `MvPowerSeries.isUnit_iff_constantCoeff` are in
  `Mathlib/RingTheory/MvPowerSeries/Inverse.lean`.

* Put `m := IsLocalRing.maximalIdeal R`.  First prove the small API lemma
  `m = RingHom.ker MvPowerSeries.constantCoeff`.  Use
  `IsLocalRing.ker_eq_maximalIdeal` from
  `Mathlib/RingTheory/LocalRing/MaximalIdeal/Basic.lean`; constant coefficient
  is onto because `MvPowerSeries.C` is a section (`constantCoeff_C`).  Retain
  the resulting residue-field equivalence
  `R ⧸ m ≃+* k`, obtained from
  `RingHom.quotientKerEquivOfSurjective` in
  `Mathlib/RingTheory/Ideal/Quotient/Operations.lean`.
  Install the non-instance field structure explicitly with
  `letI : Field (R ⧸ m) := Ideal.Quotient.field m`; Mathlib deliberately does
  not make this structure an instance.

* Isolate the only power-series calculation as a helper, for every `n` and
  `f : R`:
  `f ∈ m ^ n ↔ ∀ d : Fin 2 →₀ ℕ, d.degree < n →
    MvPowerSeries.coeff d f = 0`.
  For the forward direction use the description of `m` above and convolution.
  For the reverse direction partition the exponents of total degree at least
  `n` by `i = min (d 0) n`, and write `f` as the finite sum, for
  `i : Fin (n + 1)`, of
  `X 0 ^ i * X 1 ^ (n - i) * f_i`.  Define each `f_i` coefficientwise.
  Extensionality plus `MvPowerSeries.coeff_monomial_mul` verifies the
  decomposition.  The reusable facts `X_pow_eq`, `monomial_mul_monomial`,
  `coeff_monomial_mul`, and `MvPowerSeries.ext` are all in
  `Mathlib/RingTheory/MvPowerSeries/Basic.lean`.

* Name `N n : Submodule R R := m ^ n • ⊤`.  Derive the quotient-facing lemma
  for `x : N n`:
  `x ∈ m • (⊤ : Submodule R (N n)) ↔ (x : R) ∈ m ^ (n + 1)`.
  Use `Submodule.mem_smul_top_iff` and `Ideal.smul_eq_mul` from
  `Mathlib/RingTheory/Ideal/Operations.lean`, followed by `Ideal.mul_top` and
  `pow_succ'`.  This lemma should be used everywhere below instead of
  unfolding `hilbertGradedPiece` repeatedly.

* Construct a semilinear coefficient map from `N n` to
  `Fin (n + 1) → k`, sending `f` to the coefficients at
  `single 0 i + single 1 (n - i)`.  Regard the codomain as an
  `R ⧸ m`-module through the residue-field equivalence.  When checking scalar
  linearity, the preceding vanishing lemma kills every nonconstant term of
  the scalar.  The degree-`n` coefficient map kills the denominator by the
  quotient-facing lemma, so descend it with `Submodule.liftQ` from
  `Mathlib/LinearAlgebra/Quotient/Basic.lean` to a map
  `hilbertGradedPiece R n →ₗ[R ⧸ m] Fin (n + 1) → k`.

* Prove this descended map bijective.  Injectivity says that an element of
  `m^n` whose degree-`n` coefficients vanish belongs to `m^(n+1)`, exactly the
  power-series helper.  For surjectivity, lift a function `a` to the class of
  the finite sum
  `∑ i, C (a i) * X 0 ^ i * X 1 ^ (n - i)` and compute its coefficients using
  the same `Basic.lean` lemmas.  Package it with `LinearEquiv.ofBijective`.

* Finally rewrite `hilbertFunction`, use `LinearEquiv.finrank_eq`, then
  `Module.finrank_fintype_fun_eq_card` from
  `Mathlib/LinearAlgebra/Dimension/Constructions.lean` and
  `Fintype.card_fin` to obtain `n + 1`.  Supply the four inferred structures
  in the existential with
  `⟨R, inferInstance, inferInstance, inferInstance, ...⟩`.

Known dead end: `MvPowerSeries.toAdicCompletionAlgEquiv` does not by itself
identify the maximal-ideal powers or the two submodule quotients used by
`hilbertGradedPiece`; attempting to simplify through that equivalence merely
moves the missing coefficient/power lemma to the completion side.
-/
/-- There is a noetherian local ring whose Hilbert function is `n + 1`. -/
theorem exists_noetherian_local_ring_hilbertFunction_eq_succ :
    ∃ (R : Type u) (hR : CommRing R) (hlocal : IsLocalRing R)
      (hnoeth : IsNoetherianRing R),
      ∀ n : ℕ, @hilbertFunction R hR hlocal hnoeth n = n + 1 := by
  sorry

end

end Formalization.Books.Exercises.Unit57
