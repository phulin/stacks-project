import Formalization.Books.Exercises.Unit57.HilbertFunctionAllowed
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Dimension.RankNullity
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# Exercises, Chapter 57: a prohibited Hilbert function

This file records the numerical consequence of the three initial values in
the source.
-/

namespace Formalization.Books.Exercises.Unit57

universe u

/-
Proof roadmap (the degree-three Macaulay bound).

No hypothesis needs changing.  For a local ring, multiplication of ideal
powers makes `⊕ n, m^n / m^(n+1)` standard graded over `R ⧸ m`; the proof must
expose that fact because `hilbertGradedPiece` currently presents only the
individual modules.  The assumptions `h1` and `h2` are therefore the degree
one and degree two dimensions of a standard-graded algebra, not dimensions of
three unrelated vector spaces.  (`h0` records the conventional initial value
but is not needed once `h1 = 3` rules out the degenerate case.)

* Let `m := IsLocalRing.maximalIdeal R`, `K := R ⧸ m`, and
  `G n := hilbertGradedPiece R n`.  Install
  `letI : Field K := Ideal.Quotient.field m` explicitly; the quotient field
  structure is intentionally a non-instance.  First add the same quotient-facing helper
  used in `HilbertFunctionAllowed.lean`: for
  `N n := m ^ n • (⊤ : Submodule R R)` and `x : N n`,
  `x ∈ m • (⊤ : Submodule R (N n)) ↔ (x : R) ∈ m ^ (n + 1)`.
  Its proof is `Submodule.mem_smul_top_iff`, `Ideal.smul_eq_mul`,
  `Ideal.mul_top`, and `pow_succ'` from
  `Mathlib/RingTheory/Ideal/Operations.lean`.

* Define the graded multiplication
  `gradedMul (i j : ℕ) : G i →ₗ[K] G j →ₗ[K] G (i + j)` by multiplying
  representatives.  Construct the bilinear map on `N i × N j`, and descend
  through both quotients with `LinearMap.liftQ₂` from
  `Mathlib/LinearAlgebra/Quotient/Bilinear.lean`.  Well-definedness is the
  pair of containments
  `m^(i+1) * m^j ≤ m^(i+j+1)` and
  `m^i * m^(j+1) ≤ m^(i+j+1)`; normalize them with `← pow_add`.
  Record application, zero, scalar, associativity, and commutativity lemmas
  immediately, so the main proof never unfolds this construction.

* The noetherian instances already synthesize
  `Module.Finite K (G n)`.  From `h1` (after unfolding `hilbertFunction`), take
  `b : Module.Basis (Fin 3) K (G 1) :=
    Module.finBasisOfFinrankEq K (G 1) h1`.
  `Module.Free.of_divisionRing` is supplied by
  `Mathlib/LinearAlgebra/Basis/VectorSpace.lean`, while the finite basis
  declaration is in `Mathlib/LinearAlgebra/Dimension/Free.lean`.
  For each `n`, set
  `H n := MvPolynomial.homogeneousSubmodule (Fin 3) K n`.  Define
  `evalGraded b n : H n →ₗ[K] G n` on a monomial of total degree `n` as the
  iterated `gradedMul` product of the three elements `b i`, and extend by the
  monomial basis.  Useful exact APIs are
  `MvPolynomial.homogeneousSubmodule_eq_finsupp_supported` and
  `MvPolynomial.isHomogeneous_monomial` in
  `Mathlib/RingTheory/MvPolynomial/Homogeneous.lean`, together with
  `MvPolynomial.basisRestrictSupport` and `basisMonomials` in
  `Mathlib/RingTheory/MvPolynomial/Basic.lean`.

* Prove `evalGraded b n` surjective by induction on `n`.  Expand membership in
  `m^(n+1) = m^n * m`; write a representative as a finite sum of products,
  map the degree-one factors to their coordinates in `b`, and discard every
  replacement error in `m^(n+2)` using the quotient-facing helper.  This is
  the formal standard-graded claim and is the point at which the local-ring
  origin of the Hilbert function is used.

* Establish the two small source dimensions separately, without a general
  stars-and-bars development:
  `Module.finrank K (H 2) = 6` and
  `Module.finrank K (H 3) = 10`.
  Reindex `MvPolynomial.basisRestrictSupport` along explicit equivalences from
  `{d : Fin 3 →₀ ℕ // d.degree = 2}` to `Fin 6`, and from the corresponding
  degree-three subtype to `Fin 10`; prove the inverse laws by `fin_cases` on
  the three coordinates.  Finish each count with
  `Module.finrank_eq_card_basis` and `Fintype.card_fin`.

* Apply rank-nullity to the surjection `evalGraded b 2`.  The equivalence
  `(evalGraded b 2).quotKerEquivRange`, `LinearMap.range_eq_top.mpr`, and
  `Submodule.finrank_quotient_add_finrank` from
  `Mathlib/LinearAlgebra/Dimension/RankNullity.lean`, together with `h2`, give
  `Module.finrank K (LinearMap.ker (evalGraded b 2)) = 1`.  Choose a basis
  vector `q` of this kernel; its subtype in `H 2` is nonzero.

* Show that the three cubics `X i * q` lie in
  `LinearMap.ker (evalGraded b 3)` by the multiplication lemma for
  `evalGraded`.  They are linearly independent: a relation is
  `(∑ i, C (a i) * X i) * q = 0`; the `IsDomain` instance for
  `MvPolynomial (Fin 3) K` is in
  `Mathlib/Algebra/MvPolynomial/Basic.lean`, so `q ≠ 0` forces the linear form
  to vanish, and its coefficients at `Finsupp.single i 1` are the `a i`.
  Thus a three-dimensional span is contained in the degree-three kernel;
  use `Submodule.finrank_le` from
  `Mathlib/LinearAlgebra/Dimension/Constructions.lean` to get
  `3 ≤ finrank K (ker (evalGraded b 3))`.

* Rank-nullity for the surjection in degree three now gives
  `hilbertFunction R 3 + finrank K (ker (evalGraded b 3)) = 10`.
  Combine it with the preceding lower bound to conclude
  `hilbertFunction R 3 ≤ 7` by ordinary natural-number arithmetic.

Known dead end: there is no Macaulay-growth theorem or usable associated-
graded-ring construction in the current Mathlib/project imports.  Applying
linear arithmetic directly to `h0`, `h1`, and `h2` loses the multiplication
that makes the assertion true; build `gradedMul` and `evalGraded` first.
-/
theorem hilbertFunction_third_le_seven
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (h0 : hilbertFunction R 0 = 1)
    (h1 : hilbertFunction R 1 = 3)
    (h2 : hilbertFunction R 2 = 5) :
    hilbertFunction R 3 ≤ 7 := by
  sorry

end Formalization.Books.Exercises.Unit57
