import Formalization.Books.Exercises.Unit21.Core

import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.KrullDimension.NonZeroDivisors

/-!
# Exercises, Chapter 21: Dimension of fibres

This file records the theorem interfaces for the two numbered exercises.
Proofs are deferred to the proving stage.
-/

namespace Formalization.Books.Exercises.Unit21

universe u

noncomputable section

/-! ## Exercise `nr-components-fibre` -/

/- The source's phrase “finite type extension of domains” is represented by
   an injective finite-type ring homomorphism with a domain as target.  The
   polynomial source rings are domains under the field hypotheses.  Example
   targets live in the coefficient field's universe; an unrelated target
   universe would impose an unjustified cardinality constraint on the required
   injection. -/

/-- For every `n ≥ 0`, there is a finite-type domain extension of `k[x]`
whose zero fibre has exactly `n` irreducible components. -/
theorem exists_finiteType_domain_extension_with_fibre_component_cardinal
    (k : Type u) [Field k] [IsAlgClosed k] :
    ∀ n : ℕ,
      ∃ (A : Type u) (_ : CommRing A)
        (f : oneVariablePolynomialRing k →+* A),
        IsDomain A ∧ Function.Injective f ∧ RingHom.FiniteType f ∧
          fibreComponentCardinal f (oneVariableOriginIdeal k) = (n : ℕ∞) := by
  /-
  Proof roadmap.

  1. Split on `n`.  For zero use
     `A := Localization.Away (Polynomial.X : Polynomial k)` and the canonical
     algebra map.  Its injectivity is `IsLocalization.injective`, using
     `powers_le_nonZeroDivisors_of_noZeroDivisors`; finite type is
     `IsLocalization.finiteType_of_monoid_fg` together with
     `Submonoid.powers_fg` (all in
     `Mathlib/RingTheory/Localization/InvSubmonoid.lean`).  The image of `(X)`
     is top by `Ideal.map_span`,
     `IsLocalization.Away.algebraMap_isUnit`, and
     `Ideal.span_singleton_eq_top`.  Thus the quotient has empty spectrum by
     `PrimeSpectrum.nonempty_iff_nontrivial`, so its component encard is zero.

  2. For `n = m + 1`, choose distinct `a : Fin (m + 1) → k` by composing
     `Fin.valEmbedding` with `Infinite.natEmbedding k`, and put
     `p := ∏ i, (Polynomial.X - Polynomial.C (a i))`.  Take
     `A := Polynomial k` and `f := (Polynomial.aeval p).toRingHom`.
     `Polynomial.transcendental` plus `transcendental_iff_injective` proves
     injectivity (the degree is `m + 1` and the leading coefficient is one).
     Prove `f.FiniteType` directly from the singleton generator `{X}`:
     constants are already in the image of `f`, and `Polynomial.induction_on'`
     proves `Algebra.adjoin (Polynomial k) {X} = ⊤` for `f.toAlgebra`.

  3. Simplify the mapped origin ideal to `Ideal.span {p}`.  The factors are
     pairwise coprime because `a` is injective.  Use
     `Ideal.iInf_span_singleton`,
     `Ideal.quotientInfRingEquivPiQuotient`, and
     `Polynomial.quotientSpanXSubCAlgEquiv` (respectively in
     `Mathlib/RingTheory/Ideal/Operations.lean`,
     `Ideal/Quotient/Operations.lean`, and `Polynomial/Quotient.lean`) to
     obtain a ring equivalence from the fibre to `Fin (m + 1) → k`.

  4. Compute the component encard of that product.  The homeomorphism
     `PrimeSpectrum.sigmaToPiHomeo` identifies its spectrum with
     `Σ i : Fin (m + 1), PrimeSpectrum k`; each field spectrum has one
     point.  Equivalently transfer through
     `minimalPrimes.equivIrreducibleComponents`, and finish with
     `Set.encard_congr` and `Set.encard_univ`.  Transport components across
     the ring equivalence with `PrimeSpectrum.homeomorphOfRingEquiv` and
     `irreducibleComponentsEquivOfIsPreirreducibleFiber`; alternatively use
     the order equivalence `PrimeSpectrum.comapEquiv` on minimal primes.
  -/
  sorry

/-- There is a finite-type domain extension of `k[x]` whose fibre over every
closed point is nonempty and reducible. -/
theorem exists_finiteType_domain_extension_with_all_fibres_reducible
    (k : Type u) [Field k] [IsAlgClosed k] :
    ∃ (A : Type u) (_ : CommRing A)
      (f : oneVariablePolynomialRing k →+* A),
      IsDomain A ∧ Function.Injective f ∧ RingHom.FiniteType f ∧
        ∀ α : k,
          Nonempty (PrimeSpectrum (fibreRing f (oneVariablePointIdeal k α))) ∧
            fibreIsReducible f (oneVariablePointIdeal k α) := by
  /-
  Proof roadmap.

  1. Use `A := Polynomial k`, `q := X ^ 3 - X`, and
     `f := (Polynomial.aeval q).toRingHom`.  As in the preceding proof,
     `Polynomial.transcendental` and `transcendental_iff_injective` give
     injectivity, while `{X}` and `Polynomial.induction_on'` give
     `RingHom.FiniteType f`.

  2. For `α : k`, rewrite the fibre as
     `Polynomial k ⨸ Ideal.span {q - Polynomial.C α}` using
     `Ideal.map_span` and `Polynomial.aeval_X`.  It is nontrivial because this
     monic cubic is not a unit (`Polynomial.isUnit_iff` and its nat-degree),
     and `PrimeSpectrum.nonempty_iff_nontrivial` then supplies a point.

  3. Prove a local helper saying `q - C α` has two distinct roots.  It
     splits by `IsAlgClosed.splits_domain`.  If it had only one distinct root
     `r`, `Polynomial.Splits.eq_prod_roots_of_monic` would identify it with
     `(X - C r) ^ 3`.  Comparing the `X²` and `X` coefficients gives
     `3 * r = 0` and `3 * r ^ 2 = -1`; multiplying the first equality by `r`
     is a contradiction in every characteristic.  This coefficient argument
     avoids a characteristic split.

  4. The two root ideals `span {X - C r}` and `span {X - C s}` yield distinct
     minimal primes over `span {q - C α}`.  Establish minimality either by
     the PID divisibility description or by applying the Chinese remainder
     tools from the preceding roadmap to the distinct-root primary factors.
     Transfer them to distinct minimal primes of the quotient with
     `Ideal.isPrime_map_quotientMk_of_isPrime`.  If the fibre spectrum were
     irreducible, `irreducibleComponents_eq_singleton` together with
     `minimalPrimes.equivIrreducibleComponents` would force a unique minimal
     prime, a contradiction.  Unfold `fibreIsReducible` for the conclusion.
  -/
  sorry

/-- There is a finite-type domain extension of `k[x,y]` whose non-origin
fibres are irreducible and whose origin fibre is nonempty and reducible. -/
theorem exists_finiteType_domain_extension_with_irreducible_nonzero_fibres
    (k : Type u) [Field k] [IsAlgClosed k] :
    ∃ (A : Type u) (_ : CommRing A)
      (f : twoVariablePolynomialRing k →+* A),
      IsDomain A ∧ Function.Injective f ∧ RingHom.FiniteType f ∧
        (∀ α β : k, ((α, β) : k × k) ≠ (0, 0) →
          fibreIsIrreducible f (twoVariablePointIdeal k α β)) ∧
        Nonempty (PrimeSpectrum (fibreRing f (twoVariablePointIdeal k 0 0))) ∧
          fibreIsReducible f (twoVariablePointIdeal k 0 0) := by
  /-
  Proof roadmap.

  1. Let `A := MvPolynomial (Fin 4) k`, name its variables
     `Y := X 0`, `U := X 1`, `V := X 2`, `W := X 3`, and define
     `f := (MvPolynomial.aeval ![U * V - Y * W, Y]).toRingHom`.
     A specialization `A →+* MvPolynomial (Fin 2) k` sending
     `(Y,U,V,W)` to `(X 1, X 0, 1, 0)` is a left inverse to `f`; use
     `MvPolynomial.eval₂Hom` and `Function.LeftInverse.injective`.
     The four target variables form a finite generating set over `f`, so
     `MvPolynomial.adjoin_range_X` proves `f.FiniteType`.  The target is a
     domain by the standard multivariate-polynomial instance.

  2. For a point `(α,β)`, simplify the mapped point ideal to
     `Jαβ := span {U * V - Y * W - C α, Y - C β}`.  When
     `β ≠ 0`, evaluation at
     `Y = β, W = β⁻¹ * (U * V - α)` is a surjection onto
     `MvPolynomial (Fin 2) k` with kernel `Jαβ`.  Prove the kernel equality
     by `MvPolynomial.induction_on` in `Y,W`, then use
     `RingHom.quotientKerEquivOfSurjective`.  The quotient is a domain, hence
     its spectrum is irreducible by `PrimeSpectrum.irreducibleSpace`.

  3. When `β = 0` and `α ≠ 0`, first eliminate `Y`; the quotient is
     `k[U,V,W]/(U*V-α)`.  Regard the relation as linear in `V` and apply
     `MvPolynomial.irreducible_mul_X_add` from
     `Mathlib/RingTheory/MvPolynomial/IrreducibleQuadratic.lean`; the nonzero
     constant is relatively prime to `U`.  In the UFD polynomial ring this
     irreducible is prime, so `Ideal.isPrime_span_singleton_of_prime` makes
     the quotient a domain.  This covers every non-origin point.

  4. At the origin the same elimination gives `k[U,V,W]/(U*V)`.  It is
     nontrivial by evaluation at zero.  The images of `(U)` and `(V)` are two
     distinct minimal primes (use
     `Ideal.span_singleton_mul_span_singleton` and primality of the variable
     ideals), so `minimalPrimes.equivIrreducibleComponents` proves the
     spectrum reducible.  Do not use the tempting family `U*V = x`: its
     fibres over `(0,β)` would remain reducible and fail the statement.
  -/
  sorry

/-! ## Exercise `codim-1` -/

/-- The codimension-one exercise's dimension bounds for a nonzero origin
fibre.  Dimensions use Mathlib's canonical `ringKrullDim`, whose values are
in `WithBot ℕ∞`; the source's natural number `d` is inserted canonically. -/
theorem fibre_dimension_bounds_at_coordinate_origin
    (k : Type u) [Field k] [IsAlgClosed k]
    (n : ℕ) (hn : 1 ≤ n)
    {A : Type u} [CommRing A] [IsDomain A]
    (f : nVariablePolynomialRing k n →+* A)
    (hinj : Function.Injective f) (hfinite : RingHom.FiniteType f)
    (d : ℕ)
    (hdim : ringKrullDim A = (((d : ℕ∞) : WithBot ℕ∞)))
    (hfibre : Nontrivial (fibreRing f (coordinateOriginIdeal k n))) :
    (((d - n : ℕ) : ℕ∞) : WithBot ℕ∞) ≤
        ringKrullDim (fibreRing f (coordinateOriginIdeal k n)) ∧
      ringKrullDim (fibreRing f (coordinateOriginIdeal k n)) ≤
        (((d - 1 : ℕ) : ℕ∞) : WithBot ℕ∞) := by
  /-
  Proof roadmap.

  1. Put `I := (coordinateOriginIdeal k n).map f` and install
     `f.toAlgebra`.  Compose `MvPolynomial.C` with `f`; finite type follows
     from `RingHom.FiniteType.comp hfinite` and the finite-type polynomial
     instance.  Hence `A` is a finite-type `k`-algebra and is Noetherian by
     `Algebra.FiniteType.isNoetherianRing`.  Use `hfibre` as the
     `Nontrivial (A ⨸ I)` instance, so `I ≠ ⊤`.

  2. For the upper bound choose `i₀ : Fin n` from `hn`.  Injectivity makes
     `f (MvPolynomial.X i₀)` nonzero; in the domain `A` it belongs to
     `A⁰`.  It also lies in `I`.  Apply
     `ringKrullDim_succ_le_of_surjective` from
     `Mathlib/RingTheory/KrullDimension/NonZeroDivisors.lean` to
     `Ideal.Quotient.mk I`.  Rewriting with `hdim` gives
     `dim(A/I) + 1 ≤ d`, and finite `WithBot ℕ∞` arithmetic gives
     `dim(A/I) ≤ d - 1`.

  3. For the lower bound choose a maximal ideal `M ≥ I` with
     `Ideal.exists_le_maximal`.  Its contraction is the coordinate-origin
     ideal: the latter is maximal (prove its quotient is `k` by evaluation at
     zero), while the contraction is proper and contains it.  Let `p,q` be
     the corresponding points of the source and target spectra.

  4. Import and apply
     `Formalization.Books.Algebra.Unit112.ringKrullDim_localization_le_base_add_fibre`
     from `Formalization/Books/Algebra/Unit112/HomomorphismsAndDimension.lean`.
     The target local dimension is `d`: apply
     `Formalization.Books.Algebra.Unit116.dimension_prime_polynomial_ring`
     from `.../Unit116/DimensionFiniteTypeAlgebrasReprise.lean` to `A` with
     `K := FractionRing A`, then identify its global dimension using `hdim`.
     The same theorem applied to `MvPolynomial (Fin n) k`, together with
     `MvPolynomial.ringKrullDim_of_isNoetherianRing`, makes the source local
     dimension `n`.

  5. Transport `Unit112.localRingOfFibre` to the localization of `A/I` at the
     prime induced by `M` with
     `Formalization.Books.Algebra.Unit112.localRingOfFibre_equiv_localized_quotient`.
     Its dimension is that prime's height by
     `IsLocalization.AtPrime.ringKrullDim_eq_height`, and
     `Ideal.height_le_ringKrullDim_of_ne_top` bounds it by `ringKrullDim (A/I)`.
     Thus `d ≤ n + dim(A/I)`; convert the finite values to naturals and
     rearrange to `d - n ≤ dim(A/I)`.  This local argument is needed:
     `ringKrullDim_le_ringKrullDim_quotient_add_spanFinrank` cannot be applied
     globally because `I` need not lie in `Ring.jacobson A`.
  -/
  sorry

/-- Every natural value in the interval supplied by the preceding bounds is
realized by the origin fibre of a finite-type domain extension. -/
theorem exists_finiteType_domain_extension_for_every_admissible_fibre_dimension
    (k : Type u) [Field k] [IsAlgClosed k]
    (n : ℕ) (hn : 1 ≤ n) :
    ∀ d e : ℕ, n ≤ d → d - n ≤ e → e ≤ d - 1 →
      ∃ (A : Type u) (_ : CommRing A)
        (f : nVariablePolynomialRing k n →+* A),
        IsDomain A ∧ Function.Injective f ∧ RingHom.FiniteType f ∧
          ringKrullDim A = (((d : ℕ∞) : WithBot ℕ∞)) ∧
          Nontrivial (fibreRing f (coordinateOriginIdeal k n)) ∧
          ringKrullDim (fibreRing f (coordinateOriginIdeal k n)) =
            (((e : ℕ∞) : WithBot ℕ∞)) := by
  /-
  Proof roadmap.

  1. Fix admissible `d,e` and put `r := d - e`.  The hypotheses imply
     `1 ≤ r`, `r ≤ n`, `n - r ≤ e`, and `r + e = d`; isolate these
     natural-number facts with `omega` before defining any `Fin` maps.

  2. Take `A := MvPolynomial (Fin d) k`.  Define the images of the source
     variables by
       `z i = X i` for `i.val < r`, and
       `z i = X 0 * X i` for `r ≤ i.val`
     (use `n ≤ d` to cast `i : Fin n` to `Fin d`), and set
     `f := (MvPolynomial.aeval z).toRingHom`.  Constants commute automatically.
     The exponent map on monomials sends `a₀` to
     `a₀ + ∑ i ≥ r, aᵢ` and leaves every other source exponent visible;
     it is injective.  Expand with `MvPolynomial.aeval_monomial` and use
     `Finsupp.mapDomain_injective`/`AddMonoidAlgebra.mapDomain_injective` to
     prove `f` injective.  All `d` target variables are a finite set of
     algebra generators, so `MvPolynomial.adjoin_range_X` proves finite type.

  3. Since `r ≥ 1`, the mapped coordinate-origin ideal is exactly the ideal
     generated by `X 0,…,X (r-1)`; the remaining images are already multiples
     of `X 0`.  Reindex `Fin d` as `Fin r ⊕ Fin e` using
     `finSumFinEquiv`, `MvPolynomial.renameEquiv`, and
     `MvPolynomial.sumAlgEquiv` (`Mathlib/Algebra/MvPolynomial/Equiv.lean`).
     Evaluation of the first block at zero, followed by
     `RingHom.quotientKerEquivOfSurjective`, identifies the fibre with
     `MvPolynomial (Fin e) k`.  This also gives its `Nontrivial` instance.

  4. Compute dimensions with
     `MvPolynomial.ringKrullDim_of_isNoetherianRing` from
     `Mathlib/RingTheory/KrullDimension/Polynomial.lean` and
     `ringKrullDim_eq_zero_of_field`; the target has dimension `d` and the
     fibre has dimension `e`.  Package the standard domain instance, injectivity,
     finite type, the quotient equivalence, and both dimension equalities in
     the existential conjunction.
  -/
  sorry

/-- For at least two base variables, some origin fibres have irreducible
components of different Krull dimensions.  The lower bound is necessary:
for one variable the nonzero fibre ideal is principal in an affine domain, so
all its minimal primes have height one and its components are equidimensional. -/
theorem exists_finiteType_domain_extension_with_mixed_fibre_component_dimensions
    (k : Type u) [Field k] [IsAlgClosed k]
    (n : ℕ) (hn : 2 ≤ n) :
    ∃ (A : Type u) (_ : CommRing A)
      (f : nVariablePolynomialRing k n →+* A),
      IsDomain A ∧ Function.Injective f ∧ RingHom.FiniteType f ∧
        ∃ C D : Set
            (PrimeSpectrum (fibreRing f (coordinateOriginIdeal k n))),
          C ∈ irreducibleComponents
              (PrimeSpectrum (fibreRing f (coordinateOriginIdeal k n))) ∧
          D ∈ irreducibleComponents
              (PrimeSpectrum (fibreRing f (coordinateOriginIdeal k n))) ∧
          fibreComponentDimension f (coordinateOriginIdeal k n) C ≠
            fibreComponentDimension f (coordinateOriginIdeal k n) D := by
  /-
  Proof roadmap.

  1. Let `A := MvPolynomial (Fin (n + 1)) k`, with first variables `a,b,c`.
     Send source variables by
       `x₀ ↦ a*b`, `x₁ ↦ a*c`, and `xᵢ ↦ X (i+1)` for `i ≥ 2`.
     The casts are justified by `hn`.  On monomial exponents the `b` and `c`
     coordinates recover the first two source exponents and the later
     coordinates recover the rest, so the same
     `MvPolynomial.aeval_monomial`/`Finsupp.mapDomain_injective` argument as in
     the preceding roadmap proves injectivity.  The target is a domain and
     `MvPolynomial.adjoin_range_X` gives finite type.

  2. The mapped origin ideal is
     `J = (a*b, a*c, X 3, ..., X n)`.  In `A` set
     `P = (a, X 3, ..., X n)` and
     `Q = (b, c, X 3, ..., X n)`.  Prove `J = P ⊓ Q` using
     `Ideal.span_singleton_mul_span_singleton`, distributivity of ideal
     products, and coefficient evaluation; both `P` and `Q` are prime because
     their quotients are polynomial rings.  They are incomparable, hence are
     exactly the minimal primes over `J`.

  3. In the fibre `B := A ⨸ J`, map `P` and `Q` by
     `Ideal.Quotient.mk J`.  Use
     `Ideal.isPrime_map_quotientMk_of_isPrime` and the equality from step 2 to
     show that the two images are distinct minimal primes of `B`.  Let `C,D`
     be their zero loci.  Their component membership follows from
     `PrimeSpectrum.zeroLocus_ideal_mem_irreducibleComponents`, or directly
     from `minimalPrimes.equivIrreducibleComponents` in
     `Mathlib/RingTheory/Spectrum/Prime/Topology.lean`.

  4. The component `C` is homeomorphic to `Spec(A/P) ≃ Spec(k[b,c])`, while
     `D` is homeomorphic to `Spec(A/Q) ≃ Spec(k[a])`.  Build the quotient
     ring equivalences by evaluation and
     `RingHom.quotientKerEquivOfSurjective`.  For the zero-locus subspaces use
     `PrimeSpectrum.isClosedEmbedding_comap_of_surjective` and its induced
     homeomorphism.  Then
     `PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim` and
     `MvPolynomial.ringKrullDim_of_isNoetherianRing` compute the two values as
     `2` and `1`.  Unfold `fibreComponentDimension` and close their inequality
     by `norm_num`.
  -/
  sorry

end

end Formalization.Books.Exercises.Unit21
