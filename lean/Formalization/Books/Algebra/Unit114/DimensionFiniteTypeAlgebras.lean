import Formalization.Books.Algebra.Unit104.CohenMacaulayRings
import Formalization.Books.Algebra.Unit105.CatenaryRings
import Formalization.Books.Algebra.Unit110.RegularRingsAndGlobalDimension
import Formalization.Books.Topology.Unit10.KrullDimension
import Formalization.Books.Topology.Unit11.CodimensionAndCatenary
import Mathlib.RingTheory.Idempotents
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.RegularLocalRing.Polynomial
import Mathlib.RingTheory.Spectrum.Maximal.Localization
import Mathlib.RingTheory.Spectrum.Prime.Jacobson
import Mathlib.Topology.Clopen

/-!
# Commutative Algebra, Chapter 114: Dimension of finite type algebras over fields

The polynomial algebra in `n` variables is represented by
`MvPolynomial (Fin n) k`.  Krull dimensions use Mathlib's `ringKrullDim`,
prime heights use `Ideal.height`, and local dimensions of spectra use the
topological `krullDimensionAt` from Topology, Chapter 10.
-/

namespace Formalization.Books.Algebra.Unit114

universe u v

noncomputable section

open Set
open TopologicalSpace
open Formalization.Books.Topology.Unit10
open Formalization.Books.Topology.Unit11

/-! ## Local dimensions and components -/

/- The source's maximum over irreducible components through a point is the
   set of their canonical topological Krull dimensions. -/
def componentDimensionsAtPoint
    {X : Type u} [TopologicalSpace X] (x : X) : Set (WithBot ℕ∞) :=
  {d | ∃ Z : Set X,
    Z ∈ irreducibleComponents X ∧ x ∈ Z ∧ topologicalKrullDim Z = d}

/- The source's minimum over maximal localizations above a prime is recorded
   using the canonical maximal spectrum and localization at that ideal. -/
def maximalLocalDimensionsAbove
    {S : Type u} [CommRing S] (p : PrimeSpectrum S) : Set (WithBot ℕ∞) :=
  {d | ∃ m : MaximalSpectrum S,
    p.asIdeal ≤ m.asIdeal ∧
      ringKrullDim (Localization.AtPrime m.asIdeal) = d}

private lemma isIrreducible_preimage_of_isInducing
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : Y → X} (hf : _root_.Topology.IsInducing f) {s : Set X}
    (hs : IsIrreducible s) (hsrange : s ⊆ Set.range f) :
    IsIrreducible (f ⁻¹' s) := by
  refine ⟨?_, ?_⟩
  · rcases hs.nonempty with ⟨x, hx⟩
    rcases hsrange hx with ⟨y, rfl⟩
    exact ⟨y, hx⟩
  · intro u v hu hv hU hV
    rcases hf.isOpen_iff.mp hu with ⟨u', huopen, hu_eq⟩
    rcases hf.isOpen_iff.mp hv with ⟨v', hvopen, hv_eq⟩
    have hsu : (s ∩ u').Nonempty := by
      rw [← hu_eq] at hU
      rcases hU with ⟨y, hyS, hyU⟩
      exact ⟨f y, hyS, hyU⟩
    have hsv : (s ∩ v').Nonempty := by
      rw [← hv_eq] at hV
      rcases hV with ⟨y, hyS, hyV⟩
      exact ⟨f y, hyS, hyV⟩
    rcases hs.2 u' v' huopen hvopen hsu hsv with ⟨x, hxs, hxu, hxv⟩
    rcases hsrange hxs with ⟨y, rfl⟩
    refine ⟨y, hxs, ?_⟩
    constructor
    · rw [← hu_eq]
      exact hxu
    · rw [← hv_eq]
      exact hxv

private theorem topologicalKrullDim_le_iSup_componentDimensions
    {X : Type u} [TopologicalSpace X] :
    topologicalKrullDim X ≤
      ⨆ Z : irreducibleComponents X, topologicalKrullDim (Z : Set X) := by
  rw [topologicalKrullDim, Order.krullDim_eq_iSup_height]
  refine iSup_le fun A => ?_
  obtain ⟨Z, hZ, hAZ⟩ :=
    exists_mem_irreducibleComponents_subset_of_isIrreducible
      (A : Set X) A.isIrreducible
  have hZnebot : topologicalKrullDim (Z : Set X) ≠ ⊥ := by
    rw [topologicalKrullDim, Order.krullDim_ne_bot_iff]
    let U : IrreducibleCloseds Z :=
      { carrier := Set.univ
        isIrreducible' :=
          @IrreducibleSpace.isIrreducible_univ Z _ (Subtype.irreducibleSpace hZ.1)
        isClosed' := isClosed_univ }
    exact ⟨U⟩
  have hheight : Order.height A ≤ topologicalKrullDim (Z : Set X) := by
    rw [← WithBot.le_unbotD_iff (a := 0) hZnebot]
    apply Order.height_le
    intro C hC
    let f : Z → X := (↑)
    have hf : _root_.Topology.IsClosedEmbedding f :=
      (isClosed_of_mem_irreducibleComponents Z hZ).isClosedEmbedding_subtypeVal
    let g : {V : IrreducibleCloseds X // (V : Set X) ⊆ Z} →
        IrreducibleCloseds Z := fun V =>
      { carrier := f ⁻¹' (V : Set X)
        isIrreducible' :=
          isIrreducible_preimage_of_isInducing hf.isInducing V.1.isIrreducible
            (fun x hx => ⟨⟨x, V.2 hx⟩, rfl⟩)
        isClosed' := V.1.isClosed.preimage hf.continuous }
    have hg : StrictMono g := by
      intro V W hVW
      apply lt_of_le_of_ne
      · change f ⁻¹' (V : Set X) ⊆ f ⁻¹' (W : Set X)
        exact Set.preimage_mono hVW.le
      · intro hEq
        apply hVW.2
        intro x hx
        have hxZ : x ∈ Z := W.2 hx
        have hx' : (⟨x, hxZ⟩ : Z) ∈ (g W : Set Z) := by
          exact hx
        have hx'' : (⟨x, hxZ⟩ : Z) ∈ (g V : Set Z) := by
          rw [hEq]
          exact hx'
        exact hx''
    have hsubset : ∀ i : Fin (C.length + 1),
        ((C i : IrreducibleCloseds X) : Set X) ⊆ Z := by
      intro i x hx
      have hi : (C i : Set X) ⊆ (C.last : Set X) :=
        C.monotone (Fin.le_last _)
      apply hAZ
      rw [← hC]
      exact hi hx
    let D : LTSeries (IrreducibleCloseds Z) :=
      { length := C.length
        toFun := fun i => g ⟨C i, hsubset i⟩
        step := fun i => hg (C.step i) }
    rw [WithBot.le_unbotD_iff (a := 0) hZnebot]
    simpa [D, topologicalKrullDim] using
      (Order.LTSeries.length_le_krullDim D)
  exact hheight.trans (le_iSup (fun Z : irreducibleComponents X =>
    topologicalKrullDim (Z : Set X)) ⟨Z, hZ⟩)

/-! ## The dimension of affine space -/

/-- A maximal ideal of affine `n`-space has `n` generators and its local ring
has dimension `n` and is regular local. -/
theorem dim_affine_space
    {k : Type u} [Field k] (n : ℕ)
    (m : MaximalSpectrum (MvPolynomial (Fin n) k)) :
    (∃ x : Fin n → MvPolynomial (Fin n) k,
        Ideal.span (Set.range x) = m.asIdeal) ∧
      ringKrullDim (Localization.AtPrime m.asIdeal) = n ∧
        IsRegularLocalRing (Localization.AtPrime m.asIdeal) := by
  /-
  Proof roadmap (the global generator statement is intentional and agrees
  with Stacks 00OO, Lemma 10.114.1; it must not be replaced by generators
  only after localization).

  1. Isolate two small induction lemmas immediately above this theorem.  For
     the generator lemma use

       `MvPolynomial.finSuccEquiv k r :
          MvPolynomial (Fin (r + 1)) k ≃ₐ[k]
            Polynomial (MvPolynomial (Fin r) k)`

     from `Mathlib/Algebra/MvPolynomial/Equiv.lean`.  In the polynomial step,
     for a maximal `P : Ideal R[X]`, put `p := P.comap Polynomial.C`.
     `Polynomial.isMaximal_comap_C_of_isJacobsonRing` from
     `Mathlib/RingTheory/Jacobson/Ring.lean` makes `p` maximal.  Apply the
     induction hypothesis to generators of `p`.  Map `P` to the fibre
     `(R ⨸ p)[X]` using
     `Polynomial.polynomialQuotientEquivQuotientPolynomial`; that image is
     principal by `IsPrincipalIdealRing.principal`.  Lift its generator to
     `R[X]`, append it to the mapped generators of `p`, and prove that their
     span is `P` by mapping along the surjective quotient homomorphism.  The
     useful normalization lemmas are `Ideal.map_span`,
     `Ideal.map_comap_of_surjective`, `Ideal.comap_map_of_surjective`, and
     `Ideal.mk_ker`.  Transport the resulting `Fin (r + 1)` family
     back through `MvPolynomial.finSuccEquiv`; use
     `Ideal.map_span` for the equivalence's ring homomorphism and
     `Set.range_comp`, rather than unfolding `Ideal.span`.
     In the `r = 0` base, transport through
     `MvPolynomial.isEmptyRingEquiv k (Fin 0)`; the unique proper ideal of
     the field is `⊥`, and the empty family spans `⊥`.

  2. Prove the numerical induction separately: every maximal ideal of
     `MvPolynomial (Fin r) k` has height `(r : ℕ∞)`.  In the successor
     step transport the ideal with `MvPolynomial.finSuccEquiv`, contract it
     along `Polynomial.C`, and use
     `Polynomial.height_eq_height_add_one` from
     `Mathlib/RingTheory/KrullDimension/Polynomial.lean`.  Its `LiesOver`
     instance is the contraction equality.  Normalize transport with
     `RingEquiv.height_map`/`RingEquiv.height_comap`; the base uses
     `MvPolynomial.isEmptyRingEquiv k (Fin 0)` and `Ideal.height_bot`.

  3. Apply the generator induction to `m` for the first conjunct.  Rewrite
     the height equality from step 2 as the displayed localization dimension
     with the fully instantiated
     `IsLocalization.AtPrime.ringKrullDim_eq_height m.asIdeal
       (Localization.AtPrime m.asIdeal)` from
     `Mathlib/RingTheory/Ideal/Height.lean`.

  4. `MvPolynomial.isRegularRing_of_isRegularRing` from
     `Mathlib/RingTheory/RegularLocalRing/Polynomial.lean` supplies
     `_root_.IsRegularRing (MvPolynomial (Fin n) k)`.  Specialize
     `_root_.isRegularRing_iff` (Defs.lean) to the prime associated to `m` to
     obtain regularity of its localization, and assemble the conjunction.

  Do not try to obtain step 1 from regularity of the local ring: a generating
  family after localization does not by itself give the required equality of
  ideals in the polynomial ring.
  -/
  sorry

/-- A polynomial algebra over a field is regular of global dimension `n`, and
all of its maximal localizations are regular local rings of dimension `n`. -/
theorem finite_gl_dim_polynomial_ring
    {k : Type u} [Field k] (n : ℕ) :
    Formalization.Books.Algebra.Unit110.IsRegularRing
        (MvPolynomial (Fin n) k) ∧
      Formalization.Books.Algebra.Unit109.globalDimension
          (MvPolynomial (Fin n) k) =
        ((n : ℕ∞) : WithBot ℕ∞) ∧
        ∀ m : MaximalSpectrum (MvPolynomial (Fin n) k),
          IsRegularLocalRing (Localization.AtPrime m.asIdeal) ∧
            ringKrullDim (Localization.AtPrime m.asIdeal) =
              ((n : ℕ∞) : WithBot ℕ∞) := by
  /-
  Proof roadmap:
  1. Put `P := MvPolynomial (Fin n) k`.  Install the canonical Noetherian and
     regular-ring instances.  The regular instance is
     `MvPolynomial.isRegularRing_of_isRegularRing` in
     `Mathlib/RingTheory/RegularLocalRing/Polynomial.lean`.
  2. Compute `ringKrullDim P = ((n : ℕ∞) : WithBot ℕ∞)` with
     `MvPolynomial.ringKrullDim_of_isNoetherianRing` from
     `Mathlib/RingTheory/KrullDimension/Polynomial.lean`; `simp` reduces the
     field dimension and `Nat.card (Fin n)`.
  3. Feed the pair from steps 1--2 to alternative `1` of
     `Formalization.Books.Algebra.Unit110.
       finite_global_dimension_iff_regular_finite_dimension (R := P) n`
     (`RegularRingsAndGlobalDimension.lean`) and take `.out 1 0`.  This gives
     the exact `Unit109.globalDimension P` required by the middle conjunct.
  4. For each maximal `m`, take `.2.2` and `.2.1` respectively from
     `dim_affine_space n m`; cast the natural `n` equality once, then assemble
     the requested order of the two local conclusions.
  -/
  sorry

/-! ## Heights and chains in a polynomial algebra -/

/-- In a polynomial algebra over a field, every maximal prime chain between
two primes has length equal to the difference of their heights. -/
theorem dimension_height_polynomial_ring
    {k : Type u} [Field k] {n : ℕ}
    (p q : Ideal (MvPolynomial (Fin n) k))
    (hp : p.IsPrime) (hq : q.IsPrime) (hpq : p < q) :
    ∀ C : LTSeries
        (Set.Iic (⟨q, hq⟩ : PrimeSpectrum (MvPolynomial (Fin n) k))),
      IsMaximalChainBetween
          (⟨p, hp⟩ : PrimeSpectrum (MvPolynomial (Fin n) k))
          (⟨q, hq⟩ : PrimeSpectrum (MvPolynomial (Fin n) k))
          (le_of_lt hpq) C →
        (C.length : ℕ∞) = q.height - p.height := by
  /-
  Proof roadmap:
  1. Install the Noetherian instance for
     `P := MvPolynomial (Fin n) k`.  Build the field witness for
     `Unit104.IsCohenMacaulayRing k` from
     `Unit104.isCohenMacaulayLocalRing_iff_exists_regularSequence`.  Every
     prime of `k` is `⊥`.  For
     `L := Localization.AtPrime (⊥ : Ideal k)`, use
     `IsLocalization.mk'_surjective` to prove
     `∀ z : L, IsUnit z ∨ z = 0` (a fraction is zero when its numerator is
     zero and otherwise is a unit), then install
     `Field.ofIsUnitOrEqZero`.  The empty list is regular, and its quotient
     has dimension zero by `ringKrullDim_eq_zero_of_field`.  Then apply
     `Unit104.isCohenMacaulayRing_mPolynomial k ... n`.  Pass this to
     `Unit105.isCatenaryRing_of_isCohenMacaulayRing` in
     `Formalization/Books/Algebra/Unit105/CatenaryRings.lean`.
  2. Regard `p` and `q` as points `pS qS : PrimeSpectrum P`.  The hypothesis
     on `C` and
     `Unit105.IsCatenaryRing.maximalChainBetween_length_eq_coheight hcat`
     give

       `(C.length : ℕ∞) =
          Order.coheight (⟨pS, hpq.le⟩ : Set.Iic qS)`.

  3. Prove a small local helper identifying this interval coheight.  Set
     `Rq := Localization.AtPrime q` and
     `pq := p.map (algebraMap P Rq)`.  The prime instance for `pq` is
     `Ideal.isPrime_map_of_isLocalizationAtPrime q hpq.le`.  Apply
     `Unit104.dimension_eq_localization_add_quotient Rq (hCM qS)
       ⟨pq, inferInstance⟩` from `CohenMacaulayRings.lean`.
     Rewrite its three terms as follows:

       * `dim Rq = q.height` by
         `IsLocalization.AtPrime.ringKrullDim_eq_height`;
       * the localization of `Rq` at `pq` is ring-equivalent to
         `Localization.AtPrime p` via
         `IsLocalization.localizationLocalizationAtPrimeIsoLocalization`
         (`Mathlib/RingTheory/Localization/LocalizationLocalization.lean`),
         so its dimension is `p.height`;
       * the spectrum of `Rq ⨸ pq` is order-isomorphic to the interval of
         primes between `pS` and `qS`.  Compose
         `Ideal.primeSpectrumQuotientOrderIsoZeroLocus pq` with
         `IsLocalization.AtPrime.primeSpectrumOrderIso Rq q`; then use
         `ringKrullDim_quotient` and
         `Order.coheight_eq_krullDim_Ici` to identify its dimension with the
         coheight in step 2.

     The resulting equality is
     `q.height = p.height + intervalCoheight`.  Both heights are finite by
     the Noetherian `Ideal.FiniteHeight` instances, so convert the three
     `ℕ∞` values to naturals (or use `ENat.addLECancellable_of_ne_top`) and
     conclude
     `intervalCoheight = q.height - p.height` by truncated-subtraction
     cancellation.
  4. Rewrite the result of step 2 with step 3.  Keep the chain length in
     `ℕ∞`; no `WithBot` coercion is needed in this theorem.

  Catenarity alone only identifies the length with interval coheight; it does
  not turn that coheight into a difference of absolute heights.  The
  Cohen--Macaulay localization equality in step 3 is the required bridge.
  -/
  sorry

/-! ## Finite type domains and local dimensions -/

/-- The dimension of a finite-type domain over a field is the dimension of any
of its localizations at maximal ideals. -/
theorem dimension_spell_it_out
    {k S : Type u} [Field k] [CommRing S] [Algebra k S]
    [Algebra.FiniteType k S] [IsDomain S]
    (m : MaximalSpectrum S) :
    ringKrullDim S = ringKrullDim (Localization.AtPrime m.asIdeal) := by
  /-
  Proof roadmap (follow Stacks 00OO, Lemma 10.114.4, so this proof remains
  independent of the later Noether-normalization chapter):
  1. Choose a presentation with
     `Algebra.FiniteType.iff_quotient_mvPolynomial''`:
     `n : ℕ` and a surjective
     `φ : MvPolynomial (Fin n) k →ₐ[k] S`.  Put `I := RingHom.ker φ`;
     `I.IsPrime` follows from `IsDomain S`.  Form
     `e : (MvPolynomial (Fin n) k ⨸ I) ≃ₐ[k] S` with
     `Ideal.quotientKerAlgEquivOfSurjective` (or `Ideal.kerLiftAlg` plus
     `AlgEquiv.ofBijective`).
  2. Establish a local helper for every `m' : MaximalSpectrum S`.  Let
     `q := m'.asIdeal.comap φ`; it is maximal by
     `Ideal.comap_isMaximal_of_surjective`.  Use `dim_affine_space n` to
     record `q.height = n`.  Transport a height-attaining series below
     `m'.asIdeal` (from `Ideal.exists_ltSeries_length_eq_height` in
     `Mathlib/RingTheory/Ideal/Height.lean`) through the quotient order
     equivalence
     `Ideal.primeSpectrumQuotientOrderIsoZeroLocus I`.  Its image is a
     maximal chain between `I` and `q`; maximality follows because an
     extension would pull back to a longer series below `m'`.
     If `I = q`, use `dim_affine_space n ⟨I, _⟩` to get `I.height = n`
     and compute the quotient height as zero directly.  Otherwise `I < q`,
     and `dimension_height_polynomial_ring I q` computes

       `m'.asIdeal.height = (n : ℕ∞) - I.height`.

     Keep this as a named equality `hheight m'`.
  3. Rewrite the right side of the theorem using
     `IsLocalization.AtPrime.ringKrullDim_eq_height m.asIdeal
       (Localization.AtPrime m.asIdeal)` and `hheight m`.
  4. Rewrite the left side with
     `Formalization.Books.Algebra.Unit60.
       ringKrullDim_eq_iSup_maximal_height` from
     `Formalization/Books/Algebra/Unit60/Dimension.lean`.  Every summand is
     the same finite value by `hheight`; use the supplied `m` as the
     nonempty index witnessing the reverse inequality.  This gives the same
     `(n : ℕ∞) - I.height`, and the desired equality follows.

  When transporting through the presentation, normalize heights only via
  `RingEquiv.height_map`/`RingEquiv.height_comap` and dimensions via
  `ringKrullDim_eq_of_ringEquiv`; unfolding the quotient spectrum creates
  avoidable coercion goals.
  -/
  sorry

/-- At a point of the spectrum of a finite-type algebra over a field, the
topological local dimension is the maximum component dimension through the
point and the minimum dimension of a maximal localization above it. -/
theorem dimension_at_a_point_finite_type_over_field
    {k S : Type u} [Field k] [CommRing S] [Algebra k S]
    [Algebra.FiniteType k S] (p : Ideal S) (hp : p.IsPrime) :
    let x : PrimeSpectrum S := ⟨p, hp⟩
    ∃ d : WithBot ℕ∞,
      krullDimensionAt x = d ∧
        IsGreatest (componentDimensionsAtPoint x) d ∧
          IsLeast (maximalLocalDimensionsAbove x) d := by
  /-
  Proof roadmap (Stacks 00OO, Lemma 10.114.5):
  1. Install once
     `letI : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing k S`
     and
     `letI : IsJacobsonRing S := isJacobsonRing_of_finiteType`.
     Write `X := PrimeSpectrum S` and `x := (⟨p, hp⟩ : X)`.  The set of
     components is finite by
     `TopologicalSpace.NoetherianSpace.finite_irreducibleComponents`
     (`Mathlib/Topology/NoetherianSpace.lean`).  Components of `X` are
     `PrimeSpectrum.zeroLocus q` for `q ∈ minimalPrimes S`, by
     `PrimeSpectrum.zeroLocus_minimalPrimes` in
     `Mathlib/RingTheory/Spectrum/Prime/Topology.lean`.

  2. Prove a reusable component-dimension helper.  If
     `q ∈ minimalPrimes S`, set `A := S ⨸ q`.  Give `A` its finite-type
     `k`-algebra and domain instances.  The quotient-spectrum order
     equivalence `Ideal.primeSpectrumQuotientOrderIsoZeroLocus q`, together
     with `PrimeSpectrum.isClosedEmbedding_comap_of_surjective` and
     `Homeomorph.setCongr`, gives a homeomorphism

       `PrimeSpectrum A ≃ₜ PrimeSpectrum.zeroLocus (q : Set S)`.

     Hence `ringKrullDim A` is the topological dimension of that component,
     using `PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim` and
     `_root_.Topology.IsHomeomorph.topologicalKrullDim_eq`.

     Strengthen this as follows.  If `W : Set X` is open and
     `(W ∩ zeroLocus q).Nonempty`, use
     `nonempty_inter_closedPoints` from
     `Mathlib/Topology/JacobsonSpace.lean` (the intersection is locally
     closed) to choose a closed point `m` in it.  It is a maximal ideal by
     `PrimeSpectrum.isClosed_singleton_iff_isMaximal`.  Apply
     `dimension_spell_it_out` to the maximal ideal of `A` induced by `m`.
     A height-attaining chain in `A` below that maximal ideal lies entirely
     in the pullback of `W`, because `W.isOpen.stableUnderGeneralization`.
     Mapping the chain through the homeomorphism proves

       `topologicalKrullDim (W ∩ zeroLocus q) = ringKrullDim A`.

     The reverse inequality is just `topologicalKrullDim_subspace_le`.
     Keep this helper explicit; it is used both for the greatest and least
     assertions below.

  3. Let `Iₓ` be the finite nonempty subtype of components containing `x`,
     and let `d` be the maximum of their dimensions.  Nonemptiness follows
     from `exists_mem_irreducibleComponents_subset_of_isIrreducible` applied
     to `closure {x}`.  Each component dimension is a finite `WithBot ℕ∞`
     value by step 2 and the finite-type quotient, so take the maximum with
     `Finset.max'` after converting the finite subtype to a finset.  Record
     both an attaining component `Z₀` and the upper bound for every member;
     these are exactly the two fields needed for
     `IsGreatest (componentDimensionsAtPoint x) d`.

  4. Remove all components not containing `x`.  Their union `T` is closed
     because there are finitely many components; put `U := Tᶜ`.  Then `U` is
     open and contains `x`.  For any open neighbourhood `W` of `x`, every
     component through `x` meets `W ∩ U`; step 2 says its intersection still
     has its original dimension.  The lower bound follows by
     `topologicalKrullDim_subspace_le`, and the upper bound follows from the
     private lemma `topologicalKrullDim_le_iSup_componentDimensions` above,
     after showing every component of `W ∩ U` is the preimage of one of the
     original components through `x`.  Use
     `preimage_mem_irreducibleComponents` for the subtype open embedding
     (`Mathlib/Topology/Irreducible.lean`); obtain the converse by closing the
     image and using maximality of an irreducible component.  Thus every open
     neighbourhood has dimension at least `d`, while `U` has dimension `d`.
     Unfold `krullDimensionAt` (or use `krullDimensionAt_isLeast`) to conclude
     `krullDimensionAt x = d`.

  5. Prove a second named helper for a maximal `m : MaximalSpectrum S`:

       `ringKrullDim (Localization.AtPrime m.asIdeal) =
          max { topologicalKrullDim Z |
                Z ∈ irreducibleComponents X,
                MaximalSpectrum.toPrimeSpectrum m ∈ Z }`.

     Minimal primes of the localization are precisely the maps of minimal
     primes `q ≤ m`; use
     `IsLocalization.minimalPrimes_map` from
     `Mathlib/RingTheory/Ideal/MinimalPrime/Localization.lean` (the already
     packaged correspondence
     `Formalization.Books.Algebra.Unit26.
       irreducibleComponents_through_prime_correspond_minimalPrimes_localization`
     in `Formalization/Books/Algebra/Unit26/IrreducibleComponents.lean` is an
     equivalent route).  For each such `q`, `dimension_spell_it_out` applied
     to `S ⨸ q` identifies the quotient component dimension with the
     localized quotient dimension.  Finally use
     `PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim` and the finite
     component maximum; avoid unfolding `ringKrullDim` into arbitrary chains
     more than once.

  6. If `m` lies above `p`, every component through `x` also contains the
     closed point `m`, so steps 3 and 5 give
     `d ≤ ringKrullDim (Localization.AtPrime m.asIdeal)`.  This is the
     lower-bound field of `IsLeast`.

     For attainment, the locally closed set
     `PrimeSpectrum.zeroLocus (p : Set S) ∩ U` is nonempty (it contains `x`).
     Use `nonempty_inter_closedPoints` to choose a closed point `m₀` in it.
     It gives a `MaximalSpectrum S`, contains `p`, and, by the definition of
     `U`, belongs to no component outside `Iₓ`.  Step 5 therefore computes
     its localization dimension as exactly `d`.  This supplies membership of
     `d` in `maximalLocalDimensionsAbove x` and completes `IsLeast`.

  Assemble `⟨d, hlocal, hgreat, hleast⟩`.  Do not try to obtain the least
  value merely by choosing an arbitrary maximal ideal above `p`: it may lie
  on extra, higher-dimensional components; the closed point must be chosen
  in `zeroLocus p ∩ U` as in step 6.
  -/
  sorry

/-- A maximal ideal containing every minimal prime sees the global dimension. -/
theorem ringKrullDim_eq_krullDimensionAt_of_minimalPrimes_le
    {k S : Type u} [Field k] [CommRing S] [Algebra k S]
    [Algebra.FiniteType k S] (m : MaximalSpectrum S)
    (hmin : ∀ p : Ideal S, p ∈ minimalPrimes S → p ≤ m.asIdeal) :
    ringKrullDim S = krullDimensionAt (MaximalSpectrum.toPrimeSpectrum m) := by
  have hpoint :=
    dimension_at_a_point_finite_type_over_field (k := k) (S := S) m.asIdeal m.2.isPrime
  dsimp at hpoint
  obtain ⟨d, hdx, hdcomp, _⟩ := hpoint
  have hcomp : ∀ Z : Set (PrimeSpectrum S),
      Z ∈ irreducibleComponents (PrimeSpectrum S) →
        MaximalSpectrum.toPrimeSpectrum m ∈ Z := by
    intro Z hZ
    rw [← PrimeSpectrum.zeroLocus_minimalPrimes] at hZ
    rcases (Set.mem_image _ _ _).mp hZ with ⟨p, hp, rfl⟩
    exact (PrimeSpectrum.mem_zeroLocus _ _).mpr (hmin p hp)
  have hdim : topologicalKrullDim (PrimeSpectrum S) ≤ d := by
    refine topologicalKrullDim_le_iSup_componentDimensions.trans ?_
    refine iSup_le fun Z => ?_
    exact hdcomp.2 ⟨Z, Z.2, hcomp Z Z.2, rfl⟩
  have hdim_lower : d ≤ ringKrullDim S := by
    rw [← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
    rcases hdcomp.1 with ⟨Z, hZ, _, hZd⟩
    rw [← hZd]
    exact topologicalKrullDim_subspace_le (PrimeSpectrum S) Z
  rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim] at hdim
  have hglobal : ringKrullDim S = d := le_antisymm hdim hdim_lower
  exact hglobal.trans hdx.symm

/-- The local dimension at a closed point of a finite-type affine algebra over
a field is the dimension of the corresponding maximal localization. -/
theorem dimension_closed_point_finite_type_field
    {k S : Type u} [Field k] [CommRing S] [Algebra k S]
    [Algebra.FiniteType k S] (m : MaximalSpectrum S) :
    krullDimensionAt (MaximalSpectrum.toPrimeSpectrum m) =
      ringKrullDim (Localization.AtPrime m.asIdeal) := by
  /-
  Proof roadmap:
  1. Apply `dimension_at_a_point_finite_type_over_field` to `m.asIdeal` and
     `m.isMaximal.isPrime`, then `dsimp` the resulting `let`.  Obtain
     `⟨d, hpoint, _, hleast⟩`.
  2. The target localization dimension belongs to
     `maximalLocalDimensionsAbove (MaximalSpectrum.toPrimeSpectrum m)` with
     witness `m` and `le_rfl`; hence `hleast.2` gives
     `d ≤ ringKrullDim (Localization.AtPrime m.asIdeal)`.
  3. From `hleast.1`, obtain a maximal `m'` above `m` whose localization
     dimension is `d`.  Maximality forces `m.asIdeal = m'.asIdeal` via
     `Ideal.IsMaximal.eq_of_le m.isMaximal m'.isMaximal.ne_top`; use
     `MaximalSpectrum.ext` (or substitute the ideal equality) to rewrite that
     witness equality and obtain the reverse inequality, in fact equality.
  4. Rewrite with `hpoint : krullDimensionAt _ = d` and the equality from
     step 3.
  -/
  sorry

/-! ## Cohen--Macaulay finite-type algebras -/

/- The first form of the final lemma indexes the source's `T₀, ..., T_d`
   by the finite type `Fin (d + 1)`. The empty-spectrum case is included
   separately, matching the source's convention that the empty space has
   dimension `-∞`. -/
def HasDisjointEquidimensionalDecomposition
    (S : Type u) [CommRing S] : Prop :=
  IsEmpty (PrimeSpectrum S) ∨
    (∃ d : ℕ, ringKrullDim S = d ∧
      ∃ T : Fin (d + 1) → Set (PrimeSpectrum S),
        (∀ i, IsClopen (T i) ∧
          ∀ C ∈ irreducibleComponents (T i),
            topologicalKrullDim C = (i.1 : WithBot ℕ∞)) ∧
          (⋃ i, T i) = (Set.univ : Set (PrimeSpectrum S)) ∧
            (∀ i j, i ≠ j → Disjoint (T i) (T j)))

/- The equivalent product form of the source's decomposition.  The explicit
   family of commutative-ring structures keeps the product factors usable as
   ordinary Lean types. -/
def HasDimensionProductDecomposition
    (S : Type u) [CommRing S] : Prop :=
  IsEmpty (PrimeSpectrum S) ∨
    (∃ d : ℕ, ringKrullDim S = d ∧
      ∃ (R : Fin (d + 1) → Type u) (hR : ∀ i, CommRing (R i)),
        letI : ∀ i, CommRing (R i) := hR
        Nonempty (S ≃+* (∀ i, R i)) ∧
          ∀ i : Fin (d + 1),
            ∀ m : MaximalSpectrum (R i),
              m.asIdeal.height = (i.1 : ℕ∞))

/-- A finite-type Cohen--Macaulay algebra over a field decomposes
into open and closed equidimensional pieces, equivalently into ring factors
whose maximal ideals have the corresponding heights. -/
theorem disjoint_decomposition_CM_algebra
    {k S : Type u} [Field k] [CommRing S] [Algebra k S]
    [Algebra.FiniteType k S]
    (hS :
      letI : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing k S
      Formalization.Books.Algebra.Unit104.IsCohenMacaulayRing S) :
    HasDisjointEquidimensionalDecomposition S ∧
      (HasDisjointEquidimensionalDecomposition S ↔
        HasDimensionProductDecomposition S) := by
  /-
  Proof roadmap (Stacks 00OO, Lemma 10.114.7).  Start with

    `letI : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing k S`

  and turn `hS` into a named
  `hCM : Formalization.Books.Algebra.Unit104.IsCohenMacaulayRing S`.

  A. Construct the clopen equidimensional pieces.

  1. Split on `IsEmpty (PrimeSpectrum S)`.  In the empty case both
     decomposition predicates hold by their left disjunct, so the theorem is
     immediate.  In the nonempty case, show that `ringKrullDim S` is a
     natural value.  Choose a finite polynomial presentation with
     `Algebra.FiniteType.iff_quotient_mvPolynomial''`; the surjection and
     `ringKrullDim_le_of_surjective`, followed by
     `MvPolynomial.ringKrullDim_of_isNoetherianRing`, exclude `⊤`.
     `krullDimension_eq_bot_iff` (after
     `PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim`) excludes `⊥`.
     Thus fix

       `d : ℕ` and `hd : ringKrullDim S = ((d : ℕ∞) : WithBot ℕ∞)`.

  2. Prove a named CM component helper.  If `m : MaximalSpectrum S` and
     `Z = PrimeSpectrum.zeroLocus (q : Set S)` is an irreducible component
     through `m`, then

       `topologicalKrullDim Z =
          ringKrullDim (Localization.AtPrime m.asIdeal)`.

     Here `q ∈ minimalPrimes S` comes from
     `PrimeSpectrum.zeroLocus_minimalPrimes`.  In
     `Rm := Localization.AtPrime m.asIdeal`, the mapped ideal `qm` is a
     minimal prime by `IsLocalization.minimalPrimes_map`.  Apply
     `Unit104.dimension_eq_localization_add_quotient Rm (hCM _)` to `qm`.
     Its first summand is zero: rewrite with
     `IsLocalization.AtPrime.ringKrullDim_eq_height` and
     `Ideal.height_eq_zero_iff`.  Therefore
     `ringKrullDim (Rm ⨸ qm) = ringKrullDim Rm`.  Identify `Rm ⨸ qm`
     with the localization of `S ⨸ q` at the maximal ideal induced by
     `m` (construct the equivalence with the quotient/localization universal
     properties).  Now `dimension_spell_it_out (S := S ⨸ q)` identifies
     that local dimension with `ringKrullDim (S ⨸ q)`, while
     `ringKrullDim_quotient`,
     `PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim`, and
     `_root_.Topology.IsHomeomorph.topologicalKrullDim_eq` identify the latter
     with `topologicalKrullDim Z`.

  3. If two irreducible components `Z` and `Z'` meet, their intersection is
     nonempty and closed.  The finite-type Jacobson instance
     `isJacobsonRing_of_finiteType` and `nonempty_inter_closedPoints` from
     `Mathlib/Topology/JacobsonSpace.lean` give a closed point in the
     intersection; convert it to `MaximalSpectrum S` using
     `PrimeSpectrum.isClosed_singleton_iff_isMaximal`.  Apply step 2 to both
     components at this maximal point.  Hence intersecting components have
     equal dimensions.

  4. Components are finite by
     `TopologicalSpace.NoetherianSpace.finite_irreducibleComponents`.  For
     each component `Z`, its nonempty subspace dimension is not `⊥`, and
     `topologicalKrullDim_subspace_le` plus `hd` bounds it by `d`.  Extract
     the unique `i : Fin (d + 1)` satisfying
     `topologicalKrullDim Z = (i.1 : WithBot ℕ∞)`.  Define

       `T i := ⋃₀ {Z | Z ∈ irreducibleComponents (PrimeSpectrum S) ∧
                         topologicalKrullDim Z = (i.1 : WithBot ℕ∞)}`.

     Each `T i` is closed by finiteness.  Step 3 says components assigned
     different indices are disjoint; since all components cover the space,
     the complement of `T i` is the finite union of the other `T j`, hence
     `T i` is open as well.  This also gives pairwise disjointness and
     `(⋃ i, T i) = Set.univ`.

     For the remaining component clause, use the open embedding
     `(T i : Type u) → PrimeSpectrum S`.  Mathlib's
     `preimage_mem_irreducibleComponents` in
     `Mathlib/Topology/Irreducible.lean` sends every ambient component that
     meets `T i` to a component of the subtype; the converse follows by
     closing its image and ambient maximality.  Step 3 ensures that a
     component meeting `T i` was assigned index `i`.  Transport its dimension
     with `_root_.Topology.IsHomeomorph.topologicalKrullDim_eq`.  Package
     `⟨d, hd, T, ...⟩` as `HasDisjointEquidimensionalDecomposition S`.

  B. Convert a clopen partition to a product.

  5. Work from arbitrary data `⟨d, hd, T, hT, hcover, hdisj⟩` in the
     right disjunct of `HasDisjointEquidimensionalDecomposition S`.  For
     `I := Fin (d + 1)`, let `e i : S` be the idempotent corresponding to the
     clopen `T i` under
     `PrimeSpectrum.isIdempotentElemEquivClopens` from
     `Mathlib/RingTheory/Spectrum/Prime/Topology.lean`; thus
     `PrimeSpectrum.basicOpen (e i) = T i`.

     Prove `he : CompleteOrthogonalIdempotents e`.  Pairwise disjointness,
     `PrimeSpectrum.basicOpen_mul`, and
     `PrimeSpectrum.basicOpen_injOn_isIdempotentElem` give
     `e i * e j = 0` for `i ≠ j`.  The cover gives
     `PrimeSpectrum.basicOpen (∑ i, e i) = Set.univ`; the orthogonality
     makes the sum idempotent, so injectivity against the idempotent `1`
     gives `∑ i, e i = 1`; use
     `OrthogonalIdempotents.isIdempotentElem_sum` for the required
     idempotence of the finite sum.  Finish with
     `CompleteOrthogonalIdempotents.iff_ortho_complete` from
     `Mathlib/RingTheory/Idempotents.lean`.

  6. Use the universe-preserving factors

       `R i := S ⨸ Ideal.span ({1 - e i} : Set S) : Type u`.

     Set `hR i := inferInstance : CommRing (R i)`.  The homomorphism
     `RingHom.pi (fun i => Ideal.Quotient.mk (Ideal.span {1 - e i}))`
     is bijective by `he.bijective_pi`; package it as
     `RingEquiv.ofBijective` to obtain `S ≃+* (∀ i, R i)`.

  7. Verify the maximal-height clause factor by factor.  Give `R i` its
     quotient `k`-algebra; it is finite type.  The idempotent localization
     instance `IsLocalization.Away.quotient_of_isIdempotentElem (he.idem i)`
     and `IsLocalization.algEquiv`, together with
     `Unit17.standardOpenSpectrumHomeomorph` from
     `Formalization/Books/Algebra/Unit17/Spectrum.lean`, identify
     `PrimeSpectrum (R i)` with `T i`.  Under this homeomorphism every
     irreducible component has dimension `i` by the input decomposition.
     Apply `dimension_at_a_point_finite_type_over_field` to a maximal point of
     `R i`: its greatest-component clause gives local dimension `i`.
     Then use `dimension_closed_point_finite_type_field` and
     `IsLocalization.AtPrime.ringKrullDim_eq_height` to conclude
     `m.asIdeal.height = (i.1 : ℕ∞)`.  This constructs the right disjunct of
     `HasDimensionProductDecomposition S`.

  C. Convert a product to a clopen partition.

  8. Conversely unpack
     `⟨d, hd, R, hR, ⟨e⟩, hheight⟩`, install `letI : ∀ i, CommRing (R i) := hR`,
     and form the homeomorphism

       `(PrimeSpectrum.sigmaToPiHomeo R).trans
          (PrimeSpectrum.comapEquiv e).symm :
            (Σ i, PrimeSpectrum (R i)) ≃ₜ PrimeSpectrum S`.

     Define `T i` as the image of the `i`th sigma summand.  Since the index is
     finite, each summand is clopen; the homeomorphism makes the `T i`
     clopen, pairwise disjoint, and a cover.

  9. It remains to show the `i`th factor is equidimensional of dimension `i`.
     First give `R i` a finite-type `k`-algebra structure through the
     surjection

       `(Pi.evalRingHom R i).comp e.toRingHom : S →+* R i`.

     Define the `k`-algebra map by composing this homomorphism with
     `algebraMap k S`; then package the displayed homomorphism as a
     `k`-algebra homomorphism and apply `Algebra.FiniteType.of_surjective`.
     Equivalently, compose its `RingHom.FiniteType` proof with
     `RingHom.finiteType_algebraMap`.  This supplies Noetherian and Jacobson
     instances.  For an
     irreducible component `Z` of `PrimeSpectrum (R i)`, remove the finite
     union of all other components.  Irreducibility shows the remaining open
     part of `Z` is nonempty.  Choose a closed point `m` there with
     `nonempty_inter_closedPoints`.  It lies on `Z` and on no other
     component.  By `hheight`,
     `IsLocalization.AtPrime.ringKrullDim_eq_height`, and
     `dimension_closed_point_finite_type_field`, its topological local
     dimension is `i`.  The greatest-component clause of
     `dimension_at_a_point_finite_type_over_field` now has only `Z` available,
     so `topologicalKrullDim Z = (i.1 : WithBot ℕ∞)`.  Transport components
     and dimensions through the homeomorphism from step 8 to obtain the
     required clause for `T i`.

  10. Assemble the reverse right disjunct with the original `d` and `hd`, and
      combine B and C with the common empty-spectrum case to obtain the
      biconditional.  Pair it with the decomposition constructed in A.

  Keep the factors in `Type u` exactly as stated.  Do not replace the finite
  product by iterated binary products: that creates changing index types and
  loses the direct `CompleteOrthogonalIdempotents.bijective_pi` interface.
  -/
  sorry

end

end Formalization.Books.Algebra.Unit114
