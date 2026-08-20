import Formalization.Books.Algebra.Unit99.CriteriaForFlatness
import Formalization.Books.Algebra.Unit102.WhatMakesAComplexExact
import Formalization.Books.Algebra.Unit104.CohenMacaulayRings
import Formalization.Books.Algebra.Unit112.HomomorphismsAndDimension
import Formalization.Books.Algebra.Unit125.DimensionOfFibres
import Formalization.Books.Algebra.Unit128.MoreFlatnessCriteria
import Formalization.Books.Topology.Unit10.KrullDimension
import Mathlib.RingTheory.FinitePresentation
import Mathlib.RingTheory.RingHom.Flat

/-!
# Commutative Algebra, Chapter 129: Openness of the flat locus

This file records the source-facing interfaces for the chapter.  Vanishing
loci, local fibre rings, finite free complexes, and flatness at a prime use the
canonical constructions from earlier chapters.  The small predicates below
only package the source's fibre hypotheses and its localized fibre complex.
-/

namespace Formalization.Books.Algebra.Unit129

open Set
open Formalization.Books.Algebra.Unit99
open Formalization.Books.Algebra.Unit102
open Formalization.Books.Algebra.Unit104
open Formalization.Books.Algebra.Unit112
open Formalization.Books.Topology.Unit10
open scoped TensorProduct

universe u

noncomputable section

/-! ## Fibre hypotheses and local fibre complexes -/

/- The existing Cohen--Macaulay ring predicate carries a Noetherian-ring
  typeclass argument.  This package makes that implicit finiteness part of a
  fibre hypothesis without replacing the canonical predicate itself. -/
def IsCohenMacaulayEquidimensionalOfDimension
    (A : Type u) [CommRing A] (d : ℕ) : Prop :=
  ∃ hA : IsNoetherianRing A,
    letI : IsNoetherianRing A := hA
    Formalization.Books.Algebra.Unit104.IsCohenMacaulayRing A ∧
      Equidimensional (X := PrimeSpectrum A) ∧
        ringKrullDim A = (((d : ℕ∞) : WithBot ℕ∞))

/- The source's assertion that all fibres have a common Cohen--Macaulay,
  equidimensional dimension, with the algebra structure induced by `f`. -/
def AllFibresCohenMacaulayEquidimensional
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (d : ℕ) : Prop :=
  letI : Algebra R S := f.toAlgebra
  ∀ p : PrimeSpectrum R,
    IsCohenMacaulayEquidimensionalOfDimension
      (S ⊗[R] p.asIdeal.ResidueField) d

/- The quotient presentation `S_q / p S_q` is the canonical local-ring model
  for `F_{\bullet,q} ⊗_R κ(p)` used in the source. -/
noncomputable def localFibreRingMap
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (q : PrimeSpectrum S) :
    S →+* localRingOfFibre f (PrimeSpectrum.comap f q) q rfl :=
  (Ideal.Quotient.mk
      (fibreIdealInLocalization f (PrimeSpectrum.comap f q) q)).comp
    (algebraMap S (Localization.AtPrime q.asIdeal))

/- The elements of `S` occurring in a regular-sequence assertion on the local
  fibre. -/
noncomputable def localFibreSequence
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (fs : List S) (q : PrimeSpectrum S) :
    List (localRingOfFibre f (PrimeSpectrum.comap f q) q rfl) :=
  (fs.map (algebraMap S (Localization.AtPrime q.asIdeal))).map
    (Ideal.Quotient.mk
      (fibreIdealInLocalization f (PrimeSpectrum.comap f q) q))

/- A differential of the finite free complex after passing to the local fibre.
  `mapCoordinateLinearMap` is the canonical scalar-extension operation on the
  coordinate matrices. -/
noncomputable def localFibreDifferential
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) {e : ℕ}
    (C : Formalization.Books.Algebra.Unit102.FiniteFreeComplex S e)
    (q : PrimeSpectrum S) (i : ℕ) :
    (Fin (C.termRank (i + 1)) →
        localRingOfFibre f (PrimeSpectrum.comap f q) q rfl) →ₗ[
      localRingOfFibre f (PrimeSpectrum.comap f q) q rfl]
      (Fin (C.termRank i) →
        localRingOfFibre f (PrimeSpectrum.comap f q) q rfl) :=
  Formalization.Books.Algebra.Unit102.mapCoordinateLinearMap
    (localFibreRingMap f q) (C.differential i)

/- The preceding differential with the source reindexed from `i - 1 + 1` to
  `i`, as required by exactness at a positive degree. -/
noncomputable def localFibrePreviousDifferential
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) {e : ℕ}
    (C : Formalization.Books.Algebra.Unit102.FiniteFreeComplex S e)
    (q : PrimeSpectrum S) (i : ℕ) (hi : 0 < i) :
    (Fin (C.termRank i) →
        localRingOfFibre f (PrimeSpectrum.comap f q) q rfl) →ₗ[
      localRingOfFibre f (PrimeSpectrum.comap f q) q rfl]
      (Fin (C.termRank (i - 1)) →
        localRingOfFibre f (PrimeSpectrum.comap f q) q rfl) := by
  have h : i - 1 + 1 = i := Nat.sub_add_cancel hi
  exact h ▸ localFibreDifferential f C q (i - 1)

/- Exactness of the displayed finite complex on the fibre at `q`.  The
  endpoint and interior clauses are the same exactness convention as the
  earlier finite-free-complex interface. -/
def FiniteFreeComplexIsExactOnLocalFibre
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) {e : ℕ}
    (C : Formalization.Books.Algebra.Unit102.FiniteFreeComplex S e)
    (q : PrimeSpectrum S) : Prop :=
  ∀ i : ℕ,
    if hi0 : i = 0 then
      True
    else if _hiL : i = e then
      e ≠ 0 ∧ Function.Injective
        (localFibrePreviousDifferential f C q i (Nat.pos_of_ne_zero hi0))
    else if _hi_lt : i < e then
      Function.Exact (localFibreDifferential f C q i)
        (localFibrePreviousDifferential f C q i (Nat.pos_of_ne_zero hi0))
    else
      True

/- The source's pointwise flatness condition, expressed using Chapter 99's
  canonical localization and restriction-of-scalars construction. -/
noncomputable def flatAtPrimeOverBaseRingHom
    {R S M : Type u} [CommRing R] [CommRing S]
    [AddCommGroup M] [Module S M]
    (f : R →+* S) (q : PrimeSpectrum S) : Prop :=
  letI : Algebra R S := f.toAlgebra
  letI : Module R M := Module.compHom M f
  letI : IsScalarTower R S M := SMul.comp.isScalarTower f
  Formalization.Books.Algebra.Unit99.flatAtPrimeOverBase
    (R := R) (S := S) (M := M) q

/-! ## Dimension and regular sequences -/

/- The first lemma: a dimension bound on a vanishing locus in a finite-type
  Cohen--Macaulay equidimensional algebra is sharp and gives regular
  sequences in all local rings on that locus. -/
theorem cm_dim_finite_type
    {k S : Type u} [Field k] [CommRing S] [Algebra k S]
    [Algebra.FiniteType k S]
    (fs : List S) (d : ℕ)
    (hS :
      letI : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing k S
      Formalization.Books.Algebra.Unit104.IsCohenMacaulayRing S)
    (hequidim : Equidimensional (X := PrimeSpectrum S))
    (hdim : ringKrullDim S = (((d : ℕ∞) : WithBot ℕ∞)))
    -- The source omits nonemptiness, but its equality is false for an empty
    -- vanishing locus; `hlen` records the natural-number encoding of `d - i`.
    (hVnonempty :
      (PrimeSpectrum.zeroLocus (Ideal.ofList fs : Set S)).Nonempty)
    (hlen : fs.length ≤ d)
    (hVdim :
      topologicalKrullDim
          (PrimeSpectrum.zeroLocus (Ideal.ofList fs : Set S)) ≤
        ((((d - fs.length : ℕ) : ℕ∞) : WithBot ℕ∞))) :
    topologicalKrullDim
          (PrimeSpectrum.zeroLocus (Ideal.ofList fs : Set S)) =
        ((((d - fs.length : ℕ) : ℕ∞) : WithBot ℕ∞)) ∧
      ∀ q : PrimeSpectrum S,
        q ∈ PrimeSpectrum.zeroLocus (Ideal.ofList fs : Set S) →
          RingTheory.Sequence.IsRegular
            (Localization.AtPrime q.asIdeal)
            (fs.map (algebraMap S (Localization.AtPrime q.asIdeal))) := by
  /-
  Proof roadmap (Stacks, Lemma 10.129.1 / Tag 00R9).

  Install `Algebra.FiniteType.isNoetherianRing k S` once and put
  `I := Ideal.ofList fs`.  The proof is best split into three small local
  helpers.

  1. Show that every `m : MaximalSpectrum S` has

       `ringKrullDim (Localization.AtPrime m.asIdeal) = d`.

     Apply
     `Formalization.Books.Algebra.Unit114.dimension_closed_point_finite_type_field`
     from `Formalization/Books/Algebra/Unit114/DimensionFiniteTypeAlgebras.lean`.
     In the description of the local dimension supplied by
     `Unit114.dimension_at_a_point_finite_type_over_field`, use
     `irreducibleComponent_mem_irreducibleComponents`,
     `mem_irreducibleComponent`, `hequidim`, and
     `PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim` to identify the
     greatest component dimension with `hdim`.  Keep all dimensions in
     `WithBot ℕ∞` until the final `exact_mod_cast`.

  2. If `m` contains `I`, let `A := Localization.AtPrime m.asIdeal` and
     `xs := fs.map (algebraMap S A)`.  The composite spectrum map from
     `A ⨸ Ideal.ofList xs` into `PrimeSpectrum S` is an order embedding
     with image contained in `zeroLocus I`: use
     `PrimeSpectrum.isClosedEmbedding_comap_of_surjective` for the quotient
     and `IsLocalization.orderEmbedding` for the localization.  Consequently
     `hVdim` bounds the quotient dimension by `d - fs.length`.  The reverse
     inequality is the generalized principal ideal theorem
     `ringKrullDim_le_ringKrullDim_quotient_add_card` from
     `Mathlib/RingTheory/Ideal/KrullsHeightTheorem.lean`, applied to
     `xs.toFinset`; every entry lies in the local maximal ideal because
     `I ≤ m.asIdeal`.  Use `hlen` to cancel the finite coercions and obtain

       `ringKrullDim (A ⨸ Ideal.ofList xs) + fs.length = ringKrullDim A`.

     Now apply `Unit104.regularSequence_iff_expected_quotient_dimension`
     from `Formalization/Books/Algebra/Unit104/CohenMacaulayRings.lean` to
     `hS (MaximalSpectrum.toPrimeSpectrum m)` and conclude that `xs` is
     regular.

  3. For an arbitrary `q ∈ zeroLocus I`, choose a maximal ideal `m ≥ q`
     and use step 2.  Pass from `S_m` to `S_q`: construct the scalar tower
     with `IsLocalization.localizationAlgebraOfSubmonoidLe` and
     `IsLocalization.isLocalization_of_submonoid_le`, apply the weakly
     regular part of the result at `m`, and recover regularity at `q` with
     `RingTheory.Sequence.IsWeaklyRegular.isRegular_of_isLocalization_of_mem`
     from `Mathlib/RingTheory/Regular/Flat.lean`.  The membership premise is
     exactly `q ∈ zeroLocus I`.

  For the dimension equality, `hVdim` is the upper bound.  The nonempty
  hypothesis gives `I ≠ ⊤`; choose a maximal `m ≥ I`.  Step 2 gives a
  quotient of dimension `d - fs.length`, and its spectrum embeds into
  `zeroLocus I`, giving the reverse bound.  Do not try to infer this lower
  bound from `hVdim`: the empty zero locus is precisely the counterexample
  excluded by `hVnonempty`.
  -/
  sorry

/- The second lemma: regularity on the local fibres is an open condition inside
  the vanishing locus. -/
theorem open_regular_sequence
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (hfinite : RingHom.FiniteType f) (d : ℕ)
    (hfibres : AllFibresCohenMacaulayEquidimensional f d)
    (fs : List S) :
    IsOpen
      {q : {q : PrimeSpectrum S //
          q ∈ PrimeSpectrum.zeroLocus (Ideal.ofList fs : Set S)} |
          RingTheory.Sequence.IsRegular
            (localRingOfFibre f (PrimeSpectrum.comap f q.1) q.1 rfl)
            (localFibreSequence f fs q.1)} := by
  /-
  Proof roadmap (Stacks, Lemma 10.129.2 / Tag 00RA).

  Work with `I := Ideal.ofList fs` and the quotient map

    `fbar : R →+* S ⨸ I := (Ideal.Quotient.mk I).comp f`.

  It is finite type by `RingHom.FiniteType.comp` and
  `RingHom.FiniteType.of_surjective`.  The closed embedding
  `PrimeSpectrum.comap (Ideal.Quotient.mk I)` identifies its source with
  `zeroLocus I`; use
  `PrimeSpectrum.isClosedEmbedding_comap_of_surjective` and
  `range_comap_of_surjective`, rather than rewriting the two subtypes by
  definitional equality.

  Fix a point `q` of the stated regular locus, set
  `p := PrimeSpectrum.comap f q.1`, and let
  `qbar := Unit112.tensorFibrePrime f p q.1 rfl`.  Two comparison helpers are
  needed and should be stated with explicit ring equivalences:

  * `Unit112.localRingOfFibre_equiv_tensor_fibre` from
    `Formalization/Books/Algebra/Unit112/HomomorphismsAndDimension.lean`
    transports the hypothesis to regularity of the images of `fs` in the
    localization of `S ⊗[R] p.asIdeal.ResidueField` at `qbar`.
  * Quotient, tensor product, and localization give an equivalence between
    the corresponding local fibre of `fbar` and the quotient of that local
    ring by the mapped sequence.  Under this equivalence the two fibre
    residue fields agree.  Prove the generator formula on `fs` before using
    `LinearEquiv.isRegular_congr'`; a direct `simpa [localFibreSequence]`
    asks Lean to discover a large tensor/localization equivalence and is a
    known dead end.

  Apply
  `Formalization.Books.Algebra.Unit116.dimension_at_a_point_finite_type_field`
  from
  `Formalization/Books/Algebra/Unit116/DimensionFiniteTypeAlgebrasReprise.lean`
  to the original and quotient fibres.  The regular-sequence dimension
  formula
  `ringKrullDim_add_length_eq_ringKrullDim_of_isRegular` cancels the common
  transcendence-degree term and gives

    `relativeDimensionAt fbar _ _ qbarQuot rfl = d - fs.length`.

  Here `fs.length ≤ d` follows by applying the same dimension formula to
  the regular sequence and using the fibre dimension supplied by
  `hfibres p`.

  Invoke `Unit125.relativeDimensionLocus_isOpen_near` from
  `Formalization/Books/Algebra/Unit125/DimensionOfFibres.lean` at the quotient
  point.  Refine its open neighbourhood to a basic open with
  `PrimeSpectrum.isBasis_basic_opens`.  Write that basic open as the spectrum
  of a principal localization using `Unit17.standardOpenSpectrumHomeomorph`.
  For every new base prime, the relative-dimension bound on all points of
  the localized quotient fibre is exactly the topological dimension bound
  required by `cm_dim_finite_type`: use
  `Unit10.krullDimension_eq_iSup_krullDimensionAt` and identify the quotient
  spectrum with the zero locus using the same closed-embedding homeomorphism
  as above.  Destructure `hfibres` at that base prime and install its stored
  `IsNoetherianRing` instance.  Before applying `cm_dim_finite_type`, record
  that the nonempty principal localization of this fibre is still
  Cohen--Macaulay, equidimensional, and of dimension `d`.  For
  Cohen--Macaulayness, compare each local ring with the corresponding local
  ring of the original fibre and use
  `Unit104.isCohenMacaulayLocalRing_localization`; for equidimensionality and
  dimension, use the basic-open homeomorphism and the fact that a nonempty
  open subset of an irreducible component has the same Krull dimension.
  Nonemptiness is supplied by the point under consideration.  The regularity
  conclusion of `cm_dim_finite_type` says the whole chosen relative basic
  open lies in the desired locus.

  Finally transport this neighbourhood through the quotient closed
  embedding and use `IsOpen.isOpenEmbedding_subtypeVal` to conclude openness
  in the subtype `zeroLocus I`.  No flatness hypothesis is needed here; this
  is intentional and matches the source lemma.
  -/
  sorry

/-! ## Exact complexes on fibres -/

/- The third lemma: for a finite free complex over a finite-type flat map with
  Cohen--Macaulay equidimensional fibres, exactness on fibres is open. -/
theorem exact_on_fibres_open
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (hfinite : RingHom.FiniteType f)
    (hflat : RingHom.Flat f) [IsNoetherianRing R] (d : ℕ)
    (hfibres : AllFibresCohenMacaulayEquidimensional f d)
    {e : ℕ}
    (C : Formalization.Books.Algebra.Unit102.FiniteFreeComplex S e) :
    IsOpen
      {q : PrimeSpectrum S |
        FiniteFreeComplexIsExactOnLocalFibre f C q} := by
  /-
  Proof roadmap (Stacks, Lemma 10.129.3 / Tag 00RB).

  Use `isOpen_iff_forall_mem_open`.  Fix `q` where the local fibre complex is
  exact and put `p := PrimeSpectrum.comap f q`.  Install the algebra
  structure from `f`; `hfinite` and `[IsNoetherianRing R]` give
  `[IsNoetherianRing S]` via `Algebra.FiniteType.isNoetherianRing R S`.

  1. First spread exactness of the underlying complex.  Define a small local
     helper which maps `C` coefficientwise along a ring homomorphism using
     `Unit102.mapCoordinateLinearMap`; prove its `differential_comp` field by
     applying the homomorphism to `C.differential_comp`.  For the local map
     `Localization.localRingHom p.asIdeal q.asIdeal f _`, package the mapped
     coordinate modules as a `Unit99.FiniteFlatModuleComplex`: finiteness is
     finite freeness, and flatness over `R_p` follows from `hflat` and
     localization/base change.  Compare quotienting its terms by the maximal
     ideal of `R_p` with `localFibreRing f p q rfl`; prove the comparison on
     coordinate vectors and differentials.  Then
     `Unit99.complex_exact_mod` from
     `Formalization/Books/Algebra/Unit99/CriteriaForFlatness.lean` lifts the
     assumed fibre exactness to exactness over `S_q`.

     The finitely many homology modules of the coordinate complex are finite
     because `S` is Noetherian.  Clear denominators in generators of those
     modules to obtain `a ∉ q.asIdeal` such that the complex over
     `Localization.Away a` is exact.  This finite-denominator argument is the
     needed bridge from local exactness to a basic open; it is not provided by
     `FiniteFreeComplex` itself.

  2. Over `S_a`, set

       `r_i := Unit102.alternatingRank C i`,
       `I_i := Unit102.rankIdeal (C.previousDifferential i hi)`

     for `1 ≤ i ≤ e`.  Apply `Unit102.proposition_what_exact` from
     `Formalization/Books/Algebra/Unit102/WhatMakesAComplexExact.lean` at all
     prime localizations of `S_a`.  This gives the fixed rank formula and
     makes every larger minor vanish.  Establish coefficientwise helper
     lemmas saying that exterior powers, `rank`, and `rankIdeal` commute with
     the localization and with `localFibreRingMap`; these are required before
     applying the proposition on a fibre.  In particular, do not use the
     global `rankIdeal` before step 1: its rank can drop after localization.

  3. At the original `q`, the fibre version of
     `Unit102.proposition_what_exact` says, for each `i`, either the localized
     `I_i` is the unit ideal or it contains a regular sequence of length `i`.
     In the first case shrink to the basic open on which `I_i` is the unit
     ideal.  In the second case clear denominators to choose a list
     `xs_i : List S` of length `i`, with every entry in `I_i`, whose image is
     regular at `q`.  Apply `open_regular_sequence f hfinite d hfibres xs_i`.
     On the complement of `V(xs_i)`, membership `xs_i ⊆ I_i` makes `I_i`
     the unit ideal; on its relative open part inside `V(xs_i)`, it supplies
     the required regular sequence.  Thus the union of these two opens is a
     neighbourhood on which the `i`th Buchsbaum--Eisenbud ideal condition
     holds.

  Intersect the finitely many neighbourhoods from step 3 with `D(a)`.  At
  every point in the intersection, the rank condition from step 2 and the
  ideal conditions imply fibre exactness by the reverse implication of
  `Unit102.proposition_what_exact`.  Unfold
  `FiniteFreeComplexIsExactOnLocalFibre` only in the final comparison with
  the mapped helper complex; proof irrelevance handles the positive-index
  witnesses in `localFibrePreviousDifferential`.
  -/
  sorry

/-! ## Openness of the flat locus -/

/- The final theorem: finite presentation of both the algebra and the module
  makes the locus where the localized module is flat over the base open. -/
theorem openness_flatness
    {R S M : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (hfinitePresentation : RingHom.FinitePresentation f)
    [AddCommGroup M] [Module S M] [Module.FinitePresentation S M] :
    IsOpen
      {q : PrimeSpectrum S |
        flatAtPrimeOverBaseRingHom (R := R) (S := S) (M := M) f q} := by
  /-
  Proof roadmap (Stacks, Theorem 10.129.4 / Tag 00RC; interface audit:
  `exact_on_fibres_open` has precisely the hypotheses needed after the
  polynomial and Noetherian reductions, so no theorem signature is to be
  weakened or augmented).

  Use `isOpen_iff_forall_mem_open` and fix `q` in the flat locus, with
  `p := PrimeSpectrum.comap f q`.  The proof has four reductions.

  1. Choose a finite polynomial presentation of `f` from
     `Algebra.FinitePresentation.iff_quotient_mvPolynomial'` in
     `Mathlib/RingTheory/FinitePresentation.lean`:

       `P := MvPolynomial (Fin n) R`, `g : P →+* S`, `g` surjective,
       `g.comp MvPolynomial.C = f`, and `(RingHom.ker g).FG`.

     Restrict `M` along `g`.  The quotient `S` is finitely presented as a
     `P`-module by `Module.finitePresentation_of_surjective`, and then
     `Module.FinitePresentation.trans` from
     `Mathlib/Algebra/Module/FinitePresentation.lean` shows that `M` is
     finitely presented over `P`.  The closed embedding
     `PrimeSpectrum.comap g` identifies `PrimeSpectrum S` with
     `zeroLocus (RingHom.ker g)`.  It is therefore enough to construct an
     ambient open flat neighbourhood for this `P`-module at `comap g q`.

  2. Descend the polynomial situation to a Noetherian stage.  Start with a
     finite coordinate presentation from
     `Module.FinitePresentation.exists_fin' P M`.  Its matrix contains only
     finitely many polynomials and hence finitely many coefficients of `R`.
     Form the directed system of finitely generated `ℤ`-subalgebras `R_i`
     containing those coefficients, put
     `P_i := MvPolynomial (Fin n) R_i`, and let `M_i` be the cokernel of the
     descended coordinate matrix.  Package this system using
     `Unit127.DirectedRingMapColimit` and
     `Unit127.DirectedModuleColimitPresentation`; the verification follows
     the construction underlying `Unit127.limitModuleFinitePresentation` in
     `Formalization/Books/Algebra/Unit127/ColimitsAndFinitePresentation.lean`,
     but the explicit choice `P_i = MvPolynomial (Fin n) R_i` is essential
     because it retains flatness and the known polynomial fibres.

     Localize source and target stages at the inverse images of `p` and
     `comap g q`, and base-change the module stages.  The localized transition
     maps are `Localization.localRingHom`s and hence local; package this
     explicitly as `Unit128.HasLocalTransitionMaps`.  Now apply
     `Unit128.colimit_eventually_flat` from
     `Formalization/Books/Algebra/Unit128/MoreFlatnessCriteria.lean` to the
     given flat localized module.  It produces a stage at which the localized
     descended module is flat.  The unlocalized source stage is finite type
     over `ℤ` and hence Noetherian, and its target is the polynomial algebra
     `P_i`.

     Interface trap to avoid: an arbitrary witness returned by
     `Unit127.limitModuleEssentiallyFinitePresentation` does not expose
     `HasLocalTransitionMaps`; `DirectedRingMapColimit.stagesAreLocal` only
     concerns the vertical stage maps.  Use the explicit coefficient system
     above, whose localized arrows are `localRingHom`s, instead of trying to
     infer the missing field from `localStages`.  Likewise, an arbitrary
     witness of `limitModuleFinitePresentation` need not retain polynomial
     target stages, so it cannot directly supply the `hflat` and `hfibres`
     arguments of `exact_on_fibres_open`.

  3. Prove the Noetherian polynomial case.  Write the target as
     `P₀ := MvPolynomial (Fin n) R₀`.  Its map from `R₀` is finite type
     and flat.  For every `p₀ : PrimeSpectrum R₀`, use
     `MvPolynomial.algebraTensorAlgEquiv` to identify its fibre with
     `MvPolynomial (Fin n) p₀.asIdeal.ResidueField`.  Supply
     `AllFibresCohenMacaulayEquidimensional _ n` using
     `Unit104.isCohenMacaulayRing_mPolynomial`,
     `Unit114.finite_gl_dim_polynomial_ring`, the domain instance for a
     polynomial ring over a field, and
     `irreducibleComponents_eq_singleton`; transport the three properties
     across the displayed ring equivalence explicitly.

     Obtain a finite-free resolution with
     `Unit71.exists_finite_free_resolution` from
     `Formalization/Books/Algebra/Unit71/ExtGroups.lean`.  At the chosen point,
     propagate flatness through its first `n` short exact sequences with
     `Formalization.Books.Algebra.Unit39.flat_short_exact`.  The fibre has
     global dimension `n` by `Unit114.finite_gl_dim_polynomial_ring`, so the
     `n`th fibre syzygy is projective; over its local ring it is finite free.
     Apply `Unit99.free_fibre_flat_free` to lift this to freeness of the
     localized syzygy, and spread that freeness to a principal neighbourhood
     with `Module.FinitePresentation.exists_free_localizedModule_powers` from
     `Mathlib/RingTheory/Localization/Free.lean`.

     Choose finite bases for the resolution terms and this terminal syzygy
     and coordinateize the truncated resolution as a
     `Unit102.FiniteFreeComplex P₀ n`.  Record small comparison lemmas between
     its coordinate maps, the original resolution, and their local fibres.
     Apply `exact_on_fibres_open` and refine its open neighbourhood to a basic
     open.  On that localization all fibres of the truncated complex are
     exact.  Applying `Unit99.complex_exact_mod` at each prime gives flatness
     of its cokernel; assemble these local conclusions with
     `Unit39.flat_iff_localized_over_primes`.  The cokernel comparison from the
     resolution identifies it with the localized descended module.

  4. Pull this basic open forward through the directed system.  Flatness is
     preserved by base change (`Module.Flat.baseChange`/the tensor-product
     criterion in `Formalization/Books/Algebra/Unit39/FlatModules.lean`), and
     the stage/module isomorphisms in
     `DirectedModuleFinitePresentationApproximation` identify the resulting
     localization with the original `M`.  Thus obtain `a ∉ q.asIdeal` with
     `M_a` flat over `R`.  Every prime in `PrimeSpectrum.basicOpen a` is then
     in the required locus by localization of a flat module.  Intersect this
     ambient basic open with the closed image from step 1 and transport it
     back along `PrimeSpectrum.comap g` to finish the pointwise openness
     argument.

  Keep the rings in `Type u` throughout the approximation and resolution
  constructions (`ModuleCat.{u}` and `CommRingCat.of`); otherwise the
  `DirectedRingMapColimit` stage objects acquire incompatible universes.
  -/
  sorry

end

end Formalization.Books.Algebra.Unit129
