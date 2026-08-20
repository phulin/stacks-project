import Formalization.Books.Algebra.Unit112.HomomorphismsAndDimension
import Formalization.Books.Algebra.Unit113.DimensionFormula
import Formalization.Books.Algebra.Unit114.DimensionFiniteTypeAlgebras
import Formalization.Books.Algebra.Unit115.NoetherNormalization
import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.SetTheory.Cardinal.ENat

/-!
# Commutative Algebra, Chapter 116: Dimension of finite type algebras over fields, reprise

The source's Krull dimensions use Mathlib's `ringKrullDim`, local dimensions
of spectra use the topological `krullDimensionAt`, and transcendence degrees
use the cardinal-valued `Algebra.trdeg`.  The tensor-product fibre in the
last statement uses the canonical `Unit112.tensorLocalRingOfFibre` interface.
-/

namespace Formalization.Books.Algebra.Unit116

universe u v

noncomputable section

open Set
open scoped TensorProduct
open Formalization.Books.Topology.Unit10

/-! ## Dimension and transcendence degree -/

/- The field of fractions is supplied as a field carrying the canonical
   algebra and scalar-tower structures over the finite-type domain. -/
theorem dimension_prime_polynomial_ring
    {k S : Type u} {K : Type v}
    [Field k] [CommRing S] [Algebra k S]
    [Algebra.FiniteType k S] [IsDomain S]
    [Field K] [Algebra S K] [IsFractionRing S K]
    [Algebra k K] [IsScalarTower k S K] :
    ∃ r : ℕ, Algebra.trdeg k K = r ∧
      ringKrullDim S = r ∧
        ∀ m : MaximalSpectrum S,
          ringKrullDim (Localization.AtPrime m.asIdeal) = r := by
  classical
  obtain ⟨n, φ, hφ⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp
    (inferInstance : Algebra.FiniteType k S)
  have hI : RingHom.ker φ ≠ ⊤ := by
    intro hI
    have hzero : φ (1 : MvPolynomial (Fin n) k) = 0 := by
      have hmem : (1 : MvPolynomial (Fin n) k) ∈ RingHom.ker φ := by
        rw [hI]
        trivial
      exact hmem
    simp at hzero
  obtain ⟨r, _, g, hg, hgf, hdim, _⟩ :=
    Formalization.Books.Algebra.Unit115.noether_normalization
      (RingHom.ker φ) hI
  let e : (MvPolynomial (Fin n) k ⧸ RingHom.ker φ) ≃ₐ[k] S :=
    AlgEquiv.ofBijective (Ideal.kerLiftAlg φ) ⟨
      Ideal.kerLiftAlg_injective φ, by
        intro s
        obtain ⟨p, hp⟩ := hφ s
        refine ⟨Ideal.Quotient.mk (RingHom.ker φ) p, ?_⟩
        exact (Ideal.kerLiftAlg_mk φ p).trans hp
        ⟩
  have hdimS : ringKrullDim S = r := by
    calc
      ringKrullDim S = ringKrullDim
        (MvPolynomial (Fin n) k ⧸ RingHom.ker φ) :=
        (ringKrullDim_eq_of_ringEquiv e.toRingEquiv).symm
      _ = r := hdim
  have htrdegS : Algebra.trdeg k S = r := by
    have htrdegQ : Algebra.trdeg k
        (MvPolynomial (Fin n) k ⧸ RingHom.ker φ) = r := by
      let : IsDomain (MvPolynomial (Fin n) k ⧸ RingHom.ker φ) :=
        e.toRingEquiv.isDomain_iff.mpr inferInstance
      let : Algebra (MvPolynomial (Fin r) k)
          (MvPolynomial (Fin n) k ⧸ RingHom.ker φ) := g.toAlgebra
      let : IsScalarTower k (MvPolynomial (Fin r) k)
          (MvPolynomial (Fin n) k ⧸ RingHom.ker φ) :=
        IsScalarTower.of_algebraMap_eq fun x => (g.commutes x).symm
      have hfaith : FaithfulSMul (MvPolynomial (Fin r) k)
          (MvPolynomial (Fin n) k ⧸ RingHom.ker φ) :=
        (faithfulSMul_iff_algebraMap_injective _ _).mpr hg
      let : FaithfulSMul (MvPolynomial (Fin r) k)
          (MvPolynomial (Fin n) k ⧸ RingHom.ker φ) := hfaith
      let : Module.Finite (MvPolynomial (Fin r) k)
          (MvPolynomial (Fin n) k ⧸ RingHom.ker φ) := hgf
      let : Algebra.IsAlgebraic (MvPolynomial (Fin r) k)
          (MvPolynomial (Fin n) k ⧸ RingHom.ker φ) :=
        Algebra.IsAlgebraic.of_finite _ _
      rw [← trdeg_add_eq k (MvPolynomial (Fin r) k)]
      have hz : Algebra.trdeg (MvPolynomial (Fin r) k)
          (MvPolynomial (Fin n) k ⧸ RingHom.ker φ) = 0 := trdeg_eq_zero
      rw [hz, add_zero]
      simp [MvPolynomial.trdeg_of_isDomain]
    simpa using e.trdeg_eq.symm.trans htrdegQ
  have htrdegK : Algebra.trdeg k K = r := by
    let : Algebra.IsAlgebraic S K := IsLocalization.isAlgebraic K (nonZeroDivisors S)
    have hfaith : FaithfulSMul S K :=
      (faithfulSMul_iff_algebraMap_injective _ _).mpr (IsFractionRing.injective S K)
    let : FaithfulSMul S K := hfaith
    have h := lift_trdeg_add_eq k S K
    rw [htrdegS, trdeg_eq_zero] at h
    simpa using h.symm
  refine ⟨r, htrdegK, hdimS, ?_⟩
  intro m
  exact (Formalization.Books.Algebra.Unit114.dimension_spell_it_out
    (k := k) (S := S) m).symm.trans hdimS

/- The residue-field transcendence degree strictly decreases along a proper
   specialization. -/
theorem tr_deg_specialization
    {k S : Type u} [Field k] [CommRing S] [Algebra k S]
    [Algebra.FiniteType k S]
    (q q' : PrimeSpectrum S) (hqq' : q < q') :
    Algebra.trdeg k q'.asIdeal.ResidueField <
      Algebra.trdeg k q.asIdeal.ResidueField := by
  let A := S ⧸ q.asIdeal
  let A' := S ⧸ q'.asIdeal
  have hqdim := dimension_prime_polynomial_ring
    (k := k) (S := A) (K := q.asIdeal.ResidueField)
  have hq'dim := dimension_prime_polynomial_ring
    (k := k) (S := A') (K := q'.asIdeal.ResidueField)
  obtain ⟨r, htr, hdim, _⟩ := hqdim
  obtain ⟨r', htr', hdim', _⟩ := hq'dim
  have hqq'ideal : q.asIdeal ≤ q'.asIdeal :=
    (PrimeSpectrum.asIdeal_le_asIdeal q q').mpr hqq'.le
  obtain ⟨x, hxq', hxq⟩ := SetLike.exists_of_lt
    ((PrimeSpectrum.asIdeal_lt_asIdeal q q').mpr hqq')
  have hxne : Ideal.Quotient.mk q.asIdeal x ≠ 0 := by
    simpa [Ideal.Quotient.eq_zero_iff_mem] using hxq
  have hxreg : Ideal.Quotient.mk q.asIdeal x ∈ nonZeroDivisors A := by
    rw [mem_nonZeroDivisors_iff_ne_zero]
    exact hxne
  have hdimlt : ringKrullDim A' + 1 ≤ ringKrullDim A := by
    apply ringKrullDim_succ_le_of_surjective
      (Ideal.Quotient.factor hqq'ideal)
      (Ideal.Quotient.factor_surjective hqq'ideal)
      hxreg
    exact Ideal.Quotient.factor_mk hqq'ideal x ▸
      (Ideal.Quotient.eq_zero_iff_mem.mpr hxq')
  have hnat : r' + 1 ≤ r := by
    rw [hdim', hdim] at hdimlt
    exact_mod_cast hdimlt
  rw [htr', htr]
  exact_mod_cast (show r' < r by omega)

/- The local dimension formula at an arbitrary point of a finite-type affine
   algebra over a field. -/
theorem dimension_at_a_point_finite_type_field
    {k S : Type u} [Field k] [CommRing S] [Algebra k S]
    [Algebra.FiniteType k S] (p : PrimeSpectrum S) :
    krullDimensionAt p =
      ringKrullDim (Localization.AtPrime p.asIdeal) +
        ((Cardinal.toENat (Algebra.trdeg k p.asIdeal.ResidueField) : ℕ∞) :
          WithBot ℕ∞) := by
  /-
  Proof roadmap (the statement has the required finiteness hypothesis).
  Write

    `t := Cardinal.toENat (Algebra.trdeg k p.asIdeal.ResidueField) : ℕ∞`.

  Install `Algebra.FiniteType.isNoetherianRing k S` once; this supplies the
  `Ideal.FiniteHeight` instances used below.  The proof has three local
  helpers and a final greatest-element argument.

  1. Apply
     `Formalization.Books.Algebra.Unit114.dimension_at_a_point_finite_type_over_field`
     (in `Formalization/Books/Algebra/Unit114/DimensionFiniteTypeAlgebras.lean`)
     to `p.asIdeal`.  After `dsimp`, retain

       `hd : krullDimensionAt p = d` and
       `hgreat : IsGreatest (componentDimensionsAtPoint p) d`.

     The `IsLeast maximalLocalDimensionsAbove` part is not needed for this
     component proof.  At the end, `hgreat.1` supplies a component attaining
     `d`, while `hgreat.2` compares every other component with `d`.

  2. Prove a helper for a minimal prime `q` with `q ≤ p.asIdeal`.  Set

       `A := S ⧸ q`,
       `pbar := p.asIdeal.map (Ideal.Quotient.mk q) : Ideal A`.

     Give `q` its prime instance from `q ∈ minimalPrimes S`, and give `pbar`
     its prime instance with
     `Ideal.isPrime_map_quotientMk_of_isPrime`.  The desired helper is

       `topologicalKrullDim (PrimeSpectrum.zeroLocus (q : Set S)) =
          ((pbar.height + t : ℕ∞) : WithBot ℕ∞)`.

     First identify the left side with `ringKrullDim A`.  Use
     `PrimeSpectrum.isClosedEmbedding_comap_of_surjective`
     for `Ideal.Quotient.mk q`, its embedding homeomorphism onto the range,
     `range_comap_of_surjective`, and `Homeomorph.setCongr` to obtain

       `PrimeSpectrum A ≃ₜ PrimeSpectrum.zeroLocus (q : Set S)`.

     Then use `IsHomeomorph.topologicalKrullDim_eq` from
     `Mathlib/Topology/KrullDimension.lean` and
     `PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim` from
     `Mathlib/RingTheory/Spectrum/Prime/Topology.lean`.

     Compute this dimension as follows.  Apply the already proved
     `dimension_prime_polynomial_ring` twice: to the finite-type domain `A`
     with fraction field `q.ResidueField`, obtaining a natural `r`, and to
     `A ⨸ pbar` with fraction field `pbar.ResidueField`, obtaining a natural
     `s`.  The canonical quotient residue-field map

       `Ideal.ResidueField.mapₐ p.asIdeal pbar (Ideal.Quotient.mkₐ k q) ...`

     is bijective by
     `RingHom.SurjectiveOnStalks.residueFieldMap_bijective` applied to
     `RingHom.surjectiveOnStalks_of_surjective Ideal.Quotient.mk_surjective`.
     Package it with `AlgEquiv.ofBijective`; `AlgEquiv.trdeg_eq` then rewrites
     `s` to `Algebra.trdeg k p.asIdeal.ResidueField`, hence `t = s` after
     `Cardinal.toENat`.

     It remains to show `pbar.height + s = r`.  Apply
     `Formalization.Books.Algebra.Unit113.dimension_formula` (in
     `Formalization/Books/Algebra/Unit113/DimensionFormula.lean`) to
     `algebraMap k A`, the unique prime `(⊥ : Ideal k)`, and `pbar`.
     The injectivity is `FaithfulSMul.algebraMap_injective k A`; pass the
     finite-type hypothesis as
     `RingHom.finiteType_algebraMap.mpr (inferInstance :
       Algebra.FiniteType k A)`.  Supply the equality branch with
     `Formalization.Books.Algebra.Unit105.isUniversallyCatenary_of_isCohenMacaulayRing k`;
     the small field Cohen--Macaulay witness uses
     `Formalization.Books.Algebra.Unit104.isCohenMacaulayLocalRing_iff_exists_regularSequence`,
     the empty regular sequence, and `ringKrullDim_eq_zero_of_field` (the same
     construction appears in `Books/Exercises/Unit18/Statements.lean`, but do
     not import that later exercise file).

     Two scalar-tower rewrites are important here.  Use
     `lift_trdeg_add_eq k A q.ResidueField`,
     `IsLocalization.isAlgebraic`, and `trdeg_eq_zero` to replace
     `Algebra.trdeg k A` by `r`.  Use
     `Ideal.algEquivResidueFieldOfField (⊥ : Ideal k)`,
     `Ideal.ResidueField.map_algebraMap`, and an explicit
     `IsScalarTower.of_algebraMap_eq` to replace the residue-field degree in
     `Unit113.dimension_formula` by `s`.  Thus its equality reads
     `pbar.height = r - s`.  Obtain `s ≤ r` independently from
     `trdeg_le_of_surjective` for `A → A ⨸ pbar` followed by the two
     fraction-field transcendence equalities; then finish with
     `tsub_add_cancel_of_le`.  Keeping `r` and `s` as naturals avoids any
     non-injectivity issue for `Cardinal.toENat` on infinite cardinals.

  3. Prove that the relative heights in step 2 have greatest element
     `p.asIdeal.height`:

       `IsGreatest {h : ℕ∞ | ∃ q ∈ minimalPrimes S,
          q ≤ p.asIdeal ∧
          (p.asIdeal.map (Ideal.Quotient.mk q)).height = h}
          p.asIdeal.height`.

     For the upper bound, take the height-attaining series for the image
     prime from `Ideal.exists_ltSeries_length_eq_height`, and map it through
     `PrimeSpectrum.comap (Ideal.Quotient.mk q)`.  Strictness is
     `RingHom.strictMono_comap_of_surjective Ideal.Quotient.mk_surjective`;
     `Ideal.comap_map_quotientMk` identifies its last point with `p`.  Bound
     its unchanged length by `Order.length_le_height_last`, then rewrite with
     `PrimeSpectrum.height_eq_orderHeight`.

     For attainment, take the series ending at `p.asIdeal` from
     `Ideal.exists_ltSeries_length_eq_height` in
     `Mathlib/RingTheory/Ideal/Height.lean`.  Choose a minimal prime below its
     head with `Ideal.exists_minimalPrimes_le`.  If that inclusion were
     strict, prepend it with `RelSeries.cons`; `RelSeries.cons_length` and
     `Order.length_le_height` contradict the defining height bound, so the
     head itself is a minimal prime `q`.  Transport the series to
     `A = S ⨸ q` with the quotient spectrum order equivalence
     `Ideal.primeSpectrumQuotientOrderIsoZeroLocus` from
     `Mathlib/RingTheory/Spectrum/Prime/RingHom.lean`.  This gives the reverse
     inequality for `pbar.height`, hence equality.

  4. Rewrite components with `PrimeSpectrum.zeroLocus_minimalPrimes`:
     a component through `p` is exactly `zeroLocus q` for a minimal `q` with
     `q ≤ p.asIdeal`.  Step 2 expresses its dimension as `h + t`; step 3
     says every such `h` is at most `p.asIdeal.height` and one equals it.
     Therefore `hgreat` gives

       `d = ((p.asIdeal.height + t : ℕ∞) : WithBot ℕ∞)`.

     Finally rewrite `p.asIdeal.height` as the localization dimension with
     `IsLocalization.AtPrime.ringKrullDim_eq_height` from
     `Mathlib/RingTheory/Ideal/Height.lean`, use `hd`, and normalize the two
     coercions and `WithBot.coe_add`.

  Do not try to obtain the equality by iterating `tr_deg_specialization`:
  that theorem supplies strict decrease along a chain, but not the exact
  chain length, so it cannot identify the localization-height summand.
  -/
  sorry

/- The codimension formula for a surjective finite-type map is written using
   the canonical comap point and the corresponding prime heights. -/
theorem codimension
    {k S' S : Type u} [Field k]
    [CommRing S'] [CommRing S] [Algebra k S'] [Algebra k S]
    [Algebra.FiniteType k S'] [Algebra.FiniteType k S]
    (f : S' →ₐ[k] S) (hf : Function.Surjective f)
    (p : PrimeSpectrum S) :
    WithBot.unbotD 0 (krullDimensionAt (PrimeSpectrum.comap f.toRingHom p)) -
        WithBot.unbotD 0 (krullDimensionAt p) =
      (PrimeSpectrum.comap f.toRingHom p).asIdeal.height - p.asIdeal.height := by
  /-
  Proof roadmap (both rings already carry the finite-type hypotheses needed
  by `dimension_at_a_point_finite_type_field`).

  1. Put `p' := PrimeSpectrum.comap f.toRingHom p`.  Apply
     `dimension_at_a_point_finite_type_field` to `(S := S') p'` and to
     `(S := S) p`.  In both equalities rewrite the localization term with the
     fully instantiated lemma

       `IsLocalization.AtPrime.ringKrullDim_eq_height
          p.asIdeal (Localization.AtPrime p.asIdeal)`

     (and similarly for `p'`).  Rewrite the sum as a single coercion with
     `← WithBot.coe_add`; then `WithBot.unbotD_coe` turns the two local
     dimensions into sums in `ℕ∞`.

  2. Prove that the two transcendence summands agree.  The defining ideal
     equality is

       `p'.asIdeal = p.asIdeal.comap f.toRingHom`.

     Form the canonical `k`-algebra map

       `κf := Ideal.ResidueField.mapₐ p'.asIdeal p.asIdeal f ...`.

     From `hf`, obtain
     `RingHom.surjectiveOnStalks_of_surjective hf`; then
     `RingHom.SurjectiveOnStalks.residueFieldMap_bijective` (both in
     `Mathlib/RingTheory/SurjectiveOnStalks.lean` and
     `Mathlib/RingTheory/LocalRing/ResidueField/Ideal.lean`) proves `κf`
     bijective.  Define

       `eκ : p'.asIdeal.ResidueField ≃ₐ[k] p.asIdeal.ResidueField :=
          AlgEquiv.ofBijective κf hκf`.

     Now `eκ.trdeg_eq` gives equality of the cardinal-valued degrees, and
     applying `Cardinal.toENat` gives a common `t : ℕ∞`.

  3. The common transcendence term must be shown finite before cancelling
     it.  Put

       `t := Cardinal.toENat (Algebra.trdeg k p.asIdeal.ResidueField)`.

     Apply `dimension_prime_polynomial_ring` to the domain
     `S ⧸ p.asIdeal`, with fraction field `p.asIdeal.ResidueField`; its
     natural witness and `Cardinal.toENat_ne_top` prove `t ≠ ⊤`.  Install
     `Algebra.FiniteType.isNoetherianRing k S` and its `S'` analogue, and use
     `Ideal.height_ne_top_of_isPrime` to prove both heights are also not top.

     After the rewrites from steps 1 and 2, the left side is

       `(p'.asIdeal.height + t) - (p.asIdeal.height + t)`.

     Do not apply `add_tsub_add_eq_tsub_right` directly to `ℕ∞`: it asks for
     the unavailable global `AddLeftReflectLE ℕ∞` instance.  Instead use
     `ENat.ne_top_iff_exists` on the two heights and `t`, rewrite all three as
     natural casts, run `norm_cast`, and close the natural-number identity
     with `Nat.add_sub_add_right`.  No comparison of the two heights is
     required.

  The residue fields should be compared through `Ideal.ResidueField.mapₐ`,
  not by unfolding `Ideal.ResidueField` or the two localizations; unfolding
  loses the canonical `k`-algebra compatibility needed by `AlgEquiv.trdeg_eq`.
  -/
  sorry

/-! ## Base change by a field extension -/

private structure TensorDimensionWitness
    {k S K : Type u} [Field k] [CommRing S] [Algebra k S]
    [Algebra.FiniteType k S] [Field K] [Algebra k K] (r : ℕ) where
  dimension : ringKrullDim (K ⊗[k] S) = r

/- The global Krull dimension is unchanged by extension of the ground field. -/
theorem dimension_preserved_field_extension
    {k S K : Type u} [Field k] [CommRing S] [Algebra k S]
    [Algebra.FiniteType k S] [Field K] [Algebra k K] :
    ringKrullDim S = ringKrullDim (K ⊗[k] S) := by
  classical
  by_cases hS : Nontrivial S
  · let _ : Nontrivial S := hS
    obtain ⟨n, φ, hφ⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp
      (inferInstance : Algebra.FiniteType k S)
    have hI : RingHom.ker φ ≠ ⊤ := by
      intro hI
      have hzero : φ (1 : MvPolynomial (Fin n) k) = 0 := by
        have hmem : (1 : MvPolynomial (Fin n) k) ∈ RingHom.ker φ := by
          rw [hI]
          trivial
        exact hmem
      simp at hzero
    let A := (MvPolynomial (Fin n) k) ⧸ RingHom.ker φ
    let e : A ≃ₐ[k] S :=
      AlgEquiv.ofBijective (Ideal.kerLiftAlg φ) ⟨
        Ideal.kerLiftAlg_injective φ, by
          intro s
          obtain ⟨p, hp⟩ := hφ s
          refine ⟨Ideal.Quotient.mk (RingHom.ker φ) p, ?_⟩
          exact (Ideal.kerLiftAlg_mk φ p).trans hp
          ⟩
    obtain ⟨r, _, g, hginj, hgfinite, hdim, _⟩ :=
      Formalization.Books.Algebra.Unit115.noether_normalization
        (RingHom.ker φ) hI
    have hdimS : ringKrullDim S = r := by
      calc
        ringKrullDim S = ringKrullDim A :=
          (ringKrullDim_eq_of_ringEquiv e.toRingEquiv).symm
        _ = r := hdim
    let eK : (K ⊗[k] A) ≃ₐ[K] (K ⊗[k] S) :=
      Algebra.TensorProduct.congr (AlgEquiv.refl : K ≃ₐ[K] K) e
    let pK : (K ⊗[k] MvPolynomial (Fin r) k) ≃ₐ[K]
        MvPolynomial (Fin r) K :=
      MvPolynomial.algebraTensorAlgEquiv k K
    let hdimKData : TensorDimensionWitness (k := k) (S := S) (K := K) r := by
      let cKP : CommRing (K ⊗[k] MvPolynomial (Fin r) k) := inferInstance
      let cKA : CommRing (K ⊗[k] A) := inferInstance
      let cPK : CommRing (MvPolynomial (Fin r) k ⊗[k] K) := inferInstance
      let cAK : CommRing (A ⊗[k] K) := inferInstance
      let gT : (K ⊗[k] MvPolynomial (Fin r) k) →+*
          (K ⊗[k] A) :=
        (Algebra.TensorProduct.map (AlgHom.id K K) g).toRingHom
      let gK : MvPolynomial (Fin r) K →+* (K ⊗[k] S) :=
        eK.toRingEquiv.toRingHom.comp
          (gT.comp pK.symm.toRingEquiv.toRingHom)
      have hgTinj : Function.Injective gT := by
        change Function.Injective ((g.toLinearMap).lTensor K)
        exact Module.Flat.lTensor_preserves_injective_linearMap g.toLinearMap hginj
      have hgKinj : Function.Injective gK := by
        exact eK.injective.comp (hgTinj.comp pK.symm.injective)
      have hgTfinite : RingHom.Finite gT := by
        let gT' : (MvPolynomial (Fin r) k ⊗[k] K) →+* (A ⊗[k] K) :=
          (Algebra.TensorProduct.map g (AlgHom.id k K)).toRingHom
        have hgT'finite : RingHom.Finite gT' :=
          RingHom.Finite.tensorProductMap hgfinite (AlgHom.Finite.id k K)
        have hcomm :
            (Algebra.TensorProduct.comm k A K).toRingEquiv.toRingHom.comp
                (gT'.comp (Algebra.TensorProduct.comm k K
                  (MvPolynomial (Fin r) k)).toRingEquiv.toRingHom) = gT := by
          ext <;> simp [gT, gT']
        rw [← hcomm]
        exact (Algebra.TensorProduct.comm k A K).toRingEquiv.finite.comp
          (hgT'finite.comp
            (Algebra.TensorProduct.comm k K (MvPolynomial (Fin r) k)).toRingEquiv.finite)
      have hgKfinite : RingHom.Finite gK := by
        exact eK.toRingEquiv.finite.comp
          (hgTfinite.comp pK.symm.toRingEquiv.finite)
      have hdimK : ringKrullDim (K ⊗[k] S) = r := by
        have hdim' : ringKrullDim (MvPolynomial (Fin r) K) =
          ringKrullDim (K ⊗[k] S) :=
          Formalization.Books.Algebra.Unit112.integral_subring_ringKrullDim_eq
            gK hgKinj hgKfinite.to_isIntegral
        calc
          ringKrullDim (K ⊗[k] S) = ringKrullDim (MvPolynomial (Fin r) K) := hdim'.symm
          _ = r := by
            rw [MvPolynomial.ringKrullDim_of_isNoetherianRing,
              ringKrullDim_eq_zero_of_field]
            simp
      exact ⟨hdimK⟩
    exact hdimS.trans hdimKData.dimension.symm
  · let _ : Subsingleton S := not_nontrivial_iff_subsingleton.mp hS
    have : Subsingleton (K ⊗[k] S) := inferInstance
    simp only [ringKrullDim_eq_bot_of_subsingleton]

/- The local dimension is unchanged at corresponding points after base change.
   The right tensor inclusion is the map defining “lying over” here. -/
theorem dimension_at_a_point_preserved_field_extension
    {k S K : Type u} [Field k] [CommRing S] [Algebra k S]
    [Algebra.FiniteType k S] [Field K] [Algebra k K]
    (q : PrimeSpectrum S)
    (qK : PrimeSpectrum (K ⊗[k] S))
    (hlying :
      PrimeSpectrum.comap
          (Algebra.TensorProduct.includeRight (R := k) (A := K) (B := S)).toRingHom qK =
        q) :
    krullDimensionAt q = krullDimensionAt qK := by
  sorry

/- The local fibre dimension is both the difference of local Krull
   dimensions and the difference of the corresponding transcendence degrees;
   a prime minimal over the extended prime gives fibre dimension zero. -/
theorem inequalities_under_field_extension
    {k S K : Type u} [Field k] [CommRing S] [Algebra k S]
    [Algebra.FiniteType k S] [Field K] [Algebra k K]
    (q : PrimeSpectrum S)
    (qK : PrimeSpectrum (K ⊗[k] S))
    (hlying :
      PrimeSpectrum.comap
          (Algebra.TensorProduct.includeRight (R := k) (A := K) (B := S)).toRingHom qK =
        q) :
    WithBot.unbotD 0
          (ringKrullDim
            (Formalization.Books.Algebra.Unit112.tensorLocalRingOfFibre
              (Algebra.TensorProduct.includeRight (R := k) (A := K) (B := S)).toRingHom
              q qK hlying)) =
        WithBot.unbotD 0 (ringKrullDim (Localization.AtPrime qK.asIdeal)) -
          WithBot.unbotD 0 (ringKrullDim (Localization.AtPrime q.asIdeal)) ∧
      WithBot.unbotD 0 (ringKrullDim (Localization.AtPrime qK.asIdeal)) -
          WithBot.unbotD 0 (ringKrullDim (Localization.AtPrime q.asIdeal)) =
        Cardinal.toENat (Algebra.trdeg k q.asIdeal.ResidueField) -
          Cardinal.toENat (Algebra.trdeg K qK.asIdeal.ResidueField) ∧
      ∃ qK' : PrimeSpectrum (K ⊗[k] S),
        ∃ hlying' : PrimeSpectrum.comap
              (Algebra.TensorProduct.includeRight (R := k) (A := K) (B := S)).toRingHom qK' =
            q,
          WithBot.unbotD 0
              (ringKrullDim
                (Formalization.Books.Algebra.Unit112.tensorLocalRingOfFibre
                  (Algebra.TensorProduct.includeRight (R := k) (A := K) (B := S)).toRingHom
                  q qK' hlying')) = 0 := by
  sorry

end

end Formalization.Books.Algebra.Unit116
