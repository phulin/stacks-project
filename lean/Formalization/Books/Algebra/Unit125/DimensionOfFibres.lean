import Formalization.Books.Algebra.Unit14.BaseChange
import Formalization.Books.Algebra.Unit17.Spectrum
import Formalization.Books.Algebra.Unit50.ValuationRings
import Formalization.Books.Algebra.Unit112.HomomorphismsAndDimension
import Formalization.Books.Algebra.Unit113.DimensionFormula
import Formalization.Books.Algebra.Unit115.NoetherNormalization
import Formalization.Books.Algebra.Unit116.DimensionFiniteTypeAlgebrasReprise
import Formalization.Books.Algebra.Unit122.QuasiFinite
import Formalization.Books.Algebra.Unit123.ZariskiMain
import Mathlib.RingTheory.FinitePresentation
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.RingHom.QuasiFinite

/-!
# Commutative Algebra, Chapter 125: Dimension of fibres

The relative dimension at a point is the topological Krull dimension of the
canonical point of the canonical tensor-product fibre.  Polynomial algebras
use `MvPolynomial (Fin n)`, and quasi-finiteness uses the source-facing
predicates from Chapter 122, which retain the finite-type component of the
source definition while delegating the fibre condition to Mathlib.
-/

namespace Formalization.Books.Algebra.Unit125

open Set
open Formalization.Books.Topology.Unit10
open scoped TensorProduct

universe u v

noncomputable section

/-! ### Relative dimension -/

/-- The relative dimension of `S/R` at a prime `q` over `p`. -/
noncomputable def relativeDimensionAt
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (_hfinite : RingHom.FiniteType f)
    (p : PrimeSpectrum R) (q : PrimeSpectrum S)
    (hq : PrimeSpectrum.comap f q = p) : WithBot ℕ∞ :=
  krullDimensionAt
    (Formalization.Books.Algebra.Unit112.tensorFibrePrime f p q hq)

/-- The supremum of the relative dimensions of all fibres of `S/R`. -/
noncomputable def relativeDimension
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (hfinite : RingHom.FiniteType f) : WithBot ℕ∞ :=
  ⨆ q : PrimeSpectrum S,
    relativeDimensionAt f hfinite (PrimeSpectrum.comap f q) q rfl

/-- The locus where the relative fibre dimension is at most `n`. -/
noncomputable def relativeDimensionLocus
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (hfinite : RingHom.FiniteType f) (n : ℕ) :
    Set (PrimeSpectrum S) :=
  {q | relativeDimensionAt f hfinite (PrimeSpectrum.comap f q) q rfl ≤ n}

/-- For a finite-type map, quasi-finiteness at a point is equivalent to zero
relative dimension there. -/
theorem quasiFiniteAt_iff_relativeDimensionAt_eq_zero
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (hfinite : RingHom.FiniteType f)
    (p : PrimeSpectrum R) (q : PrimeSpectrum S)
    (hq : PrimeSpectrum.comap f q = p) :
    Formalization.Books.Algebra.Unit122.IsQuasiFiniteAt f q ↔
      relativeDimensionAt f hfinite p q hq = 0 := by
  let _ : Algebra R S := f.toAlgebra
  let _ : Algebra.FiniteType R S := hfinite
  have hp : PrimeSpectrum.comap (algebraMap R S) q = p := by
    simpa [RingHom.algebraMap_toAlgebra] using hq
  cases hp
  let e := PrimeSpectrum.preimageHomeomorphFiber R S
    (PrimeSpectrum.comap (algebraMap R S) q)
  let x : PrimeSpectrum.comap (algebraMap R S) ⁻¹'
      {PrimeSpectrum.comap (algebraMap R S) q} :=
    ⟨q, rfl⟩
  have hx : e x = Formalization.Books.Algebra.Unit112.tensorFibrePrime f
      (PrimeSpectrum.comap (algebraMap R S) q) q hq := by
    rfl
  have ht := Formalization.Books.Algebra.Unit122.isolated_point_fibre_criteria f
    (PrimeSpectrum.comap (algebraMap R S) q) q hq hfinite
  have hqf := Algebra.quasiFiniteAt_iff_isOpen_singleton_fiber (R := R) q
  have hqf' : Algebra.QuasiFiniteAt R q.asIdeal ↔ IsOpen ({x} : Set _) := by
    convert hqf using 1
  have hdim : IsOpen ({x} : Set _) ↔
      relativeDimensionAt f hfinite (PrimeSpectrum.comap (algebraMap R S) q) q hq = 0 := by
    rw [← e.isOpen_image, Set.image_singleton]
    change Formalization.Books.Topology.Unit26.IsolatedPoint (e x) ↔ _
    rw [hx]
    simpa [relativeDimensionAt] using ht.out 0 3
  change (RingHom.FiniteType f ∧ Algebra.QuasiFiniteAt R q.asIdeal) ↔ _
  constructor
  · intro h
    exact hdim.mp (hqf'.mp h.2)
  · intro h
    exact ⟨hfinite, hqf'.mpr (hdim.mpr h)⟩

/-! ### Quasi-finite polynomial covers -/

/-- A point of relative dimension `n` has a standard neighbourhood which is
quasi-finite over an `n`-variable polynomial algebra over the base. -/
/-
Proof roadmap (Stacks, Lemma 10.125.2 / Tag 00QE).

* Put `p := PrimeSpectrum.comap f q`, `k := p.asIdeal.ResidueField`, and
  `B := p.asIdeal.Fiber S`.  Transport `q` to the fibre point
  `qbar := tensorFibrePrime f p q rfl` (Unit112/HomomorphismsAndDimension.lean).
  Starting from the equality defining `hdim`, use
  `krullDimensionAt_hasBasis` (Topology/Unit10/KrullDimension.lean) to choose
  a fibre neighbourhood of dimension `n`.  Pull it back through
  `PrimeSpectrum.preimageHomeomorphFiber` to the subspace of `Spec S` over
  `p`, extend the subspace-open set to `Spec S`, and refine at `q` with
  `PrimeSpectrum.isTopologicalBasis_basic_opens`.  This produces `g₀ : S`
  with `g₀ ∉ q.asIdeal` and whose fibre basic open is contained in the chosen
  neighbourhood.  Monotonicity of dimension for open subsets together with
  `krullDimensionAt_le` gives both inequalities, so that basic open, cut out
  by `1 ⊗ₜ g₀`, still has topological Krull dimension exactly `n`.  Identify it
  open with the spectrum of `Localization.Away (1 ⊗ₜ g₀)` by
  `PrimeSpectrum.localization_away_isOpenEmbedding`, and hence turn the last
  equality into a ring-Krull-dimension equality using
  `PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim`.

* Identify that localized fibre with the fibre of `Localization.Away g₀`
  using `IsLocalization.Away.tensorProductEquivTMulRight`
  (Mathlib/RingTheory/Localization/BaseChange.lean).  Present this finite-type
  `k`-algebra as a quotient of `MvPolynomial (Fin m) k` using
  `Algebra.FiniteType.iff_quotient_mvPolynomial''` and
  `Ideal.quotientKerAlgEquivOfSurjective`.  Apply
  `Formalization.Books.Algebra.Unit115.noether_normalization` to its kernel.
  Its dimension assertion and the preceding equality force the returned
  number of normalizing variables to be `n`.

* The important descent point is the final membership supplied for every
  normalizing polynomial by `noether_normalization`: it lies in
  `Unit115.integerPolynomialSubalgebra k m`.  Prove a small local helper that
  this subalgebra is the range of coefficient change from the corresponding
  integer polynomial ring (use `Algebra.adjoin_eq_range` and
  `MvPolynomial.map`).  Thus the normalizing polynomials have representatives
  before passing from `R` to `k`; evaluating those representatives at the
  chosen finite-type generators defines
  `φ₀ : MvPolynomial (Fin n) R →ₐ[R] Localization.Away g₀`.  Check its
  specialization on `MvPolynomial.C` and `MvPolynomial.X`; under the fibre and
  quotient equivalences it is precisely the finite map returned by Unit115.

* Let `q₀` be the prime of `Localization.Away g₀` above `q`.  Apply
  `Unit122.quasiFiniteAt_above_prime_criteria` (Unit122/QuasiFinite.lean) to
  `φ₀.toRingHom`; the specialized finite normalization makes its fibre module
  finite, so `φ₀` is quasi-finite at `q₀`.  Now use
  `Unit123.isOpen_quasiFiniteLocus` (Unit123/ZariskiMain.lean) and choose a
  basic open about `q₀` contained in that locus.  Clear its denominator with
  `IsLocalization.Away.sec`, obtaining `s : S`, and identify the iterated
  localization with `Localization.Away (g₀ * s)` using
  `IsLocalization.Away.mul'` and `IsLocalization.algEquiv`.  Transport `φ₀`
  and the global `Unit122.IsQuasiFinite` assertion across that equivalence and
  return `g := g₀ * s`; primality and the two nonmembership hypotheses prove
  `g ∉ q.asIdeal`.

Do not try to apply normalization directly to the original fibre before the
first localization: `hdim` controls a neighbourhood of `qbar`, not the whole
fibre.  Also keep all comparisons above as explicit equivalences rather than
asking definitional equality to identify the two localization presentations.
-/
theorem quasiFinite_over_polynomial_algebra
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (hfinite : RingHom.FiniteType f)
    (q : PrimeSpectrum S) {n : ℕ}
    (hdim :
      relativeDimensionAt f hfinite (PrimeSpectrum.comap f q) q rfl = n) :
    letI : Algebra R S := f.toAlgebra
    ∃ g : S, g ∉ q.asIdeal ∧
      ∃ φ : MvPolynomial (Fin n) R →ₐ[R] Localization.Away g,
        Formalization.Books.Algebra.Unit122.IsQuasiFinite φ.toRingHom := by
  sorry

/-- The refined polynomial cover whose point contracts to the base prime and
the variables after the residue-field transcendence degree. -/
/-
Proof roadmap (Stacks, Lemma 10.125.3 / Tag 0520).

* Apply `quasiFinite_over_polynomial_algebra f hfinite q` to `hdim`.  Write
  `g₀ : S` for its denominator,
  `θ : MvPolynomial (Fin n) R →ₐ[R] Localization.Away g₀` for its map, and
  `q₀` for the prime above `q`.  Set
  `P := PrimeSpectrum.comap θ.toRingHom q₀`.  First record the explicit
  coefficient contraction
  `P.asIdeal.comap MvPolynomial.C = p.asIdeal`; prove it by composing comaps,
  using `hq`, and checking `θ.commutes` together with the localization map.

* Put `k := p.asIdeal.ResidueField`.  Form the fibre prime of `P` for the
  coefficient map `MvPolynomial.C` with
  `Unit112.tensorFibrePrime`, and transport it through
  `MvPolynomial.algebraTensorAlgEquiv` to a prime
  `Pbar : PrimeSpectrum (MvPolynomial (Fin n) k)`.  Prove the intermediate
  equality `Algebra.trdeg k Pbar.asIdeal.ResidueField = r` as a separate
  helper.  Use `Unit113.residueFieldMapAt θ.toRingHom P q₀ rfl` for the map
  `P.asIdeal.ResidueField →+* q₀.asIdeal.ResidueField`.  Quasi-finiteness of
  `θ` makes this extension finite by
  `Algebra.WeaklyQuasiFiniteAt.finite_residueField`, hence algebraic by
  `Algebra.IsAlgebraic.of_finite`.  Install explicitly the scalar tower from
  `k`, use injectivity of maps between fields for `FaithfulSMul`, and apply
  `lift_trdeg_add_eq` followed by `trdeg_eq_zero`.  The localization map
  `S → Localization.Away g₀` induces an equivalence between the residue fields
  of `q` and `q₀`; prove its residue-field map bijective using
  `IsLocalization.ringHom_ext` and `Ideal.ResidueField.ringHom_ext`, and use it
  to rewrite `htrdeg`.  Finally transport from the fibre prime to `Pbar` with
  `Ideal.residueFieldAlgEquiv` for `MvPolynomial.algebraTensorAlgEquiv`.
  Keeping these equivalences and tower instances in this helper prevents
  repeated inference of the several residue-field algebra structures.

* Apply `Unit115.refined_noether_normalization Pbar.asIdeal Pbar.isPrime`.
  It supplies `r₀ ≤ n`, an equality of the residue-field transcendence degree
  with `r₀`, and a finite polynomial endomorphism `rhoBar` whose inverse image
  of `Pbar.asIdeal` is `Unit115.tailVariableIdeal k n r₀` and which fixes
  constants.  Compare its transcendence-degree equality with the preceding
  one to obtain `r₀ = r`, and rewrite the tail ideal.  Lift the
  finitely many polynomials `rhoBar (MvPolynomial.X i)` to the base after one
  principal localization: use
  `IsLocalization.exist_integer_multiples_of_finite`
  (Mathlib/RingTheory/Localization/Integer.lean), instantiated with
  `R ⧸ p.asIdeal`, its non-zero-divisor submonoid, and `k`, on the finite union
  of their coefficient sets.  Lift the returned quotient-ring denominator to
  `a : R`; its submonoid membership gives `ha : a ∉ p.asIdeal`.  The universal
  property of `Localization.Away a` then gives a map to `k` whose range
  contains every coefficient, and
  `MvPolynomial.mem_range_map_iff_coeffs_subset` supplies polynomial lifts.
  This yields an endomorphism
  `rho : MvPolynomial (Fin n) (Localization.Away a) →ₐ[Localization.Away a]
    MvPolynomial (Fin n) (Localization.Away a)` defined by `MvPolynomial.aeval`.
  State and prove separately that its specialization to `k` is `rhoBar`, on
  `C` and `X`, and consequently is finite and has the required contracted
  fibre prime.

* Base-change `θ` along `R → Localization.Away a`; the last conjunct of
  `Unit122.isQuasiFinite_baseChange` preserves its global quasi-finiteness.
  Compose that base-changed map after `rho`.  On the fibre at the selected
  base prime this composite is `rhoBar` followed by the fibre of `θ`.
  Regard finite `rhoBar` as quasi-finite and use
  `Unit122.isQuasiFinite_comp` to make this specialized composite
  quasi-finite.  Then identify the fibre at the contracted polynomial prime
  and apply `Unit122.isolated_point_fibre_criteria` to prove that the lifted
  composite is quasi-finite at the prime induced by `q₀`.  Its finite-type
  part comes from `RingHom.FiniteType.comp`; do not claim that the lifted
  `rho` is finite globally merely because its special fibre is finite.  Now
  shrink the *target point in the localized `S`-algebra* inside
  `Unit123.quasiFiniteLocus`, whose openness is
  `Unit123.isOpen_quasiFiniteLocus`, and clear the new denominator.  Combining
  that denominator with `g₀` gives `b : S` with `hb : b ∉ q.asIdeal`; on this
  final target localization the composite is globally quasi-finite.

* Identify all iterated target localizations with
  `Localization.Away (f a * b)`.  Use `IsLocalization.Away.mul'`,
  `IsLocalization.Away.mul_of_associated`, and `IsLocalization.algEquiv`;
  prove that the transported base map is exactly
  `Unit30.localizationAwayMulMap f a b` by
  `IsLocalization.ringHom_ext`.  This produces the stated `φ`, and transports
  the composed `Unit122.IsQuasiFinite` proof to `φ.toRingHom`.

* Prove the contracted-prime identity before the final localization
  transport.  The equality for `rhoBar` gives one inclusion immediately
  after specialization.  For the reverse inclusion, specialize an arbitrary
  member of the comap, use
  `rhoBar ⁻¹' Pbar = Unit115.tailVariableIdeal k n r`, and lift the resulting
  coefficient statement back through `R → Localization.Away a`; the
  coefficient contraction recorded in the first step supplies precisely
  `(p.asIdeal.map (algebraMap R (Localization.Away a))).map MvPolynomial.C`.
  Localization at elements outside the chosen primes does not change this
  comap.  Finish with `Ideal.comap_comap` and `PrimeSpectrum.ext`, transporting
  along the same localization equivalences as for `φ`.

Interface audit: the equality must be in
`MvPolynomial (Fin n) (Localization.Away a)`, and the target really must be
the single principal localization at `f a * b`; both are necessary to retain
the base denominator while shrinking the source algebra.  Thus the current
statement is not overstrong.  A known dead end is to apply
`refined_noether_normalization` directly to `q.asIdeal`: its input must be the
polynomial *fibre* prime `Pbar`, or the tail-ideal equality has the wrong
coefficient contraction.
-/
theorem refined_quasiFinite_over_polynomial_algebra
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (hfinite : RingHom.FiniteType f)
    (p : PrimeSpectrum R) (q : PrimeSpectrum S)
    (hq : PrimeSpectrum.comap f q = p) :
    letI : Algebra R S := f.toAlgebra
    letI : Algebra p.asIdeal.ResidueField q.asIdeal.ResidueField :=
      (Formalization.Books.Algebra.Unit113.residueFieldMapAt f p q hq).toAlgebra
    ∀ {n r : ℕ},
      relativeDimensionAt f hfinite p q hq = n →
        Algebra.trdeg p.asIdeal.ResidueField q.asIdeal.ResidueField = r →
          ∃ a : R, ∃ ha : a ∉ p.asIdeal,
            ∃ b : S, ∃ hb : b ∉ q.asIdeal,
              let α :=
                Formalization.Books.Algebra.Unit30.localizationAwayMulMap f a b
              letI : Algebra (Localization.Away a)
                  (Localization.Away (f a * b)) := α.toAlgebra
              ∃ φ : MvPolynomial (Fin n) (Localization.Away a) →ₐ[
                  Localization.Away a] Localization.Away (f a * b),
                Formalization.Books.Algebra.Unit122.IsQuasiFinite φ.toRingHom ∧
                  Ideal.comap φ.toRingHom
                      (Formalization.Books.Algebra.Unit122.localizedPrimeAwayMul
                        f p q hq a b ha hb).asIdeal =
                    (p.asIdeal.map (algebraMap R (Localization.Away a))).map
                        (MvPolynomial.C : Localization.Away a →+*
                          MvPolynomial (Fin n) (Localization.Away a)) +
                      Formalization.Books.Algebra.Unit115.tailVariableIdeal
                        (Localization.Away a) n r := by
  sorry

/-! ### Dimension inequalities -/

/-- A quasi-finite finite-type map cannot increase the dimension of a local
ring. -/
theorem ringKrullDim_localization_le_of_quasiFiniteAt
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S)
    (p : PrimeSpectrum R) (q : PrimeSpectrum S)
    (hq : PrimeSpectrum.comap f q = p)
    (hquasi : Formalization.Books.Algebra.Unit122.IsQuasiFiniteAt f q) :
    ringKrullDim (Localization.AtPrime q.asIdeal) ≤
      ringKrullDim (Localization.AtPrime p.asIdeal) := by
  let _ : Algebra R S := f.toAlgebra
  rcases hquasi with ⟨hfinite, hqf⟩
  let _ : Algebra.QuasiFiniteAt R q.asIdeal := hqf
  have hqp : q.asIdeal.comap f = p.asIdeal := by
    simpa [PrimeSpectrum.comap_asIdeal] using congrArg PrimeSpectrum.asIdeal hq
  let F : Set.Iic q → Set.Iic p := fun r =>
    ⟨PrimeSpectrum.comap f r.1, by
      apply (PrimeSpectrum.asIdeal_le_asIdeal _ _).mp
      change r.1.asIdeal.comap f ≤ p.asIdeal
      calc
        r.1.asIdeal.comap f ≤ q.asIdeal.comap f :=
          Ideal.comap_mono ((PrimeSpectrum.asIdeal_le_asIdeal _ _).mpr r.2)
        _ = p.asIdeal := hqp⟩
  have hF : StrictMono F := by
    intro a b hab
    change PrimeSpectrum.comap f a.1 < PrimeSpectrum.comap f b.1
    apply lt_of_le_of_ne
    · exact (PrimeSpectrum.asIdeal_le_asIdeal _ _).mp
        (Ideal.comap_mono ((PrimeSpectrum.asIdeal_le_asIdeal _ _).mpr hab.le))
    · intro heq
      have hbeq : b.1.asIdeal ≤ q.asIdeal :=
        (PrimeSpectrum.asIdeal_le_asIdeal _ _).mpr b.2
      let _ : Algebra.QuasiFiniteAt R b.1.asIdeal :=
        Algebra.QuasiFiniteAt.of_le hbeq
      have habideal : a.1.asIdeal ≤ b.1.asIdeal :=
        (PrimeSpectrum.asIdeal_le_asIdeal _ _).mpr hab.le
      have hunder : a.1.asIdeal.under R = b.1.asIdeal.under R := by
        rw [Ideal.under_def, Ideal.under_def]
        simpa [PrimeSpectrum.comap_asIdeal, RingHom.algebraMap_toAlgebra] using
          congrArg PrimeSpectrum.asIdeal heq
      have hab' : a.1 = b.1 := by
        apply PrimeSpectrum.ext
        exact Algebra.QuasiFiniteAt.eq_of_le_of_under_eq habideal hunder
      exact hab.ne (Subtype.ext hab')
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height
      q.asIdeal (Localization.AtPrime q.asIdeal),
    IsLocalization.AtPrime.ringKrullDim_eq_height
      p.asIdeal (Localization.AtPrime p.asIdeal)]
  rw [PrimeSpectrum.height_eq_orderHeight q, PrimeSpectrum.height_eq_orderHeight p]
  rw [Order.height_eq_krullDim_Iic q, Order.height_eq_krullDim_Iic p]
  exact Order.krullDim_le_of_strictMono F hF

/-- A quasi-finite cover of affine `n`-space has Krull dimension at most `n`. -/
theorem ringKrullDim_le_of_quasiFinite_polynomial
    {k S : Type u} [Field k] [CommRing S] [Algebra k S]
    [Algebra.FiniteType k S] (n : ℕ)
    (φ : MvPolynomial (Fin n) k →ₐ[k] S)
    (hquasi : Formalization.Books.Algebra.Unit122.IsQuasiFinite φ.toRingHom) :
    ringKrullDim S ≤ n := by
  rcases hquasi with ⟨hfinite, hqf⟩
  apply (Formalization.Books.Algebra.Unit60.ringKrullDim_le_iff_maximal_height_le
    (n : WithBot ℕ∞)).mpr
  intro m hm
  let q : PrimeSpectrum S := ⟨m, hm.isPrime⟩
  have hloc := ringKrullDim_localization_le_of_quasiFiniteAt
    φ.toRingHom (PrimeSpectrum.comap φ.toRingHom q) q rfl
    ⟨hfinite, hqf q⟩
  have hpoly : ringKrullDim (MvPolynomial (Fin n) k) =
      (n : WithBot ℕ∞) := by
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing,
      ringKrullDim_eq_zero_of_field]
    simp
  have hbase : ringKrullDim
      (Localization.AtPrime (PrimeSpectrum.comap φ.toRingHom q).asIdeal) ≤
        (n : WithBot ℕ∞) := by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height
      (PrimeSpectrum.comap φ.toRingHom q).asIdeal
      (Localization.AtPrime (PrimeSpectrum.comap φ.toRingHom q).asIdeal)]
    have hp := (Formalization.Books.Algebra.Unit60.ringKrullDim_le_iff_prime_height_le
      (R := MvPolynomial (Fin n) k) (ringKrullDim (MvPolynomial (Fin n) k))).mp le_rfl
        (PrimeSpectrum.comap φ.toRingHom q).isPrime
    rw [hpoly] at hp
    exact hp
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height m
    (Localization.AtPrime m)] at hloc
  calc
    (m.height : WithBot ℕ∞) ≤
        ringKrullDim (Localization.AtPrime (PrimeSpectrum.comap φ.toRingHom q).asIdeal) := hloc
    _ ≤ (n : WithBot ℕ∞) := hbase

/-! ### Openness and base change of bounded fibre dimension -/

/-- Around a point where the fibre has dimension `n`, the fibre dimensions are
bounded above by `n` on an open neighbourhood. -/
/-
Proof roadmap (Stacks, Lemma 10.125.6 / Tag 00QH, local step).

* Obtain `g : S`, `hg : g ∉ q.asIdeal`, and
  `φ : MvPolynomial (Fin n) R →ₐ[R] Localization.Away g` from
  `quasiFinite_over_polynomial_algebra f hfinite q hdim`.  Take
  `V := PrimeSpectrum.basicOpen g`; use `PrimeSpectrum.isOpen_basicOpen` and
  `PrimeSpectrum.mem_basicOpen` for the first three parts of the conclusion.

* Fix `q' ∈ V`, put `p' := PrimeSpectrum.comap f q'` and
  `k' := p'.asIdeal.ResidueField`, and let `q'g` be
  `Unit17.standardOpenSpectrumInverse g ⟨q', hq'⟩`
  (Unit17/Spectrum.lean).  Base-change `φ.toRingHom` along `R → k'`.
  Instantiate the third conjunct of `Unit122.isQuasiFinite_baseChange` with
  `R' := k'`; after transport by `MvPolynomial.algebraTensorAlgEquiv`, this is
  an `IsQuasiFinite` map
  `MvPolynomial (Fin n) k' →ₐ[k']
    (Localization.Away g ⊗[R] k')`.  Apply the already proved
  `ringKrullDim_le_of_quasiFinite_polynomial` to get the intermediate bound
  `ringKrullDim (Localization.Away g ⊗[R] k') ≤ n`.

* Compare that target with the principal localization of the original fibre
  `p'.asIdeal.Fiber S` at the image of `g`.  The algebra equivalence is
  `IsLocalization.Away.tensorProductEquivTMulRight`
  (Mathlib/RingTheory/Localization/BaseChange.lean), composed with tensor
  commutativity if the factors occur in the opposite order.  State explicitly
  that it sends the fibre point `Unit112.tensorFibrePrime f p' q' rfl` to the
  prime corresponding to `q'g`; prove this by `PrimeSpectrum.ext` and check
  pure tensors rather than by `rfl`.

* The spectrum of this localized fibre is homeomorphic to the standard open
  containing the fibre point by `Unit17.standardOpenSpectrumHomeomorph`.
  Convert its topological dimension to the preceding ring dimension using
  `PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim`, then apply
  `krullDimensionAt_le` (Topology/Unit10/KrullDimension.lean) to that open
  neighbourhood.  Unfold only `relativeDimensionAt` at the end; the resulting
  inequality is exactly the requested bound for `q'`.

The essential transport is through the fibre of `Localization.Away g`; it is
not definitionally equal to the localization of `p'.asIdeal.Fiber S`, so a
direct `simpa` without the stated tensor/localization equivalence is a known
dead end.
-/
theorem relativeDimensionLocus_isOpen_near
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (hfinite : RingHom.FiniteType f)
    (p : PrimeSpectrum R) (q : PrimeSpectrum S)
    (hq : PrimeSpectrum.comap f q = p) {n : ℕ}
    (hdim : relativeDimensionAt f hfinite p q hq = n) :
    ∃ V : Set (PrimeSpectrum S), IsOpen V ∧ q ∈ V ∧
      ∀ q' : PrimeSpectrum S, q' ∈ V →
        relativeDimensionAt f hfinite (PrimeSpectrum.comap f q') q' rfl ≤ n := by
  sorry

/-- The bounded relative-dimension locus is open. -/
/-
Proof roadmap.

Use `isOpen_iff_forall_mem_open`.  For a point `q` in
`relativeDimensionLocus f hfinite n`, abbreviate
`d₀ := relativeDimensionAt f hfinite (PrimeSpectrum.comap f q) q rfl`; the
membership hypothesis says `d₀ ≤ (n : WithBot ℕ∞)`.  Extract a natural value
without assuming it definitionally:

1. Prove `0 ≤ d₀` by unfolding `relativeDimensionAt` and
   `krullDimensionAt`, applying `le_iInf`, and using
   `Order.krullDim_nonneg_iff`.  For every open neighbourhood `U`, the closure
   of the singleton of its distinguished point is the required nonempty
   irreducible closed subset (`isIrreducible_singleton.closure` and
   `isClosed_closure`).
2. This excludes `⊥`; apply `WithBot.ne_bot_iff_exists` to write
   `d₀ = (x : WithBot ℕ∞)` for `x : ℕ∞`.
3. The bound by the finite value `n` excludes `x = ⊤`; apply
   `ENat.ne_top_iff_exists` to obtain `d : ℕ` with `x = d`.  Coercion
   injectivity then gives both `d₀ = d` and `d ≤ n`.

Apply `relativeDimensionLocus_isOpen_near f hfinite _ q rfl` to the equality
`d₀ = d`.  It returns an open `V` containing `q` on which every relative
dimension is at most `d`; compose with `d ≤ n` and finish with
`simpa only [relativeDimensionLocus, Set.mem_setOf_eq]`.  The explicit
`WithBot ℕ∞ → ℕ∞ → ℕ` extraction is essential: destructing `d₀` as though the
upper bound alone made it a natural number leaves the `⊥` case unresolved.
-/
theorem isOpen_relativeDimensionLocus
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (hfinite : RingHom.FiniteType f) (n : ℕ) :
    IsOpen (relativeDimensionLocus f hfinite n) := by
  sorry

/-- Formation of the bounded relative-dimension locus commutes with arbitrary
base change. -/
theorem relativeDimensionLocus_baseChange
    {R S R' : Type u} [CommRing R] [CommRing S] [CommRing R']
    (f : R →+* S) (g : R →+* R') (hfinite : RingHom.FiniteType f)
    (n : ℕ) :
    letI : Algebra R S := f.toAlgebra
    letI : Algebra R R' := g.toAlgebra
    (PrimeSpectrum.comap
        (Formalization.Books.Algebra.Unit14.baseChangeAlgebraMap f g)) ⁻¹'
        relativeDimensionLocus f hfinite n =
      relativeDimensionLocus
        (Formalization.Books.Algebra.Unit14.baseChangeRingMap f g)
        (Formalization.Books.Algebra.Unit14.baseChange_finite_type f g hfinite) n := by
  sorry

/-- For a finitely presented map, the bounded relative-dimension locus is a
quasi-compact open. -/
theorem isOpen_isCompact_relativeDimensionLocus_of_finitePresentation
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (hfinitePresentation : RingHom.FinitePresentation f)
    (n : ℕ) :
    IsOpen
        (relativeDimensionLocus f
          (RingHom.FiniteType.of_finitePresentation hfinitePresentation) n) ∧
      IsCompact
        (relativeDimensionLocus f
          (RingHom.FiniteType.of_finitePresentation hfinitePresentation) n) := by
  sorry

/-! ### Finite-type domains over valuation rings -/

/-- For a finite-type domain over a valuation ring, the generic and special
fibres have the same dimension; the special fibre is equidimensional. -/
theorem finiteType_domain_over_valuationRing_dimension_fibres
    {R S : Type u} [CommRing R] [IsDomain R] [ValuationRing R]
    [CommRing S] [IsDomain S] [Algebra R S]
    (hinjective : Function.Injective (algebraMap R S))
    (hfinite : RingHom.FiniteType (algebraMap R S))
    (hnonzero : Nontrivial (S ⊗[R] IsLocalRing.ResidueField R)) :
    ringKrullDim (S ⊗[R] IsLocalRing.ResidueField R) =
        ringKrullDim (S ⊗[R] FractionRing R) ∧
      Formalization.Books.Topology.Unit10.Equidimensional
        (X := PrimeSpectrum (S ⊗[R] IsLocalRing.ResidueField R)) := by
  sorry

end

end Formalization.Books.Algebra.Unit125
