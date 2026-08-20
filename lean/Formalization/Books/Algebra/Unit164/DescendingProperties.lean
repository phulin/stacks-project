import Formalization.Books.Algebra.Unit37.NormalRings
import Formalization.Books.Algebra.Unit105.CatenaryRings
import Formalization.Books.Algebra.Unit110.RegularRingsAndGlobalDimension
import Formalization.Books.Algebra.Unit112.HomomorphismsAndDimension
import Formalization.Books.Algebra.Unit152.LocalStructureUnramifiedRingMaps
import Formalization.Books.Algebra.Unit157.SerresCriterion
import Formalization.Books.Algebra.Unit162.NagataRings
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.RingTheory.Ideal.Height
import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RingHom.Etale
import Mathlib.RingTheory.RingHom.FaithfullyFlat
import Mathlib.RingTheory.RingHom.Finite
import Mathlib.RingTheory.RingHom.FiniteType
import Mathlib.RingTheory.Finiteness.Descent
import Mathlib.RingTheory.RingHom.Smooth
import Mathlib.RingTheory.Spectrum.Prime.RingHom
import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Commutative Algebra, Chapter 164: Descending properties

The source section consists of faithfully flat descent for the standard ring
properties, descent of the Nagata property, and a counterexample showing that
universal catenarity does not descend along an étale map.  The named ring
properties below use Mathlib and earlier-chapter predicates whenever those
interfaces already exist.
-/

namespace Formalization.Books.Algebra.Unit164

open Formalization.Books.Algebra.Unit37
open Set
open scoped TensorProduct

universe u v w

noncomputable section

/-! ## The source's local conditions -/

/- The introductory warning that descent results are useful only together with
  the corresponding ascent results is explanatory rather than a separate
  mathematical proposition.  The declarations in this file record the
  precise descent assertions that follow it. -/

/-
The source's `(S_k)` condition says that at every prime, local depth is at
least the minimum of `k` and local dimension.  `ringKrullDim` has codomain
`WithBot ℕ∞`, so the depth and the integer are cast to that same canonical
dimension type.
-/
/- The source's `(R_k)` condition says that every prime of height at most `k`
  has regular localization.  The Noetherian hypothesis is kept on the
  theorem statements, as in the source, rather than duplicated in this
  predicate. -/
/-! ## Japanese and Nagata properties -/

/- Reuse the canonical predicates introduced in Chapters 161 and 162.  These
  aliases preserve Unit164's public names without creating definitionally
  unrelated copies of the Japanese and Nagata interfaces. -/
abbrev IsJapaneseDomain (R : Type u) [CommRing R] [IsDomain R] : Prop :=
  Formalization.Books.Algebra.Unit161.IsJapaneseDomain R

abbrev IsUniversallyJapanese (R : Type u) [CommRing R] : Prop :=
  Formalization.Books.Algebra.Unit162.IsUniversallyJapanese R

abbrev IsNagataRing (R : Type u) [CommRing R] : Prop :=
  Formalization.Books.Algebra.Unit162.IsNagataRing R

/- The characterization invoked in the proof of Nagata descent. -/
theorem nagata_iff_noetherian_universallyJapanese
    {R : Type u} [CommRing R] :
    IsNagataRing R ↔ IsNoetherianRing R ∧ IsUniversallyJapanese R := by
  /-
  Proof roadmap:
  1. Use
     `Formalization.Books.Algebra.Unit162.nagata_iff_universallyJapanese_noetherian`
     from `Formalization/Books/Algebra/Unit162/NagataRings.lean`.  After the
     aliases above unfold, its left side is definitionally the present left
     side and its right side is
     `IsUniversallyJapanese R ∧ IsNoetherianRing R`.
  2. Finish by commuting the two conjuncts, e.g. `simpa [and_comm] using ...`.
     No quotient or universe conversion is needed: all three predicates are
     instantiated in `Type u`.
  -/
  simpa [and_comm] using
    (Formalization.Books.Algebra.Unit162.nagata_iff_universallyJapanese_noetherian
      (R := R))

/- The map from a ring to the localization of a target ring at one of its
  prime ideals, used to state that the maximal ideal of `A` generates the
  maximal ideal after localization. -/
noncomputable def mapToPrimeLocalization
    {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) (p : PrimeSpectrum B) :
    A →+* Localization.AtPrime p.asIdeal :=
  (algebraMap B (Localization.AtPrime p.asIdeal)).comp f

/-! ## Faithfully flat descent -/

/- The informal proof uses the faithfully flat ideal criterion for the
  Noetherian condition; later proofs use the corresponding nilradical,
  localization, and local-criterion arguments. -/

theorem noetherian_descends_of_faithfullyFlat
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (hff : RingHom.FaithfullyFlat f)
    (hS : IsNoetherianRing S) : IsNoetherianRing R := by
  let : Algebra R S := f.toAlgebra
  let _ : Module.FaithfullyFlat R S := by
    simpa [RingHom.FaithfullyFlat] using hff
  rw [isNoetherianRing_iff_ideal_fg]
  intro I
  apply Ideal.FG.of_FG_map_of_faithfullyFlat (S := S)
  exact hS.noetherian _

theorem reduced_descends_of_faithfullyFlat
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (hff : RingHom.FaithfullyFlat f)
    (hS : IsReduced S) : IsReduced R := by
  let : IsReduced S := hS
  exact isReduced_of_injective f hff.injective

theorem normal_descends_of_faithfullyFlat
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (hff : RingHom.FaithfullyFlat f)
    (hS : IsNormalRing S) : IsNormalRing R := by
  let : Algebra R S := f.toAlgebra
  let _ : Module.FaithfullyFlat R S := by
    simpa [RingHom.FaithfullyFlat] using hff
  have hred : IsReduced R :=
    reduced_descends_of_faithfullyFlat f hff (normalRing_isReduced hS)
  let : IsReduced R := hred
  intro p
  obtain ⟨q, hq⟩ :=
    PrimeSpectrum.comap_surjective_of_faithfullyFlat (A := R) (B := S) p
  have hpq : p.asIdeal = q.asIdeal.comap f := by
    have hpq' : q.asIdeal.comap (algebraMap R S) = p.asIdeal :=
      congrArg PrimeSpectrum.asIdeal hq
    change p.asIdeal = q.asIdeal.comap (algebraMap R S)
    exact hpq'.symm
  let hloc := Localization.localRingHom p.asIdeal q.asIdeal f hpq
  let : Algebra (Localization.AtPrime p.asIdeal) (Localization.AtPrime q.asIdeal) :=
    hloc.toAlgebra
  have hflat : RingHom.Flat hloc :=
    RingHom.Flat.localRingHom hff.flat q.asIdeal p.asIdeal hpq
  let _ : Module.Flat (Localization.AtPrime p.asIdeal) (Localization.AtPrime q.asIdeal) := by
    simpa [RingHom.Flat] using hflat
  let _ : IsLocalHom
      (algebraMap (Localization.AtPrime p.asIdeal) (Localization.AtPrime q.asIdeal)) := by
    change IsLocalHom hloc
    infer_instance
  let _ : Module.FaithfullyFlat (Localization.AtPrime p.asIdeal)
      (Localization.AtPrime q.asIdeal) :=
    Module.FaithfullyFlat.of_flat_of_isLocalHom
  let : IsDomain (Localization.AtPrime q.asIdeal) := (hS q).1
  let : IsDomain (Localization.AtPrime p.asIdeal) :=
    (FaithfulSMul.algebraMap_injective
      (Localization.AtPrime p.asIdeal) (Localization.AtPrime q.asIdeal)).isDomain _
  have hclosed : IsIntegrallyClosed (Localization.AtPrime p.asIdeal) := by
    rw [isIntegrallyClosed_iff (FractionRing (Localization.AtPrime p.asIdeal))]
    intro x hx
    let g : Localization.AtPrime p.asIdeal →+* FractionRing (Localization.AtPrime q.asIdeal) :=
      (algebraMap (Localization.AtPrime q.asIdeal) _).comp hloc
    have hg : Function.Injective g :=
      (IsFractionRing.injective (Localization.AtPrime q.asIdeal)
        (FractionRing (Localization.AtPrime q.asIdeal))).comp
        (FaithfulSMul.algebraMap_injective
          (Localization.AtPrime p.asIdeal) (Localization.AtPrime q.asIdeal))
    let φ : FractionRing (Localization.AtPrime p.asIdeal) →+*
        FractionRing (Localization.AtPrime q.asIdeal) :=
      IsFractionRing.lift (A := Localization.AtPrime p.asIdeal)
        (K := FractionRing (Localization.AtPrime p.asIdeal))
        (L := FractionRing (Localization.AtPrime q.asIdeal)) hg
    have hφ (z : Localization.AtPrime p.asIdeal) :
        φ (algebraMap _ _ z) = algebraMap _ _ (hloc z) := by
      exact IsFractionRing.lift_algebraMap hg z
    obtain ⟨a, b, hb, rfl⟩ :=
      IsFractionRing.div_surjective (Localization.AtPrime p.asIdeal) x
    have hfx : IsIntegral (Localization.AtPrime q.asIdeal) (φ
        (algebraMap _ _ a / algebraMap _ _ b)) := by
      apply IsIntegral.map_of_comp_eq (R := Localization.AtPrime p.asIdeal)
        (S := FractionRing (Localization.AtPrime p.asIdeal))
        (T := Localization.AtPrime q.asIdeal)
        (U := FractionRing (Localization.AtPrime q.asIdeal))
        (algebraMap _ _) φ
      · ext z
        exact (hφ z).symm
      · exact hx
    obtain ⟨c, hc⟩ :=
      (isIntegrallyClosed_iff (FractionRing (Localization.AtPrime q.asIdeal))).mp
        (hS q).2 hfx
    have hbA : (b : Localization.AtPrime p.asIdeal) ≠ 0 :=
      mem_nonZeroDivisors_iff_ne_zero.mp hb
    have hbB : hloc b ≠ 0 := by
      intro h
      apply hbA
      apply (FaithfulSMul.algebraMap_injective
        (Localization.AtPrime p.asIdeal) (Localization.AtPrime q.asIdeal))
      change hloc b = hloc 0
      simpa using h
    have hbF : algebraMap (Localization.AtPrime q.asIdeal)
        (FractionRing (Localization.AtPrime q.asIdeal)) (hloc b) ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors
        (mem_nonZeroDivisors_iff_ne_zero.mpr hbB)
    have hcross : hloc b * c = hloc a := by
      apply IsFractionRing.injective (Localization.AtPrime q.asIdeal)
        (FractionRing (Localization.AtPrime q.asIdeal))
      calc
        algebraMap _ _ (hloc b * c) =
            algebraMap _ _ (hloc b) * algebraMap _ _ c := map_mul _ _ _
        _ = φ (algebraMap _ _ b) *
            φ (algebraMap _ _ a / algebraMap _ _ b) := by rw [hc, hφ]
        _ = φ (algebraMap _ _ b) *
            (φ (algebraMap _ _ a) / φ (algebraMap _ _ b)) := by rw [map_div₀]
        _ = φ (algebraMap _ _ a) := by
          rw [mul_comm, div_mul_cancel₀ _ (by simpa [hφ] using hbF)]
        _ = algebraMap _ _ (hloc a) := hφ a
    have hmem_map :
        hloc a ∈ Ideal.map hloc (Ideal.span ({b} : Set _)) := by
      rw [← hcross]
      exact (Ideal.map hloc (Ideal.span ({b} : Set _))).mul_mem_right c
        (Ideal.mem_map_of_mem hloc (Ideal.mem_span_singleton_self b))
    have hmem : a ∈ Ideal.span ({b} : Set _) := by
      have hmem' : a ∈
          (Ideal.map (algebraMap (Localization.AtPrime p.asIdeal)
            (Localization.AtPrime q.asIdeal)) (Ideal.span ({b} : Set _))).comap
              (algebraMap (Localization.AtPrime p.asIdeal)
                (Localization.AtPrime q.asIdeal)) :=
        Ideal.mem_comap.mpr hmem_map
      rw [Ideal.comap_map_eq_self_of_faithfullyFlat] at hmem'
      exact hmem'
    obtain ⟨d, hd⟩ := Ideal.mem_span_singleton'.mp hmem
    refine ⟨d, ?_⟩
    rw [← hd, map_mul,
      mul_div_cancel_right₀ _ (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb)]
  exact ⟨inferInstance, hclosed⟩

theorem regular_descends_of_faithfullyFlat
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (hff : RingHom.FaithfullyFlat f)
    (hS : IsRegularRing S) : IsRegularRing R := by
  /-
  Proof roadmap:
  1. Install `hS` as the `IsRegularRing S` instance and obtain
     `hRnoeth : IsNoetherianRing R` from
     `noetherian_descends_of_faithfullyFlat f hff hS.toIsNoetherianRing`.
     Install `hRnoeth`; construct the result with `IsRegularRing.mk`.
  2. For a prime `p : Ideal R`, regard it as `PrimeSpectrum R` and choose
     `q : PrimeSpectrum S` over it using
     `PrimeSpectrum.comap_surjective_of_faithfullyFlat` from
     `Mathlib/RingTheory/Flat/FaithfullyFlat/Algebra.lean` (after setting
     `f.toAlgebra` and the corresponding `Module.FaithfullyFlat R S`).
  3. Set
     `g := Localization.localRingHom p q f hpq`, where
     `hpq : p = q.asIdeal.comap f` comes from the equality of spectra.
     `RingHom.Flat.localRingHom hff.flat q.asIdeal p hpq` supplies
     `RingHom.Flat g`; the local-hom instance is inferred.  Noetherianity of
     both localizations follows from the installed Noetherian instances.
  4. The target localization is regular by
     `hS.isRegularLocalRing_localization q.asIdeal`.  Apply
     `Formalization.Books.Algebra.Unit110.isRegularLocalRing_of_flat_localHom_of_regular`
     from `Formalization/Books/Algebra/Unit110/RegularRingsAndGlobalDimension.lean`
     to `g`.  This is exactly the required field of `IsRegularRing.mk`.
  -/
  sorry

theorem propertySk_descends_of_faithfullyFlat
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (hff : RingHom.FaithfullyFlat f) (k : ℕ)
    (hS : IsNoetherianRing S)
    (hSk : Formalization.Books.Algebra.Unit157.HasPropertySk S k) :
    IsNoetherianRing R ∧
      Formalization.Books.Algebra.Unit157.HasPropertySk R k := by
  /-
  Proof roadmap (one upstream depth lemma is still required):
  1. Prove the first conjunct with
     `noetherian_descends_of_faithfullyFlat f hff hS`; install both
     Noetherian instances and unfold `Unit157.HasPropertySk`.
  2. For `p : PrimeSpectrum R`, first choose `q₀` over `p` by
     `PrimeSpectrum.comap_surjective_of_faithfullyFlat`.  Then use
     `Ideal.exists_minimalPrimes_le` from
     `Mathlib/RingTheory/Ideal/MinimalPrime/Basic.lean` to choose
     `q.asIdeal ∈ (p.asIdeal.map f).minimalPrimes` below `q₀.asIdeal`.
     Faithful flatness gives
     `(p.asIdeal.map f).comap f = p.asIdeal` via
     `Ideal.comap_map_eq_self_of_faithfullyFlat`; squeezing between `p` and
     `q₀.comap f` proves `PrimeSpectrum.comap f q = p`.
  3. For `g : Localization.AtPrime p.asIdeal →+*
     Localization.AtPrime q.asIdeal`, use
     `Unit112.ringKrullDim_localization_eq_base_add_fibre_of_goingDown` from
     `Formalization/Books/Algebra/Unit112/HomomorphismsAndDimension.lean`.
     Flatness installs `Algebra.HasGoingDown R S`.  Minimality of `q` over
     `pS`, together with `Unit112.localRingOfFibre_equiv_localized_quotient`
     and `Ideal.height_eq_zero_iff`, makes the fibre term zero, hence
     `ringKrullDim R_p = ringKrullDim S_q`.
  4. The missing reusable result should state that for this same flat local
     map, when `q ∈ (p.map f).minimalPrimes`, one has
     `Unit72.localDepth R_p R_p = Unit72.localDepth S_q S_q`.  Its proof is
     the source's ideal-of-definition argument: use
     `IsLocalization.AtPrime.radical_map_of_mem_minimalPrimes` to show that
     the extension of the maximal ideal of `R_p` has radical the maximal
     ideal of `S_q`, then combine invariance of depth under radical with
     faithfully-flat preservation/descent of regular sequences.  That lemma
     is not exposed by the currently imported API.
  5. Apply `hSk q`, rewrite its dimension and depth terms with steps 3 and 4,
     and return the transported inequality.

  Do not use `Unit163.depth_eq_add_depth_fibre` as the missing step: its
  current statement is inconsistent already for an identity map (it reduces
  to `depth = depth + depth`).
  -/
  sorry

theorem propertyRk_descends_of_faithfullyFlat
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (hff : RingHom.FaithfullyFlat f) (k : ℕ)
    (hS : IsNoetherianRing S)
    (hRk : Formalization.Books.Algebra.Unit157.HasPropertyRk S k) :
    IsNoetherianRing R ∧
      Formalization.Books.Algebra.Unit157.HasPropertyRk R k := by
  /-
  Proof roadmap:
  1. Obtain and install Noetherianity of `R` as in the `(S_k)` proof, then
     unfold `Unit157.HasPropertyRk` and fix `p : PrimeSpectrum R` with
     `p.asIdeal.height ≤ (k : ℕ∞)`.
  2. Choose `q : PrimeSpectrum S` minimal over `p.asIdeal.map f` by the
     `q₀`/`Ideal.exists_minimalPrimes_le` construction in the preceding
     roadmap.  Again prove `PrimeSpectrum.comap f q = p` using
     `Ideal.comap_map_eq_self_of_faithfullyFlat`.
  3. Apply
     `Unit112.ringKrullDim_localization_eq_base_add_fibre_of_goingDown`.
     The quotient-fibre prime is minimal, so
     `Ideal.height_eq_zero_iff` and
     `Unit112.localRingOfFibre_equiv_localized_quotient` reduce the fibre
     dimension to zero.  Rewrite both local dimensions with
     `IsLocalization.AtPrime.ringKrullDim_eq_height`; this yields
     `q.asIdeal.height = p.asIdeal.height`, hence the height hypothesis needed
     for `hRk q`.
  4. Form the flat local map
     `g := Localization.localRingHom p.asIdeal q.asIdeal f hpq` and obtain its
     flatness from `RingHom.Flat.localRingHom hff.flat ...`.  Apply
     `Unit110.isRegularLocalRing_of_flat_localHom_of_regular` to `g` and the
     regularity `hRk q (...)`.  This is precisely the required regularity of
     `Localization.AtPrime p.asIdeal`.
  -/
  sorry

/- Smoothness and surjectivity on spectra are the exact hypotheses in the
  source's Nagata descent lemma.  The proof route is the finite-type local
  criterion for the N-2 property together with surjectivity of `Spec S →
  Spec R`. -/
theorem nagata_descends_of_smooth_surjective
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (hsmooth : RingHom.Smooth f)
    (hsurjective : Function.Surjective (PrimeSpectrum.comap f))
    (hS : IsNagataRing S) : IsNagataRing R := by
  /-
  Proof roadmap:
  1. Build `hff : RingHom.FaithfullyFlat f` with
     `(RingHom.faithfullyFlat_iff f).2 ⟨hsmooth.flat, hsurjective⟩`, then
     get `IsNoetherianRing R` by the theorem above and the Noetherian conjunct
     of `hS`.
  2. Use
     `Unit162.nagata_iff_universallyJapanese_noetherian`; it remains to prove
     universal Japaneseness.  Apply
     `Unit162.universallyJapanese_of_NOne_finiteType`, fix a finite-type map
     `a : R →+* A` with `A` a domain, and aim at `Unit161.IsNOne A`.
  3. Put `B := A ⊗[R] S`.  The map `A → B` is the smooth base change of
     `f` (`Algebra.Smooth.baseChange` in
     `Mathlib/RingTheory/Smooth/Basic.lean`) and is faithfully flat because
     base change preserves faithful flatness.  The map `S → B` is finite
     type because it is the base change of `a`.  Therefore
     `Unit162.nagata_iff_finiteType_algebras_nagata` applied to `hS` makes
     `B` Nagata.  Also obtain `IsReduced B` from
     `Unit163.reduced_goes_up` applied to the smooth map `A → B` and the
     domain `A`.
  4. Let `C := integralClosure B (totalQuotientRing B)`.  Apply
     `Unit162.integralClosure_finite_of_nagata_essFiniteType_reduced` to
     `B → totalQuotientRing B`; its essential-finite-type hypothesis is
     `Algebra.EssFiniteType.of_isLocalization`.  This gives
     `Module.Finite B C`.
  5. Let `D := integralClosure A (FractionRing A)`.  Lift `A → B` to a map
     `FractionRing A → totalQuotientRing B` using `IsLocalization.lift`:
     flatness sends every nonzero element of the domain `A` to a
     nonzerodivisor of `B`, hence to a unit in the total quotient ring.
     Restrict the lift to an algebra map `D → C` using `IsIntegral.map`.
     Its base change is a `B`-linear map `B ⊗[A] D → C`; prove it injective
     by the injection into total quotient rings and
     `Module.Flat.lTensor_preserves_injective_linearMap`.
  6. Since `B` is Noetherian and `C` is finite, apply
     `Module.Finite.of_injective` to make `B ⊗[A] D` finite over `B`.
     Finally descend this finiteness through the faithfully flat map `A → B`
     with `Module.Finite.of_finite_tensorProduct_of_faithfullyFlat` from
     `Mathlib/RingTheory/Finiteness/Descent.lean`.  The resulting
     `Module.Finite A D` is exactly `Unit161.IsNOne A`; assemble the canonical
     Nagata equivalence from steps 1–2.
  -/
  sorry

/-! ## The universally catenary counterexample -/

/- The final source remark is an existence construction.  This structure
  records its rings, all ring maps, the finite/formally-unramified map,
  semilocal and local data, the residue-field identifications, the tensor
  product decomposition, the two minimal primes and quotient identifications,
  and the contrasting catenarity conclusions. -/
structure UniversallyCatenaryDescentCounterexample where
  A : Type u
  B : Type u
  A' : Type u
  B₁ : Type u
  B₂ : Type u
  [commRingA : CommRing A]
  [commRingB : CommRing B]
  [commRingA' : CommRing A']
  [commRingB₁ : CommRing B₁]
  [commRingB₂ : CommRing B₂]
  [localA : IsLocalRing A]
  [localA' : IsLocalRing A']
  f : A →+* B
  finite : RingHom.Finite f
  formallyUnramified : RingHom.FormallyUnramified f
  noetherianA : IsNoetherianRing A
  notUniversallyCatenaryA :
    ¬ Formalization.Books.Algebra.Unit105.IsUniversallyCatenary.{u} A
  m : PrimeSpectrum B
  n : PrimeSpectrum B
  m_maximal : m.asIdeal.IsMaximal
  n_maximal : n.asIdeal.IsMaximal
  distinct_maximals : m ≠ n
  semilocal : ∀ q : PrimeSpectrum B, q.asIdeal.IsMaximal → q = m ∨ q = n
  m_regular : IsRegularLocalRing (Localization.AtPrime m.asIdeal)
  m_dimension : ringKrullDim (Localization.AtPrime m.asIdeal) = 2
  n_regular : IsRegularLocalRing (Localization.AtPrime n.asIdeal)
  n_dimension : ringKrullDim (Localization.AtPrime n.asIdeal) = 1
  m_residueField :
    letI : m.asIdeal.IsMaximal := m_maximal
    Nonempty (m.asIdeal.ResidueField ≃+* IsLocalRing.ResidueField A)
  n_residueField :
    letI : n.asIdeal.IsMaximal := n_maximal
    Nonempty (n.asIdeal.ResidueField ≃+* IsLocalRing.ResidueField A)
  m_maximalIdeal_generates :
    Ideal.map (mapToPrimeLocalization f m) (IsLocalRing.maximalIdeal A) =
      IsLocalRing.maximalIdeal (Localization.AtPrime m.asIdeal)
  n_maximalIdeal_generates :
    Ideal.map (mapToPrimeLocalization f n) (IsLocalRing.maximalIdeal A) =
      IsLocalRing.maximalIdeal (Localization.AtPrime n.asIdeal)
  baseChange : A →+* A'
  baseChange_local : IsLocalHom baseChange
  baseChange_etale : RingHom.Etale baseChange
  factorMap₁ : A' →+* B₁
  factorMap₂ : A' →+* B₂
  factorMap₁_surjective : Function.Surjective factorMap₁
  factorMap₂_surjective : Function.Surjective factorMap₂
  tensorProduct_factors :
    letI : Algebra A B := f.toAlgebra
    letI : Algebra A A' := baseChange.toAlgebra
    ∃ e : B ⊗[A] A' ≃+* B₁ × B₂,
      factorMap₁ =
        (RingHom.fst B₁ B₂).comp
          (e.toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom) ∧
      factorMap₂ =
        (RingHom.snd B₁ B₂).comp
          (e.toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom)
  B₁_regular : IsRegularLocalRing B₁
  B₂_regular : IsRegularLocalRing B₂
  q₁ : Ideal A'
  q₂ : Ideal A'
  q₁_minimal : q₁ ∈ minimalPrimes A'
  q₂_minimal : q₂ ∈ minimalPrimes A'
  distinct_minimal_primes : q₁ ≠ q₂
  exactly_two_minimal_primes :
    ∀ q : Ideal A', q ∈ minimalPrimes A' → q = q₁ ∨ q = q₂
  quotient₁ :
    letI : q₁.IsPrime := q₁_minimal.isPrime
    ∃ e : (A' ⧸ q₁) ≃+* B₁,
      e.toRingHom.comp (Ideal.Quotient.mk q₁) = factorMap₁
  quotient₂ :
    letI : q₂.IsPrime := q₂_minimal.isPrime
    ∃ e : (A' ⧸ q₂) ≃+* B₂,
      e.toRingHom.comp (Ideal.Quotient.mk q₂) = factorMap₂
  universallyCatenaryA' :
    Formalization.Books.Algebra.Unit105.IsUniversallyCatenary.{u} A'

attribute [instance] UniversallyCatenaryDescentCounterexample.commRingA
  UniversallyCatenaryDescentCounterexample.commRingB
  UniversallyCatenaryDescentCounterexample.commRingA'
  UniversallyCatenaryDescentCounterexample.commRingB₁
  UniversallyCatenaryDescentCounterexample.commRingB₂
  UniversallyCatenaryDescentCounterexample.localA
  UniversallyCatenaryDescentCounterexample.localA'

/- Universal catenarity therefore fails to descend even though the displayed
  base-change map is local and étale. -/
theorem exists_universallyCatenary_descent_counterexample :
    Nonempty (UniversallyCatenaryDescentCounterexample.{u}) := by
  /-
  Proof roadmap / dependency boundary:
  1. The intended raw rings are the `A d` and `B d` construction in
     `Formalization/Books/Examples/Unit19/NonCatenary.lean`, with the two
     maximal ideals `mBIdeal d`, `nBIdeal d`.  That file already exposes
     `b_finite_over_a`, `a_isNoetherian`, `a_isLocal`, `b_maximal_ideals`,
     `b_localization_m_properties`, `b_localization_n_properties`, and
     `a_not_universally_catenary` (swap the labels so the dimensions match
     the `m_dimension = 2`, `n_dimension = 1` fields here).
  2. Package the inclusion `A d → B d` as `f`.  The still-needed raw
     construction lemmas are: existence of a `PowerSeriesData k`; formal
     unramifiedness of this inclusion; equality between the image of the
     maximal ideal of `A d` and the maximal ideals after both localizations;
     and residue-field equivalences with `IsLocalRing.ResidueField (A d)`.
     None of these four results is currently exported by Examples Unit19.
  3. Given that package, apply
     `Unit152.lemma_etale_makes_unramified_closed` from
     `Formalization/Books/Algebra/Unit152/LocalStructureUnramifiedRingMaps.lean`
     at the closed point of `A`, then localize its étale neighborhood at
     `p'`.  Eliminate the complementary factor using `noPrimeOver`, identify
     the two closed factors with `B₁` and `B₂`, and use the two-point
     description `b_maximal_ideals` to prove that precisely two factors
     remain.  The current `EtaleSeparatedUnramifiedData` interface does not
     expose the required exhaustive correspondence between its `Fin n`
     factors and the primes in the fibre, so that correspondence is also an
     upstream interface requirement.
  4. The surjective factor maps identify their kernels with the two minimal
     primes `q₁`, `q₂`; use `RingHom.quotientKerEquivOfSurjective` for the
     quotient equivalences.  Once the quotient rings are the regular local
     rings `B₁`, `B₂`, prove universal catenarity of `A'` with
     `Unit105.isUniversallyCatenary_iff_quotient_minimalPrime` and the earlier
     regular-local/Cohen–Macaulay-to-universally-catenary API.

  This declaration is intentionally left for the normal stage, but it cannot
  be completed from the chronological imports alone until the raw Examples
  construction and the exhaustive Chapter 152 factor interface above are
  promoted to an earlier shared module.  Importing Examples Unit19 here would
  be a forbidden dependency on a later book.
  -/
  sorry

end

end Formalization.Books.Algebra.Unit164
