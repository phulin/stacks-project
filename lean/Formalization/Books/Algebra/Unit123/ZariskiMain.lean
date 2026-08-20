import Formalization.Books.Algebra.Unit122.QuasiFinite
import Mathlib.RingTheory.ZariskisMainTheorem
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.LocalProperties.Exactness
import Mathlib.Topology.Maps.Basic
import Mathlib.Topology.IsLocalHomeomorph

/-!
# Commutative Algebra, Chapter 123: Zariski's Main Theorem

The chapter uses Mathlib's canonical `IsIntegral`, `integralClosure`,
`conductor`, `IsStronglyTranscendental`, `Algebra.QuasiFiniteAt`, and
`Algebra.ZariskisMainProperty` declarations.  The declarations below retain
the order and interfaces of the source while exposing the corresponding
Mathlib constructions in a chapter namespace.
-/

namespace Formalization.Books.Algebra.Unit123

open Set
open Polynomial

universe u v

noncomputable section

/-! ## The first integral-element lemmas -/

/- The source's coefficient relation is represented by evaluation of a
   polynomial.  `isIntegral_leadingCoeff_smul` is exactly the determinant-trick
   statement used in the source proof. -/
theorem make_integral_trivial
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (p : R[X]) (t : S) (hp : aeval t p = 0) :
    IsIntegral R (p.leadingCoeff • t) := by
  exact isIntegral_leadingCoeff_smul p t hp

/- The Euclidean-division step in the source is Mathlib's integral-subtraction
   interface for a monic polynomial. -/
theorem make_integral_trick
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (φ : R[X] →ₐ[R] S) (t : S) (ht : φ.IsIntegralElem t)
    (p : R[X]) (hp : p.Monic) (hpt : φ p * t ∈ φ.range) :
    ∃ q : R[X], IsIntegral R (t - φ q) := by
  exact exists_isIntegral_sub_of_isIntegralElem_of_mul_mem_range φ t p ht hp hpt

/- The leading coefficient and denominator-clearing conclusion is retained in
   the scalar form used by the canonical Mathlib theorem. -/
theorem combine_lemmas
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (φ : R[X] →ₐ[R] S) (t : S) (ht : φ.IsIntegralElem t)
    (p : R[X]) (hpt : φ p * t ∈ φ.range) :
    ∃ q : R[X], ∃ n : ℕ,
      IsIntegral R (p.leadingCoeff ^ n • t - φ q) := by
  exact exists_isIntegral_leadingCoeff_pow_smul_sub_of_isIntegralElem_of_mul_mem_range
    φ t p ht hpt

/-! ## The one-transcendental-element situation -/

/- `integralClosure R S = ⊥` records that the image of `R` in `S` is
   integrally closed, without adding an injectivity assumption. -/
structure OneTranscendentalElementSituation
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] where
  φ : R[X] →ₐ[R] S
  finite : RingHom.Finite φ.toRingHom
  integralClosure_eq_bot : integralClosure R S = ⊥

/- Mathlib's conductor of `R[φ(X)]` is the source's ideal
   `J = {g | gS ⊆ Im(φ)}`. -/
def conductorIdeal
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (H : OneTranscendentalElementSituation R S) : Ideal S :=
  conductor R (H.φ X)

theorem leading_coefficient_in_conductor
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (H : OneTranscendentalElementSituation R S) (u : S) (p : R[X])
    (hp : H.φ p * u ∈ conductorIdeal H) :
    ∃ n : ℕ, p.leadingCoeff ^ n • u ∈ conductorIdeal H := by
  simpa [conductorIdeal, mul_comm] using
    (exists_leadingCoeff_pow_smul_mem_conductor H.φ u p
      H.integralClosure_eq_bot H.finite hp)

theorem all_coefficients_in_radical_conductor
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (H : OneTranscendentalElementSituation R S) (u : S) (p : R[X])
    (hp : H.φ p * u ∈ (conductorIdeal H).radical) :
    ∀ i : ℕ, p.coeff i • u ∈ (conductorIdeal H).radical := by
  simpa [conductorIdeal, mul_comm] using
    (exists_leadingCoeff_pow_smul_mem_radical_conductor H.φ u p
      H.integralClosure_eq_bot H.finite hp)

/-! ## Strong transcendence -/

/- The source definition is Mathlib's `IsStronglyTranscendental`; no parallel
   predicate is introduced. -/
theorem strongly_transcendental_iff_fraction_ring
    {R S K : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [Field K] [Algebra S K] [Algebra R K] [IsFractionRing S K]
    [IsScalarTower R S K] [FaithfulSMul R S] (x : S) :
    IsStronglyTranscendental R x ↔
      Transcendental R (algebraMap S K x) := by
  exact IsStronglyTranscendental.iff_of_isFractionRing K

theorem strongly_transcendental_iff_fraction_fields
    {R S K L : Type u} [CommRing R] [CommRing S] [IsDomain R] [IsDomain S]
    [Algebra R S] [FaithfulSMul R S]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [Field L] [Algebra S L] [IsFractionRing S L]
    [Algebra R L] [Algebra K L] [IsScalarTower R S L]
    [IsScalarTower R K L] [FaithfulSMul K L] (x : S) :
    IsStronglyTranscendental R x ↔
      Transcendental K (algebraMap S L x) := by
  exact
    (IsStronglyTranscendental.iff_of_isLocalization (R := R) (S := S) (T := L)
      (M := nonZeroDivisors S) le_rfl).symm.trans
      ((⟨fun h => IsStronglyTranscendental.of_isLocalization_left
          (M := nonZeroDivisors R) h,
        fun h => IsStronglyTranscendental.restrictScalars h⟩ :
        IsStronglyTranscendental R (algebraMap S L x) ↔
          IsStronglyTranscendental K (algebraMap S L x)).trans
        (isStronglyTranscendental_iff_of_field (R := K) (K := L)))

/- The quotient-base formulation is kept explicit because the source contracts
   `R` to `R / (R ∩ q)` at a minimal prime. -/
theorem reduced_strongly_transcendental_minimal_prime
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [IsReduced R] [IsReduced S]
    (x : S) (hx : IsStronglyTranscendental R x)
    (q : Ideal S) (hq : q ∈ minimalPrimes S) :
    IsStronglyTranscendental (R ⧸ q.under R)
      (Ideal.Quotient.mk q x) := by
  exact IsStronglyTranscendental.of_surjective_left
    (isStronglyTranscendental_mk_of_mem_minimalPrimes hx q hq)
    Ideal.Quotient.mk_surjective

/- In the domain case, the source's “finite over `R[x]`” hypothesis is the
   canonical finiteness of the evaluation map `R[X] → S`. -/
theorem domains_transcendental_not_quasi_finite
    {R S : Type u} [CommRing R] [CommRing S] [IsDomain R] [IsDomain S]
    [Algebra R S] [FaithfulSMul R S]
    (x : S) (hx : IsStronglyTranscendental R x)
    (hfinite : (aeval (R := R) x).toRingHom.Finite)
    (q : Ideal S) [q.IsPrime] :
    ¬ Algebra.QuasiFiniteAt R q := by
  intro hq
  exact (Algebra.not_isStronglyTranscendental_of_quasiFiniteAt hfinite q) hx

theorem reduced_strongly_transcendental_not_quasi_finite
    {R S : Type u} [CommRing R] [CommRing S] [IsReduced R] [IsReduced S]
    [Algebra R S]
    (x : S) (hx : IsStronglyTranscendental R x)
    (hfinite : (aeval (R := R) x).toRingHom.Finite)
    (q : Ideal S) [q.IsPrime] :
    ¬ Algebra.QuasiFiniteAt R q := by
  intro hq
  exact (Algebra.not_isStronglyTranscendental_of_quasiFiniteAt hfinite q) hx

/-! ## The monogenic case and Zariski's Main Theorem -/

/- The integral closure is represented by Mathlib's `integralClosure`, and the
   isomorphism of localizations is represented by bijectivity of its canonical
   localization map. -/
theorem quasi_finite_monogenic
    {R : Type u} [CommRing R] (I : Ideal R[X])
    (q : PrimeSpectrum (R[X] ⧸ I))
    [Algebra.QuasiFiniteAt R q.asIdeal] :
    ∃ g : integralClosure R (R[X] ⧸ I),
      g.1 ∉ q.asIdeal ∧
        Function.Bijective
          (Localization.awayMap (integralClosure R (R[X] ⧸ I)).val.toRingHom g) := by
  exact Algebra.ZariskisMainProperty.of_finiteType q.asIdeal

theorem zariskis_main_theorem
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.FiniteType R S] (q : PrimeSpectrum S)
    [Algebra.QuasiFiniteAt R q.asIdeal] :
    ∃ g : integralClosure R S, g.1 ∉ q.asIdeal ∧
      Function.Bijective
        (Localization.awayMap (integralClosure R S).val.toRingHom g) := by
  exact Algebra.ZariskisMainProperty.of_finiteType q.asIdeal

/-! ## Openness of the quasi-finite locus -/

def quasiFiniteLocus
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] :
    Set (PrimeSpectrum S) :=
  {q | Algebra.QuasiFiniteAt R q.asIdeal}

theorem isOpen_quasiFiniteLocus
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.FiniteType R S] :
    IsOpen (quasiFiniteLocus R S) := by
  exact (isOpen_iff_forall_mem_open (s := quasiFiniteLocus R S)).mpr
    (fun (q : PrimeSpectrum S) hq => by
      let hqfin : Algebra.QuasiFiniteAt R q.asIdeal := by
        simpa [quasiFiniteLocus] using hq
      obtain ⟨g, hg, H⟩ :=
        @Algebra.ZariskisMainProperty.of_finiteType R S _ _ _ _ q.asIdeal inferInstance hqfin
      refine ⟨PrimeSpectrum.basicOpen g.1, ?_, PrimeSpectrum.isOpen_basicOpen, ?_⟩
      · intro q' hq'
        apply Algebra.ZariskisMainProperty.quasiFiniteAt q'.asIdeal
        exact ⟨g, (PrimeSpectrum.mem_basicOpen g.1 q').mp hq', H⟩
      · exact (PrimeSpectrum.mem_basicOpen g.1 q).mpr hg)

/-! ## The quasi-finite integral-closure refinement -/

private lemma basicOpen_domRestrict_comap_isOpenEmbedding_of_awayMap_bijective
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] (g : A)
    (H : Function.Bijective (Localization.awayMap (algebraMap A B) g)) :
    Topology.IsOpenEmbedding
      (Set.domRestrict (PrimeSpectrum.basicOpen (algebraMap A B g))
        (PrimeSpectrum.comap (algebraMap A B))) := by
  let e : Localization.Away g ≃+* Localization.Away (algebraMap A B g) :=
    RingEquiv.ofBijective (Localization.awayMap (algebraMap A B) g) H
  let lB := PrimeSpectrum.localization_away_isOpenEmbedding
    (Localization.Away (algebraMap A B g)) (algebraMap A B g)
  have hpre :
      (PrimeSpectrum.comap (algebraMap B (Localization.Away (algebraMap A B g))) ⁻¹'
        (PrimeSpectrum.basicOpen (algebraMap A B g) : Set (PrimeSpectrum B))) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro q
    rw [← PrimeSpectrum.localization_away_comap_range
      (Localization.Away (algebraMap A B g)) (algebraMap A B g)]
    exact ⟨q, rfl⟩
  have hB0range :
      (PrimeSpectrum.basicOpen (algebraMap A B g) : Set (PrimeSpectrum B)) ⊆
        Set.range (PrimeSpectrum.comap
          (algebraMap B (Localization.Away (algebraMap A B g)))) := by
    rw [PrimeSpectrum.localization_away_comap_range
      (Localization.Away (algebraMap A B g)) (algebraMap A B g)]
  let hB0 := lB.isEmbedding.homeomorphOfSubsetRange
    (s := (PrimeSpectrum.basicOpen (algebraMap A B g) : Set (PrimeSpectrum B))) hB0range
  let hB : PrimeSpectrum (Localization.Away (algebraMap A B g)) ≃ₜ
      (PrimeSpectrum.basicOpen (algebraMap A B g) : Set (PrimeSpectrum B)) :=
    (Homeomorph.Set.univ _).symm.trans
      ((Homeomorph.setCongr hpre.symm).trans hB0)
  let hE : PrimeSpectrum (Localization.Away (algebraMap A B g)) ≃ₜ
      PrimeSpectrum (Localization.Away g) :=
    (PrimeSpectrum.homeomorphOfRingEquiv e).symm
  let k : PrimeSpectrum (Localization.Away (algebraMap A B g)) →
      PrimeSpectrum A :=
    PrimeSpectrum.comap (algebraMap A (Localization.Away g)) ∘ hE
  have hk : Topology.IsOpenEmbedding k :=
    (PrimeSpectrum.localization_away_isOpenEmbedding (Localization.Away g) g).comp
      hE.isOpenEmbedding
  let f : (PrimeSpectrum.basicOpen (algebraMap A B g) : Set (PrimeSpectrum B)) →
      PrimeSpectrum A :=
    Set.domRestrict (PrimeSpectrum.basicOpen (algebraMap A B g))
      (PrimeSpectrum.comap (algebraMap A B))
  have hcomp : f ∘ hB = k := by
    funext q
    apply PrimeSpectrum.ext
    ext a
    have hBq : (hB q : PrimeSpectrum B) =
        PrimeSpectrum.comap (algebraMap B
          (Localization.Away (algebraMap A B g))) q := by
      let z := (Homeomorph.setCongr hpre.symm)
        ((Homeomorph.Set.univ _).symm q)
      change (hB0 z : PrimeSpectrum B) =
        PrimeSpectrum.comap (algebraMap B
          (Localization.Away (algebraMap A B g))) q
      rw [Topology.IsEmbedding.homeomorphOfSubsetRange_apply_coe
        lB.isEmbedding hB0range z]
      rfl
    change algebraMap A B a ∈ ((hB q : PrimeSpectrum B).asIdeal) ↔
      e (algebraMap A (Localization.Away g) a) ∈ q.asIdeal
    rw [show e (algebraMap A (Localization.Away g) a) =
        algebraMap B (Localization.Away (algebraMap A B g)) (algebraMap A B a) by
      simp [e, Localization.awayMap, IsLocalization.Away.map,
        IsLocalization.map_eq]]
    rw [hBq]
    rfl
  have hf : Topology.IsOpenEmbedding f := by
    rw [show f = k ∘ hB.symm by
      rw [← hcomp]
      ext q
      simp]
    exact hk.comp hB.symm.isOpenEmbedding
  exact hf

private lemma isOpenEmbedding_comap_of_local_awayMap_bijective
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (h : ∀ q : PrimeSpectrum B, ∃ g : A, algebraMap A B g ∉ q.asIdeal ∧
      Function.Bijective (Localization.awayMap (algebraMap A B) g)) :
    Topology.IsOpenEmbedding (PrimeSpectrum.comap (algebraMap A B)) := by
  let f := PrimeSpectrum.comap (algebraMap A B)
  have hl : IsLocalHomeomorph f :=
    (isLocalHomeomorph_iff_isOpenEmbedding_restrict).mpr fun q => by
      obtain ⟨g, hg, H⟩ := h q
      refine ⟨PrimeSpectrum.basicOpen (algebraMap A B g), ?_, ?_⟩
      · exact PrimeSpectrum.isOpen_basicOpen.mem_nhds
          ((PrimeSpectrum.mem_basicOpen (algebraMap A B g) q).mpr hg)
      · exact basicOpen_domRestrict_comap_isOpenEmbedding_of_awayMap_bijective g H
  apply hl.isOpenEmbedding_of_injective
  intro q₁ q₂ hq
  obtain ⟨g, hg, H⟩ := h q₁
  have hq₁' : q₁ ∈ PrimeSpectrum.basicOpen (algebraMap A B g) :=
    (PrimeSpectrum.mem_basicOpen (algebraMap A B g) q₁).mpr hg
  have hq₂' : q₂ ∈ PrimeSpectrum.basicOpen (algebraMap A B g) := by
    have hq₁'' : f q₁ ∈ PrimeSpectrum.basicOpen g := by
      simpa [f, PrimeSpectrum.mem_basicOpen, PrimeSpectrum.comap_asIdeal] using hq₁'
    have hq₂'' : f q₂ ∈ PrimeSpectrum.basicOpen g := by
      rw [← hq]
      exact hq₁''
    simpa [f, PrimeSpectrum.mem_basicOpen, PrimeSpectrum.comap_asIdeal] using hq₂''
  have hsub :
      (⟨q₁, hq₁'⟩ : PrimeSpectrum.basicOpen (algebraMap A B g)) =
        ⟨q₂, hq₂'⟩ := by
    apply (basicOpen_domRestrict_comap_isOpenEmbedding_of_awayMap_bijective g H).injective
    change f q₁ = f q₂
    exact hq
  exact congrArg Subtype.val hsub

private lemma localized_awayMap_bijective_of_awayMap_bijective
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (hinj : Function.Injective (algebraMap A B)) (g a : A)
    (H : Function.Bijective (Localization.awayMap (algebraMap A B) a)) :
    Function.Bijective
      (Localization.awayMap (Localization.awayMap (algebraMap A B) g)
        (algebraMap A (Localization.Away g) a)) := by
  have hga := Localization.awayMap_bijective_of_dvd (algebraMap A B)
    (show a ∣ g * a from ⟨g, by simp [mul_comm]⟩) H
  refine ⟨?_, ?_⟩
  · exact IsLocalization.map_injective_of_injective _ _ _
      (by
        let hloc : IsLocalization
            ((Submonoid.powers g).map (algebraMap A B))
            (Localization.Away (algebraMap A B g)) := by
          rw [Submonoid.map_powers]
          infer_instance
        exact @IsLocalization.map_injective_of_injective
          A _ (.powers g) (Localization.Away g) _ _ B _ _
          (algebraMap A B) (Localization.Away (algebraMap A B g)) _ _ hinj hloc)
  · exact Localization.awayMap_awayMap_surjective (algebraMap A B) g a hga.2

private lemma awayMap_bijective_of_basicOpen_subset_range
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (hinj : Function.Injective (algebraMap A B))
    (hlocal : ∀ q : PrimeSpectrum B, ∃ a : A, algebraMap A B a ∉ q.asIdeal ∧
      Function.Bijective (Localization.awayMap (algebraMap A B) a))
    (g : A)
    (hg : (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum A)) ⊆
      Set.range (PrimeSpectrum.comap (algebraMap A B))) :
    Function.Bijective (Localization.awayMap (algebraMap A B) g) := by
  classical
  let a : PrimeSpectrum B → A := fun q => (hlocal q).choose
  have ha : ∀ q : PrimeSpectrum B, algebraMap A B (a q) ∉ q.asIdeal := by
    intro q
    exact (hlocal q).choose_spec.1
  have hA : ∀ q : PrimeSpectrum B,
      Function.Bijective (Localization.awayMap (algebraMap A B) (a q)) := by
    intro q
    exact (hlocal q).choose_spec.2
  have hcover : (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum A)) ⊆
      ⋃ q : PrimeSpectrum B, PrimeSpectrum.basicOpen (a q) := by
    intro p hp
    obtain ⟨q, hq⟩ := hg hp
    have hq' : PrimeSpectrum.comap (algebraMap A B) q ∈
        PrimeSpectrum.basicOpen (a q) := by
      simpa [PrimeSpectrum.mem_basicOpen, PrimeSpectrum.comap_asIdeal] using
        (PrimeSpectrum.mem_basicOpen (algebraMap A B (a q)) q).mpr (ha q)
    rw [hq] at hq'
    exact Set.mem_iUnion.mpr ⟨q, hq'⟩
  obtain ⟨t, ht⟩ := (PrimeSpectrum.isCompact_basicOpen g).elim_finite_subcover
    (fun q : PrimeSpectrum B => PrimeSpectrum.basicOpen (a q))
    (fun q => PrimeSpectrum.isOpen_basicOpen) hcover
  let A_g := Localization.Away g
  let s : Set A_g := Set.range (fun q : t => algebraMap A A_g (a q))
  have hspan : Ideal.span s = ⊤ := by
    rw [← PrimeSpectrum.iSup_basicOpen_eq_top_iff]
    apply top_unique
    intro p hp
    have hp' : p.comap (algebraMap A A_g) ∈ PrimeSpectrum.basicOpen g := by
      have hp'' : p.comap (algebraMap A A_g) ∈
          Set.range (PrimeSpectrum.comap (algebraMap A A_g)) := ⟨p, rfl⟩
      rw [PrimeSpectrum.localization_away_comap_range A_g g] at hp''
      exact hp''
    obtain ⟨q, hqt, hpq⟩ := Set.mem_iUnion₂.mp (ht hp')
    have hpq' : p ∈ PrimeSpectrum.basicOpen (algebraMap A A_g (a q)) := by
      simpa [PrimeSpectrum.mem_basicOpen, PrimeSpectrum.comap_asIdeal] using hpq
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨q, hqt⟩, hpq'⟩
  let f := Localization.awayMap (algebraMap A B) g
  apply bijective_of_isLocalization_of_span_eq_top hspan
    (fun r : s => Localization.Away r.1)
    (fun r : s => Localization.Away (f r.1)) f
  intro r
  obtain ⟨q, hq⟩ := r.property
  rw [← hq]
  exact localized_awayMap_bijective_of_awayMap_bijective hinj g (a q) (hA q)

theorem quasi_finite_open_integral_closure
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.FiniteType R S] [Algebra.QuasiFinite R S] :
    Topology.IsOpenEmbedding
        (PrimeSpectrum.comap (integralClosure R S).val.toRingHom) ∧
      (∀ g : integralClosure R S,
        (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum (integralClosure R S))) ⊆
            Set.range (PrimeSpectrum.comap (integralClosure R S).val.toRingHom) →
          Function.Bijective
            (Localization.awayMap (integralClosure R S).val.toRingHom g)) ∧
      ∃ S'' : Subalgebra R S,
        S'' ≤ integralClosure R S ∧
          Module.Finite R S'' ∧
            Topology.IsOpenEmbedding (PrimeSpectrum.comap S''.val.toRingHom) ∧
              (∀ g : S'',
                (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum S'')) ⊆
                    Set.range (PrimeSpectrum.comap S''.val.toRingHom) →
                  Function.Bijective (Localization.awayMap S''.val.toRingHom g)) := by
  let A := integralClosure R S
  have hAinj : Function.Injective A.val.toRingHom := Subtype.val_injective
  have hAlocal : ∀ q : PrimeSpectrum S, ∃ g : A, g.1 ∉ q.asIdeal ∧
      Function.Bijective (Localization.awayMap A.val.toRingHom g) := by
    intro q
    let hqfin : Algebra.QuasiFiniteAt R q.asIdeal := inferInstance
    exact @Algebra.ZariskisMainProperty.of_finiteType R S _ _ _ _ q.asIdeal inferInstance hqfin
  have hAopen : Topology.IsOpenEmbedding (PrimeSpectrum.comap A.val.toRingHom) :=
    isOpenEmbedding_comap_of_local_awayMap_bijective (by
      intro q
      obtain ⟨g, hg, H⟩ := hAlocal q
      exact ⟨g, hg, H⟩)
  have hAaway : ∀ g : A,
      (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum A)) ⊆
        Set.range (PrimeSpectrum.comap A.val.toRingHom) →
      Function.Bijective (Localization.awayMap A.val.toRingHom g) := by
    intro g hg
    exact awayMap_bijective_of_basicOpen_subset_range hAinj (by
      intro q
      obtain ⟨a, ha, H⟩ := hAlocal q
      exact ⟨a, ha, H⟩) g hg
  choose T hTfg r hr hT using fun q : PrimeSpectrum S => by
    let hqfin : Algebra.QuasiFiniteAt R q.asIdeal := inferInstance
    have Hq : Algebra.ZariskisMainProperty R q.asIdeal :=
      @Algebra.ZariskisMainProperty.of_finiteType R S _ _ _ _ q.asIdeal inferInstance hqfin
    exact Algebra.ZariskisMainProperty.exists_fg_and_exists_notMem_and_awayMap_bijective
      q.asIdeal Hq
  have hcoverS : (Set.univ : Set (PrimeSpectrum S)) ⊆
      ⋃ q : PrimeSpectrum S, PrimeSpectrum.basicOpen (r q).1 := by
    intro q hq
    exact Set.mem_iUnion.mpr ⟨q, (PrimeSpectrum.mem_basicOpen (r q).1 q).mpr (hr q)⟩
  obtain ⟨t, ht⟩ := (isCompact_univ : IsCompact (Set.univ : Set (PrimeSpectrum S))).elim_finite_subcover
    (fun q : PrimeSpectrum S => PrimeSpectrum.basicOpen (r q).1)
    (fun q => PrimeSpectrum.isOpen_basicOpen) hcoverS
  choose U hUfin hUspan using fun q : t => Submodule.fg_def.mp (hTfg q)
  let V : Set S := ⋃ q : t, U q
  have hVfin : V.Finite := Set.finite_iUnion hUfin
  have hVint : ∀ x ∈ V, IsIntegral R x := by
    intro x hx
    obtain ⟨q, hxq⟩ := Set.mem_iUnion.mp hx
    apply IsIntegral.of_mem_of_fg (T q) (hTfg q) x
    change x ∈ (T q).toSubmodule
    rw [← hUspan q]
    exact Submodule.subset_span hxq
  let S'' : Subalgebra R S := Algebra.adjoin R V
  have hSfin : Module.Finite R S'' :=
    Algebra.finite_adjoin_of_finite_of_isIntegral hVfin hVint
  have hSle : S'' ≤ A :=
    le_integralClosure_iff_isIntegral.mpr (Algebra.IsIntegral.adjoin hVint)
  have hTle : ∀ q : t, T q ≤ S'' := by
    intro q x hx
    have hxspan : x ∈ Submodule.span R (U q) := by
      rw [hUspan q]
      exact hx
    have hle : Submodule.span R (U q) ≤ S''.toSubmodule :=
      Submodule.span_le.2 (fun y hy =>
        Algebra.subset_adjoin (Set.mem_iUnion.mpr ⟨q, hy⟩))
    exact hle hxspan
  have hSlocal : ∀ p : PrimeSpectrum S, ∃ g : S'', g.1 ∉ p.asIdeal ∧
      Function.Bijective (Localization.awayMap S''.val.toRingHom g) := by
    intro p
    obtain ⟨q, hqt, hpq⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ p))
    let j : (T q) →ₐ[R] S'' :=
      Subalgebra.inclusion (hTle ⟨q, hqt⟩)
    let g : S'' := j (r q)
    refine ⟨g, ?_, ?_⟩
    · simpa [g, j] using (PrimeSpectrum.mem_basicOpen (r q).1 p).mp hpq
    · refine ⟨IsLocalization.map_injective_of_injective _ _ _ Subtype.val_injective, ?_⟩
      have hcomp :
          (Localization.awayMap S''.val.toRingHom (j (r q))).comp
              (Localization.awayMap j.toRingHom (r q)) =
            Localization.awayMap (T q).val.toRingHom (r q) := by
        apply IsLocalization.ringHom_ext (.powers (r q))
        ext x
        change (Localization.awayMap S''.val.toRingHom (j (r q)))
            (Localization.awayMap j.toRingHom (r q)
              (algebraMap (T q) (Localization.Away (r q)) x)) =
          Localization.awayMap (T q).val.toRingHom (r q)
            (algebraMap (T q) (Localization.Away (r q)) x)
        simp only [Localization.awayMap, IsLocalization.Away.map]
        simp only [IsLocalization.map_eq]
        exact IsLocalization.map_eq _ _
      intro y
      obtain ⟨x, hx⟩ := (hT q).2 y
      refine ⟨Localization.awayMap j.toRingHom (r q) x, ?_⟩
      change ((Localization.awayMap S''.val.toRingHom (j (r q))).comp
          (Localization.awayMap j.toRingHom (r q))) x = y
      rw [hcomp]
      exact hx
  refine ⟨hAopen, ?_, ⟨S'', hSle, hSfin, ?_, ?_⟩⟩
  · intro g hg
    exact hAaway g hg
  · exact isOpenEmbedding_comap_of_local_awayMap_bijective (by
      intro q
      obtain ⟨g, hg, H⟩ := hSlocal q
      exact ⟨g, hg, H⟩)
  · intro g hg
    exact awayMap_bijective_of_basicOpen_subset_range Subtype.val_injective (by
      intro q
      obtain ⟨a, ha, H⟩ := hSlocal q
      exact ⟨a, ha, H⟩) g hg

end

end Formalization.Books.Algebra.Unit123
