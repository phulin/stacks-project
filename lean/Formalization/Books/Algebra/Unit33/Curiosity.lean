import Mathlib.Algebra.Ring.Prod
import Mathlib.GroupTheory.Finiteness
import Mathlib.RingTheory.Localization.Basic
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.Idempotents
import Mathlib.RingTheory.Spectrum.Prime.Noetherian
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.Topology.NoetherianSpace

/-!
# Commutative Algebra, Chapter 33: Curiosity

The two source lemmas are represented using Mathlib's canonical localization
`Localization`, spectrum map `PrimeSpectrum.comap`, closed-set predicate
`IsClosed`, Noetherian-ring predicate `IsNoetherianRing`, Noetherian-space
predicate `TopologicalSpace.NoetherianSpace`, and finitely generated-submonoid
predicate `Submonoid.FG`.  The quotient statement records that its ideal is the
kernel of the canonical localization map, which is the ideal used by the
subsequent product-decomposition argument.
-/

namespace Formalization.Books.Algebra.Unit33

open scoped BigOperators

universe u

/-! ## Closed images of localization spectra -/

/-- A localization whose spectrum image is closed is a quotient of the base ring. -/
theorem localization_closed_image_quotient
    {R : Type u} [CommRing R] (S : Submonoid R)
    (hclosed :
      IsClosed
        (Set.range (PrimeSpectrum.comap (algebraMap R (Localization S))))) :
    ∃ I : Ideal R,
      I = RingHom.ker (algebraMap R (Localization S)) ∧
        Set.range (PrimeSpectrum.comap (algebraMap R (Localization S))) =
        PrimeSpectrum.zeroLocus (I : Set R) ∧
        Nonempty (Localization S ≃+* R ⧸ I) := by
  classical
  let f : R →+* Localization S := algebraMap R (Localization S)
  let I : Ideal R := RingHom.ker f
  have hrange : Set.range (PrimeSpectrum.comap f) =
      PrimeSpectrum.zeroLocus (I : Set R) := by
    calc
      Set.range (PrimeSpectrum.comap f) =
          closure (Set.range (PrimeSpectrum.comap f)) := hclosed.closure_eq.symm
      _ = PrimeSpectrum.zeroLocus (I : Set R) := by
        simpa [I] using PrimeSpectrum.closure_range_comap f
  have hunit : ∀ s : S, IsUnit (Ideal.Quotient.mk I (s : R)) := by
    intro s
    by_contra hs
    obtain ⟨M, hM, hsM⟩ :=
      exists_max_ideal_of_mem_nonunits (mem_nonunits_iff.mpr hs)
    let p : PrimeSpectrum R :=
      PrimeSpectrum.comap (Ideal.Quotient.mk I) ⟨M, hM.isPrime⟩
    have hpI : p ∈ PrimeSpectrum.zeroLocus (I : Set R) := by
      rw [PrimeSpectrum.mem_zeroLocus]
      intro x hx
      simp [p, Ideal.Quotient.eq_zero_iff_mem.mpr hx]
    rw [← hrange] at hpI
    obtain ⟨q, hq⟩ := hpI
    have hmem : (s : R) ∈ p.asIdeal := by
      simpa [p] using hsM
    rw [← hq, PrimeSpectrum.comap_asIdeal, Ideal.mem_comap] at hmem
    exact (Ideal.notMem_of_isUnit q.asIdeal
      (IsLocalization.map_units (S := Localization S) s)) hmem
  let g : Localization S →+* R ⧸ I :=
    IsLocalization.lift (M := S) hunit
  let k : R ⧸ I →+* Localization S := RingHom.kerLift f
  have hgcomp : g.comp f = Ideal.Quotient.mk I := by
    simpa [g] using (IsLocalization.lift_comp (M := S) hunit)
  have hkcomp : k.comp (Ideal.Quotient.mk I) = f := by
    ext x
    simp [k, I]
  have hleft : k.comp g = RingHom.id _ := by
    apply IsLocalization.ringHom_ext S
    rw [RingHom.comp_assoc, hgcomp, hkcomp, RingHom.id_comp]
  have hright : g.comp k = RingHom.id _ := by
    apply RingHom.ext
    intro x
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
    simpa [k, I] using RingHom.congr_fun hgcomp r
  refine ⟨I, rfl, ?_, ?_⟩
  · simpa [f] using hrange
  · exact Nonempty.intro (RingEquiv.ofRingHom g k hright hleft)

/-- Under any of the source's finiteness hypotheses, the localization splits off
as a direct product factor of the original ring. -/
theorem localization_closed_image_product
    {R : Type u} [CommRing R] (S : Submonoid R)
    (hclosed :
      IsClosed
        (Set.range (PrimeSpectrum.comap (algebraMap R (Localization S)))))
    (hfinite :
      IsNoetherianRing R ∨
        TopologicalSpace.NoetherianSpace (PrimeSpectrum R) ∨ S.FG) :
    ∃ (R' : Type u) (hR' : CommRing R'),
      letI : CommRing R' := hR'
      Nonempty (R ≃+* (Localization S × R')) := by
  classical
  obtain ⟨I, hI, hV, hIso⟩ := localization_closed_image_quotient S hclosed
  have idem_mem_of_radical {J : Ideal R} {e : R}
      (he : IsIdempotentElem e) (h : e ∈ J.radical) : e ∈ J := by
    obtain ⟨n, hn⟩ := Ideal.mem_radical_iff.mp h
    have hp : ∀ n : ℕ, e ^ (n + 1) = e := by
      intro n
      induction n with
      | zero => simpa using he.eq
      | succ n ih =>
          rw [pow_succ, ih, he.eq]
    cases n with
    | zero =>
        have htop : J = ⊤ := J.eq_top_iff_one.mpr (by simpa using hn)
        rw [htop]
        trivial
    | succ n =>
        simpa [hp n] using hn
  have hcompact_basic
      (hN : TopologicalSpace.NoetherianSpace (PrimeSpectrum R)) :
      ∃ t : Finset I,
        (PrimeSpectrum.zeroLocus (I : Set R))ᶜ =
          ⋃ x ∈ t, PrimeSpectrum.basicOpen (x : R) := by
    have hcover : (PrimeSpectrum.zeroLocus (I : Set R))ᶜ ⊆
        ⋃ x : I, PrimeSpectrum.basicOpen (x : R) := by
      intro p hp
      have hp' : p ∉ PrimeSpectrum.zeroLocus (I : Set R) := by
        simpa only [Set.mem_compl_iff] using hp
      by_contra hc
      apply hp'
      rw [PrimeSpectrum.mem_zeroLocus]
      intro x hx
      by_contra hxp
      exact hc (Set.mem_iUnion.mpr ⟨⟨x, hx⟩,
        (PrimeSpectrum.mem_basicOpen (x : R) p).mpr hxp⟩)
    obtain ⟨t, ht⟩ :=
      (@TopologicalSpace.NoetherianSpace.isCompact (PrimeSpectrum R) inferInstance hN
      (PrimeSpectrum.zeroLocus (I : Set R))ᶜ).elim_finite_subcover
        (fun x : I => PrimeSpectrum.basicOpen (x : R))
        (fun _ => PrimeSpectrum.isOpen_basicOpen) hcover
    refine ⟨t, Set.Subset.antisymm ht ?_⟩
    intro p hp
    rcases Set.mem_iUnion.mp hp with ⟨x, hp⟩
    rcases Set.mem_iUnion.mp hp with ⟨hxt, hpx⟩
    have hpx' : (x : R) ∉ p.asIdeal :=
      (PrimeSpectrum.mem_basicOpen (x : R) p).mp hpx
    intro hpI
    rw [PrimeSpectrum.mem_zeroLocus] at hpI
    exact hpx' (hpI x.property)
  have hfinite_data (t : Finset I)
      (ht : (PrimeSpectrum.zeroLocus (I : Set R))ᶜ =
        ⋃ x ∈ t, PrimeSpectrum.basicOpen (x : R)) :
      ∃ g : R, g ∈ S ∧
        PrimeSpectrum.basicOpen g = PrimeSpectrum.zeroLocus (I : Set R) := by
    have hkill (z : I) : ∃ s : S, (s : R) * (z : R) = 0 := by
      have hzker : (z : R) ∈ RingHom.ker (algebraMap R (Localization S)) := by
        rw [← hI]
        exact z.property
      have hzmk : IsLocalization.mk' (Localization S) (z : R) (1 : S) = 0 := by
        rw [IsLocalization.mk'_one]
        exact hzker
      obtain ⟨s, hs⟩ :=
        (IsLocalization.mk'_eq_zero_iff (S := Localization S) (z : R) (1 : S)).mp
          hzmk
      exact ⟨s, hs⟩
    let d : I → S := fun z => Classical.choose (hkill z)
    have hd (z : I) : (d z : R) * (z : R) = 0 :=
      Classical.choose_spec (hkill z)
    let g : R := ∏ z ∈ t, (d z : R)
    have hg : g ∈ S := by
      dsimp [g]
      exact S.prod_mem (fun z hz => (d z).property)
    have hkill' (z : I) (hz : z ∈ t) : g * (z : R) = 0 := by
      obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem (fun z : I => (d z : R)) hz
      calc
        g * (z : R) = ((d z : R) * c) * (z : R) := by
          change (∏ i ∈ t, (d i : R)) * (z : R) = _
          exact congrArg (fun q : R => q * (z : R)) hc
        _ = c * ((d z : R) * (z : R)) := by ring
        _ = 0 := by rw [hd z, mul_zero]
    refine ⟨g, hg, ?_⟩
    ext p
    constructor
    · intro hpg
      have hpg' : g ∉ p.asIdeal :=
        (PrimeSpectrum.mem_basicOpen g p).mp hpg
      by_contra hpI
      have hpcomp : p ∈ (PrimeSpectrum.zeroLocus (I : Set R))ᶜ := hpI
      rw [ht] at hpcomp
      rcases Set.mem_iUnion.mp hpcomp with ⟨z, hpcomp⟩
      rcases Set.mem_iUnion.mp hpcomp with ⟨hz, hpz⟩
      have hpz' : (z : R) ∉ p.asIdeal :=
        (PrimeSpectrum.mem_basicOpen (z : R) p).mp hpz
      rcases p.2.mem_or_mem_of_mul_eq_zero (hkill' z hz) with hgp | hpz'
      · exact hpg' hgp
      · exact hpz hpz'
    · intro hpI
      apply (PrimeSpectrum.mem_basicOpen g p).mpr
      intro hgp
      have hprange : p ∈ Set.range
          (PrimeSpectrum.comap (algebraMap R (Localization S))) := by
        rw [hV]
        exact hpI
      obtain ⟨q, hq⟩ := hprange
      have hqgp : algebraMap R (Localization S) g ∈ q.asIdeal := by
        rw [← hq, PrimeSpectrum.comap_asIdeal, Ideal.mem_comap] at hgp
        exact hgp
      exact Ideal.notMem_of_isUnit q.asIdeal
        (IsLocalization.map_units (S := Localization S) ⟨g, hg⟩) hqgp
  have hdata : ∃ g : R, g ∈ S ∧
      PrimeSpectrum.basicOpen g = PrimeSpectrum.zeroLocus (I : Set R) := by
    rcases hfinite with h | h | h
    · let _ : IsNoetherianRing R := h
      obtain ⟨t, ht⟩ := hcompact_basic (by infer_instance)
      exact hfinite_data t ht
    · obtain ⟨t, ht⟩ := hcompact_basic h
      exact hfinite_data t ht
    · obtain ⟨t, ht⟩ := h
      let g : R := ∏ z ∈ t, z
      have hg : g ∈ S := by
        rw [← ht]
        exact (Submonoid.closure (↑t : Set R)).prod_mem
          (fun z hz => Submonoid.subset_closure hz)
      refine ⟨g, hg, ?_⟩
      have hbasic_range : PrimeSpectrum.basicOpen g =
          Set.range (PrimeSpectrum.comap (algebraMap R (Localization S))) := by
        ext p
        rw [PrimeSpectrum.localization_comap_range (R := R) (S := Localization S) S]
        constructor
        · intro hpg
          apply Set.disjoint_left.mpr
          intro z hzS hzp
          have hle : S ≤ p.asIdeal.primeCompl := by
            rw [← ht]
            exact Submonoid.closure_le.mpr (fun z hz => by
              intro hzp'
              apply (PrimeSpectrum.mem_basicOpen g p).mp hpg
              apply p.asIdeal.mem_of_dvd _ hzp'
              simpa [g] using (Finset.dvd_prod_of_mem (fun z : R => z) hz))
          exact (hle hzS) hzp
        · intro hdis
          apply (PrimeSpectrum.mem_basicOpen g p).mpr
          intro hgp
          obtain ⟨z, hz, hzp⟩ :=
            p.2.prod_mem_iff_exists_mem t |>.mp hgp
          have hzS : z ∈ S := by
            rw [← ht]
            exact Submonoid.subset_closure (by simpa using hz)
          exact (Set.disjoint_left.mp hdis hzS) hzp
      exact hbasic_range.trans hV
  obtain ⟨g, hg, hbasic⟩ := hdata
  have hclopen : IsClopen (PrimeSpectrum.zeroLocus (I : Set R)) :=
    ⟨PrimeSpectrum.isClosed_zeroLocus _, by
      rw [← hbasic]
      exact PrimeSpectrum.isOpen_basicOpen⟩
  obtain ⟨x, y, hxy, hxy1, hx, hy⟩ :=
    PrimeSpectrum.exists_mul_eq_zero_add_eq_one_basicOpen_eq_of_isClopen hclopen
  have hxidem : IsIdempotentElem x := (IsIdempotentElem.of_mul_add hxy hxy1).1
  have hyidem : IsIdempotentElem y := (IsIdempotentElem.of_mul_add hxy hxy1).2
  have hxg_rad : x ∈ (Ideal.span ({g} : Set R)).radical := by
    apply (PrimeSpectrum.basicOpen_le_basicOpen_iff x g).mp
    rw [← SetLike.coe_subset_coe, ← hx, ← hbasic]
  have hxg : x ∈ Ideal.span ({g} : Set R) := idem_mem_of_radical hxidem hxg_rad
  obtain ⟨a, hax⟩ := Ideal.mem_span_singleton'.mp hxg
  have hzero : PrimeSpectrum.zeroLocus (I : Set R) =
      PrimeSpectrum.zeroLocus (Ideal.span ({y} : Set R) : Set R) := by
    rw [PrimeSpectrum.zeroLocus_span]
    rw [hx, PrimeSpectrum.zeroLocus_eq_basicOpen_of_mul_add y x]
    · exact by simpa [mul_comm] using hxy
    · simpa [add_comm] using hxy1
  have hyrad : y ∈ I.radical := by
    rw [PrimeSpectrum.zeroLocus_eq_iff] at hzero
    rw [hzero]
    exact Ideal.le_radical (Ideal.mem_span_singleton_self y)
  have hyI : y ∈ I := idem_mem_of_radical hyidem hyrad
  have hIspan : I = Ideal.span ({y} : Set R) := by
    apply le_antisymm
    · intro r hr
      have hker : r ∈ RingHom.ker (algebraMap R (Localization S)) := by
        rw [← hI]
        exact hr
      have hrmk : IsLocalization.mk' (Localization S) r (1 : S) = 0 := by
        rw [IsLocalization.mk'_one]
        exact hker
      obtain ⟨s, hsr⟩ :=
        (IsLocalization.mk'_eq_zero_iff (S := Localization S) r (1 : S)).mp
          hrmk
      have hxs : x ∈ Ideal.span ({(s : R)} : Set R) := by
        apply idem_mem_of_radical hxidem
        apply (PrimeSpectrum.basicOpen_le_basicOpen_iff x (s : R)).mp
        intro p hp
        have hpI : p ∈ PrimeSpectrum.zeroLocus (I : Set R) := by
          rw [hx]
          exact hp
        rw [PrimeSpectrum.mem_basicOpen]
        intro hsp
        have hprange : p ∈ Set.range
            (PrimeSpectrum.comap (algebraMap R (Localization S))) := by
          rw [hV]
          exact hpI
        obtain ⟨q, hq⟩ := hprange
        have hqsp : algebraMap R (Localization S) (s : R) ∈ q.asIdeal := by
          rw [← hq, PrimeSpectrum.comap_asIdeal, Ideal.mem_comap] at hsp
          exact hsp
        exact Ideal.notMem_of_isUnit q.asIdeal
          (IsLocalization.map_units (S := Localization S) s) hqsp
      obtain ⟨b, hbx⟩ := Ideal.mem_span_singleton'.mp hxs
      have hxr : x * r = 0 := by
        rw [← hbx, mul_assoc, hsr, mul_zero]
      have hre : y * r = r := by
        calc
          y * r = (x + y) * r := by rw [add_mul, hxr, zero_add]
          _ = r := by rw [hxy1, one_mul]
      exact Ideal.mem_span_singleton'.mpr ⟨r, by simpa [mul_comm] using hre⟩
    · exact Ideal.span_le.mpr (by
        intro z hz
        rw [Set.mem_singleton_iff] at hz
        simpa [hz] using hyI)
  obtain ⟨e⟩ := hIso
  have hquot : R ⧸ Ideal.span ({y} : Set R) ≃+* Localization S := by
    rw [← hIspan]
    exact e.symm
  let R' := R ⧸ Ideal.span ({x} : Set R)
  refine ⟨R', inferInstance, ?_⟩
  let E := AlgEquiv.prodQuotientOfIsIdempotentElem R hyidem hxidem
    (by simpa [add_comm] using hxy1) (by simpa [mul_comm] using hxy)
  exact ⟨E.toRingEquiv.trans (RingEquiv.prodCongr hquot (RingEquiv.refl _))⟩

end Formalization.Books.Algebra.Unit33
