import Formalization.Books.Algebra.Unit29.ImagesOfFinitePresentation
import Mathlib.RingTheory.Algebraic.Basic
import Mathlib.RingTheory.Localization.FractionRing

/-!
# Commutative Algebra, Chapter 30: More on images

The source's spectrum maps are represented by Mathlib's canonical
`PrimeSpectrum.comap`.  Ideals, radicals, minimal primes, constructible sets,
finite type and finite presentation use the corresponding canonical Mathlib
interfaces.  The only source-facing construction below is the localization
map needed to write the generic finite-presentation statement with explicit
denominators.
-/

namespace Formalization.Books.Algebra.Unit30

open Set
open _root_.Topology
open scoped TensorProduct

/-! ## Generic finite presentation and constructible images -/

/- The map in the first lemma is the canonical map
`R_f → S_{φ(f)g}`.  It is obtained by the universal property of localization;
the image of `f` is invertible because it divides `φ(f) * g`. -/
noncomputable def localizationAwayMulMap
    {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (f : R) (g : S) :
    Localization.Away f →+* Localization.Away (φ f * g) :=
  Localization.awayLift
    ((algebraMap S (Localization.Away (φ f * g))).comp φ) f
    (by
      change IsUnit (algebraMap S (Localization.Away (φ f * g)) (φ f))
      exact IsLocalization.Away.isUnit_of_dvd
        (S := Localization.Away (φ f * g))
        (x := φ f * g) (r := φ f) (dvd_mul_right (φ f) g))

/-- A finite-type inclusion of domains becomes finitely presented after
localizing the source and target at suitable nonzero elements. -/
theorem exists_localization_away_finitePresentation
    {R S : Type*} [CommRing R] [CommRing S] [IsDomain R] [IsDomain S]
    (φ : R →+* S) (hφ : Function.Injective φ)
    (hft : RingHom.FiniteType φ) :
    ∃ f : R, f ≠ 0 ∧ ∃ g : S, g ≠ 0 ∧
      RingHom.FinitePresentation (localizationAwayMulMap φ f g) := by
  sorry

/- The quotient/localization square in the source proof is proof scaffolding:
the canonical quotient spectra and `PrimeSpectrum.comap` already provide its
four arrows.  The theorem below records the resulting relative open-dense
statement directly. -/
/- The displayed polynomial relation in the source's proof of the last lemma
is likewise an argument for the theorem, not an additional chapter-level
interface. -/

/- A constructible image of a finite-type map contains a relatively open dense
subset of the closure of every point it contains. -/
theorem image_constructible_contains_open_dense_subset_of_finiteType
    {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (hφ : RingHom.FiniteType φ) {E : Set (PrimeSpectrum S)}
    (hE : IsConstructible E) {ξ : PrimeSpectrum R}
    (hξ : ξ ∈ PrimeSpectrum.comap φ '' E) :
    ∃ U : Set (closure ({ξ} : Set (PrimeSpectrum R))),
      IsOpen U ∧ Dense U ∧
        (U : Set (PrimeSpectrum R)) ⊆ PrimeSpectrum.comap φ '' E := by
  sorry

/-! ## Surjectivity on spectra and radical ideals -/

/- The four conditions in the source are stated as a single `List.TFAE`, so
the ideal-map/comap directions and the prime-spectrum range are visible in
one reusable interface. -/
theorem spectrum_surjective_radical_ideal_conditions
    {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) :
    List.TFAE
      [ Function.Surjective (PrimeSpectrum.comap φ),
        ∀ I : Ideal R,
          Ideal.comap φ (I.map φ).radical = I.radical,
        ∀ I : Ideal R, I.IsRadical →
          Ideal.comap φ (I.map φ) = I,
      ∀ p : PrimeSpectrum R,
          Ideal.comap φ (p.asIdeal.map φ) = p.asIdeal ] := by
  rw [List.tfae_cons_cons]
  refine ⟨?_, ?_⟩
  · constructor
    · intro h I
      rw [Ideal.comap_radical]
      have hle : Ideal.comap φ (I.map φ) ≤ I.radical := by
        rw [Ideal.radical_eq_sInf]
        refine le_sInf ?_
        intro p hp
        let _ : p.IsPrime := hp.2
        have hprime : Ideal.comap φ (p.map φ) = p := by
          obtain ⟨q, hq⟩ := h ⟨p, hp.2⟩
          rw [Ideal.comap_map_eq_self_iff_of_isPrime]
          refine ⟨q.asIdeal, q.isPrime, ?_⟩
          simpa using congrArg PrimeSpectrum.asIdeal hq
        have hle' : Ideal.comap φ (I.map φ) ≤ Ideal.comap φ (p.map φ) :=
          Ideal.comap_mono (Ideal.map_mono hp.1)
        rw [hprime] at hle'
        exact hle'
      apply le_antisymm
      · simpa using Ideal.radical_mono hle
      · exact Ideal.radical_mono Ideal.le_comap_map
    · intro h p
      apply (PrimeSpectrum.mem_range_comap_iff φ).mpr
      apply le_antisymm
      · calc
          Ideal.comap φ (p.asIdeal.map φ) ≤
              Ideal.comap φ (p.asIdeal.map φ).radical :=
            Ideal.comap_mono Ideal.le_radical
          _ = p.asIdeal.radical := h p.asIdeal
          _ = p.asIdeal := p.isPrime.radical
      · exact Ideal.le_comap_map
  · rw [List.tfae_cons_cons]
    refine ⟨?_, ?_⟩
    · constructor
      · intro h I hI
        apply le_antisymm
        · calc
            Ideal.comap φ (I.map φ) ≤
                Ideal.comap φ (I.map φ).radical :=
              Ideal.comap_mono Ideal.le_radical
            _ = I.radical := h I
            _ = I := hI.radical
        · exact Ideal.le_comap_map
      · intro h I
        have hupper : Ideal.comap φ (I.map φ) ≤ I.radical := by
          calc
            Ideal.comap φ (I.map φ) ≤
                Ideal.comap φ ((I.radical).map φ) :=
              Ideal.comap_mono (Ideal.map_mono Ideal.le_radical)
            _ = I.radical := h I.radical (Ideal.radical_isRadical I)
        have heq : (Ideal.comap φ (I.map φ)).radical = I.radical := by
          apply le_antisymm
          · simpa using Ideal.radical_mono hupper
          · exact Ideal.radical_mono Ideal.le_comap_map
        rw [Ideal.comap_radical]
        exact heq
    · rw [List.tfae_cons_cons]
      refine ⟨?_, ?_⟩
      · constructor
        · intro h p
          exact h p.asIdeal p.isPrime.isRadical
        · intro h I hI
          apply le_antisymm
          · have hle : Ideal.comap φ (I.map φ) ≤
                sInf {J : Ideal R | I ≤ J ∧ J.IsPrime} := by
              refine le_sInf ?_
              intro p hp
              have hle' : Ideal.comap φ (I.map φ) ≤ Ideal.comap φ (p.map φ) :=
                Ideal.comap_mono (Ideal.map_mono hp.1)
              simpa using hle'.trans_eq (h ⟨p, hp.2⟩)
            calc
              Ideal.comap φ (I.map φ) ≤ I.radical := by
                rw [Ideal.radical_eq_sInf]
                exact hle
              _ = I := hI.radical
          · exact Ideal.le_comap_map
      · exact List.tfae_singleton _

/- The source's base-change clause asserts preservation of the first three
conditions.  The tensor product uses the algebra structures induced by the
two displayed ring maps. -/
theorem spectrum_surjective_radical_ideal_conditions_baseChange
    {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (hφ : Function.Surjective (PrimeSpectrum.comap φ))
    {R' : Type*} [CommRing R'] (ψ : R →+* R') :
    letI : Algebra R S := φ.toAlgebra
    letI : Algebra R R' := ψ.toAlgebra
    List.TFAE
      [ Function.Surjective
          (PrimeSpectrum.comap (algebraMap R' (R' ⊗[R] S))),
        ∀ I : Ideal R',
          Ideal.comap (algebraMap R' (R' ⊗[R] S))
            (I.map (algebraMap R' (R' ⊗[R] S))).radical = I.radical,
        ∀ I : Ideal R', I.IsRadical →
          Ideal.comap (algebraMap R' (R' ⊗[R] S))
            (I.map (algebraMap R' (R' ⊗[R] S))) = I ] ∧
      Function.Surjective
        (PrimeSpectrum.comap (algebraMap R' (R' ⊗[R] S))) := by
  let solve : ∀ [algS : Algebra R S] [algR' : Algebra R R'],
      algS = φ.toAlgebra → algR' = ψ.toAlgebra →
      List.TFAE
        [ Function.Surjective
            (PrimeSpectrum.comap (algebraMap R' (R' ⊗[R] S))),
          ∀ I : Ideal R',
            Ideal.comap (algebraMap R' (R' ⊗[R] S))
              (I.map (algebraMap R' (R' ⊗[R] S))).radical = I.radical,
          ∀ I : Ideal R', I.IsRadical →
            Ideal.comap (algebraMap R' (R' ⊗[R] S))
              (I.map (algebraMap R' (R' ⊗[R] S))) = I ] ∧
        Function.Surjective
          (PrimeSpectrum.comap (algebraMap R' (R' ⊗[R] S))) := by
    intro algS algR' halgS halgR'
    have hmapS : (algebraMap R S : R →+* S) = φ := by
      calc
        algebraMap R S =
            @algebraMap R S _ _ (φ.toAlgebra) :=
          congrArg (fun a : Algebra R S => @algebraMap R S _ _ a) halgS
        _ = φ := RingHom.algebraMap_toAlgebra φ
    have hmapR' : (algebraMap R R' : R →+* R') = ψ := by
      calc
        algebraMap R R' =
            @algebraMap R R' _ _ (ψ.toAlgebra) :=
          congrArg (fun a : Algebra R R' => @algebraMap R R' _ _ a) halgR'
        _ = ψ := RingHom.algebraMap_toAlgebra ψ
    rw [List.tfae_cons_cons]
    refine ⟨?_, ?_⟩
    · have hT := spectrum_surjective_radical_ideal_conditions
        (algebraMap R' (R' ⊗[R] S))
      rw [List.tfae_cons_cons] at hT
      rw [List.tfae_cons_cons] at hT
      rw [List.tfae_cons_cons]
      exact ⟨hT.1, ⟨hT.2.1, List.tfae_singleton _⟩⟩
    · intro p'
      apply (PrimeSpectrum.nontrivial_iff_mem_rangeComap p').mp
      let p := PrimeSpectrum.comap ψ p'
      obtain ⟨q, hq⟩ := hφ p
      have hf : p.asIdeal = q.asIdeal.comap φ := by
        simpa [p] using congrArg PrimeSpectrum.asIdeal hq.symm
      have hfiber : Nontrivial (p.asIdeal.ResidueField ⊗[R] S) := by
        apply (PrimeSpectrum.nontrivial_iff_mem_rangeComap p).mpr
        have hrange : p ∈ Set.range (PrimeSpectrum.comap φ) := ⟨q, hq⟩
        simpa [hmapS] using hrange
      let k := p.asIdeal.ResidueField
      let K := p'.asIdeal.ResidueField
      have hfp : p.asIdeal = p'.asIdeal.comap ψ := by
        rfl
      let kmap := Ideal.ResidueField.map p.asIdeal p'.asIdeal ψ hfp
      let algRK := ((algebraMap R' K).comp ψ).toAlgebra
      let hKK :=
        (letI : Algebra R K := algRK
         letI : Algebra k K := kmap.toAlgebra
         letI : IsScalarTower R k K :=
           IsScalarTower.of_algebraMap_eq' (by
             ext r
             change algebraMap R' K (ψ r) = kmap (algebraMap R k r)
             symm
             exact Ideal.ResidueField.map_algebraMap p.asIdeal p'.asIdeal ψ hfp r)
         (Module.FaithfullyFlat.nontrivial_tensorProduct_iff_right
           (R := k) (M := K) (N := k ⊗[R] S)).mpr hfiber)
      let e1 :=
        (letI : Algebra R K := algRK
         letI : Algebra k K := kmap.toAlgebra
         letI : IsScalarTower R k K :=
           IsScalarTower.of_algebraMap_eq' (by
             ext r
             change algebraMap R' K (ψ r) = kmap (algebraMap R k r)
             symm
             exact Ideal.ResidueField.map_algebraMap p.asIdeal p'.asIdeal ψ hfp r)
         Algebra.TensorProduct.cancelBaseChange R k K K S)
      let e2 :=
        (letI : Algebra R K := algRK
         letI : IsScalarTower R R' K :=
           IsScalarTower.of_algebraMap_eq' (by
             ext r
             dsimp [algRK]
             rw [RingHom.algebraMap_toAlgebra, hmapR']
             simp [RingHom.comp_apply])
         Algebra.TensorProduct.cancelBaseChange R R' K K S)
      obtain ⟨x, y, hxy⟩ := hKK.exists_pair_ne
      refine ⟨e2.symm (e1 x), e2.symm (e1 y), ?_⟩
      intro heq
      apply hxy
      apply e1.injective
      exact e2.symm.injective heq
  exact @solve (φ.toAlgebra) (ψ.toAlgebra) rfl rfl

/-! ## Dense images and minimal primes -/

/- `DenseRange` is the canonical set-level formulation of the source's
statement that the image contains a dense set of points. -/
theorem domain_injective_dense_spectrum_image_conditions
    {R S : Type*} [CommRing R] [CommRing S] [IsDomain R] (φ : R →+* S) :
    List.TFAE
      [ Function.Injective φ,
        DenseRange (PrimeSpectrum.comap φ),
        ∃ q : PrimeSpectrum S,
          Ideal.comap φ q.asIdeal = (⊥ : Ideal R) ] := by
  rw [List.tfae_cons_cons]
  refine ⟨?_, ?_⟩
  · constructor
    · intro h
      rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical]
      rw [RingHom.ker_eq_comap_bot, Ideal.comap_bot_of_injective φ h]
      exact bot_le
    · intro h
      rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical] at h
      have hnil : nilradical R = (⊥ : Ideal R) :=
        nilradical_eq_bot_iff.mpr inferInstance
      rw [hnil] at h
      intro x y hxy
      have hxy0 : x - y ∈ RingHom.ker φ := by
        change φ (x - y) = 0
        rw [map_sub, hxy, sub_self]
      have hz : x - y ∈ (⊥ : Ideal R) := h hxy0
      apply sub_eq_zero.mp
      simpa using hz
  · rw [List.tfae_cons_cons]
    refine ⟨?_, List.tfae_singleton _⟩
    constructor
    · intro h
      have hinj : Function.Injective φ := by
        rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical] at h
        have hnil : nilradical R = (⊥ : Ideal R) :=
          nilradical_eq_bot_iff.mpr inferInstance
        rw [hnil] at h
        intro x y hxy
        have hxy0 : x - y ∈ RingHom.ker φ := by
          change φ (x - y) = 0
          rw [map_sub, hxy, sub_self]
        have hz : x - y ∈ (⊥ : Ideal R) := h hxy0
        apply sub_eq_zero.mp
        simpa using hz
      have hbot : (⊥ : PrimeSpectrum R) ∈ Set.range (PrimeSpectrum.comap φ) := by
        apply (PrimeSpectrum.mem_range_comap_iff φ).mpr
        simpa only [PrimeSpectrum.asIdeal_bot, Ideal.map_bot] using
          (Ideal.comap_bot_of_injective φ hinj)
      rcases hbot with ⟨q, hq⟩
      refine ⟨q, ?_⟩
      simpa only [PrimeSpectrum.comap_asIdeal, PrimeSpectrum.asIdeal_bot] using
        (congrArg PrimeSpectrum.asIdeal hq)
    · rintro ⟨q, hq⟩
      rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical]
      calc
        RingHom.ker φ ≤ Ideal.comap φ q.asIdeal := Ideal.ker_le_comap φ
        _ = ⊥ := hq
        _ ≤ nilradical R := bot_le

theorem injective_spectrum_image_contains_minimalPrimes
    {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (hφ : Function.Injective φ) (p : PrimeSpectrum R)
    (hp : p.asIdeal ∈ minimalPrimes R) :
    p ∈ Set.range (PrimeSpectrum.comap φ) := by
  obtain ⟨q, hq, hqp⟩ :=
    Ideal.exists_comap_eq_of_mem_minimalPrimes_of_injective hφ p.asIdeal hp
  refine ⟨⟨q, hq⟩, ?_⟩
  apply PrimeSpectrum.ext
  exact hqp

theorem spectrum_image_dense_kernel_nilpotent_conditions
    {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) :
    List.TFAE
      [ (∀ x : R, x ∈ RingHom.ker φ → IsNilpotent x),
        ∀ p : PrimeSpectrum R, p.asIdeal ∈ minimalPrimes R →
          p ∈ Set.range (PrimeSpectrum.comap φ),
        DenseRange (PrimeSpectrum.comap φ) ] := by
  rw [List.tfae_cons_cons]
  refine ⟨?_, ?_⟩
  · constructor
    · intro h
      have hdense : DenseRange (PrimeSpectrum.comap φ) :=
        (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical φ).mpr (by
          intro x hx
          simpa only [mem_nilradical] using h x hx)
      intro p hp
      have hp' := (PrimeSpectrum.denseRange_comap_iff_minimalPrimes φ).mp hdense
        p.asIdeal hp
      rcases hp' with ⟨q, hq⟩
      refine ⟨q, ?_⟩
      apply PrimeSpectrum.ext
      simpa only [PrimeSpectrum.comap_asIdeal] using
        (congrArg PrimeSpectrum.asIdeal hq)
    · intro h
      have hdense : DenseRange (PrimeSpectrum.comap φ) :=
        (PrimeSpectrum.denseRange_comap_iff_minimalPrimes φ).mpr (by
          intro I hI
          exact h ⟨I, hI.1.1⟩ hI)
      intro x hx
      have hx' := (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical φ).mp hdense hx
      simpa only [mem_nilradical] using hx'
  · rw [List.tfae_cons_cons]
    refine ⟨?_, List.tfae_singleton _⟩
    constructor
    · intro h
      apply (PrimeSpectrum.denseRange_comap_iff_minimalPrimes φ).mpr
      intro I hI
      exact h ⟨I, hI.1.1⟩ hI
    · intro h p hp
      have hp' := (PrimeSpectrum.denseRange_comap_iff_minimalPrimes φ).mp h p.asIdeal hp
      rcases hp' with ⟨q, hq⟩
      refine ⟨q, ?_⟩
      apply PrimeSpectrum.ext
      simpa only [PrimeSpectrum.comap_asIdeal] using
        (congrArg PrimeSpectrum.asIdeal hq)

theorem minimalPrime_in_spectrum_image_of_minimalPrime
    {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (p : PrimeSpectrum R) (hp : p.asIdeal ∈ minimalPrimes R)
    (hpImage : p ∈ Set.range (PrimeSpectrum.comap φ)) :
    ∃ q : PrimeSpectrum S, q.asIdeal ∈ minimalPrimes S ∧
      PrimeSpectrum.comap φ q = p := by
  obtain ⟨q, hq⟩ := hpImage
  obtain ⟨r, hr, hrq⟩ :=
    Ideal.exists_minimalPrimes_le (I := (⊥ : Ideal S)) (J := q.asIdeal) bot_le
  let _ : r.IsPrime := hr.1.1
  let _ : (Ideal.comap φ r).IsPrime := Ideal.comap_isPrime φ r
  have hqp : Ideal.comap φ q.asIdeal = p.asIdeal := by
    simpa only [PrimeSpectrum.comap_asIdeal] using
      (congrArg PrimeSpectrum.asIdeal hq)
  have hle : Ideal.comap φ r ≤ p.asIdeal :=
    (Ideal.comap_mono hrq).trans_eq hqp
  have heq : p.asIdeal = Ideal.comap φ r :=
    (hp.2 ⟨inferInstance, bot_le⟩ hle).antisymm hle
  refine ⟨⟨r, hr.1.1⟩, hr, ?_⟩
  apply PrimeSpectrum.ext
  exact heq.symm

/-! ## Algebraic fraction fields -/

/- The source's ``A ⊂ B`` is forced by the displayed fraction-field and
   scalar-tower assumptions.  These compatibilities are kept explicit, so this
   interface also applies to any chosen fraction-field models. -/
theorem ideal_comap_ne_bot_of_algebraic_fractionFields
    {A B K L : Type*} [CommRing A] [CommRing B] [IsDomain A] [IsDomain B]
    [Field K] [Field L] [Algebra A B] [Algebra A K] [Algebra A L]
    [Algebra B L] [Algebra K L] [IsFractionRing A K] [IsFractionRing B L]
    [IsScalarTower A B L] [IsScalarTower A K L]
    [Algebra.IsAlgebraic K L]
    (J : Ideal B) (hJ : J ≠ ⊥) :
    Ideal.comap (algebraMap A B) J ≠ (⊥ : Ideal A) := by
  obtain ⟨x, hxJ, hx0⟩ := J.ne_bot_iff.mp hJ
  have hxalgL : IsAlgebraic A (algebraMap B L x) :=
    (IsFractionRing.isAlgebraic_iff A K L).mpr
      (Algebra.IsAlgebraic.isAlgebraic (R := K) (algebraMap B L x))
  obtain ⟨p, hpne, hpx⟩ := hxalgL
  have hxalgB : IsAlgebraic A x := by
    refine ⟨p, hpne, ?_⟩
    apply (IsFractionRing.injective B L)
    rw [← Polynomial.aeval_algebraMap_apply]
    simpa using hpx
  exact Ideal.comap_ne_bot_of_algebraic_mem hx0 hxJ hxalgB

/- The final sentence of the source lemma is recorded as its direct spectral
consequence for a proper closed subset. -/
theorem image_proper_closed_not_dense_of_algebraic_fractionFields
    {A B K L : Type*} [CommRing A] [CommRing B] [IsDomain A] [IsDomain B]
    [Field K] [Field L] [Algebra A B] [Algebra A K] [Algebra A L]
    [Algebra B L] [Algebra K L] [IsFractionRing A K] [IsFractionRing B L]
    [IsScalarTower A B L] [IsScalarTower A K L]
    [Algebra.IsAlgebraic K L]
    {Z : Set (PrimeSpectrum B)} (hZclosed : IsClosed Z)
    (hZproper : Z ≠ Set.univ) :
    ¬ Dense (PrimeSpectrum.comap (algebraMap A B) '' Z) := by
  rcases (PrimeSpectrum.isClosed_iff_zeroLocus_ideal Z).mp hZclosed with ⟨J, hJZ⟩
  have hJne : J ≠ (⊥ : Ideal B) := by
    intro hJbot
    apply hZproper
    rw [hJZ, hJbot, PrimeSpectrum.zeroLocus_bot]
  have hIne :
      Ideal.comap (algebraMap A B) J ≠ (⊥ : Ideal A) :=
    ideal_comap_ne_bot_of_algebraic_fractionFields
      (A := A) (B := B) (K := K) (L := L) J hJne
  have hsub :
      PrimeSpectrum.comap (algebraMap A B) '' Z ⊆
        PrimeSpectrum.zeroLocus
          (Ideal.comap (algebraMap A B) J : Set A) := by
    rintro p ⟨q, hq, rfl⟩
    rw [PrimeSpectrum.mem_zeroLocus]
    intro a ha
    change algebraMap A B a ∈ q.asIdeal
    apply (PrimeSpectrum.mem_zeroLocus q (J : Set B)).mp
      (hJZ ▸ hq)
    exact ha
  intro hdense
  have hclosedI : IsClosed
      (PrimeSpectrum.zeroLocus
        (Ideal.comap (algebraMap A B) J : Set A)) :=
    PrimeSpectrum.isClosed_zeroLocus _
  have hclosure :
      closure (PrimeSpectrum.comap (algebraMap A B) '' Z) =
        (Set.univ : Set (PrimeSpectrum A)) :=
    hdense.closure_eq
  have hunivsubset :
      (Set.univ : Set (PrimeSpectrum A)) ⊆
        PrimeSpectrum.zeroLocus
          (Ideal.comap (algebraMap A B) J : Set A) := by
    rw [← hclosure]
    exact (hclosedI.closure_subset_iff).mpr hsub
  have hzero :
      PrimeSpectrum.zeroLocus
          (Ideal.comap (algebraMap A B) J : Set A) =
        (Set.univ : Set (PrimeSpectrum A)) :=
    Set.eq_univ_of_forall fun p => hunivsubset (Set.mem_univ p)
  have hIleNil :
      Ideal.comap (algebraMap A B) J ≤ nilradical A := by
    exact (PrimeSpectrum.zeroLocus_eq_univ_iff
      (Ideal.comap (algebraMap A B) J : Set A)).mp hzero
  have hnil : nilradical A = (⊥ : Ideal A) :=
    nilradical_eq_bot_iff.mpr inferInstance
  exact hIne (le_antisymm (by simpa [hnil] using hIleNil) bot_le)

end Formalization.Books.Algebra.Unit30
