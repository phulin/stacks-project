import Formalization.Books.Algebra.Unit17.Spectrum
import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Spectrum.Prime.TensorProduct

/-!
# Commutative Algebra, Chapter 18: Local rings

The source definitions are represented by Mathlib's canonical interfaces:
`IsLocalRing` for local rings, `IsLocalHom` for local ring maps,
`IsLocalRing.maximalIdeal` for the unique maximal ideal,
`Ideal.ResidueField` for the residue field at a prime, and
`Ideal.Fiber` for a tensor-product fibre.  The declarations below record the
source-facing statements while keeping those canonical constructions.
-/

namespace Formalization.Books.Algebra.Unit18

open Set
open scoped TensorProduct

universe u v

noncomputable section

/-! ## Local rings, residue fields, and local maps -/

theorem localRing_iff_unique_maximalIdeal {R : Type u} [CommRing R] :
    IsLocalRing R ↔ ∃! I : Ideal R, I.IsMaximal := by
  constructor
  · intro hR
    exact @IsLocalRing.maximal_ideal_unique R _ hR
  · exact IsLocalRing.of_unique_max_ideal

theorem field_isLocalRing (K : Type u) [Field K] : IsLocalRing K := by
  infer_instance

theorem ringHom_between_fields_isLocalHom {K L : Type u} [Field K] [Field L]
    (f : K →+* L) : IsLocalHom f := by
  infer_instance

/-! ## Prime localizations -/

theorem localizationAtPrime_isLocalRing {R : Type u} [CommRing R]
    (p : Ideal R) [p.IsPrime] : IsLocalRing (Localization.AtPrime p) := by
  infer_instance

theorem localizationAtPrime_maximalIdeal {R : Type u} [CommRing R]
    (p : Ideal R) [p.IsPrime] :
    Ideal.map (algebraMap R (Localization.AtPrime p)) p =
      IsLocalRing.maximalIdeal (Localization.AtPrime p) :=
  Localization.AtPrime.map_eq_maximalIdeal

theorem localizationAtPrime_residueField_quotient_equiv {R : Type u} [CommRing R]
    (p : Ideal R) [p.IsPrime] :
    Nonempty
      ((Localization.AtPrime p ⧸
          Ideal.map (algebraMap R (Localization.AtPrime p)) p) ≃+* p.ResidueField) := by
  rw [localizationAtPrime_maximalIdeal p]
  exact ⟨RingEquiv.refl _⟩

theorem localizationAtPrime_prime_le_maximalIdeal {R : Type u} [CommRing R]
    (p : Ideal R) [p.IsPrime] (q : PrimeSpectrum (Localization.AtPrime p)) :
    q.asIdeal ≤ IsLocalRing.maximalIdeal (Localization.AtPrime p) := by
  exact IsLocalRing.le_maximalIdeal_of_isPrime q.asIdeal

theorem prime_residueField_isFractionRing {R : Type u} [CommRing R]
    (p : Ideal R) [p.IsPrime] : IsFractionRing (R ⧸ p) p.ResidueField := by
  infer_instance

theorem prime_residueField_spectrum_maps_to_prime {R : Type u} [CommRing R]
    (p : Ideal R) [p.IsPrime] (x : PrimeSpectrum p.ResidueField) :
    PrimeSpectrum.comap (algebraMap R (Localization.AtPrime p))
        (PrimeSpectrum.comap (IsLocalRing.residue (Localization.AtPrime p)) x) =
      (⟨p, inferInstance⟩ : PrimeSpectrum R) := by
  rw [IsLocalRing.PrimeSpectrum.comap_residue]
  apply PrimeSpectrum.ext
  change
    (IsLocalRing.maximalIdeal (Localization.AtPrime p)).comap
        (algebraMap R (Localization.AtPrime p)) = p
  exact Localization.AtPrime.under_maximalIdeal

/-! ## Maps of localizations and residue fields -/

theorem localize_at_prime_ringHom_isLocalHom
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (p : Ideal R) [p.IsPrime] (q : Ideal S) [q.IsPrime]
    (φ : R →+* S) (h : p = q.comap φ) :
    IsLocalHom (Localization.localRingHom p q φ h) := by
  infer_instance

theorem localize_at_prime_ringHom_apply
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (p : Ideal R) [p.IsPrime] (q : Ideal S) [q.IsPrime]
    (φ : R →+* S) (h : p = q.comap φ) (r : R) :
    Localization.localRingHom p q φ h (algebraMap R (Localization.AtPrime p) r) =
      algebraMap S (Localization.AtPrime q) (φ r) := by
  exact Localization.localRingHom_to_map p q φ h r

theorem localize_at_prime_residueField_map
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (p : Ideal R) [p.IsPrime] (q : Ideal S) [q.IsPrime]
    (φ : R →+* S) (h : p = q.comap φ) :
    ∃ f : p.ResidueField →+* q.ResidueField,
      ∀ r : R,
        f (algebraMap R p.ResidueField r) =
          algebraMap S q.ResidueField (φ r) := by
  refine ⟨Ideal.ResidueField.map p q φ h, ?_⟩
  intro r
  exact Ideal.ResidueField.map_algebraMap p q φ h r

theorem local_ring_algebraMap_at_prime_not_local
    {R : Type u} [CommRing R] [IsLocalRing R]
    (p : Ideal R) [p.IsPrime]
    (hp : p ≠ IsLocalRing.maximalIdeal R) :
    ¬ IsLocalHom (algebraMap R (Localization.AtPrime p)) := by
  intro h
  apply hp
  rw [← Localization.AtPrime.under_maximalIdeal (I := p)]
  exact
    ((IsLocalRing.local_hom_TFAE (algebraMap R (Localization.AtPrime p))).out 0 4).mp h

/-! ## Characterizations -/

theorem characterize_local_ring {R : Type u} [CommRing R] :
    List.TFAE
      [ IsLocalRing R,
        ∃! p : PrimeSpectrum R, IsClosed ({p} : Set (PrimeSpectrum R)),
        ∃ m : Ideal R, m.IsMaximal ∧ ∀ x : R, x ∉ m → IsUnit x,
        (0 : R) ≠ 1 ∧ ∀ x : R, IsUnit x ∨ IsUnit (1 - x) ] := by
  tfae_have 1 → 2 := by
    intro h
    let : IsLocalRing R := h
    let p : PrimeSpectrum R := ⟨IsLocalRing.maximalIdeal R, inferInstance⟩
    refine
      ⟨p, (PrimeSpectrum.isClosed_singleton_iff_isMaximal p).mpr inferInstance, ?_⟩
    intro q hq
    apply PrimeSpectrum.ext
    exact
      IsLocalRing.eq_maximalIdeal
        (PrimeSpectrum.isClosed_singleton_iff_isMaximal q |>.mp hq)
  tfae_have 2 → 1 := by
    rintro ⟨p, hp, huniq⟩
    rw [localRing_iff_unique_maximalIdeal]
    refine
      ⟨p.asIdeal, (PrimeSpectrum.isClosed_singleton_iff_isMaximal p).mp hp, ?_⟩
    intro I hI
    let q : PrimeSpectrum R := ⟨I, hI.isPrime⟩
    have hq : IsClosed ({q} : Set (PrimeSpectrum R)) :=
      (PrimeSpectrum.isClosed_singleton_iff_isMaximal q).mpr hI
    exact congrArg PrimeSpectrum.asIdeal (huniq q hq)
  tfae_have 1 → 3 := by
    intro h
    let : IsLocalRing R := h
    exact
      ⟨IsLocalRing.maximalIdeal R, inferInstance, fun x hx =>
        IsLocalRing.notMem_maximalIdeal.mp hx⟩
  tfae_have 3 → 4 := by
    rintro ⟨m, hm, hu⟩
    have h01 : (0 : R) ≠ 1 := by
      intro h
      apply hm.ne_top
      apply m.eq_top_iff_one.mpr
      rw [← h]
      exact m.zero_mem
    refine ⟨h01, ?_⟩
    intro x
    by_cases hx : x ∈ m
    · right
      apply hu
      intro hmem
      apply hm.ne_top
      apply m.eq_top_iff_one.mpr
      simpa using m.add_mem hx hmem
    · exact Or.inl (hu x hx)
  tfae_have 4 → 1 := by
    intro h4
    exact
      @IsLocalRing.of_isUnit_or_isUnit_one_sub_self R _
        (nontrivial_of_ne 0 1 h4.1) h4.2
  tfae_finish

theorem characterize_local_ring_map
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S] (φ : R →+* S) :
    List.TFAE
      [ IsLocalHom φ,
        φ '' (IsLocalRing.maximalIdeal R : Set R) ⊆
          (IsLocalRing.maximalIdeal S : Set S),
        (IsLocalRing.maximalIdeal S).comap φ = IsLocalRing.maximalIdeal R,
        ∀ x : R, IsUnit (φ x) → IsUnit x ] := by
  tfae_have 1 ↔ 2 := (IsLocalRing.local_hom_TFAE φ).out 0 1
  tfae_have 1 ↔ 3 := (IsLocalRing.local_hom_TFAE φ).out 0 4
  tfae_have 1 → 4 := by
    intro h
    let : IsLocalHom φ := h
    intro x hx
    exact (isUnit_map_iff φ x).mp hx
  tfae_have 4 → 1 := by
    intro h
    apply ((IsLocalRing.local_hom_TFAE φ).out 3 0).mp
    intro x hx
    change φ x ∈ IsLocalRing.maximalIdeal S
    by_contra hnot
    exact
      (IsLocalRing.notMem_maximalIdeal.mpr
        (h x (IsLocalRing.notMem_maximalIdeal.mp hnot))) hx
  tfae_finish

/-! ## The fundamental fibre diagram -/

/-
The source's algebraic equalities are represented by the canonical
`Ideal.Fiber.algEquivAux₁` and by the localization equivalence below.  The
horizontal spectrum homeomorphisms are the localization and quotient
homeomorphisms from Chapter 17; the fibre-square assertion is recorded by
`PrimeSpectrum.preimageHomeomorphFiber`.
-/

noncomputable def fundamentalDiagram_fiberQuotientEquiv
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    (p : Ideal R) [p.IsPrime] :
    p.Fiber S ≃+*
      Localization (Algebra.algebraMapSubmonoid S p.primeCompl) ⧸
        (p.map (algebraMap R S)).map
          (algebraMap S (Localization (Algebra.algebraMapSubmonoid S p.primeCompl))) :=
by
  letI : Algebra S (p.Fiber S) := Algebra.TensorProduct.rightAlgebra
  exact (Ideal.Fiber.algEquivAux₁ p).toRingEquiv

theorem fundamentalDiagram_outerColumns_equiv
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    (p : Ideal R) [p.IsPrime] :
    Nonempty
      (p.Fiber S ≃+*
        Localization
          (Algebra.algebraMapSubmonoid
            (S ⧸ p.map (algebraMap R S)) p.primeCompl)) := by
  let pS : Ideal S := p.map (algebraMap R S)
  let M : Submonoid S := Algebra.algebraMapSubmonoid S p.primeCompl
  let Sp := Localization M
  let A := S ⧸ pS
  let Q := Sp ⧸ pS.map (algebraMap S Sp)
  let Mbar : Submonoid A := Algebra.algebraMapSubmonoid A p.primeCompl
  let : IsLocalization (M.map (Ideal.Quotient.mk pS)) Q := by
    apply
      IsLocalization.of_surjective M Sp (Ideal.Quotient.mk pS)
        Ideal.Quotient.mk_surjective
        (Ideal.Quotient.mk (pS.map (algebraMap S Sp)))
        Ideal.Quotient.mk_surjective
    · rfl
    · simp
  have hM :
      M.map (Ideal.Quotient.mk pS) =
        Algebra.algebraMapSubmonoid A p.primeCompl := by
    exact
      Algebra.algebraMapSubmonoid_map_eq p.primeCompl
        (Ideal.Quotient.mkₐ R pS)
  let : IsLocalization Mbar Q := by
    change IsLocalization (Algebra.algebraMapSubmonoid A p.primeCompl) Q
    rw [← hM]
    exact inferInstance
  have e : Q ≃ₐ[A] Localization Mbar :=
    IsLocalization.algEquiv Mbar Q (Localization Mbar)
  have e' :
      p.Fiber S ≃+* Localization (Algebra.algebraMapSubmonoid A p.primeCompl) := by
    simpa [pS, M, Sp, A, Q, Mbar] using
      (fundamentalDiagram_fiberQuotientEquiv p).trans e.toRingEquiv
  let e'' :
      p.Fiber S ≃+*
        Localization
          (Algebra.algebraMapSubmonoid
            (S ⧸ p.map (algebraMap R S)) p.primeCompl) := by
    simpa [pS, A] using e'
  exact Nonempty.intro e''

theorem fundamentalDiagram_horizontal_spectrumHomeomorphs
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    (p : Ideal R) [p.IsPrime] :
    Nonempty
        (PrimeSpectrum (Localization (Algebra.algebraMapSubmonoid S p.primeCompl)) ≃ₜ
          {q : PrimeSpectrum S //
            Disjoint (Algebra.algebraMapSubmonoid S p.primeCompl : Set S) q.asIdeal}) ∧
      Nonempty
        (PrimeSpectrum (S ⧸ p.map (algebraMap R S)) ≃ₜ
          {q : PrimeSpectrum S //
            q ∈ PrimeSpectrum.zeroLocus
              (p.map (algebraMap R S) : Set S)}) := by
  exact
    ⟨⟨Formalization.Books.Algebra.Unit17.localizationSpectrumHomeomorph
        (Algebra.algebraMapSubmonoid S p.primeCompl)⟩,
      ⟨Formalization.Books.Algebra.Unit17.quotientSpectrumHomeomorph
        (p.map (algebraMap R S))⟩⟩

theorem fundamentalDiagram_base_horizontal_spectrumHomeomorphs
    {R : Type u} [CommRing R] (p : Ideal R) [p.IsPrime] :
    Nonempty
        (PrimeSpectrum (Localization.AtPrime p) ≃ₜ
          {q : PrimeSpectrum R // Disjoint (p.primeCompl : Set R) q.asIdeal}) ∧
      Nonempty
        (PrimeSpectrum (R ⧸ p) ≃ₜ
          {q : PrimeSpectrum R //
            q ∈ PrimeSpectrum.zeroLocus (p : Set R)}) := by
  exact
    ⟨⟨Formalization.Books.Algebra.Unit17.localizationSpectrumHomeomorph p.primeCompl⟩,
      ⟨Formalization.Books.Algebra.Unit17.quotientSpectrumHomeomorph p⟩⟩

theorem fundamentalDiagram_quotient_horizontal_spectrumHomeomorph
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    (p : Ideal R) [p.IsPrime] :
    Nonempty
      (PrimeSpectrum
          (Localization
            (Algebra.algebraMapSubmonoid
              (S ⧸ p.map (algebraMap R S)) p.primeCompl)) ≃ₜ
        {q : PrimeSpectrum (S ⧸ p.map (algebraMap R S)) //
          Disjoint
            (Algebra.algebraMapSubmonoid
              (S ⧸ p.map (algebraMap R S)) p.primeCompl :
                Set (S ⧸ p.map (algebraMap R S))) q.asIdeal}) := by
  exact ⟨Formalization.Books.Algebra.Unit17.localizationSpectrumHomeomorph
    (Algebra.algebraMapSubmonoid
      (S ⧸ p.map (algebraMap R S)) p.primeCompl)⟩

noncomputable def fundamentalDiagram_fiberHomeomorph
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    (p : Ideal R) [p.IsPrime] :
    (PrimeSpectrum.comap (algebraMap R S)) ⁻¹'
        ({(⟨p, inferInstance⟩ : PrimeSpectrum R)} : Set (PrimeSpectrum R)) ≃ₜ
      PrimeSpectrum (p.Fiber S) :=
  PrimeSpectrum.preimageHomeomorphFiber R S ⟨p, inferInstance⟩

/-! ## The image criterion -/

theorem prime_in_image_iff_fiber_nontrivial
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    (p : Ideal R) [p.IsPrime] :
    (⟨p, inferInstance⟩ : PrimeSpectrum R) ∈
        Set.range (PrimeSpectrum.comap (algebraMap R S)) ↔
      Nontrivial (p.Fiber S) := by
  simpa using
    (PrimeSpectrum.nontrivial_iff_mem_rangeComap
      (R := R) (S := S) (⟨p, inferInstance⟩ : PrimeSpectrum R)).symm

theorem characterize_prime_in_image
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    (p : Ideal R) [p.IsPrime] :
    let Sₚ := Localization (Algebra.algebraMapSubmonoid S p.primeCompl)
    let pS := p.map (algebraMap R S)
    let Squot := S ⧸ pS
    let Squotₚ := Localization (Algebra.algebraMapSubmonoid Squot p.primeCompl)
    List.TFAE
      [ (⟨p, inferInstance⟩ : PrimeSpectrum R) ∈
          Set.range (PrimeSpectrum.comap (algebraMap R S)),
        Nontrivial (p.Fiber S),
        Nontrivial (Sₚ ⧸ pS.map (algebraMap S Sₚ)),
        Nontrivial Squotₚ,
        p = pS.comap (algebraMap R S) ] := by
  dsimp
  tfae_have 1 ↔ 2 := prime_in_image_iff_fiber_nontrivial p
  tfae_have 2 ↔ 3 := by
    exact
      (fundamentalDiagram_fiberQuotientEquiv p).toEquiv.nontrivial_congr
  tfae_have 3 ↔ 4 := by
    let e₁ :
        p.Fiber S ≃+*
          Localization (Algebra.algebraMapSubmonoid S p.primeCompl) ⧸
            (p.map (algebraMap R S)).map
              (algebraMap S
                (Localization (Algebra.algebraMapSubmonoid S p.primeCompl))) :=
      fundamentalDiagram_fiberQuotientEquiv p
    let e₂ :
        p.Fiber S ≃+*
          Localization
            (Algebra.algebraMapSubmonoid
              (S ⧸ p.map (algebraMap R S)) p.primeCompl) :=
      Classical.choice (fundamentalDiagram_outerColumns_equiv p)
    exact (e₁.symm.trans e₂).toEquiv.nontrivial_congr
  tfae_have 1 ↔ 5 := by
    simpa [eq_comm] using
      (PrimeSpectrum.mem_range_comap_iff
        (f := algebraMap R S)
        (p := (⟨p, inferInstance⟩ : PrimeSpectrum R)))
  tfae_finish

/-! ## Local rings of fibres -/

noncomputable def localFiber_primeCorrespondence
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    (p : Ideal R) [p.IsPrime] :
    p.primesOver S ≃o PrimeSpectrum (p.Fiber S) :=
  PrimeSpectrum.primesOverOrderIsoFiber R S p

theorem localFiber_localization_equiv_tensor
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    (p : Ideal R) [p.IsPrime] (qbar : Ideal (p.Fiber S)) [qbar.IsPrime] :
    letI : Algebra (Localization.AtPrime p)
        (Localization.AtPrime (qbar.comap Algebra.TensorProduct.includeRight)) :=
      Localization.AtPrime.algebraOfLiesOver p
        (qbar.comap Algebra.TensorProduct.includeRight)
    Nonempty
      (Localization.AtPrime qbar ≃+*
        (Localization.AtPrime (qbar.comap Algebra.TensorProduct.includeRight) ⊗[Localization.AtPrime p]
          p.ResidueField)) := by
  let r := qbar.comap Algebra.TensorProduct.includeRight
  let Rp := Localization.AtPrime p
  let Sr := Localization.AtPrime r
  let : Algebra Rp Sr := Localization.AtPrime.algebraOfLiesOver p r
  have hI :
      (IsLocalRing.maximalIdeal Rp).map (algebraMap Rp Sr) =
        (p.map (algebraMap R S)).map (algebraMap S Sr) := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal]
    rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq]
    rw [IsScalarTower.algebraMap_eq R S Sr, ← Ideal.map_map]
  have e₁ :
      Localization.AtPrime qbar ≃ₐ[R]
        Sr ⧸ (p.map (algebraMap R S)).map (algebraMap S Sr) :=
    Ideal.Fiber.algEquivAux₂ p qbar
  have e₀ :
      (Sr ⧸ (p.map (algebraMap R S)).map (algebraMap S Sr)) ≃ₐ[Sr]
        Sr ⧸ (IsLocalRing.maximalIdeal Rp).map (algebraMap Rp Sr) :=
    Ideal.quotientEquivAlgOfEq Sr hI.symm
  have e₂ :
      (Sr ⧸ (IsLocalRing.maximalIdeal Rp).map (algebraMap Rp Sr)) ≃ₐ[Sr]
        Sr ⊗[Rp] p.ResidueField :=
    Algebra.TensorProduct.quotIdealMapEquivTensorQuot Sr
      (IsLocalRing.maximalIdeal Rp)
  exact ⟨e₁.toRingEquiv.trans (e₀.toRingEquiv.trans e₂.toRingEquiv)⟩

theorem localFiber_localization_equiv_quotient
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    (p : Ideal R) [p.IsPrime] (qbar : Ideal (p.Fiber S)) [qbar.IsPrime] :
    Nonempty
      (Localization.AtPrime qbar ≃+*
        Localization.AtPrime (qbar.comap Algebra.TensorProduct.includeRight) ⧸
          p.map
            (algebraMap R
              (Localization.AtPrime (qbar.comap Algebra.TensorProduct.includeRight)))) := by
  let : Algebra (Localization.AtPrime p)
      (Localization.AtPrime (qbar.comap Algebra.TensorProduct.includeRight)) :=
    Localization.AtPrime.algebraOfLiesOver p
      (qbar.comap Algebra.TensorProduct.includeRight)
  exact ⟨(Ideal.Fiber.localizationAlgEquivQuotient p qbar).toRingEquiv⟩

end

end Formalization.Books.Algebra.Unit18
