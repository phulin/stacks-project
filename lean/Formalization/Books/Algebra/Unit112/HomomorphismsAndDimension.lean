import Formalization.Books.Algebra.Unit41.GoingUpAndGoingDown
import Formalization.Books.Algebra.Unit60.Dimension
import Formalization.Books.Algebra.Unit103.CohenMacaulayModules
import Formalization.Books.Algebra.Unit106.RegularLocalRings
import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
import Mathlib.RingTheory.RingHom.Finite
import Mathlib.RingTheory.RingHom.Flat

/-!
# Commutative Algebra, Chapter 112: Homomorphisms and dimension

The source's ring-map hypotheses use Mathlib's canonical going-up and going-down
classes after installing the algebra structure attached to a ring homomorphism.
The local ring of a fibre is represented by the quotient of the localization at
the target prime; the canonical tensor-product fibre and the localization of
the quotient are recorded by ring-equivalence interfaces below.
-/

namespace Formalization.Books.Algebra.Unit112

universe u v

noncomputable section

/-! ## Dimension and going up/down -/

/-- A going-up or going-down ring map with surjective map on spectra cannot
decrease Krull dimension. -/
theorem dimension_le_of_goingUp_or_goingDown
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) :
    letI : Algebra R S := f.toAlgebra
    (Algebra.HasGoingUp R S ∨ Algebra.HasGoingDown R S) →
      Function.Surjective (PrimeSpectrum.comap f) →
        ringKrullDim R ≤ ringKrullDim S := by
  intro h hsurj
  let _ : Algebra R S := f.toAlgebra
  rw [← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim,
    ← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
  apply Formalization.Books.Topology.Unit19.topologicalKrullDim_le_of_surjective_of_specializing_or_generalizing
    (PrimeSpectrum.comap f) (PrimeSpectrum.continuous_comap f) hsurj
  cases h with
  | inl h =>
    exact Or.inl (Algebra.HasGoingUp.iff_specializingMap_primeSpectrumComap.mp h)
  | inr h =>
    exact Or.inr (Algebra.HasGoingDown.iff_generalizingMap_primeSpectrumComap.mp h)
  /- Original proof attempt:
  intro h hsurj
  haveI : Algebra R S := f.toAlgebra
  rw [← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim,
    ← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
  apply Formalization.Books.Topology.Unit19.topologicalKrullDim_le_of_surjective_of_specializing_or_generalizing
    (PrimeSpectrum.comap f) (PrimeSpectrum.continuous_comap f) hsurj
  cases h with
  | inl h =>
    exact Or.inl (Algebra.HasGoingUp.iff_specializingMap_primeSpectrumComap.mp h)
  | inr h =>
    exact Or.inr (Algebra.HasGoingDown.iff_generalizingMap_primeSpectrumComap.mp h)

  -/

/-- Under going up, the contraction of a maximal ideal is maximal. -/
theorem isMaximal_comap_of_goingUp
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) :
    letI : Algebra R S := f.toAlgebra
    Algebra.HasGoingUp R S →
      ∀ q : Ideal S, q.IsMaximal → (q.comap f).IsMaximal := by
  intro h q hq
  let _ : Algebra R S := f.toAlgebra
  letI : Algebra.HasGoingUp R S := h
  letI : q.IsMaximal := hq
  letI : q.LiesOver (q.comap f) := ⟨rfl⟩
  refine ⟨⟨Ideal.comap_ne_top (f := f) hq.ne_top, ?_⟩⟩
  intro J hJ
  apply Ideal.maximal_of_no_maximal ?_ J hJ
  intro m hm hmax
  letI : m.IsMaximal := hmax
  obtain ⟨Q, hqQ, hQ, hQover⟩ :=
    Ideal.exists_ideal_ge_liesOver_of_le (P := q)
      (p := q.comap f) (q := m) hm.le
  by_cases hQtop : Q = ⊤
  · exact hmax.ne_top (by simpa [hQtop] using hQover.over)
  · have hqQeq : q = Q := hq.eq_of_le hQtop hqQ
    have hcontra : q.comap f = m := by
      calc
        q.comap f = Q.comap f := congrArg (fun I : Ideal S => I.comap f) hqQeq
        _ = m := hQover.over.symm
    exact (hm.ne hcontra).elim
  /- Original proof attempt:
  intro h q hq
  haveI : Algebra R S := f.toAlgebra
  haveI : Algebra.HasGoingUp R S := h
  haveI : q.IsMaximal := hq
  refine ⟨⟨Ideal.comap_ne_top (f := f) hq.ne_top, ?_⟩⟩
  intro J hJ
  apply Ideal.maximal_of_no_maximal ?_ J hJ
  intro m hm hmax
  haveI : m.IsMaximal := hmax
  obtain ⟨Q, hqQ, hQ, hQover⟩ :=
    Ideal.exists_ideal_ge_liesOver_of_le (P := q)
      (p := q.comap f) (q := m) hm.le
  by_cases hQtop : Q = ⊤
  · exact hQtop
  · have hqQeq : q = Q := hq.eq_of_le hQtop hqQ
    have hcontra : q.comap f = m := by
      calc
        q.comap f = Q.comap f := congrArg (fun I : Ideal S => I.comap f) hqQeq
        _ = m := hQover.over.symm
    exact (hm.ne hcontra).elim

  -/

/-! ## Integral extensions -/

/-- An integral ring map lowers Krull dimension and sends closed points of the
spectrum to closed points. -/
theorem integral_ringKrullDim_le_and_closedPoint_map
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    (hf : f.IsIntegral) :
    ringKrullDim S ≤ ringKrullDim R ∧
      ∀ q : PrimeSpectrum S, q.asIdeal.IsMaximal →
        (q.asIdeal.comap f).IsMaximal := by
  constructor
  · let _ : Algebra R S := f.toAlgebra
    let _ : Algebra.IsIntegral R S := ⟨hf⟩
    change Order.krullDim (PrimeSpectrum S) ≤ Order.krullDim (PrimeSpectrum R)
    apply Order.krullDim_le_of_strictMono (PrimeSpectrum.comap f)
    intro q q' hqq'
    change q.asIdeal.comap (algebraMap R S) < q'.asIdeal.comap (algebraMap R S)
    have hideal : q.asIdeal < q'.asIdeal :=
      (PrimeSpectrum.asIdeal_lt_asIdeal q q').mpr hqq'
    exact Ideal.IsIntegral.comap_lt_comap hideal
  · intro q hq
    exact Ideal.isMaximal_comap_of_isIntegral_of_isMaximal' f hf q.asIdeal
  /- Original proof attempt:
  constructor
  · haveI : Algebra R S := f.toAlgebra
    haveI : Algebra.IsIntegral R S := ⟨hf⟩
    change Order.krullDim (PrimeSpectrum S) ≤ Order.krullDim (PrimeSpectrum R)
    apply Order.krullDim_le_of_strictMono (PrimeSpectrum.comap f)
    intro q q' hqq'
    change q.asIdeal.comap (algebraMap R S) < q'.asIdeal.comap (algebraMap R S)
    have hideal : q.asIdeal < q'.asIdeal :=
      (PrimeSpectrum.asIdeal_lt_asIdeal q q').mpr hqq'
    exact Ideal.IsIntegral.comap_lt_comap hideal
  · intro q hq
    exact Ideal.isMaximal_comap_of_isIntegral_of_isMaximal' f hf q.asIdeal

  -/

/-- An injective integral ring map preserves Krull dimension. -/
theorem integral_subring_ringKrullDim_eq
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    (hinj : Function.Injective f) (hf : f.IsIntegral) :
    ringKrullDim R = ringKrullDim S := by
  apply le_antisymm
  · let _ : Algebra R S := f.toAlgebra
    let _ : Algebra.IsIntegral R S := ⟨hf⟩
    apply dimension_le_of_goingUp_or_goingDown f
    · exact Or.inl inferInstance
    · exact hf.comap_surjective hinj
  · exact (integral_ringKrullDim_le_and_closedPoint_map f hf).1

/-! ## The local ring of a fibre -/

/-- The ideal `p S_q`, expressed by mapping `p` along `R → S_q`. -/
noncomputable def fibreIdealInLocalization
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    (p : PrimeSpectrum R) (q : PrimeSpectrum S) :
    Ideal (Localization.AtPrime q.asIdeal) :=
  (p.asIdeal.map f).map (algebraMap S (Localization.AtPrime q.asIdeal))

/-- The local ring of the fibre at a prime `q` over `p`, in its quotient
presentation `S_q / p S_q`. -/
noncomputable abbrev localRingOfFibre
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    (p : PrimeSpectrum R) (q : PrimeSpectrum S)
    (_hq : PrimeSpectrum.comap f q = p) : Type u :=
  (Localization.AtPrime q.asIdeal) ⧸ fibreIdealInLocalization f p q

/-- The ideal `pS` in `S`. -/
def fibreIdealInTarget
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    (p : PrimeSpectrum R) : Ideal S :=
  p.asIdeal.map f

/-- The prime of `S / pS` induced by a prime `q` lying over `p`. -/
noncomputable def fibreQuotientPrime
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    (p : PrimeSpectrum R) (q : PrimeSpectrum S)
    (hq : PrimeSpectrum.comap f q = p) :
    PrimeSpectrum (S ⧸ fibreIdealInTarget f p) := by
  let I : Ideal S := fibreIdealInTarget f p
  have hcomap : q.asIdeal.comap f = p.asIdeal := by
    simpa [PrimeSpectrum.comap_asIdeal] using congrArg PrimeSpectrum.asIdeal hq
  have hI : I ≤ q.asIdeal := by
    apply Ideal.map_le_iff_le_comap.mpr
    exact hcomap.symm.le
  exact ⟨q.asIdeal.map (Ideal.Quotient.mk I),
    Ideal.isPrime_map_quotientMk_of_isPrime hI⟩

/- The tensor-product presentation of the same local fibre ring. -/
noncomputable abbrev tensorFibrePrime
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    (p : PrimeSpectrum R) (q : PrimeSpectrum S)
    (hq : PrimeSpectrum.comap f q = p) :
    letI : Algebra R S := f.toAlgebra
    PrimeSpectrum (p.asIdeal.Fiber S) := by
  let _ : Algebra R S := f.toAlgebra
  exact PrimeSpectrum.preimageEquivFiber R S p ⟨q, by
    simpa [RingHom.algebraMap_toAlgebra] using hq⟩

/-- The localization of the tensor-product fibre at the prime corresponding
to `q`. -/
noncomputable abbrev tensorLocalRingOfFibre
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    (p : PrimeSpectrum R) (q : PrimeSpectrum S)
    (hq : PrimeSpectrum.comap f q = p) :
    Type u := by
  let _ : Algebra R S := f.toAlgebra
  exact Localization.AtPrime (tensorFibrePrime f p q hq).asIdeal

/-- The quotient and localization presentations of the local ring of a fibre
are canonically ring-equivalent. -/
theorem localRingOfFibre_equiv_localized_quotient
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    (p : PrimeSpectrum R) (q : PrimeSpectrum S)
    (hq : PrimeSpectrum.comap f q = p) :
    Nonempty
      (localRingOfFibre f p q hq ≃+*
        Localization.AtPrime (fibreQuotientPrime f p q hq).asIdeal) := by
  let I : Ideal S := fibreIdealInTarget f p
  let Sp := Localization.AtPrime q.asIdeal
  let Q := Sp ⧸ I.map (algebraMap S Sp)
  let M : Submonoid S := q.asIdeal.primeCompl
  let qbar := fibreQuotientPrime f p q hq
  have hIle : I ≤ q.asIdeal := by
    change p.asIdeal.map f ≤ q.asIdeal
    apply Ideal.map_le_iff_le_comap.mpr
    simpa [PrimeSpectrum.comap_asIdeal] using
      (congrArg PrimeSpectrum.asIdeal hq).symm.le
  have hqcomap : qbar.asIdeal.comap (Ideal.Quotient.mk I) = q.asIdeal := by
    change (q.asIdeal.map (Ideal.Quotient.mk I)).comap (Ideal.Quotient.mk I) = q.asIdeal
    rw [Ideal.comap_map_of_surjective (f := Ideal.Quotient.mk I)
      Ideal.Quotient.mk_surjective]
    apply sup_eq_left.mpr
    intro x hx
    have hx0 : Ideal.Quotient.mk I x = 0 := by simpa using hx
    exact hIle (Ideal.Quotient.eq_zero_iff_mem.mp hx0)
  have hM : M.map (Ideal.Quotient.mk I) = qbar.asIdeal.primeCompl := by
    change q.asIdeal.primeCompl.map (Ideal.Quotient.mk I) = qbar.asIdeal.primeCompl
    simpa only [hqcomap] using
      (Ideal.map_primeCompl_comap_of_surjective
        (f := Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective qbar.asIdeal)
  have hloc : IsLocalization (M.map (Ideal.Quotient.mk I)) Q := by
    apply IsLocalization.of_surjective M Sp (Ideal.Quotient.mk I)
      Ideal.Quotient.mk_surjective
      (Ideal.Quotient.mk (I.map (algebraMap S Sp)))
      Ideal.Quotient.mk_surjective
    · rfl
    · simp
  let : IsLocalization qbar.asIdeal.primeCompl Q := by
    rw [← hM]
    exact hloc
  change Nonempty (Q ≃+* Localization.AtPrime qbar.asIdeal)
  exact ⟨(IsLocalization.algEquiv qbar.asIdeal.primeCompl
    (Localization.AtPrime qbar.asIdeal) Q).symm.toRingEquiv⟩

/-- The quotient presentation of the local ring of a fibre is canonically
ring-equivalent to the localization of the tensor-product fibre
`S ⊗_R κ(p)`. -/
theorem localRingOfFibre_equiv_tensor_fibre
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    (p : PrimeSpectrum R) (q : PrimeSpectrum S)
    (hq : PrimeSpectrum.comap f q = p) :
    Nonempty
      (localRingOfFibre f p q hq ≃+* tensorLocalRingOfFibre f p q hq) := by
  let _ : Algebra R S := f.toAlgebra
  have hq' : PrimeSpectrum.comap (algebraMap R S) q = p := by
    simpa [RingHom.algebraMap_toAlgebra] using hq
  have hqF :
      (tensorFibrePrime f p q hq).asIdeal.comap
          Algebra.TensorProduct.includeRight = q.asIdeal := by
    have hleft :=
      (PrimeSpectrum.preimageEquivFiber R S p).left_inv
        (⟨q, hq'⟩ : PrimeSpectrum.comap (algebraMap R S) ⁻¹' {p})
    have hleft' := congrArg
      (fun z : PrimeSpectrum.comap (algebraMap R S) ⁻¹' {p} => z.1.asIdeal) hleft
    change
      (PrimeSpectrum.preimageEquivFiber R S p
        (⟨q, hq'⟩ : PrimeSpectrum.comap (algebraMap R S) ⁻¹' {p})).asIdeal.comap
          Algebra.TensorProduct.includeRight = q.asIdeal at hleft'
    change
      (PrimeSpectrum.preimageEquivFiber R S p
        (⟨q, hq'⟩ : PrimeSpectrum.comap (algebraMap R S) ⁻¹' {p})).asIdeal.comap
          Algebra.TensorProduct.includeRight = q.asIdeal
    exact hleft'
  let _ : Algebra (Localization.AtPrime p.asIdeal)
      (Localization.AtPrime
        ((tensorFibrePrime f p q hq).asIdeal.comap
          Algebra.TensorProduct.includeRight)) :=
    Localization.AtPrime.algebraOfLiesOver p.asIdeal _
  let e := Ideal.Fiber.localizationAlgEquivQuotient
    p.asIdeal (tensorFibrePrime f p q hq).asIdeal
  let r : Ideal S :=
    (tensorFibrePrime f p q hq).asIdeal.comap Algebra.TensorProduct.includeRight
  have hr : r = q.asIdeal := hqF
  have hM : r.primeCompl = q.asIdeal.primeCompl := by
    ext x
    simp only [Ideal.mem_primeCompl_iff]
    rw [hr]
  letI : IsLocalization r.primeCompl (Localization.AtPrime q.asIdeal) := by
    rw [hM]
    infer_instance
  let eLoc : Localization.AtPrime r ≃ₐ[S] Localization.AtPrime q.asIdeal :=
    IsLocalization.algEquiv r.primeCompl _ _
  have hI : fibreIdealInLocalization f p q =
      p.asIdeal.map (algebraMap R (Localization.AtPrime q.asIdeal)) := by
    change (p.asIdeal.map f).map
        (algebraMap S (Localization.AtPrime q.asIdeal)) = _
    rw [Ideal.map_map]
    congr 1
  have hIeq :
      p.asIdeal.map (algebraMap R (Localization.AtPrime q.asIdeal)) =
        (p.asIdeal.map (algebraMap R (Localization.AtPrime r))).map eLoc.toRingHom := by
    rw [Ideal.map_map]
    congr 1
    ext x
    change algebraMap R (Localization.AtPrime q.asIdeal) x =
      eLoc (algebraMap R (Localization.AtPrime r) x)
    rw [IsScalarTower.algebraMap_apply R S (Localization.AtPrime q.asIdeal),
      IsScalarTower.algebraMap_apply R S (Localization.AtPrime r)]
    exact (eLoc.commutes (algebraMap R S x)).symm
  let eQuot := Ideal.quotientEquiv
    (p.asIdeal.map (algebraMap R (Localization.AtPrime r)))
    (p.asIdeal.map (algebraMap R (Localization.AtPrime q.asIdeal)))
    eLoc.toRingEquiv hIeq
  exact ⟨(Ideal.quotientEquivAlgOfEq R hI).toRingEquiv.trans
    (eQuot.symm.trans e.symm.toRingEquiv)⟩
  /- Original proof attempt:
  haveI : Algebra R S := f.toAlgebra
  have hq' : PrimeSpectrum.comap (algebraMap R S) q = p := by
    simpa [RingHom.algebraMap_toAlgebra] using hq
  have hqF :
      (tensorFibrePrime f p q hq).asIdeal.comap
          Algebra.TensorProduct.includeRight = q.asIdeal := by
    have hleft :=
      (PrimeSpectrum.preimageEquivFiber R S p).left_inv
        (⟨q, hq'⟩ : PrimeSpectrum.comap (algebraMap R S) ⁻¹' {p})
    have hleft' := congrArg
      (fun z : PrimeSpectrum.comap (algebraMap R S) ⁻¹' {p} => z.1.asIdeal) hleft
    change
      (PrimeSpectrum.preimageEquivFiber R S p
        (⟨q, hq'⟩ : PrimeSpectrum.comap (algebraMap R S) ⁻¹' {p})).asIdeal.comap
          Algebra.TensorProduct.includeRight = q.asIdeal at hleft'
    change
      (PrimeSpectrum.preimageEquivFiber R S p
        (⟨q, hq'⟩ : PrimeSpectrum.comap (algebraMap R S) ⁻¹' {p})).asIdeal.comap
          Algebra.TensorProduct.includeRight = q.asIdeal
    exact hleft'
  haveI : Algebra (Localization.AtPrime p.asIdeal)
      (Localization.AtPrime
        ((tensorFibrePrime f p q hq).asIdeal.comap Algebra.TensorProduct.includeRight)) :=
    Localization.AtPrime.algebraOfLiesOver p.asIdeal _
  let e := Ideal.Fiber.localizationAlgEquivQuotient
    p.asIdeal (tensorFibrePrime f p q hq).asIdeal
  exact ⟨e.symm.toRingEquiv⟩

  -/

/-! ## Dimension of a base, fibre, and total ring -/

private theorem ringKrullDim_le_of_localRingHom
    {A B : Type u} [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B]
    [IsNoetherianRing A] [IsNoetherianRing B]
    (g : A →+* B) [IsLocalHom g] :
    ringKrullDim B ≤
      ringKrullDim A + ringKrullDim (B ⧸ (IsLocalRing.maximalIdeal A).map g) := by
  classical
  have hbot : ringKrullDim A ≠ ⊥ := ringKrullDim_ne_bot
  have htop : ringKrullDim A ≠ ⊤ := ringKrullDim_ne_top
  obtain ⟨d, hd⟩ : ∃ d : ℕ, ringKrullDim A = d := by
    cases hq : ringKrullDim A with
    | bot => exact (hbot hq).elim
    | coe q =>
        cases q with
        | top => exact (htop hq).elim
        | coe d =>
            refine ⟨d, ?_⟩
            simp
  have hparam :=
    ((Formalization.Books.Algebra.Unit60.local_dimension_characterization
      A inferInstance d).out 0 2).mp hd
  obtain ⟨x, hx, hdef⟩ := hparam.1
  let I : Ideal A := Ideal.span (Set.range x)
  let J : Ideal B := I.map g
  have hIle : I ≤ IsLocalRing.maximalIdeal A := by
    rw [← hdef]
    exact Ideal.le_radical
  have hJle : J ≤ IsLocalRing.maximalIdeal B := by
    rw [Ideal.map_le_iff_le_comap, IsLocalRing.maximalIdeal_comap]
    exact hIle
  have hIspan : I.spanFinrank ≤ d := by
    let s : Finset A := Finset.univ.image x
    have hs : (s : Set A) = Set.range x := by
      ext y
      simp [s]
    have hscard : s.card ≤ d := by
      simpa [s] using (Finset.card_image_le (f := x) (s := Finset.univ))
    rw [show I = Ideal.span (s : Set A) by simp [I, hs]]
    calc
      (Ideal.span (s : Set A)).spanFinrank ≤ s.card := by
        change (Submodule.span A (s : Set A)).spanFinrank ≤ s.card
        simpa using (Submodule.spanFinrank_span_le_ncard_of_finite
          (R := A) (M := A) (s := (s : Set A)) s.finite_toSet)
      _ ≤ d := hscard
  have hJspan : J.spanFinrank ≤ d := by
    exact (Ideal.spanFinrank_map_le_of_fg g
      (IsNoetherian.noetherian I)).trans hIspan
  have hrad : J.radical = ((IsLocalRing.maximalIdeal A).map g).radical := by
    apply le_antisymm
    · exact Ideal.radical_mono (Ideal.map_mono hIle)
    · have hmap : (IsLocalRing.maximalIdeal A).map g ≤ J.radical := by
        rw [← hdef]
        exact I.map_radical_le g
      simpa [J] using (Ideal.radical_mono hmap)
  have hquot : ringKrullDim (B ⧸ J) =
      ringKrullDim (B ⧸ (IsLocalRing.maximalIdeal A).map g) := by
    rw [ringKrullDim_quotient, ringKrullDim_quotient,
      PrimeSpectrum.zeroLocus_eq_iff.mpr hrad]
  calc
    ringKrullDim B ≤ ringKrullDim (B ⧸ J) + J.spanFinrank := by
      exact ringKrullDim_le_ringKrullDim_quotient_add_spanFinrank J
        (by simpa [IsLocalRing.ringJacobson_eq_maximalIdeal] using hJle)
    _ ≤ ringKrullDim (B ⧸ (IsLocalRing.maximalIdeal A).map g) + d := by
      rw [← hquot]
      have hJspan' : (J.spanFinrank : WithBot ℕ∞) ≤ d := by
        exact_mod_cast hJspan
      exact add_le_add_right hJspan' _
    _ = ringKrullDim A + ringKrullDim (B ⧸ (IsLocalRing.maximalIdeal A).map g) := by
      rw [hd]
      simp [add_comm]

/-- The dimension of a localized target is bounded by the dimensions of the
localized base and the local fibre. -/
theorem ringKrullDim_localization_le_base_add_fibre
    {R S : Type u} [CommRing R] [CommRing S]
    [IsNoetherianRing R] [IsNoetherianRing S]
    (f : R →+* S) (p : PrimeSpectrum R) (q : PrimeSpectrum S)
    (hq : PrimeSpectrum.comap f q = p) :
    ringKrullDim (Localization.AtPrime q.asIdeal) ≤
      ringKrullDim (Localization.AtPrime p.asIdeal) +
        ringKrullDim (localRingOfFibre f p q hq) := by
  have hqp : p.asIdeal = q.asIdeal.comap f := by
    simpa [PrimeSpectrum.comap_asIdeal] using
      (congrArg PrimeSpectrum.asIdeal hq).symm
  let g := Localization.localRingHom p.asIdeal q.asIdeal f hqp
  have hK :
      (IsLocalRing.maximalIdeal (Localization.AtPrime p.asIdeal)).map g =
        fibreIdealInLocalization f p q := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal (I := p.asIdeal)]
    change
      (p.asIdeal.map (algebraMap R (Localization.AtPrime p.asIdeal))).map g =
        (p.asIdeal.map f).map (algebraMap S (Localization.AtPrime q.asIdeal))
    rw [Ideal.map_map]
    have heq :
        g.comp (algebraMap R (Localization.AtPrime p.asIdeal)) =
          (algebraMap S (Localization.AtPrime q.asIdeal)).comp f := by
      ext x
      simp [g, Localization.localRingHom_to_map]
    rw [heq]
    rw [← Ideal.map_map]
  have hbound := ringKrullDim_le_of_localRingHom g
  rw [hK] at hbound
  simpa only [localRingOfFibre] using hbound

/-- Going down gives equality in the base--fibre dimension formula. -/
theorem ringKrullDim_localization_eq_base_add_fibre_of_goingDown
    {R S : Type u} [CommRing R] [CommRing S]
    [IsNoetherianRing R] [IsNoetherianRing S]
    (f : R →+* S) (p : PrimeSpectrum R) (q : PrimeSpectrum S)
    (hq : PrimeSpectrum.comap f q = p) :
    letI : Algebra R S := f.toAlgebra
    Algebra.HasGoingDown R S →
        ringKrullDim (Localization.AtPrime q.asIdeal) =
        ringKrullDim (Localization.AtPrime p.asIdeal) +
          ringKrullDim (localRingOfFibre f p q hq) := by
  intro hGD
  let _ : Algebra R S := f.toAlgebra
  let _ : Algebra.HasGoingDown R S := hGD
  have hcomap : q.asIdeal.comap (algebraMap R S) = p.asIdeal := by
    simpa [RingHom.algebraMap_toAlgebra, PrimeSpectrum.comap_asIdeal] using
      congrArg PrimeSpectrum.asIdeal hq
  let _ : q.asIdeal.LiesOver p.asIdeal := ⟨hcomap.symm⟩
  let I : Ideal S := p.asIdeal.map (algebraMap R S)
  have hheight :=
    Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown
      (p := p.asIdeal) (P := q.asIdeal)
  have hfibre :
      ringKrullDim (localRingOfFibre f p q hq) =
        (fibreQuotientPrime f p q hq).asIdeal.height := by
    obtain ⟨e⟩ := localRingOfFibre_equiv_localized_quotient f p q hq
    rw [ringKrullDim_eq_of_ringEquiv e]
    exact IsLocalization.AtPrime.ringKrullDim_eq_height
      (fibreQuotientPrime f p q hq).asIdeal
      (Localization.AtPrime (fibreQuotientPrime f p q hq).asIdeal)
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height
      p.asIdeal (Localization.AtPrime p.asIdeal),
    IsLocalization.AtPrime.ringKrullDim_eq_height
      q.asIdeal (Localization.AtPrime q.asIdeal), hfibre]
  have hqbar :
      (fibreQuotientPrime f p q hq).asIdeal =
        q.asIdeal.map (Ideal.Quotient.mk I) := by
    rfl
  rw [← WithBot.coe_add]
  rw [hqbar]
  exact congrArg (fun n : ℕ∞ => (n : WithBot ℕ∞)) hheight

/-! ## Regular and Cohen--Macaulay consequences -/

private theorem exists_minimal_maximalIdeal_generators
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R] :
    ∃ xs : List R,
      Formalization.Books.Algebra.Unit106.IsMinimalIdealGeneratingList
        (IsLocalRing.maximalIdeal R) xs := by
  classical
  let gens : Set R := (IsLocalRing.maximalIdeal R).generators
  let hfg : (IsLocalRing.maximalIdeal R).FG :=
    IsNoetherian.noetherian (IsLocalRing.maximalIdeal R)
  let hgens : gens.Finite := Submodule.FG.finite_generators hfg
  let F : Finset R := hgens.toFinset
  let xs : List R := F.toList
  have hgensF : (F : Set R) = gens := hgens.coe_toFinset
  have hspan : Ideal.ofList xs = IsLocalRing.maximalIdeal R := by
    simpa [Ideal.ofList, xs, gens, hgensF] using
      (IsLocalRing.maximalIdeal R).span_generators
  refine ⟨xs, ⟨hspan, ?_⟩⟩
  intro i hi
  have hspan_erase :
      Ideal.ofList (xs.eraseIdx i.1) = IsLocalRing.maximalIdeal R := by
    apply le_antisymm
    · rw [← hspan]
      apply Ideal.span_le.mpr
      intro y hy
      exact Ideal.subset_span (List.eraseIdx_subset hy)
    · rw [← hspan]
      apply Ideal.span_le.mpr
      intro y hy
      by_cases hyeq : y = xs.get i
      · simpa [hyeq] using hi
      · have hy' : y ∈ xs.eraseIdx i.1 := by
          change y ∈ xs at hy
          obtain ⟨j, hj, hget⟩ := List.mem_iff_getElem.mp hy
          have hji : j ≠ i.1 := by
            intro hji
            apply hyeq
            subst j
            exact hget.symm
          rw [List.mem_eraseIdx_iff_getElem]
          exact ⟨j, hj, hji, hget⟩
        change y ∈ Ideal.span {r | r ∈ xs.eraseIdx i.1}
        exact Ideal.subset_span hy'
  let E : Finset R := (xs.eraseIdx i.1).toFinset
  have hspanE : Ideal.span (↑E : Set R) = IsLocalRing.maximalIdeal R := by
    simpa [E, Ideal.ofList] using hspan_erase
  have hspanE' : Submodule.span R (↑E : Set R) = IsLocalRing.maximalIdeal R :=
    hspanE
  have hle := Submodule.spanFinrank_span_le_ncard_of_finite
    (R := R) (M := R) (s := (↑E : Set R)) E.finite_toSet
  rw [hspanE'] at hle
  have hgen : (IsLocalRing.maximalIdeal R).spanFinrank = F.card := by
    rw [← Submodule.FG.generators_ncard hfg]
    simpa [F, gens] using Set.ncard_eq_toFinset_card (hs := hgens)
  rw [hgen] at hle
  have hcard : E.card ≤ (xs.eraseIdx i.1).length := by
    simpa [E] using List.toFinset_card_le (xs.eraseIdx i.1)
  have hle' : F.card ≤ (xs.eraseIdx i.1).length :=
    le_trans (by simpa using hle) hcard
  have hle'' : xs.length ≤ (xs.eraseIdx i.1).length := by
    simpa [xs] using hle'
  have hlen : (xs.eraseIdx i.1).length + 1 = xs.length :=
    List.length_eraseIdx_add_one i.isLt
  omega

/-- A flat local map of Noetherian local rings with regular source and regular
fibre has regular target. -/
theorem isRegularLocalRing_of_flat_localHom_of_regular_fibre
    {R S : Type u} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S]
    [IsNoetherianRing R] [IsNoetherianRing S]
    (f : R →+* S) [IsLocalHom f]
    (hR : IsRegularLocalRing R)
    (hFibre : IsRegularLocalRing
      (S ⧸ (IsLocalRing.maximalIdeal R).map f))
    (hflat : RingHom.Flat f) :
    IsRegularLocalRing S := by
  let _ : Algebra R S := f.toAlgebra
  let _ : IsLocalHom (algebraMap R S) := by
    change IsLocalHom f
    infer_instance
  obtain ⟨xs, hxs⟩ := exists_minimal_maximalIdeal_generators (R := R)
  have hregR : RingTheory.Sequence.IsRegular R xs :=
    (Formalization.Books.Algebra.Unit106.regular_ring_CM xs hxs).1
  let _ : Module.Flat R S := RingHom.flat_algebraMap_iff.mp (by
    simpa [RingHom.algebraMap_toAlgebra] using hflat)
  let _ : Module.FaithfullyFlat R S :=
    Module.FaithfullyFlat.of_flat_of_isLocalHom
  have hregS : RingTheory.Sequence.IsRegular S
      (xs.map (algebraMap R S)) :=
    RingTheory.Sequence.IsRegular.of_faithfullyFlat hregR
  have hideal :
      Ideal.ofList (xs.map (algebraMap R S)) =
        (IsLocalRing.maximalIdeal R).map (algebraMap R S) := by
    rw [← Ideal.map_ofList, hxs.1]
  have hquot : IsRegularLocalRing
      (S ⧸ Ideal.ofList (xs.map (algebraMap R S))) := by
    let _ : IsRegularLocalRing
        (S ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R S)) := by
      simpa [RingHom.algebraMap_toAlgebra] using hFibre
    exact IsRegularLocalRing.of_ringEquiv
      (Ideal.quotientEquivAlgOfEq S hideal).toRingEquiv.symm
  exact Formalization.Books.Algebra.Unit106.regular_local_of_regular_sequence
    (xs.map (algebraMap R S)) hregS hquot

/-- A finite-flat local extension of a Cohen--Macaulay local ring is
Cohen--Macaulay; the same conclusion holds for a flat extension whose
dimension is no larger than that of the source. -/
theorem isCohenMacaulay_of_finiteFlat_or_flat_of_ringKrullDim_le
    {R S : Type u} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S]
    [IsNoetherianRing R] [IsNoetherianRing S]
    (f : R →+* S) [IsLocalHom f]
    (hR : Formalization.Books.Algebra.Unit103.IsCohenMacaulay R R)
    (hcase :
      (RingHom.Finite f ∧ RingHom.Flat f) ∨
        (RingHom.Flat f ∧ ringKrullDim S ≤ ringKrullDim R)) :
    Formalization.Books.Algebra.Unit103.IsCohenMacaulay S S ∧
      ringKrullDim R = ringKrullDim S := by
  have aux : ∀ (hflat : RingHom.Flat f),
      ringKrullDim S ≤ ringKrullDim R →
        Formalization.Books.Algebra.Unit103.IsCohenMacaulay S S ∧
          ringKrullDim R = ringKrullDim S := by
    intro hflat hdim
    let _ : Algebra R S := f.toAlgebra
    let _ : IsLocalHom (algebraMap R S) := by
      change IsLocalHom f
      infer_instance
    have hRdim :
        ((Formalization.Books.Algebra.Unit72.localDepth R R : ℕ∞) :
          WithBot ℕ∞) = ringKrullDim R := by
      calc
        ((Formalization.Books.Algebra.Unit72.localDepth R R : ℕ∞) :
            WithBot ℕ∞) = Module.supportDim R R := hR
        _ = ringKrullDim R := Module.supportDim_self_eq_ringKrullDim R
    obtain ⟨ys, hregR, hlen⟩ :=
      Formalization.Books.Algebra.Unit72.regular_sequence_extend_to_localDepth
        (R := R) (M := R) []
        (@RingTheory.Sequence.IsRegular.nil R R _ _ _ inferInstance)
    have hmemR : ∀ x ∈ ys, x ∈ IsLocalRing.maximalIdeal R := by
      intro x hx
      by_contra hxmax
      have hxunit : IsUnit x := IsLocalRing.notMem_maximalIdeal.mp hxmax
      have hxideal : x ∈ Ideal.ofList ys := Ideal.subset_span hx
      have htop : Ideal.ofList ys = ⊤ :=
        Ideal.eq_top_of_isUnit_mem _ hxideal hxunit
      have htop' : (⊤ : Submodule R R) =
          Ideal.ofList ys • (⊤ : Submodule R R) := by
        rw [Ideal.smul_eq_mul, Ideal.mul_top, htop]
      exact hregR.top_ne_smul htop'
    let _ : Module.Flat R S := RingHom.flat_algebraMap_iff.mp (by
      simpa [RingHom.algebraMap_toAlgebra] using hflat)
    let _ : Module.FaithfullyFlat R S :=
      Module.FaithfullyFlat.of_flat_of_isLocalHom
    have hregS : RingTheory.Sequence.IsRegular S
        (ys.map (algebraMap R S)) :=
      RingTheory.Sequence.IsRegular.of_faithfullyFlat hregR
    have hmemS : ∀ x ∈ ys.map (algebraMap R S),
        x ∈ IsLocalRing.maximalIdeal S := by
      intro z hz
      obtain ⟨x, hx, hzx⟩ := List.mem_map.mp hz
      rw [← hzx]
      exact map_nonunit (algebraMap R S) x (hmemR x hx)
    have hSmax : IsLocalRing.maximalIdeal S • (⊤ : Submodule S S) ≠ ⊤ :=
      Formalization.Books.Algebra.Unit72.smul_top_ne_top_of_le_ring_jacobson
        (IsLocalRing.maximalIdeal S) S
        (IsLocalRing.maximalIdeal_le_jacobson (⊥ : Ideal S))
    have hdepthS :
        ((ys.map (algebraMap R S)).length : ℕ∞) ≤
          Formalization.Books.Algebra.Unit72.localDepth S S := by
      unfold Formalization.Books.Algebra.Unit72.localDepth
        Formalization.Books.Algebra.Unit72.depth
      rw [dif_neg hSmax]
      apply le_sSup
      exact ⟨ys.map (algebraMap R S), by simp, hmemS, hregS⟩
    have hdepthRS :
        Formalization.Books.Algebra.Unit72.localDepth R R ≤
          Formalization.Books.Algebra.Unit72.localDepth S S := by
      rw [hlen]
      simpa using hdepthS
    have hdepthRS' :
        ((Formalization.Books.Algebra.Unit72.localDepth R R : ℕ∞) :
          WithBot ℕ∞) ≤
          ((Formalization.Books.Algebra.Unit72.localDepth S S : ℕ∞) :
            WithBot ℕ∞) :=
      WithBot.coe_le_coe.mpr hdepthRS
    have hSdepth :
        ((Formalization.Books.Algebra.Unit72.localDepth S S : ℕ∞) :
          WithBot ℕ∞) ≤ ringKrullDim S := by
      calc
        ((Formalization.Books.Algebra.Unit72.localDepth S S : ℕ∞) :
            WithBot ℕ∞) ≤ Module.supportDim S S :=
          Formalization.Books.Algebra.Unit72.supportDim_ge_localDepth
        _ = ringKrullDim S := Module.supportDim_self_eq_ringKrullDim S
    have hdimRS : ringKrullDim R = ringKrullDim S := by
      apply le_antisymm
      · calc
          ringKrullDim R =
              ((Formalization.Books.Algebra.Unit72.localDepth R R : ℕ∞) :
                WithBot ℕ∞) := hRdim.symm
          _ ≤ ((Formalization.Books.Algebra.Unit72.localDepth S S : ℕ∞) :
              WithBot ℕ∞) := hdepthRS'
          _ ≤ ringKrullDim S := hSdepth
      · exact hdim
    have hCMS : Formalization.Books.Algebra.Unit103.IsCohenMacaulay S S := by
      unfold Formalization.Books.Algebra.Unit103.IsCohenMacaulay
      apply le_antisymm
      · exact Formalization.Books.Algebra.Unit72.supportDim_ge_localDepth
      · calc
          Module.supportDim S S = ringKrullDim S :=
            Module.supportDim_self_eq_ringKrullDim S
          _ = ringKrullDim R := hdimRS.symm
          _ = ((Formalization.Books.Algebra.Unit72.localDepth R R : ℕ∞) :
              WithBot ℕ∞) := hRdim.symm
          _ ≤ ((Formalization.Books.Algebra.Unit72.localDepth S S : ℕ∞) :
              WithBot ℕ∞) := hdepthRS'
    exact ⟨hCMS, hdimRS⟩
  rcases hcase with ⟨hfinite, hflat⟩ | ⟨hflat, hdim⟩
  · exact aux hflat
      (Formalization.Books.Algebra.Unit112.integral_ringKrullDim_le_and_closedPoint_map
        f hfinite.to_isIntegral).1
  · exact aux hflat hdim

end

end Formalization.Books.Algebra.Unit112
