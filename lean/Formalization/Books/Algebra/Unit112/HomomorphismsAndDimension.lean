import Formalization.Books.Algebra.Unit41.GoingUpAndGoingDown
import Formalization.Books.Algebra.Unit60.Dimension
import Formalization.Books.Algebra.Unit103.CohenMacaulayModules
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

/-- Under going up, the contraction of a maximal ideal is maximal. -/
theorem isMaximal_comap_of_goingUp
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) :
    letI : Algebra R S := f.toAlgebra
    Algebra.HasGoingUp R S →
      ∀ q : Ideal S, q.IsMaximal → (q.comap f).IsMaximal := by
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

/-! ## Dimension of a base, fibre, and total ring -/

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
  sorry

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
  sorry

/-! ## Regular and Cohen--Macaulay consequences -/

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
  sorry

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
  sorry

end

end Formalization.Books.Algebra.Unit112
