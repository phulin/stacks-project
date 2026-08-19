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
  let _ : Algebra R S := f.toAlgebra
  intro hmap hsurj
  rw [← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim,
    ← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
  apply Formalization.Books.Topology.Unit19.topologicalKrullDim_le_of_surjective_of_specializing_or_generalizing
    (PrimeSpectrum.comap f) (PrimeSpectrum.continuous_comap f) hsurj
  rcases hmap with hgu | hgd
  · exact Or.inl ((Formalization.Books.Algebra.Unit41.hasGoingUp_iff_specializingMap).mp
      (show Algebra.HasGoingUp R S from hgu))
  · exact Or.inr ((Formalization.Books.Algebra.Unit41.hasGoingDown_iff_generalizingMap).mp
      (show Algebra.HasGoingDown R S from hgd))

/-- Under going up, the contraction of a maximal ideal is maximal. -/
theorem isMaximal_comap_of_goingUp
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) :
    letI : Algebra R S := f.toAlgebra
    Algebra.HasGoingUp R S →
      ∀ q : Ideal S, q.IsMaximal → (q.comap f).IsMaximal := by
  let _ : Algebra R S := f.toAlgebra
  intro hgu q hq
  let _ : Algebra.HasGoingUp R S := hgu
  let _ : q.IsPrime := hq.isPrime
  apply Ideal.isMaximal_def.mpr
  constructor
  · intro htop
    have hmap : (q.comap f).map f ≤ q := by
      rw [Ideal.map_le_iff_le_comap]
    rw [htop, Ideal.map_top] at hmap
    exact hq.ne_top (top_unique hmap)
  · intro J hJ
    by_contra hJtop
    obtain ⟨m, hm, hJm⟩ := Ideal.exists_le_maximal J hJtop
    have hpm : q.comap f < m := lt_of_lt_of_le hJ hJm
    let _ : m.IsPrime := hm.isPrime
    obtain ⟨Q, hqQ, hQprime, hQover⟩ :=
      Algebra.HasGoingUp.exists_ideal_ge_liesOver_of_lt q hpm
    have hqeqQ : q = Q := hq.eq_of_le hQprime.ne_top hqQ
    have hQunder : m = Q.comap f := by
      simpa [Ideal.under_def, RingHom.algebraMap_toAlgebra] using hQover.over
    have heq : m = q.comap f := hQunder.trans
      (congrArg (fun I : Ideal S => I.comap f) hqeqQ.symm)
    exact hpm.ne heq.symm

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

/-- An injective integral ring map preserves Krull dimension. -/
theorem integral_subring_ringKrullDim_eq
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    (hinj : Function.Injective f) (hf : f.IsIntegral) :
    ringKrullDim R = ringKrullDim S := by
  let _ : Algebra R S := f.toAlgebra
  let _ : Algebra.IsIntegral R S := ⟨hf⟩
  have hgu : Algebra.HasGoingUp R S := by infer_instance
  have hsurj : Function.Surjective (PrimeSpectrum.comap f) :=
    Formalization.Books.Algebra.Unit36.primeSpectrum_comap_surjective_of_integral f hf hinj
  have h₁ : ringKrullDim R ≤ ringKrullDim S :=
    dimension_le_of_goingUp_or_goingDown f (Or.inl hgu) hsurj
  have h₂ : ringKrullDim S ≤ ringKrullDim R :=
    (integral_ringKrullDim_le_and_closedPoint_map f hf).1
  exact le_antisymm h₁ h₂

/-! ## The local ring of a fibre -/

/-- The ideal `p S_q`, expressed by mapping `p` along `R → S_q`. -/
noncomputable def fibreIdealInLocalization
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    (p : PrimeSpectrum R) (q : PrimeSpectrum S) :
    Ideal (Localization.AtPrime q.asIdeal) :=
  p.asIdeal.map ((algebraMap S (Localization.AtPrime q.asIdeal)).comp f)

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
  letI : Algebra R S := f.toAlgebra
  exact PrimeSpectrum.preimageEquivFiber R S p ⟨q, by
    simpa [RingHom.algebraMap_toAlgebra] using hq⟩

/-- The localization of the tensor-product fibre at the prime corresponding
to `q`. -/
noncomputable abbrev tensorLocalRingOfFibre
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    (p : PrimeSpectrum R) (q : PrimeSpectrum S)
    (hq : PrimeSpectrum.comap f q = p) :
    Type u := by
  letI : Algebra R S := f.toAlgebra
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
    change p.asIdeal ≤ q.asIdeal.comap f
    simpa [PrimeSpectrum.comap_asIdeal] using
      (congrArg PrimeSpectrum.asIdeal hq).symm.le
  have hqcomap : qbar.asIdeal.comap (Ideal.Quotient.mk I) = q.asIdeal := by
    change (q.asIdeal.map (Ideal.Quotient.mk I)).comap (Ideal.Quotient.mk I) = q.asIdeal
    rw [Ideal.comap_map_of_surjective (f := Ideal.Quotient.mk I)
      Ideal.Quotient.mk_surjective]
    apply sup_eq_left.mpr
    intro x hx
    rw [Ideal.mem_comap] at hx
    have hx0 : Ideal.Quotient.mk I x = 0 := by simpa using hx
    exact hIle (Ideal.Quotient.eq_zero_iff_mem.mp hx0)
  have hM : M.map (Ideal.Quotient.mk I) = qbar.asIdeal.primeCompl := by
    rw [← hqcomap]
    exact Ideal.map_primeCompl_comap_of_surjective
      Ideal.Quotient.mk_surjective qbar.asIdeal
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
  simpa [localRingOfFibre, fibreIdealInLocalization, fibreIdealInTarget,
    Q, Sp, I, qbar, Ideal.map_map] using
    (⟨(IsLocalization.algEquiv qbar.asIdeal.primeCompl
      (Localization.AtPrime qbar.asIdeal) Q).symm.toRingEquiv⟩ :
      Nonempty (Q ≃+* Localization.AtPrime qbar.asIdeal))

/-- The quotient presentation of the local ring of a fibre is canonically
ring-equivalent to the localization of the tensor-product fibre
`S ⊗_R κ(p)`. -/
theorem localRingOfFibre_equiv_tensor_fibre
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    (p : PrimeSpectrum R) (q : PrimeSpectrum S)
    (hq : PrimeSpectrum.comap f q = p) :
    Nonempty
      (localRingOfFibre f p q hq ≃+* tensorLocalRingOfFibre f p q hq) := by
  letI : Algebra R S := f.toAlgebra
  let q' : {q : PrimeSpectrum S // PrimeSpectrum.comap (algebraMap R S) q = p} :=
    ⟨q, by simpa [RingHom.algebraMap_toAlgebra] using hq⟩
  let qbar : PrimeSpectrum (p.asIdeal.Fiber S) :=
    PrimeSpectrum.preimageEquivFiber R S p q'
  have hqbar : qbar.asIdeal.comap Algebra.TensorProduct.includeRight = q.asIdeal := by
    have h := (PrimeSpectrum.preimageEquivFiber R S p).symm_apply_apply q'
    have h' := congrArg (fun x : {q : PrimeSpectrum S //
        PrimeSpectrum.comap (algebraMap R S) q = p} => x.1.asIdeal) h
    simpa [qbar] using h'
  have e := Ideal.Fiber.algEquivAux₂ p.asIdeal qbar.asIdeal
  simpa [localRingOfFibre, fibreIdealInLocalization, tensorLocalRingOfFibre,
    tensorFibrePrime, qbar, q', hqbar, Ideal.map_map,
    RingHom.algebraMap_toAlgebra] using
    (⟨e.symm.toRingEquiv⟩ : Nonempty
      ((Localization.AtPrime qbar.asIdeal.comap Algebra.TensorProduct.includeRight ⧸
          (p.asIdeal.map f).map
            (algebraMap S
              (Localization.AtPrime qbar.asIdeal.comap Algebra.TensorProduct.includeRight))) ≃+*
        Localization.AtPrime qbar.asIdeal))

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
  letI : Algebra R S := f.toAlgebra
  have hcomap : q.asIdeal.comap (algebraMap R S) = p.asIdeal := by
    simpa [PrimeSpectrum.comap_asIdeal, RingHom.algebraMap_toAlgebra] using
      congrArg PrimeSpectrum.asIdeal hq
  let φ := Localization.localRingHom p.asIdeal q.asIdeal f hcomap.symm
  letI : Algebra (Localization.AtPrime p.asIdeal)
      (Localization.AtPrime q.asIdeal) := φ.toAlgebra
  have hideal :
      (IsLocalRing.maximalIdeal (Localization.AtPrime p.asIdeal)).map
          (algebraMap (Localization.AtPrime p.asIdeal)
            (Localization.AtPrime q.asIdeal)) =
        fibreIdealInLocalization f p q := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal]
    rw [Ideal.map_map]
    ext r
    simpa [φ, RingHom.algebraMap_toAlgebra] using
      (Localization.localRingHom_to_map p.asIdeal q.asIdeal f hcomap.symm r)
  have hPover :
      (IsLocalRing.maximalIdeal (Localization.AtPrime q.asIdeal)).LiesOver
        (IsLocalRing.maximalIdeal (Localization.AtPrime p.asIdeal)) := by
    exact (Ideal.liesOver_iff _ _).mpr
      (IsLocalRing.maximalIdeal_comap φ).symm
  rw [Formalization.Books.Algebra.Unit60.ringKrullDim_le_iff_maximal_height_le]
  intro m hm
  have hm_eq : m = IsLocalRing.maximalIdeal (Localization.AtPrime q.asIdeal) :=
    (IsLocalRing.maximal_ideal_unique _).unique m hm
  rw [hm_eq]
  let P := IsLocalRing.maximalIdeal (Localization.AtPrime q.asIdeal)
  let p₀ := IsLocalRing.maximalIdeal (Localization.AtPrime p.asIdeal)
  let _ : P.LiesOver p₀ := hPover
  let _ : (P.map (Ideal.Quotient.mk (p₀.map
      (algebraMap (Localization.AtPrime p.asIdeal)
        (Localization.AtPrime q.asIdeal)))).IsPrime :=
    Ideal.isPrime_map_quotientMk_of_isPrime hPover.over
  have hheight := Ideal.height_le_height_add_of_liesOver p₀ P
  have hbase : p₀.height ≤ ringKrullDim (Localization.AtPrime p.asIdeal) :=
    le_of_eq IsLocalRing.maximalIdeal_height_eq_ringKrullDim
  have hquot :
      (P.map (Ideal.Quotient.mk (p₀.map
        (algebraMap (Localization.AtPrime p.asIdeal)
          (Localization.AtPrime q.asIdeal))))).height ≤
        ringKrullDim
          ((Localization.AtPrime q.asIdeal) ⧸
            p₀.map (algebraMap (Localization.AtPrime p.asIdeal)
              (Localization.AtPrime q.asIdeal))) :=
    Ideal.height_le_ringKrullDim_of_isPrime
  have hquot_eq :
      ringKrullDim
          ((Localization.AtPrime q.asIdeal) ⧸
            p₀.map (algebraMap (Localization.AtPrime p.asIdeal)
              (Localization.AtPrime q.asIdeal))) =
        ringKrullDim (localRingOfFibre f p q hq) := by
    simpa [localRingOfFibre, p₀, hideal]
  calc
    P.height ≤ p₀.height +
        (P.map (Ideal.Quotient.mk (p₀.map
          (algebraMap (Localization.AtPrime p.asIdeal)
            (Localization.AtPrime q.asIdeal)))).height := hheight
    _ ≤ ringKrullDim (Localization.AtPrime p.asIdeal) +
        ringKrullDim (localRingOfFibre f p q hq) := by
      rw [hquot_eq]
      exact add_le_add hbase hquot

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
  letI : Algebra R S := f.toAlgebra
  let _ : Algebra.HasGoingDown R S := hGD
  have hcomap : q.asIdeal.comap (algebraMap R S) = p.asIdeal := by
    simpa [PrimeSpectrum.comap_asIdeal, RingHom.algebraMap_toAlgebra] using
      congrArg PrimeSpectrum.asIdeal hq
  have hqover : q.asIdeal.LiesOver p.asIdeal := by
    exact (Ideal.liesOver_iff _ _).mpr hcomap.symm
  let _ : q.asIdeal.LiesOver p.asIdeal := hqover
  let _ : (q.asIdeal.map (Ideal.Quotient.mk (p.asIdeal.map f))).IsPrime :=
    Ideal.isPrime_map_quotientMk_of_isPrime hqover.over
  have hheight :=
    Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown p.asIdeal q.asIdeal
  have hbase :
      ringKrullDim (Localization.AtPrime p.asIdeal) = p.asIdeal.height :=
    IsLocalization.AtPrime.ringKrullDim_eq_height p.asIdeal
      (Localization.AtPrime p.asIdeal)
  let qbar := fibreQuotientPrime f p q hq
  have hqbar :
      ringKrullDim (Localization.AtPrime qbar.asIdeal) =
        (q.asIdeal.map (Ideal.Quotient.mk (p.asIdeal.map f))).height := by
    simpa [qbar, fibreQuotientPrime, fibreIdealInTarget] using
      (IsLocalization.AtPrime.ringKrullDim_eq_height qbar.asIdeal
        (Localization.AtPrime qbar.asIdeal))
  have hfibre :
      ringKrullDim (localRingOfFibre f p q hq) =
        ringKrullDim (Localization.AtPrime qbar.asIdeal) := by
    obtain ⟨e⟩ := localRingOfFibre_equiv_localized_quotient f p q hq
    exact ringKrullDim_eq_of_ringEquiv e
  calc
    ringKrullDim (Localization.AtPrime q.asIdeal) = q.asIdeal.height :=
      IsLocalization.AtPrime.ringKrullDim_eq_height q.asIdeal
        (Localization.AtPrime q.asIdeal)
    _ = p.asIdeal.height +
        (q.asIdeal.map (Ideal.Quotient.mk (p.asIdeal.map f))).height := by
      simpa [RingHom.algebraMap_toAlgebra] using hheight
    _ = ringKrullDim (Localization.AtPrime p.asIdeal) +
        ringKrullDim (localRingOfFibre f p q hq) := by
      rw [← hbase, ← hqbar, ← hfibre]

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
