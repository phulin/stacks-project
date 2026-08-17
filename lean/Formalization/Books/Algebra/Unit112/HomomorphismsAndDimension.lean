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
  sorry

/-- Under going up, the contraction of a maximal ideal is maximal. -/
theorem isMaximal_comap_of_goingUp
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) :
    letI : Algebra R S := f.toAlgebra
    Algebra.HasGoingUp R S →
      ∀ q : Ideal S, q.IsMaximal → (q.comap f).IsMaximal := by
  sorry

/-! ## Integral extensions -/

/-- An integral ring map lowers Krull dimension and sends closed points of the
spectrum to closed points. -/
theorem integral_ringKrullDim_le_and_closedPoint_map
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    (hf : f.IsIntegral) :
    ringKrullDim S ≤ ringKrullDim R ∧
      ∀ q : PrimeSpectrum S, q.asIdeal.IsMaximal →
        (q.asIdeal.comap f).IsMaximal := by
  sorry

/-- An injective integral ring map preserves Krull dimension. -/
theorem integral_subring_ringKrullDim_eq
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    (hinj : Function.Injective f) (hf : f.IsIntegral) :
    ringKrullDim R = ringKrullDim S := by
  sorry

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
  sorry

/-- The quotient presentation of the local ring of a fibre is canonically
ring-equivalent to the localization of the tensor-product fibre
`S ⊗_R κ(p)`. -/
theorem localRingOfFibre_equiv_tensor_fibre
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    (p : PrimeSpectrum R) (q : PrimeSpectrum S)
    (hq : PrimeSpectrum.comap f q = p) :
    Nonempty
      (localRingOfFibre f p q hq ≃+* tensorLocalRingOfFibre f p q hq) := by
  sorry

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
