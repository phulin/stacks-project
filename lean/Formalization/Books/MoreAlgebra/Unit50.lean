import Formalization.Books.MoreAlgebra.Unit12
import Formalization.Books.MoreAlgebra.Unit46
import Formalization.Books.MoreAlgebra.Unit45
import Formalization.Books.MoreAlgebra.Unit49
import Mathlib.RingTheory.DedekindDomain.Basic
import Mathlib.RingTheory.EssentialFiniteness
import Mathlib.RingTheory.MvPowerSeries.Basic
import Mathlib.RingTheory.MvPowerSeries.NoZeroDivisors
import Mathlib.RingTheory.RingHom.Finite
import Mathlib.RingTheory.RingHom.QuasiFinite

/-!
# More on Algebra, Chapter 50: G-rings

This file records the source definitions and theorem interfaces for G-rings.
Formal fibres use the canonical adic completion and tensor-product APIs; the
regularity predicates are the geometric-regularity predicates from the
preceding chapters.
-/

namespace Formalization.Books.MoreAlgebra.Unit50

open CategoryTheory
open Formalization.Books.Algebra.Unit96
open Formalization.Books.Algebra.Unit154
open Formalization.Books.Algebra.Unit155
open Formalization.Books.MoreAlgebra.Unit12
open Formalization.Books.MoreAlgebra.Unit46
open Formalization.Books.MoreAlgebra.Unit40
open Formalization.Books.MoreAlgebra.Unit41
open scoped TensorProduct

noncomputable section

universe u

/-! ## Formal fibres and the definition of a G-ring -/

/-- The completion of the localization of a ring at a prime. -/
noncomputable abbrev completionAtPrime
    (R : Type u) [CommRing R] (p : PrimeSpectrum R) : Type u :=
  ringCompletion
    (IsLocalRing.maximalIdeal (Localization.AtPrime p.asIdeal))

noncomputable instance completionAtPrimeCommRing
    (R : Type u) [CommRing R] (p : PrimeSpectrum R) :
    CommRing (completionAtPrime R p) := by
  change CommRing
    (ringCompletion
      (IsLocalRing.maximalIdeal (Localization.AtPrime p.asIdeal)))
  infer_instance

/-- The canonical map from a ring to the completion at one of its primes. -/
noncomputable def completionAtPrimeMap
    (R : Type u) [CommRing R] (p : PrimeSpectrum R) :
    R →+* completionAtPrime R p :=
  (algebraMap (Localization.AtPrime p.asIdeal) (completionAtPrime R p)).comp
    (algebraMap R (Localization.AtPrime p.asIdeal))

noncomputable instance completionAtPrimeAlgebra
    (R : Type u) [CommRing R] (p : PrimeSpectrum R) :
    Algebra R (completionAtPrime R p) :=
  (completionAtPrimeMap R p).toAlgebra

@[instance_reducible] noncomputable def primeResidueFieldAlgebra
    (R : Type u) [CommRing R] (q : PrimeSpectrum R) :
    Algebra R q.asIdeal.ResidueField :=
  Algebra.compHom q.asIdeal.ResidueField
    (algebraMap R (Localization.AtPrime q.asIdeal))

/-- The formal fibre of `R` at a pair of primes `q ≤ p`, written as
`(Rₚ)^ ∧ ⊗_R κ(q)`.  The type is also useful without the order assumption. -/
noncomputable abbrev formalFiberAt
    (R : Type u) [CommRing R] (p q : PrimeSpectrum R) : Type u :=
  letI : Algebra R (completionAtPrime R p) :=
    completionAtPrimeAlgebra R p
  letI : Algebra R q.asIdeal.ResidueField :=
    primeResidueFieldAlgebra R q
  letI : Module R (completionAtPrime R p) := Algebra.toModule
  letI : Module R q.asIdeal.ResidueField := Algebra.toModule
  completionAtPrime R p ⊗[R] q.asIdeal.ResidueField

/-- Geometric regularity of a formal fibre at a pair of primes. -/
def IsGeometricallyRegularFormalFiberAt
    (R : Type u) [CommRing R] (p q : PrimeSpectrum R) : Prop :=
  letI : Algebra R (completionAtPrime R p) :=
    completionAtPrimeAlgebra R p
  letI : Algebra R q.asIdeal.ResidueField :=
    primeResidueFieldAlgebra R q
  letI : Module R (completionAtPrime R p) := Algebra.toModule
  letI : Module R q.asIdeal.ResidueField := Algebra.toModule
  letI : Algebra q.asIdeal.ResidueField
      (completionAtPrime R p ⊗[R] q.asIdeal.ResidueField) :=
    Algebra.TensorProduct.rightAlgebra
  IsGeometricallyRegular q.asIdeal.ResidueField
    (completionAtPrime R p ⊗[R] q.asIdeal.ResidueField)

/-- Regularity of a formal fibre at a pair of primes. -/
def IsRegularFormalFiberAt
    (R : Type u) [CommRing R] (p q : PrimeSpectrum R) : Prop :=
  letI : Algebra R (completionAtPrime R p) :=
    completionAtPrimeAlgebra R p
  letI : Algebra R q.asIdeal.ResidueField :=
    primeResidueFieldAlgebra R q
  letI : Module R (completionAtPrime R p) := Algebra.toModule
  letI : Module R q.asIdeal.ResidueField := Algebra.toModule
  letI : Algebra q.asIdeal.ResidueField
      (completionAtPrime R p ⊗[R] q.asIdeal.ResidueField) :=
    Algebra.TensorProduct.rightAlgebra
  IsRegularRingPredicate
    (completionAtPrime R p ⊗[R] q.asIdeal.ResidueField)

/-- All formal fibres of a ring are geometrically regular. -/
def HasGeometricallyRegularFormalFibers
    (R : Type u) [CommRing R] : Prop :=
  ∀ (q p : PrimeSpectrum R), q.asIdeal ≤ p.asIdeal →
    IsGeometricallyRegularFormalFiberAt R p q

/-- All formal fibres of a ring are regular as rings. -/
def HasRegularFormalFibers
    (R : Type u) [CommRing R] : Prop :=
  ∀ (q p : PrimeSpectrum R), q.asIdeal ≤ p.asIdeal →
    IsRegularFormalFiberAt R p q

/-- The formal fibre of a Noetherian local ring at a prime. -/
noncomputable abbrev formalFiber
    (A : Type u) [CommRing A] [IsLocalRing A]
    (q : PrimeSpectrum A) : Type u :=
  ringCompletion (IsLocalRing.maximalIdeal A) ⊗[A] q.asIdeal.ResidueField

/-- All formal fibres of a local ring are geometrically regular. -/
def HasGeometricallyRegularLocalFormalFibers
    (A : Type u) [CommRing A] [IsLocalRing A] : Prop :=
  ∀ q : PrimeSpectrum A,
    let C := ringCompletion (IsLocalRing.maximalIdeal A)
    letI : Algebra A C := (algebraMap A C).toAlgebra
    letI : Algebra A q.asIdeal.ResidueField :=
      primeResidueFieldAlgebra A q
    letI : Module A C := Algebra.toModule
    letI : Module A q.asIdeal.ResidueField := Algebra.toModule
    let F := C ⊗[A] q.asIdeal.ResidueField
    letI : Algebra q.asIdeal.ResidueField F :=
      Algebra.TensorProduct.rightAlgebra
    IsGeometricallyRegular q.asIdeal.ResidueField F

/-- The first and third displayed presentations of a formal fibre are
canonically isomorphic: completion commutes with passage to the residue-field
quotient in this local Noetherian situation. -/
theorem formalFiber_quotient_presentation
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (q : PrimeSpectrum A) :
    let C := ringCompletion (IsLocalRing.maximalIdeal A)
    letI : Algebra A C := (algebraMap A C).toAlgebra
    letI : Algebra A q.asIdeal.ResidueField :=
      primeResidueFieldAlgebra A q
    letI : Module A C := Algebra.toModule
    letI : Module A q.asIdeal.ResidueField := Algebra.toModule
    let F := C ⊗[A] q.asIdeal.ResidueField
    let Q := A ⧸ q.asIdeal
    let Cq := ringCompletion
      (Ideal.map (Ideal.Quotient.mk q.asIdeal) (IsLocalRing.maximalIdeal A))
    letI : Algebra Q Cq := (algebraMap Q Cq).toAlgebra
    letI : Algebra Q q.asIdeal.ResidueField := inferInstance
    letI : Module Q Cq := Algebra.toModule
    letI : Module Q q.asIdeal.ResidueField := Algebra.toModule
    let G := Cq ⊗[Q] q.asIdeal.ResidueField
    Nonempty (F ≃+* G) := by
  sorry

/-- All formal fibres of a local ring are regular as rings. -/
def HasRegularLocalFormalFibers
    (A : Type u) [CommRing A] [IsLocalRing A] : Prop :=
  ∀ q : PrimeSpectrum A, IsRegularRingPredicate (formalFiber A q)

/-- A ring is a G-ring when it is Noetherian and every local-to-completion
map is regular. -/
def IsGRing (R : Type u) [CommRing R] : Prop :=
  IsNoetherianRing R ∧
    ∀ p : PrimeSpectrum R,
      IsRegularRingMap
        (algebraMap (Localization.AtPrime p.asIdeal)
          (completionAtPrime R p))

/-- For a Noetherian local ring, regularity of the completion map is equivalent
to geometric regularity of all its formal fibres. -/
theorem regular_completion_iff_geometricallyRegularLocalFormalFibers
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A] :
    IsRegularRingMap
        (algebraMap A (ringCompletion (IsLocalRing.maximalIdeal A))) ↔
      HasGeometricallyRegularLocalFormalFibers A := by
  sorry

/-- For a `ℚ`-algebra, regularity of every formal fibre implies geometric
regularity of every formal fibre. -/
theorem geometricallyRegularLocalFormalFibers_of_QAlgebra
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    [Algebra ℚ A]
    (hregular : HasRegularLocalFormalFibers A) :
    HasGeometricallyRegularLocalFormalFibers A := by
  sorry

/-- A G-ring can equivalently be checked by the geometric regularity of every
formal fibre `(Rₚ)^ ∧ ⊗_R κ(q)` for `q ≤ p`. -/
theorem isGRing_iff_geometricallyRegularFormalFibers
    {R : Type u} [CommRing R] :
    IsGRing R ↔
      IsNoetherianRing R ∧ HasGeometricallyRegularFormalFibers R := by
  sorry

/-- The informal local-ring formulation of the G-ring condition. -/
theorem isGRing_iff_all_localizations_have_geometricallyRegularFormalFibers
    {R : Type u} [CommRing R] :
    IsGRing R ↔
      IsNoetherianRing R ∧
        ∀ p : PrimeSpectrum R,
          HasGeometricallyRegularLocalFormalFibers
            (Localization.AtPrime p.asIdeal) := by
  sorry

/-! ## The quotient criterion -/

/-- The formal fibre after replacing `R` by `R / q`, at a prime of the
quotient. -/
noncomputable abbrev quotientFormalFiber
    (R : Type u) [CommRing R] (q : PrimeSpectrum R)
    (p : PrimeSpectrum (R ⧸ q.asIdeal)) : Type u :=
  ringCompletion
      (IsLocalRing.maximalIdeal (Localization.AtPrime p.asIdeal)) ⊗[
        R ⧸ q.asIdeal] q.asIdeal.ResidueField

/-- The quotient-form geometric formal-fibre condition. -/
def HasGeometricallyRegularQuotientFormalFibers
    (R : Type u) [CommRing R] : Prop :=
  ∀ (q : PrimeSpectrum R) (p : PrimeSpectrum (R ⧸ q.asIdeal)),
    let C := ringCompletion
      (IsLocalRing.maximalIdeal (Localization.AtPrime p.asIdeal))
    letI : Algebra (R ⧸ q.asIdeal) C := (algebraMap (R ⧸ q.asIdeal) C).toAlgebra
    letI : Algebra (R ⧸ q.asIdeal) q.asIdeal.ResidueField := inferInstance
    letI : Module (R ⧸ q.asIdeal) C := Algebra.toModule
    letI : Module (R ⧸ q.asIdeal) q.asIdeal.ResidueField := Algebra.toModule
    let F := C ⊗[R ⧸ q.asIdeal] q.asIdeal.ResidueField
    letI : Algebra q.asIdeal.ResidueField F :=
      Algebra.TensorProduct.rightAlgebra
    IsGeometricallyRegular q.asIdeal.ResidueField F

/-- The easy prime-pair criterion for G-rings. -/
theorem isGRing_iff_geometricallyRegular_quotientFormalFibers
    {R : Type u} [CommRing R] [IsNoetherianRing R] :
    IsGRing R ↔ HasGeometricallyRegularQuotientFormalFibers R := by
  sorry

/-! ## Quasi-finite ascent -/

/-- Geometric regularity of one formal fibre ascends across a finite-type map
which is quasi-finite at the target prime. -/
theorem geometricallyRegularFormalFiberAt_of_quasiFiniteAt
    {R S : Type u} [CommRing R] [CommRing S]
    [IsNoetherianRing R] [IsNoetherianRing S]
    (f : R →+* S)
    (hfinite : RingHom.FiniteType f)
    (q p : PrimeSpectrum R) (q' p' : PrimeSpectrum S)
    (hq : q'.asIdeal.comap f = q.asIdeal)
    (hp : p'.asIdeal.comap f = p.asIdeal)
    (hqp : q.asIdeal ≤ p.asIdeal)
    (hqp' : q'.asIdeal ≤ p'.asIdeal)
    (hquasi : RingHom.QuasiFiniteAt f p'.asIdeal)
    (hgeom : IsGeometricallyRegularFormalFiberAt R p q) :
    IsGeometricallyRegularFormalFiberAt S p' q' := by
  sorry

/-- The preceding ascent statement for all formal fibres over a fixed target
prime. -/
theorem hasGeometricallyRegularFormalFibersAt_of_quasiFiniteAt
    {R S : Type u} [CommRing R] [CommRing S]
    [IsNoetherianRing R] [IsNoetherianRing S]
    (f : R →+* S) (p' : PrimeSpectrum S)
    (hfinite : RingHom.FiniteType f)
    (hquasi : RingHom.QuasiFiniteAt f p'.asIdeal)
    (hR : HasGeometricallyRegularFormalFibers R) :
    ∀ (q' : PrimeSpectrum S), q'.asIdeal ≤ p'.asIdeal →
      IsGeometricallyRegularFormalFiberAt S p' q' := by
  sorry

/-- A quasi-finite finite-type extension of a G-ring is a G-ring. -/
theorem isGRing_of_quasiFinite_finiteType
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) [IsNoetherianRing R] [IsNoetherianRing S]
    (hfinite : RingHom.FiniteType f)
    (hquasi : RingHom.QuasiFinite f)
    (hR : IsGRing R) : IsGRing S := by
  sorry

/-! ## Finite-free and positive-characteristic criteria -/

/-- The finite-free test for G-rings. -/
theorem isGRing_iff_finiteFree_maps_have_regularFormalFibers
    {R : Type u} [CommRing R] [IsNoetherianRing R] :
    IsGRing R ↔
      ∀ (S : Type u) [CommRing S] (f : R →+* S),
        letI : Algebra R S := f.toAlgebra
        RingHom.Finite f → Module.Free R S → HasRegularFormalFibers S := by
  sorry

/-- The polynomial-power-series ring used in the positive-characteristic
helper lemma. -/
noncomputable instance powerSeriesPolynomialRingIsDomain
    (k : Type u) [Field k] (n m : ℕ) :
    IsDomain (powerSeriesPolynomialRing k n m) := by
  let _ : IsDomain (MvPowerSeries (Fin n) k) :=
    NoZeroDivisors.to_isDomain _
  dsimp [powerSeriesPolynomialRing]
  infer_instance

/-- The source's positive-characteristic helper: the generic formal fibre of
`k[[x₁, ..., xₙ]][y₁, ..., yₘ]` is geometrically regular. -/
theorem geometricallyRegular_fractionField_formalFiber_powerSeriesPolynomial
    (k : Type u) [Field k] (n m : ℕ)
    (p : PrimeSpectrum (powerSeriesPolynomialRing k n m)) :
    let A := powerSeriesPolynomialRing k n m
    let K := FractionRing A
    letI : Algebra A K := (algebraMap A K).toAlgebra
    letI : Algebra A (completionAtPrime A p) := completionAtPrimeAlgebra A p
    letI : Module A (completionAtPrime A p) := Algebra.toModule
    letI : Module A K := Algebra.toModule
    letI : Algebra K (completionAtPrime A p ⊗[A] K) :=
      Algebra.TensorProduct.rightAlgebra
    IsGeometricallyRegular K (completionAtPrime A p ⊗[A] K) := by
  sorry

/-- A Noetherian complete local ring is a G-ring. -/
theorem isGRing_of_noetherian_complete_local
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A] : IsGRing A := by
  sorry

/-- For a Noetherian ring it is enough to check the formal fibres at maximal
ideals. -/
theorem isGRing_iff_maximalFormalFibers
    {R : Type u} [CommRing R] [IsNoetherianRing R] :
    IsGRing R ↔
      ∀ m : MaximalSpectrum R,
        HasGeometricallyRegularLocalFormalFibers
          (Localization.AtPrime (MaximalSpectrum.toPrimeSpectrum m).asIdeal) := by
  sorry

/-! ## Henselizations and polynomial helpers -/

/-- A G-ring has G-ring henselizations and strict henselizations. -/
theorem isGRing_henselization_and_strictHenselization
    {R K : Type u} [CommRing R] [IsLocalRing R]
    [Field K] [Algebra (IsLocalRing.ResidueField R) K]
    (D : StrictHenselizationData R K) (hR : IsGRing R) :
    IsGRing D.henselization ∧ IsGRing D.strictHenselization := by
  sorry

/-- The positive-characteristic polynomial helper.  Here `q` is maximal over
the maximal ideal of `A`, and `r` is a nonzero prime over the zero prime. -/
theorem geometricallyRegular_formalFiber_polynomial_of_complete_local_domain
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    [IsDomain A] [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (p : ℕ) [Fact (Nat.Prime p)] [CharP A p]
    (q : MaximalSpectrum (Polynomial A))
    (r : PrimeSpectrum (Polynomial A))
    (hrq : r.asIdeal ≤ q.asIdeal)
    (hr_ne_bot : r.asIdeal ≠ (⊥ : Ideal (Polynomial A)))
    (hq : q.asIdeal.comap (algebraMap A (Polynomial A)) =
      IsLocalRing.maximalIdeal A)
    (hr : r.asIdeal.comap (algebraMap A (Polynomial A)) =
      (⊥ : Ideal A)) :
    IsGeometricallyRegularFormalFiberAt (Polynomial A)
      (MaximalSpectrum.toPrimeSpectrum q) r := by
  sorry

/-- G-rings are stable under essentially finite type ring maps. -/
theorem isGRing_of_essentiallyFiniteType
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (hR : IsGRing R)
    (hfinite : RingHom.EssFiniteType f) : IsGRing S := by
  sorry

/-! ## The non-permanence remark and examples -/

/-- G-rings need not remain G-rings after completion along an arbitrary ideal. -/
theorem not_isGRing_completion_in_general :
    ¬ ∀ (R : Type u) [CommRing R] (I : Ideal R),
      IsGRing R → IsGRing (ringCompletion I) := by
  sorry

/-- Fields, complete local Noetherian rings, `ℤ`, characteristic-zero
Dedekind domains, and finite-type extensions of these are G-rings. -/
theorem isGRing_ubiquity :
    (∀ (K : Type u) [Field K], IsGRing K) ∧
    (∀ (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
      [IsAdicComplete (IsLocalRing.maximalIdeal A) A], IsGRing A) ∧
    IsGRing ℤ ∧
    (∀ (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]
      [IsDedekindDomain R] [CharZero (FractionRing R)], IsGRing R) ∧
    (∀ (R S : Type u) [CommRing R] [CommRing S] (f : R →+* S),
      IsGRing R → RingHom.FiniteType f → IsGRing S) := by
  sorry

/-- A henselian local ring is a filtered colimit of henselian local G-rings
with local transition maps. -/
theorem exists_filteredLocalGRingColimit
    {A : Type u} [CommRing A] [HenselianLocalRing A] :
    ∃ (I : Type u) (_ : Category I) (_ : IsFiltered I)
      (D : FilteredLocalRingColimitData I A),
      ∀ i, IsLocalRing (D.diagram.obj i) ∧
        HenselianLocalRing (D.diagram.obj i) ∧
          IsGRing (D.diagram.obj i) := by
  sorry

/-- For a G-ring, completion along any ideal is a regular ring map. -/
theorem gRing_to_completion_regular
    {A : Type u} [CommRing A] (hA : IsGRing A) (I : Ideal A) :
    IsRegularRingMap (algebraMap A (ringCompletion I)) := by
  sorry

/-- Henselization along an ideal preserves the G-ring property. -/
theorem isGRing_henselization_of_pair
    {A : Type u} [CommRing A] (hA : IsGRing A) (I : Ideal A)
    (D : HenselizationData ({ ideal := I } : Pair A)) :
    IsGRing D.carrier := by
  sorry

end

end Formalization.Books.MoreAlgebra.Unit50
