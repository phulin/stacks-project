import Formalization.Books.Algebra.Unit105.CatenaryRings
import Formalization.Books.Algebra.Unit112.HomomorphismsAndDimension
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.RingTheory.AlgebraicIndependent.Basic
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Mathlib.SetTheory.Cardinal.ENat

/-!
# Commutative Algebra, Chapter 113: The dimension formula

The source's heights use Mathlib's `Ideal.height`.  Since Mathlib's
transcendence degree is cardinal-valued while heights are `ℕ∞`-valued, the
dimension formula below uses the canonical `Cardinal.toENat` projection; under
the finite-type hypotheses this records the same finite transcendence degrees.
The residue-field and fraction-field maps are the canonical maps supplied by
Mathlib, packaged only where the source-facing hypotheses need them.
-/

namespace Formalization.Books.Algebra.Unit113

universe u v

noncomputable section

/-! ## Canonical maps used by the source statements -/

/- The source's residue-field extension `κ(p) ⟶ κ(q)` is Mathlib's canonical
   residue-field map, with the displayed equality of primes used to put the
   source prime `p` at the left-hand side. -/
noncomputable def residueFieldMapAt
    {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (p : PrimeSpectrum R) (q : PrimeSpectrum S)
    (hq : PrimeSpectrum.comap f q = p) :
    p.asIdeal.ResidueField →+* q.asIdeal.ResidueField :=
  Ideal.ResidueField.map p.asIdeal q.asIdeal f (by
    simpa [PrimeSpectrum.comap_asIdeal] using
      (congrArg PrimeSpectrum.asIdeal hq).symm)

/- The source's induced extension of fraction fields is represented by the
   canonical localization map between the fraction rings of the two domains. -/
noncomputable def fractionFieldMap
    {A B : Type*} [CommRing A] [CommRing B] [IsDomain A] [IsDomain B]
    (f : A →+* B) (hinj : Function.Injective f) :
    FractionRing A →+* FractionRing B :=
  IsFractionRing.map (j := f) hinj

/-! ## The dimension formula -/

/-- The dimension formula for a finite-type inclusion of Noetherian domains.

The displayed source inequality is expressed with Mathlib's `ℕ∞` heights and
the canonical `Cardinal.toENat` conversion of its cardinal-valued
transcendence degrees. -/
theorem dimension_formula
    {R S : Type*} [CommRing R] [CommRing S]
    [IsNoetherianRing R] [IsDomain R] [IsDomain S]
    (f : R →+* S) (hfinite : RingHom.FiniteType f)
    (hinj : Function.Injective f)
    (p : PrimeSpectrum R) (q : PrimeSpectrum S)
    (hq : PrimeSpectrum.comap f q = p) :
    letI : Algebra R S := f.toAlgebra
    letI : Algebra p.asIdeal.ResidueField q.asIdeal.ResidueField :=
      (residueFieldMapAt f p q hq).toAlgebra
    q.asIdeal.height ≤
        p.asIdeal.height + Cardinal.toENat (Algebra.trdeg R S) -
          Cardinal.toENat
            (Algebra.trdeg p.asIdeal.ResidueField q.asIdeal.ResidueField) ∧
      (Formalization.Books.Algebra.Unit105.IsUniversallyCatenary R →
        q.asIdeal.height =
          p.asIdeal.height + Cardinal.toENat (Algebra.trdeg R S) -
            Cardinal.toENat
              (Algebra.trdeg p.asIdeal.ResidueField q.asIdeal.ResidueField)) := by
  sorry

/-! ## Finite maps in codimension one -/

/-- A generically finite finite-type map has finitely many height-one primes
over a height-one prime, and every prime in that fibre has height one. -/
theorem finite_in_codimension_one
    {A B : Type*} [CommRing A] [CommRing B]
    [IsNoetherianRing A] [IsDomain A] [IsDomain B]
    (f : A →+* B) (hinj : Function.Injective f)
    (hfraction :
      letI : Algebra (FractionRing A) (FractionRing B) :=
        (fractionFieldMap f hinj).toAlgebra
      FiniteDimensional (FractionRing A) (FractionRing B))
    (hfinite : RingHom.FiniteType f)
    (p : PrimeSpectrum A) (hp : p.asIdeal.height = 1) :
    Set.Finite {q : PrimeSpectrum B | PrimeSpectrum.comap f q = p} ∧
      ∀ q : PrimeSpectrum B, PrimeSpectrum.comap f q = p →
        q.asIdeal.height = 1 := by
  sorry

end

end Formalization.Books.Algebra.Unit113
