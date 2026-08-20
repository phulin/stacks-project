import Formalization.Books.MoreAlgebra.Unit50
import Formalization.Books.Algebra.Unit37.NormalRings
import Formalization.Books.Algebra.Unit43.GeometricallyReduced
import Formalization.Books.Algebra.Unit104.CohenMacaulayRings
import Formalization.Books.Algebra.Unit157.SerresCriterion
import Formalization.Books.Algebra.Unit165.GeometricallyNormal
import Mathlib.RingTheory.RingHom.FaithfullyFlat
import Mathlib.RingTheory.RingHom.Flat

/-!
# More on Algebra, Chapter 51: Properties of formal fibres

This file records the property-of-fibres framework, the permanence interfaces
(A)--(E), and the formal-fibre permanence statements from the source section.
The generic property is intentionally a predicate on field algebras; the
source only applies it to Noetherian target rings, while this presentation
keeps the tensor-product interface usable without manufacturing a separate
Noetherian instance for every fibre.
-/

namespace Formalization.Books.MoreAlgebra.Unit51

open Formalization.Books.Algebra.Unit37
open Formalization.Books.Algebra.Unit43
open Formalization.Books.Algebra.Unit96
open Formalization.Books.Algebra.Unit104
open Formalization.Books.Algebra.Unit157
open Formalization.Books.Algebra.Unit165
open Formalization.Books.Algebra.Unit155
open Formalization.Books.MoreAlgebra.Unit41
open Formalization.Books.MoreAlgebra.Unit45
open Formalization.Books.MoreAlgebra.Unit50
open Formalization.Books.MoreAlgebra.Unit12
open scoped TensorProduct

noncomputable section

universe u

/-! ## The property-of-fibres framework

The source's displayed fibre map `κ(q) → B ⊗[A] κ(q)` is represented by
the residue-field algebra instance installed in `HasPropertyOnFibres`.
Likewise, `formalFiberAt` from Chapter 50 and
`HasQuotientFormalFiberProperty` below are the two displayed presentations
of the formal fibre used in the source's prime-pair criterion, so no separate
proposition is needed for a merely notational rewrite of those presentations.
-/

/-- A property of an algebra over a field.

The source restricts the target algebra to be Noetherian.  Noetherianity is a
standing hypothesis on the maps and rings below, rather than part of this
predicate, so that the same property can be used for canonical tensor fibres
whose Noetherian instance is supplied by the relevant theorem.
-/
def RingMapProperty : Type (u + 1) :=
  ∀ (k R : Type u) [Field k] [CommRing R] [Algebra k R], Prop

/-- `P` holds for all fibres of a ring homomorphism. -/
def HasPropertyOnFibres
    (P : RingMapProperty)
    {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) : Prop :=
  letI : Algebra A B := f.toAlgebra
  ∀ q : PrimeSpectrum A,
    letI : Algebra A q.asIdeal.ResidueField :=
      Algebra.compHom q.asIdeal.ResidueField
        (algebraMap A (Localization.AtPrime q.asIdeal))
    letI : Module A B := Algebra.toModule
    letI : Module A q.asIdeal.ResidueField := Algebra.toModule
    letI : Algebra q.asIdeal.ResidueField
        (B ⊗[A] q.asIdeal.ResidueField) :=
      Algebra.TensorProduct.rightAlgebra
    P q.asIdeal.ResidueField (B ⊗[A] q.asIdeal.ResidueField)

/-- `P` holds for the formal fibre at the pair of primes `q ≤ p`. -/
def HasFormalFiberAtProperty
    (P : RingMapProperty)
    (R : Type u) [CommRing R] (p q : PrimeSpectrum R) : Prop :=
  letI : Algebra R (completionAtPrime R p) := completionAtPrimeAlgebra R p
  letI : Algebra R q.asIdeal.ResidueField := primeResidueFieldAlgebra R q
  letI : Module R (completionAtPrime R p) := Algebra.toModule
  letI : Module R q.asIdeal.ResidueField := Algebra.toModule
  letI : Algebra q.asIdeal.ResidueField (formalFiberAt R p q) :=
    Algebra.TensorProduct.rightAlgebra
  P q.asIdeal.ResidueField (formalFiberAt R p q)

/-- The quotient presentation of the formal fibre at `q ≤ p`, using the
completion of the localization of `R ⧸ q` at the corresponding quotient
prime. -/
def HasQuotientFormalFiberProperty
    (P : RingMapProperty)
    (R : Type u) [CommRing R] (q : PrimeSpectrum R)
    (p : PrimeSpectrum (R ⧸ q.asIdeal)) : Prop :=
  let C := ringCompletion
    (IsLocalRing.maximalIdeal (Localization.AtPrime p.asIdeal))
  letI : Algebra (R ⧸ q.asIdeal) C := (algebraMap (R ⧸ q.asIdeal) C).toAlgebra
  letI : Algebra (R ⧸ q.asIdeal) q.asIdeal.ResidueField := inferInstance
  letI : Module (R ⧸ q.asIdeal) C := Algebra.toModule
  letI : Module (R ⧸ q.asIdeal) q.asIdeal.ResidueField := Algebra.toModule
  let F := C ⊗[R ⧸ q.asIdeal] q.asIdeal.ResidueField
  letI : Algebra q.asIdeal.ResidueField F :=
    Algebra.TensorProduct.rightAlgebra
  P q.asIdeal.ResidueField F

/-- `P` holds for the formal fibres of a local ring. -/
def HasFormalFibresProperty
    (P : RingMapProperty)
    (A : Type u) [CommRing A] [IsLocalRing A] : Prop :=
  HasPropertyOnFibres P
    (algebraMap A (ringCompletion (IsLocalRing.maximalIdeal A)))

/-- `P` holds for the formal fibres of the localization of `R` at `p`. -/
def HasFormalFibresPropertyAt
    (P : RingMapProperty)
    (R : Type u) [CommRing R] (p : PrimeSpectrum R) : Prop :=
  HasFormalFibresProperty P (Localization.AtPrime p.asIdeal)

/-- A Noetherian ring whose localizations have formal fibres with `P`. -/
def IsPRing
    (P : RingMapProperty)
    (R : Type u) [CommRing R] : Prop :=
  IsNoetherianRing R ∧
    ∀ p : PrimeSpectrum R, HasFormalFibresPropertyAt P R p

/-! ## Assertions (A)--(E) -/

/-- (A): finite-type field extension preserves `P`. -/
def PropertyA (P : RingMapProperty) : Prop :=
  ∀ (k k' R : Type u) [Field k] [Field k'] [CommRing R]
    [Algebra k k'] [Algebra k R] [Algebra.FiniteType k k']
    [IsNoetherianRing R],
    P k R →
      letI : Algebra k' (R ⊗[k] k') := Algebra.TensorProduct.rightAlgebra
      P k' (R ⊗[k] k')

/-- (B): `P` can be checked on all localizations of the target. -/
def PropertyB (P : RingMapProperty) : Prop :=
  ∀ (k R : Type u) [Field k] [CommRing R] [Algebra k R]
    [IsNoetherianRing R],
    (∀ p : PrimeSpectrum R,
      letI : Algebra k (Localization.AtPrime p.asIdeal) :=
        ((algebraMap R (Localization.AtPrime p.asIdeal)).comp
          (algebraMap k R)).toAlgebra
      P k (Localization.AtPrime p.asIdeal)) ↔ P k R

/-- (C): regularity of `B → C` ascends a fibre property from `A → B` to
`A → C`, for flat maps of Noetherian rings. -/
def PropertyC (P : RingMapProperty) : Prop :=
  ∀ (A B C : Type u) [CommRing A] [CommRing B] [CommRing C]
    [IsNoetherianRing A] [IsNoetherianRing B] [IsNoetherianRing C]
    (f : A →+* B) (g : B →+* C),
    RingHom.Flat f → RingHom.Flat g → IsRegularRingMap g →
    HasPropertyOnFibres P f → HasPropertyOnFibres P (g.comp f)

/-- (D): faithful flat descent of a fibre property. -/
def PropertyD (P : RingMapProperty) : Prop :=
  ∀ (A B C : Type u) [CommRing A] [CommRing B] [CommRing C]
    [IsNoetherianRing A] [IsNoetherianRing B] [IsNoetherianRing C]
    (f : A →+* B) (g : B →+* C),
    RingHom.Flat f → RingHom.Flat g → RingHom.FaithfullyFlat g →
    HasPropertyOnFibres P (g.comp f) → HasPropertyOnFibres P f

/-- (E): separable algebraic extension of the ground field preserves `P`. -/
def PropertyE (P : RingMapProperty) : Prop :=
  ∀ (k k' R : Type u) [Field k] [Field k'] [CommRing R]
    [Algebra k k'] [Algebra k' R] [Algebra k R]
    [IsScalarTower k k' R] [Algebra.IsAlgebraic k k']
    [Algebra.IsSeparable k k'] [IsNoetherianRing R],
    P k R → P k' R

/- (F) in the source is the literal placeholder “add more here”, so it has no
   mathematical content to encode. -/

/-! ## Locality and quasi-finite ascent -/

/-- The localized fibre condition appearing in the second item of the local
criterion. -/
def HasLocalizedPropertyOnFibres
    (P : RingMapProperty)
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) : Prop :=
  ∀ (p : PrimeSpectrum R) (q : PrimeSpectrum S)
    (hq : PrimeSpectrum.comap f q = p),
    HasPropertyOnFibres P (localizedPrimeRingHom f p q hq)

/-- The maximal-localized fibre condition appearing in the third item of the
local criterion. -/
def HasMaximalLocalizedPropertyOnFibres
    (P : RingMapProperty)
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) : Prop :=
  ∀ (m : MaximalSpectrum R) (n : MaximalSpectrum S)
    (hn : PrimeSpectrum.comap f n.toPrimeSpectrum = m.toPrimeSpectrum),
    HasPropertyOnFibres P
      (localizedPrimeRingHom f m.toPrimeSpectrum n.toPrimeSpectrum hn)

/-- Property (B) makes fibrewise `P` equivalent to its prime-local and
maximal-local versions. -/
theorem propertyOnFibres_iff_localized_iff_maximalLocalized
    (P : RingMapProperty)
    {R S : Type u} [CommRing R] [CommRing S]
    [IsNoetherianRing R] [IsNoetherianRing S]
    (f : R →+* S) (hB : PropertyB P) :
    List.TFAE
      [ HasPropertyOnFibres P f,
        HasLocalizedPropertyOnFibres P f,
        HasMaximalLocalizedPropertyOnFibres P f ] := by
  sorry

/-- A single formal fibre ascends through a finite-type map that is
quasi-finite at the target prime. -/
theorem formalFiberPropertyAt_of_quasiFiniteAt
    (P : RingMapProperty)
    {R S : Type u} [CommRing R] [CommRing S]
    [IsNoetherianRing R] [IsNoetherianRing S]
    (f : R →+* S) (hfinite : RingHom.FiniteType f)
    (q p : PrimeSpectrum R) (q' p' : PrimeSpectrum S)
    (hq : q'.asIdeal.comap f = q.asIdeal)
    (hp : p'.asIdeal.comap f = p.asIdeal)
    (hqp : q.asIdeal ≤ p.asIdeal)
    (hqp' : q'.asIdeal ≤ p'.asIdeal)
    (hquasi : RingHom.QuasiFiniteAt f p'.asIdeal)
    (hA : PropertyA P) (hB : PropertyB P)
    (hP : HasFormalFiberAtProperty P R p q) :
    HasFormalFiberAtProperty P S p' q' := by
  sorry

/-- The preceding ascent statement for all primes below a fixed target prime.
-/
theorem hasFormalFibresPropertyAt_of_quasiFiniteAt
    (P : RingMapProperty)
    {R S : Type u} [CommRing R] [CommRing S]
    [IsNoetherianRing R] [IsNoetherianRing S]
    (f : R →+* S) (p' : PrimeSpectrum S)
    (p : PrimeSpectrum R)
    (hp : p'.asIdeal.comap f = p.asIdeal)
    (hfinite : RingHom.FiniteType f)
    (hquasi : RingHom.QuasiFiniteAt f p'.asIdeal)
    (hA : PropertyA P) (hB : PropertyB P)
    (hR : HasFormalFibresPropertyAt P R p) :
    HasFormalFibresPropertyAt P S p' := by
  sorry

/-- A quasi-finite finite-type extension of a `P`-ring is a
`P`-ring. -/
theorem isPRing_of_quasiFinite_finiteType
    (P : RingMapProperty)
    {R S : Type u} [CommRing R] [CommRing S]
    [IsNoetherianRing R] [IsNoetherianRing S]
    (f : R →+* S) (hfinite : RingHom.FiniteType f)
    (hquasi : RingHom.QuasiFinite f) (hR : IsPRing P R)
    (hA : PropertyA P) (hB : PropertyB P) :
    IsPRing P S := by
  sorry

/-- The easy prime-pair criterion for a `P`-ring, in the quotient
presentation of the formal fibre. -/
theorem isPRing_iff_quotientFormalFiber
    (P : RingMapProperty)
    {R : Type u} [CommRing R] [IsNoetherianRing R] :
    IsPRing P R ↔
      ∀ (q : PrimeSpectrum R) (p : PrimeSpectrum (R ⧸ q.asIdeal)),
        HasQuotientFormalFiberProperty P R q p := by
  sorry

/-- A Noetherian ring is a `P`-ring exactly when its localizations at maximal
ideals have `P` formal fibres, assuming (C) and (D). -/
theorem isPRing_iff_maximalFormalFibres
    (P : RingMapProperty)
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    (hC : PropertyC P) (hD : PropertyD P) :
    IsPRing P R ↔
      ∀ m : MaximalSpectrum R,
        HasFormalFibresPropertyAt P R m.toPrimeSpectrum := by
  sorry

/-- `P` is stable under essentially finite-type maps from a `P`-ring, under
(A), (B), (C), and (D). -/
theorem isPRing_of_essentiallyFiniteType
    (P : RingMapProperty)
    {R S : Type u} [CommRing R] [CommRing S]
    [IsNoetherianRing R]
    (f : R →+* S) (hR : IsPRing P R)
    (hfinite : RingHom.EssFiniteType f)
    (hA : PropertyA P) (hB : PropertyB P)
    (hC : PropertyC P) (hD : PropertyD P) :
    IsPRing P S := by
  sorry

/-- The fibres of completion along any ideal of a `P`-ring have `P`, assuming
(B) and (D). -/
theorem propertyOnFibres_to_completion
    (P : RingMapProperty)
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) (hA : IsPRing P A)
    (hB : PropertyB P) (hD : PropertyD P) :
    HasPropertyOnFibres P (algebraMap A (ringCompletion I)) := by
  sorry

/-! ## Henselizations -/

/-- Henselization of a pair inherits the `P`-ring property under (B)--(E). -/
theorem isPRing_henselizationPair
    (P : RingMapProperty)
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    (I : Ideal A)
    (D : HenselizationData ({ ideal := I } : Pair A))
    (hA : IsPRing P A) (hB : PropertyB P) (hC : PropertyC P)
    (hD : PropertyD P) (hE : PropertyE P) :
    IsPRing P D.carrier := by
  sorry

/-- The henselization and strict henselization of a Noetherian local
`P`-ring are `P`-rings. -/
theorem isPRing_henselization_and_strictHenselization
    (P : RingMapProperty)
    {R K : Type u} [CommRing R] [IsLocalRing R]
    [Field K] [Algebra (IsLocalRing.ResidueField R) K]
    (D : StrictHenselizationData R K) [IsNoetherianRing R]
    (hR : IsPRing P R) (hB : PropertyB P) (hC : PropertyC P)
    (hD : PropertyD P) (hE : PropertyE P) :
    IsPRing P D.henselization ∧ IsPRing P D.strictHenselization := by
  sorry

/-! ## Concrete properties -/

/-- Geometric reducedness as a property of a field algebra. -/
def GeometricallyReducedProperty : RingMapProperty :=
  fun k R _ _ _ => IsGeometricallyReduced k R

/-- Normality as a property of a field algebra. -/
def GeometricallyNormalProperty : RingMapProperty :=
  fun k R _ _ _ => IsGeometricallyNormal k R

/-- Serre's `(S_n)` property as a property of a field algebra. -/
def SerreSProperty (n : ℕ) : RingMapProperty :=
  fun _ R _ _ _ => HasPropertySk R n

/-- Cohen--Macaulayness as a property on the intended Noetherian target
algebras.  The existential presentation makes the Noetherian standing
hypothesis explicit without adding a second predicate to the framework. -/
def CohenMacaulayProperty : RingMapProperty :=
  fun _ R _ _ _ => ∃ hR : IsNoetherianRing R, @IsCohenMacaulayRing R _ hR

/-- `(R_n)` after every finite extension of the ground field. -/
def SerreRAfterFiniteExtensionsProperty (n : ℕ) : RingMapProperty :=
  fun k R _ _ _ =>
    ∀ (k' : Type u) [Field k'] [Algebra k k'] [FiniteDimensional k k'],
      HasPropertyRk (R ⊗[k] k') n

/-- Geometric reducedness satisfies the source's assertions (A)--(E). -/
theorem geometricallyReducedProperty_A_to_E :
    PropertyA GeometricallyReducedProperty ∧
      PropertyB GeometricallyReducedProperty ∧
        PropertyC GeometricallyReducedProperty ∧
          PropertyD GeometricallyReducedProperty ∧
            PropertyE GeometricallyReducedProperty := by
  sorry

/-- Geometric normality satisfies the source's assertions (A)--(E). -/
theorem geometricallyNormalProperty_A_to_E :
    PropertyA GeometricallyNormalProperty ∧
      PropertyB GeometricallyNormalProperty ∧
        PropertyC GeometricallyNormalProperty ∧
          PropertyD GeometricallyNormalProperty ∧
            PropertyE GeometricallyNormalProperty := by
  sorry

/-- For `n ≥ 1`, `(S_n)` satisfies the source's assertions (A)--(E). -/
theorem serreSProperty_A_to_E (n : ℕ) (hn : 1 ≤ n) :
    PropertyA (SerreSProperty n) ∧
      PropertyB (SerreSProperty n) ∧
        PropertyC (SerreSProperty n) ∧
          PropertyD (SerreSProperty n) ∧
            PropertyE (SerreSProperty n) := by
  sorry

/-- Cohen--Macaulayness satisfies the source's assertions (A)--(E). -/
theorem cohenMacaulayProperty_A_to_E :
    PropertyA CohenMacaulayProperty ∧
      PropertyB CohenMacaulayProperty ∧
        PropertyC CohenMacaulayProperty ∧
          PropertyD CohenMacaulayProperty ∧
            PropertyE CohenMacaulayProperty := by
  sorry

/-- The `(R_n)`-after-finite-extensions property satisfies (A)--(E). -/
theorem serreRAfterFiniteExtensionsProperty_A_to_E (n : ℕ) :
    PropertyA (SerreRAfterFiniteExtensionsProperty n) ∧
      PropertyB (SerreRAfterFiniteExtensionsProperty n) ∧
        PropertyC (SerreRAfterFiniteExtensionsProperty n) ∧
          PropertyD (SerreRAfterFiniteExtensionsProperty n) ∧
            PropertyE (SerreRAfterFiniteExtensionsProperty n) := by
  sorry

end
end Formalization.Books.MoreAlgebra.Unit51
