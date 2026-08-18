import Formalization.Books.Algebra.Unit127.ColimitsAndFinitePresentation
import Formalization.Books.Algebra.Unit84.TransfiniteDevissage
import Formalization.Books.Algebra.Unit88.MittagLefflerModules
import Mathlib.FieldTheory.IsSepClosed
import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.RingHom.QuasiFinite
import Mathlib.RingTheory.RingHom.Etale
import Mathlib.RingTheory.RingHom.Unramified
import Mathlib.RingTheory.Etale.Finite
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.Topology.KrullDimension

/-!
# Commutative Algebra, Chapter 153: Henselian local rings

This file follows the three sections of the chapter.  Mathlib's
`HenselianLocalRing` is the canonical henselian-local-ring predicate.  The
chapter-specific interfaces below retain the residue-field, étale-colimit,
decomposition, and functorial data that occur in the source.
-/

namespace Formalization.Books.Algebra.Unit153

open CategoryTheory
open CategoryTheory.Limits
open Formalization.Books.Categories.Unit21
open Formalization.Books.Algebra.Unit127
open Polynomial
open Set
open scoped TensorProduct

noncomputable section

universe u v

/-- The maximal point of a local ring. -/
def maximalPrime (R : Type u) [CommRing R] [IsLocalRing R] : PrimeSpectrum R :=
  ⟨IsLocalRing.maximalIdeal R, inferInstance⟩

/-! ## Henselian local rings -/

/- Mathlib already provides the definition and its root-lifting API. -/
abbrev IsHenselian (R : Type u) [CommRing R] [IsLocalRing R] : Prop :=
  HenselianLocalRing R

/-- A strictly henselian local ring is henselian and has separably closed
residue field. -/
class StrictlyHenselianLocalRing (R : Type u) [CommRing R]
    extends HenselianLocalRing R where
  separablyClosed : IsSepClosed (IsLocalRing.ResidueField R)

/-- Reduction of a polynomial to the residue field of a local ring. -/
def residuePolynomial (R : Type u) [CommRing R] [IsLocalRing R]
    (f : Polynomial R) : Polynomial (IsLocalRing.ResidueField R) :=
  f.map (IsLocalRing.residue R)

/-- The source's “simple root” condition. -/
def IsSimpleResidueRoot (R : Type u) [CommRing R] [IsLocalRing R]
    (f : Polynomial R) (a₀ : IsLocalRing.ResidueField R) : Prop :=
  (residuePolynomial R f).IsRoot a₀ ∧
    (residuePolynomial R f).derivative.eval a₀ ≠ 0

/-- The root-lifting formulation used in the definition of a henselian local
ring.  It is definitionally expressed using Mathlib's residue map. -/
def HenselianRootLifting (R : Type u) [CommRing R] [IsLocalRing R] : Prop :=
  ∀ f : Polynomial R, f.Monic → ∀ a₀ : IsLocalRing.ResidueField R,
    IsSimpleResidueRoot R f a₀ →
      ∃ a : R, f.IsRoot a ∧ IsLocalRing.residue R a = a₀

theorem henselian_iff_root_lifting
    (R : Type u) [CommRing R] [IsLocalRing R] :
    List.TFAE [IsHenselian R, HenselianRootLifting R] := by
  sorry

/-- The uniqueness assertion for a lift of a simple root. -/
theorem root_lift_unique
    {R : Type u} [CommRing R] [IsLocalRing R]
    (f : Polynomial R) {a b : R}
    (ha : f.eval a = 0) (hb : f.eval b = 0)
    (hab : a - b ∈ IsLocalRing.maximalIdeal R)
    (hderiv : f.derivative.eval a ∉ IsLocalRing.maximalIdeal R) :
    a = b := by
  sorry

/-- Lifting a factorization of the residue polynomial, with the monic
hypothesis from the corresponding item in the source. -/
def MonicFactorizationLift (R : Type u) [CommRing R] [IsLocalRing R] : Prop :=
  ∀ f : Polynomial R, f.Monic → ∀ g₀ h₀ : Polynomial (IsLocalRing.ResidueField R),
    residuePolynomial R f = g₀ * h₀ → IsCoprime g₀ h₀ →
      ∃ g h : Polynomial R,
        f = g * h ∧ residuePolynomial R g = g₀ ∧ residuePolynomial R h = h₀

/-- The degree-preserving monic factorization assertion. -/
def MonicDegreeFactorizationLift (R : Type u) [CommRing R] [IsLocalRing R] : Prop :=
  ∀ f : Polynomial R, f.Monic → ∀ g₀ h₀ : Polynomial (IsLocalRing.ResidueField R),
    residuePolynomial R f = g₀ * h₀ → IsCoprime g₀ h₀ →
      ∃ g h : Polynomial R,
        f = g * h ∧ residuePolynomial R g = g₀ ∧ residuePolynomial R h = h₀ ∧
          g.natDegree = g₀.natDegree

/-- The unrestricted factorization assertion. -/
def FactorizationLift (R : Type u) [CommRing R] [IsLocalRing R] : Prop :=
  ∀ f : Polynomial R, ∀ g₀ h₀ : Polynomial (IsLocalRing.ResidueField R),
    residuePolynomial R f = g₀ * h₀ → IsCoprime g₀ h₀ →
      ∃ g h : Polynomial R,
        f = g * h ∧ residuePolynomial R g = g₀ ∧ residuePolynomial R h = h₀

/-- The unrestricted, degree-preserving factorization assertion. -/
def DegreeFactorizationLift (R : Type u) [CommRing R] [IsLocalRing R] : Prop :=
  ∀ f : Polynomial R, ∀ g₀ h₀ : Polynomial (IsLocalRing.ResidueField R),
    residuePolynomial R f = g₀ * h₀ → IsCoprime g₀ h₀ →
      ∃ g h : Polynomial R,
        f = g * h ∧ residuePolynomial R g = g₀ ∧ residuePolynomial R h = h₀ ∧
          g.natDegree = g₀.natDegree

/-- A residue-field identification at an étale point.  The two displayed
equalities are the exact condition that the map is over the residue field of
the base local ring. -/
structure ResidueFieldIdentification
    {R A S : Type u} [CommRing R] [CommRing A] [CommRing S]
    [Algebra R A] [Algebra R S] [IsLocalRing R] [IsLocalRing S]
    (q : PrimeSpectrum A) (hq : q.asIdeal.comap (algebraMap R A) =
      IsLocalRing.maximalIdeal R) where
  map : q.asIdeal.ResidueField →+* IsLocalRing.ResidueField S
  over_base : ∀ r : R,
    map (algebraMap (A ⧸ q.asIdeal) q.asIdeal.ResidueField
      (Ideal.Quotient.mk q.asIdeal (algebraMap R A r))) =
      IsLocalRing.residue S (algebraMap R S r)

/-- Residue-field data for an étale point over the closed point of a local
target.  Unlike `ResidueFieldIdentification`, the source ring need not be
local; this is the formulation used by the two map-into-henselian lemmas. -/
structure ResidueFieldCompatibility
    {R A S : Type u} [CommRing R] [CommRing A] [CommRing S]
    [Algebra R A] [Algebra R S] [IsLocalRing S]
    (q : PrimeSpectrum A)
    (hq : q.asIdeal.comap (algebraMap R A) =
      (IsLocalRing.maximalIdeal S).comap (algebraMap R S)) where
  map : q.asIdeal.ResidueField →+* IsLocalRing.ResidueField S
  over_base : ∀ r : R,
    map (algebraMap (A ⧸ q.asIdeal) q.asIdeal.ResidueField
      (Ideal.Quotient.mk q.asIdeal (algebraMap R A r))) =
      IsLocalRing.residue S (algebraMap R S r)

/-- The residue-field diagram used for strict henselian functoriality. -/
structure StrictResidueFieldCompatibility
    {R A S L : Type u} [CommRing R] [CommRing A] [CommRing S]
    [Algebra R A] [Algebra R S] [IsLocalRing R] [IsLocalRing S]
    [Field L] [Algebra (IsLocalRing.ResidueField S) L]
    (φ : R →ₐ[R] S) (q : PrimeSpectrum A)
    (hq : q.asIdeal.comap (algebraMap R A) = IsLocalRing.maximalIdeal R) where
  map : q.asIdeal.ResidueField →+* L
  over_base : ∀ r : R,
    map (algebraMap (A ⧸ q.asIdeal) q.asIdeal.ResidueField
      (Ideal.Quotient.mk q.asIdeal (algebraMap R A r))) =
      algebraMap (IsLocalRing.ResidueField S) L
        (IsLocalRing.residue S (φ r))

/-- The étale retraction assertion in the characterization lemma. -/
def EtaleRetractionProperty (R : Type u) [CommRing R] [IsLocalRing R] : Prop :=
  ∀ {A : Type u} [CommRing A] [Algebra R A]
    (_hA : Algebra.Etale R A) (q : PrimeSpectrum A)
    (hq : q.asIdeal.comap (algebraMap R A) = IsLocalRing.maximalIdeal R)
    (τ : ResidueFieldIdentification (R := R) q hq),
    ∃ f : A →ₐ[R] R,
      PrimeSpectrum.comap f.toRingHom (maximalPrime R) = q ∧
        ∀ a : A, τ.map (algebraMap (A ⧸ q.asIdeal) q.asIdeal.ResidueField
          (Ideal.Quotient.mk q.asIdeal a)) =
          IsLocalRing.residue R (f a)

/-- The unique version of the étale retraction assertion. -/
def UniqueEtaleRetractionProperty (R : Type u) [CommRing R] [IsLocalRing R] : Prop :=
  ∀ {A : Type u} [CommRing A] [Algebra R A]
    (_hA : Algebra.Etale R A) (q : PrimeSpectrum A)
    (hq : q.asIdeal.comap (algebraMap R A) = IsLocalRing.maximalIdeal R)
    (τ : ResidueFieldIdentification (R := R) q hq),
    ∃! f : A →ₐ[R] R,
      PrimeSpectrum.comap f.toRingHom (maximalPrime R) = q ∧
        ∀ a : A, τ.map (algebraMap (A ⧸ q.asIdeal) q.asIdeal.ResidueField
          (Ideal.Quotient.mk q.asIdeal a)) =
          IsLocalRing.residue R (f a)

/-- The product decomposition data for a finite algebra over a local ring. -/
structure FiniteLocalProductData
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] where
  n : ℕ
  factor : Fin n → Type u
  [commRingFactor : ∀ i, CommRing (factor i)]
  [algebraFactor : ∀ i, Algebra R (factor i)]
  [localFactor : ∀ i, IsLocalRing (factor i)]
  [henselianFactor : ∀ i, HenselianLocalRing (factor i)]
  finiteFactor : ∀ i, RingHom.Finite (algebraMap R (factor i))
  decomposition : Nonempty (S ≃+* (∀ i, factor i))

/-- A finite-index product of local algebras. -/
structure FiniteProductData
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] where
  n : ℕ
  factor : Fin n → Type u
  [commRingFactor : ∀ i, CommRing (factor i)]
  [algebraFactor : ∀ i, Algebra R (factor i)]
  [localFactor : ∀ i, IsLocalRing (factor i)]
  decomposition : Nonempty (S ≃+* (∀ i, factor i))

/-- An arbitrary product decomposition of a finite algebra. -/
structure ProductData
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] where
  index : Type u
  factor : index → Type u
  [commRingFactor : ∀ i, CommRing (factor i)]
  [algebraFactor : ∀ i, Algebra R (factor i)]
  decomposition : Nonempty (S ≃+* (∀ i, factor i))

/-- The “finite algebra is a finite product of local rings” assertion. -/
def FiniteLocalProductProperty (R : Type u) [CommRing R] [IsLocalRing R] : Prop :=
  ∀ {S : Type u} [CommRing S] [Algebra R S],
    RingHom.Finite (algebraMap R S) →
      Nonempty (FiniteProductData R S)

/-- The unrestricted product assertion in item (9). -/
def FiniteProductProperty (R : Type u) [CommRing R] [IsLocalRing R] : Prop :=
  ∀ {S : Type u} [CommRing S] [Algebra R S],
    RingHom.Finite (algebraMap R S) →
      Nonempty (ProductData R S)

/-- Decomposition data for the finite-type “finite part times non-quasi-finite
part” assertions. -/
structure FiniteTypePartData
    (R S : Type u) [CommRing R] [CommRing S] [IsLocalRing R] [Algebra R S] where
  A : Type u
  [commRingA : CommRing A]
  [algebraRA : Algebra R A]
  B : Type u
  [commRingB : CommRing B]
  [algebraRB : Algebra R B]
  finiteA : RingHom.Finite (algebraMap R A)
  decomposition : Nonempty (S ≃+* A × B)
  noQuasiFiniteAt : ∀ q : PrimeSpectrum B,
    PrimeSpectrum.comap (algebraMap R B) q = IsLocalRing.maximalIdeal R →
      ¬ RingHom.QuasiFiniteAt (algebraMap R B) q.asIdeal

/-- The quasi-finite decomposition data with its special fibre explicitly
zero. -/
structure QuasiFinitePartData
    (R S : Type u) [CommRing R] [CommRing S] [IsLocalRing R]
    [Algebra R S] where
  A : Type u
  [commRingA : CommRing A]
  [algebraRA : Algebra R A]
  B : Type u
  [commRingB : CommRing B]
  [algebraRB : Algebra R B]
  finiteA : RingHom.Finite (algebraMap R A)
  decomposition : Nonempty (S ≃+* A × B)
  specialFiberZero : Subsingleton (IsLocalRing.ResidueField R ⊗[R] B)

/-- Decomposition data for the finite-type assertion whose remaining factor
has no zero-dimensional irreducible component in the special fibre. -/
structure PositiveDimensionalPartData
    (R S : Type u) [CommRing R] [CommRing S] [IsLocalRing R]
    [Algebra R S] where
  A : Type u
  [commRingA : CommRing A]
  [algebraRA : Algebra R A]
  B : Type u
  [commRingB : CommRing B]
  [algebraRB : Algebra R B]
  finiteA : RingHom.Finite (algebraMap R A)
  decomposition : Nonempty (S ≃+* A × B)
  positiveDimensionalFiber :
    ∀ C ∈ irreducibleComponents
      (PrimeSpectrum (IsLocalRing.ResidueField R ⊗[R] B)),
      1 ≤ topologicalKrullDim C

/-- The finite-type decomposition into local finite factors and a remainder
with no quasi-finite point over the closed point. -/
structure MopUpData
    (R S : Type u) [CommRing R] [CommRing S] [IsLocalRing R]
    [Algebra R S] where
  n : ℕ
  A : Fin n → Type u
  [commRingA : ∀ i, CommRing (A i)]
  [algebraRA : ∀ i, Algebra R (A i)]
  [localA : ∀ i, IsLocalRing (A i)]
  [henselianA : ∀ i, HenselianLocalRing (A i)]
  B : Type u
  [commRingB : CommRing B]
  [algebraRB : Algebra R B]
  finiteA : ∀ i, RingHom.Finite (algebraMap R (A i))
  decomposition : Nonempty (S ≃+* (∀ i, A i) × B)
  noQuasiFiniteAt : ∀ q : PrimeSpectrum B,
    PrimeSpectrum.comap (algebraMap R B) q = IsLocalRing.maximalIdeal R →
      ¬ RingHom.QuasiFiniteAt (algebraMap R B) q.asIdeal

/-- The strictly henselian refinement of `MopUpData`, recording the purely
inseparable residue-field extensions of its local factors. -/
structure StrictMopUpData
    (R S : Type u) [CommRing R] [CommRing S] [IsLocalRing R]
    [Algebra R S] where
  base : MopUpData R S
  residueAlgebra : ∀ i,
    letI : CommRing (base.A i) := base.commRingA i
    letI : IsLocalRing (base.A i) := base.localA i
    Algebra (IsLocalRing.ResidueField R)
      (IsLocalRing.ResidueField (base.A i))
  residuePurelyInseparable : ∀ i,
    letI : CommRing (base.A i) := base.commRingA i
    letI : IsLocalRing (base.A i) := base.localA i
    @IsPurelyInseparable (IsLocalRing.ResidueField R)
      (IsLocalRing.ResidueField (base.A i))
      (inferInstance : CommRing (IsLocalRing.ResidueField R))
      (inferInstance : Ring (IsLocalRing.ResidueField (base.A i)))
      (residueAlgebra i)

/-- The decomposition of an unramified algebra over a strictly henselian
local ring: the factors meeting the closed point are quotients of the base. -/
structure StrictUnramifiedDecompositionData
    (R S : Type u) [CommRing R] [CommRing S] [IsLocalRing R]
    [Algebra R S] where
  n : ℕ
  A : Fin n → Type u
  [commRingA : ∀ i, CommRing (A i)]
  [algebraRA : ∀ i, Algebra R (A i)]
  B : Type u
  [commRingB : CommRing B]
  [algebraRB : Algebra R B]
  decomposition : Nonempty (S ≃+* (∀ i, A i) × B)
  surjective : ∀ i, Function.Surjective (algebraMap R (A i))
  noPrimeOver : ∀ q : PrimeSpectrum B,
    PrimeSpectrum.comap (algebraMap R B) q ≠ IsLocalRing.maximalIdeal R

/-- The source's finite-type decomposition property. -/
def FiniteTypePartProperty (R : Type u) [CommRing R] [IsLocalRing R] : Prop :=
  ∀ {S : Type u} [CommRing S] [Algebra R S], Algebra.FiniteType R S →
    Nonempty (FiniteTypePartData R S)

/-- The quasi-finite decomposition statement, with the special-fibre vanishing
condition kept explicit. -/
def QuasiFinitePartProperty (R : Type u) [CommRing R] [IsLocalRing R] : Prop :=
  ∀ {S : Type u} [CommRing S] [Algebra R S],
    RingHom.QuasiFinite (algebraMap R S) →
      Nonempty (QuasiFinitePartData R S)

def PositiveDimensionalPartProperty
    (R : Type u) [CommRing R] [IsLocalRing R] : Prop :=
  ∀ {S : Type u} [CommRing S] [Algebra R S], Algebra.FiniteType R S →
    Nonempty (PositiveDimensionalPartData R S)

theorem characterize_henselian
    (R : Type u) [CommRing R] [IsLocalRing R] :
    List.TFAE
      [ IsHenselian R,
        HenselianRootLifting R,
        MonicFactorizationLift R,
        MonicDegreeFactorizationLift R,
        FactorizationLift R,
        DegreeFactorizationLift R,
        EtaleRetractionProperty R,
        UniqueEtaleRetractionProperty R,
        FiniteProductProperty R,
        FiniteLocalProductProperty R,
        FiniteTypePartProperty R,
        PositiveDimensionalPartProperty R,
        QuasiFinitePartProperty R ] := by
  sorry

theorem finite_over_henselian
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [HenselianLocalRing R] (hS : RingHom.Finite (algebraMap R S)) :
    Nonempty (FiniteLocalProductData R S) := by
  sorry

theorem finite_local_over_henselian
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [HenselianLocalRing R] [IsLocalRing S]
    (hS : RingHom.Finite (algebraMap R S)) :
    HenselianLocalRing S ∧ IsLocalHom (algebraMap R S) := by
  sorry

theorem quasiFinite_localization_over_henselian
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [HenselianLocalRing R] (q : PrimeSpectrum S)
    (hq : q.asIdeal.comap (algebraMap R S) = IsLocalRing.maximalIdeal R)
    (hfinite : Algebra.FiniteType R S)
    (hquasi : RingHom.QuasiFiniteAt (algebraMap R S) q.asIdeal) :
    HenselianLocalRing (Localization.AtPrime q.asIdeal) ∧
      RingHom.Finite (algebraMap R (Localization.AtPrime q.asIdeal)) := by
  sorry

theorem quasiFinite_over_henselian
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [HenselianLocalRing R]
    (hquasi : RingHom.QuasiFinite (algebraMap R S)) (q : PrimeSpectrum S)
    (hq : q.asIdeal.comap (algebraMap R S) = IsLocalRing.maximalIdeal R) :
    HenselianLocalRing (Localization.AtPrime q.asIdeal) ∧
      RingHom.Finite (algebraMap R (Localization.AtPrime q.asIdeal)) := by
  sorry

theorem henselian_finite_type_decomposition
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [HenselianLocalRing R] [Algebra.FiniteType R S] :
    Nonempty (MopUpData R S) := by
  sorry

theorem strictly_henselian_finite_type_decomposition
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [StrictlyHenselianLocalRing R] [Algebra.FiniteType R S] :
    Nonempty (StrictMopUpData R S) := by
  sorry

theorem finite_etale_residue_equivalence
    (R : Type u) [CommRing R] [HenselianLocalRing R] :
    Nonempty (CommAlgCat.FiniteEtale R ≌
      CommAlgCat.FiniteEtale (IsLocalRing.ResidueField R)) := by
  sorry

theorem unramified_over_strictly_henselian
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [StrictlyHenselianLocalRing R] (hS : Algebra.Unramified R S) :
    Nonempty (StrictUnramifiedDecompositionData R S) := by
  sorry

theorem complete_local_henselian
    (R : Type u) [CommRing R] [IsLocalRing R] [IsAdicComplete
      (IsLocalRing.maximalIdeal R) R] :
    HenselianLocalRing R := by
  sorry

theorem zero_dimensional_local_henselian
    (R : Type u) [CommRing R] [IsLocalRing R]
    (hzero : ringKrullDim R = 0) : HenselianLocalRing R := by
  sorry

/-- The map-into-a-henselian-local-ring assertion, including the residue-field
compatibility condition. -/
theorem map_into_henselian
    {R A S : Type u} [CommRing R] [CommRing A] [CommRing S]
    [Algebra R A] [Algebra R S] [HenselianLocalRing S]
    (hA : Algebra.Etale R A) (q : PrimeSpectrum A)
    (hq : q.asIdeal.comap (algebraMap R A) =
      (IsLocalRing.maximalIdeal S).comap (algebraMap R S))
    (τ : ResidueFieldCompatibility (R := R) (S := S) q hq) :
    ∃! f : A →ₐ[R] S,
      PrimeSpectrum.comap f.toRingHom (maximalPrime S) = q ∧
        ∀ a : A, τ.map (algebraMap (A ⧸ q.asIdeal) q.asIdeal.ResidueField
          (Ideal.Quotient.mk q.asIdeal a)) =
          IsLocalRing.residue S (f a) := by
  sorry

/- The solution sets in the strictly henselian polynomial-system lemma. -/
def PolynomialSystemSolutions
    (R : Type u) [CommRing R] (n : ℕ)
    (P : Fin n → MvPolynomial (Fin n) R) : Type u :=
  {x : Fin n → R // ∀ i, MvPolynomial.aeval x (P i) = 0}

/-- The tensor-kernel characterization of the Mittag--Leffler condition used
in the final result of the first section.  This is stated locally so that the
chapter remains independent of the unfinished proof-only development of the
earlier characterization chapter. -/
abbrev ModuleMittagLeffler
    {R : Type u} [CommRing R] (M : ModuleCat.{u} R) : Prop :=
  Formalization.Books.Algebra.Unit88.IsMittagLefflerModule M

theorem strictly_henselian_solution_bijection
    {R S : Type u} [CommRing R] [CommRing S]
    [StrictlyHenselianLocalRing R] [StrictlyHenselianLocalRing S]
    (φ : R →+* S) (hφ : IsLocalHom φ) (n : ℕ)
    (P : Fin n → MvPolynomial (Fin n) R)
    (hP : Algebra.Etale R
      (MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range P))) :
    Nonempty (PolynomialSystemSolutions R n P ≃
      PolynomialSystemSolutions S n (fun i => MvPolynomial.map φ (P i))) := by
  sorry

theorem henselian_countable_mittag_leffler
    {R M : Type u} [CommRing R] [HenselianLocalRing R]
    [AddCommGroup M] [Module R M]
    (hcountable : Formalization.Books.Algebra.Unit84.Module.IsCountablyGenerated R M)
    (hML : ModuleMittagLeffler (ModuleCat.of R M)) :
    ∃ (I : Type u) (N : I → ModuleCat R),
      (∀ i, Module.FinitePresentation R (N i)) ∧
        Nonempty ((M : Type u) ≃ₗ[R]
          DirectSum I (fun i : I => (N i : Type u))) := by
  sorry

/-! ## Filtered colimits of étale ring maps -/

/-- A chosen directed-colimit presentation all of whose stages are étale. -/
def IsFilteredColimitOfEtale
    {R A : Type u} [CommRing R] [CommRing A] (f : R →+* A) : Prop :=
  ∃ D : DirectedAlgebraColimit f,
    letI : Preorder D.index := D.indexPreorder
    ∀ i, RingHom.Etale (D.diagram.obj i).hom.hom

theorem base_change_colimit_etale
    {R A R' : Type u} [CommRing R] [CommRing A] [CommRing R']
    (f : R →+* A) (g : R →+* R')
    (h : IsFilteredColimitOfEtale f) :
    letI : Algebra R A := f.toAlgebra
    letI : Algebra R R' := g.toAlgebra
    IsFilteredColimitOfEtale
      (algebraMap R' (R' ⊗[R] A)) := by
  sorry

theorem composition_colimit_etale
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (f : A →+* B) (g : B →+* C)
    (hAB : IsFilteredColimitOfEtale f)
    (hBC : IsFilteredColimitOfEtale g) :
    IsFilteredColimitOfEtale (g.comp f) := by
  sorry

/-- Nested colimit data for the source's “colimit of colimits” lemma. -/
structure NestedEtaleColimitData (R A : Type u) [CommRing R] [CommRing A]
    (f : R →+* A) where
  outer : DirectedAlgebraColimit f
  inner : ∀ i, letI : Preorder outer.index := outer.indexPreorder
    IsFilteredColimitOfEtale (outer.diagram.obj i).hom.hom

/-- Two compatible directed ring colimits, with each stage map presented as a
filtered colimit of étale maps. -/
structure DirectedArrowColimitData (R A : Type u) [CommRing R] [CommRing A]
    (f : R →+* A) where
  index : Type u
  [indexPreorder : Preorder index]
  directed : IsDirectedSet index
  baseDiagram : System index CommRingCat
  targetDiagram : System index CommRingCat
  baseCocone : Cocone baseDiagram
  targetCocone : Cocone targetDiagram
  baseIsColimit : IsColimit baseCocone
  targetIsColimit : IsColimit targetCocone
  baseTargetIso : baseCocone.pt ≅ CommRingCat.of R
  targetTargetIso : targetCocone.pt ≅ CommRingCat.of A
  stageMap : ∀ i, (baseDiagram.obj i : Type u) →+*
    (targetDiagram.obj i : Type u)
  compatible : ∀ i,
    targetTargetIso.hom.hom.comp
        ((targetCocone.ι.app i).hom.comp (stageMap i)) =
      f.comp (baseTargetIso.hom.hom.comp ((baseCocone.ι.app i).hom))
  stage : ∀ i, IsFilteredColimitOfEtale (stageMap i)

theorem colimit_of_colimits_etale
    {R A : Type u} [CommRing R] [CommRing A] (f : R →+* A)
    (h : NestedEtaleColimitData R A f) : IsFilteredColimitOfEtale f := by
  sorry

theorem colimit_of_colimits_etale_better
    {R A : Type u} [CommRing R] [CommRing A] (f : R →+* A)
    (D : DirectedArrowColimitData R A f) :
    IsFilteredColimitOfEtale f := by
  sorry

theorem colimits_of_etale
    {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
    (f : R →+* A) (g : R →+* B)
    (hA : IsFilteredColimitOfEtale f)
    (hB : IsFilteredColimitOfEtale g)
    (φ : A →+* B) (hφ : φ.comp f = g) :
    IsFilteredColimitOfEtale φ := by
  sorry

theorem map_into_henselian_colimit
    {R A S : Type u} [CommRing R] [CommRing A] [CommRing S]
    [Algebra R A] [Algebra R S] [HenselianLocalRing S]
    (hA : IsFilteredColimitOfEtale (algebraMap R A))
    (q : PrimeSpectrum A)
    (hq : q.asIdeal.comap (algebraMap R A) =
      (IsLocalRing.maximalIdeal S).comap (algebraMap R S))
    (τ : ResidueFieldCompatibility (R := R) (S := S) q hq) :
    ∃! f : A →ₐ[R] S,
      PrimeSpectrum.comap f.toRingHom (maximalPrime S) = q ∧
        ∀ a : A, τ.map (algebraMap (A ⧸ q.asIdeal) q.asIdeal.ResidueField
          (Ideal.Quotient.mk q.asIdeal a)) =
          IsLocalRing.residue S (f a) := by
  sorry

theorem uniqueness_henselian_colimit
    {R S S' K : Type u} [CommRing R] [CommRing S] [CommRing S']
    [Field K] [Algebra R K] [Algebra R S] [Algebra R S']
    [HenselianLocalRing S] [HenselianLocalRing S']
    (hS : IsFilteredColimitOfEtale (algebraMap R S))
    (hS' : IsFilteredColimitOfEtale (algebraMap R S'))
    (e : S →+* K) (e' : S' →+* K)
    (he : IsLocalHom e) (he' : IsLocalHom e')
    (he_surj : Function.Surjective e) (he'_surj : Function.Surjective e')
    (e_over : e.comp (algebraMap R S) = algebraMap R K)
    (e'_over : e'.comp (algebraMap R S') = algebraMap R K) :
    ∃! α : S ≃ₐ[R] S', e'.comp α.toRingHom = e := by
  sorry

theorem colimit_henselian_local
    {R A : Type u} [CommRing R] [CommRing A]
    (f : R →+* A) (D : DirectedAlgebraColimit f)
    (hstage : letI : Preorder D.index := D.indexPreorder
      ∀ i, HenselianLocalRing (D.diagram.obj i).right)
    (hloc : letI : Preorder D.index := D.indexPreorder
      ∀ {i j} (hij : i ≤ j),
      IsLocalHom (D.diagram.map (homOfLE hij)).right.hom) :
    HenselianLocalRing A := by
  sorry

theorem colimit_strictly_henselian_local
    {R A : Type u} [CommRing R] [CommRing A]
    (f : R →+* A) (D : DirectedAlgebraColimit f)
    (hstage : letI : Preorder D.index := D.indexPreorder
      ∀ i, StrictlyHenselianLocalRing (D.diagram.obj i).right)
    (hloc : letI : Preorder D.index := D.indexPreorder
      ∀ {i j} (hij : i ≤ j),
      IsLocalHom (D.diagram.map (homOfLE hij)).right.hom) :
    StrictlyHenselianLocalRing A := by
  sorry

/-! ## Henselization and strict henselization -/

/-- Data supplied by the henselization existence lemma. -/
structure HenselizationData (R : Type u) [CommRing R] [IsLocalRing R] where
  Rh : Type u
  [commRingRh : CommRing Rh]
  [algebraRRh : Algebra R Rh]
  [localRh : IsLocalRing Rh]
  map_local : IsLocalHom (algebraMap R Rh)
  flat : RingHom.Flat (algebraMap R Rh)
  henselian : HenselianLocalRing Rh
  etaleColimit : IsFilteredColimitOfEtale (algebraMap R Rh)
  maximalIdeal_map : Ideal.map (algebraMap R Rh) (IsLocalRing.maximalIdeal R) =
    IsLocalRing.maximalIdeal Rh
  residueEquiv : Nonempty
    (IsLocalRing.ResidueField R ≃+* IsLocalRing.ResidueField Rh)

theorem exists_henselization
    (R : Type u) [CommRing R] [IsLocalRing R] :
    Nonempty (HenselizationData R) := by
  sorry

/-- A selected henselization datum.  The choice is noncomputable because the
source constructs it as a filtered colimit. -/
noncomputable def henselization
    (R : Type u) [CommRing R] [IsLocalRing R] : HenselizationData R :=
  Classical.choice (exists_henselization R)

/-- The selected local map into the henselization. -/
noncomputable def henselizationMap
    (R : Type u) [CommRing R] [IsLocalRing R] :
    let H := henselization R
    letI : CommRing H.Rh := H.commRingRh
    letI : Algebra R H.Rh := H.algebraRRh
    R →+* H.Rh :=
  let H := henselization R
  letI : CommRing H.Rh := H.commRingRh
  letI : Algebra R H.Rh := H.algebraRRh
  algebraMap R H.Rh

/-- Data for a strict henselization relative to a chosen separable algebraic
closure of the residue field. -/
structure StrictHenselizationData
    (R K : Type u) [CommRing R] [IsLocalRing R] [Field K]
    [Algebra (IsLocalRing.ResidueField R) K] where
  Rsh : Type u
  [commRingRsh : CommRing Rsh]
  [algebraRRsh : Algebra R Rsh]
  [localRsh : IsLocalRing Rsh]
  local_map : IsLocalHom (algebraMap R Rsh)
  flat : RingHom.Flat (algebraMap R Rsh)
  strict_henselian : StrictlyHenselianLocalRing Rsh
  etaleColimit : IsFilteredColimitOfEtale (algebraMap R Rsh)
  maximalIdeal_map : Ideal.map (algebraMap R Rsh) (IsLocalRing.maximalIdeal R) =
    IsLocalRing.maximalIdeal Rsh
  residueEquiv : Nonempty (IsLocalRing.ResidueField Rsh ≃+* K)

theorem exists_strict_henselization
    (R K : Type u) [CommRing R] [IsLocalRing R] [Field K]
    [Algebra (IsLocalRing.ResidueField R) K]
    [Algebra.IsAlgebraic (IsLocalRing.ResidueField R) K]
    [Algebra.IsSeparable (IsLocalRing.ResidueField R) K] [IsSepClosed K] :
    Nonempty (StrictHenselizationData R K) := by
  sorry

/-- A selected strict henselization datum. -/
noncomputable def strictHenselization
    (R K : Type u) [CommRing R] [IsLocalRing R] [Field K]
    [Algebra (IsLocalRing.ResidueField R) K]
    [Algebra.IsAlgebraic (IsLocalRing.ResidueField R) K]
    [Algebra.IsSeparable (IsLocalRing.ResidueField R) K] [IsSepClosed K] :
    StrictHenselizationData R K :=
  Classical.choice (exists_strict_henselization R K)

/-- A ring map satisfying the defining universal properties of the
henselization constructed above. -/
def IsHenselizationMap
    {R Rh : Type u} [CommRing R] [IsLocalRing R]
    [CommRing Rh] [IsLocalRing Rh] (f : R →+* Rh) : Prop :=
  IsLocalHom f ∧ RingHom.Flat f ∧ HenselianLocalRing Rh ∧
    IsFilteredColimitOfEtale f ∧
      Ideal.map f (IsLocalRing.maximalIdeal R) = IsLocalRing.maximalIdeal Rh ∧
        Nonempty (IsLocalRing.ResidueField R ≃+*
          IsLocalRing.ResidueField Rh)

/-- The corresponding defining predicate for a strict henselization relative
to a chosen separable algebraic residue-field extension. -/
def IsStrictHenselizationMap
    {R Rh K : Type u} [CommRing R] [IsLocalRing R]
    [CommRing Rh] [IsLocalRing Rh] [Field K]
    [Algebra (IsLocalRing.ResidueField R) K]
    (f : R →+* Rh) : Prop :=
    IsHenselizationMap f ∧ StrictlyHenselianLocalRing Rh ∧
    Nonempty (IsLocalRing.ResidueField Rh ≃+* K)

/- A finite étale local lift of a finite separable residue-field extension.
This packages the finite stages used in the source's construction of the
strict henselization from the henselization. -/
structure FiniteEtaleResidueStage
    (R K' : Type u) [CommRing R] [IsLocalRing R] [Field K']
    [Algebra (IsLocalRing.ResidueField R) K'] where
  A : Type u
  [commRingA : CommRing A]
  [algebraRA : Algebra R A]
  [localA : IsLocalRing A]
  local_map : IsLocalHom (algebraMap R A)
  finite : RingHom.Finite (algebraMap R A)
  etale : Algebra.Etale R A
  residueEquiv : IsLocalRing.ResidueField A ≃+* K'
  residue_over_base : ∀ r : R,
    residueEquiv (IsLocalRing.residue A (algebraMap R A r)) =
      algebraMap (IsLocalRing.ResidueField R) K'
        (IsLocalRing.residue R r)

theorem finite_etale_residue_stage
    (R K' : Type u) [CommRing R] [IsLocalRing R] [Field K']
    [Algebra (IsLocalRing.ResidueField R) K']
    [FiniteDimensional (IsLocalRing.ResidueField R) K']
    [Algebra.IsSeparable (IsLocalRing.ResidueField R) K'] :
    Nonempty (FiniteEtaleResidueStage R K') := by
  sorry

/-- The source's finite étale construction of a strict henselization from the
henselization. -/
structure StrictHenselizationAsUnion
    (R K : Type u) [CommRing R] [IsLocalRing R] [Field K]
    [Algebra (IsLocalRing.ResidueField R) K]
    [Algebra.IsAlgebraic (IsLocalRing.ResidueField R) K]
    [Algebra.IsSeparable (IsLocalRing.ResidueField R) K] [IsSepClosed K] where
  h : HenselizationData R
  strict : StrictHenselizationData R K
  finiteStage : ∀ (K' : Type u) [Field K']
    [Algebra (IsLocalRing.ResidueField R) K'] [Algebra K' K]
    [IsScalarTower (IsLocalRing.ResidueField R) K' K]
    [FiniteDimensional (IsLocalRing.ResidueField R) K']
    [Algebra.IsSeparable (IsLocalRing.ResidueField R) K'],
    Nonempty (FiniteEtaleResidueStage R K')
  residueStages : IsSepClosed K

theorem strict_henselization_from_henselization
    (R K : Type u) [CommRing R] [IsLocalRing R] [Field K]
    [Algebra (IsLocalRing.ResidueField R) K]
    [Algebra.IsAlgebraic (IsLocalRing.ResidueField R) K]
    [Algebra.IsSeparable (IsLocalRing.ResidueField R) K] [IsSepClosed K] :
    Nonempty (StrictHenselizationAsUnion R K) := by
  sorry

theorem henselization_to_strict_is_flat_local
    {R K : Type u} [CommRing R] [IsLocalRing R] [Field K]
    [Algebra (IsLocalRing.ResidueField R) K]
    [Algebra.IsAlgebraic (IsLocalRing.ResidueField R) K]
    [Algebra.IsSeparable (IsLocalRing.ResidueField R) K] [IsSepClosed K]
    (D : StrictHenselizationAsUnion R K) :
    letI : CommRing D.h.Rh := D.h.commRingRh
    letI : CommRing D.strict.Rsh := D.strict.commRingRsh
    ∃ f : D.h.Rh →+* D.strict.Rsh, IsLocalHom f ∧ RingHom.Flat f := by
  sorry

theorem henselian_functorial_prepare
    {R S A : Type u} [CommRing R] [CommRing S] [CommRing A]
    [IsLocalRing R] [IsLocalRing S] [Algebra R A] [Algebra R S]
    (φ : R →ₐ[R] S) (hφ : IsLocalHom φ.toRingHom)
    (Sh : HenselizationData S) (hA : Algebra.Etale R A)
    (q : PrimeSpectrum A)
    (hq : q.asIdeal.comap (algebraMap R A) = IsLocalRing.maximalIdeal R)
    (hq_residue : Nonempty
      (IsLocalRing.ResidueField R ≃+* q.asIdeal.ResidueField)) :
    letI : CommRing Sh.Rh := Sh.commRingRh
    letI : IsLocalRing Sh.Rh := Sh.localRh
    letI : Algebra S Sh.Rh := Sh.algebraRRh
    ∃! f : A →+* Sh.Rh,
      f.comp (algebraMap R A) =
          (algebraMap S Sh.Rh).comp φ.toRingHom ∧
        PrimeSpectrum.comap f (maximalPrime Sh.Rh) = q := by
  sorry

theorem henselization_maps_functorially
    {R S : Type u} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S]
    (φ : R →+* S) (hφ : IsLocalHom φ)
    (Rh : HenselizationData R) (Sh : HenselizationData S) :
    letI : CommRing Rh.Rh := Rh.commRingRh
    letI : CommRing Sh.Rh := Sh.commRingRh
    letI : Algebra R Rh.Rh := Rh.algebraRRh
    letI : Algebra S Sh.Rh := Sh.algebraRRh
    ∃! f : Rh.Rh →+* Sh.Rh,
      IsLocalHom f ∧
        f.comp (algebraMap R Rh.Rh) =
          (algebraMap S Sh.Rh).comp φ := by
  sorry

/- The two presentations in the alternative construction of a henselization
are kept as explicit colimit presentations, with their canonical comparison. -/
structure HenselizationDifferentData
    (R : Type u) [CommRing R] (p : PrimeSpectrum R) (Rh : Type u)
    [CommRing Rh]
    [Algebra (Localization.AtPrime p.asIdeal) Rh] where
  pairPresentation :
    DirectedAlgebraColimit
      (algebraMap (Localization.AtPrime p.asIdeal) Rh)
  localizedPresentation :
    DirectedAlgebraColimit
      (algebraMap (Localization.AtPrime p.asIdeal) Rh)
  comparison :
    letI : Preorder pairPresentation.index := pairPresentation.indexPreorder
    letI : Preorder localizedPresentation.index :=
      localizedPresentation.indexPreorder
    pairPresentation.cocone.pt ≅ localizedPresentation.cocone.pt

theorem henselization_different
    (R : Type u) [CommRing R] (p : PrimeSpectrum R)
    (Rh : HenselizationData (Localization.AtPrime p.asIdeal)) :
    letI : CommRing Rh.Rh := Rh.commRingRh
    letI : Algebra (Localization.AtPrime p.asIdeal) Rh.Rh := Rh.algebraRRh
    Nonempty (HenselizationDifferentData R p Rh.Rh) := by
  sorry

theorem henselization_functorial_improved
    {R S : Type u} [CommRing R] [CommRing S]
    (φ : R →+* S) (p : PrimeSpectrum R) (q : PrimeSpectrum S)
    (hq : q.asIdeal.comap φ = p.asIdeal)
    (Rh : HenselizationData (Localization.AtPrime p.asIdeal))
    (Sh : HenselizationData (Localization.AtPrime q.asIdeal)) :
    letI : CommRing Rh.Rh := Rh.commRingRh
    letI : CommRing Sh.Rh := Sh.commRingRh
    letI : Algebra (Localization.AtPrime p.asIdeal) Rh.Rh := Rh.algebraRRh
    letI : Algebra (Localization.AtPrime q.asIdeal) Sh.Rh := Sh.algebraRRh
    Nonempty {f : Rh.Rh →+* Sh.Rh // IsLocalHom f} := by
  sorry

theorem strictly_henselian_functorial_prepare
    {R S A L : Type u} [CommRing R] [CommRing S] [CommRing A]
    [IsLocalRing R] [IsLocalRing S] [Algebra R A] [Algebra R S]
    [Field L] [Algebra (IsLocalRing.ResidueField S) L]
    (φ : R →ₐ[R] S) (hφ : IsLocalHom φ.toRingHom)
    (Sh : StrictHenselizationData S L) (hA : Algebra.Etale R A)
    (q : PrimeSpectrum A)
    (hq : q.asIdeal.comap (algebraMap R A) = IsLocalRing.maximalIdeal R)
    (τ : StrictResidueFieldCompatibility (R := R) (S := S) (L := L)
      φ q hq) :
    letI : CommRing Sh.Rsh := Sh.commRingRsh
    letI : IsLocalRing Sh.Rsh := Sh.localRsh
    letI : Algebra S Sh.Rsh := Sh.algebraRRsh
    ∃! f : A →+* Sh.Rsh,
      f.comp (algebraMap R A) =
          (algebraMap S Sh.Rsh).comp φ.toRingHom ∧
        PrimeSpectrum.comap f (maximalPrime Sh.Rsh) = q := by
  sorry

theorem strict_henselization_functorial
    {R S K L : Type u} [CommRing R] [CommRing S] [IsLocalRing R]
    [IsLocalRing S] [Field K] [Field L]
    [Algebra (IsLocalRing.ResidueField R) K]
    [Algebra (IsLocalRing.ResidueField S) L]
    [Algebra.IsAlgebraic (IsLocalRing.ResidueField R) K]
    [Algebra.IsSeparable (IsLocalRing.ResidueField R) K]
    [Algebra.IsAlgebraic (IsLocalRing.ResidueField S) L]
    [Algebra.IsSeparable (IsLocalRing.ResidueField S) L]
    [IsSepClosed K] [IsSepClosed L]
    (φ : R →+* S) (hφ : IsLocalHom φ)
    (ψ : K →+* L)
    (hψ : ∀ r : R,
      ψ (algebraMap (IsLocalRing.ResidueField R) K
        (IsLocalRing.residue R r)) =
        algebraMap (IsLocalRing.ResidueField S) L
          (IsLocalRing.residue S (φ r)))
    (Rh : StrictHenselizationData R K)
    (Sh : StrictHenselizationData S L) :
    letI : CommRing Rh.Rsh := Rh.commRingRsh
    letI : CommRing Sh.Rsh := Sh.commRingRsh
    letI : Algebra R Rh.Rsh := Rh.algebraRRsh
    letI : Algebra S Sh.Rsh := Sh.algebraRRsh
    ∃! f : Rh.Rsh →+* Sh.Rsh,
      IsLocalHom f ∧
        f.comp (algebraMap R Rh.Rsh) =
          (algebraMap S Sh.Rsh).comp φ := by
  sorry

structure StrictHenselizationDifferentData
    (R : Type u) [CommRing R] (p : PrimeSpectrum R) (Rsh : Type u)
    [CommRing Rsh]
    [Algebra (Localization.AtPrime p.asIdeal) Rsh] where
  pairPresentation :
    DirectedAlgebraColimit
      (algebraMap (Localization.AtPrime p.asIdeal) Rsh)
  localizedPresentation :
    DirectedAlgebraColimit
      (algebraMap (Localization.AtPrime p.asIdeal) Rsh)
  comparison :
    letI : Preorder pairPresentation.index := pairPresentation.indexPreorder
    letI : Preorder localizedPresentation.index :=
      localizedPresentation.indexPreorder
    pairPresentation.cocone.pt ≅ localizedPresentation.cocone.pt

theorem strict_henselization_different
    (R : Type u) [CommRing R] (p : PrimeSpectrum R) (K : Type u)
    [Field K]
    [Algebra (IsLocalRing.ResidueField (Localization.AtPrime p.asIdeal)) K]
    [Algebra.IsAlgebraic (IsLocalRing.ResidueField
      (Localization.AtPrime p.asIdeal)) K]
    [Algebra.IsSeparable (IsLocalRing.ResidueField
      (Localization.AtPrime p.asIdeal)) K] [IsSepClosed K]
    (Rsh : StrictHenselizationData (Localization.AtPrime p.asIdeal) K) :
    letI : CommRing Rsh.Rsh := Rsh.commRingRsh
    letI : Algebra (Localization.AtPrime p.asIdeal) Rsh.Rsh := Rsh.algebraRRsh
    Nonempty (StrictHenselizationDifferentData R p Rsh.Rsh) := by
  sorry

theorem strictly_henselian_functorial_improved
    {R S K L : Type u} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S] [Field K] [Field L]
    [Algebra (IsLocalRing.ResidueField R) K]
    [Algebra (IsLocalRing.ResidueField S) L]
    [Algebra.IsAlgebraic (IsLocalRing.ResidueField R) K]
    [Algebra.IsSeparable (IsLocalRing.ResidueField R) K]
    [Algebra.IsAlgebraic (IsLocalRing.ResidueField S) L]
    [Algebra.IsSeparable (IsLocalRing.ResidueField S) L]
    [IsSepClosed K] [IsSepClosed L]
    (φ : R →+* S) (p : PrimeSpectrum R) (q : PrimeSpectrum S)
    (hq : q.asIdeal.comap φ = p.asIdeal)
    (ψ : K →+* L)
    (hψ : ∀ r : R,
      ψ (algebraMap (IsLocalRing.ResidueField R) K
        (IsLocalRing.residue R r)) =
        algebraMap (IsLocalRing.ResidueField S) L
          (IsLocalRing.residue S (φ r)))
    [Algebra (IsLocalRing.ResidueField (Localization.AtPrime p.asIdeal)) K]
    [Algebra (IsLocalRing.ResidueField (Localization.AtPrime q.asIdeal)) L]
    (Rh : StrictHenselizationData (Localization.AtPrime p.asIdeal) K)
    (Sh : StrictHenselizationData (Localization.AtPrime q.asIdeal) L) :
    letI : CommRing Rh.Rsh := Rh.commRingRsh
    letI : CommRing Sh.Rsh := Sh.commRingRsh
    Nonempty {f : Rh.Rsh →+* Sh.Rsh // IsLocalHom f} := by
  sorry

theorem strict_henselization_from_henselization_map
    {R S K : Type u} [CommRing R] [CommRing S]
    [Field K] [IsSepClosed K]
    (φ : R →+* S) (p : PrimeSpectrum R) (q : PrimeSpectrum S)
    (hq : q.asIdeal.comap φ = p.asIdeal)
    (hres : Nonempty
      (IsLocalRing.ResidueField (Localization.AtPrime p.asIdeal) ≃+*
        IsLocalRing.ResidueField (Localization.AtPrime q.asIdeal)))
    [Algebra (IsLocalRing.ResidueField (Localization.AtPrime p.asIdeal)) K]
    [Algebra (IsLocalRing.ResidueField (Localization.AtPrime q.asIdeal)) K]
    [Algebra.IsAlgebraic
      (IsLocalRing.ResidueField (Localization.AtPrime p.asIdeal)) K]
    [Algebra.IsSeparable
      (IsLocalRing.ResidueField (Localization.AtPrime p.asIdeal)) K]
    [Algebra.IsAlgebraic
      (IsLocalRing.ResidueField (Localization.AtPrime q.asIdeal)) K]
    [Algebra.IsSeparable
      (IsLocalRing.ResidueField (Localization.AtPrime q.asIdeal)) K]
    (Rh : HenselizationData (Localization.AtPrime p.asIdeal))
    (Sh : HenselizationData (Localization.AtPrime q.asIdeal))
    (Rsh : StrictHenselizationData (Localization.AtPrime p.asIdeal) K)
    (Ssh : StrictHenselizationData (Localization.AtPrime q.asIdeal) K)
    [CommRing Rh.Rh] [CommRing Sh.Rh] [CommRing Rsh.Rsh] [CommRing Ssh.Rsh]
    [Algebra Rh.Rh Sh.Rh] [Algebra Rh.Rh Rsh.Rsh] :
    Nonempty (Ssh.Rsh ≃+* (Sh.Rh ⊗[Rh.Rh] Rsh.Rsh)) := by
  sorry

end

end Formalization.Books.Algebra.Unit153
