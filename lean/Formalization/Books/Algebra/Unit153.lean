import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.DirectSum.Module
import Mathlib.FieldTheory.IsSepClosed
import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.RingTheory.Etale.Finite
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Mathlib.RingTheory.MvPolynomial
import Mathlib.RingTheory.RingHom.Etale
import Mathlib.RingTheory.RingHom.QuasiFinite
import Mathlib.RingTheory.RingHom.Unramified
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.Topology.KrullDimension

/-!
# Commutative Algebra, Chapter 153: Henselian local rings

This file formalizes the definitions and theorem interfaces in the source
section `Henselian local rings`.
-/

namespace Formalization.Books.Algebra.Unit153

open CategoryTheory
open Polynomial
open Set
open scoped TensorProduct

noncomputable section

universe u v w

/-! ## Henselianity and the root-lifting formulation -/

/-- The prime of a local ring defined by its maximal ideal. -/
def maximalPrime (R : Type u) [CommRing R] [IsLocalRing R] : PrimeSpectrum R :=
  ⟨IsLocalRing.maximalIdeal R, inferInstance⟩

/-- The source's henselian predicate, using Mathlib's canonical class. -/
abbrev IsHenselian (R : Type u) [CommRing R] [IsLocalRing R] : Prop :=
  HenselianLocalRing R

/-- A henselian local ring whose residue field is separably algebraically
closed. -/
class StrictlyHenselianLocalRing (R : Type u) [CommRing R]
    extends HenselianLocalRing R where
  [separablyClosed : IsSepClosed (IsLocalRing.ResidueField R)]

/-- Reduction of a polynomial to the residue field. -/
def residuePolynomial (R : Type u) [CommRing R] [IsLocalRing R]
    (f : Polynomial R) : Polynomial (IsLocalRing.ResidueField R) :=
  f.map (IsLocalRing.residue R)

/-- A root of the reduced polynomial is simple when its derivative is nonzero. -/
def IsSimpleResidueRoot (R : Type u) [CommRing R] [IsLocalRing R]
    (f : Polynomial R) (a₀ : IsLocalRing.ResidueField R) : Prop :=
  (residuePolynomial R f).IsRoot a₀ ∧
    (residuePolynomial R f).derivative.eval a₀ ≠ 0

theorem isSimpleResidueRoot_iff
    (R : Type u) [CommRing R] [IsLocalRing R] (f : Polynomial R)
    (a₀ : IsLocalRing.ResidueField R) :
    IsSimpleResidueRoot R f a₀ ↔
      (residuePolynomial R f).IsRoot a₀ ∧
        (residuePolynomial R f).derivative.eval a₀ ≠ 0 :=
  Iff.rfl

theorem residuePolynomial_derivative
    (R : Type u) [CommRing R] [IsLocalRing R] (f : Polynomial R) :
    (residuePolynomial R f).derivative = residuePolynomial R f.derivative := by
  simp [residuePolynomial]

/-- The root-lifting definition of henselianity in the source. -/
def HenselianRootLifting (R : Type u) [CommRing R] [IsLocalRing R] : Prop :=
  ∀ f : Polynomial R, f.Monic → ∀ a₀ : IsLocalRing.ResidueField R,
    IsSimpleResidueRoot R f a₀ →
      ∃ a : R, f.IsRoot a ∧ IsLocalRing.residue R a = a₀

/- The uniqueness assertion following the definition. -/
theorem root_lift_unique
    {R : Type u} [CommRing R] [IsLocalRing R]
    (f : Polynomial R) {a b : R}
    (ha : f.eval a = 0) (hb : f.eval b = 0)
    (hab : a - b ∈ IsLocalRing.maximalIdeal R)
    (hderiv : f.derivative.eval a ∉ IsLocalRing.maximalIdeal R) :
    a = b := by
  sorry

/-! ## The thirteen equivalent characterizations -/

/-- A monic factorization of the special-fibre polynomial lifts upstairs. -/
def MonicFactorizationLift (R : Type u) [CommRing R] [IsLocalRing R] : Prop :=
  ∀ f : Polynomial R, f.Monic →
    ∀ g₀ h₀ : Polynomial (IsLocalRing.ResidueField R),
      residuePolynomial R f = g₀ * h₀ → IsCoprime g₀ h₀ →
        ∃ g h : Polynomial R,
          f = g * h ∧ residuePolynomial R g = g₀ ∧
            residuePolynomial R h = h₀

/-- The monic factorization characterization with degree preservation. -/
def MonicDegreeFactorizationLift
    (R : Type u) [CommRing R] [IsLocalRing R] : Prop :=
  ∀ f : Polynomial R, f.Monic →
    ∀ g₀ h₀ : Polynomial (IsLocalRing.ResidueField R),
      residuePolynomial R f = g₀ * h₀ → IsCoprime g₀ h₀ →
        ∃ g h : Polynomial R,
          f = g * h ∧ residuePolynomial R g = g₀ ∧
            residuePolynomial R h = h₀ ∧ g.degree = g₀.degree

/-- The unrestricted factorization characterization. -/
def FactorizationLift (R : Type u) [CommRing R] [IsLocalRing R] : Prop :=
  ∀ f : Polynomial R,
    ∀ g₀ h₀ : Polynomial (IsLocalRing.ResidueField R),
      residuePolynomial R f = g₀ * h₀ → IsCoprime g₀ h₀ →
        ∃ g h : Polynomial R,
          f = g * h ∧ residuePolynomial R g = g₀ ∧
            residuePolynomial R h = h₀

/-- The unrestricted factorization characterization with degree preservation. -/
def DegreeFactorizationLift
    (R : Type u) [CommRing R] [IsLocalRing R] : Prop :=
  ∀ f : Polynomial R,
    ∀ g₀ h₀ : Polynomial (IsLocalRing.ResidueField R),
      residuePolynomial R f = g₀ * h₀ → IsCoprime g₀ h₀ →
        ∃ g h : Polynomial R,
          f = g * h ∧ residuePolynomial R g = g₀ ∧
            residuePolynomial R h = h₀ ∧ g.degree = g₀.degree

/-- Existence of an étale retraction over a point with the same residue field. -/
def EtaleRetractionProperty (R : Type u) [CommRing R] [IsLocalRing R] : Prop :=
  ∀ {A : Type u} [CommRing A] [Algebra R A]
    (_hA : Prop) (q : PrimeSpectrum A)
    (_hq : q.asIdeal.comap (algebraMap R A) = IsLocalRing.maximalIdeal R)
    (_hqResidue : q.asIdeal.ResidueField = IsLocalRing.ResidueField R),
    Nonempty (A →ₐ[R] R)

/-- The unique étale retraction characterization. -/
def UniqueEtaleRetractionProperty
    (R : Type u) [CommRing R] [IsLocalRing R] : Prop :=
  ∀ {A : Type u} [CommRing A] [Algebra R A]
    (_hA : Prop) (q : PrimeSpectrum A)
    (_hq : q.asIdeal.comap (algebraMap R A) = IsLocalRing.maximalIdeal R)
    (_hqResidue : q.asIdeal.ResidueField = IsLocalRing.ResidueField R),
    ∃! f : A →ₐ[R] R,
      PrimeSpectrum.comap f.toRingHom (maximalPrime R) = q

/-- Data expressing a product of local `R`-algebras. -/
structure ProductOfLocalAlgebras
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] where
  index : Type u
  factor : index → Type u
  [commRingFactor : ∀ i, CommRing (factor i)]
  [algebraFactor : ∀ i, Algebra R (factor i)]
  [localFactor : ∀ i, IsLocalRing (factor i)]
  decomposition : Nonempty (S ≃ₐ[R] (∀ i, factor i))

/-- Data expressing a finite product of local `R`-algebras. -/
structure FiniteProductOfLocalAlgebras
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] where
  n : ℕ
  factor : Fin n → Type u
  [commRingFactor : ∀ i, CommRing (factor i)]
  [algebraFactor : ∀ i, Algebra R (factor i)]
  [localFactor : ∀ i, IsLocalRing (factor i)]
  decomposition : Nonempty (S ≃ₐ[R] (∀ i, factor i))

/-- Data for the finite/non-quasi-finite decomposition of a finite-type algebra. -/
structure FiniteTypePartData
    (R S : Type u) [CommRing R] [CommRing S] [IsLocalRing R] [Algebra R S] where
  A : Type u
  [commRingA : CommRing A]
  [algebraRA : Algebra R A]
  B : Type u
  [commRingB : CommRing B]
  [algebraRB : Algebra R B]
  finiteA : RingHom.Finite (algebraMap R A)
  decomposition : Nonempty (S ≃ₐ[R] A × B)
  noQuasiFiniteAt : ∀ q : PrimeSpectrum B,
    q.asIdeal.comap (algebraMap R B) = IsLocalRing.maximalIdeal R →
      ¬ RingHom.QuasiFiniteAt (algebraMap R B) q.asIdeal

/-- The positive-dimensional special-fibre condition in characterization (12). -/
def PositiveDimensionalFiber
    (R B : Type u) [CommRing R] [CommRing B] [IsLocalRing R]
    [Algebra R B] : Prop :=
  ∀ C ∈ irreducibleComponents
      (PrimeSpectrum (B ⊗[R] IsLocalRing.ResidueField R)),
    1 ≤ topologicalKrullDim C

/-- Data for the positive-dimensional special-fibre decomposition. -/
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
  decomposition : Nonempty (S ≃ₐ[R] A × B)
  positiveDimensionalFiber : PositiveDimensionalFiber R B

/-- Data for the quasi-finite decomposition with zero special fibre remainder. -/
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
  decomposition : Nonempty (S ≃ₐ[R] A × B)
  specialFiberZero : ∀ x : B ⊗[R] IsLocalRing.ResidueField R, x = 0

def ProductOfLocalAlgebrasProperty
    (R : Type u) [CommRing R] [IsLocalRing R] : Prop :=
  ∀ {S : Type u} [CommRing S] [Algebra R S],
    RingHom.Finite (algebraMap R S) → Nonempty (ProductOfLocalAlgebras R S)

def FiniteProductOfLocalAlgebrasProperty
    (R : Type u) [CommRing R] [IsLocalRing R] : Prop :=
  ∀ {S : Type u} [CommRing S] [Algebra R S],
    RingHom.Finite (algebraMap R S) →
      Nonempty (FiniteProductOfLocalAlgebras R S)

def FiniteTypePartProperty
    (R : Type u) [CommRing R] [IsLocalRing R] : Prop :=
  ∀ {S : Type u} [CommRing S] [Algebra R S],
    Algebra.FiniteType R S → Nonempty (FiniteTypePartData R S)

def PositiveDimensionalPartProperty
    (R : Type u) [CommRing R] [IsLocalRing R] : Prop :=
  ∀ {S : Type u} [CommRing S] [Algebra R S],
    Algebra.FiniteType R S → Nonempty (PositiveDimensionalPartData R S)

def QuasiFinitePartProperty
    (R : Type u) [CommRing R] [IsLocalRing R] : Prop :=
  ∀ {S : Type u} [CommRing S] [Algebra R S],
    RingHom.QuasiFinite (algebraMap R S) → Nonempty (QuasiFinitePartData R S)

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
        ProductOfLocalAlgebrasProperty R,
        FiniteProductOfLocalAlgebrasProperty R,
        FiniteTypePartProperty R,
        PositiveDimensionalPartProperty R,
        QuasiFinitePartProperty R ] := by
  sorry

/-! ## Finite algebras and finite-type decompositions -/

structure FiniteHenselianLocalProductData
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] where
  n : ℕ
  factor : Fin n → Type u
  [commRingFactor : ∀ i, CommRing (factor i)]
  [algebraFactor : ∀ i, Algebra R (factor i)]
  [localFactor : ∀ i, IsLocalRing (factor i)]
  [henselianFactor : ∀ i, HenselianLocalRing (factor i)]
  finiteFactor : ∀ i, RingHom.Finite (algebraMap R (factor i))
  decomposition : Nonempty (S ≃ₐ[R] (∀ i, factor i))

theorem finite_over_henselian
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [HenselianLocalRing R] (hS : RingHom.Finite (algebraMap R S)) :
    Nonempty (FiniteHenselianLocalProductData R S) := by
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

structure MopUpData
    (R S : Type u) [CommRing R] [CommRing S] [IsLocalRing R] [Algebra R S] where
  n : ℕ
  A : Fin n → Type u
  [commRingA : ∀ i, CommRing (A i)]
  [algebraRA : ∀ i, Algebra R (A i)]
  [localA : ∀ i, IsLocalRing (A i)]
  B : Type u
  [commRingB : CommRing B]
  [algebraRB : Algebra R B]
  finiteA : ∀ i, RingHom.Finite (algebraMap R (A i))
  decomposition : Nonempty (S ≃ₐ[R] (∀ i, A i) × B)
  noQuasiFiniteAt : ∀ q : PrimeSpectrum B,
    q.asIdeal.comap (algebraMap R B) = IsLocalRing.maximalIdeal R →
      ¬ RingHom.QuasiFiniteAt (algebraMap R B) q.asIdeal

theorem henselian_finite_type_decomposition
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [HenselianLocalRing R] [Algebra.FiniteType R S] :
    Nonempty (MopUpData R S) := by
  sorry

structure StrictMopUpData
    (R S : Type u) [CommRing R] [CommRing S] [IsLocalRing R] [Algebra R S] where
  n : ℕ
  A : Fin n → Type u
  [commRingA : ∀ i, CommRing (A i)]
  [algebraRA : ∀ i, Algebra R (A i)]
  [localA : ∀ i, IsLocalRing (A i)]
  B : Type u
  [commRingB : CommRing B]
  [algebraRB : Algebra R B]
  finiteA : ∀ i, RingHom.Finite (algebraMap R (A i))
  decomposition : Nonempty (S ≃ₐ[R] (∀ i, A i) × B)
  noQuasiFiniteAt : ∀ q : PrimeSpectrum B,
    q.asIdeal.comap (algebraMap R B) = IsLocalRing.maximalIdeal R →
      ¬ RingHom.QuasiFiniteAt (algebraMap R B) q.asIdeal
  residueAlgebra : ∀ i,
    Algebra (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField (A i))
  residueAlgebraMap : ∀ (i : Fin n) (r : R),
    algebraMap (IsLocalRing.ResidueField R)
        (IsLocalRing.ResidueField (A i)) (IsLocalRing.residue R r) =
      IsLocalRing.residue (A i) (algebraMap R (A i) r)
  residueFinite : ∀ i,
    Module.Finite (IsLocalRing.ResidueField R)
      (IsLocalRing.ResidueField (A i))
  residuePurelyInseparable : ∀ i,
    @IsPurelyInseparable (IsLocalRing.ResidueField R)
      (IsLocalRing.ResidueField (A i))
      (inferInstance : CommRing (IsLocalRing.ResidueField R))
      (inferInstance : Ring (IsLocalRing.ResidueField (A i)))
      (residueAlgebra i)

theorem strictly_henselian_finite_type_decomposition
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [StrictlyHenselianLocalRing R] [Algebra.FiniteType R S] :
    Nonempty (StrictMopUpData R S) := by
  sorry

/-! ## Finite étale and unramified algebras -/

/-- Base change of finite étale algebras to the residue field. -/
def finiteEtaleSpecialFiber
    (R : Type u) [CommRing R] [IsLocalRing R] :
    CommAlgCat.FiniteEtale R ⥤
      CommAlgCat.FiniteEtale (IsLocalRing.ResidueField R) :=
  CommAlgCat.FiniteEtale.baseChange R (IsLocalRing.ResidueField R)

theorem finite_etale_residue_equivalence
    (R : Type u) [CommRing R] [HenselianLocalRing R] :
    (finiteEtaleSpecialFiber R).IsEquivalence := by
  sorry

structure StrictUnramifiedDecompositionData
    (R S : Type u) [CommRing R] [CommRing S] [IsLocalRing R]
    [Algebra R S] where
  n : ℕ
  A : Fin n → Type u
  [commRingA : ∀ i, CommRing (A i)]
  [algebraRA : ∀ i, Algebra R (A i)]
  [localA : ∀ i, IsLocalRing (A i)]
  B : Type u
  [commRingB : CommRing B]
  [algebraRB : Algebra R B]
  finiteA : ∀ i, RingHom.Finite (algebraMap R (A i))
  decomposition : Nonempty (S ≃ₐ[R] (∀ i, A i) × B)
  surjective : ∀ i, Function.Surjective (algebraMap R (A i))
  noPrimeOver : ∀ q : PrimeSpectrum B,
    q.asIdeal.comap (algebraMap R B) ≠ IsLocalRing.maximalIdeal R

theorem unramified_over_strictly_henselian
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [StrictlyHenselianLocalRing R] (hS : Algebra.Unramified R S) :
    Nonempty (StrictUnramifiedDecompositionData R S) := by
  sorry

/-! ## Complete and zero-dimensional local rings -/

theorem complete_local_henselian
    (R : Type u) [CommRing R] [IsLocalRing R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R] :
    HenselianLocalRing R := by
  sorry

theorem zero_dimensional_local_henselian
    (R : Type u) [CommRing R] [IsLocalRing R]
    (hzero : ringKrullDim R = 0) : HenselianLocalRing R := by
  sorry

/-! ## Maps into henselian rings and solutions over strictly henselian rings -/

/-- A residue-field map compatible with an algebra map from `R`. -/
structure ResidueFieldMapData
    {R A S : Type u} [CommRing R] [CommRing A] [CommRing S]
    [Algebra R A] [Algebra R S] [IsLocalRing S]
    (q : PrimeSpectrum A)
    (hq : q.asIdeal.comap (algebraMap R A) =
      (IsLocalRing.maximalIdeal S).comap (algebraMap R S)) where
  map : q.asIdeal.ResidueField →+* IsLocalRing.ResidueField S
  overBase : ∀ r : R,
    map (algebraMap (A ⧸ q.asIdeal) q.asIdeal.ResidueField
      (Ideal.Quotient.mk q.asIdeal (algebraMap R A r))) =
      IsLocalRing.residue S (algebraMap R S r)

theorem map_into_henselian
    {R A S : Type u} [CommRing R] [CommRing A] [CommRing S]
    [Algebra R A] [Algebra R S] [HenselianLocalRing S]
    (hA : Algebra.Etale R A)
    (q : PrimeSpectrum A)
    (hq : q.asIdeal.comap (algebraMap R A) =
      (IsLocalRing.maximalIdeal S).comap (algebraMap R S))
    (τ : ResidueFieldMapData (R := R) (S := S) q hq) :
    ∃! f : A →ₐ[R] S,
      PrimeSpectrum.comap f.toRingHom (maximalPrime S) = q ∧
        ∀ a : A,
          τ.map (algebraMap (A ⧸ q.asIdeal) q.asIdeal.ResidueField
            (Ideal.Quotient.mk q.asIdeal a)) =
            IsLocalRing.residue S (f a) := by
  sorry

def PolynomialSystemSolutions
    (R : Type u) [CommRing R] (n : ℕ)
    (P : Fin n → MvPolynomial (Fin n) R) : Type u :=
  {x : Fin n → R // ∀ i, MvPolynomial.aeval x (P i) = 0}

/-- The map on polynomial solutions induced by a ring homomorphism. -/
def polynomialSystemMap
    {R S : Type u} [CommRing R] [CommRing S]
    (φ : R →+* S) (n : ℕ)
    (P : Fin n → MvPolynomial (Fin n) R) :
    PolynomialSystemSolutions R n P →
      PolynomialSystemSolutions S n (fun i => MvPolynomial.map φ (P i)) :=
  fun x => ⟨fun j => φ (x.1 j), by
    intro i
    change MvPolynomial.eval (fun j => φ (x.1 j))
      (MvPolynomial.map φ (P i)) = 0
    have hx : MvPolynomial.eval x.1 (P i) = 0 := by
      simpa only [MvPolynomial.aeval_eq_eval] using x.2 i
    calc
      MvPolynomial.eval (fun j => φ (x.1 j)) (MvPolynomial.map φ (P i)) =
          φ (MvPolynomial.eval x.1 (P i)) := by
            simpa only [Function.comp_def] using
              (MvPolynomial.map_eval φ x.1 (P i)).symm
      _ = 0 := by rw [hx, map_zero]⟩

theorem strictly_henselian_solution_bijection
    {R S : Type u} [CommRing R] [CommRing S]
    [StrictlyHenselianLocalRing R] [StrictlyHenselianLocalRing S]
    (φ : R →+* S) (hφ : IsLocalHom φ) (n : ℕ)
    (P : Fin n → MvPolynomial (Fin n) R)
    (hP : Algebra.Etale R
      (MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range P))) :
    Function.Bijective (polynomialSystemMap φ n P) := by
  sorry

/-! ## Countably generated Mittag--Leffler modules -/

/-- Countable generation by a spanning set. -/
def CountablyGeneratedModule
    (R : Type u) (M : Type v) [CommRing R] [AddCommGroup M] [Module R M] : Prop :=
  ∃ s : Set M, s.Countable ∧ Submodule.span R s = ⊤

/-- Tensor-kernel domination of linear maps. -/
def TensorKernelDominates
    {R : Type u} [CommRing R] {M N N' : Type w}
    [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N]
    [AddCommGroup N'] [Module R N']
    (g : M →ₗ[R] N') (f : M →ₗ[R] N) : Prop :=
  ∀ (Q : Type (max u w)) [AddCommGroup Q] [Module R Q],
    LinearMap.ker (f.rTensor Q) ≤ LinearMap.ker (g.rTensor Q)

/-- Mutual tensor-kernel domination. -/
def MutuallyTensorKernelDominates
    {R : Type u} [CommRing R] {M N N' : Type w}
    [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N]
    [AddCommGroup N'] [Module R N']
    (g : M →ₗ[R] N') (f : M →ₗ[R] N) : Prop :=
  TensorKernelDominates g f ∧ TensorKernelDominates f g

/-- The finitely-presented factorization formulation of a Mittag--Leffler module.
This is the module-level interface used by the source's preceding chapter. -/
def MittagLefflerModule
    (R : Type u) [CommRing R] (M : ModuleCat.{w} R) : Prop :=
  ∀ (P : ModuleCat.{w} R), Module.FinitePresentation R P →
    ∀ (f : (P : Type w) →ₗ[R] (M : Type w)),
      ∃ Q : ModuleCat.{w} R, Module.FinitePresentation R Q ∧
        ∃ g : (P : Type w) →ₗ[R] (Q : Type w),
          MutuallyTensorKernelDominates g f

theorem henselian_countable_mittag_leffler
    {R M : Type u} [CommRing R] [HenselianLocalRing R]
    [AddCommGroup M] [Module R M]
    (hcountable : CountablyGeneratedModule R M)
    (hML : MittagLefflerModule R (ModuleCat.of R M)) :
    ∃ (I : Type u) (N : I → ModuleCat R),
      (∀ i, Module.FinitePresentation R (N i)) ∧
        Nonempty ((M : Type u) ≃ₗ[R]
          DirectSum I (fun i : I => (N i : Type u))) := by
  sorry

end
end Formalization.Books.Algebra.Unit153
