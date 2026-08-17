import Formalization.Books.Algebra.Unit50.ValuationRings
import Formalization.Books.Algebra.Unit54.EssentiallyFiniteType
import Formalization.Books.Algebra.Unit99.CriteriaForFlatness
import Formalization.Books.Algebra.Unit112.HomomorphismsAndDimension
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.Field.Subfield.Basic
import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.RingTheory.AdicCompletion.Algebra
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.MvPowerSeries.Rename
import Mathlib.RingTheory.PowerSeries.Basic

/-!
# Commutative Algebra, Chapter 119: Around Krull-Akizuki

The source section is formalized with Mathlib's canonical local-ring,
Noetherian, dimension, valuation-ring, length, residue-field, localization,
finite-type, and completion interfaces.  The theorem proofs are deferred to
the proving stage; the concrete algebraic constructions below have their
source-faithful bodies.
-/

namespace Formalization.Books.Algebra.Unit119

open Set

universe u v

noncomputable section

/-! ## Domination and the local alternatives -/

/- The kernel and cokernel condition in the Kollár alternative is the common
   source-facing form of ``annihilated by a power of the maximal ideal''.  The
   cokernel is the quotient by the canonical `R`-linear map underlying `f`. -/
def IsFiniteLocalModification
    {R S : Type u} [CommRing R] [CommRing S] [IsLocalRing R]
    (f : R →+* S) : Prop :=
  RingHom.Finite f ∧ ¬ Function.Bijective f ∧
    ∃ n m : ℕ,
      Formalization.Books.Algebra.Unit99.IsAnnihilatedByIdealPower
        (N := RingHom.ker f)
        (IsLocalRing.maximalIdeal R) n ∧
        (letI : Algebra R S := f.toAlgebra
         Formalization.Books.Algebra.Unit99.IsAnnihilatedByIdealPower
           (N := S ⧸ LinearMap.range (Algebra.linearMap R S))
           (IsLocalRing.maximalIdeal R) m)

/- The four alternatives are packaged as a finite family so that `∃!` records
   the source's phrase “exactly one”, rather than merely listing equivalent
   conditions. -/
def kollarAlternative
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (i : Fin 4) : Prop :=
  match i.1 with
  | 0 => IsArtinianRing R
  | 1 => IsRegularLocalRing R ∧ ringKrullDim R = 1
  | 2 => 2 ≤ Formalization.Books.Algebra.Unit72.localDepth R R
  | _ =>
      ∃ (S : CommRingCat.{u}) (f : CommRingCat.of R ⟶ S),
        IsFiniteLocalModification f.hom ∧
          (letI : Algebra R (S : Type u) := f.hom.toAlgebra
           ¬ IsLocalRing.maximalIdeal R ∈
              _root_.associatedPrimes R (S : Type u)) ∧
          Nontrivial (S : Type u)

theorem dominate_by_dimension_one
    {R K : Type u} [CommRing R] [IsDomain R]
    [IsLocalRing R] [IsNoetherianRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (hfield : ¬ IsField R) :
    ∃ S : Subalgebra R K,
      IsLocalRing S ∧
        IsNoetherianRing S ∧
          ringKrullDim S = 1 ∧
            IsLocalHom (algebraMap R S) ∧
              RingHom.EssFiniteType (algebraMap R S) := by
  sorry

theorem kollar_local_ring_alternative
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R] :
    ∃! i : Fin 4, kollarAlternative R i := by
  sorry

theorem exists_finite_local_modification_of_nonregular_dimension_one
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (hdim : ringKrullDim R = 1)
    (hcotangent : 1 < Module.finrank (IsLocalRing.ResidueField R)
      (IsLocalRing.CotangentSpace R)) :
    ∃ (S : CommRingCat.{u}) (f : CommRingCat.of R ⟶ S),
      IsFiniteLocalModification f.hom ∧
        (letI : Algebra R (S : Type u) := f.hom.toAlgebra
         ¬ IsLocalRing.maximalIdeal R ∈
            _root_.associatedPrimes R (S : Type u)) ∧
        Nontrivial (S : Type u) := by
  sorry

/-! ## The two examples and the resolution remark -/

abbrev nonreducedExamplePowerSeries (k : Type u) [Field k] :=
  MvPowerSeries (Fin 2) k

def nonreducedExampleRelation (k : Type u) [Field k] :
    Ideal (nonreducedExamplePowerSeries k) :=
  Ideal.span
    ({(MvPowerSeries.X (1 : Fin 2) : nonreducedExamplePowerSeries k) ^ 2} :
      Set (nonreducedExamplePowerSeries k))

abbrev nonreducedExampleRing (k : Type u) [Field k] :=
  nonreducedExamplePowerSeries k ⧸ nonreducedExampleRelation k

def nonreducedExampleX (k : Type u) [Field k] : nonreducedExampleRing k :=
  Ideal.Quotient.mk (nonreducedExampleRelation k)
    (MvPowerSeries.X (0 : Fin 2))

def nonreducedExampleY (k : Type u) [Field k] : nonreducedExampleRing k :=
  Ideal.Quotient.mk (nonreducedExampleRelation k)
    (MvPowerSeries.X (1 : Fin 2))

abbrev nonreducedExampleTargetRing (k : Type u) [Field k] :=
  nonreducedExampleRing k

def nonreducedExampleTargetX (k : Type u) [Field k] :
    nonreducedExampleTargetRing k :=
  nonreducedExampleX k

def nonreducedExampleTargetZ (k : Type u) [Field k] :
    nonreducedExampleTargetRing k :=
  nonreducedExampleY k

/- The element adjoined after `n` repetitions is the source's `y/x^n`,
   expressed in the localization in which `x` is invertible. -/
noncomputable def nonreducedExampleAdjoinedElement
    (k : Type u) [Field k] (n : ℕ) :
    Localization.Away (nonreducedExampleX k) :=
  Localization.mk (nonreducedExampleY k)
    ⟨(nonreducedExampleX k) ^ n,
      (Submonoid.mem_powers_iff _ _).2 ⟨n, rfl⟩⟩

noncomputable def nonreducedExampleIteratedAdjoin
    (k : Type u) [Field k] (n : ℕ) :
    Subalgebra (nonreducedExampleRing k)
      (Localization.Away (nonreducedExampleX k)) :=
  Algebra.adjoin (nonreducedExampleRing k)
    ({nonreducedExampleAdjoinedElement k n} :
      Set (Localization.Away (nonreducedExampleX k)))

theorem nonreduced_example_properties (k : Type u) [Field k] :
    ∃ hN : IsNoetherianRing (nonreducedExampleRing k),
      ∃ hL : IsLocalRing (nonreducedExampleRing k),
        letI : IsNoetherianRing (nonreducedExampleRing k) := hN
        letI : IsLocalRing (nonreducedExampleRing k) := hL
        Formalization.Books.Algebra.Unit103.IsCohenMacaulay
            (nonreducedExampleRing k) (nonreducedExampleRing k) ∧
            ringKrullDim (nonreducedExampleRing k) = 1 ∧
            ∃ f : nonreducedExampleRing k →+*
                nonreducedExampleTargetRing k,
              IsFiniteLocalModification f ∧
                Function.Injective f ∧
                  (letI : Algebra (nonreducedExampleRing k)
                      (nonreducedExampleTargetRing k) := f.toAlgebra
                   ¬ IsLocalRing.maximalIdeal (nonreducedExampleRing k) ∈
                      _root_.associatedPrimes (nonreducedExampleRing k)
                        (nonreducedExampleTargetRing k)) ∧
                    f (nonreducedExampleX k) =
                        nonreducedExampleTargetX k ∧
                      f (nonreducedExampleY k) =
                        nonreducedExampleTargetX k *
                          nonreducedExampleTargetZ k := by
  sorry

def pPowerSubfield (k : Type u) (p : ℕ) [Field k] [Fact p.Prime]
    [CharP k p] : Subfield k :=
  (frobenius k p).fieldRange

def finiteDegreeOverPowers (k : Type u) (p : ℕ) [Field k] [Fact p.Prime]
    [CharP k p] (s : Set k) : Prop :=
  ∃ F : IntermediateField (pPowerSubfield k p) k,
    s ⊆ (F : Set k) ∧ Module.Finite (pPowerSubfield k p) F

def badDvrCoefficientCondition (k : Type u) (p : ℕ) [Field k]
    [Fact p.Prime] [CharP k p] (f : PowerSeries k) : Prop :=
  finiteDegreeOverPowers k p
    (Set.range (fun i : ℕ => PowerSeries.coeff i f))

/- The structure records the concrete set defining `A`, its DVR property, its
   completion, and the infinite purely inseparable fraction-field extension.
   The map field makes “induced extension” explicit. -/
structure BadDvrExampleData (k : Type u) (p : ℕ) [Field k] [Fact p.Prime]
    [CharP k p] where
  A : Subring (PowerSeries k)
  carrier_spec : ∀ f : PowerSeries k,
    f ∈ A ↔ badDvrCoefficientCondition k p f
  isDomain : IsDomain (A : Type u)
  isDVR : @IsDiscreteValuationRing (A : Type u) _ isDomain
  maximalIdeal : Ideal (A : Type u)
  maximalIdeal_isMaximal : maximalIdeal.IsMaximal
  completion_equiv : Nonempty
    (AdicCompletion maximalIdeal (A : Type u) ≃+* PowerSeries k)
  fractionFieldMap :
    (letI : IsDomain (A : Type u) := isDomain
     FractionRing (A : Type u) →+* FractionRing (PowerSeries k))
  fractionFieldMap_commutes :
    (letI : IsDomain (A : Type u) := isDomain
     fractionFieldMap.comp (algebraMap (A : Type u) (FractionRing (A : Type u))) =
       (algebraMap (PowerSeries k) (FractionRing (PowerSeries k))).comp A.subtype)
  fractionField_infinite :
    (letI : IsDomain (A : Type u) := isDomain
     letI : Algebra (FractionRing (A : Type u)) (FractionRing (PowerSeries k)) :=
       fractionFieldMap.toAlgebra
     ¬ Module.Finite (FractionRing (A : Type u)) (FractionRing (PowerSeries k)))
  fractionField_purelyInseparable :
    (letI : IsDomain (A : Type u) := isDomain
     letI : Algebra (FractionRing (A : Type u)) (FractionRing (PowerSeries k)) :=
       fractionFieldMap.toAlgebra
     IsPurelyInseparable (FractionRing (A : Type u))
       (FractionRing (PowerSeries k)))

theorem bad_dvr_characteristic_p_example
    {k : Type u} {p : ℕ} [Field k] [Fact p.Prime] [CharP k p]
    (hinfinite : ¬ Module.Finite (pPowerSubfield k p) k) :
    Nonempty (BadDvrExampleData k p) := by
  sorry

noncomputable def badDvrAdjoin
    {k : Type u} {p : ℕ} [Field k] [Fact p.Prime] [CharP k p]
    (D : BadDvrExampleData k p) (f : PowerSeries k) :
    Subalgebra (D.A : Type u) (PowerSeries k) :=
  letI : Algebra (D.A : Type u) (PowerSeries k) := D.A.subtype.toAlgebra
  Algebra.adjoin (D.A : Type u) ({f} : Set (PowerSeries k))

theorem bad_dvr_adjoin_properties
    {k : Type u} {p : ℕ} [Field k] [Fact p.Prime] [CharP k p]
    (D : BadDvrExampleData k p) (f : PowerSeries k)
    (hf : f ∉ D.A) :
    ∃ hN : IsNoetherianRing (badDvrAdjoin D f),
      ∃ hL : IsLocalRing (badDvrAdjoin D f),
        ∃ hD : IsDomain (badDvrAdjoin D f),
          letI : IsNoetherianRing (badDvrAdjoin D f) := hN
          letI : IsLocalRing (badDvrAdjoin D f) := hL
          letI : IsDomain (badDvrAdjoin D f) := hD
          ringKrullDim (badDvrAdjoin D f) = 1 ∧
            ¬ IsReduced
              (AdicCompletion (IsLocalRing.maximalIdeal (badDvrAdjoin D f))
                (badDvrAdjoin D f)) := by
  sorry

def IsOneDimensionalSemilocalNoetherianDomain
    (R : Type u) [CommRing R] : Prop :=
  IsDomain R ∧ IsNoetherianRing R ∧ ringKrullDim R = 1 ∧
    Finite (MaximalSpectrum R)

def IsRegularSemilocalRing (R : Type u) [CommRing R] : Prop :=
  ∀ m : MaximalSpectrum R,
    IsRegularLocalRing (Localization.AtPrime m.asIdeal)

def HasFiniteBirationalExtension
    (R : Type u) [CommRing R] [IsDomain R] : Prop :=
  ∃ S : CommRingCat.{u}, ∃ f : CommRingCat.of R ⟶ S,
    IsOneDimensionalSemilocalNoetherianDomain (S : Type u) ∧
      ∃ hS : IsDomain (S : Type u),
        letI : IsDomain (S : Type u) := hS
        RingHom.Finite f.hom ∧ Function.Injective f.hom ∧
          ∃ e : FractionRing R ≃+* FractionRing (S : Type u),
            e.toRingHom.comp (algebraMap R (FractionRing R)) =
              (algebraMap (S : Type u) (FractionRing (S : Type u))).comp f.hom

def HasRegularFiniteBirationalModel
    (R : Type u) [CommRing R] [IsDomain R] : Prop :=
  ∃ S : CommRingCat.{u}, ∃ f : CommRingCat.of R ⟶ S,
    IsOneDimensionalSemilocalNoetherianDomain (S : Type u) ∧
      IsRegularSemilocalRing (S : Type u) ∧
      ∃ hS : IsDomain (S : Type u),
        letI : IsDomain (S : Type u) := hS
        RingHom.Finite f.hom ∧ Function.Injective f.hom ∧
          ∃ e : FractionRing R ≃+* FractionRing (S : Type u),
            e.toRingHom.comp (algebraMap R (FractionRing R)) =
              (algebraMap (S : Type u) (FractionRing (S : Type u))).comp f.hom

def AllLocalCompletionsReduced
    (R : Type u) [CommRing R] [IsNoetherianRing R] : Prop :=
  ∀ m : MaximalSpectrum R,
    IsReduced
      (AdicCompletion
        (IsLocalRing.maximalIdeal (Localization.AtPrime m.asIdeal))
        (Localization.AtPrime m.asIdeal))

theorem resolution_step_of_nonregular_maximal
    {R : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    (hdim : ringKrullDim R = 1)
    (hsemilocal : Finite (MaximalSpectrum R))
    (m : MaximalSpectrum R)
    (hnonregular : ¬ IsRegularLocalRing (Localization.AtPrime m.asIdeal)) :
    HasFiniteBirationalExtension R := by
  sorry

theorem reduced_local_completions_give_regular_model
    {R : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    (hdim : ringKrullDim R = 1) (hsemilocal : Finite (MaximalSpectrum R))
    (hcompletion : AllLocalCompletionsReduced R) :
    HasRegularFiniteBirationalModel R := by
  sorry

theorem exists_characteristic_zero_nonreduced_completion
    : ∃ R : CommRingCat.{u},
      CharZero (R : Type u) ∧
        IsNoetherianRing (R : Type u) ∧ IsLocalRing (R : Type u) ∧
          IsDomain (R : Type u) ∧ ringKrullDim (R : Type u) = 1 ∧
            ∃ m : Ideal (R : Type u),
              m.IsMaximal ∧ ¬ IsReduced (AdicCompletion m (R : Type u)) := by
  sorry

/-! ## Discrete valuation rings and uniformizers -/

def HasPrincipalNonzeroMaximalIdeal
    (A : Type u) [CommRing A] : Prop :=
  ∃ m : Ideal A, m.IsMaximal ∧
    ∃ π : A, π ≠ 0 ∧ m = Ideal.span ({π} : Set A)

theorem characterize_discrete_valuation_ring
    {A : Type u} [CommRing A] :
    List.TFAE
      [ (∃ hA : IsDomain A, @IsDiscreteValuationRing A _ hA),
        (∃ hA : IsDomain A,
          @ValuationRing A _ hA ∧ IsNoetherianRing A ∧ ¬ IsField A),
        IsRegularLocalRing A ∧ ringKrullDim A = 1,
        IsNoetherianRing A ∧ IsLocalRing A ∧ IsDomain A ∧
          HasPrincipalNonzeroMaximalIdeal A,
        IsNoetherianRing A ∧ IsLocalRing A ∧
          Formalization.Books.Algebra.Unit37.IsNormalDomain A ∧
            ringKrullDim A = 1 ] := by
  sorry

def IsUniformizer
    {A : Type u} [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] (π : A) : Prop :=
  Ideal.span ({π} : Set A) = IsLocalRing.maximalIdeal A

theorem uniformizers_associated
    {A : Type u} [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] {π ρ : A}
    (hπ : IsUniformizer π) (hρ : IsUniformizer ρ) :
    Associated π ρ := by
  sorry

theorem dvr_unique_unit_mul_pow
    {A : Type u} [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] {π : A}
    (hπ : IsUniformizer π) :
    ∀ x : A, x ≠ 0 →
      ∃! q : A × ℕ, IsUnit q.1 ∧ x = q.1 * π ^ q.2 := by
  sorry

/-! ## Length bounds and residue fields -/

theorem finite_length_submodule_bound
    {R K : Type u} [CommRing R] [IsDomain R]
    [IsLocalRing R] [IsNoetherianRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (hdim : ringKrullDim R = 1) (r : ℕ)
    (M : Submodule R (Fin r → K)) (x : R) (hx : x ≠ 0) :
    Module.length R (R ⧸ Ideal.span ({x} : Set R)) < ⊤ ∧
      Module.length R
          (Formalization.Books.Algebra.Unit63.quotientByElement R
            (M : Type u) x) ≤
        (r : ℕ∞) * Module.length R (R ⧸ Ideal.span ({x} : Set R)) := by
  sorry

theorem finite_residue_field_fibres
    {R S K L : Type u} [CommRing R] [CommRing S]
    [IsDomain R] [IsDomain S] [IsLocalRing R] [IsNoetherianRing R]
    [Field K] [Field L] [Algebra R K] [IsFractionRing R K]
    [Algebra S L] [IsFractionRing S L] [Algebra K L] [Module.Finite K L]
    (f : R →+* S)
    (hcompat : (algebraMap K L).comp (algebraMap R K) =
      (algebraMap S L).comp f)
    (hinjective : Function.Injective (algebraMap K L))
    (hdim : ringKrullDim R = 1) :
    (∀ n : Ideal S, n.IsPrime →
      n.comap f = IsLocalRing.maximalIdeal R → n.IsMaximal) ∧
      Set.Finite
        {n : Ideal S | n.IsPrime ∧
          n.comap f = IsLocalRing.maximalIdeal R} ∧
        (∀ n : Ideal S, (hn : n.IsPrime) →
          n.comap f = IsLocalRing.maximalIdeal R →
            letI : n.IsPrime := hn
            ∃ φ : IsLocalRing.ResidueField R →+* n.ResidueField,
              (∀ r : R,
                φ (algebraMap R (IsLocalRing.ResidueField R) r) =
                  algebraMap S n.ResidueField (f r)) ∧
                (letI : Algebra (IsLocalRing.ResidueField R)
                    n.ResidueField := φ.toAlgebra
                 Module.Finite (IsLocalRing.ResidueField R)
                   n.ResidueField)) := by
  sorry

theorem finite_length_global_submodule
    {R K : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (hdim : ringKrullDim R = 1) (r : ℕ)
    (M : Submodule R (Fin r → K)) (x : R) (hx : x ≠ 0) :
    Module.length R
        (Formalization.Books.Algebra.Unit63.quotientByElement R
          (M : Type u) x) < ⊤ := by
  sorry

/-! ## Krull-Akizuki and dominating DVRs -/

theorem krull_akizuki
    {R K L : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [Field L] [Algebra K L] [Algebra R L] [IsScalarTower R K L]
    [Module.Finite K L]
    (hdim : ringKrullDim R = 1) (A : Subalgebra R L) :
    IsNoetherianRing A := by
  sorry

theorem exists_dvr_dominating
    {R K L : Type u} [CommRing R] [IsDomain R]
    [IsLocalRing R] [IsNoetherianRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [Field L] [Algebra K L] [Algebra R L] [IsScalarTower R K L]
    [Algebra.FiniteType K L]
    (hfield : ¬ IsField R) :
    ∃ A : Subalgebra R L,
      (∃ hA : IsDomain (A : Type u),
        @IsDiscreteValuationRing (A : Type u) _ hA) ∧
        IsFractionRing (A : Type u) L ∧
          IsLocalHom (algebraMap R A) := by
  sorry

end

end Formalization.Books.Algebra.Unit119
