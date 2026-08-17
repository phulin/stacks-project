import Formalization.Books.Algebra.Unit137.SmoothRingMaps
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.FieldTheory.Separable
import Mathlib.RingTheory.Ideal.Cotangent
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.RegularLocalRing.Defs

/-!
# Commutative Algebra, Chapter 140: Smooth algebras over fields

This chapter records the differential and regularity criteria for smooth
finite-type algebras over fields.  Differential fibres use the canonical
Kaehler differential module from Chapter 131, pointwise smoothness uses the
Chapter 137 basic-open predicate, and dimensions use the `WithBot ℕ∞`
normalization already used by Chapters 114 and 116.
-/

namespace Formalization.Books.Algebra.Unit140

open Set
open scoped TensorProduct

noncomputable section

universe u v

/-! ## Differential fibres and algebraically closed fields -/

/- The source warns that the first two lemmas below need not hold over
   nonperfect fields; their algebraically closed hypotheses are retained. -/

/- The source writes `Ω_{S/k} ⊗_S κ(q)`.  We use the canonically equivalent
   localized presentation, with the residue field as the left factor, so that
   the localized Kaehler module and its `κ(q)`-module structure are both
   supplied by Mathlib. -/
abbrev DifferentialFiber
    (k S : Type*) [CommRing k] [CommRing S] [Algebra k S]
    (q : PrimeSpectrum S) : Type _ :=
  IsLocalRing.ResidueField (Localization.AtPrime q.asIdeal) ⊗[
      Localization.AtPrime q.asIdeal]
    Formalization.Books.Algebra.Unit131.ModuleOfDifferentials k
      (Localization.AtPrime q.asIdeal)

/- The raw tensor-product API needs this scalar-action bridge because the
   residue field is presented through the local ring at `q`. -/
noncomputable instance differentialFiberModule
    (k S : Type*) [CommRing k] [CommRing S] [Algebra k S]
    (q : PrimeSpectrum S) :
    Module q.asIdeal.ResidueField (DifferentialFiber k S q) := by
  letI : SMulCommClass (Localization.AtPrime q.asIdeal)
      (IsLocalRing.ResidueField (Localization.AtPrime q.asIdeal))
      (IsLocalRing.ResidueField (Localization.AtPrime q.asIdeal)) :=
    Algebra.to_smulCommClass
  exact TensorProduct.leftModule

theorem rank_omega
    {k S : Type u} [Field k] [CommRing S] [Algebra k S]
    [Algebra.FiniteType k S] [IsAlgClosed k]
    (m : MaximalSpectrum S) :
    Module.finrank (MaximalSpectrum.toPrimeSpectrum m).asIdeal.ResidueField
        (DifferentialFiber k S (MaximalSpectrum.toPrimeSpectrum m)) =
      Module.finrank (MaximalSpectrum.toPrimeSpectrum m).asIdeal.ResidueField
        (IsLocalRing.CotangentSpace
          (Localization.AtPrime (MaximalSpectrum.toPrimeSpectrum m).asIdeal)) := by
  sorry

/-! ## Smoothness over an algebraically closed field -/

theorem characterize_smooth_kbar
    {k S : Type u} [Field k] [CommRing S] [Algebra k S]
    [Algebra.FiniteType k S] [IsAlgClosed k]
    (m : MaximalSpectrum S) :
    List.TFAE
      [ IsRegularLocalRing (Localization.AtPrime m.asIdeal),
        ((Module.finrank (MaximalSpectrum.toPrimeSpectrum m).asIdeal.ResidueField
            (DifferentialFiber k S (MaximalSpectrum.toPrimeSpectrum m)) : ℕ∞) :
          WithBot ℕ∞) ≤ ringKrullDim (Localization.AtPrime m.asIdeal),
        ((Module.finrank (MaximalSpectrum.toPrimeSpectrum m).asIdeal.ResidueField
            (DifferentialFiber k S (MaximalSpectrum.toPrimeSpectrum m)) : ℕ∞) :
          WithBot ℕ∞) = ringKrullDim (Localization.AtPrime m.asIdeal),
        Formalization.Books.Algebra.Unit137.IsSmoothAt k S
          (MaximalSpectrum.toPrimeSpectrum m) ] := by
  sorry

/-! ## Smoothness over an arbitrary field -/

theorem characterize_smooth_over_field
    {k S : Type u} [Field k] [CommRing S] [Algebra k S]
    [Algebra.FiniteType k S] (q : PrimeSpectrum S) :
    List.TFAE
      [ Formalization.Books.Algebra.Unit137.IsSmoothAt k S q,
        ((Module.finrank q.asIdeal.ResidueField
            (DifferentialFiber k S q) : ℕ∞) : WithBot ℕ∞) ≤
          Formalization.Books.Topology.Unit10.krullDimensionAt q,
        ((Module.finrank q.asIdeal.ResidueField
            (DifferentialFiber k S q) : ℕ∞) : WithBot ℕ∞) =
          Formalization.Books.Topology.Unit10.krullDimensionAt q ] ∧
      (Formalization.Books.Algebra.Unit137.IsSmoothAt k S q →
        IsRegularLocalRing (Localization.AtPrime q.asIdeal)) := by
  sorry

/-! ## The differential from the cotangent space -/

/- The target is the differential fibre at the closed point of a local ring.
   This is the canonical map induced by the universal derivation and the
   residue-field scalar extension. -/
noncomputable def differentialCotangentMap
    {k R : Type*} [CommRing k] [CommRing R] [Algebra k R]
    [IsLocalRing R] :
    IsLocalRing.CotangentSpace R →ₗ[k]
      IsLocalRing.ResidueField R ⊗[R]
        Formalization.Books.Algebra.Unit131.ModuleOfDifferentials k R :=
  letI : Algebra R (IsLocalRing.ResidueField R) :=
    IsLocalRing.ResidueField.algebra (R₀ := R) R
  let f : IsLocalRing.maximalIdeal R →ₗ[k]
      IsLocalRing.ResidueField R ⊗[R]
        Formalization.Books.Algebra.Unit131.ModuleOfDifferentials k R :=
    ((TensorProduct.mk R (IsLocalRing.ResidueField R)
        (Formalization.Books.Algebra.Unit131.ModuleOfDifferentials k R) 1).restrictScalars k).comp
      ((Formalization.Books.Algebra.Unit131.universalDifferential k R).toLinearMap.comp
        ((IsLocalRing.maximalIdeal R).subtype.restrictScalars k))
  Ideal.Cotangent.lift f (by
    intro x y
    change (1 : IsLocalRing.ResidueField R) ⊗ₜ[R]
      Formalization.Books.Algebra.Unit131.universalDifferential k R
        ((x : R) * (y : R)) = 0
    rw [Derivation.leibniz]
    rw [TensorProduct.tmul_add]
    rw [TensorProduct.tmul_smul, TensorProduct.tmul_smul]
    rw [TensorProduct.smul_tmul', TensorProduct.smul_tmul']
    rw [Algebra.smul_def, Algebra.smul_def]
    have hx0 : algebraMap R (IsLocalRing.ResidueField R) (x : R) = 0 := by
      rw [IsLocalRing.ResidueField.algebraMap_eq, IsLocalRing.residue_def]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr x.2
    have hy0 : algebraMap R (IsLocalRing.ResidueField R) (y : R) = 0 := by
      rw [IsLocalRing.ResidueField.algebraMap_eq, IsLocalRing.residue_def]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr y.2
    rw [hx0, hy0]
    simp)

theorem computation_differential
    {k R : Type*} [Field k] [CommRing R] [Algebra k R]
    [IsLocalRing R] [IsNoetherianRing R]
    [Algebra.FiniteType k (IsLocalRing.ResidueField R)]
    [Algebra.IsSeparable k (IsLocalRing.ResidueField R)] :
    Function.Injective (differentialCotangentMap (k := k) (R := R)) := by
  sorry

/-! ## Separable residue fields -/

theorem separable_smooth
    {k S : Type u} [Field k] [CommRing S] [Algebra k S]
    [Algebra.FiniteType k S] (q : PrimeSpectrum S)
    [Algebra.IsSeparable k q.asIdeal.ResidueField] :
    Formalization.Books.Algebra.Unit137.IsSmoothAt k S q ↔
      IsRegularLocalRing (Localization.AtPrime q.asIdeal) := by
  sorry

/-! ## The characteristic-zero direct-summand criterion -/

/- A `Q`-algebra map is made explicit by the two ground-field algebra
   structures and their scalar-tower compatibility.  The `CharZero`
   assumptions exclude the degenerate zero-ring interpretation and are the
   hypotheses used by the source's integer coefficients. -/
theorem characteristic_zero_not_nilpotent
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra ℚ R] [Algebra ℚ S] [IsScalarTower ℚ R S]
    [CharZero R] [CharZero S]
    (f : S) (C : Submodule S
      (Formalization.Books.Algebra.Unit131.ModuleOfDifferentials R S))
    (hsplit : IsCompl
      (Submodule.span S
        {Formalization.Books.Algebra.Unit131.universalDifferential R S f}) C) :
    ¬ IsNilpotent f := by
  sorry

theorem characteristic_zero_is_regular
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra ℚ R] [Algebra ℚ S] [IsScalarTower ℚ R S]
    [CharZero R] [CharZero S] [IsNoetherianRing S] [IsLocalRing S]
    (f : S) (C : Submodule S
      (Formalization.Books.Algebra.Unit131.ModuleOfDifferentials R S))
    (hsplit : IsCompl
      (Submodule.span S
        {Formalization.Books.Algebra.Unit131.universalDifferential R S f}) C) :
    IsRegular f := by
  sorry

/-! ## The characteristic-zero local criterion -/

theorem characteristic_zero_local_smooth
    {k S : Type u} [Field k] [CharZero k] [CommRing S] [Algebra k S]
    [Algebra.FiniteType k S] (q : PrimeSpectrum S) :
    List.TFAE
      [ Formalization.Books.Algebra.Unit137.IsSmoothAt k S q,
        Formalization.Books.Algebra.Unit137.DifferentialsFiniteFreeAt k S q,
        IsRegularLocalRing (Localization.AtPrime q.asIdeal) ] := by
  sorry

/-! ## Characteristic-p counterexamples -/

abbrev nilpotentPolynomialQuotient (p : ℕ) : Type :=
  Polynomial (ZMod p) ⧸
    Ideal.span ({Polynomial.X ^ p} : Set (Polynomial (ZMod p)))

theorem characteristic_p_nilpotent_example
    (p : ℕ) [Fact p.Prime] :
    ¬ Algebra.Smooth (ZMod p) (nilpotentPolynomialQuotient p) ∧
      Module.Free (nilpotentPolynomialQuotient p)
        (Formalization.Books.Algebra.Unit131.ModuleOfDifferentials
          (ZMod p) (nilpotentPolynomialQuotient p)) := by
  sorry

def characteristicPHypersurfaceRelation
    (K : Type u) [CommRing K] (p : ℕ) (α : K) :
    Ideal (MvPolynomial (Fin 2) K) :=
  Ideal.span
    ({MvPolynomial.X 0 ^ p + MvPolynomial.X 1 ^ 2 + MvPolynomial.C α} :
      Set (MvPolynomial (Fin 2) K))

abbrev characteristicPHypersurface
    (K : Type u) [CommRing K] (p : ℕ) (α : K) : Type u :=
  MvPolynomial (Fin 2) K ⧸ characteristicPHypersurfaceRelation K p α

def characteristicPHypersurfacePrime
    (K : Type u) [CommRing K] (p : ℕ) (α : K) :
    Ideal (characteristicPHypersurface K p α) :=
  Ideal.span
    ({ Ideal.Quotient.mk _ (MvPolynomial.X 1),
        Ideal.Quotient.mk _
          (MvPolynomial.X 0 ^ p + MvPolynomial.C α) } :
      Set (characteristicPHypersurface K p α))

/- The printed example leaves `α` implicit.  The natural repair is the
   displayed non-pth-power condition, which makes the indicated ideal prime;
   the theorem below records the corrected source-facing example. -/
theorem characteristic_p_hypersurface_example
    {K : Type u} [Field K] (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 2 < p) (α : K)
    (hα : α ∉ Set.range (fun z : K => z ^ p))
    (q : PrimeSpectrum (characteristicPHypersurface K p α))
    (hq : q.asIdeal = characteristicPHypersurfacePrime K p α) :
    IsRegularLocalRing (Localization.AtPrime q.asIdeal) ∧
      ¬ Formalization.Books.Algebra.Unit137.IsSmoothAt K
        (characteristicPHypersurface K p α) q := by
  sorry

/-! ## The generic point -/

def genericPoint (S : Type*) [CommRing S] [IsDomain S] : PrimeSpectrum S :=
  ⟨(⊥ : Ideal S), inferInstance⟩

theorem smooth_at_generic_point
    {R S : Type u} [CommRing R] [CommRing S]
    [IsDomain R] [IsDomain S]
    (f : R →+* S) (hinj : Function.Injective f)
    (hfinite : RingHom.FiniteType f) :
    letI : Algebra R S := f.toAlgebra
    letI : Algebra (FractionRing R) (FractionRing S) :=
      (Formalization.Books.Algebra.Unit113.fractionFieldMap f hinj).toAlgebra
    Formalization.Books.Algebra.Unit137.IsSmoothAt R S (genericPoint S) ↔
      Algebra.IsSeparable (FractionRing R) (FractionRing S) := by
  sorry

end

end Formalization.Books.Algebra.Unit140
