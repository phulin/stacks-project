import Formalization.Books.MoreAlgebra.Unit34.CartierEquality
import Formalization.Books.Algebra.Unit106.RegularLocalRings
import Formalization.Books.Algebra.Unit166.GeometricallyRegular
import Mathlib.Algebra.Algebra.ZMod
import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.RingTheory.MvPolynomial.Localization

/-!
# More on Algebra, Chapter 35: Geometric regularity

This file records the local Jacobi--Zariski sequence, the positive
characteristic criterion for geometric regularity, and the residue-field
flatness lemma from the source section.  Geometric regularity and regular
rings use the canonical predicates from the earlier Algebra chapters.
-/

namespace Formalization.Books.MoreAlgebra.Unit35

open scoped TensorProduct

noncomputable section

universe u v

/-! ## The local Jacobi--Zariski sequence -/

@[instance_reducible]
noncomputable def residueFieldAlgebra
    {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [IsLocalRing A] : Algebra R (IsLocalRing.ResidueField A) :=
  Algebra.compHom (IsLocalRing.ResidueField A) (algebraMap R A)

/-- The canonical first-cotangent map at the residue field.  The canonical
conormal identification for the residue-field quotient identifies its target
with the usual `m/m²` term in the local Jacobi--Zariski sequence. -/
noncomputable def residueH1CotangentMap
    {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [IsLocalRing A] :
    let K := IsLocalRing.ResidueField A
    letI : Algebra R K := residueFieldAlgebra
    letI : Algebra A K := IsLocalRing.ResidueField.algebra (R₀ := A) A
    letI : IsScalarTower R A K :=
      IsScalarTower.of_algebraMap_eq' (by ext; rfl)
    Algebra.H1Cotangent R K →ₗ[K] Algebra.H1Cotangent A K := by
  let K := IsLocalRing.ResidueField A
  letI : Algebra R K := residueFieldAlgebra
  letI : Algebra A K := IsLocalRing.ResidueField.algebra (R₀ := A) A
  letI : IsScalarTower R A K :=
    IsScalarTower.of_algebraMap_eq' (by ext; rfl)
  exact Algebra.H1Cotangent.map R A K K

/-- The local Jacobi--Zariski exact sequence, with the canonical conormal
module represented by `Algebra.H1Cotangent A K`, which is canonically
`m/m²` for the residue-field quotient. -/
theorem local_jacobi_zariski_exact
    {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [IsLocalRing A] :
    let K := IsLocalRing.ResidueField A
    letI : Algebra R K := residueFieldAlgebra
    letI : Algebra A K := IsLocalRing.ResidueField.algebra (R₀ := A) A
    letI : IsScalarTower R A K :=
      IsScalarTower.of_algebraMap_eq' (by ext; rfl)
    Function.Exact (residueH1CotangentMap (R := R) (A := A))
        (Algebra.H1Cotangent.δ R A K) ∧
      Function.Exact (Algebra.H1Cotangent.δ R A K)
        (KaehlerDifferential.mapBaseChange R A K) ∧
      Function.Surjective (KaehlerDifferential.mapBaseChange R A K) := by
  sorry

/-! ## The differential map in the characteristic-p criterion -/

/-- The canonical map
`K ⊗[R] Ω[P/R] → K ⊗[A] Ω[P/A]` at a residue field, expressed with
the canonical associativity/cancellation equivalence for tensor products. -/
noncomputable def residueDifferentialMap
    {P R A : Type*} [CommRing P] [CommRing R] [CommRing A]
    [Algebra P R] [Algebra R A] [Algebra P A]
    [IsScalarTower P R A]
    [IsLocalRing A] :
    let K := IsLocalRing.ResidueField A
    letI : Algebra P K := Algebra.compHom K (algebraMap P A)
    letI : Algebra R K := residueFieldAlgebra
    letI : Algebra A K := IsLocalRing.ResidueField.algebra (R₀ := A) A
    letI : IsScalarTower R A K :=
      IsScalarTower.of_algebraMap_eq' (by ext; rfl)
    letI : IsScalarTower P A K :=
      IsScalarTower.of_algebraMap_eq' (by ext; rfl)
    letI : IsScalarTower P R K :=
      IsScalarTower.of_algebraMap_eq' (by
        ext x
        simp only [RingHom.comp_apply]
        rw [IsScalarTower.algebraMap_apply R A K]
        rw [← IsScalarTower.algebraMap_apply P R A]
        rw [← IsScalarTower.algebraMap_apply P A K])
    letI : IsScalarTower R K K := IsScalarTower.right
    letI : IsScalarTower P K K := IsScalarTower.right
    letI : Module P K := Algebra.toModule
    letI : Module R K := Algebra.toModule
    letI : Module A K := Algebra.toModule
    letI : SMulCommClass R K K :=
      Algebra.to_smulCommClass (R := R) (A := K)
    letI : SMulCommClass A K K :=
      Algebra.to_smulCommClass (R := A) (A := K)
    letI : Module K (K ⊗[R] KaehlerDifferential P R) := by
      letI : SMulCommClass R K K := Algebra.to_smulCommClass
      exact
        @TensorProduct.leftModule R K _ _ K (KaehlerDifferential P R)
          _ _ _ _ _ (Algebra.to_smulCommClass (R := R) (A := K))
    letI : Module K (K ⊗[A] KaehlerDifferential P A) := by
      letI : SMulCommClass A K K := Algebra.to_smulCommClass
      exact TensorProduct.leftModule
    K ⊗[R] KaehlerDifferential P R →ₗ[K]
      K ⊗[A] KaehlerDifferential P A := by
  let K := IsLocalRing.ResidueField A
  letI : Algebra P K := Algebra.compHom K (algebraMap P A)
  letI : Algebra R K := residueFieldAlgebra
  letI : Algebra A K := IsLocalRing.ResidueField.algebra (R₀ := A) A
  letI : IsScalarTower R A K :=
    IsScalarTower.of_algebraMap_eq' (by ext; rfl)
  letI : IsScalarTower P A K :=
    IsScalarTower.of_algebraMap_eq' (by ext; rfl)
  letI : IsScalarTower P R K :=
    IsScalarTower.of_algebraMap_eq' (by
      ext x
      simp only [RingHom.comp_apply]
      rw [IsScalarTower.algebraMap_apply R A K]
      rw [← IsScalarTower.algebraMap_apply P R A]
      rw [← IsScalarTower.algebraMap_apply P A K])
  letI : IsScalarTower R K K := IsScalarTower.right
  letI : IsScalarTower P K K := IsScalarTower.right
  letI : Module P K := Algebra.toModule
  letI : Module R K := Algebra.toModule
  letI : Module A K := Algebra.toModule
  letI : SMulCommClass R K K :=
    Algebra.to_smulCommClass (R := R) (A := K)
  letI : SMulCommClass A K K :=
    Algebra.to_smulCommClass (R := A) (A := K)
  letI : Module K (K ⊗[R] KaehlerDifferential P R) := by
    letI : SMulCommClass R K K := Algebra.to_smulCommClass
    exact
      @TensorProduct.leftModule R K _ _ K (KaehlerDifferential P R)
        _ _ _ _ _ (Algebra.to_smulCommClass (R := R) (A := K))
  letI : Module K (K ⊗[A] KaehlerDifferential P A) := by
    letI : SMulCommClass A K K := Algebra.to_smulCommClass
    exact TensorProduct.leftModule
  let e := TensorProduct.AlgebraTensorModule.cancelBaseChange
      R A K K (KaehlerDifferential P R)
  exact
    (TensorProduct.AlgebraTensorModule.lTensor K K
      (KaehlerDifferential.mapBaseChange P R A)).comp
      e.symm.toLinearMap

/-! ## The characteristic-p criterion -/

/-- In positive characteristic, geometric regularity of a Noetherian local
`k`-algebra is equivalent to the finite purely inseparable base-change test,
regularity together with injectivity of the local first-cotangent map, and
regularity together with injectivity of the differential map over
`\mathbf F_p`. -/
theorem characterization_geometrically_regular
    {k A : Type u} [Field k] [CommRing A] [Algebra k A]
    [IsLocalRing A] [IsNoetherianRing A]
    (p : ℕ) (hp : 0 < p) [CharP k p] [Fact (Nat.Prime p)] :
    letI : Algebra (ZMod p) k :=
      @ZMod.algebra k _ p (inferInstance : CharP k p)
    letI : Algebra (ZMod p) A :=
      Algebra.compHom A ((algebraMap k A).comp (algebraMap (ZMod p) k))
    letI : IsScalarTower (ZMod p) k A :=
      IsScalarTower.of_algebraMap_eq' (by ext; rfl)
    List.TFAE
      [ Formalization.Books.Algebra.Unit166.IsGeometricallyRegular k A,
        ∀ (k' : Type u) [Field k'] [Algebra k k']
          [FiniteDimensional k k'] [IsPurelyInseparable k k'],
          IsRegularRing (k' ⊗[k] A),
        IsRegularLocalRing A ∧
          Function.Injective (residueH1CotangentMap (R := k) (A := A)),
        IsRegularLocalRing A ∧
          Function.Injective
            (residueDifferentialMap (P := ZMod p) (R := k) (A := A)) ] := by
  sorry

/-! ## The finitely generated residue-field lemma -/

/-- The data used to say that a polynomial presentation has residue-field
coordinates whose differentials form a basis. -/
structure ResidueFieldCoordinateData
    {k A K F : Type u} [Field k] [CommRing A] [Algebra k A]
    [Field K] [Field F] [Algebra k F] [Algebra k K] [Algebra F K]
    [IsScalarTower k F K] [IsLocalRing A] where
  numberOfVariables : ℕ
  map : MvPolynomial (Fin numberOfVariables) k →ₐ[k] A
  coordinates : Fin numberOfVariables → F
  differentialBasis :
    Module.Basis (Fin numberOfVariables) k (KaehlerDifferential k F)
  differentialBasis_eq : ∀ i,
    differentialBasis i = KaehlerDifferential.D k F (coordinates i)
  residueFieldMap : IsLocalRing.ResidueField A →+* K
  residueFieldMap_bijective : Function.Bijective residueFieldMap
  residue_coordinates : ∀ i,
    residueFieldMap (IsLocalRing.residue A (map (MvPolynomial.X i))) =
      algebraMap F K (coordinates i)
  prime : PrimeSpectrum (MvPolynomial (Fin numberOfVariables) k)
  prime_eq_comap : prime.asIdeal =
    (IsLocalRing.maximalIdeal A).comap map.toRingHom

/-! The source's `k[y_1, ..., y_m]` is represented by a finite-variable
MvPolynomial algebra; the localization map is retained explicitly in the
conclusion so that its flatness and its compatibility with the polynomial
map are both visible in the interface. -/
theorem geometrically_regular_over_field
    {k A K F : Type u} [Field k] [CommRing A] [Algebra k A]
    [Field K] [Field F] [Algebra k F] [Algebra k K] [Algebra F K]
    [IsScalarTower k F K] [IsLocalRing A] [IsNoetherianRing A]
    [Algebra.FiniteType k F]
    (hgeom : Formalization.Books.Algebra.Unit166.IsGeometricallyRegular k A)
    (data : ResidueFieldCoordinateData (k := k) (A := A) (K := K) (F := F)) :
    ∃ ψ : Localization.AtPrime data.prime.asIdeal →+* A,
      ψ.comp (algebraMap (MvPolynomial (Fin data.numberOfVariables) k)
        (Localization.AtPrime data.prime.asIdeal)) = data.map.toRingHom ∧
      RingHom.Flat ψ ∧
      IsRegularRing
        (A ⧸ Ideal.map data.map.toRingHom data.prime.asIdeal) := by
  sorry

end

end Formalization.Books.MoreAlgebra.Unit35
