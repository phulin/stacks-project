import Formalization.Books.MoreAlgebra.Unit37.FormallySmooth
import Formalization.Books.Algebra.Unit110.RegularRingsAndGlobalDimension
import Formalization.Books.Algebra.Unit134.NaiveCotangentComplex
import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.FieldTheory.PurelyInseparable.PerfectClosure
import Mathlib.RingTheory.MvPolynomial.Localization
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Algebra.Algebra.ZMod
import Mathlib.RingTheory.RingHom.Flat
import Mathlib.RingTheory.AdicCompletion.RingHom
import Mathlib.RingTheory.Localization.Away.Basic

/-!
# More Algebra, Chapter 40: Geometric regularity and formal smoothness

This file records the definitions, examples, and theorem interfaces in the
section. Adic formal smoothness is the canonical Unit37 predicate. Regular
rings use the earlier Unit110 predicate, and cotangent and differential maps
use Mathlib's canonical interfaces.
-/

namespace Formalization.Books.MoreAlgebra.Unit40

open scoped TensorProduct

noncomputable section

universe u v w

/-! ## Geometric regularity and the local characteristic criteria -/

/- The bundled `IsRegularRing` predicate from Unit110 additionally asks for a
  noetherian-ring instance.  The tensor products in the definition below are
  noetherian by the usual finite-dimensional argument, but that fact is not a
  typeclass in the current Mathlib API.  We therefore use its underlying local
  criterion here. -/
def IsRegularRingPredicate (R : Type*) [CommRing R] : Prop :=
  ∀ p : PrimeSpectrum R, IsRegularLocalRing (Localization.AtPrime p.asIdeal)

/-- A Noetherian algebra over a field is geometrically regular when every
finite purely inseparable field extension has regular base change. -/
def IsGeometricallyRegular
    (k : Type u) (A : Type v) [Field k] [CommRing A] [Algebra k A]
    : Prop :=
  ∀ (k' : Type u) [Field k'] [Algebra k k'] [FiniteDimensional k k']
    [IsPurelyInseparable k k'],
    letI : Algebra k' (k' ⊗[k] A) := Algebra.TensorProduct.leftAlgebra
    IsRegularRingPredicate (k' ⊗[k] A)

/- The residue field algebra is intentionally instance-reducible: it is a
  canonical composed algebra used throughout the chapter. -/
@[instance_reducible]
noncomputable def residueFieldAlgebra
    {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [IsLocalRing A] : Algebra R (IsLocalRing.ResidueField A) :=
  Algebra.compHom (IsLocalRing.ResidueField A) (algebraMap R A)

/-- The canonical first-cotangent map at the residue field.  The canonical
conormal equivalence for the residue-field quotient identifies its target
with the usual `m/m²` term in the Jacobi--Zariski sequence. -/
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

/-- Injectivity of the source's canonical map H_1(L_{K/R}) to m/m². -/
def residueH1CotangentInjective
    {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [IsLocalRing A] : Prop :=
  Function.Injective (residueH1CotangentMap (R := R) (A := A))

/-- The base-change map on differentials at a residue field. -/
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

/-- Characteristic zero case of the chapter's main characterization. -/
theorem regular_iff_formallySmooth_charZero
    {k A : Type u} [Field k] [CharZero k] [CommRing A] [Algebra k A]
    [IsLocalRing A] [IsNoetherianRing A] :
    IsRegularLocalRing A ↔
      Formalization.Books.MoreAlgebra.Unit37.FormallySmoothForIdeal
        (algebraMap k A) (IsLocalRing.maximalIdeal A) := by
  sorry

/-- Positive-characteristic case of the chapter's main characterization. -/
theorem geometricallyRegular_iff_formallySmooth_charP
    {k A : Type u} [Field k] [CommRing A] [Algebra k A]
    [IsLocalRing A] [IsNoetherianRing A]
    (p : ℕ) (hp : 0 < p) [CharP k p] [Fact (Nat.Prime p)] :
    letI : Algebra (ZMod p) k := @ZMod.algebra k _ p (inferInstance : CharP k p)
    letI : Algebra (ZMod p) A :=
      Algebra.compHom A ((algebraMap k A).comp (algebraMap (ZMod p) k))
    letI : IsScalarTower (ZMod p) k A :=
      IsScalarTower.of_algebraMap_eq' (by ext; rfl)
    List.TFAE
      [ IsGeometricallyRegular k A,
        Formalization.Books.MoreAlgebra.Unit37.FormallySmoothForIdeal
          (algebraMap k A) (IsLocalRing.maximalIdeal A),
        ∀ (k' : Type u) [Field k'] [Algebra k k'] [FiniteDimensional k k']
          [IsPurelyInseparable k k'],
          letI : Algebra k' (k' ⊗[k] A) := Algebra.TensorProduct.leftAlgebra
          IsRegularRingPredicate (k' ⊗[k] A),
        IsRegularLocalRing A ∧ residueH1CotangentInjective (R := k) (A := A),
        IsRegularLocalRing A ∧
          Function.Injective
            (residueDifferentialMap (P := ZMod p) (R := k) (A := A)) ] := by
  sorry

/-! ## The examples -/

/-- The prime ideal used for the inseparable residue-field example. -/
def inseparableExamplePrimeIdeal
    (k : Type*) [Field k] (p : ℕ) (a : k) :
    Ideal (MvPolynomial (Fin 2) k) :=
  Ideal.span
    ({MvPolynomial.X (0 : Fin 2),
      MvPolynomial.X (1 : Fin 2) ^ p - MvPolynomial.C a} :
      Set (MvPolynomial (Fin 2) k))

/-- The relation ideal imposing `y^p - a = x`. -/
def inseparableExampleRelationIdeal
    (k : Type*) [Field k] (p : ℕ) (a : k) :
    Ideal (MvPolynomial (Fin 2) k) :=
  Ideal.span
    ({MvPolynomial.X (1 : Fin 2) ^ p - MvPolynomial.C a -
        MvPolynomial.X (0 : Fin 2)} : Set (MvPolynomial (Fin 2) k))

/-- The localization-and-quotient ring
`k[x,y]_(x,y^p-a)/(y^p-a-x)` from the source example. -/
noncomputable def inseparableResidueExampleRing
    (k : Type*) [Field k] (p : ℕ) (a : k)
    (q : PrimeSpectrum (MvPolynomial (Fin 2) k)) : Type _ :=
  Localization.AtPrime q.asIdeal ⧸
    Ideal.map
      (algebraMap (MvPolynomial (Fin 2) k)
        (Localization.AtPrime q.asIdeal))
      (inseparableExampleRelationIdeal k p a)

noncomputable instance inseparableResidueExampleCommRing
    (k : Type*) [Field k] (p : ℕ) (a : k)
    (q : PrimeSpectrum (MvPolynomial (Fin 2) k)) :
    CommRing (inseparableResidueExampleRing k p a q) := by
  dsimp [inseparableResidueExampleRing]
  infer_instance

noncomputable instance inseparableResidueExampleAlgebra
    (k : Type*) [Field k] (p : ℕ) (a : k)
    (q : PrimeSpectrum (MvPolynomial (Fin 2) k)) :
    Algebra k (inseparableResidueExampleRing k p a q) := by
  dsimp [inseparableResidueExampleRing]
  infer_instance

/-- The ideal induced by the source localization prime in the quotient. -/
noncomputable def inseparableResidueExampleMaximalIdeal
    (k : Type*) [Field k] (p : ℕ) (a : k)
    (q : PrimeSpectrum (MvPolynomial (Fin 2) k)) :
    Ideal (inseparableResidueExampleRing k p a q) :=
  Ideal.map
    (Ideal.Quotient.mk
      (Ideal.map
        (algebraMap (MvPolynomial (Fin 2) k)
          (Localization.AtPrime q.asIdeal))
        (inseparableExampleRelationIdeal k p a)))
    (Ideal.map
      (algebraMap (MvPolynomial (Fin 2) k)
        (Localization.AtPrime q.asIdeal)) q.asIdeal)

/-- The first example is formally smooth in the induced maximal-ideal
topology when `a` is not a `p`th power and the displayed localization prime
is the standard one. -/
theorem inseparable_residue_example_formallySmooth
    (k : Type*) [Field k] (p : ℕ) [Fact (Nat.Prime p)]
    [CharP k p] (a : k) (ha : ∀ b : k, b ^ p ≠ a)
    (q : PrimeSpectrum (MvPolynomial (Fin 2) k))
    (hq : q.asIdeal = inseparableExamplePrimeIdeal k p a) :
    Formalization.Books.MoreAlgebra.Unit37.FormallySmoothForIdeal
      (algebraMap k (inseparableResidueExampleRing k p a q))
      (inseparableResidueExampleMaximalIdeal k p a q) := by
  sorry

/-- Data for the second example: `k = F_p(s)`, a perfect purely inseparable
extension model for `K`, and the map `s ↦ t + x` into `K[[x]]`. -/
structure PowerSeriesFormalSmoothExample
    (p : ℕ) [Fact (Nat.Prime p)] where
  k : Type u
  K : Type u
  [fieldK : Field k]
  [fieldK' : Field K]
  [charPK : CharP K p]
  [algebraFpK : Algebra (ZMod p) K]
  [algebraRationalK : Algebra (FractionRing (Polynomial (ZMod p))) K]
  [perfectK : PerfectField K]
  k_rationalFunctionField : Nonempty
    (k ≃+* FractionRing (Polynomial (ZMod p)))
  K_purelyInseparableOverK :
    IsPurelyInseparable (FractionRing (Polynomial (ZMod p))) K
  K_perfectClosure : Nonempty
    (K ≃+*
      (perfectClosure (FractionRing (Polynomial (ZMod p)))
        (AlgebraicClosure (FractionRing (Polynomial (ZMod p))))))
  s : k
  t : K
  map : k →+* PowerSeries K
  map_s : map s = PowerSeries.C t + PowerSeries.X
  cotangentFree : Module.Free (PowerSeries K)
    (KaehlerDifferential (ZMod p) (PowerSeries K))
  formallySmooth :
    Formalization.Books.MoreAlgebra.Unit37.FormallySmoothForIdeal map
      (IsLocalRing.maximalIdeal (PowerSeries K))

/-- The second source example is available with its stated formal-smoothness
property. -/
theorem exists_powerSeries_formallySmooth_example
    (p : ℕ) [Fact (Nat.Prime p)] :
    Nonempty (PowerSeriesFormalSmoothExample p) := by
  sorry

/-! ## Local maps, the Jacobi--Zariski sequence, and lifting -/

/-- Formal smoothness of a local algebra map in the target maximal-ideal
adic topology. -/
def FormallySmoothLocalMap
    {A B : Type*} [CommRing A] [CommRing B] [IsLocalRing B]
    [Algebra A B] : Prop :=
  Formalization.Books.MoreAlgebra.Unit37.FormallySmoothForIdeal
    (algebraMap A B) (IsLocalRing.maximalIdeal B)

/-- The special fibre is presented in Mathlib's canonical order
`k ⊗[A] B`; it is canonically isomorphic to the source's `B ⊗[A] k`. -/
abbrev SpecialFiber
    (A B : Type*) [CommRing A] [CommRing B] [Algebra A B]
    [IsLocalRing A] : Type _ :=
  IsLocalRing.ResidueField A ⊗[A] B

/-- A formally smooth local map of Noetherian local rings is flat. -/
theorem formallySmooth_localMap_flat
    {A B : Type*} [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B]
    [IsNoetherianRing A] [IsNoetherianRing B]
    [Algebra A B] [IsLocalHom (algebraMap A B)]
    (hfs : FormallySmoothLocalMap (A := A) (B := B)) :
    RingHom.Flat (algebraMap A B) := by
  sorry

/-- The Jacobi--Zariski exact sequence used in the local argument.  The
`H₁` term is the canonical cotangent model for the conormal space
`m_B / m_B²`. -/
theorem formallySmooth_JacobiZariski
    {A B : Type*} [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B]
    [IsNoetherianRing A] [IsNoetherianRing B]
    (f : A →+* B) [IsLocalHom f]
    (hfs : Formalization.Books.MoreAlgebra.Unit37.FormallySmoothForIdeal
      f (IsLocalRing.maximalIdeal B)) :
    letI : Algebra A B := f.toAlgebra
    let K := IsLocalRing.ResidueField B
    letI : Algebra B K := IsLocalRing.ResidueField.algebra (R₀ := B) B
    letI : Algebra A K := Algebra.compHom K f
    letI : IsScalarTower A B K :=
      IsScalarTower.of_algebraMap_eq' (by ext; rfl)
    Function.Injective (Algebra.H1Cotangent.map A B K K) ∧
      Function.Exact (Algebra.H1Cotangent.map A B K K)
        (Algebra.H1Cotangent.δ A B K) ∧
      Function.Exact (Algebra.H1Cotangent.δ A B K)
        (KaehlerDifferential.mapBaseChange A B K) ∧
      Function.Surjective (KaehlerDifferential.mapBaseChange A B K) := by
  sorry

/-- Flatness and geometrically regular formal-smoothness of the special
fibre are equivalent to formal smoothness of a Noetherian local map. -/
theorem flat_geometricallyRegular_specialFiber_iff_formallySmooth
    {A B : Type*} [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B]
    [IsNoetherianRing A] [IsNoetherianRing B]
    [Algebra A B] [IsLocalHom (algebraMap A B)] :
    let k := IsLocalRing.ResidueField A
    let F := SpecialFiber A B
    letI : Algebra k F := Algebra.TensorProduct.leftAlgebra
    List.TFAE
      [ RingHom.Flat (algebraMap A B) ∧ IsGeometricallyRegular k F,
        RingHom.Flat (algebraMap A B) ∧
          FormallySmoothLocalMap (A := k) (B := F),
        FormallySmoothLocalMap (A := A) (B := B) ] := by
  sorry

/-- Data supplied by the lifting lemma: a Noetherian complete local
`A`-algebra with formally smooth structure and the prescribed special fibre. -/
structure FormallySmoothLiftData
    (A B : Type*) [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B]
    [IsNoetherianRing A] [IsNoetherianRing B]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    [IsAdicComplete (IsLocalRing.maximalIdeal B) B]
    [Algebra (IsLocalRing.ResidueField A) B] where
  C : Type*
  [commRingC : CommRing C]
  [localRingC : IsLocalRing C]
  [noetherianC : IsNoetherianRing C]
  [completeC : IsAdicComplete (IsLocalRing.maximalIdeal C) C]
  [algebraAC : Algebra A C]
  [localHomAC : IsLocalHom (algebraMap A C)]
  formalSmooth : FormallySmoothLocalMap (A := A) (B := C)
  specialFiberEquiv : Nonempty
    ((C ⊗[A] IsLocalRing.ResidueField A) ≃+*
      B)

/-- Existence of the complete local formally smooth lift with prescribed
special fibre. -/
theorem exists_formallySmooth_lift
    {A B : Type*} [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B]
    [IsNoetherianRing A] [IsNoetherianRing B]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    [IsAdicComplete (IsLocalRing.maximalIdeal B) B]
    [Algebra (IsLocalRing.ResidueField A) B]
    (_hfsB : FormallySmoothLocalMap
      (A := IsLocalRing.ResidueField A) (B := B)) :
    Nonempty (FormallySmoothLiftData A B) := by
  sorry

/-! ## The completion remark following the lifting lemma -/

/-- The completed tensor product appearing in the deformation remark. -/
noncomputable def completedBaseChange
    {A A' C : Type*} [CommRing A] [CommRing A'] [CommRing C]
    [IsLocalRing A'] [Algebra A A'] [Algebra A C] : Type _ :=
  let T := C ⊗[A] A'
  letI : Algebra A' T := Algebra.TensorProduct.rightAlgebra
  AdicCompletion
    (Ideal.map (algebraMap A' T) (IsLocalRing.maximalIdeal A')) T

noncomputable instance completedBaseChangeCommRing
    {A A' C : Type*} [CommRing A] [CommRing A'] [CommRing C]
    [IsLocalRing A'] [Algebra A A'] [Algebra A C] :
    CommRing (completedBaseChange (A := A) (A' := A') (C := C)) := by
  dsimp [completedBaseChange]
  infer_instance

/-- The four formal properties of the completed tensor product in the
source's final remark. -/
def completedBaseChangeRemark
    {A A' B C : Type*} [CommRing A] [CommRing A'] [CommRing B] [CommRing C]
    [IsLocalRing A] [IsLocalRing A'] [IsLocalRing B] [IsLocalRing C]
    [Algebra A A'] [Algebra A C] [Algebra A B] [Algebra A' B] [Algebra C B]
    [IsLocalHom (algebraMap A A')] [IsLocalHom (algebraMap A C)]
    [IsLocalHom (algebraMap A' B)] [IsLocalHom (algebraMap C B)]
    [IsScalarTower A A' B] [IsScalarTower A C B]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A') A']
    [IsAdicComplete (IsLocalRing.maximalIdeal B) B]
    [IsAdicComplete (IsLocalRing.maximalIdeal C) C]
    (_hres : Nonempty
      (IsLocalRing.ResidueField A ≃+* IsLocalRing.ResidueField A'))
    (_hfibre : Nonempty
      ((C ⊗[A] IsLocalRing.ResidueField A) ≃+*
        (IsLocalRing.ResidueField A' ⊗[A'] B)))
    (_hfsC : FormallySmoothLocalMap (A := A) (B := C))
    (_hfsSpecial : FormallySmoothLocalMap
      (A := IsLocalRing.ResidueField A')
      (B := SpecialFiber A' B)) : Prop :=
  ∃ φ : completedBaseChange (A := A) (A' := A') (C := C) →+* B,
    Function.Surjective φ ∧
      (Function.Surjective (algebraMap A A') →
        Function.Surjective (algebraMap C B)) ∧
      (Module.Finite A A' → Module.Finite C B) ∧
      (RingHom.Flat (algebraMap A' B) →
        Nonempty (completedBaseChange (A := A) (A' := A') (C := C) ≃+* B))

/-- The completed tensor product satisfies the four properties listed in the
source remark once the formally smooth special-fibre lift is fixed. -/
theorem completedBaseChange_remark
    {A A' B C : Type*} [CommRing A] [CommRing A'] [CommRing B] [CommRing C]
    [IsLocalRing A] [IsLocalRing A'] [IsLocalRing B] [IsLocalRing C]
    [Algebra A A'] [Algebra A C] [Algebra A B] [Algebra A' B] [Algebra C B]
    [IsLocalHom (algebraMap A A')] [IsLocalHom (algebraMap A C)]
    [IsLocalHom (algebraMap A' B)] [IsLocalHom (algebraMap C B)]
    [IsScalarTower A A' B] [IsScalarTower A C B]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A') A']
    [IsAdicComplete (IsLocalRing.maximalIdeal B) B]
    [IsAdicComplete (IsLocalRing.maximalIdeal C) C]
    (_hres : Nonempty
      (IsLocalRing.ResidueField A ≃+* IsLocalRing.ResidueField A'))
    (_hfibre : Nonempty
      ((C ⊗[A] IsLocalRing.ResidueField A) ≃+*
        (IsLocalRing.ResidueField A' ⊗[A'] B)))
    (_hfsC : FormallySmoothLocalMap (A := A) (B := C))
    (_hfsSpecial : FormallySmoothLocalMap
      (A := IsLocalRing.ResidueField A')
      (B := SpecialFiber A' B)) :
    completedBaseChangeRemark _hres _hfibre _hfsC _hfsSpecial := by
  sorry

end

end Formalization.Books.MoreAlgebra.Unit40
