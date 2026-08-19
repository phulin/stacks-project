import Formalization.Books.Dualizing.Unit05.InjectiveHulls
import Formalization.Books.LocalCohomology.Unit17
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.CharP.Frobenius
import Mathlib.Algebra.DirectSum.Module
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.MvPowerSeries.Derivative
import Mathlib.RingTheory.MvPowerSeries.Inverse

/-!
# Local Cohomology, Chapter 18: Structure of certain modules

This file records the definitions and theorem interfaces in the section
“Structure of certain modules”.  The proofs are deferred to the proving
stage, while the definitions use the canonical power-series, derivation,
injective-hull, direct-sum, and Frobenius APIs.
-/

namespace Formalization.Books.LocalCohomology.Unit18

open CategoryTheory
open DirectSum
open scoped TensorProduct

noncomputable section

universe u v

/-! ## Torsion and direct sums -/

/-- An elementwise formulation of power torsion by an ideal. -/
def PowerTorsion {A M : Type*} [CommSemiring A] [AddCommMonoid M]
    [Module A M] (I : Ideal A) : Prop :=
  ∀ z : M, ∃ n : ℕ, ∀ a ∈ I ^ n, a • z = 0

/-- The submodule of elements killed by every element of an ideal. -/
def annihilatorSubmodule {A M : Type*} [CommSemiring A] [AddCommMonoid M]
    [Module A M] (I : Ideal A) : Submodule A M where
  carrier := {z | ∀ a ∈ I, a • z = 0}
  zero_mem' := by
    intro a ha
    simp
  add_mem' := by
    intro x y hx hy a ha
    change a • (x + y) = 0
    rw [smul_add, hx a ha, hy a ha, add_zero]
  smul_mem' := by
    intro c x hx a ha
    rw [smul_smul]
    have hac : a * c ∈ I := by
      simpa [mul_comm] using I.mul_mem_left c ha
    exact hx (a * c) hac

/-- A linear map restricts to the submodules annihilated by an ideal.  This is
the formal version of the maps denoted `φ[x]` in the source. -/
def mapAnnihilator {A M N : Type*} [CommSemiring A] [AddCommMonoid M]
    [AddCommMonoid N] [Module A M] [Module A N] (f : M →ₗ[A] N) (I : Ideal A) :
    annihilatorSubmodule (M := M) I →ₗ[A] annihilatorSubmodule (M := N) I :=
  { toFun := fun z =>
      ⟨f z, by
        intro a ha
        rw [← f.map_smul, z.2 a ha, map_zero]⟩
    map_add' := by
      intro x y
      apply Subtype.ext
      simp
    map_smul' := by
      intro a x
      apply Subtype.ext
      simp }

/-- Divisibility by a fixed scalar. -/
def IsDivisibleBy {A M : Type*} [Monoid A] [AddCommMonoid M] [DistribMulAction A M]
    (x : A) : Prop :=
  ∀ z : M, ∃ y : M, x • y = z

/-- The submodule of elements killed by each member of a family of scalars. -/
def killedByFamily {A M ι : Type*} [CommSemiring A] [AddCommMonoid M]
    [Module A M] (xs : ι → A) : Submodule A M where
  carrier := {z | ∀ i, xs i • z = 0}
  zero_mem' := by
    intro i
    simp
  add_mem' := by
    intro x y hx hy i
    change xs i • (x + y) = 0
    rw [smul_add, hx i, hy i, add_zero]
  smul_mem' := by
    intro c x hx i
    simpa [smul_smul, mul_comm] using congrArg (fun z => c • z) (hx i)

/-- The common annihilator layer used in the Frobenius proof. -/
def frobeniusTorsionLayer {A M ι : Type*} [CommSemiring A] [AddCommMonoid M]
    [Module A M] (xs : ι → A) (p n : ℕ) : Submodule A M :=
  killedByFamily (fun i => xs i ^ p ^ n)

/-- The Frobenius endomorphism used in the positive-characteristic statement. -/
def frobeniusEndomorphism {A : Type*} [CommRing A] (p : ℕ) [ExpChar A p] : A →+* A :=
  frobenius A p

/-- The tensor-product module occurring after iterating Frobenius base change. -/
def frobeniusBaseChangeModule {A M : Type*} [CommRing A] [AddCommGroup M]
    [Module A M] (p n : ℕ) [ExpChar A (p ^ n)] : ModuleCat A :=
  (ModuleCat.extendScalars (frobenius A (p ^ n))).obj (ModuleCat.of A M)

/-- Freeness over an ideal quotient, retaining the quotient-module structure
needed by the source's assertion about the layers `M_n`. -/
def IsFreeOverIdealQuotient {A N : Type*} [CommRing A] [AddCommGroup N]
    [Module A N] (I : Ideal A) : Prop :=
  ∃ h : Module (A ⧸ I) N,
    @Module.Free (A ⧸ I) N (inferInstance) (inferInstance) h

/-- A finite family is minimal when it generates the maximal ideal and its
classes form a residue-field linearly independent family. -/
def IsMinimalGeneratingFamily {A : Type*} [CommRing A] [IsLocalRing A]
    {d : ℕ} (xs : Fin d → A) : Prop :=
  Ideal.span (Set.range xs) = IsLocalRing.maximalIdeal A ∧
    LinearIndependent (A ⧸ IsLocalRing.maximalIdeal A)
      (fun i => Ideal.Quotient.mk (IsLocalRing.maximalIdeal A) (xs i))

/-- A module is a direct sum of copies of a fixed module. -/
def IsDirectSumOfCopies {A : Type u} [Ring A] (M E : ModuleCat.{u} A) : Prop :=
  ∃ J : Type u, Nonempty ((M : Type u) ≃ₗ[A] DirectSum J (fun _ => (E : Type u)))

/-- The source's phrase “a direct sum of copies of the injective hull of `k`”.

The injective hull is the canonical `InjectiveHull` predicate from the
Dualizing Complexes formalization, applied to the residue-field inclusion. -/
def IsDirectSumOfInjectiveHullCopies {A : Type u} [CommRing A] [IsLocalRing A]
    (M : ModuleCat.{u} A) : Prop :=
  ∃ (E : ModuleCat.{u} A)
    (f : ModuleCat.of A (IsLocalRing.ResidueField A) ⟶ E),
    Formalization.Books.Dualizing.Unit05.InjectiveHull f ∧
      IsDirectSumOfCopies M E

/-! ## Formal power series and Leibniz operators -/

/-- The multivariate formal power-series ring used in the characteristic-zero
structure theorem. -/
abbrev formalPowerSeries (k : Type u) (d : ℕ) := MvPowerSeries (Fin d) k

/-- The canonical formal partial derivative with respect to a variable. -/
def formalPartialDerivative (k : Type u) [CommRing k] (d : ℕ) (i : Fin d) :
    Derivation k (formalPowerSeries k d) (formalPowerSeries k d) :=
  MvPowerSeries.pderiv k i

/-- Additive operators satisfying the Leibniz rule for a family of derivations. -/
def HasLeibnizOperators {R A M ι : Type*} [CommSemiring R] [CommSemiring A]
    [AddCommMonoid M] [Algebra R A] [Module A M]
    (derivations : ι → Derivation R A A) (D : ι → M →+ M) : Prop :=
  ∀ i f z, D i (f • z) = (derivations i f) • z + f • D i z

/-! ## Characteristic-zero structure theorem -/

/-- The characteristic-zero structure theorem for power-torsion modules with
formal partial-derivative operators. -/
theorem structure_of_torsion_D_module_regular
    {k : Type u} [Field k] [CharZero k]
    (d : ℕ) (hd : 1 ≤ d)
    (M : ModuleCat.{u} (formalPowerSeries k d))
    (D : Fin d → (M : Type u) →+ (M : Type u))
    (hD : HasLeibnizOperators (R := k) (A := formalPowerSeries k d)
      (M := (M : Type u))
      (fun i => formalPartialDerivative k d i) D)
    (hT : PowerTorsion (M := (M : Type u))
      (IsLocalRing.maximalIdeal (formalPowerSeries k d))) :
    IsDirectSumOfInjectiveHullCopies M := by
  sorry

/-! ## Interfaces for the displayed proof assertions -/

/-- The divisibility consequence used in the characteristic-zero proof. -/
theorem D_module_is_divisible_by_variable
    {k : Type u} [Field k] [CharZero k]
    (d : ℕ) (hd : 1 ≤ d)
    (M : ModuleCat.{u} (formalPowerSeries k d))
    (D : Fin d → (M : Type u) →+ (M : Type u))
    (hD : HasLeibnizOperators (R := k) (A := formalPowerSeries k d)
      (M := (M : Type u)) (fun i => formalPartialDerivative k d i) D)
    (hT : PowerTorsion (M := (M : Type u))
      (IsLocalRing.maximalIdeal (formalPowerSeries k d)))
    (i : Fin d) :
    IsDivisibleBy (A := formalPowerSeries k d) (M := (M : Type u))
      (MvPowerSeries.X (R := k) i) := by
  sorry

/-! ## Interfaces for the displayed Frobenius-layer assertions -/

/-- The zeroth layer is the maximal-ideal annihilator when the chosen
generators span the maximal ideal. -/
theorem frobeniusTorsionLayer_zero_eq_annihilator
    {A M : Type*} [CommRing A] [AddCommGroup M] [Module A M]
    {d : ℕ} (xs : Fin d → A) (p : ℕ) (I : Ideal A)
    (hxs : Ideal.span (Set.range xs) = I) :
    frobeniusTorsionLayer (M := M) xs p 0 = annihilatorSubmodule I := by
  sorry

/-- Power torsion is exhausted by the Frobenius layers associated to a finite
generating family of the ideal. -/
theorem iSup_frobeniusTorsionLayer_eq_top
    {A M : Type*} [CommRing A] [AddCommGroup M] [Module A M]
    {d : ℕ} (xs : Fin d → A) (p : ℕ) (I : Ideal A)
    (hp : 0 < p) (hxs : Ideal.span (Set.range xs) = I)
    (hT : PowerTorsion (M := M) I) :
    ⨆ n : ℕ, frobeniusTorsionLayer (M := M) xs p n = ⊤ := by
  sorry

/-- The layer identification obtained by applying the Frobenius-stability
isomorphism to the iterated base change. -/
theorem frobeniusTorsionLayer_baseChange_equiv
    {A M : Type u} [CommRing A] [AddCommGroup M] [Module A M]
    [IsRegularLocalRing A]
    (p n : ℕ) [Fact p.Prime] [CharP A p] [ExpChar A p]
    [ExpChar A (p ^ n)] {d : ℕ} (xs : Fin d → A)
    (hF : Formalization.Books.LocalCohomology.Unit17.frobeniusBaseChange
      (A := A) (M := M) p) :
    Nonempty
      ((frobeniusTorsionLayer (M := M) xs p n : Type u) ≃ₗ[A]
        (frobeniusTorsionLayer
          (M := (frobeniusBaseChangeModule (A := A) (M := M) p n : Type u))
          xs p n : Type u)) := by
  sorry

/-- The layer `M_n` is free over the quotient by the `p^n`-th powers of a
minimal system of generators of the maximal ideal. -/
theorem frobeniusTorsionLayer_isFreeOverIdealQuotient
    {A M : Type u} [CommRing A] [AddCommGroup M] [Module A M]
    [IsRegularLocalRing A]
    (p : ℕ) [Fact p.Prime] [CharP A p] [ExpChar A p]
    (hT : PowerTorsion (M := M) (IsLocalRing.maximalIdeal A))
    (hF : Formalization.Books.LocalCohomology.Unit17.frobeniusBaseChange
      (A := A) (M := M) p)
    {d : ℕ} (xs : Fin d → A)
    (hxs : IsMinimalGeneratingFamily xs)
    (n : ℕ) [ExpChar A (p ^ n)] :
    IsFreeOverIdealQuotient
      (N := (frobeniusTorsionLayer (M := M) xs p n : Type u))
      (I := Ideal.span (Set.range (fun i => xs i ^ p ^ n)))
      := by
  sorry

/-- The divisibility-by-a-generator assertion used to pass from the layers
`M_n` to divisibility of the whole module. -/
theorem frobeniusTorsionLayer_isDivisibleBy_variable
    {A M : Type u} [CommRing A] [AddCommGroup M] [Module A M]
    [IsRegularLocalRing A]
    (p : ℕ) [Fact p.Prime] [CharP A p] [ExpChar A p]
    (hT : PowerTorsion (M := M) (IsLocalRing.maximalIdeal A))
    (hF : Formalization.Books.LocalCohomology.Unit17.frobeniusBaseChange
      (A := A) (M := M) p)
    {d : ℕ} (xs : Fin d → A) (hxs : IsMinimalGeneratingFamily xs)
    (n : ℕ) [ExpChar A (p ^ n)] (i : Fin d) :
    IsDivisibleBy (A := A)
      (M := (frobeniusTorsionLayer (M := M) xs p n : Type u)) (xs i) := by
  sorry

/-- The annihilator quotient isomorphism used in the induction on dimension;
the equation records its action on pure tensors without choosing quotient
representatives. -/
theorem frobenius_annihilator_quotient_equiv
    {A M : Type u} [CommRing A] [AddCommGroup M] [Module A M]
    [IsRegularLocalRing A]
    (p : ℕ) [Fact p.Prime] [CharP A p] [ExpChar A p]
    (hT : PowerTorsion (M := M) (IsLocalRing.maximalIdeal A))
    (hF : Formalization.Books.LocalCohomology.Unit17.frobeniusBaseChange
      (A := A) (M := M) p)
    {d : ℕ} (xs : Fin d → A) (hxs : IsMinimalGeneratingFamily xs)
    (i : Fin d) :
    ∃ e :
        TensorProduct A
          (annihilatorSubmodule (M := M) (Ideal.span {(xs i) ^ p}) : Type u)
          (A ⧸ Ideal.span {xs i}) ≃ₗ[A]
        (annihilatorSubmodule (M := M) (Ideal.span {xs i}) : Type u),
      ∀ (z : annihilatorSubmodule (M := M)
          (Ideal.span {(xs i) ^ p})) (a : A),
        (e (z ⊗ₜ[A] Ideal.Quotient.mk (Ideal.span {xs i}) a) : M) =
          a • ((xs i) ^ (p - 1) • (z : M)) := by
  sorry

/-! ## Frobenius-stable modules -/

/-- The Frobenius structure theorem for power-torsion modules over a regular
local ring.  `frobeniusBaseChange` is the target-action-correct base-change
interface from Chapter 17. -/
theorem structure_of_torsion_Frobenius_regular
    {A : Type u} [CommRing A] [IsRegularLocalRing A]
    (p : ℕ) [Fact p.Prime] [CharP A p] [ExpChar A p]
    (M : ModuleCat.{u} A)
    (hT : PowerTorsion (M := (M : Type u)) (IsLocalRing.maximalIdeal A))
    (hF : Formalization.Books.LocalCohomology.Unit17.frobeniusBaseChange
      (A := A) (M := (M : Type u)) p) :
    IsDirectSumOfInjectiveHullCopies M := by
  sorry

end

end Formalization.Books.LocalCohomology.Unit18
