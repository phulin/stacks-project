import Formalization.Books.Algebra.Unit03.BasicNotions
import Formalization.Books.Algebra.Unit52.Length
import Formalization.Books.Algebra.Unit119.AroundKrullAkizuki
import Mathlib.Algebra.Algebra.RestrictScalars
import Mathlib.Algebra.Module.Equiv.Basic
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.LinearAlgebra.Transvection.Generation
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.Length
import Mathlib.RingTheory.Localization.AsSubring
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Mathlib.RingTheory.Norm.Basic
import Mathlib.RingTheory.OrderOfVanishing.Basic
import Mathlib.RingTheory.Spectrum.Maximal.Basic

/-!
# Commutative Algebra, Chapter 121: Orders of vanishing

The order of vanishing on a one-dimensional fraction field is the integer-valued
form of Mathlib's `Ring.ordFrac`.  Lattices are represented by finite submodules
whose `K`-span is the whole ambient vector space, and finite colengths use
canonical submodule quotients.
-/

namespace Formalization.Books.Algebra.Unit121

open Set
open scoped BigOperators Pointwise

universe u v

noncomputable section

/-! ## Orders of vanishing -/

/- Mathlib's `Ring.ord` is the canonical extended-natural length of a principal
   quotient.  This natural-valued wrapper is used for the finite lengths in the
   source. -/
def principalQuotientLength
    (R : Type u) [CommRing R] (a : R) : ℕ :=
  (Ring.ord R a).toNat

def principalQuotientHasFiniteLength
    (R : Type u) [CommRing R] (a : R) : Prop :=
  IsFiniteLength R (R ⧸ Ideal.span ({a} : Set R))

/- The source's exact sequence is already the canonical Mathlib sequence.  Its
   middle term is written `R ⧸ (b • I)`, which is definitionally the target
   used by `Ideal.mulQuot`; for `I = (a)` this is the source's `R/(ab)` after
   the standard principal-ideal identification. -/
theorem principal_quotient_short_exact
    {R : Type u} [CommRing R] {a b : R}
    (_ha : a ∈ nonZeroDivisors R) (hb : b ∈ nonZeroDivisors R) :
    Function.Injective (Ideal.mulQuot b (Ideal.span ({a} : Set R))) ∧
      Function.Surjective (Ideal.quotOfMul b (Ideal.span ({a} : Set R))) ∧
        Function.Exact (Ideal.mulQuot b (Ideal.span ({a} : Set R)))
          (Ideal.quotOfMul b (Ideal.span ({a} : Set R))) := by
  exact ⟨Ideal.mulQuot_injective (Ideal.span ({a} : Set R)) hb,
    Ideal.quotOfMul_surjective (Ideal.span ({a} : Set R)),
    Ideal.exact_mulQuot_quotOfMul (Ideal.span ({a} : Set R))⟩

theorem principal_quotient_length_additive
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    (hsemilocal : Formalization.Books.Algebra.Unit03.IsSemilocalRing R)
    (hdim : ringKrullDim R = 1) (a b : R)
    (ha : a ∈ nonZeroDivisors R) (hb : b ∈ nonZeroDivisors R) :
    principalQuotientHasFiniteLength R a ∧
      principalQuotientHasFiniteLength R b ∧
        principalQuotientHasFiniteLength R (a * b) ∧
          Module.length R (R ⧸ Ideal.span ({a * b} : Set R)) =
            Module.length R (R ⧸ Ideal.span ({a} : Set R)) +
              Module.length R (R ⧸ Ideal.span ({b} : Set R)) := by
  sorry

/- The dimension hypothesis is supplied as a source-facing equality.  The
   canonical fraction-field API needs the corresponding `KrullDimLE 1`
   instance, which is installed locally in this definition. -/
noncomputable def orderOfVanishing
    {R : Type u} {K : Type v} [CommRing R] [IsDomain R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (hnoetherian : IsNoetherianRing R)
    (hdim : ringKrullDim R = 1) : Kˣ → ℤ :=
  letI : IsNoetherianRing R := hnoetherian
  letI : Ring.KrullDimLE 1 R := Ring.krullDimLE_iff.mpr hdim.le
  fun x => WithZero.log (Ring.ordFrac R (x : K))

noncomputable def fractionUnit
    {R : Type u} {K : Type v} [CommRing R] [IsDomain R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (x y : R) (hx : x ∈ nonZeroDivisors R)
    (hy : y ∈ nonZeroDivisors R) : Kˣ :=
  Units.mk0 (algebraMap R K x / algebraMap R K y)
    (div_ne_zero
      (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hx)
      (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hy))

theorem orderOfVanishing_fractionUnit
    {R : Type u} {K : Type v} [CommRing R] [IsDomain R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (hnoetherian : IsNoetherianRing R) (hdim : ringKrullDim R = 1)
    (x y : R) (hx : x ∈ nonZeroDivisors R)
    (hy : y ∈ nonZeroDivisors R) :
    orderOfVanishing hnoetherian hdim
        (fractionUnit (R := R) (K := K) x y hx hy) =
      (principalQuotientLength R x : ℤ) - principalQuotientLength R y := by
  sorry

@[simp]
theorem orderOfVanishing_mul
    {R : Type u} {K : Type v} [CommRing R] [IsDomain R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (hnoetherian : IsNoetherianRing R) (hdim : ringKrullDim R = 1)
    (x y : Kˣ) :
    orderOfVanishing hnoetherian hdim (x * y) =
      orderOfVanishing hnoetherian hdim x +
        orderOfVanishing hnoetherian hdim y := by
  sorry

/-! ## Lattices and their finite colengths -/

/- The tensor-product condition in the source is expressed by the equivalent
   and more usable condition that the `K`-span of the submodule is `⊤`.  The
   accompanying finite-generation condition is the source's finite
   `R`-submodule condition. -/
def IsLattice
    (R : Type u) (K : Type v) (V : Type v)
    [CommRing R] [Field K] [Algebra R K]
    [AddCommGroup V] [Module K V] [Module R V]
    [IsScalarTower R K V] (M : Submodule R V) : Prop :=
  Module.Finite R (M : Type v) ∧
    Submodule.span K (M : Set V) = (⊤ : Submodule K V)

/- This records the source's warning about the DVR case as a usable theorem:
   the non-DVR freeness caution is deliberately not strengthened into a
   universal counterexample assertion. -/
theorem lattice_free_over_dvr
    {R : Type u} {K : Type v} {V : Type v}
    [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [AddCommGroup V] [Module K V] [Module R V]
    [IsScalarTower R K V] (M : Submodule R V)
    (hM : IsLattice R K V M) : Module.Free R (M : Type v) := by
  sorry

abbrev latticeQuotient
    (R : Type u) {V : Type v} [CommRing R]
    [AddCommGroup V] [Module R V]
    (N M : Submodule R V) : Type v :=
  M ⧸ Submodule.comap M.subtype N

def latticeLengthNat
    (R : Type u) {V : Type v} [CommRing R]
    [AddCommGroup V] [Module R V]
    (N M : Submodule R V) : ℕ :=
  (Module.length R (latticeQuotient R N M)).toNat

def latticeQuotientHasFiniteLength
    (R : Type u) {V : Type v} [CommRing R]
    [AddCommGroup V] [Module R V]
    (N M : Submodule R V) : Prop :=
  IsFiniteLength R (latticeQuotient R N M)

def latticeLengthInt
    (R : Type u) {V : Type v} [CommRing R]
    [AddCommGroup V] [Module R V]
    (N M : Submodule R V) : ℤ :=
  latticeLengthNat R N M

theorem lattice_comparison_upper
    {R : Type u} {K : Type v} {V : Type v}
    [CommRing R] [IsLocalRing R] [IsDomain R] [IsNoetherianRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [AddCommGroup V] [Module K V] [Module R V]
    [IsScalarTower R K V] (hdim : ringKrullDim R = 1)
    (M M' : Submodule R V) (hM : IsLattice R K V M) (hMM' : M ≤ M') :
    List.TFAE
      [ IsLattice R K V M',
        latticeQuotientHasFiniteLength R M M',
        Module.Finite R (M' : Type v) ] := by
  sorry

theorem lattice_comparison_lower
    {R : Type u} {K : Type v} {V : Type v}
    [CommRing R] [IsLocalRing R] [IsDomain R] [IsNoetherianRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [AddCommGroup V] [Module K V] [Module R V]
    [IsScalarTower R K V] (hdim : ringKrullDim R = 1)
    (M M' : Submodule R V) (hM : IsLattice R K V M) (hM'M : M' ≤ M) :
    IsLattice R K V M' ↔ latticeQuotientHasFiniteLength R M' M := by
  sorry

theorem lattice_intersection_and_sum
    {R : Type u} {K : Type v} {V : Type v}
    [CommRing R] [IsLocalRing R] [IsDomain R] [IsNoetherianRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [AddCommGroup V] [Module K V] [Module R V]
    [IsScalarTower R K V] (hdim : ringKrullDim R = 1)
    (M M' : Submodule R V) (hM : IsLattice R K V M)
    (hM' : IsLattice R K V M') :
    IsLattice R K V (M ⊓ M') ∧ IsLattice R K V (M ⊔ M') := by
  sorry

theorem lattice_length_additive
    {R : Type u} {K : Type v} {V : Type v}
    [CommRing R] [IsLocalRing R] [IsDomain R] [IsNoetherianRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [AddCommGroup V] [Module K V] [Module R V]
    [IsScalarTower R K V] (hdim : ringKrullDim R = 1)
    (M M' M'' : Submodule R V) (hM : IsLattice R K V M)
    (hM' : IsLattice R K V M') (hM'' : IsLattice R K V M'')
    (hMM' : M ≤ M') (hM'M'' : M' ≤ M'') :
    latticeLengthNat R M M'' =
      latticeLengthNat R M M' + latticeLengthNat R M' M'' := by
  sorry

theorem lattice_length_comparison
    {R : Type u} {K : Type v} {V : Type v}
    [CommRing R] [IsLocalRing R] [IsDomain R] [IsNoetherianRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [AddCommGroup V] [Module K V] [Module R V]
    [IsScalarTower R K V] (hdim : ringKrullDim R = 1)
    (M M' N N' : Submodule R V)
    (hM : IsLattice R K V M) (hM' : IsLattice R K V M')
    (hN : IsLattice R K V N) (hN' : IsLattice R K V N')
    (hNM : N ≤ M ⊓ M') (hMM'N' : M ⊔ M' ≤ N') :
    latticeLengthInt R (M ⊓ M') M - latticeLengthInt R (M ⊓ M') M' =
        latticeLengthInt R N M - latticeLengthInt R N M' ∧
      latticeLengthInt R N M - latticeLengthInt R N M' =
        latticeLengthInt R M' (M ⊔ M') - latticeLengthInt R M (M ⊔ M') ∧
      latticeLengthInt R M' (M ⊔ M') - latticeLengthInt R M (M ⊔ M') =
        latticeLengthInt R M' N' - latticeLengthInt R M N' := by
  sorry

def latticeDistance
    (R : Type u) {V : Type v} [CommRing R]
    [AddCommGroup V] [Module R V]
    (M M' : Submodule R V) : ℤ :=
  latticeLengthInt R (M ⊓ M') M - latticeLengthInt R (M ⊓ M') M'

theorem latticeDistance_of_le
    {R : Type u} {K : Type v} {V : Type v}
    [CommRing R] [IsLocalRing R] [IsDomain R] [IsNoetherianRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [AddCommGroup V] [Module K V] [Module R V]
    [IsScalarTower R K V] (hdim : ringKrullDim R = 1)
    (M M' : Submodule R V) (hM : IsLattice R K V M)
    (hM' : IsLattice R K V M') (hM'M : M' ≤ M) :
    latticeDistance R M M' = latticeLengthInt R M' M := by
  sorry

theorem latticeDistance_additive
    {R : Type u} {K : Type v} {V : Type v}
    [CommRing R] [IsLocalRing R] [IsDomain R] [IsNoetherianRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [AddCommGroup V] [Module K V] [Module R V]
    [IsScalarTower R K V] (hdim : ringKrullDim R = 1)
    (M M' M'' : Submodule R V)
    (hM : IsLattice R K V M) (hM' : IsLattice R K V M')
    (hM'' : IsLattice R K V M'') :
    latticeDistance R M M'' =
      latticeDistance R M M' + latticeDistance R M' M'' := by
  sorry

theorem latticeDistance_antisymm
    {R : Type u} {K : Type v} {V : Type v}
    [CommRing R] [IsLocalRing R] [IsDomain R] [IsNoetherianRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [AddCommGroup V] [Module K V] [Module R V]
    [IsScalarTower R K V] (hdim : ringKrullDim R = 1)
    (M M' : Submodule R V) (hM : IsLattice R K V M)
    (hM' : IsLattice R K V M') :
    latticeDistance R M M' = -latticeDistance R M' M := by
  sorry

/-! ## Transport by linear isomorphisms and determinants -/

def latticeMap
    {R : Type u} {K : Type v} {V : Type v}
    [CommRing R] [Field K] [Algebra R K]
    [AddCommGroup V] [Module K V] [Module R V]
    [IsScalarTower R K V] (φ : V ≃ₗ[K] V) (M : Submodule R V) :
    Submodule R V :=
  M.map (φ.restrictScalars R).toLinearMap

theorem isLattice_latticeMap
    {R : Type u} {K : Type v} {V : Type v}
    [CommRing R] [IsLocalRing R] [IsDomain R] [IsNoetherianRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [AddCommGroup V] [Module K V] [Module R V]
    [IsScalarTower R K V] (hdim : ringKrullDim R = 1)
    (φ : V ≃ₗ[K] V) (M : Submodule R V) (hM : IsLattice R K V M) :
    IsLattice R K V (latticeMap φ M) := by
  sorry

theorem latticeDistance_latticeMap_pair
    {R : Type u} {K : Type v} {V : Type v}
    [CommRing R] [IsLocalRing R] [IsDomain R] [IsNoetherianRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [AddCommGroup V] [Module K V] [Module R V]
    [IsScalarTower R K V] (hdim : ringKrullDim R = 1)
    (φ : V ≃ₗ[K] V) (M M' : Submodule R V)
    (hM : IsLattice R K V M) (hM' : IsLattice R K V M') :
    latticeDistance R (latticeMap φ M) (latticeMap φ M') =
      latticeDistance R M M' := by
  sorry

theorem latticeDistance_map_independent
    {R : Type u} {K : Type v} {V : Type v}
    [CommRing R] [IsLocalRing R] [IsDomain R] [IsNoetherianRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [AddCommGroup V] [Module K V] [Module R V]
    [IsScalarTower R K V] (hdim : ringKrullDim R = 1)
    (φ : V ≃ₗ[K] V) (M M' : Submodule R V)
    (hM : IsLattice R K V M) (hM' : IsLattice R K V M') :
    latticeDistance R M (latticeMap φ M) =
      latticeDistance R M' (latticeMap φ M') := by
  sorry

theorem latticeDistance_comp_decomposition
    {R : Type u} {K : Type v} {V : Type v}
    [CommRing R] [IsLocalRing R] [IsDomain R] [IsNoetherianRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [AddCommGroup V] [Module K V] [Module R V]
    [IsScalarTower R K V] (hdim : ringKrullDim R = 1)
    (φ ψ : V ≃ₗ[K] V) (M : Submodule R V) (hM : IsLattice R K V M) :
    latticeDistance R M (latticeMap (ψ.trans φ) M) =
        latticeDistance R M (latticeMap ψ M) +
          latticeDistance R (latticeMap ψ M) (latticeMap (ψ.trans φ) M) ∧
      latticeDistance R (latticeMap ψ M) (latticeMap (ψ.trans φ) M) =
        latticeDistance R M (latticeMap φ M) := by
  sorry

theorem orderOfVanishing_det_comp
    {R : Type u} {K : Type v} {V : Type v}
    [CommRing R] [IsLocalRing R] [IsDomain R] [IsNoetherianRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [AddCommGroup V] [Module K V]
    (hnoetherian : IsNoetherianRing R) (hdim : ringKrullDim R = 1)
    (φ ψ : V ≃ₗ[K] V) :
    orderOfVanishing hnoetherian hdim (LinearEquiv.det (ψ.trans φ)) =
      orderOfVanishing hnoetherian hdim (LinearEquiv.det φ) +
        orderOfVanishing hnoetherian hdim (LinearEquiv.det ψ) := by
  sorry

theorem latticeDistance_map_eq_orderOfVanishing
    {R : Type u} {K : Type v} {V : Type v}
    [CommRing R] [IsLocalRing R] [IsDomain R] [IsNoetherianRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [AddCommGroup V] [Module K V] [Module R V]
    [IsScalarTower R K V] [Module.Finite K V]
    (hnoetherian : IsNoetherianRing R) (hdim : ringKrullDim R = 1)
    (M : Submodule R V) (hM : IsLattice R K V M) (φ : V ≃ₗ[K] V) :
    latticeDistance R M (latticeMap φ M) =
      orderOfVanishing hnoetherian hdim (LinearEquiv.det φ) := by
  sorry

/- The source's elementary matrices are represented by Mathlib's canonical
   rank-one transvections and dilatransvections. -/
theorem generalLinearEquiv_mem_generated_dilatransvections
    {K : Type v} {V : Type v} [Field K] [AddCommGroup V] [Module K V]
    [Module.Finite K V] (φ : V ≃ₗ[K] V) :
    ∃ n : ℕ, φ ∈ (LinearEquiv.dilatransvections K V) ^ n := by
  sorry

theorem exists_fin_basis_equiv
    {K : Type v} {V : Type v} [Field K] [AddCommGroup V]
    [Module K V] [Module.Finite K V] :
    ∃ n : ℕ, Nonempty ((Fin n → K) ≃ₗ[K] V) := by
  sorry

theorem latticeDistance_transvection
    {R : Type u} {K : Type v} {V : Type v}
    [CommRing R] [IsLocalRing R] [IsDomain R] [IsNoetherianRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [AddCommGroup V] [Module K V] [Module R V]
    [IsScalarTower R K V] [Module.Finite K V]
    (hnoetherian : IsNoetherianRing R) (hdim : ringKrullDim R = 1)
    (M : Submodule R V) (hM : IsLattice R K V M)
    {f : Module.Dual K V} {v : V} (hfv : f v = 0) :
    latticeDistance R M
        (latticeMap (LinearEquiv.transvection hfv) M) = 0 := by
  sorry

noncomputable def elementaryDiagonal
    {K : Type v} [Field K] (n : ℕ) (i : Fin n) (a : Kˣ) :
    (Fin n → K) ≃ₗ[K] (Fin n → K) :=
  LinearEquiv.piCongrRight (fun j =>
    if _h : j = i then a.mulLeftLinearEquiv K K else LinearEquiv.refl K K)

theorem latticeDistance_elementaryDiagonal
    {R : Type u} {K : Type v} [CommRing R] [IsLocalRing R]
    [IsDomain R] [IsNoetherianRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] (hnoetherian : IsNoetherianRing R)
    (hdim : ringKrullDim R = 1) (n : ℕ) (i : Fin n) (a : Kˣ)
    (M : Submodule R (Fin n → K))
    (hM : IsLattice R K (Fin n → K) M) :
    latticeDistance R M (latticeMap (elementaryDiagonal n i a) M) =
      orderOfVanishing hnoetherian hdim a := by
  sorry

/-! ## Finite extensions and norm formulas -/

noncomputable def localizedFractionRingAt
    {B : Type u} {L : Type v} [CommRing B] [IsDomain B]
    [Field L] [Algebra B L] [IsFractionRing B L]
    (q : MaximalSpectrum B) : Subalgebra B L :=
  Localization.subalgebra.ofField L q.asIdeal.primeCompl
    q.asIdeal.primeCompl_le_nonZeroDivisors

noncomputable def residueFieldDegreeAt
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [IsLocalRing A]
    (f : A →+* B) (q : MaximalSpectrum B)
    (hq : IsLocalRing.maximalIdeal A = q.asIdeal.comap f) : ℕ :=
  letI : Algebra (IsLocalRing.maximalIdeal A).ResidueField
      q.asIdeal.ResidueField :=
    (Ideal.ResidueField.map (IsLocalRing.maximalIdeal A) q.asIdeal f hq).toAlgebra
  Module.finrank (IsLocalRing.maximalIdeal A).ResidueField
    q.asIdeal.ResidueField

noncomputable def localizedOrderOfVanishing
    {B : Type u} {L : Type v} [CommRing B] [IsDomain B]
    [Field L] [Algebra B L] [IsFractionRing B L]
    (q : MaximalSpectrum B)
    (hnoetherian : IsNoetherianRing
      (localizedFractionRingAt (B := B) (L := L) q))
    (hdim : ringKrullDim (localizedFractionRingAt (B := B) (L := L) q) = 1)
    (y : Lˣ) : ℤ :=
  orderOfVanishing hnoetherian hdim y

theorem norm_eq_det_multiplication
    {K : Type u} {L : Type v} [Field K] [Field L]
    [Algebra K L] [Module.Finite K L] (y : L) :
    Algebra.norm K y = LinearMap.det (Algebra.lmul K L y) := by
  rfl

/- The local quotient-length identity used in the finite-extension proof is
   exactly the earlier Chapter 52 pushdown theorem, with the canonical
   `MaximalSpectrum` indexing and `Fintype.ofFinite` enumeration. -/
theorem finite_extension_local_length_sum
    {A B M : Type u} [CommRing A] [CommRing B] [IsLocalRing A]
    [Algebra A B] [AddCommGroup M] [Module B M] [Module A M]
    [IsScalarTower A B M] [Finite (MaximalSpectrum B)]
    (h_over : ∀ q : MaximalSpectrum B,
      q.asIdeal.comap (algebraMap A B) = IsLocalRing.maximalIdeal A)
    (hfinite : ∀ q : MaximalSpectrum B,
      Module.Finite A q.asIdeal.ResidueField)
    (hM : IsFiniteLength B M) :
    letI := Fintype.ofFinite (MaximalSpectrum B)
    Module.length A M =
        ∑ q : MaximalSpectrum B,
          Module.length A q.asIdeal.ResidueField *
            Module.length (Localization.AtPrime q.asIdeal)
              (LocalizedModule.AtPrime q.asIdeal M) ∧
      Module.length A M < ⊤ := by
  exact Formalization.Books.Algebra.Unit52.length_pushdown h_over hfinite hM

theorem finite_extension_order_formula
    {A B K L : Type u} [CommRing A] [CommRing B]
    [IsDomain A] [IsDomain B] [IsLocalRing A] [IsNoetherianRing A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    [Field L] [Algebra B L] [IsFractionRing B L]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    [Module.Finite K L] (f : A →+* B)
    (hinjective : Function.Injective f) (hfinite : RingHom.Finite f)
    (hcompat : (algebraMap K L).comp (algebraMap A K) =
      (algebraMap B L).comp f)
    (hKL : Function.Injective (algebraMap K L))
    (hdim : ringKrullDim A = 1) :
    ∃ hsemilocal : Finite (MaximalSpectrum B),
      letI := hsemilocal
      ∃ hmax : ∀ q : MaximalSpectrum B,
          IsLocalRing.maximalIdeal A = q.asIdeal.comap f,
        ∃ hlocal : ∀ q : MaximalSpectrum B,
            IsNoetherianRing (localizedFractionRingAt (B := B) (L := L) q) ∧
              ringKrullDim (localizedFractionRingAt (B := B) (L := L) q) = 1,
          letI := Fintype.ofFinite (MaximalSpectrum B)
          ∀ y : Lˣ,
            orderOfVanishing (inferInstance : IsNoetherianRing A) hdim
                (Units.map (Algebra.norm K) y) =
              ∑ q : MaximalSpectrum B,
                residueFieldDegreeAt f q (hmax q) *
                  localizedOrderOfVanishing (B := B) (L := L) q
                    (hlocal q).1 (hlocal q).2 y := by
  sorry

end

end Formalization.Books.Algebra.Unit121
