import Formalization.Books.Algebra.Unit25.ZerodivisorsAndTotalRingsOfFractions
import Formalization.Books.Algebra.Unit42.SeparableExtensions
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.Algebra.Colimit.DirectLimit
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Field.TransferInstance
import Mathlib.Algebra.Algebra.Shrink
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.FieldTheory.Separable
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.TensorProduct.DirectLimit
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Polynomial.Nilpotent
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.RingTheory.TensorProduct.Pi
import Mathlib.RingTheory.TensorProduct.MvPolynomial
import Mathlib.RingTheory.AlgebraicIndependent.Adjoin
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Localization.FractionRing

/-!
# Commutative Algebra, Chapter 43: Geometrically reduced algebras

The source predicate is expressed by quantifying over field extensions and using
Mathlib's canonical `IsReduced`, tensor product, subalgebra, localization, and
finite-type APIs.
-/

namespace Formalization.Books.Algebra.Unit43

open scoped TensorProduct

universe u v w z

noncomputable section

/-! ## The definition -/

/-- An algebra is geometrically reduced over a field when every field base
change remains reduced. -/
def IsGeometricallyReduced (k : Type u) (S : Type v) [Field k] [CommRing S]
    [Algebra k S] : Prop :=
  ∀ (K : Type u) [Field K] [Algebra k K],
    IsReduced (K ⊗[k] S)

/- The introductory reduction to an algebraic closure and to finite purely
   inseparable extensions is recorded here as its two source-facing
   sufficiency statements. -/

/-- Reducedness after tensoring with an algebraic closure is enough to imply
geometric reducedness. -/
theorem isGeometricallyReduced_of_isReduced_algebraicClosure
    {k : Type u} {S : Type v} {Ω : Type w}
    [Field k] [CommRing S] [Field Ω]
    [Algebra k S] [Algebra k Ω]
    [Algebra.IsAlgebraic k Ω] [IsAlgClosed Ω]
    (hS : IsReduced S) (hΩ : IsReduced (Ω ⊗[k] S)) :
    IsGeometricallyReduced k S := by
  sorry

/-- It is enough to test reducedness after every finite purely inseparable
field extension of the base. -/
theorem isGeometricallyReduced_of_finitePurelyInseparable_baseChanges
    {k : Type u} {S : Type v} [Field k] [CommRing S] [Algebra k S]
    (hS : IsReduced S)
    (h : ∀ (k' : Type u) [Field k'] [Algebra k k']
      [FiniteDimensional k k'] [IsPurelyInseparable k k'],
      IsReduced (k' ⊗[k] S)) :
    IsGeometricallyReduced k S := by
  sorry
/-
  sorry

/-! ## Elementary permanence properties -/

/-- Geometric reducedness descends to every `k`-subalgebra. -/
theorem isGeometricallyReduced_subalgebra
    {k : Type u} {S : Type v} [Field k] [CommRing S] [Algebra k S]
    (hS : IsGeometricallyReduced k S) :
    ∀ A : Subalgebra k S, IsGeometricallyReduced k A := by
  intro A K _ _
  let _ : IsReduced (K ⊗[k] S) := hS K
  exact isReduced_of_injective (Algebra.TensorProduct.map 1 A.val)
    (Module.Flat.lTensor_preserves_injective_linearMap A.val.toLinearMap Subtype.val_injective)

/-- If every finite-type `k`-subalgebra is geometrically reduced, then so is
the ambient algebra. -/
theorem isGeometricallyReduced_of_finiteType_subalgebras
    {k : Type u} {S : Type v} [Field k] [CommRing S] [Algebra k S]
    (hS : ∀ A : Subalgebra k S, Algebra.FiniteType k A →
      IsGeometricallyReduced k A) :
    IsGeometricallyReduced k S := by
  intro K _ _
  apply IsReduced.tensorProduct_of_flat_of_forall_fg
  intro B hB
  exact (hS B ((Subalgebra.fg_iff_finiteType B).mp hB)) K

/-- A directed colimit of geometrically reduced `k`-algebras is geometrically
reduced. -/
theorem isGeometricallyReduced_directLimit
    {k : Type u} [Field k] {ι : Type v} [Preorder ι] [Nonempty ι]
    [IsDirectedOrder ι] {A : ι → Type w} [∀ i, CommRing (A i)]
    [∀ i, Algebra k (A i)]
    (f : ∀ i j, i ≤ j → A i →ₐ[k] A j)
    [DirectedSystem A (f · · ·)]
    (hA : ∀ i, IsGeometricallyReduced k (A i)) :
    IsGeometricallyReduced k (DirectLimit A f) := by
  classical
  intro K _ _
  let fL : ∀ i j, i ≤ j → A i →ₗ[k] A j := fun i j h => (f i j h).toLinearMap
  let _ : DirectedSystem A (fL · · ·) := {
    map_self := fun {i} x => by
      simpa [fL] using ((inferInstance : DirectedSystem A (fun i j h => f i j h)).map_self x)
    map_map := fun {k j i} hij hjk x => by
      simpa [fL] using ((inferInstance : DirectedSystem A (fun i j h => f i j h)).map_map hij hjk x) }
  let ea : Module.DirectLimit A fL ≃ₗ[k] DirectLimit A f :=
    Module.DirectLimit.linearEquiv (R := k) (ι := ι) (G := A) fL
  let e := TensorProduct.directLimitRight fL K
  let et := TensorProduct.congr (LinearEquiv.refl k K) ea
  let F := e.symm.trans et
  let φ : ∀ i, (K ⊗[k] A i) →ₐ[K] (K ⊗[k] DirectLimit A f) :=
    fun i => Algebra.TensorProduct.map 1 (DirectLimit.Algebra.of A f i)
  have hφ : ∀ i y,
      F.symm (φ i y) = Module.DirectLimit.of k ι (fun i => K ⊗[k] A i)
        (fun i j h => LinearMap.lTensor K (fL i j h)) i y := by
    intro i y
    refine y.induction_on ?_ ?_ ?_
    · simp [F, et, e, φ]
    · intro a b
      have hbe : ea.symm (DirectLimit.Algebra.of A f i b) =
          Module.DirectLimit.of k ι A fL i b := by
        rfl
      change e (a ⊗ₜ[k] ea.symm (DirectLimit.Algebra.of A f i b)) = _
      rw [hbe]
      simp [e]
    · intro x y hx hy
      rw [map_add, map_add, hx, hy, map_add]
  have hφf : ∀ i j (hij : i ≤ j) (y : K ⊗[k] A i),
      φ j (Algebra.TensorProduct.map (AlgHom.id K K) (f i j hij) y) = φ i y := by
    intro i j hij y
    refine y.induction_on ?_ ?_ ?_
    · simp [φ]
    · intro a b
      simp [φ]
    · intro x y hx hy
      rw [map_add, map_add, hx, hy]
      exact (map_add (φ i) x y).symm
  have hrep : ∀ x : K ⊗[k] DirectLimit A f, ∃ i y, φ i y = x := by
    intro x
    refine x.induction_on ?_ ?_ ?_
    · let i := Classical.arbitrary ι
      exact ⟨i, 0, by simp [φ]⟩
    · intro a b
      obtain ⟨i, b, hb⟩ := DirectLimit.exists_eq_mk f b
      refine ⟨i, a ⊗ₜ[k] b, ?_⟩
      simp [φ, hb]
    · rintro x y ⟨i, xi, hxi⟩ ⟨j, yj, hyj⟩
      obtain ⟨l, hil, hjl⟩ := exists_ge_ge i j
      refine ⟨l,
        Algebra.TensorProduct.map (AlgHom.id K K) (f i l hil) xi +
          Algebra.TensorProduct.map (AlgHom.id K K) (f j l hjl) yj, ?_⟩
      rw [map_add, hφf, hφf, hxi, hyj]
  constructor
  intro x hx
  obtain ⟨i, y, rfl⟩ := hrep x
  obtain ⟨n, hn⟩ := hx
  have hzero : φ i (y ^ n) = 0 := by
    rw [map_pow]
    exact hn
  have hdlzero := congrArg F.symm hzero
  rw [hφ i (y ^ n)] at hdlzero
  obtain ⟨j, hij, hjy⟩ := Module.DirectLimit.of.zero_exact hdlzero
  let _ : IsReduced (K ⊗[k] A j) := hA j K
  let g : (K ⊗[k] A i) →ₐ[K] (K ⊗[k] A j) :=
    Algebra.TensorProduct.map (AlgHom.id K K) (f i j hij)
  have hpow : (g y) ^ n = 0 := by
    rw [← map_pow]
    exact hjy
  have hyj : g y = 0 := IsReduced.eq_zero _ ⟨n, hpow⟩
  rw [← hφf i j hij y, hyj, map_zero]

/-- Localizing a geometrically reduced algebra preserves geometric
reducedness. -/
theorem isGeometricallyReduced_localization
    {k : Type u} {R : Type v} [Field k] [CommRing R] [Algebra k R]
    (hR : IsGeometricallyReduced k R) (M : Submonoid R) :
    IsGeometricallyReduced k (Localization M) := by
  intro K _ _
  let _ : IsReduced (K ⊗[k] R) := hR K
  let M' : Submonoid (K ⊗[k] R) :=
    M.map (Algebra.TensorProduct.includeRight (R := k) (A := K))
  let _ : IsReduced (Localization M') := inferInstance
  let e : (K ⊗[k] Localization M) ≃ₐ[K] Localization M' :=
    IsLocalization.tensorProductEquivOfMapIncludeRight k K M (Localization M)
      (Localization M')
  exact isReduced_of_injective e.toAlgHom e.injective

/-- Polynomial extension of a geometrically reduced algebra is geometrically
reduced. -/
theorem isGeometricallyReduced_polynomial
    {k : Type u} {R : Type v} [Field k] [CommRing R] [Algebra k R]
    (hR : IsGeometricallyReduced k R) :
    IsGeometricallyReduced k (Polynomial R) := by
  intro K _ _
  let _ : IsReduced (K ⊗[k] R) := hR K
  let e₁ : K ⊗[k] Polynomial R ≃ₐ[K] K ⊗[k] MvPolynomial Unit R :=
    Algebra.TensorProduct.congr (AlgEquiv.refl : K ≃ₐ[K] K)
      ((MvPolynomial.uniqueAlgEquiv R Unit).symm.restrictScalars k)
  let e₂ : K ⊗[k] MvPolynomial Unit R ≃ₐ[K]
      MvPolynomial Unit (K ⊗[k] R) :=
    MvPolynomial.rTensorAlgEquiv
  let e₃ : MvPolynomial Unit (K ⊗[k] R) ≃ₐ[K] Polynomial (K ⊗[k] R) :=
    (MvPolynomial.uniqueAlgEquiv (K ⊗[k] R) Unit).restrictScalars K
  let _ : IsReduced (Polynomial (K ⊗[k] R)) := by
    constructor
    intro p hp
    have hp' := (Polynomial.isNilpotent_iff).mp hp
    exact Polynomial.ext fun n => IsReduced.eq_zero _ (hp' n)
  let e := e₁.trans (e₂.trans e₃)
  exact isReduced_of_injective e.toAlgHom e.injective

/- The localization item in the source's elementary list is represented by
   `isGeometricallyReduced_localization`, whose explicit `Submonoid` argument
   is also the source-faithful form of the first clause of the permanence
   lemma; `isGeometricallyReduced_polynomial` records its second clause. -/

/- The source's observation immediately before the limit argument is made
   explicit using the canonical tensor-product map. -/

/-- The tensor-product map induced by inclusions of two `k`-subalgebras. -/
def subalgebraTensorProductMap
    {k : Type u} {R : Type v} {S : Type w}
    [CommRing k] [CommRing R] [CommRing S]
    [Algebra k R] [Algebra k S]
    (R' : Subalgebra k R) (S' : Subalgebra k S) :
    (R' ⊗[k] S') →ₐ[k] (R ⊗[k] S) :=
  Algebra.TensorProduct.map R'.val S'.val

/-- Tensoring inclusions of algebras over a field is injective. -/
theorem subalgebraTensorProductMap_injective
    {k : Type u} {R : Type v} {S : Type w}
    [Field k] [CommRing R] [CommRing S]
    [Algebra k R] [Algebra k S]
    (R' : Subalgebra k R) (S' : Subalgebra k S) :
    Function.Injective (subalgebraTensorProductMap R' S') := by
  exact TensorProduct.map_injective_of_flat_flat
    R'.val.toLinearMap S'.val.toLinearMap Subtype.val_injective Subtype.val_injective

/-! ## Finite subalgebra reduction -/

/-- A nonreduced tensor product is already nonreduced after replacing each
factor by a finite-type subalgebra. -/
theorem exists_finiteType_subalgebras_of_not_isReduced_tensorProduct
    {k : Type u} {R : Type v} {S : Type w}
    [Field k] [CommRing R] [CommRing S]
    [Algebra k R] [Algebra k S]
    (h : ¬ IsReduced (R ⊗[k] S)) :
    ∃ (R' : Subalgebra k R) (S' : Subalgebra k S),
      Algebra.FiniteType k R' ∧ Algebra.FiniteType k S' ∧
        ¬ IsReduced (R' ⊗[k] S') := by
  classical
  obtain ⟨x, hxne, hxnil⟩ := exists_isNilpotent_of_not_isReduced h
  obtain ⟨n, a, b, hab⟩ := TensorProduct.exists_sum_tmul_eq x
  let R' : Subalgebra k R :=
    Algebra.adjoin k (↑(Finset.univ.image a) : Set R)
  let S' : Subalgebra k S :=
    Algebra.adjoin k (↑(Finset.univ.image b) : Set S)
  have hR' : Algebra.FiniteType k R' := by
    apply (Subalgebra.fg_iff_finiteType R').mp
    exact Subalgebra.fg_adjoin_finset _
  have hS' : Algebra.FiniteType k S' := by
    apply (Subalgebra.fg_iff_finiteType S').mp
    exact Subalgebra.fg_adjoin_finset _
  let y : R' ⊗[k] S' :=
    ∑ j, (⟨a j, Algebra.subset_adjoin (by simp)⟩ ⊗ₜ[k]
      ⟨b j, Algebra.subset_adjoin (by simp)⟩)
  have hy : subalgebraTensorProductMap R' S' y = x := by
    simp only [y, map_sum, subalgebraTensorProductMap,
      Algebra.TensorProduct.map_tmul]
    exact hab.symm
  have hmap : Function.Injective (subalgebraTensorProductMap R' S') :=
    subalgebraTensorProductMap_injective R' S'
  refine ⟨R', S', hR', hS', ?_⟩
  intro hred
  have hyne : y ≠ 0 := by
    intro hyzero
    apply hxne
    rw [← hy, hyzero, map_zero]
  have hynil : IsNilpotent y := by
    apply (IsNilpotent.map_iff hmap).mp
    rw [hy]
    exact hxnil
  exact hyne (hred.eq_zero y hynil)

/-- A nonzero zero divisor in a tensor product is already present in a tensor
product of finite-type subalgebras. -/
theorem exists_finiteType_subalgebras_of_nonzero_zeroDivisor_tensorProduct
    {k : Type u} {R : Type v} {S : Type w}
    [Field k] [CommRing R] [CommRing S]
    [Algebra k R] [Algebra k S]
    (h : ∃ x : R ⊗[k] S,
      x ≠ 0 ∧ x ∉ nonZeroDivisors (R ⊗[k] S)) :
    ∃ (R' : Subalgebra k R) (S' : Subalgebra k S),
        Algebra.FiniteType k R' ∧ Algebra.FiniteType k S' ∧
        ∃ x : R' ⊗[k] S',
          x ≠ 0 ∧ x ∉ nonZeroDivisors (R' ⊗[k] S') := by
  classical
  obtain ⟨x, hxne, hxzd⟩ := h
  obtain ⟨z, hxz, hzne⟩ : ∃ z : R ⊗[k] S, x * z = 0 ∧ z ≠ 0 := by
    rcases notMem_nonZeroDivisors_iff.mp hxzd with hz | hz
    · rcases hz with ⟨z, hxz, hzne⟩
      exact ⟨z, hxz, hzne⟩
    · rcases hz with ⟨z, hzx, hzne⟩
      exact ⟨z, by simpa [mul_comm] using hzx, hzne⟩
  obtain ⟨n, a, b, hab⟩ := TensorProduct.exists_sum_tmul_eq x
  obtain ⟨m, c, d, hcd⟩ := TensorProduct.exists_sum_tmul_eq z
  let rset : Finset R := Finset.univ.image a ∪ Finset.univ.image c
  let sset : Finset S := Finset.univ.image b ∪ Finset.univ.image d
  let R' : Subalgebra k R := Algebra.adjoin k (↑rset : Set R)
  let S' : Subalgebra k S := Algebra.adjoin k (↑sset : Set S)
  have hR' : Algebra.FiniteType k R' := by
    apply (Subalgebra.fg_iff_finiteType R').mp
    exact Subalgebra.fg_adjoin_finset _
  have hS' : Algebra.FiniteType k S' := by
    apply (Subalgebra.fg_iff_finiteType S').mp
    exact Subalgebra.fg_adjoin_finset _
  let y : R' ⊗[k] S' :=
    ∑ j, (⟨a j, Algebra.subset_adjoin (by simp [rset])⟩ ⊗ₜ[k]
      ⟨b j, Algebra.subset_adjoin (by simp [sset])⟩)
  let w : R' ⊗[k] S' :=
    ∑ j, (⟨c j, Algebra.subset_adjoin (by simp [rset])⟩ ⊗ₜ[k]
      ⟨d j, Algebra.subset_adjoin (by simp [sset])⟩)
  have hy : subalgebraTensorProductMap R' S' y = x := by
    simp only [y, map_sum, subalgebraTensorProductMap,
      Algebra.TensorProduct.map_tmul]
    exact hab.symm
  have hw : subalgebraTensorProductMap R' S' w = z := by
    simp only [w, map_sum, subalgebraTensorProductMap,
      Algebra.TensorProduct.map_tmul]
    exact hcd.symm
  have hmap : Function.Injective (subalgebraTensorProductMap R' S') :=
    subalgebraTensorProductMap_injective R' S'
  have hyne : y ≠ 0 := by
    intro hyzero
    apply hxne
    rw [← hy, hyzero, map_zero]
  have hwne : w ≠ 0 := by
    intro hwzero
    apply hzne
    rw [← hw, hwzero, map_zero]
  have hyw : y * w = 0 := by
    apply hmap
    rw [map_mul, hy, hw, hxz, map_zero]
  refine ⟨R', S', hR', hS', y, hyne, ?_⟩
  rw [notMem_nonZeroDivisors_iff_left]
  exact ⟨w, hyw, hwne⟩

/-- A nontrivial idempotent in a tensor product is already present in a tensor
product of finite-type subalgebras. -/
theorem exists_finiteType_subalgebras_of_nontrivial_idempotent_tensorProduct
    {k : Type u} {R : Type v} {S : Type w}
    [Field k] [CommRing R] [CommRing S]
    [Algebra k R] [Algebra k S]
    (h : ∃ e : R ⊗[k] S,
      IsIdempotentElem e ∧ e ≠ 0 ∧ e ≠ 1) :
    ∃ (R' : Subalgebra k R) (S' : Subalgebra k S),
      Algebra.FiniteType k R' ∧ Algebra.FiniteType k S' ∧
        ∃ e : R' ⊗[k] S',
          IsIdempotentElem e ∧ e ≠ 0 ∧ e ≠ 1 := by
  classical
  obtain ⟨e, he, hene, he1⟩ := h
  obtain ⟨n, a, b, hab⟩ := TensorProduct.exists_sum_tmul_eq e
  let R' : Subalgebra k R :=
    Algebra.adjoin k (↑(Finset.univ.image a) : Set R)
  let S' : Subalgebra k S :=
    Algebra.adjoin k (↑(Finset.univ.image b) : Set S)
  have hR' : Algebra.FiniteType k R' := by
    apply (Subalgebra.fg_iff_finiteType R').mp
    exact Subalgebra.fg_adjoin_finset _
  have hS' : Algebra.FiniteType k S' := by
    apply (Subalgebra.fg_iff_finiteType S').mp
    exact Subalgebra.fg_adjoin_finset _
  let y : R' ⊗[k] S' :=
    ∑ j, (⟨a j, Algebra.subset_adjoin (by simp)⟩ ⊗ₜ[k]
      ⟨b j, Algebra.subset_adjoin (by simp)⟩)
  have hy : subalgebraTensorProductMap R' S' y = e := by
    simp only [y, map_sum, subalgebraTensorProductMap,
      Algebra.TensorProduct.map_tmul]
    exact hab.symm
  have hmap : Function.Injective (subalgebraTensorProductMap R' S') :=
    subalgebraTensorProductMap_injective R' S'
  have hyid : IsIdempotentElem y := by
    change y * y = y
    apply hmap
    rw [map_mul, hy, he]
  have hyne : y ≠ 0 := by
    intro hyzero
    apply hene
    rw [← hy, hyzero, map_zero]
  have hy1 : y ≠ 1 := by
    intro hyone
    apply he1
    rw [← hy, hyone, map_one]
  exact ⟨R', S', hR', hS', y, hyid, hyne, hy1⟩

private theorem tensorProduct_piRightHom_injective
    {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]
    {ι : Type w} {M : ι → Type*} [∀ i, AddCommMonoid (M i)]
    [∀ i, Module k (M i)] :
    Function.Injective (TensorProduct.piRightHom k K K M) := by
  classical
  let b := Module.Free.chooseBasis k K
  have hcoord : ∀ (x : K ⊗[k] (∀ i, M i))
      (i : Module.Free.ChooseBasisIndex k K) (j : ι),
      (TensorProduct.equivFinsuppOfBasisLeft b x i) j =
        (TensorProduct.equivFinsuppOfBasisLeft b
          (TensorProduct.piRightHom k K K M x j) i) := by
    intro x
    refine x.induction_on ?_ ?_ ?_
    · simp
    · intro a f i j
      simp [TensorProduct.piRightHom_tmul]
    · intro x y hx hy i j
      simp [hx, hy]
  intro x y hxy
  apply (TensorProduct.equivFinsuppOfBasisLeft b).injective
  ext i j
  rw [hcoord x i j, congrArg (fun z =>
    (TensorProduct.equivFinsuppOfBasisLeft b z i)) (congrFun hxy j)]
  exact (hcoord y i j).symm

/-! ## Reduced base change -/

/-- Base change by a reduced `k`-algebra preserves reducedness when the other
factor is geometrically reduced. -/
theorem isReduced_tensorProduct_of_isReduced_of_isGeometricallyReduced
    {k : Type u} {R : Type v} {S : Type w}
    [Field k] [CommRing R] [CommRing S]
    [Algebra k R] [Algebra k S]
    (hR : IsReduced R) (hS : IsGeometricallyReduced k S) :
    IsReduced (R ⊗[k] S) := by
  classical
  by_contra hnot
  obtain ⟨R', S', hR', hS', hnot'⟩ :=
    exists_finiteType_subalgebras_of_not_isReduced_tensorProduct hnot
  let _ : Algebra.FiniteType k R' := hR'
  let _ : IsReduced R' := isReduced_of_injective R'.val Subtype.val_injective
  let _ : Small.{u} R' := Algebra.FiniteType.small (R := k) (S := R')
  have hS'geom : IsGeometricallyReduced k S' :=
    (isGeometricallyReduced_subalgebra hS) S'
  have hNoeth : IsNoetherianRing R' :=
    Algebra.FiniteType.isNoetherianRing k R'
  let _ : IsNoetherianRing R' := hNoeth
  have hminfin : (minimalPrimes R').Finite :=
    minimalPrimes.finite_of_isNoetherianRing R'
  let _ : Finite (minimalPrimes R') := hminfin.to_subtype
  let _ : Finite (Formalization.Books.Algebra.Unit25.MinimalPrimeSpectrum R') :=
    Finite.of_injective
      (fun p : Formalization.Books.Algebra.Unit25.MinimalPrimeSpectrum R' =>
        (⟨p.1.asIdeal, p.2⟩ : minimalPrimes R'))
      (by
        intro p q hpq
        apply Subtype.ext
        apply PrimeSpectrum.ext
        exact congrArg Subtype.val hpq)
  let _ : Fintype (Formalization.Books.Algebra.Unit25.MinimalPrimeSpectrum R') :=
    Fintype.ofFinite _
  let _ : ∀ p : Formalization.Books.Algebra.Unit25.MinimalPrimeSpectrum R',
      IsField (Localization.AtPrime p.1.asIdeal) :=
    fun p => Unit25.isField_localizationAt_minimalPrime_of_isReduced p
  let f : R' →ₐ[k]
      (∀ p : Formalization.Books.Algebra.Unit25.MinimalPrimeSpectrum R',
        Localization.AtPrime p.1.asIdeal) :=
    { toRingHom := Unit25.mapToMinimalPrimeLocalizations
      commutes' := by
        intro c
        ext p
        rfl }
  have hf : Function.Injective f :=
    by simpa [f] using (Unit25.mapToMinimalPrimeLocalizations_injective
      (R := R'))
  have hlocal : ∀ p : Formalization.Books.Algebra.Unit25.MinimalPrimeSpectrum R',
      IsReduced (S' ⊗[k] Localization.AtPrime p.1.asIdeal) := by
    intro p
    let L := Localization.AtPrime p.1.asIdeal
    let hfield : IsField L :=
      Unit25.isField_localizationAt_minimalPrime_of_isReduced p
    let _ : Field L := hfield.toField
    let _ : Small.{u} L := small_of_surjective Localization.mkHom_surjective
    let eL : Shrink L ≃ L := (equivShrink L).symm
    let _ : Field (Shrink L) := eL.field
    let ae : Shrink L ≃ₐ[k] L := Shrink.algEquiv k L
    let _ : IsReduced (Shrink L ⊗[k] S') := hS'geom (Shrink L)
    let m : (L ⊗[k] S') →ₐ[k] (Shrink L ⊗[k] S') :=
      Algebra.TensorProduct.map ae.symm (AlgHom.id k S')
    have hm : Function.Injective m := by
      exact TensorProduct.map_injective_of_flat_flat ae.symm.toLinearMap
        (LinearMap.id) ae.symm.injective Function.injective_id
    have hLS : IsReduced (L ⊗[k] S') := isReduced_of_injective m hm
    exact isReduced_of_injective
      (Algebra.TensorProduct.comm k S' L)
      (Algebra.TensorProduct.comm k S' L).injective
  let g : (R' ⊗[k] S') →+*
      (∀ p : Formalization.Books.Algebra.Unit25.MinimalPrimeSpectrum R',
        S' ⊗[k] Localization.AtPrime p.1.asIdeal) :=
    ((Algebra.TensorProduct.piRight k S' S'
      (fun p : Formalization.Books.Algebra.Unit25.MinimalPrimeSpectrum R' =>
        Localization.AtPrime p.1.asIdeal)).toRingEquiv.toRingHom.comp
      (Algebra.TensorProduct.comm k
        (∀ p : Formalization.Books.Algebra.Unit25.MinimalPrimeSpectrum R',
          Localization.AtPrime p.1.asIdeal) S').toRingEquiv.toRingHom).comp
      (Algebra.TensorProduct.map f (AlgHom.id k S')).toRingHom
  have hmap : Function.Injective (Algebra.TensorProduct.map f (AlgHom.id k S')) :=
    TensorProduct.map_injective_of_flat_flat f.toLinearMap (LinearMap.id)
      hf Function.injective_id
  have hg : Function.Injective g := by
    intro x y hxy
    apply hmap
    apply (Algebra.TensorProduct.comm k
      (∀ p : Formalization.Books.Algebra.Unit25.MinimalPrimeSpectrum R',
        Localization.AtPrime p.1.asIdeal) S').injective
    apply (Algebra.TensorProduct.piRight k S' S'
      (fun p : Formalization.Books.Algebra.Unit25.MinimalPrimeSpectrum R' =>
        Localization.AtPrime p.1.asIdeal)).injective
    simpa [g] using hxy
  have hred : IsReduced (R' ⊗[k] S') := isReduced_of_injective g hg
  exact hnot' hred

private theorem isGeometricallyReduced_intermediateField_of_algebraicIndependent
    {k : Type u} {F : Type w} {ι : Type z} [Field k] [Field F] [Algebra k F]
    (x : ι → F) (hx : AlgebraicIndependent k x) :
    IsGeometricallyReduced k (IntermediateField.adjoin k (Set.range x)) := by
  have hmv : IsGeometricallyReduced k (MvPolynomial ι k) := by
    intro L _ _
    let _ : IsReduced (L ⊗[k] k) :=
      isReduced_of_injective (Algebra.TensorProduct.rid k L L)
        (Algebra.TensorProduct.rid k L L).injective
    let e : L ⊗[k] MvPolynomial ι k ≃ₐ[L]
        MvPolynomial ι (L ⊗[k] k) := MvPolynomial.rTensorAlgEquiv
    exact isReduced_of_injective e.toAlgHom e.injective
  have hfr : IsGeometricallyReduced k (FractionRing (MvPolynomial ι k)) :=
    isGeometricallyReduced_localization hmv (nonZeroDivisors _)
  intro L _ _
  let _ : IsReduced (L ⊗[k] FractionRing (MvPolynomial ι k)) := hfr L
  let e := Algebra.TensorProduct.map (AlgHom.id L L)
    hx.aevalEquivField.symm.toAlgHom
  have he : Function.Injective e :=
    TensorProduct.map_injective_of_flat_flat (LinearMap.id)
      hx.aevalEquivField.symm.toLinearMap Function.injective_id
      hx.aevalEquivField.symm.injective
  exact isReduced_of_injective e he

private theorem isGeometricallyReduced_of_finiteType_separablyGenerated
    {k : Type u} {F : Type w} [Field k] [Field F] [Algebra k F]
    [Algebra.EssFiniteType k F]
    (hF : Formalization.Books.Algebra.Unit42.IsSeparablyGenerated k F) :
    IsGeometricallyReduced k F := by
  obtain ⟨r, x, y, htr, hx, hgen, hysep⟩ :=
    Formalization.Books.Algebra.Unit42.exists_finite_generators_of_separably_generated hF
  let A : IntermediateField k F := IntermediateField.adjoin k (Set.range x)
  let _ : CommSemiring A := SubsemiringClass.toCommSemiring A
  have hA : IsGeometricallyReduced k A :=
    isGeometricallyReduced_intermediateField_of_algebraicIndependent x hx.1
  have hgenA : IntermediateField.adjoin A ({y} : Set F) = ⊤ := by
    apply (IntermediateField.restrictScalars_eq_top_iff (K := k)).mp
    rw [IntermediateField.restrictScalars_adjoin_eq_sup]
    rw [← IntermediateField.adjoin_union]
    exact hgen
  have hsepA : Algebra.IsSeparable A F := by
    rw [← IntermediateField.isSeparable_top]
    rw [← hgenA]
    refine (IntermediateField.isSeparable_adjoin_iff_isSeparable A F).2 ?_
    intro z hz
    rw [Set.mem_singleton_iff.mp hz]
    exact hysep
  let _ : Module A F :=
    @Algebra.toModule A F _ _ (inferInstance : Algebra A F)
  have hFgeom : IsGeometricallyReduced A F := by
    intro E _ _
    let _ : Algebra.IsSeparable A F := hsepA
    let _ : Algebra.EssFiniteType A F := Algebra.EssFiniteType.of_comp k A F
    let _ : Algebra.FormallyUnramified A F :=
      Algebra.FormallyUnramified.of_isSeparable A F
    let _ : Algebra.FormallyUnramified E (E ⊗[A] F) := inferInstance
    let _ : Algebra.EssFiniteType E (E ⊗[A] F) := inferInstance
    exact Algebra.FormallyUnramified.isReduced_of_field E (E ⊗[A] F)
  intro L _ _
  let _ : Algebra A (L ⊗[k] A) := Algebra.TensorProduct.rightAlgebra
  let _ : Module A (L ⊗[k] A) :=
    @Algebra.toModule A (L ⊗[k] A) _ _ Algebra.TensorProduct.rightAlgebra
  let _ : IsScalarTower A (L ⊗[k] A) (L ⊗[k] A) := inferInstance
  let _ : SMulCommClass A (L ⊗[k] A) (L ⊗[k] A) := inferInstance
  let _ : IsReduced (L ⊗[k] A) := hA L
  let _ : Algebra A (A ⊗[k] L) := Algebra.TensorProduct.leftAlgebra
  let _ : Module A (A ⊗[k] L) :=
    @Algebra.toModule A (A ⊗[k] L) _ _ Algebra.TensorProduct.leftAlgebra
  have hbase :=
    isReduced_tensorProduct_of_isReduced_of_isGeometricallyReduced
      (k := A) (R := L ⊗[k] A) (S := F) (hA L) hFgeom
  let e₁ : ((L ⊗[k] A) ⊗[A] F) ≃ₐ[A]
      F ⊗[A] (L ⊗[k] A) := Algebra.TensorProduct.comm A (L ⊗[k] A) F
  let e₂ : (F ⊗[A] (L ⊗[k] A)) ≃ₐ[A]
      F ⊗[A] (A ⊗[k] L) :=
    Algebra.TensorProduct.congr (AlgEquiv.refl : F ≃ₐ[A] F)
      (Algebra.TensorProduct.commRight k A L).symm
  let e₃ : (F ⊗[A] (A ⊗[k] L)) ≃ₐ[F] F ⊗[k] L :=
    Algebra.TensorProduct.cancelBaseChange k A F F L
  let e₄ : (F ⊗[k] L) ≃ₐ[k] L ⊗[k] F := Algebra.TensorProduct.comm k F L
  let e : ((L ⊗[k] A) ⊗[A] F) ≃+* (L ⊗[k] F) :=
    e₁.toRingEquiv.trans (e₂.toRingEquiv.trans (e₃.toRingEquiv.trans e₄.toRingEquiv))
  let _ : IsReduced ((L ⊗[k] A) ⊗[A] F) := hbase
  exact isReduced_of_injective e.symm e.symm.injective

private theorem isGeometricallyReduced_of_isSeparableExtension
    {k : Type u} {K : Type w} [Field k] [Field K] [Algebra k K]
    (hK : Formalization.Books.Algebra.Unit42.IsSeparableExtension k K) :
    IsGeometricallyReduced k K := by
  apply isGeometricallyReduced_of_finiteType_subalgebras
  intro B hB
  obtain ⟨s, hs⟩ := (Subalgebra.fg_iff_finiteType B).mpr hB
  let L : IntermediateField k K := IntermediateField.adjoin k (s : Set K)
  have hL : Algebra.EssFiniteType k L :=
    (IntermediateField.essFiniteType_iff).2
      (IntermediateField.fg_adjoin_finset s)
  have hBmem : ∀ b : B, (b : K) ∈ L := by
    intro b
    have hb : (b : K) ∈ Algebra.adjoin k (s : Set K) := by
      rw [hs]
      exact b.property
    change (b : K) ∈ IntermediateField.adjoin k (s : Set K)
    exact (IntermediateField.algebra_adjoin_le_adjoin k (s : Set K)) hb
  let f : B →ₐ[k] L :=
    { toFun := fun b => ⟨(b : K), hBmem b⟩
      map_one' := by ext; simp
      map_mul' := by intro x y; ext; simp
      map_zero' := by ext; simp
      map_add' := by intro x y; ext; simp
      commutes' := by intro c; ext; simp }
  have hf : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    simpa [f] using congrArg Subtype.val hxy
  have hBgeom : IsGeometricallyReduced k B := by
    intro E _ _
    let _ : IsReduced (E ⊗[k] L) :=
      isGeometricallyReduced_of_finiteType_separablyGenerated
        (hK L hL) E
    have hfmap : Function.Injective (Algebra.TensorProduct.map (AlgHom.id k E) f) :=
      TensorProduct.map_injective_of_flat_flat (LinearMap.id) f.toLinearMap
        Function.injective_id hf
    exact isReduced_of_injective _ hfmap
  exact hBgeom

private theorem isGeometricallyReduced_of_isSeparablyGenerated
    {k : Type u} {K : Type w} [Field k] [Field K] [Algebra k K]
    (hK : Formalization.Books.Algebra.Unit42.IsSeparablyGenerated k K) :
    IsGeometricallyReduced k K := by
  rcases hK with ⟨ι, x, hx, hsep⟩
  let A : IntermediateField k K := IntermediateField.adjoin k (Set.range x)
  let _ : CommSemiring A := SubsemiringClass.toCommSemiring A
  have hAgeom : IsGeometricallyReduced k A :=
    isGeometricallyReduced_intermediateField_of_algebraicIndependent x hx.1
  let _ : Algebra.IsSeparable A K := by simpa [A] using hsep
  apply isGeometricallyReduced_of_finiteType_subalgebras
  intro B hB
  obtain ⟨s, hs⟩ := (Subalgebra.fg_iff_finiteType B).mpr hB
  let M : IntermediateField A K := IntermediateField.adjoin A (s : Set K)
  let M₀ : IntermediateField k K := M.restrictScalars k
  have hMfinite : Algebra.EssFiniteType A M :=
    (IntermediateField.essFiniteType_iff).2
      (IntermediateField.fg_adjoin_finset s)
  have hMsep : Algebra.IsSeparable A M := by
    refine (IntermediateField.isSeparable_adjoin_iff_isSeparable A K).2 ?_
    intro z hz
    exact Algebra.IsSeparable.isSeparable A z
  have hMgeomA : IsGeometricallyReduced A M := by
    intro E _ _
    let _ : Algebra.IsSeparable A M := hMsep
    let _ : Algebra.EssFiniteType A M := hMfinite
    let _ : Algebra.FormallyUnramified A M :=
      Algebra.FormallyUnramified.of_isSeparable A M
    let _ : Algebra.FormallyUnramified E (E ⊗[A] M) := inferInstance
    let _ : Algebra.EssFiniteType E (E ⊗[A] M) := inferInstance
    exact Algebra.FormallyUnramified.isReduced_of_field E (E ⊗[A] M)
  have hMgeom : IsGeometricallyReduced k M₀ := by
    intro E _ _
    let _ : IsReduced (E ⊗[k] A) := hAgeom E
    let _ : Algebra A (E ⊗[k] A) := Algebra.TensorProduct.rightAlgebra
    let _ : Module A (E ⊗[k] A) :=
      @Algebra.toModule A (E ⊗[k] A) _ _ Algebra.TensorProduct.rightAlgebra
    let _ : IsScalarTower A (E ⊗[k] A) (E ⊗[k] A) := inferInstance
    let _ : SMulCommClass A (E ⊗[k] A) (E ⊗[k] A) := inferInstance
    have hbase :=
      isReduced_tensorProduct_of_isReduced_of_isGeometricallyReduced
        (k := A) (R := E ⊗[k] A) (S := M) (hAgeom E) hMgeomA
    let _ : Algebra A (A ⊗[k] E) := Algebra.TensorProduct.leftAlgebra
    let _ : Module A (A ⊗[k] E) :=
      @Algebra.toModule A (A ⊗[k] E) _ _ Algebra.TensorProduct.leftAlgebra
    let e₁ : ((E ⊗[k] A) ⊗[A] M) ≃ₐ[A]
        M ⊗[A] (E ⊗[k] A) := Algebra.TensorProduct.comm A (E ⊗[k] A) M
    let e₂ : (M ⊗[A] (E ⊗[k] A)) ≃ₐ[A]
        M ⊗[A] (A ⊗[k] E) :=
      Algebra.TensorProduct.congr (AlgEquiv.refl : M ≃ₐ[A] M)
        (Algebra.TensorProduct.commRight k A E).symm
    let e₃ : (M ⊗[A] (A ⊗[k] E)) ≃ₐ[M] M ⊗[k] E :=
      Algebra.TensorProduct.cancelBaseChange k A M M E
    let e₄ : (M ⊗[k] E) ≃ₐ[k] E ⊗[k] M :=
      Algebra.TensorProduct.comm k M E
    let e : ((E ⊗[k] A) ⊗[A] M) ≃+* (E ⊗[k] M₀) :=
      e₁.toRingEquiv.trans (e₂.toRingEquiv.trans
        (e₃.toRingEquiv.trans e₄.toRingEquiv))
    let _ : IsReduced ((E ⊗[k] A) ⊗[A] M) := hbase
    exact isReduced_of_injective e.symm e.symm.injective
  have hBmem : ∀ b : B, (b : K) ∈ M₀ := by
    intro b
    have hb : (b : K) ∈ Algebra.adjoin k (s : Set K) := by
      rw [hs]
      exact b.property
    have hle : IntermediateField.adjoin k (s : Set K) ≤ M₀ := by
      apply IntermediateField.adjoin_le_iff.mpr
      intro z hz
      exact IntermediateField.subset_adjoin A (s : Set K) hz
    apply hle
    exact (IntermediateField.algebra_adjoin_le_adjoin k (s : Set K)) hb
  let f : B →ₐ[k] M₀ :=
    { toFun := fun b => ⟨(b : K), hBmem b⟩
      map_one' := by ext; simp
      map_mul' := by intro x y; ext; simp
      map_zero' := by ext; simp
      map_add' := by intro x y; ext; simp
      commutes' := by intro c; ext; simp }
  have hf : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    simpa [f] using congrArg Subtype.val hxy
  have hBgeom : IsGeometricallyReduced k B := by
    intro E _ _
    let _ : IsReduced (E ⊗[k] M₀) := hMgeom E
    have hfmap : Function.Injective (Algebra.TensorProduct.map (AlgHom.id k E) f) :=
      TensorProduct.map_injective_of_flat_flat (LinearMap.id) f.toLinearMap
        Function.injective_id hf
    exact isReduced_of_injective _ hfmap
  exact hBgeom

/-- A separable or separably generated field extension preserves reducedness
after tensoring a reduced algebra. -/
theorem isReduced_tensorProduct_of_separable_extension
    {k : Type u} {S : Type v} {K : Type w} [Field k] [CommRing S] [Field K]
    [Algebra k S] [Algebra k K]
    (hS : IsReduced S)
    (hK : Formalization.Books.Algebra.Unit42.IsSeparableExtension k K ∨
      Formalization.Books.Algebra.Unit42.IsSeparablyGenerated k K) :
    IsReduced (K ⊗[k] S) := by
  rcases hK with hK | hK
  · have hgeomK : IsGeometricallyReduced k K :=
      isGeometricallyReduced_of_isSeparableExtension hK
    let e := Algebra.TensorProduct.comm k S K
    let _ : IsReduced (S ⊗[k] K) :=
      isReduced_tensorProduct_of_isReduced_of_isGeometricallyReduced
        (k := k) (R := S) (S := K) hS hgeomK
    exact isReduced_of_injective e.symm e.symm.injective
  · have hgeomK : IsGeometricallyReduced k K :=
      isGeometricallyReduced_of_isSeparablyGenerated hK
    let e := Algebra.TensorProduct.comm k S K
    let _ : IsReduced (S ⊗[k] K) :=
      isReduced_tensorProduct_of_isReduced_of_isGeometricallyReduced
        (k := k) (R := S) (S := K) hS hgeomK
    exact isReduced_of_injective e.symm e.symm.injective

/-- The minimal-prime criterion for geometric reducedness. -/
theorem isGeometricallyReduced_of_minimalPrime_localizations
    {k : Type u} {S : Type v} [Field k] [CommRing S] [Algebra k S]
    (hS : IsReduced S)
    (hmin : ∀ p : Formalization.Books.Algebra.Unit25.MinimalPrimeSpectrum S,
      IsGeometricallyReduced k (Localization.AtPrime p.1.asIdeal)) :
    IsGeometricallyReduced k S := by
  classical
  intro K _ _
  let f : S →ₐ[k]
      (∀ p : Formalization.Books.Algebra.Unit25.MinimalPrimeSpectrum S,
        Localization.AtPrime p.1.asIdeal) :=
    { toRingHom := Unit25.mapToMinimalPrimeLocalizations
      commutes' := by
        intro c
        ext p
        rfl }
  have hf : Function.Injective f := by
    simpa [f] using (Unit25.mapToMinimalPrimeLocalizations_injective (R := S))
  let _ : ∀ p : Formalization.Books.Algebra.Unit25.MinimalPrimeSpectrum S,
      IsReduced (K ⊗[k] Localization.AtPrime p.1.asIdeal) :=
    fun p => hmin p K
  let m : (K ⊗[k] S) →ₐ[k]
      (K ⊗[k] (∀ p : Formalization.Books.Algebra.Unit25.MinimalPrimeSpectrum S,
        Localization.AtPrime p.1.asIdeal)) :=
    Algebra.TensorProduct.map (AlgHom.id k K) f
  have hm : Function.Injective m :=
    TensorProduct.map_injective_of_flat_flat (LinearMap.id) f.toLinearMap
      Function.injective_id hf
  let g : (K ⊗[k] S) →+*
      (∀ p : Formalization.Books.Algebra.Unit25.MinimalPrimeSpectrum S,
        K ⊗[k] Localization.AtPrime p.1.asIdeal) :=
    (Algebra.TensorProduct.piRightHom k K K
      (fun p : Formalization.Books.Algebra.Unit25.MinimalPrimeSpectrum S =>
        Localization.AtPrime p.1.asIdeal)).toRingHom.comp m.toRingHom
  have hpi : Function.Injective (TensorProduct.piRightHom k K K
      (fun p : Formalization.Books.Algebra.Unit25.MinimalPrimeSpectrum S =>
        Localization.AtPrime p.1.asIdeal)) :=
    tensorProduct_piRightHom_injective
  have hg : Function.Injective g := by
    intro x y hxy
    apply hm
    apply hpi
    change (TensorProduct.piRightHom k K K
      (fun p : Formalization.Books.Algebra.Unit25.MinimalPrimeSpectrum S =>
        Localization.AtPrime p.1.asIdeal) (m x)) =
      TensorProduct.piRightHom k K K
        (fun p : Formalization.Books.Algebra.Unit25.MinimalPrimeSpectrum S =>
          Localization.AtPrime p.1.asIdeal) (m y) at hxy
    exact hxy
  exact isReduced_of_injective g hg

/-! ## The separable-algebraic diagonal -/

/- The multiplication map in the source's diagonal argument is Mathlib's
   tensor-product product map for the two identity maps of `k'`. -/
/-- The canonical multiplication map `k' ⊗[k] k' →ₐ[k] k'`. -/
noncomputable def tensorProductMultiplication
    {k : Type u} {k' : Type v} [Field k] [Field k'] [Algebra k k'] :
    (k' ⊗[k] k') →ₐ[k] k' :=
  Algebra.TensorProduct.productMap (AlgHom.id k k') (AlgHom.id k k')

private theorem exists_tensorProductMultiplication_localization_of_finite
    {k : Type u} {L : Type v} [Field k] [Field L] [Algebra k L]
    [FiniteDimensional k L] [Algebra.IsSeparable k L] :
    ∃ M : Submonoid (L ⊗[k] L),
      letI : Algebra (L ⊗[k] L) L :=
        (Algebra.TensorProduct.productMap (AlgHom.id k L) (AlgHom.id k L)).toAlgebra
      IsLocalization M L := by
  let f : (L ⊗[k] L) →ₐ[k] L :=
    Algebra.TensorProduct.productMap (AlgHom.id k L) (AlgHom.id k L)
  let _ : Algebra (L ⊗[k] L) L := f.toAlgebra
  have hmul : f = (Algebra.TensorProduct.lmul' k : (L ⊗[k] L) →ₐ[k] L) := by
    change Algebra.TensorProduct.productMap (AlgHom.id k L) (AlgHom.id k L) = _
    rw [Algebra.TensorProduct.productMap_eq_comp_map]
    simp
  have hf : Function.Surjective f := by
    intro x
    refine ⟨1 ⊗ₜ[k] x, ?_⟩
    simp [f]
  let _ : IsScalarTower k (L ⊗[k] L) L :=
    IsScalarTower.of_algebraMap_eq' (by
      simp only [RingHom.algebraMap_toAlgebra]
      rw [hmul]
      simp)
  let _ : Algebra.FormallyUnramified k L :=
    Algebra.FormallyUnramified.of_isSeparable k L
  let _ : Algebra.EssFiniteType k L := inferInstance
  have hI : IsIdempotentElem (KaehlerDifferential.ideal k L) :=
    (Ideal.cotangent_subsingleton_iff _).mp
      (inferInstanceAs (Subsingleton Ω[L⁄k]))
  obtain ⟨e, he, hker⟩ :=
    (Ideal.isIdempotentElem_iff_of_fg _ (KaehlerDifferential.ideal_fg _ _)).mp hI
  have hker' : RingHom.ker (algebraMap (L ⊗[k] L) L) = Ideal.span {1 - (1 - e)} := by
    rw [show RingHom.ker (algebraMap (L ⊗[k] L) L) =
        KaehlerDifferential.ideal k L by rfl, hker]
    simp
  have hsurj : Function.Surjective (algebraMap (L ⊗[k] L) L) := by
    rw [show algebraMap (L ⊗[k] L) L = f.toRingHom by
      simp [RingHom.algebraMap_toAlgebra]]
    exact hf
  refine ⟨Submonoid.powers (1 - e), ?_⟩
  exact IsLocalization.away_of_isIdempotentElem he.one_sub hker' hsurj

/-- For a separable algebraic extension, the multiplication map from the
diagonal tensor product is a localization map. -/
theorem exists_tensorProductMultiplication_localization
    {k : Type u} {k' : Type v} [Field k] [Field k'] [Algebra k k']
    [Algebra.IsAlgebraic k k'] [Algebra.IsSeparable k k'] :
    ∃ M : Submonoid (k' ⊗[k] k'),
      letI : Algebra (k' ⊗[k] k') k' :=
        (tensorProductMultiplication (k := k) (k' := k')).toAlgebra
      IsLocalization M k' := by
  let f : (k' ⊗[k] k') →ₐ[k] k' :=
    tensorProductMultiplication (k := k) (k' := k')
  let _ : Algebra (k' ⊗[k] k') k' := f.toAlgebra
  let M : Submonoid (k' ⊗[k] k') := (IsUnit.submonoid k').comap f.toRingHom
  refine ⟨M, ?_⟩
  refine ⟨⟨?_, ?_, ?_⟩⟩
  · intro s
    exact s.2
  · intro z
    refine ⟨((1 : k') ⊗ₜ[k] z, ⟨1, by simp [M]⟩), ?_⟩
    simp only [map_one]
    rw [show algebraMap (k' ⊗[k] k') k' = f.toRingHom by
      simp [RingHom.algebraMap_toAlgebra]]
    simp [f, tensorProductMultiplication]
  · intro x y hxy
    have hxyf : f x = f y := by
      simpa [RingHom.algebraMap_toAlgebra] using hxy
    obtain ⟨r, a, b, hx⟩ := TensorProduct.exists_sum_tmul_eq x
    obtain ⟨s, c, d, hy⟩ := TensorProduct.exists_sum_tmul_eq y
    let X : Set k' := Set.range a ∪ Set.range b ∪ Set.range c ∪ Set.range d
    let _ : Finite X := by
      dsimp [X]
      infer_instance
    let L : IntermediateField k k' := IntermediateField.adjoin k X
    let _ : FiniteDimensional k L := by
      dsimp [L]
      exact IntermediateField.finiteDimensional_adjoin
        (fun z _ => Algebra.IsIntegral.isIntegral z)
    let iL : L →ₐ[k] k' :=
      { toFun := fun z => z.1
        map_one' := rfl
        map_mul' := by intro z w; rfl
        map_zero' := rfl
        map_add' := by intro z w; rfl
        commutes' := by intro z; rfl }
    have hiL : Function.Injective iL := by
      intro z w h
      exact Subtype.ext h
    let _ : Algebra.IsSeparable k L := Algebra.IsSeparable.of_algHom k k' iL
    have haL : ∀ j : Fin r, a j ∈ L := by
      intro j
      change a j ∈ IntermediateField.adjoin k X
      exact IntermediateField.subset_adjoin k X (by simp [X])
    have hbL : ∀ j : Fin r, b j ∈ L := by
      intro j
      change b j ∈ IntermediateField.adjoin k X
      exact IntermediateField.subset_adjoin k X (by simp [X])
    have hcL : ∀ j : Fin s, c j ∈ L := by
      intro j
      change c j ∈ IntermediateField.adjoin k X
      exact IntermediateField.subset_adjoin k X (by simp [X])
    have hdL : ∀ j : Fin s, d j ∈ L := by
      intro j
      change d j ∈ IntermediateField.adjoin k X
      exact IntermediateField.subset_adjoin k X (by simp [X])
    let aL : Fin r → L := fun j => ⟨a j, haL j⟩
    let bL : Fin r → L := fun j => ⟨b j, hbL j⟩
    let cL : Fin s → L := fun j => ⟨c j, hcL j⟩
    let dL : Fin s → L := fun j => ⟨d j, hdL j⟩
    let xL : L ⊗[k] L := ∑ j, aL j ⊗ₜ[k] bL j
    let yL : L ⊗[k] L := ∑ j, cL j ⊗ₜ[k] dL j
    let φ : (L ⊗[k] L) →ₐ[k] (k' ⊗[k] k') :=
      Algebra.TensorProduct.map iL iL
    let g : (L ⊗[k] L) →ₐ[k] L :=
      Algebra.TensorProduct.productMap (AlgHom.id k L) (AlgHom.id k L)
    obtain ⟨N, hN⟩ :=
      exists_tensorProductMultiplication_localization_of_finite (k := k) (L := L)
    let _ : Algebra (L ⊗[k] L) L := g.toAlgebra
    let _ : IsLocalization N L := hN
    have hxmap : φ xL = x := by
      dsimp [xL]
      rw [hx]
      simp [φ, aL, bL, iL]
    have hymap : φ yL = y := by
      dsimp [yL]
      rw [hy]
      simp [φ, cL, dL, iL]
    have hcomp : f.comp φ = iL.comp g := by
      apply AlgHom.ext
      intro z
      refine TensorProduct.induction_on z ?_ ?_ ?_
      · simp
      swap
      · intro z w hz hw
        simp only [map_add]
        rw [hz, hw]
      · intro z w
        simp [f, g, φ, iL, tensorProductMultiplication]
    have hxyL : g xL = g yL := by
      apply hiL
      calc
        iL (g xL) = f (φ xL) := by
          exact congrArg (fun q => q xL) hcomp |>.symm
        _ = f x := by rw [hxmap]
        _ = f y := hxyf
        _ = f (φ yL) := by rw [hymap]
        _ = iL (g yL) := by
          exact congrArg (fun q => q yL) hcomp
    obtain ⟨m, hm⟩ := (IsLocalization.eq_iff_exists N L).mp hxyL
    have hmUnit : IsUnit (g (m : L ⊗[k] L)) := by
      simpa [g, RingHom.algebraMap_toAlgebra] using IsLocalization.map_units L m
    have hmMem : φ (m : L ⊗[k] L) ∈ M := by
      change IsUnit (f (φ (m : L ⊗[k] L)))
      have hcompm : f (φ (m : L ⊗[k] L)) = iL (g (m : L ⊗[k] L)) := by
        simpa only [AlgHom.comp_apply] using
          congrArg (fun q => q (m : L ⊗[k] L)) hcomp
      rw [hcompm]
      exact IsUnit.map iL hmUnit
    refine ⟨⟨φ (m : L ⊗[k] L), hmMem⟩, ?_⟩
    change φ (m : L ⊗[k] L) * x = φ (m : L ⊗[k] L) * y
    rw [← hxmap, ← hymap]
    simpa [φ] using congrArg (fun z => φ z) hm

private theorem isSeparablyGenerated_of_separable_algebraic
    {k : Type u} {k' : Type v} [Field k] [Field k'] [Algebra k k']
    [Algebra.IsAlgebraic k k'] [Algebra.IsSeparable k k'] :
    Formalization.Books.Algebra.Unit42.IsSeparablyGenerated k k' := by
  let x : {i : k' // False} → k' := fun i => nomatch i.2
  have htr : IsTranscendenceBasis k x := by
    rw [isTranscendenceBasis_iff_algebraicIndependent_isAlgebraic]
    constructor
    · exact algebraicIndependent_empty_type
    · have hbot : Algebra.IsAlgebraic (⊥ : Subalgebra k k') k' :=
        (Subalgebra.algebra_isAlgebraic_bot_left_iff
          (FaithfulSMul.algebraMap_injective k k')).2
          (inferInstance : Algebra.IsAlgebraic k k')
      rw [Set.range_eq_empty x, Algebra.adjoin_empty]
      exact hbot
  have hsepbot : Algebra.IsSeparable (⊥ : IntermediateField k k') k' := by
    apply Algebra.IsSeparable.of_equiv_equiv
      (e₁ := (IntermediateField.botEquiv k k').symm.toRingEquiv)
      (e₂ := RingEquiv.refl k')
    ext z
    rfl
  refine ⟨{i : k' // False}, x, htr, ?_⟩
  rw [Set.range_eq_empty x, IntermediateField.adjoin_empty]
  exact hsepbot

private theorem isReduced_tensorProduct_of_isReduced_of_separable_algebraic_base_change
    {k : Type u} {k' : Type v} {A : Type w} {K : Type z}
    [Field k] [Field k'] [CommRing A] [Field K]
    [Algebra k k'] [Algebra k' A] [Algebra k A]
    [Algebra k' K] [Algebra k K]
    [IsScalarTower k k' A] [IsScalarTower k k' K]
    [Algebra.IsAlgebraic k k'] [Algebra.IsSeparable k k']
    (hS : IsReduced (K ⊗[k] A)) : IsReduced (K ⊗[k'] A) := by
  let D : Type _ := k' ⊗[k] k'
  let S₀ : Type _ := K ⊗[k] A
  let T : Type _ := K ⊗[k'] A
  let f : D →ₐ[k] k' := tensorProductMultiplication (k := k) (k' := k')
  let _ : Algebra D k' := f.toAlgebra
  obtain ⟨M, hM⟩ := exists_tensorProductMultiplication_localization (k := k) (k' := k')
  let hM' : IsLocalization M k' := by simpa [D, f] using hM
  let dS : D →ₐ[k] S₀ :=
    Algebra.TensorProduct.map (IsScalarTower.toAlgHom k k' K)
      (IsScalarTower.toAlgHom k k' A)
  let _ : Algebra D S₀ := dS.toAlgebra
  let _ : IsScalarTower k k' T :=
    IsScalarTower.of_algebraMap_eq' (R := k) (S := k') (A := T) (by
      ext x
      simp [← IsScalarTower.algebraMap_apply])
  let iK : K →ₐ[k] T :=
    (Algebra.TensorProduct.includeLeft : K →ₐ[k'] T).restrictScalars k
  let iA : A →ₐ[k] T :=
    (Algebra.TensorProduct.includeRight : A →ₐ[k'] T).restrictScalars k
  let q : S₀ →ₐ[k] T :=
    Algebra.TensorProduct.lift iK iA (by
      intro x y
      simp [iK, iA]
      exact mul_comm _ _)
  let dT : D →ₐ[k] T := (IsScalarTower.toAlgHom k k' T).comp f
  let _ : Algebra D T := dT.toAlgebra
  have hqd : ∀ x : D, q (dS x) = dT x := by
    intro x
    refine TensorProduct.induction_on x ?_ ?_ ?_
    · simp [q, dS, dT, f]
    swap
    · intro x y hx hy
      simp only [map_add]
      rw [hx, hy]
    · intro x y
      dsimp [q, dS, dT, f]
      rw [Algebra.TensorProduct.map_tmul]
      rw [Algebra.TensorProduct.lift_tmul]
      change iK ((algebraMap k' K) x) * iA ((algebraMap k' A) y) =
        (algebraMap k' T) (x * y)
      calc
        iK ((algebraMap k' K) x) * iA ((algebraMap k' A) y) =
          (algebraMap k' T) x * (algebraMap k' T) y := by
          congr 1
          change 1 ⊗ₜ[k'] (algebraMap k' A) y =
            (algebraMap k' K) y ⊗ₜ[k'] 1
          exact (Algebra.TensorProduct.tmul_one_eq_one_tmul y).symm
        _ = (algebraMap k' T) (x * y) := by rw [map_mul]
  let _ : IsLocalization M k' := hM'
  have hX : IsLocalization (Algebra.algebraMapSubmonoid S₀ M)
      (S₀ ⊗[D] k') := inferInstance
  let X : Type _ := S₀ ⊗[D] k'
  let _ : Algebra S₀ X := Algebra.TensorProduct.leftAlgebra
  let _ : Algebra k' X := Algebra.TensorProduct.rightAlgebra
  let s0X : S₀ →ₐ[k] X :=
    (Algebra.TensorProduct.includeLeft : S₀ →ₐ[D] X).restrictScalars k
  let jK0 : K →ₐ[k] X :=
    s0X.comp (Algebra.TensorProduct.includeLeft : K →ₐ[k] S₀)
  let jA0 : A →ₐ[k] X :=
    s0X.comp (Algebra.TensorProduct.includeRight : A →ₐ[k] S₀)
  let jK : K →ₐ[k'] X :=
    { jK0.toRingHom with
      commutes' := by
        intro r
        change (((algebraMap k' K) r) ⊗ₜ[k] (1 : A)) ⊗ₜ[D] (1 : k') =
          (1 : S₀) ⊗ₜ[D] r
        have hr :=
          Algebra.TensorProduct.tmul_one_eq_one_tmul
            (R := D) (A := S₀) (B := k')
            (Algebra.TensorProduct.includeLeft (R := k) (S := k')
              (A := k') (B := k') r)
        change dS (Algebra.TensorProduct.includeLeft (R := k) (S := k')
            (A := k') (B := k') r) ⊗ₜ[D] (1 : k') =
          (1 : S₀) ⊗ₜ[D] f (Algebra.TensorProduct.includeLeft (R := k)
            (S := k') (A := k') (B := k') r) at hr
        dsimp [dS, f] at hr
        rw [Algebra.TensorProduct.map_tmul] at hr
        simp [tensorProductMultiplication] at hr
        rw [Algebra.TensorProduct.productMap_left_apply] at hr
        simpa [RingHom.algebraMap_toAlgebra] using hr }
  let jA : A →ₐ[k'] X :=
    { jA0.toRingHom with
      commutes' := by
        intro r
        change ((1 : K) ⊗ₜ[k] ((algebraMap k' A) r)) ⊗ₜ[D] (1 : k') =
          (1 : S₀) ⊗ₜ[D] r
        have hr :=
          Algebra.TensorProduct.tmul_one_eq_one_tmul
            (R := D) (A := S₀) (B := k')
            (Algebra.TensorProduct.includeRight (R := k) (A := k') (B := k') r)
        change dS (Algebra.TensorProduct.includeRight (R := k)
            (A := k') (B := k') r) ⊗ₜ[D] (1 : k') =
          (1 : S₀) ⊗ₜ[D] f (Algebra.TensorProduct.includeRight (R := k)
            (A := k') (B := k') r) at hr
        dsimp [dS, f] at hr
        rw [Algebra.TensorProduct.map_tmul] at hr
        simp [tensorProductMultiplication] at hr
        rw [Algebra.TensorProduct.productMap_right_apply] at hr
        change ((1 : K) ⊗ₜ[k] ((algebraMap k' A) r)) ⊗ₜ[D] (1 : k') =
          (1 : S₀) ⊗ₜ[D] r at hr
        exact hr }
  let _ : IsScalarTower D k' T :=
    IsScalarTower.of_algebraMap_eq' (R := D) (S := k') (A := T) (by
      change dT.toRingHom = (algebraMap k' T).comp f.toRingHom
      rfl)
  let gD : k' →ₐ[D] T := IsScalarTower.toAlgHom D k' T
  let qD : S₀ →ₐ[D] T :=
    { q.toRingHom with
      commutes' := by
        intro x
        simpa [RingHom.algebraMap_toAlgebra] using hqd x }
  let e : X →ₐ[D] T :=
    Algebra.TensorProduct.lift qD gD (by
      intro x y
      exact Commute.all _ _)
  let p : T →ₐ[k'] X :=
    Algebra.TensorProduct.lift jK jA (by
      intro x y
      exact Commute.all _ _)
  have hpq : p.toRingHom.comp q.toRingHom = s0X.toRingHom := by
    apply RingHom.ext
    intro z
    refine TensorProduct.induction_on z ?_ ?_ ?_
    · simp
    swap
    · intro x y hx hy
      simp only [map_add]
      rw [hx, hy]
    · intro x y
      change p (iK x * iA y) = s0X (x ⊗ₜ[k] y)
      rw [map_mul]
      change p (x ⊗ₜ[k'] (1 : A)) * p ((1 : K) ⊗ₜ[k'] y) =
        s0X (x ⊗ₜ[k] y)
      rw [Algebra.TensorProduct.lift_tmul, Algebra.TensorProduct.lift_tmul]
      simp [jK, jA, jK0, jA0, s0X]
      rw [Algebra.TensorProduct.tmul_mul_tmul]
      rw [Algebra.TensorProduct.tmul_mul_tmul]
      rw [Algebra.TensorProduct.tmul_mul_tmul]
      simp only [mul_one, one_mul]
      rw [show Algebra.TensorProduct.includeLeft x =
        x ⊗ₜ[k] (1 : A) by rfl]
      rw [show Algebra.TensorProduct.includeRight y =
        (1 : K) ⊗ₜ[k] y by rfl]
      rw [Algebra.TensorProduct.tmul_mul_tmul]
      simp
  let _ : IsReduced S₀ := by simpa [S₀] using hS
  have hXred : IsReduced X := by
    constructor
    rintro x ⟨_ | n, e₀⟩
    · simpa using congr_arg (· * x) e₀
    obtain ⟨⟨y, m⟩, hx⟩ :=
      IsLocalization.surj (Algebra.algebraMapSubmonoid S₀ M) x
    dsimp only at hx
    let hx' := congr_arg (· ^ n.succ) hx
    simp only [mul_pow, e₀, zero_mul, ← map_pow] at hx'
    rw [← (algebraMap S₀ X).map_zero] at hx'
    obtain ⟨m', hm'⟩ :=
      (IsLocalization.eq_iff_exists (Algebra.algebraMapSubmonoid S₀ M) X).mp hx'
    apply_fun (· * (m' : S₀) ^ n) at hm'
    simp only [mul_assoc, zero_mul, mul_zero] at hm'
    rw [← mul_left_comm, ← pow_succ', ← mul_pow] at hm'
    replace hm' := IsNilpotent.eq_zero ⟨_, hm'.symm⟩
    rw [← (IsLocalization.map_units X m).mul_left_inj, hx, zero_mul,
      IsLocalization.map_eq_zero_iff (Algebra.algebraMapSubmonoid S₀ M)]
    exact ⟨m', by rw [← hm', mul_comm]⟩
  let _ : IsReduced X := hXred
  have hes : ∀ z : S₀, e (s0X z) = q z := by
    intro z
    change ((Algebra.TensorProduct.lift qD gD
      (by intro x y; exact Commute.all _ _)).comp
      (Algebra.TensorProduct.includeLeft : S₀ →ₐ[D] X)) z = qD z
    exact congrArg (fun F => F z)
      (Algebra.TensorProduct.lift_comp_includeLeft qD gD
        (by intro x y; exact Commute.all _ _))
  have hejK : ∀ x : K, e (jK x) = iK x := by
    intro x
    change e (s0X ((Algebra.TensorProduct.includeLeft : K →ₐ[k] S₀) x)) = iK x
    rw [hes]
    change ((Algebra.TensorProduct.lift iK iA
      (by intro x y; exact Commute.all _ _)).comp
      (Algebra.TensorProduct.includeLeft : K →ₐ[k] S₀)) x = iK x
    exact congrArg (fun F => F x)
      (Algebra.TensorProduct.lift_comp_includeLeft iK iA
        (by intro x y; exact Commute.all _ _))
  have hejA : ∀ y : A, e (jA y) = iA y := by
    intro y
    change e (s0X ((Algebra.TensorProduct.includeRight : A →ₐ[k] S₀) y)) = iA y
    rw [hes]
    change (((Algebra.TensorProduct.lift iK iA
      (by intro x y; exact Commute.all _ _)).restrictScalars k).comp
      (Algebra.TensorProduct.includeRight : A →ₐ[k] S₀)) y = iA y
    exact congrArg (fun F => F y)
      (Algebra.TensorProduct.lift_comp_includeRight iK iA
        (by intro x y; exact Commute.all _ _))
  have hep : e.toRingHom.comp p.toRingHom = RingHom.id T := by
    apply RingHom.ext
    intro z
    refine TensorProduct.induction_on z ?_ ?_ ?_
    · simp [e, p]
    swap
    · intro x y hx hy
      simp only [map_add]
      rw [hx, hy]
    · intro x y
      change e (p (x ⊗ₜ[k'] y)) = x ⊗ₜ[k'] y
      rw [Algebra.TensorProduct.lift_tmul]
      rw [map_mul, hejK x, hejA y]
      change (x ⊗ₜ[k'] (1 : A)) * ((1 : K) ⊗ₜ[k'] y) = x ⊗ₜ[k'] y
      rw [Algebra.TensorProduct.tmul_mul_tmul]
      simp
  have hp : Function.Injective p := by
    intro x y hxy
    have h := congrArg (fun z => e z) hxy
    change (e.toRingHom.comp p.toRingHom) x =
      (e.toRingHom.comp p.toRingHom) y at h
    rw [hep] at h
    exact h
  exact isReduced_of_injective p hp

/-! ## Changing a separable algebraic base field -/

/-- Geometric reducedness is unchanged on replacing the base field by a
separable algebraic extension. -/
theorem isGeometricallyReduced_iff_of_separable_algebraic
    {k : Type u} {k' : Type v} {A : Type w} [Field k] [Field k'] [CommRing A]
    [Algebra k k'] [Algebra k' A] [Algebra k A]
    [IsScalarTower k k' A]
    [Algebra.IsAlgebraic k k'] [Algebra.IsSeparable k k'] :
    IsGeometricallyReduced k A ↔ IsGeometricallyReduced k' A := by
  constructor
  · intro hA K _ _
    let _ : Algebra k K :=
      ((algebraMap k' K).comp (algebraMap k k')).toAlgebra
    let _ : IsScalarTower k k' K :=
      IsScalarTower.of_algebraMap_eq' (by rfl)
    have hS : IsReduced (K ⊗[k] A) :=
      isReduced_tensorProduct_of_isReduced_of_isGeometricallyReduced
        (k := k) (R := K) (S := A) inferInstance hA
    exact isReduced_tensorProduct_of_isReduced_of_separable_algebraic_base_change
      (k := k) (k' := k') (A := A) (K := K) hS
  · intro hA K _ _
    let hKsep' : IsReduced (k' ⊗[k] K) :=
      isReduced_tensorProduct_of_separable_extension
        (k := k) (S := K) (K := k') (inferInstance : IsReduced K)
        (Or.inr (isSeparablyGenerated_of_separable_algebraic (k := k) (k' := k')))
    let _ : IsReduced (k' ⊗[k] K) := hKsep'
    let hKsep : IsReduced (K ⊗[k] k') :=
      isReduced_of_injective (Algebra.TensorProduct.comm k k' K).symm
        (Algebra.TensorProduct.comm k k' K).symm.injective
    let _ : Algebra k' (K ⊗[k] k') := Algebra.TensorProduct.rightAlgebra
    let _ : Module k' (K ⊗[k] k') :=
      @Algebra.toModule k' (K ⊗[k] k') _ _ Algebra.TensorProduct.rightAlgebra
    let _ : IsScalarTower k' (K ⊗[k] k') (K ⊗[k] k') := inferInstance
    let _ : SMulCommClass k' (K ⊗[k] k') (K ⊗[k] k') := inferInstance
    let _ : IsReduced (K ⊗[k] k') := hKsep
    have hbase :=
      isReduced_tensorProduct_of_isReduced_of_isGeometricallyReduced
        (k := k') (R := K ⊗[k] k') (S := A) hKsep hA
    let e₁ : ((K ⊗[k] k') ⊗[k'] A) ≃ₐ[k']
        A ⊗[k'] (K ⊗[k] k') :=
      Algebra.TensorProduct.comm k' (K ⊗[k] k') A
    let e₂ : (A ⊗[k'] (K ⊗[k] k')) ≃ₐ[k']
        A ⊗[k'] (k' ⊗[k] K) :=
      Algebra.TensorProduct.congr (AlgEquiv.refl : A ≃ₐ[k'] A)
        (Algebra.TensorProduct.commRight k k' K).symm
    let e₃ : (A ⊗[k'] (k' ⊗[k] K)) ≃ₐ[A]
        A ⊗[k] K :=
      Algebra.TensorProduct.cancelBaseChange k k' A A K
    let e₄ : (A ⊗[k] K) ≃ₐ[k] K ⊗[k] A :=
      Algebra.TensorProduct.comm k A K
    let e : ((K ⊗[k] k') ⊗[k'] A) ≃+* (K ⊗[k] A) :=
      e₁.toRingEquiv.trans (e₂.toRingEquiv.trans
        (e₃.toRingEquiv.trans e₄.toRingEquiv))
    let _ : IsReduced ((K ⊗[k] k') ⊗[k'] A) := hbase
    exact isReduced_of_injective e.symm e.symm.injective

private theorem test_finitePurelyInseparable_baseChanges
    {k : Type u} {S : Type v} [Field k] [CommRing S] [Algebra k S]
    (hS : IsReduced S)
    (h : ∀ (k' : Type u) [Field k'] [Algebra k k']
      [FiniteDimensional k k'] [IsPurelyInseparable k k'],
      IsReduced (k' ⊗[k] S)) :
    IsGeometricallyReduced k S := by
  classical
  intro K _ _
  by_contra hnot
  obtain ⟨R', S', hR', hS', hnot'⟩ :=
    exists_finiteType_subalgebras_of_not_isReduced_tensorProduct hnot
  let _ : Algebra.FiniteType k R' := hR'
  let _ : Algebra.FiniteType k S' := hS'
  let _ : IsReduced R' := isReduced_of_injective R'.val Subtype.val_injective
  letI : CommRing R' := Subalgebra.toCommRing R'
  letI : IsDomain R' := by
    have hK : IsDomain K := inferInstance
    have hinj : Function.Injective (R'.val.toRingHom : R' →+* K) :=
      Subtype.val_injective
    exact Function.Injective.isDomain R'.val.toRingHom hinj
  let L := FractionRing R'
  let _ : Algebra.EssFiniteType k L :=
    Algebra.EssFiniteType.of_isLocalization (nonZeroDivisors R')
  obtain ⟨D⟩ := Formalization.Books.Algebra.Unit42.exists_purely_inseparable_base_change
    (k := k) (K := L)
  let _ : Field D.base := D.baseField
  let _ : Field D.top := D.topField
  let _ : Algebra k D.base := D.baseAlgebra
  let _ : Algebra k D.top := D.topAlgebra
  let _ : Algebra L D.top := D.topOverK
  let _ : Algebra D.base D.top := D.topOverBase
  let _ : IsScalarTower k D.base D.top := D.baseTower
  let _ : IsScalarTower k L D.top := D.topTower
  let _ : FiniteDimensional k D.base := D.baseFinite
  let _ : IsPurelyInseparable k D.base := D.basePurelyInseparable
  let _ : FiniteDimensional L D.top := D.topFinite
  let _ : IsPurelyInseparable L D.top := D.topPurelyInseparable
  let _ : Algebra D.base (D.base ⊗[k] S') :=
    Algebra.TensorProduct.leftAlgebra
  let _ : Module D.base (D.base ⊗[k] S') :=
    @Algebra.toModule D.base (D.base ⊗[k] S') _ _ Algebra.TensorProduct.leftAlgebra
  let q : (D.base ⊗[k] S') →ₐ[k] (D.base ⊗[k] S) :=
    Algebra.TensorProduct.map (AlgHom.id k D.base) S'.val
  have hq : Function.Injective q :=
    TensorProduct.map_injective_of_flat_flat (LinearMap.id) S'.val.toLinearMap
      Function.injective_id Subtype.val_injective
  let _ : IsReduced (D.base ⊗[k] S) := h D.base
  have hbase : IsReduced (D.base ⊗[k] S') := isReduced_of_injective q hq
  have htop₀ : IsReduced (D.top ⊗[D.base] (D.base ⊗[k] S')) :=
    isReduced_tensorProduct_of_separable_extension
      (k := D.base) (S := D.base ⊗[k] S') (K := D.top) hbase
      (Or.inr D.topSeparablyGenerated)
  let e₁ : (D.top ⊗[D.base] (D.base ⊗[k] S')) ≃ₐ[D.top]
      D.top ⊗[k] S' :=
    Algebra.TensorProduct.cancelBaseChange k D.base D.top D.top S'
  let _ : IsReduced (D.top ⊗[D.base] (D.base ⊗[k] S')) := htop₀
  have htop : IsReduced (D.top ⊗[k] S') :=
    isReduced_of_injective e₁.symm.toRingEquiv.toRingHom e₁.symm.injective
  let m : (L ⊗[k] S') →ₐ[k] (D.top ⊗[k] S') :=
    Algebra.TensorProduct.map (IsScalarTower.toAlgHom k L D.top) (AlgHom.id k S')
  have hm : Function.Injective m :=
    TensorProduct.map_injective_of_flat_flat
      (IsScalarTower.toAlgHom k L D.top).toLinearMap (LinearMap.id)
      (IsScalarTower.toAlgHom k L D.top).injective Function.injective_id
  let _ : IsReduced (D.top ⊗[k] S') := htop
  have hL : IsReduced (L ⊗[k] S') := isReduced_of_injective m hm
  let _ : IsScalarTower k R' L := IsScalarTower.of_algebraMap_eq' (by
    ext x
    simp [← IsScalarTower.algebraMap_apply])
  let n : (R' ⊗[k] S') →ₐ[k] (L ⊗[k] S') :=
    Algebra.TensorProduct.map (IsScalarTower.toAlgHom k R' L) (AlgHom.id k S')
  have hn : Function.Injective n :=
    TensorProduct.map_injective_of_flat_flat
      (IsScalarTower.toAlgHom k R' L).toLinearMap (LinearMap.id)
      (IsScalarTower.toAlgHom k R' L).injective Function.injective_id
  have hRS : IsReduced (R' ⊗[k] S') := isReduced_of_injective n hn
  exact hnot' hRS
-/

end

end Formalization.Books.Algebra.Unit43
