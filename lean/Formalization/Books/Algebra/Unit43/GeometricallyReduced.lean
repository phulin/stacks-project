import Formalization.Books.Algebra.Unit25.ZerodivisorsAndTotalRingsOfFractions
import Formalization.Books.Algebra.Unit42.SeparableExtensions
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.Algebra.Colimit.DirectLimit
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.FieldTheory.Separable
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.TensorProduct.DirectLimit
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Commutative Algebra, Chapter 43: Geometrically reduced algebras

The source predicate is expressed by quantifying over field extensions and using
Mathlib's canonical `IsReduced`, tensor product, subalgebra, localization, and
finite-type APIs.
-/

namespace Formalization.Books.Algebra.Unit43

open scoped TensorProduct

universe u v w

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

/-! ## Reduced base change -/

/-- Base change by a reduced `k`-algebra preserves reducedness when the other
factor is geometrically reduced. -/
theorem isReduced_tensorProduct_of_isReduced_of_isGeometricallyReduced
    {k : Type u} {R : Type v} {S : Type w}
    [Field k] [CommRing R] [CommRing S]
    [Algebra k R] [Algebra k S]
    (hR : IsReduced R) (hS : IsGeometricallyReduced k S) :
    IsReduced (R ⊗[k] S) := by
  sorry

/-- A separable or separably generated field extension preserves reducedness
after tensoring a reduced algebra. -/
theorem isReduced_tensorProduct_of_separable_extension
    {k : Type u} {S : Type v} {K : Type w} [Field k] [CommRing S] [Field K]
    [Algebra k S] [Algebra k K]
    (hS : IsReduced S)
    (hK : Formalization.Books.Algebra.Unit42.IsSeparableExtension k K ∨
      Formalization.Books.Algebra.Unit42.IsSeparablyGenerated k K) :
    IsReduced (K ⊗[k] S) := by
  sorry

/-- The minimal-prime criterion for geometric reducedness. -/
theorem isGeometricallyReduced_of_minimalPrime_localizations
    {k : Type u} {S : Type v} [Field k] [CommRing S] [Algebra k S]
    (hS : IsReduced S)
    (hmin : ∀ p : Formalization.Books.Algebra.Unit25.MinimalPrimeSpectrum S,
      IsGeometricallyReduced k (Localization.AtPrime p.1.asIdeal)) :
    IsGeometricallyReduced k S := by
  sorry

/-! ## The separable-algebraic diagonal -/

/- The multiplication map in the source's diagonal argument is Mathlib's
   tensor-product product map for the two identity maps of `k'`. -/
/-- The canonical multiplication map `k' ⊗[k] k' →ₐ[k] k'`. -/
noncomputable def tensorProductMultiplication
    {k : Type u} {k' : Type v} [Field k] [Field k'] [Algebra k k'] :
    (k' ⊗[k] k') →ₐ[k] k' :=
  Algebra.TensorProduct.productMap (AlgHom.id k k') (AlgHom.id k k')

/-- For a separable algebraic extension, the multiplication map from the
diagonal tensor product is a localization map. -/
theorem exists_tensorProductMultiplication_localization
    {k : Type u} {k' : Type v} [Field k] [Field k'] [Algebra k k']
    [Algebra.IsAlgebraic k k'] [Algebra.IsSeparable k k'] :
    ∃ M : Submonoid (k' ⊗[k] k'),
      letI : Algebra (k' ⊗[k] k') k' :=
        (tensorProductMultiplication (k := k) (k' := k')).toAlgebra
      IsLocalization M k' := by
  sorry

/-! ## Changing a separable algebraic base field -/

/-- Geometric reducedness is unchanged on replacing the base field by a
separable algebraic extension. -/
theorem isGeometricallyReduced_iff_of_separable_algebraic
    {k : Type u} {k' : Type v} {A : Type w} [Field k] [Field k'] [CommRing A]
    [Algebra k k'] [Algebra k' A] [Algebra k A]
    [IsScalarTower k k' A]
    [Algebra.IsAlgebraic k k'] [Algebra.IsSeparable k k'] :
    IsGeometricallyReduced k A ↔ IsGeometricallyReduced k' A := by
  sorry

end

end Formalization.Books.Algebra.Unit43
