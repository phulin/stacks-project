import Formalization.Books.Algebra.Unit43.GeometricallyReduced
import Formalization.Books.Algebra.Unit47.GeometricallyIrreducible
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.Algebra.Field.ULift
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Commutative Algebra, Chapter 49: Geometrically integral algebras

The geometric integral predicate is expressed using Mathlib's `IsDomain`,
with the same field-base-change tensor-product orientation as Chapters 43 and
47.  The characterization lemmas retain the source's finite-extension and
algebraic-closure tests.
-/

namespace Formalization.Books.Algebra.Unit49

open scoped TensorProduct

open Formalization.Books.Algebra.Unit43
open Formalization.Books.Algebra.Unit47

universe u v w z

noncomputable section

/-! ## Geometrically integral algebras -/

private theorem irreducibleSpace_tensorProduct_of_isGeometricallyIrreducible
    {k : Type u} {S : Type v} {R : Type w}
    [Field k] [CommRing S] [CommRing R] [Algebra k S] [Algebra k R]
    (hS : IsGeometricallyIrreducible k S)
    [IrreducibleSpace (PrimeSpectrum R)] :
    IrreducibleSpace (PrimeSpectrum (R ⊗[k] S)) := by
  let X := PrimeSpectrum R
  let Y := PrimeSpectrum (R ⊗[k] S)
  obtain ⟨e, he⟩ :=
    geometricallyIrreducible_baseChange_components (k := k) (R := R) (S := S) hS
  have hsubX : Subsingleton (irreducibleComponents X) := by
    constructor
    intro A B
    apply Subtype.ext
    have hA : A.1 = (Set.univ : Set X) := by
      have h := A.2
      simpa only [irreducibleComponents_eq_singleton, Set.mem_singleton_iff] using h
    have hB : B.1 = (Set.univ : Set X) := by
      have h := B.2
      simpa only [irreducibleComponents_eq_singleton, Set.mem_singleton_iff] using h
    exact hA.trans hB.symm
  let Cx : irreducibleComponents X :=
    ⟨Set.univ, by rw [irreducibleComponents_eq_singleton]; simp⟩
  let C : irreducibleComponents Y := e.symm Cx
  have hsubY : Subsingleton (irreducibleComponents Y) := by
    constructor
    intro A B
    apply e.injective
    letI := hsubX
    exact Subsingleton.elim (e A) (e B)
  have hC : C.1 = (Set.univ : Set Y) := by
    apply Set.Subset.antisymm
    · exact Set.subset_univ _
    · intro y hy
      have hy' : y ∈ ⋃₀ irreducibleComponents Y := by
        rw [sUnion_irreducibleComponents]
        exact Set.mem_univ y
      rcases Set.mem_sUnion.mp hy' with ⟨D, hD, hyD⟩
      have hCD : (⟨D, hD⟩ : irreducibleComponents Y) = C := by
        letI := hsubY
        exact Subsingleton.elim _ _
      rw [← congrArg Subtype.val hCD]
      exact hyD
  apply (irreducibleSpace_def _).mpr
  simpa [hC] using C.2.1

/-- An algebra over a field is geometrically integral when every field base
change is an integral domain. -/
def IsGeometricallyIntegral (k : Type u) (S : Type v) [Field k] [CommRing S]
    [Algebra k S] : Prop :=
  ∀ (K : Type w) [Field K] [Algebra k K],
    IsDomain (K ⊗[k] S)

private theorem isDomain_tensorProduct_of_isGeometricallyIntegral
    {k : Type u} {S : Type v} {K : Type z}
    [Field k] [CommRing S] [Field K] [Algebra k S] [Algebra k K]
    (h : IsGeometricallyIntegral.{u, v, w} k S) :
    IsDomain (K ⊗[k] S) := by
  let K' := ULift.{w, z} K
  letI : Field K' := inferInstance
  letI : Algebra k K' := inferInstance
  letI : IsDomain (K' ⊗[k] S) := by sorry
  let e : K' ⊗[k] S ≃ₐ[k] K ⊗[k] S :=
    Algebra.TensorProduct.congr (ULift.algEquiv (R := k))
      (AlgEquiv.refl : S ≃ₐ[k] S)
  exact e.symm.toMulEquiv.isDomain _

private theorem isReduced_tensorProduct_of_isGeometricallyIntegral
    {k : Type u} {S : Type v} {K : Type z}
    [Field k] [CommRing S] [Field K] [Algebra k S] [Algebra k K]
    (h : IsGeometricallyIntegral.{u, v, w} k S) :
    IsReduced (K ⊗[k] S) := by
  let K' := ULift.{w, z} K
  letI : Field K' := inferInstance
  letI : Algebra k K' := inferInstance
  letI : IsDomain (K' ⊗[k] S) := by sorry
  let e : K' ⊗[k] S ≃ₐ[k] K ⊗[k] S :=
    Algebra.TensorProduct.congr (ULift.algEquiv (R := k))
      (AlgEquiv.refl : S ≃ₐ[k] S)
  exact isReduced_of_injective e.symm.toRingHom e.symm.injective

/-- Geometric integrality is equivalent to geometric irreducibility together
with geometric reducedness. -/
theorem isGeometricallyIntegral_iff_geometricallyIrreducible_and_geometricallyReduced
    {k : Type u} {S : Type v} [Field k] [CommRing S] [Algebra k S] :
    IsGeometricallyIntegral k S ↔
      IsGeometricallyIrreducible k S ∧ IsGeometricallyReduced k S := by
  constructor
  · intro h
    constructor
    · intro K _ _
      letI : IsDomain (K ⊗[k] S) :=
        isDomain_tensorProduct_of_isGeometricallyIntegral h
      infer_instance
    · intro K _ _
      exact isReduced_tensorProduct_of_isGeometricallyIntegral h
  · rintro ⟨hirr, hred⟩ K _ _
    letI : IsReduced (K ⊗[k] S) :=
      isReduced_tensorProduct_of_isReduced_of_isGeometricallyReduced
        (k := k) (R := K) (S := S) inferInstance hred
    have hp : (nilradical (K ⊗[k] S)).IsPrime :=
      (PrimeSpectrum.irreducibleSpace_iff_isPrime_nilradical).mp
        (irreducibleSpace_tensorProduct_of_isGeometricallyIrreducible
          (R := K) (S := S) hirr)
    rw [nilradical_eq_zero] at hp
    letI : (⊥ : Ideal (K ⊗[k] S)).IsPrime := hp
    exact IsDomain.of_bot_isPrime _

/-- Geometric integrality can be tested after finite field extensions and
after passage to an algebraic closure. -/
theorem isGeometricallyIntegral_iff_finiteExtension_iff_algebraicClosure
    {k : Type u} {S : Type v} [Field k] [CommRing S] [Algebra k S] :
    (IsGeometricallyIntegral k S ↔
      ∀ (k' : Type u) [Field k'] [Algebra k k']
        [FiniteDimensional k k'],
        IsDomain (k' ⊗[k] S)) ∧
      ((∀ (k' : Type u) [Field k'] [Algebra k k']
        [FiniteDimensional k k'],
        IsDomain (k' ⊗[k] S)) ↔
        IsDomain (AlgebraicClosure k ⊗[k] S)) := by
  sorry

/-- Tensoring a geometrically integral algebra with an integral-domain
`k`-algebra remains an integral domain. -/
theorem isGeometricallyIntegral_any_integral_base_change
    {k : Type u} {S : Type v} {R : Type w}
    [Field k] [CommRing S] [CommRing R] [Algebra k S] [Algebra k R]
    [IsDomain R] (hS : IsGeometricallyIntegral k S) :
    IsDomain (R ⊗[k] S) := by
  sorry

end

end Formalization.Books.Algebra.Unit49
