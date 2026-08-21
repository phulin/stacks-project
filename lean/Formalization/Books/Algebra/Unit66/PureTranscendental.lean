import Mathlib.RingTheory.AlgebraicIndependent.Adjoin
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.TensorProduct.MvPolynomial

open scoped TensorProduct

namespace Formalization.Books.Algebra.Unit66

attribute [local instance] MvPolynomial.algebraMvPolynomial

/-- Extending scalars from a field to the rational function field on any set
of variables, and simultaneously extending the coefficient field, produces a
domain.  Concretely, this tensor product is a localization of the polynomial
ring over the larger coefficient field. -/
theorem isDomain_tensorProduct_fractionRing_mvPolynomial
    {k κ : Type*} [Field k] [Field κ] [Algebra k κ]
    (σ : Type*) : IsDomain (κ ⊗[k] FractionRing (MvPolynomial σ k)) := by
  let A := MvPolynomial σ k
  let F := FractionRing A
  let D := κ ⊗[k] A
  let E := κ ⊗[k] F
  let S := nonZeroDivisors A
  let f : D →ₐ[k] E := Algebra.TensorProduct.map (AlgHom.id k κ)
    (IsScalarTower.toAlgHom k A F)
  letI : Algebra D E := f.toRingHom.toAlgebra
  letI : IsScalarTower κ D E := IsScalarTower.of_algebraMap_eq'
    (show algebraMap κ E = (algebraMap D E).comp (algebraMap κ D) by
      ext x
      change x ⊗ₜ[k] (1 : F) = f (x ⊗ₜ[k] (1 : A))
      rw [Algebra.TensorProduct.map_tmul]
      simp)
  have hloc : IsLocalization
      (S.map (Algebra.TensorProduct.includeRight (R := k) (A := κ))) E := by
    apply IsLocalization.tensorProduct_tensorProduct_right k κ S F
    rfl
  letI : IsLocalization
      (S.map (Algebra.TensorProduct.includeRight (R := k) (A := κ))) E := hloc
  let eD : D ≃ₐ[κ] MvPolynomial σ κ :=
    Algebra.IsPushout.equiv k κ A (MvPolynomial σ κ)
  letI : IsDomain D := eD.toRingEquiv.isDomain_iff.mpr inferInstance
  apply IsLocalization.isDomain_of_le_nonZeroDivisors
    (R := D) (M := S.map
      (Algebra.TensorProduct.includeRight (R := k) (A := κ))) E
  intro x hx
  obtain ⟨a, ha, rfl⟩ := Submonoid.mem_map.mp hx
  rw [mem_nonZeroDivisors_iff_ne_zero]
  change (1 : κ) ⊗ₜ[k] a ≠ 0
  intro hzero
  have hinj : Function.Injective
      (Algebra.TensorProduct.includeRight (R := k) (A := κ) (B := A)) :=
    Algebra.TensorProduct.includeRight_injective
      (FaithfulSMul.algebraMap_injective k κ)
  have ha0 : a = 0 := hinj (by simpa using hzero)
  exact (mem_nonZeroDivisors_iff_ne_zero.mp ha) ha0

end Formalization.Books.Algebra.Unit66
