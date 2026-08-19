import Formalization.Books.MoreAlgebra.Unit33.Core
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.SetTheory.Cardinal.ToNat

/-!
# More on Algebra, Chapter 34: Cartier's equality and geometric regularity

The source section is recorded with Mathlib's canonical naive cotangent
homology, Kähler differentials, and Jacobi--Zariski maps.  Cokernels of the
displayed linear maps are represented by the corresponding quotient by the
linear-map range, and the cardinal-valued transcendence degree is converted
to a natural number with `Cardinal.toNat` under the finite-generation
hypotheses.
-/

namespace Formalization.Books.MoreAlgebra.Unit34

open scoped TensorProduct

noncomputable section

universe u

/-! ## Cartier equality -/

/-- Cartier's equality for a finitely generated field extension.

The source writes dimensions as ordinary integers.  In Lean the finite
dimensions are `Module.finrank`, while the transcendence degree is Mathlib's
cardinal-valued `Algebra.trdeg`; `Cardinal.toNat` is the natural-number
presentation of the latter used here.
-/
theorem cartier_equality
    {k K : Type u} [Field k] [Field K] [Algebra k K]
    [Algebra.EssFiniteType k K] :
    FiniteDimensional K (KaehlerDifferential k K) ∧
      FiniteDimensional K (Algebra.H1Cotangent k K) ∧
      Cardinal.toNat (Algebra.trdeg k K) =
        Module.finrank K (KaehlerDifferential k K) -
          Module.finrank K (Algebra.H1Cotangent k K) := by
  sorry

/-! ## Transitivity -/

/-- The Jacobi--Zariski sequence for a tower of fields, including its two
endpoint exactness assertions.

The first map is Mathlib's base change of the canonical map on first
cotangent homology, and the connecting map is Mathlib's canonical
`Algebra.H1Cotangent.δ`.
-/
theorem transitivity_gamma_exact
    {k L M : Type u} [Field k] [Field L] [Field M]
    [Algebra k L] [Algebra k M] [Algebra L M]
    [IsScalarTower k L M] :
    Function.Injective
        ((Algebra.H1Cotangent.map k k L M).liftBaseChange M) ∧
      Function.Exact
        ((Algebra.H1Cotangent.map k k L M).liftBaseChange M)
        (Algebra.H1Cotangent.map k L M M) ∧
      Function.Exact (Algebra.H1Cotangent.map k L M M)
        (Algebra.H1Cotangent.δ k L M) ∧
      Function.Exact (Algebra.H1Cotangent.δ k L M)
        (KaehlerDifferential.mapBaseChange k L M) ∧
      Function.Exact (KaehlerDifferential.mapBaseChange k L M)
        (KaehlerDifferential.map k L M M) ∧
      Function.Surjective (KaehlerDifferential.map k L M M) := by
  sorry

/-! ## The commutative field square -/

/-- The kernel and cokernel dimension formula for the two base-change maps
associated to a commutative square of finitely generated field extensions.

The maps are the canonical base changes of the Kähler-differential and first
cotangent-homology maps.  Since Mathlib represents a cokernel of a linear map
by the quotient of its codomain by its range, those quotient modules are used
explicitly in the finite-dimensional assertions and in the alternating sum.
-/
theorem gamma_commutative_diagram
    {k k' K K' : Type u}
    [Field k] [Field k'] [Field K] [Field K']
    [Algebra k k'] [Algebra k K] [Algebra k K'] [Algebra k' K']
    [Algebra K K'] [IsScalarTower k k' K'] [IsScalarTower k K K']
    [Algebra.EssFiniteType k k'] [Algebra.EssFiniteType K K'] :
    let α : K' ⊗[K] KaehlerDifferential k K →ₗ[K']
        KaehlerDifferential k' K' :=
      LinearMap.liftBaseChange K' (KaehlerDifferential.map k k' K K')
    let β : K' ⊗[K] Algebra.H1Cotangent k K →ₗ[K']
        Algebra.H1Cotangent k' K' :=
      LinearMap.liftBaseChange K' (Algebra.H1Cotangent.map k k' K K')
    FiniteDimensional K' (LinearMap.ker α) ∧
      FiniteDimensional K'
        (KaehlerDifferential k' K' ⧸ LinearMap.range α) ∧
      FiniteDimensional K' (LinearMap.ker β) ∧
      FiniteDimensional K'
        (Algebra.H1Cotangent k' K' ⧸ LinearMap.range β) ∧
      ((Module.finrank K' (LinearMap.ker α) : ℤ) -
          Module.finrank K'
            (KaehlerDifferential k' K' ⧸ LinearMap.range α) -
          Module.finrank K' (LinearMap.ker β) +
          Module.finrank K'
            (Algebra.H1Cotangent k' K' ⧸ LinearMap.range β) =
        (Cardinal.toNat (Algebra.trdeg k k') : ℤ) -
          Cardinal.toNat (Algebra.trdeg K K')) := by
  sorry

end

end Formalization.Books.MoreAlgebra.Unit34
