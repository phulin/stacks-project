import Formalization.Books.Algebra.Unit84.TransfiniteDevissage
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.RingTheory.LocalRing.Defs

/-!
# Commutative Algebra, Chapter 85: Projective modules over a local ring

The source's projective and free modules use Mathlib's canonical
`Module.Projective` and `Module.Free` predicates.  A direct summand is
represented by a complemented submodule, and a decomposition `M = N ⊕ N'`
is represented by a linear equivalence `M ≃ₗ[R] N × N'`.
-/

namespace Formalization.Books.Algebra.Unit85

universe u v w

/-! ## Projective modules over a local ring -/

/- The introductory reference to the finite case points back to the earlier
   finite-flat-local result; it is not a separate assertion at this source
   boundary. -/

/-- Every projective module is free if and only if every countably generated
projective module is free. -/
theorem projective_free_iff_countablyGenerated_projective_free
    {R : Type u} [CommRing R] :
    (∀ (M : Type v) [AddCommGroup M] [Module R M],
      Module.Projective R M → Module.Free R M) ↔
      (∀ (M : Type v) [AddCommGroup M] [Module R M],
        Module.Projective R M →
          Formalization.Books.Algebra.Unit84.Module.IsCountablyGenerated R M →
            Module.Free R M) := by
  sorry

/-- A countably generated module is free when every decomposition with a
finite free complement has the free-direct-summand property from the source.

The decomposition `M = N ⊕ N'` is represented by a linear equivalence with
the product module `N × N'`. -/
theorem free_of_countablyGenerated_of_free_direct_summand_property
    {R : Type u} {M : Type v} [CommRing R]
    [AddCommGroup M] [Module R M]
    (hM : Formalization.Books.Algebra.Unit84.Module.IsCountablyGenerated R M)
    (hproperty :
      ∀ (N N' : Type w) [AddCommGroup N] [Module R N]
        [AddCommGroup N'] [Module R N']
        [Module.Finite R N'] [Module.Free R N'],
        Nonempty (M ≃ₗ[R] N × N') →
          ∀ x : N, ∃ Q : Submodule R N,
            x ∈ Q ∧ IsComplemented Q ∧ Module.Free R Q) :
    Module.Free R M := by
  sorry

/-- Every element of a projective module over a local ring lies in a free
direct summand. -/
theorem projective_element_mem_free_direct_summand
    {R : Type u} {P : Type v} [CommRing R] [IsLocalRing R]
    [AddCommGroup P] [Module R P]
    (hP : Module.Projective R P) :
    ∀ x : P, ∃ Q : Submodule R P,
      x ∈ Q ∧ IsComplemented Q ∧ Module.Free R Q := by
  sorry

/-- **Projective modules over local rings are free.** -/
theorem projective_free_over_local_ring
    {R : Type u} {P : Type v} [CommRing R] [IsLocalRing R]
    [AddCommGroup P] [Module R P]
    (hP : Module.Projective R P) :
    Module.Free R P := by
  sorry

end Formalization.Books.Algebra.Unit85
