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
  constructor
  · intro h M _ _ hP _
    exact h M hP
  · intro h M _ _ hP
    letI : Module.Projective R M := hP
    obtain ⟨ι, N, hN, ⟨e⟩⟩ :=
      Formalization.Books.Algebra.Unit84.projective_isDirectSumOfCountablyGeneratedProjectiveModules
        (R := R) (M := M)
    letI : ∀ i, Module.Free R (N i) := fun i => h (N i) (hN i).2 (hN i).1
    let hfree : Module.Free R (DirectSum ι (fun i => (N i : Type v))) :=
      Module.Free.dfinsupp R (fun i => (N i : Type v))
    exact Module.Free.of_equiv' hfree e.symm

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
  letI : Module.Projective R P := hP
  obtain ⟨ι, N, hN, ⟨e⟩⟩ :=
    Formalization.Books.Algebra.Unit84.projective_isDirectSumOfCountablyGeneratedProjectiveModules
      (R := R) (M := P)
  letI : ∀ i, Module.Projective R (N i) := fun i => (hN i).2
  have hfree : ∀ i, Module.Free R (N i) := by
    intro i
    refine free_of_countablyGenerated_of_free_direct_summand_property
      (R := R) (M := (N i : Type v)) (hN i).1 ?_
    intro (A : Type v) (B : Type v) _ _ _ _ _ _ hAB x
    rcases hAB with ⟨eAB⟩
    let inc : A →ₗ[R] (N i : Type v) := eAB.symm.toLinearMap.comp
      (LinearMap.inl R A B)
    let proj : (N i : Type v) →ₗ[R] A := (LinearMap.fst R A B).comp eAB.toLinearMap
    have hproj : proj.comp inc = LinearMap.id := by
      ext a
      simp [inc, proj]
    letI : Module.Projective R A := Module.Projective.of_split inc proj hproj
    exact projective_element_mem_free_direct_summand (R := R) (P := A)
      (inferInstance : Module.Projective R A) x
  letI : ∀ j, Module.Free R (N j) := fun j => hfree j
  letI : Module.Free R (DirectSum ι (fun j => (N j : Type v))) :=
    Module.Free.dfinsupp R (fun j : ι => (N j : Type v))
  exact Module.Free.of_equiv' (by infer_instance) e.symm

end Formalization.Books.Algebra.Unit85
