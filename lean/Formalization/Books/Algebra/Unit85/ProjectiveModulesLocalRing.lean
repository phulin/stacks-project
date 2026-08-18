import Formalization.Books.Algebra.Unit84.TransfiniteDevissage
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
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
    let _ : Module.Projective R M := hP
    obtain ⟨ι, N, hN, ⟨e⟩⟩ :=
      Formalization.Books.Algebra.Unit84.projective_isDirectSumOfCountablyGeneratedProjectiveModules
        (R := R) (M := M)
    let _ : ∀ i, Module.Free R (N i) := fun i => h (N i) (hN i).2 (hN i).1
    let hfree : Module.Free R (DirectSum ι (fun i => (N i : Type v))) :=
      Module.Free.dfinsupp R (fun i => (N i : Type v))
    exact Module.Free.of_equiv' hfree e.symm

private theorem free_element_mem_finite_free_direct_summand
    {R : Type u} {F : Type v} [CommRing R]
    [AddCommGroup F] [Module R F] (hF : Module.Free R F) (x : F) :
    ∃ Q : Submodule R F, x ∈ Q ∧ IsComplemented Q ∧
      Module.Finite R Q ∧ Module.Free R Q := by
  classical
  let b := Module.Free.chooseBasis R F
  let c := b.repr x
  let s : Set (Module.Free.ChooseBasisIndex R F) := c.support
  let _ : Finite s := Finite.of_injective
    (fun i : s => (⟨(i : Module.Free.ChooseBasisIndex R F), by simp [s]⟩ : c.support))
    (by intro i j hij; exact Subtype.ext (congrArg Subtype.val hij))
  let Q : Submodule R F := Submodule.span R (b '' s)
  refine ⟨Q, ?_, ?_, ?_, ?_⟩
  · have hx : c.sum (fun i a => a • b i) = x := by
      simpa only [c, Finsupp.linearCombination_apply] using b.linearCombination_repr x
    rw [← hx]
    change c.sum (fun i a => a • b i) ∈ Q
    apply Submodule.sum_mem
    intro i hi
    exact Submodule.smul_mem Q (c i)
      (Submodule.subset_span ⟨i, hi, rfl⟩)
  · refine ⟨Submodule.span R (b '' sᶜ), ?_⟩
    exact b.linearIndependent.isCompl_span_image (Module.Basis.span_eq b)
      isCompl_compl
  · let v : s → Q := fun i =>
      ⟨b i, Submodule.subset_span ⟨i, i.property, rfl⟩⟩
    let bQ : Module.Basis s R Q := Module.Basis.mk (v := v) (by
      apply LinearIndependent.of_comp Q.subtype
      change LinearIndependent R (fun i : s => b (i : Module.Free.ChooseBasisIndex R F))
      exact
        b.linearIndependent.comp (fun i : s => (i : Module.Free.ChooseBasisIndex R F))
          Subtype.val_injective) (by
      intro y hy
      have hy' : (y : F) ∈ Submodule.span R (b '' s) := y.property
      refine Submodule.span_induction (p := fun z hz =>
        (⟨z, hz⟩ : Q) ∈ Submodule.span R (Set.range v)) ?_ ?_ ?_ ?_ hy'
      · rintro z ⟨i, hi, rfl⟩
        exact Submodule.subset_span ⟨⟨i, hi⟩, rfl⟩
      · exact Submodule.zero_mem _
      · intro z w hz hw hz' hw'
        exact Submodule.add_mem _ hz' hw'
      · intro a z hz hz'
        exact Submodule.smul_mem _ a hz')
    exact Module.Finite.of_basis bQ
  · let v : s → Q := fun i =>
      ⟨b i, Submodule.subset_span ⟨i, i.property, rfl⟩⟩
    let bQ : Module.Basis s R Q := Module.Basis.mk (v := v) (by
      apply LinearIndependent.of_comp Q.subtype
      change LinearIndependent R (fun i : s => b (i : Module.Free.ChooseBasisIndex R F))
      exact
        b.linearIndependent.comp (fun i : s => (i : Module.Free.ChooseBasisIndex R F))
          Subtype.val_injective) (by
      intro y hy
      have hy' : (y : F) ∈ Submodule.span R (b '' s) := y.property
      refine Submodule.span_induction (p := fun z hz =>
        (⟨z, hz⟩ : Q) ∈ Submodule.span R (Set.range v)) ?_ ?_ ?_ ?_ hy'
      · rintro z ⟨i, hi, rfl⟩
        exact Submodule.subset_span ⟨⟨i, hi⟩, rfl⟩
      · exact Submodule.zero_mem _
      · intro z w hz hw hz' hw'
        exact Submodule.add_mem _ hz' hw'
      · intro a z hz hz'
        exact Submodule.smul_mem _ a hz')
    exact Module.Free.of_basis bQ

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
  let _ : Module.Projective R P := hP
  obtain ⟨ι, N, hN, ⟨e⟩⟩ :=
    Formalization.Books.Algebra.Unit84.projective_isDirectSumOfCountablyGeneratedProjectiveModules
      (R := R) (M := P)
  let _ : ∀ i, Module.Projective R (N i) := fun i => (hN i).2
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
    let _ : Module.Projective R A := Module.Projective.of_split inc proj hproj
    exact projective_element_mem_free_direct_summand (R := R) (P := A)
      (inferInstance : Module.Projective R A) x
  let _ : ∀ j, Module.Free R (N j) := fun j => hfree j
  let _ : Module.Free R (DirectSum ι (fun j => (N j : Type v))) :=
    Module.Free.dfinsupp R (fun j : ι => (N j : Type v))
  exact Module.Free.of_equiv' (by infer_instance) e.symm

end Formalization.Books.Algebra.Unit85
