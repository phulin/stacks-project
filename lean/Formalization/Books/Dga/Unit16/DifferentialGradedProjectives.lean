import Formalization.Books.Dga.Unit14.DifferentialGradedProjectives

/-!
# Differential Graded Algebra, Chapter 16: Projective modules and differential graded algebras

This file records the source section's graded-projectivity convention, its
admissible-epimorphism lemma, and its two Hom computations.  The DGA,
graded-module, shift, admissibility, cycle, cohomology, and homotopy-category
interfaces are reused from Unit14.  In particular, the source's “surjective”
map is represented degreewise, the first displayed Hom equality by an
equivalence with `dgCycles`, and the second by an equivalence with
`dgCohomology`.
-/

namespace Formalization.Books.Dga.Unit16

open Formalization.Books.Dga.Unit14

universe u v w

variable {R : Type u} {A : ℤ → Type v}
  [CommRing R]
  [∀ i, AddCommGroup (A i)] [∀ i, Module R (A i)]
  [DirectSum.GSemiring A] [DirectSum.GAlgebra R A]

/-! ## Graded projectivity -/

/-- A differential graded module is graded projective when its underlying
graded right module is projective in the abelian category of graded modules.
This is the source's convention for “projective as a graded `A`-module”. -/
abbrev IsGradedProjective
    {D : DifferentialGradedAlgebraData (R := R) (A := A)}
    (P : DifferentialGradedModuleData D) : Prop :=
  Formalization.Books.Dga.Unit14.IsGradedProjective P

/-! ## The target lemma

The source's admissible-epimorphism assertion is covered by the canonical
Unit14 predicate, which records both degreewise surjectivity and a splitting
of the underlying graded map.
-/

/-- A degreewise-surjective DG map onto a graded-projective target is an
admissible epimorphism. -/
theorem target_graded_projective_admissible
    {D : DifferentialGradedAlgebraData (R := R) (A := A)}
    {M P : DifferentialGradedModuleData D}
    (f : DifferentialGradedModuleHom M P)
    (hf : DifferentialGradedModuleHom.DegreewiseSurjective f)
    (hP : IsGradedProjective P) :
    IsAdmissibleEpimorphism f := by
  exact Formalization.Books.Dga.Unit14.target_graded_projective_admissible f hf hP

/-! ## Hom computations from a shifted free module -/

/-- The shifted regular DG module `A[k]`. -/
noncomputable abbrev shiftedFreeModule
    (D : DifferentialGradedAlgebraData (R := R) (A := A)) (k : ℤ) :=
  differentialGradedAlgebraShift D k

/-- Maps from `A[k]` to `M` are equivalent to cycles in degree `-k`. -/
theorem hom_from_shift_free_equiv
    (D : DifferentialGradedAlgebraData (R := R) (A := A))
    (M : DifferentialGradedModuleData D) (k : ℤ) :
    Nonempty
      (DifferentialGradedModuleHom (shiftedFreeModule D k) M ≃
        dgCycles M (-k)) := by
  exact Formalization.Books.Dga.Unit14.dg_hom_from_shift_evaluation_equiv D M k

/-- Maps from `A[k]` in the homotopy category are equivalent to the
cohomology of `M` in degree `-k`. -/
theorem homotopy_hom_from_shift_free_equiv
    (D : DifferentialGradedAlgebraData (R := R) (A := A))
    (M : DifferentialGradedModuleData D) (k : ℤ) :
    Nonempty
      (dgHomotopyCategoryHom (shiftedFreeModule D k) M ≃
        dgCohomology M (-k)) := by
  exact
    Formalization.Books.Dga.Unit14.dg_homotopy_hom_from_shift_evaluation_equiv D M k

end Formalization.Books.Dga.Unit16
