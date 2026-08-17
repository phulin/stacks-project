import Formalization.Books.Algebra.Unit91.ExamplesAndNonExamples
import Formalization.Books.Algebra.Unit97.CompletionForNoetherianRings
import Formalization.Books.MoreAlgebra.Unit28.CompletionFlatness
import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal

/-!
# More on Flatness, Chapter 8: Completion and Mittag-Leffler modules

The source's module completions are Mathlib's `AdicCompletion`s.  The
Mittag-Leffler predicate is the established `IsMittagLefflerModule`, and
universal injectivity is the tensor criterion from Algebra, Chapter 82.
The source writes `Q ⊗_R N` in the associated-prime conditions.  We use the
canonically symmetric `N ⊗[R] Q` orientation so that the existing S-module
structure on `N` supplies the S-action on the tensor product.
-/

namespace Formalization.Books.Flat.Unit08

open CategoryTheory
open Formalization.Books.Algebra.Unit82
open Formalization.Books.Algebra.Unit88
open Formalization.Books.Algebra.Unit96
open scoped DirectSum TensorProduct

universe u v w z

noncomputable section

/-! ## Completion and Mittag-Leffler modules -/

/-- The completion of an arbitrary direct sum of copies of a complete
Noetherian ring is flat and Mittag-Leffler. -/
theorem completedDirectSum_flat_and_mittagLeffler
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    (I : Ideal R) [IsAdicComplete I R] (A : Type v) :
    Module.Flat R (completion I (⨁ _ : A, R)) ∧
      IsMittagLefflerModule
        (ModuleCat.of R (completion I (⨁ _ : A, R))) := by
  sorry

/-- The completion of a flat module whose reduction is projective is flat and
Mittag-Leffler over a complete Noetherian ring. -/
theorem completion_flat_and_mittagLeffler_of_flat_of_projective_mod
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    (I : Ideal R) [IsAdicComplete I R]
    {M : Type v} [AddCommGroup M] [Module R M]
    [Module.Flat R M]
    [Module.Projective (R ⧸ I)
      (M ⧸ (I • (⊤ : Submodule R M)))] :
    Module.Flat R (completion I M) ∧
      IsMittagLefflerModule (ModuleCat.of R (completion I M)) := by
  sorry

/- The source's intervening finite-type remark is already represented by the
canonical `Formalization.Books.Algebra.Unit31.finiteType_algebra_isNoetherian`.
Its `[Algebra R S]` and `[Algebra.FiniteType R S]` interface is the standard
Lean form of a finite-type ring map, so no parallel chapter-local theorem is
needed here. -/

/-- The map into completion is universally injective under the associated-prime
condition tested after tensoring with every finite R-module. -/
theorem universallyInjective_to_completion
    {R : Type u} {S : Type v} {N : Type w}
    [CommRing R] [CommRing S] [AddCommGroup N] [Module S N]
    [IsNoetherianRing R] [IsNoetherianRing S] [Module.Finite S N]
    (I : Ideal R) (f : R →+* S) :
    letI : Algebra R S := f.toAlgebra
    letI : Module R N := Module.compHom N f
    letI : IsScalarTower R S N := SMul.comp.isScalarTower f
    (∀ (Q : Type z) [AddCommGroup Q] [Module R Q] [Module.Finite R Q],
      letI : Module S (N ⊗[R] Q) := TensorProduct.leftModule
      ∀ q ∈ _root_.associatedPrimes S (N ⊗[R] Q),
        I.map f + q ≠ (⊤ : Ideal S)) →
      universallyInjective (AdicCompletion.of I N) := by
  sorry

/-- The flat variant of universal injectivity, with the associated-prime
condition checked on the fibres over the contractions of primes of S. -/
theorem universallyInjective_to_completion_of_flat
    {R : Type u} {S : Type v} {N : Type w}
    [CommRing R] [CommRing S] [AddCommGroup N] [Module S N]
    [IsNoetherianRing R] [IsNoetherianRing S] [Module.Finite S N]
    (I : Ideal R) (f : R →+* S) :
    letI : Algebra R S := f.toAlgebra
    letI : Module R N := Module.compHom N f
    letI : IsScalarTower R S N := SMul.comp.isScalarTower f
    Module.Flat R N →
      (∀ (q : Ideal S) [q.IsPrime],
        letI : Module S (N ⊗[R] (q.comap f).ResidueField) :=
          TensorProduct.leftModule
        q ∈ _root_.associatedPrimes S
            (N ⊗[R] (q.comap f).ResidueField) →
          I.map f + q ≠ (⊤ : Ideal S)) →
      universallyInjective (AdicCompletion.of I N) := by
  sorry

end

end Formalization.Books.Flat.Unit08
