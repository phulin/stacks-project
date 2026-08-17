import Formalization.Books.Algebra.Unit93.DescendingProperties

/-!
# Commutative Algebra, Chapter 95: Descending properties of modules

The source's faithfully flat descent results are already represented by the
canonical interfaces developed in the earlier descent chapter.  This chapter
re-exports those results under its own namespace, retaining Mathlib's
`Module.FaithfullyFlat` predicate and the base-change orientation
`S ⊗[R] M`.
-/

namespace Formalization.Books.Algebra.Unit95

open Formalization.Books.Algebra.Unit84
open Formalization.Books.Algebra.Unit88
open Formalization.Books.Algebra.Unit93
open scoped DirectSum TensorProduct

universe u v w

noncomputable section

/-! ## Faithfully flat descent of the basic properties -/

/-- Mittag--Lefflerness descends along faithfully flat base change. -/
theorem mittagLeffler_descends_of_faithfullyFlat
    {R S : Type u} {M : Type v} [CommRing R] [CommRing S]
    [Algebra R S] [AddCommGroup M] [Module R M]
    [Module.FaithfullyFlat R S]
    (hML : IsMittagLefflerModule
      (ModuleCat.of S (S ⊗[R] M))) :
    IsMittagLefflerModule (ModuleCat.of R M) := by
  exact Formalization.Books.Algebra.Unit93.mittagLeffler_descends_of_faithfullyFlat hML

/-- Countable generation descends along faithfully flat base change. -/
theorem countablyGenerated_descends_of_faithfullyFlat
    {R S : Type u} {M : Type v} [CommRing R] [CommRing S]
    [Algebra R S] [AddCommGroup M] [Module R M]
    [Module.FaithfullyFlat R S]
    (hcountable : Module.IsCountablyGenerated S (S ⊗[R] M)) :
    Module.IsCountablyGenerated R M := by
  exact Formalization.Books.Algebra.Unit93.countablyGenerated_descends_of_faithfullyFlat hcountable

/-- Countably generated projectivity descends along faithfully flat base
change. -/
theorem countablyGenerated_projective_descends_of_faithfullyFlat
    {R S : Type u} {M : Type v} [CommRing R] [CommRing S]
    [Algebra R S] [AddCommGroup M] [Module R M]
    [Module.FaithfullyFlat R S]
    (hcountable : Module.IsCountablyGenerated S (S ⊗[R] M))
    (hprojective : Module.Projective S (S ⊗[R] M)) :
    Module.IsCountablyGenerated R M ∧ Module.Projective R M := by
  exact Formalization.Books.Algebra.Unit93.countablyGenerated_projective_descends_of_faithfullyFlat
    hcountable hprojective

/-! ## Lifting and adapting countably generated submodules -/

/-- A countably generated `S`-submodule of a base change is contained in the
image of the base change of a countably generated `R`-submodule. -/
theorem exists_countablyGenerated_submodule_lifting
    {R S : Type u} {M : Type v} [CommRing R] [CommRing S]
    [Algebra R S] [AddCommGroup M] [Module R M]
    (Q : Submodule S (S ⊗[R] M))
    (hQ : Module.IsCountablyGenerated S (Q : Type (max u v))) :
    ∃ P : Submodule R M,
      Module.IsCountablyGenerated R (P : Type v) ∧
        (Q : Set (S ⊗[R] M)) ≤ Set.range (baseChangeSubmoduleMap P) := by
  exact Formalization.Books.Algebra.Unit93.exists_countablyGenerated_submodule_lifting Q hQ

/-- The adapted-submodule lemma from the source, with a chosen direct-sum
decomposition and the canonical base-change image made explicit. -/
theorem exists_adapted_submodule
    {R S : Type u} {M : Type v} [CommRing R] [CommRing S]
    [Algebra R S] [AddCommGroup M] [Module R M]
    (I : Type v) (Q : I → ModuleCat.{max u v} S)
    (hQ : ∀ i, Module.IsCountablyGenerated S (Q i : Type (max u v)))
    (e : (S ⊗[R] M) ≃ₗ[S]
      (⨁ i, (Q i : Type (max u v))))
    (N : Submodule R M)
    (hN : Module.IsCountablyGenerated R (N : Type v)) :
    ∃ N' : Submodule R M,
      N ≤ N' ∧ Module.IsCountablyGenerated R (N' : Type v) ∧
        ∃ I' : Set I,
          Set.range (baseChangeSubmoduleMap N') =
            (Submodule.comap e.toLinearMap
              (selectedDirectSumSubmodule Q I') :
                Set (S ⊗[R] M)) := by
  exact Formalization.Books.Algebra.Unit93.exists_adapted_submodule I Q hQ e N hN

/-! ## Faithfully flat descent of projectivity -/

/-- Projectivity descends along faithfully flat base change without a
countability hypothesis. -/
theorem projective_descends_of_faithfullyFlat
    {R S : Type u} {M : Type v} [CommRing R] [CommRing S]
    [Algebra R S] [AddCommGroup M] [Module R M]
    [Module.FaithfullyFlat R S]
    (hprojective : Module.Projective S (S ⊗[R] M)) :
    Module.Projective R M := by
  exact Formalization.Books.Algebra.Unit93.projective_descends_of_faithfullyFlat hprojective

end

end Formalization.Books.Algebra.Unit95
