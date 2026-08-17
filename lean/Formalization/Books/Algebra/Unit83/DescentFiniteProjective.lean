import Formalization.Books.Algebra.Unit78.FiniteProjectiveModules
import Formalization.Books.Algebra.Unit81.CharacterizingFlatness
import Mathlib.RingTheory.Finiteness.Descent

/-!
# Commutative Algebra, Chapter 83: Descent for finite projective modules

This file records the source section's characterization of finite projective
modules, the three stated descent properties, and faithfully flat descent of
finite projectivity.  The tensor product is written in Mathlib's canonical
orientation `S ⊗[R] M` for the base change of an `R`-module to `S`.

The section's opening paragraph is a roadmap for later sections rather than a
separate mathematical assertion at this source boundary.
-/

namespace Formalization.Books.Algebra.Unit83

open scoped TensorProduct

universe u v w

noncomputable section

/-! ## Finite projectivity and finite presentation -/

/-- A module is finite projective exactly when it is finitely presented and flat.

This is the source's `lemma-finite-projective-again`.  The finite-projective
predicate is Unit 78's canonical conjunction of `Module.Finite` and
`Module.Projective`.
-/
theorem finite_projective_iff_finitePresentation_and_flat
    {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M] :
    Formalization.Books.Algebra.Unit78.FiniteProjective R M ↔
      Module.FinitePresentation R M ∧ Module.Flat R M := by
  constructor
  · rintro ⟨hfinite, hprojective⟩
    let _ : Module.Finite R M := hfinite
    let _ : Module.Projective R M := hprojective
    exact ⟨Module.finitePresentation_of_projective R M, inferInstance⟩
  · rintro ⟨hfinitePresentation, hflat⟩
    let _ : Module.FinitePresentation R M := hfinitePresentation
    let _ : Module.Flat R M := hflat
    exact ⟨inferInstance, Module.Flat.projective_of_finitePresentation⟩

/-! ## Properties descending along faithfully flat base change -/

/-- Finite generation descends along faithfully flat base change.

This is item (1) of the source's `lemma-descend-properties-modules`.
-/
theorem finite_type_descends_of_faithfullyFlat
    {R : Type u} {S : Type v} {M : Type w} [CommRing R] [CommRing S]
    [Algebra R S] [AddCommGroup M] [Module R M]
    [Module.FaithfullyFlat R S] :
    Module.Finite S (S ⊗[R] M) → Module.Finite R M := by
  intro hfinite
  let _ : Module.Finite S (S ⊗[R] M) := hfinite
  exact Module.Finite.of_finite_tensorProduct_of_faithfullyFlat S

/-- Finite presentation descends along faithfully flat base change.

This is item (2) of the source's `lemma-descend-properties-modules`.
-/
theorem finitePresentation_descends_of_faithfullyFlat
    {R : Type u} {S : Type v} {M : Type w} [CommRing R] [CommRing S]
    [Algebra R S] [AddCommGroup M] [Module R M]
    [Module.FaithfullyFlat R S] :
    Module.FinitePresentation S (S ⊗[R] M) → Module.FinitePresentation R M := by
  sorry

/-- Flatness descends along faithfully flat base change.

This is item (3) of the source's `lemma-descend-properties-modules`.
-/
theorem flat_descends_of_faithfullyFlat
    {R : Type u} {S : Type v} {M : Type w} [CommRing R] [CommRing S]
    [Algebra R S] [AddCommGroup M] [Module R M]
    [Module.FaithfullyFlat R S] :
    Module.Flat S (S ⊗[R] M) → Module.Flat R M := by
  intro hflat
  let _ : Module.Flat S (S ⊗[R] M) := hflat
  exact Module.Flat.of_flat_tensorProduct R M S

/-- The three precise descent clauses listed in the source lemma.

The source's fourth list item is only the placeholder “add more here as
needed”; it is therefore not included in this source-faithful conjunction.
-/
theorem descend_properties_modules
    {R : Type u} {S : Type v} {M : Type w} [CommRing R] [CommRing S]
    [Algebra R S] [AddCommGroup M] [Module R M]
    [Module.FaithfullyFlat R S] :
    (Module.Finite S (S ⊗[R] M) → Module.Finite R M) ∧
      (Module.FinitePresentation S (S ⊗[R] M) →
        Module.FinitePresentation R M) ∧
        (Module.Flat S (S ⊗[R] M) → Module.Flat R M) := by
  refine ⟨finite_type_descends_of_faithfullyFlat, ?_⟩
  exact ⟨finitePresentation_descends_of_faithfullyFlat,
    flat_descends_of_faithfullyFlat⟩

/-! ## Faithfully flat descent of finite projectivity -/

/-- Finite projectivity descends along a faithfully flat ring map.

This is the source's `proposition-ffdescent-finite-projectivity`.
-/
theorem faithfullyFlat_descends_finiteProjective
    {R : Type u} {S : Type v} {M : Type w} [CommRing R] [CommRing S]
    [Algebra R S] [AddCommGroup M] [Module R M]
    [Module.FaithfullyFlat R S]
    (hM : Formalization.Books.Algebra.Unit78.FiniteProjective S (S ⊗[R] M)) :
    Formalization.Books.Algebra.Unit78.FiniteProjective R M := by
  rcases hM with ⟨hfinite, hprojective⟩
  let _ : Module.Finite S (S ⊗[R] M) := hfinite
  let _ : Module.Projective S (S ⊗[R] M) := hprojective
  have hfinitePresentation : Module.FinitePresentation S (S ⊗[R] M) :=
    Module.finitePresentation_of_projective S (S ⊗[R] M)
  apply (finite_projective_iff_finitePresentation_and_flat (R := R) (M := M)).2
  exact ⟨finitePresentation_descends_of_faithfullyFlat hfinitePresentation,
    Module.Flat.of_flat_tensorProduct R M S⟩

end

end Formalization.Books.Algebra.Unit83
