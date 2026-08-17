import Mathlib.Topology.Sheaves.Presheaf

/-!
# Sheaves on Spaces, Chapter 3: Presheaves

This file formalizes the precise statements in `books/sheaves.tex`, lines
69--135.  Mathlib's `TopCat.Presheaf` is the canonical implementation of the
presheaf data: a
presheaf of sets on a bundled topological space is a functor from the
opposite of its category of open sets to `Type`, and its morphisms are natural
transformations.  The aliases below expose that implementation using the
book's terminology without introducing a second presheaf structure.
-/

namespace Formalization.Books.Sheaves.Unit03

open CategoryTheory Opposite TopologicalSpace

universe w v

/-! ## Presheaves of sets and their morphisms -/

/-- A presheaf of sets on `X`, represented by Mathlib's canonical functor. -/
abbrev Presheaf (X : TopCat.{v}) : Type (max (w + 1) v) :=
  TopCat.Presheaf (Type w) X

/-- A morphism of presheaves of sets, represented by a natural transformation. -/
abbrev PresheafMorphism {X : TopCat.{v}} (F G : Presheaf X) :=
  F ⟶ G

/-- The category denoted `PSh(X)` in the source. -/
abbrev PSh (X : TopCat.{v}) :=
  Presheaf X

/-!
The identity and composition requirements in the source definition are the
`map_id` and `map_comp` fields of the functor `F`.  The next declarations give
their source-facing consequences on sections.
-/

/-- The sections of a presheaf over an open set. -/
abbrev Sections {X : TopCat.{v}} (F : Presheaf X) (U : Opens X) :=
  ToType (F.obj (op U))

/-- Restriction of a section along an inclusion of open subsets. -/
abbrev restriction {X : TopCat.{v}} {F : Presheaf X}
    {U V : Opens X} (h : V ≤ U) (s : Sections F U) : Sections F V :=
  TopCat.Presheaf.restrict s (homOfLE h)

/-- Restriction to the same open set is the identity. -/
@[simp]
theorem restriction_self {X : TopCat.{v}} {F : Presheaf X}
    {U : Opens X} (s : Sections F U) :
    restriction (F := F) (le_refl U) s = s := by
  change F.map (𝟙 (op U)) s = s
  simp

/-- Successive restrictions agree with direct restriction. -/
theorem restriction_restriction {X : TopCat.{v}} {F : Presheaf X}
    {U V W : Opens X} (hWV : W ≤ V) (hVU : V ≤ U) (s : Sections F U) :
    restriction (F := F) hWV (restriction (F := F) hVU s) =
      restriction (F := F) (hWV.trans hVU) s := by
  simpa [restriction] using
    (TopCat.Presheaf.restrict_restrict (F := F) hWV hVU s)

/-!
The naturality square for a presheaf morphism is the commuting square in the
source definition, written on sections.
-/

/-- Presheaf morphisms commute with restriction maps. -/
theorem morphism_restriction {X : TopCat.{v}}
    {F G : Presheaf X} (φ : PresheafMorphism F G)
    {U V : Opens X} (h : V ≤ U) (s : Sections F U) :
    restriction (F := G) h (φ.app (op U) s) =
      φ.app (op V) (restriction (F := F) h s) := by
  simpa [restriction] using (TopCat.Presheaf.map_restrict φ h s).symm

/-!
`Sections F U` is the source's `F(U)`.  The text mentions the alternative
notations `Γ(U, F)` and `H^0(U, F)` but explicitly does not use them in this
chapter, so no additional notation is introduced here.
-/

/-! ## Constant presheaves -/

/-- The constant presheaf with value `A`. -/
def constantPresheaf {X : TopCat.{v}} (A : Type w) : Presheaf X :=
  (Functor.const (Opens X)ᵒᵖ).obj A

@[simp]
theorem constantPresheaf_sections {X : TopCat.{v}} (A : Type w)
    (U : Opens X) : Sections (constantPresheaf (X := X) A) U = A :=
  rfl

/-- Every restriction map of a constant presheaf is the identity on `A`. -/
@[simp]
theorem constantPresheaf_map {X : TopCat.{v}} (A : Type w)
    {U V : Opens X} (h : V ≤ U) :
    (constantPresheaf (X := X) A).map (homOfLE h).op = 𝟙 A :=
  rfl

@[simp]
theorem constantPresheaf_restriction {X : TopCat.{v}} (A : Type w)
    {U V : Opens X} (h : V ≤ U) (s : A) :
    restriction (F := constantPresheaf (X := X) A) h s = s :=
  rfl

end Formalization.Books.Sheaves.Unit03
