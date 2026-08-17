import Formalization.Books.Sheaves.Unit22.OpenImmersions
import Formalization.Books.Sheaves.Unit22.ClosedImmersions
import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-!
# Sheaves of Modules, Chapter 7: A canonical exact sequence

The source section is `books/modules.tex:650-703`.  The open and closed
immersions, their inverse/direct-image functors, and the extension-by-zero
adjunction are the canonical constructions from the earlier sheaf chapters.
The displayed sequence is represented by a `ShortComplex`; its assertion of
short exactness is stated with Mathlib's `ShortComplex.ShortExact`.
-/

namespace Formalization.Books.Modules.Unit07

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Formalization.Books.Sheaves.Unit08
open Formalization.Books.Sheaves.Unit22

universe v

noncomputable section

/-! ## The open/closed decomposition -/

/-- The closed complement of an open subset. -/
def canonicalClosedSubset {X : TopCat.{v}} (U : Opens X) : Set X :=
  (U : Set X)ᶜ

/-- The complement of an open subset is closed. -/
theorem canonicalClosedSubset_isClosed {X : TopCat.{v}} (U : Opens X) :
    IsClosed (canonicalClosedSubset U) := by
  exact U.2.isClosed_compl

/-! ## The two canonical maps -/

/-- The counit map `j_! j⁻¹ F ⟶ F` in the canonical sequence. -/
noncomputable abbrev canonicalExactSequenceLeft {X : TopCat.{v}}
    (U : Opens X) (F : Ab X) :
    (openAbelianSheafExtensionFunctor U).obj
        ((openSheafRestriction AddCommGrpCat U).obj F) ⟶ F :=
  (openSheafExtensionAdjunction AddCommGrpCat U).counit.app F

/-- The unit map `F ⟶ i_* i⁻¹ F` in the canonical sequence. -/
noncomputable abbrev canonicalExactSequenceRight {X : TopCat.{v}}
    (U : Opens X) (F : Ab X) :
    F ⟶
      (closedSheafDirectImage AddCommGrpCat (canonicalClosedSubset U)
        (canonicalClosedSubset_isClosed U)).obj
        ((closedAbelianSheafRestriction (canonicalClosedSubset U)
          (canonicalClosedSubset_isClosed U)).obj F) :=
  (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat
    (closedInclusion (canonicalClosedSubset U))).unit.app F

/-! ## The exact sequence -/

/-- The consecutive maps in the canonical sequence compose to zero. -/
theorem canonicalExactSequence_zero {X : TopCat.{v}} (U : Opens X) (F : Ab X) :
    canonicalExactSequenceLeft U F ≫ canonicalExactSequenceRight U F = 0 := by
  sorry

/-- The short complex underlying the canonical sequence. -/
noncomputable def canonicalExactSequence {X : TopCat.{v}} (U : Opens X) (F : Ab X) :
    ShortComplex (Ab X) :=
  ShortComplex.mk (canonicalExactSequenceLeft U F)
    (canonicalExactSequenceRight U F) (canonicalExactSequence_zero U F)

/-- The sequence `0 ⟶ j_!j⁻¹F ⟶ F ⟶ i_*i⁻¹F ⟶ 0` is short exact. -/
theorem canonicalExactSequence_shortExact {X : TopCat.{v}} (U : Opens X) (F : Ab X) :
    (canonicalExactSequence U F).ShortExact := by
  sorry

/-! ## Functoriality -/

/-- A morphism of sheaves induces a morphism of canonical short complexes. -/
noncomputable def canonicalExactSequenceMap {X : TopCat.{v}} (U : Opens X)
    {F G : Ab X} (φ : F ⟶ G) :
    canonicalExactSequence U F ⟶ canonicalExactSequence U G :=
  { τ₁ := (openAbelianSheafExtensionFunctor U).map
      ((openSheafRestriction AddCommGrpCat U).map φ)
    τ₂ := φ
    τ₃ := (closedSheafDirectImage AddCommGrpCat (canonicalClosedSubset U)
      (canonicalClosedSubset_isClosed U)).map
      ((closedAbelianSheafRestriction (canonicalClosedSubset U)
        (canonicalClosedSubset_isClosed U)).map φ)
    comm₁₂ := by
      exact (openSheafExtensionAdjunction AddCommGrpCat U).counit.naturality φ
    comm₂₃ := by
      exact (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat
        (closedInclusion (canonicalClosedSubset U))).unit.naturality φ }

end

end Formalization.Books.Modules.Unit07
