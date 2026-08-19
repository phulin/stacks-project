import Formalization.Books.Sheaves.Unit31.Infrastructure
import Formalization.Books.Sheaves.Unit32.Infrastructure
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
  have hcomp (x : X) :
      (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
          (canonicalExactSequenceLeft U F ≫ canonicalExactSequenceRight U F).hom = 0 := by
    change (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
        ((canonicalExactSequenceLeft U F).hom ≫
          (canonicalExactSequenceRight U F).hom) = 0
    rw [Functor.map_comp]
    by_cases hx : x ∈ U
    · rcases closedAbelianSheafDirectImage_stalk_outside
        (canonicalClosedSubset U) (canonicalClosedSubset_isClosed U)
        ((closedAbelianSheafRestriction (canonicalClosedSubset U)
          (canonicalClosedSubset_isClosed U)).obj F) x (by
            simpa [canonicalClosedSubset] using hx) with ⟨e⟩
      apply (cancel_mono e.hom).1
      exact (isZero_zero AddCommGrpCat).eq_of_tgt _ _
    · rcases openAlgebraicSheafExtension_stalk_initial AddCommGrpCat U
        ((openSheafRestriction AddCommGrpCat U).obj F) x hx with ⟨e⟩
      apply (cancel_epi e.inv).1
      exact initialIsInitial.hom_ext _ _
  have hzero (x : X) :
      (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
        ((0 : (openAbelianSheafExtensionFunctor U).obj
          ((openSheafRestriction AddCommGrpCat U).obj F) ⟶
          (closedSheafDirectImage AddCommGrpCat (canonicalClosedSubset U)
            (canonicalClosedSubset_isClosed U)).obj
            ((closedAbelianSheafRestriction (canonicalClosedSubset U)
              (canonicalClosedSubset_isClosed U)).obj F)).hom) = 0 := by
    change (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
      (0 : ((openAbelianSheafExtensionFunctor U).obj
        ((openSheafRestriction AddCommGrpCat U).obj F)).presheaf ⟶
        ((closedSheafDirectImage AddCommGrpCat (canonicalClosedSubset U)
          (canonicalClosedSubset_isClosed U)).obj
          ((closedAbelianSheafRestriction (canonicalClosedSubset U)
            (canonicalClosedSubset_isClosed U)).obj F)).presheaf) = 0
    exact Functor.map_zero
      (TopCat.Presheaf.stalkFunctor (C := AddCommGrpCat.{v}) (X := X) x)
      ((openAbelianSheafExtensionFunctor U).obj
        ((openSheafRestriction AddCommGrpCat U).obj F)).presheaf
      ((closedSheafDirectImage AddCommGrpCat (canonicalClosedSubset U)
        (canonicalClosedSubset_isClosed U)).obj
        ((closedAbelianSheafRestriction (canonicalClosedSubset U)
          (canonicalClosedSubset_isClosed U)).obj F)).presheaf
  apply CategoryTheory.Sheaf.hom_ext
  apply NatTrans.ext
  funext V
  apply ConcreteCategory.hom_ext
  intro s
  apply TopCat.Presheaf.section_ext _ _
  intro x hx
  rw [← TopCat.Presheaf.stalkFunctor_map_germ_apply,
    ← TopCat.Presheaf.stalkFunctor_map_germ_apply]
  rw [hcomp x, hzero x]

/-- The short complex underlying the canonical sequence. -/
noncomputable def canonicalExactSequence {X : TopCat.{v}} (U : Opens X) (F : Ab X) :
    ShortComplex (Ab X) :=
  ShortComplex.mk (canonicalExactSequenceLeft U F)
    (canonicalExactSequenceRight U F) (canonicalExactSequence_zero U F)

/-- The sequence `0 ⟶ j_!j⁻¹F ⟶ F ⟶ i_*i⁻¹F ⟶ 0` is short exact. -/
theorem canonicalExactSequence_shortExact {X : TopCat.{v}} (U : Opens X) (F : Ab X) :
    (canonicalExactSequence U F).ShortExact := by
  let T (x : X) : CategoryTheory.Functor
      (TopCat.Sheaf (AddCommGrpCat.{v}) X) (AddCommGrpCat.{v}) :=
    TopCat.Sheaf.forget (AddCommGrpCat.{v}) X ⋙
    TopCat.Presheaf.stalkFunctor (AddCommGrpCat.{v}) x
  let S (x : X) := (canonicalExactSequence U F).map (T x)
  have hstalk (x : X) : (S x).ShortExact := by
    by_cases hx : x ∈ U
    · haveI : IsIso (S x).f := by
        change IsIso ((TopCat.Presheaf.stalkFunctor (AddCommGrpCat.{v}) x).map
          (canonicalExactSequenceLeft U F).hom)
        exact openAbelianSheafExtension_counit_stalk_map_isIso U F x hx
      rcases closedAbelianSheafDirectImage_stalk_outside
          (canonicalClosedSubset U) (canonicalClosedSubset_isClosed U)
          ((closedAbelianSheafRestriction (canonicalClosedSubset U)
            (canonicalClosedSubset_isClosed U)).obj F) x (by
              simpa [canonicalClosedSubset] using hx) with ⟨e⟩
      have hzero : IsZero (S x).X₃ :=
        IsZero.of_iso (isZero_zero (AddCommGrpCat.{v})) e
      haveI : Epi (S x).g := hzero.isInitial.epi_to _
      exact ShortComplex.ShortExact.mk'
        (((S x).exact_iff_epi (hzero.eq_zero_of_tgt _)).2 (by infer_instance))
        (by infer_instance) (by infer_instance)
    · have hxZ : x ∈ canonicalClosedSubset U := by
        simpa [canonicalClosedSubset] using hx
      haveI : IsIso (S x).g := by
        change IsIso ((TopCat.Presheaf.stalkFunctor (AddCommGrpCat.{v}) x).map
          (canonicalExactSequenceRight U F).hom)
        exact closedAbelianSheafRestriction_unit_stalk_map_isIso
          (canonicalClosedSubset U) (canonicalClosedSubset_isClosed U) F x hxZ
      rcases openAlgebraicSheafExtension_stalk_initial (AddCommGrpCat.{v}) U
          ((openSheafRestriction (AddCommGrpCat.{v}) U).obj F) x hx with ⟨e⟩
      have hzero : IsZero (S x).X₁ :=
        IsZero.of_iso (isZero_zero (AddCommGrpCat.{v}))
          (e ≪≫ HasZeroObject.zeroIsoInitial.symm)
      haveI : Mono (S x).f := hzero.isTerminal.mono_from _
      exact ShortComplex.ShortExact.mk'
        (((S x).exact_iff_mono (hzero.eq_zero_of_src _)).2 (by infer_instance))
        (by infer_instance) (by infer_instance)
  refine ShortComplex.ShortExact.mk'
    ((TopCat.Sheaf.exact_iff_stalkFunctor_map_exact
      (canonicalExactSequence U F)).2 fun x ↦ (hstalk x).exact) ?_ ?_
  · rw [TopCat.Presheaf.mono_iff_stalk_mono]
    intro x
    exact (hstalk x).mono_f
  · apply openAbelianSheaf_epi_of_stalk_map_epi
    intro x
    exact (hstalk x).epi_g

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
