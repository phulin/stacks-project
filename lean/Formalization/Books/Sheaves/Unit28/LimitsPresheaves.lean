import Mathlib.Topology.Sheaves.Limits
import Mathlib.Topology.Sheaves.Stalks
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
import Mathlib.CategoryTheory.Limits.FilteredColimitCommutesFiniteLimit
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory

/-!
# Sheaves on Spaces, Chapter 28: Limits and colimits of presheaves

Set-valued presheaves are functors on the opposite category of opens.  Their
limits and colimits are therefore the canonical functor-category limits and
colimits, and evaluation gives the sectionwise comparison isomorphisms.  The
stalk assertions are recorded with the corresponding categorical preservation
interfaces and comparison isomorphisms.
-/

namespace Formalization.Books.Sheaves.Unit28

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe v

noncomputable section

/-! ## Pointwise limits and colimits -/

/- The source's existence assertion is the completeness and cocompleteness of
   the functor category of set-valued presheaves. -/

/-- The category of set-valued presheaves has all limits. -/
theorem presheaf_has_limits {X : TopCat.{v}} :
    HasLimits (TopCat.Presheaf (Type v) X) := by
  infer_instance

/-- The category of set-valued presheaves has all colimits. -/
theorem presheaf_has_colimits {X : TopCat.{v}} :
    HasColimitsOfSize.{v, v} (TopCat.Presheaf (Type v) X) := by
  infer_instance

/-- The limit of a diagram of set-valued presheaves. -/
noncomputable abbrev presheafLimit {X : TopCat.{v}} {J : Type v}
    [Category.{v} J] (F : J ⥤ TopCat.Presheaf (Type v) X) :
    TopCat.Presheaf (Type v) X :=
  limit F

/-- The colimit of a diagram of set-valued presheaves. -/
noncomputable abbrev presheafColimit {X : TopCat.{v}} {J : Type v}
    [Category.{v} J] (F : J ⥤ TopCat.Presheaf (Type v) X) :
    TopCat.Presheaf (Type v) X :=
  colimit F

/- The displayed section formulas are the pointwise functor-category
   comparison isomorphisms. -/

/-- The pointwise limit formula on sections over an open. -/
noncomputable def presheafLimitSectionsIso {X : TopCat.{v}} {J : Type v}
    [Category.{v} J] (F : J ⥤ TopCat.Presheaf (Type v) X) (U : Opens X) :
    (presheafLimit F).obj (op U) ≅
      limit (F ⋙ (evaluation (Opens X)ᵒᵖ (Type v)).obj (op U)) :=
  limitObjIsoLimitCompEvaluation F (op U)

/-- The pointwise colimit formula on sections over an open. -/
noncomputable def presheafColimitSectionsIso {X : TopCat.{v}} {J : Type v}
    [Category.{v} J] (F : J ⥤ TopCat.Presheaf (Type v) X) (U : Opens X) :
    (presheafColimit F).obj (op U) ≅
      colimit (F ⋙ (evaluation (Opens X)ᵒᵖ (Type v)).obj (op U)) :=
  colimitObjIsoColimitCompEvaluation F (op U)

/-! ## Stalks -/

/- The source's left-exactness assertion is exposed as preservation of finite
   limits.  The proof that the stalk colimit has this property is deferred to
   the proof stage. -/

/-- Stalks preserve finite limits of set-valued presheaves. -/
theorem presheafStalkPreservesFiniteLimits {X : TopCat.{v}} (x : X) :
    PreservesFiniteLimits (TopCat.Presheaf.stalkFunctor (Type v) x) := by
  dsimp [TopCat.Presheaf.stalkFunctor]
  let : PreservesFiniteLimits
      ((Functor.whiskeringLeft (OpenNhds x)ᵒᵖ (Opens X)ᵒᵖ (Type v)).obj
        (OpenNhds.inclusion x).op) := by
    infer_instance
  let : PreservesFiniteLimits
      (colim : ((OpenNhds x)ᵒᵖ ⥤ Type v) ⥤ Type v) := by
    infer_instance
  exact comp_preservesFiniteLimits _ _

/-- Stalks do not preserve arbitrary limits in general. -/
theorem presheafStalkDoesNotPreserveAllLimits :
    ∃ (X : TopCat.{v}) (x : X),
      ¬ PreservesLimits (TopCat.Presheaf.stalkFunctor (Type v) x) := by
  let X : TopCat.{v} := TopCat.of (CofiniteTopology (ULift.{v} ℕ))
  let x : X := CofiniteTopology.of ⟨0⟩
  let G : Discrete (OpenNhds x) ⥤ TopCat.Presheaf (Type v) X :=
    Discrete.functor (fun U => coyoneda.obj (op (op U.1)))
  refine ⟨X, x, ?_⟩
  intro h
  let _ : PreservesLimits (TopCat.Presheaf.stalkFunctor (Type v) x) := h
  have hp := isLimitOfPreserves
    (TopCat.Presheaf.stalkFunctor (Type v) x) (limit.isLimit G)
  let legs : ∀ U : Discrete (OpenNhds x), PUnit ⟶
      (TopCat.Presheaf.stalkFunctor (Type v) x).obj (G.obj U) := fun U =>
    ↾fun _ : PUnit => colimit.ι ((OpenNhds.inclusion x).op ⋙ G.obj U)
      (op U.as) (𝟙 _)
  let c : Cone (G ⋙ TopCat.Presheaf.stalkFunctor (Type v) x) :=
    { pt := PUnit
      π := Discrete.natTrans legs }
  let a := hp.lift c PUnit.unit
  obtain ⟨W, z, hz⟩ := Types.jointly_surjective' a
  have hsmaller : ∀ W : OpenNhds x, ∃ U : OpenNhds x, U ≤ W ∧ ¬ W ≤ U := by
    intro W
    have hWc : (W.1 : Set X)ᶜ.Finite := by
      exact (CofiniteTopology.isOpen_iff.mp W.1.isOpen) ⟨x, W.2⟩
    have hWinf : (W.1 : Set X).Infinite := Set.infinite_of_finite_compl hWc
    have hnot : ¬ (W.1 : Set X) ⊆ ({x} : Set X) := by
      intro hsub
      apply hWinf
      exact (Set.finite_singleton x).subset hsub
    obtain ⟨y, hyW, hyx⟩ := Set.not_subset.mp hnot
    have hxy : x ≠ y := by
      have hyx' : y ≠ x := by simpa [Set.mem_singleton_iff] using hyx
      exact hyx'.symm
    let U : OpenNhds x :=
      ⟨⟨(W.1 : Set X) \ {y}, by
          rw [CofiniteTopology.isOpen_iff']
          right
          rw [Set.compl_sdiff]
          exact (Set.finite_singleton y).union hWc⟩,
        ⟨W.2, by simpa [Set.mem_singleton_iff] using hxy⟩⟩
    refine ⟨U, ?_, ?_⟩
    · change (U.1 : Set X) ⊆ (W.1 : Set X)
      intro z hz
      exact hz.1
    · intro hWU
      change (W.1 : Set X) ⊆ (U.1 : Set X) at hWU
      have hyU : y ∈ (U.1 : Set X) := hWU hyW
      exact hyU.2 (by simp)
  obtain ⟨U, hUW, hnWU⟩ := hsmaller W.unop
  have q := (limit.π G (Discrete.mk U)).app (op W.unop.1) z
  have hq : (op U.1 ⟶ op (W.unop.1)) := q
  exact hnWU (leOfHom hq.unop)

/-- The finite-diagram stalk/limit comparison. -/
noncomputable def presheafFiniteLimitStalkIso {X : TopCat.{v}} {J : Type v}
    [Category.{v} J] [FinCategory J]
    (F : J ⥤ TopCat.Presheaf (Type v) X) (x : X) :
    (presheafLimit F).stalk x ≅
      limit (F ⋙ TopCat.Presheaf.stalkFunctor (Type v) x) := by
  letI := presheafStalkPreservesFiniteLimits x
  exact preservesLimitIso (TopCat.Presheaf.stalkFunctor (Type v) x) F

/- The stalk is a colimit functor applied after restriction to the category
   of neighborhoods, so it preserves arbitrary colimits. -/

/-- Stalks preserve arbitrary colimits of set-valued presheaves. -/
theorem presheafStalkPreservesColimits {X : TopCat.{v}} (x : X) :
    PreservesColimits (TopCat.Presheaf.stalkFunctor (Type v) x) := by
  dsimp [TopCat.Presheaf.stalkFunctor]
  let : PreservesColimits
      ((Functor.whiskeringLeft (OpenNhds x)ᵒᵖ (Opens X)ᵒᵖ (Type v)).obj
        (OpenNhds.inclusion x).op) := by
    infer_instance
  let : PreservesColimits (colim : ((OpenNhds x)ᵒᵖ ⥤ Type v) ⥤ Type v) := by
    infer_instance
  infer_instance

/-- The canonical stalk/colimit comparison isomorphism. -/
noncomputable def presheafColimitStalkIso {X : TopCat.{v}} {J : Type v}
    [Category.{v} J]
    (F : J ⥤ TopCat.Presheaf (Type v) X) (x : X) :
    (presheafColimit F).stalk x ≅
      colimit (F ⋙ TopCat.Presheaf.stalkFunctor (Type v) x) :=
  letI := presheafStalkPreservesColimits x
  preservesColimitIso (TopCat.Presheaf.stalkFunctor (Type v) x) F

end

end Formalization.Books.Sheaves.Unit28
