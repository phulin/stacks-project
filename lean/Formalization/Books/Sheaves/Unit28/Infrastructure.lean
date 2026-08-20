import Formalization.Books.Sheaves.Unit27.Infrastructure
import Mathlib.Topology.Sheaves.Limits
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic

/-!
# Shared infrastructure for Chapter 28: Limits and colimits of presheaves

Presheaf limits and colimits are Mathlib's pointwise limits and colimits in a
functor category.  The displayed section and stalk comparisons are exposed
with the canonical evaluation isomorphisms and source-facing theorem names.
-/

namespace Formalization.Books.Sheaves.Unit22

-- The historical namespace is retained for API compatibility.

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe v

noncomputable section

/-! ## Pointwise limits and colimits -/

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

private abbrev cofiniteCounterexampleSpace : TopCat.{v} :=
  TopCat.of (CofiniteTopology (ULift.{v} ℕ))

private abbrev cofiniteCounterexamplePoint : cofiniteCounterexampleSpace :=
  CofiniteTopology.of ⟨0⟩

private theorem cofiniteNeighborhoodStrictRefinement
    (W : OpenNhds cofiniteCounterexamplePoint) :
    ∃ U : OpenNhds cofiniteCounterexamplePoint, U ≤ W ∧ ¬ W ≤ U := by
  have hWc : (W.1 : Set cofiniteCounterexampleSpace)ᶜ.Finite := by
    exact (CofiniteTopology.isOpen_iff.mp W.1.isOpen)
      ⟨cofiniteCounterexamplePoint, W.2⟩
  have hWinf : (W.1 : Set cofiniteCounterexampleSpace).Infinite :=
    Set.infinite_of_finite_compl hWc
  have hnot : ¬ (W.1 : Set cofiniteCounterexampleSpace) ⊆
      ({cofiniteCounterexamplePoint} : Set cofiniteCounterexampleSpace) := by
    intro hsub
    apply hWinf
    exact (Set.finite_singleton cofiniteCounterexamplePoint).subset hsub
  obtain ⟨y, hyW, hyx⟩ := Set.not_subset.mp hnot
  have hxy : cofiniteCounterexamplePoint ≠ y := by
    have hyx' : y ≠ cofiniteCounterexamplePoint := by
      simpa [Set.mem_singleton_iff] using hyx
    exact hyx'.symm
  let U : OpenNhds cofiniteCounterexamplePoint :=
    ⟨⟨(W.1 : Set cofiniteCounterexampleSpace) \ {y}, by
        rw [CofiniteTopology.isOpen_iff']
        right
        rw [Set.compl_sdiff]
        exact (Set.finite_singleton y).union hWc⟩,
      ⟨W.2, by simpa [Set.mem_singleton_iff] using hxy⟩⟩
  refine ⟨U, ?_, ?_⟩
  · change (U.1 : Set cofiniteCounterexampleSpace) ⊆
      (W.1 : Set cofiniteCounterexampleSpace)
    intro z hz
    exact hz.1
  · intro hWU
    change (W.1 : Set cofiniteCounterexampleSpace) ⊆
      (U.1 : Set cofiniteCounterexampleSpace) at hWU
    have hyU : y ∈ (U.1 : Set cofiniteCounterexampleSpace) := hWU hyW
    exact hyU.2 (by simp)

/-- Stalks do not preserve arbitrary limits in general. -/
theorem presheafStalkDoesNotPreserveAllLimits :
    ∃ (X : TopCat.{v}) (x : X),
      ¬ PreservesLimits (TopCat.Presheaf.stalkFunctor (Type v) x) := by
  refine ⟨cofiniteCounterexampleSpace, cofiniteCounterexamplePoint, ?_⟩
  let G : Discrete (OpenNhds cofiniteCounterexamplePoint) ⥤
      TopCat.Presheaf (Type v) cofiniteCounterexampleSpace :=
    Discrete.functor (fun U => coyoneda.obj (op (op U.1)))
  intro h
  let _ : PreservesLimits
      (TopCat.Presheaf.stalkFunctor (Type v) cofiniteCounterexamplePoint) := h
  have hp := isLimitOfPreserves
    (TopCat.Presheaf.stalkFunctor (Type v) cofiniteCounterexamplePoint)
    (limit.isLimit G)
  let legs : ∀ U : Discrete (OpenNhds cofiniteCounterexamplePoint), PUnit ⟶
      (TopCat.Presheaf.stalkFunctor (Type v) cofiniteCounterexamplePoint).obj
        (G.obj U) := fun U =>
    ↾fun _ : PUnit => colimit.ι
      ((OpenNhds.inclusion cofiniteCounterexamplePoint).op ⋙ G.obj U)
      (op U.as) (𝟙 _)
  let c : Cone (G ⋙
      TopCat.Presheaf.stalkFunctor (Type v) cofiniteCounterexamplePoint) :=
    { pt := PUnit
      π := Discrete.natTrans legs }
  let a := hp.lift c PUnit.unit
  obtain ⟨W, z, hz⟩ := Types.jointly_surjective' a
  obtain ⟨U, hUW, hnWU⟩ := cofiniteNeighborhoodStrictRefinement W.unop
  have q := (limit.π G (Discrete.mk U)).app (op W.unop.1) z
  have hq : (op U.1 ⟶ op (W.unop.1)) := q
  exact hnWU (leOfHom hq.unop)

private instance presheafStalkPreservesColimitsInstance {X : TopCat.{v}} (x : X) :
    PreservesColimits (TopCat.Presheaf.stalkFunctor (Type v) x) := by
  dsimp [TopCat.Presheaf.stalkFunctor]
  let : PreservesColimits
      ((Functor.whiskeringLeft (OpenNhds x)ᵒᵖ (Opens X)ᵒᵖ (Type v)).obj
        (OpenNhds.inclusion x).op) := by
    infer_instance
  let : PreservesColimits (colim : ((OpenNhds x)ᵒᵖ ⥤ Type v) ⥤ Type v) := by
    infer_instance
  infer_instance

/-- The finite-diagram stalk/limit comparison. -/
noncomputable def presheafFiniteLimitStalkIso {X : TopCat.{v}} {J : Type v}
    [Category.{v} J] [FinCategory J]
    (F : J ⥤ TopCat.Presheaf (Type v) X) (x : X) :
    (presheafLimit F).stalk x ≅
      limit (F ⋙ TopCat.Presheaf.stalkFunctor (Type v) x) := by
  letI := presheafStalkPreservesFiniteLimits x
  exact preservesLimitIso (TopCat.Presheaf.stalkFunctor (Type v) x) F

/- Stalks commute with arbitrary presheaf colimits. -/
theorem exists_presheafColimitStalkIso {X : TopCat.{v}} {J : Type v}
    [Category.{v} J]
    (F : J ⥤ TopCat.Presheaf (Type v) X) (x : X) :
    Nonempty ((presheafColimit F).stalk x ≅
      colimit (F ⋙ TopCat.Presheaf.stalkFunctor (Type v) x)) := by
  exact ⟨preservesColimitIso (TopCat.Presheaf.stalkFunctor (Type v) x) F⟩

/- Stalks commute with arbitrary presheaf colimits. -/
noncomputable def presheafColimitStalkIso {X : TopCat.{v}} {J : Type v}
    [Category.{v} J]
    (F : J ⥤ TopCat.Presheaf (Type v) X) (x : X) :
    (presheafColimit F).stalk x ≅
      colimit (F ⋙ TopCat.Presheaf.stalkFunctor (Type v) x) :=
  Classical.choice (exists_presheafColimitStalkIso F x)

end

end Formalization.Books.Sheaves.Unit22
