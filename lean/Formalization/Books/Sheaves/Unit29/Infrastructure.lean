import Formalization.Books.Sheaves.Unit28.Infrastructure
import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.Algebra.Group.ULift
import Mathlib.Algebra.Ring.Pi
import Mathlib.Topology.Spectral.Basic
import Mathlib.Topology.Spectral.Hom

/-!
# Shared infrastructure for Chapter 29: Limits and colimits of sheaves

This file records the canonical limit/colimit constructions for sheaves, their
section and stalk comparisons, the directed-colimit lemma, its counterexample,
and the two inverse-limit statements for spectral spaces.
-/

namespace Formalization.Books.Sheaves.Unit22

-- The historical namespace is retained for API compatibility.

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped ZeroObject
open Formalization.Books.Sheaves.Unit21

universe v u w

noncomputable section

/-! ## Limits and colimits -/

/-- The limit of a diagram of sheaves of objects of `C`. -/
noncomputable abbrev sheafLimit {X : TopCat.{v}} {C : Type (v + 1)}
    [Category.{v} C] [HasLimits C] {J : Type v} [Category.{v} J]
    (F : J ⥤ TopCat.Sheaf C X) : TopCat.Sheaf C X :=
  limit F

/-- The colimit of a diagram of set-valued sheaves. -/
noncomputable abbrev sheafColimit {X : TopCat.{v}} {J : Type u}
    [Category.{w} J]
    [HasWeakSheafify (Opens.grothendieckTopology X) (Type v)]
    [HasColimitsOfShape J (Type v)]
    (F : J ⥤ TopCat.Sheaf (Type v) X) [HasColimit F] :
    TopCat.Sheaf (Type v) X :=
  colimit F

/-- Sheaf-valued limits exist when the value category is complete. -/
theorem sheaf_has_limits {X : TopCat.{v}} {C : Type (v + 1)}
    [Category.{v} C] [HasLimits C] : HasLimits (TopCat.Sheaf C X) := by
  infer_instance

/-- Set-valued sheaf colimits exist. -/
theorem sheaf_has_colimits {X : TopCat.{v}}
    [HasWeakSheafify (Opens.grothendieckTopology X) (Type v)] :
    HasColimitsOfSize.{v, v} (TopCat.Sheaf (Type v) X) := by
  exact CategoryTheory.Sheaf.instHasColimitsOfSize

/- The sectionwise formula for a limit of set-valued sheaves. -/
theorem exists_sheafLimitSectionsIso {X : TopCat.{v}} {J : Type v}
    [Category.{v} J] (F : J ⥤ TopCat.Sheaf (Type v) X) (U : Opens X) :
    Nonempty ((sheafLimit F).presheaf.obj (op U) ≅
      limit (F ⋙ TopCat.Sheaf.forget (Type v) X ⋙
        (evaluation (Opens X)ᵒᵖ (Type v)).obj (op U))) := by
  let e := preservesLimitIso (TopCat.Sheaf.forget (Type v) X) F
  exact ⟨((evaluation (Opens X)ᵒᵖ (Type v)).obj (op U)).mapIso e ≪≫
    limitObjIsoLimitCompEvaluation
      (F ⋙ TopCat.Sheaf.forget (Type v) X) (op U)⟩

/- The sectionwise formula for a limit of set-valued sheaves. -/
noncomputable def sheafLimitSectionsIso {X : TopCat.{v}} {J : Type v}
    [Category.{v} J] (F : J ⥤ TopCat.Sheaf (Type v) X) (U : Opens X) :
    (sheafLimit F).presheaf.obj (op U) ≅
      limit (F ⋙ TopCat.Sheaf.forget (Type v) X ⋙
        (evaluation (Opens X)ᵒᵖ (Type v)).obj (op U)) :=
  Classical.choice (exists_sheafLimitSectionsIso F U)

/- Sheafification identifies a sheaf colimit with the sheafification of the
pointwise presheaf colimit. -/
theorem exists_sheafColimitSheafificationIso {X : TopCat.{v}}
    {J : Type v} [Category.{v} J]
    (F : J ⥤ TopCat.Sheaf (Type v) X) [HasColimit F]
    [HasColimit (F ⋙ TopCat.Sheaf.forget (Type v) X)] :
    Nonempty ((sheafColimit F).presheaf ≅
        (CategoryTheory.presheafToSheaf (Opens.grothendieckTopology X) (Type v)).obj
        (colimit (F ⋙ TopCat.Sheaf.forget (Type v) X)) |>.1) := by
  let G := F ⋙ TopCat.Sheaf.forget (Type v) X
  let E := colimit.cocone G
  let hE := colimit.isColimit G
  let hc := CategoryTheory.Sheaf.isColimitSheafifyCocone E hE
  exact ⟨(TopCat.Sheaf.forget (Type v) X).mapIso
    (IsColimit.coconePointUniqueUpToIso (colimit.isColimit F) hc)⟩

/- Sheafification identifies a sheaf colimit with the sheafification of the
pointwise presheaf colimit. -/
noncomputable def sheafColimitSheafificationIso {X : TopCat.{v}}
    {J : Type v} [Category.{v} J]
    (F : J ⥤ TopCat.Sheaf (Type v) X) [HasColimit F]
    [HasColimit (F ⋙ TopCat.Sheaf.forget (Type v) X)] :
    (sheafColimit F).presheaf ≅
        (CategoryTheory.presheafToSheaf (Opens.grothendieckTopology X) (Type v)).obj
        (colimit (F ⋙ TopCat.Sheaf.forget (Type v) X)) |>.1 :=
  Classical.choice (exists_sheafColimitSheafificationIso F)

/-- The inclusion of sheaves into presheaves preserves limits. -/
theorem sheafForgetPreservesLimits {X : TopCat.{v}} {C : Type (v + 1)}
    [Category.{v} C] [HasLimits C] :
    PreservesLimits (TopCat.Sheaf.forget C X) := by
  infer_instance

/-- The inclusion of sheaves into presheaves does not preserve arbitrary
colimits in general. -/
theorem sheafForgetDoesNotPreserveAllColimits :
    ∃ (X : TopCat.{v}),
      ¬ PreservesColimits (TopCat.Sheaf.forget (Type v) X) := by
  let X : TopCat.{v} := TopCat.of (CofiniteTopology (ULift.{v} ℕ))
  refine ⟨X, ?_⟩
  intro h
  let : PreservesColimits (TopCat.Sheaf.forget (Type v) X) := h
  let : HasLimits (TopCat.Sheaf (Type v) X) := sheaf_has_limits
  let : HasColimitsOfSize.{v, v} (TopCat.Sheaf (Type v) X) :=
    CategoryTheory.Sheaf.instHasColimitsOfSize
  let T : TopCat.Sheaf (Type v) X := limit (Functor.empty.{0} _)
  let F : Discrete Bool ⥤ TopCat.Sheaf (Type v) X :=
    Discrete.functor (fun _ => T)
  let G : Discrete Bool ⥤ TopCat.Presheaf (Type v) X :=
    F ⋙ TopCat.Sheaf.forget (Type v) X
  let Q : TopCat.Presheaf (Type v) X :=
    (Functor.const (Opens X)ᵒᵖ).obj (ULift.{v} Bool)
  let leg (b : Bool) : T.presheaf ⟶ Q :=
    { app := fun U => ConcreteCategory.ofHom
        (⟨fun _ : T.presheaf.obj U => (ULift.up b : ULift.{v} Bool)⟩ :
          TypeCat.Fun (T.presheaf.obj U) (Q.obj U))
      naturality := by intros; ext; rfl }
  let c : Cocone G :=
    { pt := Q
      ι := Discrete.natTrans (fun b => leg b.as) }
  let hp := isColimitOfPreserves
    (TopCat.Sheaf.forget (Type v) X) (colimit.isColimit F)
  let d := hp.desc c
  let U₀ : (Opens X)ᵒᵖ := op (⊥ : Opens X)
  let z : T.presheaf.obj U₀ :=
    ((Types.isTerminalEquivUnique _).toFun
      (TopCat.Sheaf.isTerminalOfEmpty T)).default
  let m₀ := ((TopCat.Sheaf.forget (Type v) X).map
      (colimit.ι F (Discrete.mk false))).app U₀ z
  let m₁ := ((TopCat.Sheaf.forget (Type v) X).map
      (colimit.ι F (Discrete.mk true))).app U₀ z
  have hm : m₀ = m₁ := by
    let hu : Unique ((colimit F).presheaf.obj U₀) :=
      (Types.isTerminalEquivUnique _).toFun
        (TopCat.Sheaf.isTerminalOfEmpty (colimit F))
    exact (hu.uniq m₀).trans (hu.uniq m₁).symm
  have h₀ := congr_fun
    (congrArg (fun q => q.app U₀) (hp.fac c (Discrete.mk false))) z
  have h₁ := congr_fun
    (congrArg (fun q => q.app U₀) (hp.fac c (Discrete.mk true))) z
  rw [NatTrans.comp_app] at h₀ h₁
  rw [types_comp] at h₀ h₁
  have h₀' : d.app U₀ m₀ = ULift.up false := by
    change d.app U₀ m₀ = ULift.up false at h₀
    exact h₀
  have h₁' : d.app U₀ m₁ = ULift.up true := by
    change d.app U₀ m₁ = ULift.up true at h₁
    exact h₁
  have hfalse : ULift.up false = ULift.up true := by
    calc
      ULift.up false = d.app U₀ m₀ := h₀'.symm
      _ = d.app U₀ m₁ := congrArg (d.app U₀) hm
      _ = ULift.up true := h₁'
  have : (false : Bool) = true := congrArg ULift.down hfalse
  cases this

/-- The inclusion of sheaves into presheaves need not preserve even finite
colimits. -/
theorem sheafForgetDoesNotPreserveFiniteColimits :
    ∃ (X : TopCat.{v}),
      ¬ PreservesFiniteColimits (TopCat.Sheaf.forget (Type v) X) := by
  let X : TopCat.{v} := TopCat.of (CofiniteTopology (ULift.{v} ℕ))
  refine ⟨X, ?_⟩
  intro h
  let : PreservesFiniteColimits (TopCat.Sheaf.forget (Type v) X) := h
  let : HasLimits (TopCat.Sheaf (Type v) X) := sheaf_has_limits
  let : HasColimitsOfSize.{v, v} (TopCat.Sheaf (Type v) X) :=
    CategoryTheory.Sheaf.instHasColimitsOfSize
  let T : TopCat.Sheaf (Type v) X := limit (Functor.empty.{0} _)
  let F : Discrete Bool ⥤ TopCat.Sheaf (Type v) X :=
    Discrete.functor (fun _ => T)
  let G : Discrete Bool ⥤ TopCat.Presheaf (Type v) X :=
    F ⋙ TopCat.Sheaf.forget (Type v) X
  let Q : TopCat.Presheaf (Type v) X :=
    (Functor.const (Opens X)ᵒᵖ).obj (ULift.{v} Bool)
  let leg (b : Bool) : T.presheaf ⟶ Q :=
    { app := fun U => ConcreteCategory.ofHom
        (⟨fun _ : T.presheaf.obj U => (ULift.up b : ULift.{v} Bool)⟩ :
          TypeCat.Fun (T.presheaf.obj U) (Q.obj U))
      naturality := by intros; ext; rfl }
  let c : Cocone G :=
    { pt := Q
      ι := Discrete.natTrans (fun b => leg b.as) }
  let hp := isColimitOfPreserves
    (TopCat.Sheaf.forget (Type v) X) (colimit.isColimit F)
  let d := hp.desc c
  let U₀ : (Opens X)ᵒᵖ := op (⊥ : Opens X)
  let z : T.presheaf.obj U₀ :=
    ((Types.isTerminalEquivUnique _).toFun
      (TopCat.Sheaf.isTerminalOfEmpty T)).default
  let m₀ := ((TopCat.Sheaf.forget (Type v) X).map
      (colimit.ι F (Discrete.mk false))).app U₀ z
  let m₁ := ((TopCat.Sheaf.forget (Type v) X).map
      (colimit.ι F (Discrete.mk true))).app U₀ z
  have hm : m₀ = m₁ := by
    let hu : Unique ((colimit F).presheaf.obj U₀) :=
      (Types.isTerminalEquivUnique _).toFun
        (TopCat.Sheaf.isTerminalOfEmpty (colimit F))
    exact (hu.uniq m₀).trans (hu.uniq m₁).symm
  have h₀ := congr_fun
    (congrArg (fun q => q.app U₀) (hp.fac c (Discrete.mk false))) z
  have h₁ := congr_fun
    (congrArg (fun q => q.app U₀) (hp.fac c (Discrete.mk true))) z
  rw [NatTrans.comp_app] at h₀ h₁
  rw [types_comp] at h₀ h₁
  have h₀' : d.app U₀ m₀ = ULift.up false := by
    change d.app U₀ m₀ = ULift.up false at h₀
    exact h₀
  have h₁' : d.app U₀ m₁ = ULift.up true := by
    change d.app U₀ m₁ = ULift.up true at h₁
    exact h₁
  have hfalse : ULift.up false = ULift.up true := by
    calc
      ULift.up false = d.app U₀ m₀ := h₀'.symm
      _ = d.app U₀ m₁ := congrArg (d.app U₀) hm
      _ = ULift.up true := h₁'
  have : (false : Bool) = true := congrArg ULift.down hfalse
  cases this

/-- Sheafification preserves all colimits. -/
theorem sheafificationPreservesColimits {X : TopCat.{v}}
    {C : Type (v + 1)} [Category.{v} C] [HasColimits C]
    [HasWeakSheafify (Opens.grothendieckTopology X) C] :
    PreservesColimits
      (CategoryTheory.presheafToSheaf (Opens.grothendieckTopology X) C) := by
  exact (CategoryTheory.sheafificationAdjunction
    (Opens.grothendieckTopology X) C).leftAdjoint_preservesColimits

/-- Sheafification preserves finite limits. -/
theorem sheafificationPreservesFiniteLimits {X : TopCat.{v}}
    {C : Type (v + 1)} [Category.{v} C] [HasFiniteLimits C]
    [HasSheafify (Opens.grothendieckTopology X) C] :
    PreservesFiniteLimits
      (CategoryTheory.presheafToSheaf (Opens.grothendieckTopology X) C) := by
  infer_instance

private instance presheafStalkPreservesFiniteLimitsInstance
    {X : TopCat.{v}} (x : X) :
    PreservesFiniteLimits (TopCat.Presheaf.stalkFunctor (Type v) x) :=
  presheafStalkPreservesFiniteLimits x

private instance presheafStalkPreservesColimitsInstance
    {X : TopCat.{v}} (x : X) :
    PreservesColimits (TopCat.Presheaf.stalkFunctor (Type v) x) := by
  dsimp [TopCat.Presheaf.stalkFunctor]
  let : PreservesColimits
      ((Functor.whiskeringLeft (OpenNhds x)ᵒᵖ (Opens X)ᵒᵖ (Type v)).obj
        (OpenNhds.inclusion x).op) := by
    infer_instance
  let : PreservesColimits (colim : ((OpenNhds x)ᵒᵖ ⥤ Type v) ⥤ Type v) := by
    infer_instance
  infer_instance

private instance stalkFunctorMapUnitToSheafifyIsIsoInstance
    {X : TopCat.{v}} (x : X) (P : TopCat.Presheaf (Type v) X) :
    IsIso ((TopCat.Presheaf.stalkFunctor (Type v) x).map
      (CategoryTheory.toSheafify (Opens.grothendieckTopology X) P)) :=
  TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x (Type v) P

private def coverPrelocalPredicate {X : TopCat.{v}} (A B : Opens X) :
    TopCat.PrelocalPredicate (fun _ : X => ULift.{v} PUnit) where
  pred := fun {U} _ => U ≤ A ∨ U ≤ B
  res := by
    intro U V i f h
    rcases h with h | h
    · exact Or.inl (i.le.trans h)
    · exact Or.inr (i.le.trans h)

private abbrev coverPresheaf {X : TopCat.{v}} (A B : Opens X) :
    TopCat.Presheaf (Type v) X :=
  TopCat.subpresheafToTypes (coverPrelocalPredicate A B)

private def cofiniteCounterexampleSpace : TopCat.{v} :=
  TopCat.of (CofiniteTopology (ULift.{v} ℕ))

private def cofiniteCounterexamplePoint (n : ℕ) :
    cofiniteCounterexampleSpace.carrier :=
  CofiniteTopology.of (ULift.up n)

private def cofiniteCounterexampleOpenA (n : ℕ) :
    Opens cofiniteCounterexampleSpace :=
  ⟨{x | x ≠ cofiniteCounterexamplePoint (2 * n)}, by
    change IsOpen ({x : CofiniteTopology (ULift.{v} ℕ) |
      x ≠ CofiniteTopology.of (ULift.up (2 * n))} :
      Set (CofiniteTopology (ULift.{v} ℕ)))
    rw [CofiniteTopology.isOpen_iff']
    right
    rw [Set.compl_ofPred]
    apply Set.Finite.subset
      (Set.finite_singleton (CofiniteTopology.of (ULift.up (2 * n))))
    intro y hy
    exact not_ne_iff.mp hy⟩

private def cofiniteCounterexampleOpenB (n : ℕ) :
    Opens cofiniteCounterexampleSpace :=
  ⟨{x | x ≠ cofiniteCounterexamplePoint (2 * n + 1)}, by
    change IsOpen ({x : CofiniteTopology (ULift.{v} ℕ) |
      x ≠ CofiniteTopology.of (ULift.up (2 * n + 1))} :
      Set (CofiniteTopology (ULift.{v} ℕ)))
    rw [CofiniteTopology.isOpen_iff']
    right
    rw [Set.compl_ofPred]
    apply Set.Finite.subset
      (Set.finite_singleton (CofiniteTopology.of (ULift.up (2 * n + 1))))
    intro y hy
    exact not_ne_iff.mp hy⟩

private theorem cofiniteCounterexampleOpenCover (n : ℕ) :
    cofiniteCounterexampleOpenA n ⊔ cofiniteCounterexampleOpenB n = ⊤ := by
  ext x
  simp [cofiniteCounterexampleOpenA, cofiniteCounterexampleOpenB]
  by_cases hx : x = cofiniteCounterexamplePoint (2 * n)
  · right
    intro hx'
    have hpoint : cofiniteCounterexamplePoint (2 * n) =
        cofiniteCounterexamplePoint (2 * n + 1) := hx.symm.trans hx'
    have hnat : 2 * n = 2 * n + 1 := by
      exact ULift.up.inj (CofiniteTopology.of.injective hpoint)
    omega
  · exact Or.inl hx

private theorem cofiniteCounterexampleNoCover {U : Opens cofiniteCounterexampleSpace}
    (x : cofiniteCounterexampleSpace) (hx : x ∈ U)
    (hU : ∀ n, U ≤ cofiniteCounterexampleOpenA n ∨
      U ≤ cofiniteCounterexampleOpenB n) : False := by
  classical
  have hfinite : ((U : Set cofiniteCounterexampleSpace)ᶜ).Finite := by
    rcases (CofiniteTopology.isOpen_iff' (s := (U : Set cofiniteCounterexampleSpace))).1 U.2 with
      h | h
    · exfalso
      have hx' : x ∈ (∅ : Set cofiniteCounterexampleSpace) := h ▸ hx
      simp only [Set.mem_empty_iff_false] at hx'
    · exact h
  let p : ℕ → cofiniteCounterexampleSpace := cofiniteCounterexamplePoint
  have hp_injective : Function.Injective p := by
    intro n m hnm
    exact ULift.up.inj (CofiniteTopology.of.injective hnm)
  let f : ℕ → cofiniteCounterexampleSpace := fun n =>
    if U ≤ cofiniteCounterexampleOpenA n then p (2 * n) else p (2 * n + 1)
  have hf_injective : Function.Injective f := by
    intro n m hnm
    by_cases hn : U ≤ cofiniteCounterexampleOpenA n
    · by_cases hm : U ≤ cofiniteCounterexampleOpenA m
      · have hnm' : p (2 * n) = p (2 * m) := by
          simpa only [f, if_pos hn, if_pos hm] using hnm
        have : 2 * n = 2 * m := hp_injective hnm'
        omega
      · have hnm' : p (2 * n) = p (2 * m + 1) := by
          simpa only [f, if_pos hn, if_neg hm] using hnm
        have : 2 * n = 2 * m + 1 := hp_injective hnm'
        omega
    · by_cases hm : U ≤ cofiniteCounterexampleOpenA m
      · have hnm' : p (2 * n + 1) = p (2 * m) := by
          simpa only [f, if_neg hn, if_pos hm] using hnm
        have : 2 * n + 1 = 2 * m := hp_injective hnm'
        omega
      · have hnm' : p (2 * n + 1) = p (2 * m + 1) := by
          simpa only [f, if_neg hn, if_neg hm] using hnm
        have : 2 * n + 1 = 2 * m + 1 := hp_injective hnm'
        omega
  have hf_mem : ∀ n, f n ∈ ((U : Set cofiniteCounterexampleSpace)ᶜ) := by
    intro n
    by_cases hn : U ≤ cofiniteCounterexampleOpenA n
    · have hn' : p (2 * n) ∉ (U : Set cofiniteCounterexampleSpace) := by
        intro h
        have h' := hn h
        simp [p, cofiniteCounterexampleOpenA] at h'
      change f n ∈ ((U : Set cofiniteCounterexampleSpace)ᶜ)
      simp only [f, if_pos hn]
      exact hn'
    · have hnB := (hU n).resolve_left hn
      have hn' : p (2 * n + 1) ∉ (U : Set cofiniteCounterexampleSpace) := by
        intro h
        have h' := hnB h
        simp [p, cofiniteCounterexampleOpenB] at h'
      change f n ∈ ((U : Set cofiniteCounterexampleSpace)ᶜ)
      simp only [f, if_neg hn]
      exact hn'
  have hrange : (Set.range f).Infinite := Set.infinite_range_of_injective hf_injective
  exact hrange (hfinite.subset (by
    rintro _ ⟨n, rfl⟩
    exact hf_mem n))

private theorem coverPresheaf_stalk_subsingleton
    {A B : Opens cofiniteCounterexampleSpace} (x : cofiniteCounterexampleSpace) :
    Subsingleton ((TopCat.Presheaf.stalkFunctor (Type v) x).obj
      (coverPresheaf A B)) := by
  constructor
  intro a b
  dsimp [TopCat.Presheaf.stalk, TopCat.Presheaf.stalkFunctor] at a b
  obtain ⟨U, zU, rfl⟩ := Types.jointly_surjective' a
  obtain ⟨V, zV, rfl⟩ := Types.jointly_surjective' b
  let iU : (unop U ⊓ unop V) ⟶ unop U := OpenNhds.infLELeft _ _
  let iV : (unop U ⊓ unop V) ⟶ unop V := OpenNhds.infLERight _ _
  apply Types.colimit_sound' iU.op iV.op
  apply Subtype.ext
  funext y
  exact Subsingleton.elim _ _

private theorem coverPresheaf_stalk_nonempty
    {A B : Opens cofiniteCounterexampleSpace}
    (hcover : A ⊔ B = ⊤) (x : cofiniteCounterexampleSpace) :
    Nonempty ((TopCat.Presheaf.stalkFunctor (Type v) x).obj
      (coverPresheaf A B)) := by
  have hx : x ∈ A ∨ x ∈ B := by
    have : x ∈ A ⊔ B := by simp [hcover]
    simp only [Opens.mem_sup] at this
    exact this
  rcases hx with hx | hx
  · let U : OpenNhds x := ⟨A, hx⟩
    let f : ∀ y : A, ULift.{v} PUnit :=
      fun _ => ULift.up PUnit.unit
    have hf : (coverPrelocalPredicate A B).pred f := Or.inl le_rfl
    exact ⟨(coverPresheaf A B).germ A x U.2 ⟨f, hf⟩⟩
  · let U : OpenNhds x := ⟨B, hx⟩
    let f : ∀ y : B, ULift.{v} PUnit :=
      fun _ => ULift.up PUnit.unit
    have hf : (coverPrelocalPredicate A B).pred f := Or.inr le_rfl
    exact ⟨(coverPresheaf A B).germ B x U.2 ⟨f, hf⟩⟩

private noncomputable abbrev terminalSheaf (X : TopCat.{v}) : TopCat.Sheaf (Type v) X :=
  limit (Functor.empty.{0} _)

private theorem terminalSheaf_stalk_subsingleton (X : TopCat.{v}) (x : X) :
    Subsingleton ((TopCat.Presheaf.stalkFunctor (Type v) x).obj
      (terminalSheaf X).presheaf) := by
  have hsec : ∀ U : Opens X,
      Subsingleton ((terminalSheaf X).presheaf.obj (op U)) := by
    intro U
    let F := Functor.empty.{0} (TopCat.Sheaf (Type v) X)
    let e := preservesLimitIso (TopCat.Sheaf.forget (Type v) X) F
    let e' := ((evaluation (Opens X)ᵒᵖ (Type v)).obj (op U)).mapIso e
    let e'' := e' ≪≫ limitObjIsoLimitCompEvaluation
      (F ⋙ TopCat.Sheaf.forget (Type v) X) (op U)
    let G := F ⋙ TopCat.Sheaf.forget (Type v) X ⋙
      (evaluation (Opens X)ᵒᵖ (Type v)).obj (op U)
    let ht : IsTerminal (limit G) :=
      (isLimitEquivIsTerminalOfIsEmpty (Type v)
        (limit.cone G)).toFun (limit.isLimit G)
    let hu : Unique (limit G) := (Types.isTerminalEquivUnique _).toFun ht
    refine ⟨fun a b => ?_⟩
    have hab : e''.hom a = e''.hom b := (hu.uniq _).trans (hu.uniq _).symm
    rw [← Iso.hom_inv_id_apply e'' a, ← Iso.hom_inv_id_apply e'' b]
    exact congrArg (fun z => e''.inv z) hab
  constructor
  intro a b
  dsimp [TopCat.Presheaf.stalk, TopCat.Presheaf.stalkFunctor] at a b
  obtain ⟨U, aU, rfl⟩ := Types.jointly_surjective' a
  obtain ⟨V, bV, rfl⟩ := Types.jointly_surjective' b
  let W := unop U ⊓ unop V
  let iU : W ⟶ unop U := OpenNhds.infLELeft _ _
  let iV : W ⟶ unop V := OpenNhds.infLERight _ _
  letI : Subsingleton ((terminalSheaf X).presheaf.obj (op W.1)) := hsec W.1
  apply Types.colimit_sound' iU.op iV.op
  exact Subsingleton.elim _ _

private theorem terminalSheaf_stalk_nonempty (X : TopCat.{v}) (x : X) :
    Nonempty ((TopCat.Presheaf.stalkFunctor (Type v) x).obj
      (terminalSheaf X).presheaf) := by
  let U : Opens X := ⊤
  let F := Functor.empty.{0} (TopCat.Sheaf (Type v) X)
  let e := preservesLimitIso (TopCat.Sheaf.forget (Type v) X) F
  let e' := ((evaluation (Opens X)ᵒᵖ (Type v)).obj (op U)).mapIso e
  let e'' := e' ≪≫ limitObjIsoLimitCompEvaluation
    (F ⋙ TopCat.Sheaf.forget (Type v) X) (op U)
  let G := F ⋙ TopCat.Sheaf.forget (Type v) X ⋙
    (evaluation (Opens X)ᵒᵖ (Type v)).obj (op U)
  let ht : IsTerminal (limit G) :=
    (isLimitEquivIsTerminalOfIsEmpty (Type v)
      (limit.cone G)).toFun (limit.isLimit G)
  let hu : Unique (limit G) := (Types.isTerminalEquivUnique _).toFun ht
  let z : (terminalSheaf X).presheaf.obj (op U) := e''.inv hu.default
  exact ⟨(terminalSheaf X).presheaf.germ U x (by
    change x ∈ (⊤ : Opens X)
    trivial) z⟩

private noncomputable def terminalSheaf_isTerminal (X : TopCat.{v}) :
    IsTerminal (terminalSheaf X) :=
  (isLimitEquivIsTerminalOfIsEmpty (TopCat.Sheaf (Type v) X)
    (limit.cone (Functor.empty.{0} (TopCat.Sheaf (Type v) X)))).toFun
    (limit.isLimit (Functor.empty.{0} (TopCat.Sheaf (Type v) X)))

private theorem coverPresheaf_sheafification_to_terminal_isIso
    {A B : Opens cofiniteCounterexampleSpace}
    (hcover : A ⊔ B = ⊤) :
    IsIso ((terminalSheaf_isTerminal cofiniteCounterexampleSpace).from
      ((CategoryTheory.presheafToSheaf
      (Opens.grothendieckTopology cofiniteCounterexampleSpace) (Type v)).obj
        (coverPresheaf A B))) := by
  let P := coverPresheaf A B
  let L := CategoryTheory.presheafToSheaf
    (Opens.grothendieckTopology cofiniteCounterexampleSpace) (Type v)
  let T := terminalSheaf cofiniteCounterexampleSpace
  let f : L.obj P ⟶ T := (terminalSheaf_isTerminal _).from _
  change IsIso f
  let : ∀ x : cofiniteCounterexampleSpace,
      IsIso ((TopCat.Presheaf.stalkFunctor (Type v) x).map f.1) := fun x => by
    let u := (TopCat.Presheaf.stalkFunctor (Type v) x).map
      (CategoryTheory.toSheafify
        (Opens.grothendieckTopology cofiniteCounterexampleSpace) P)
    let g := (TopCat.Presheaf.stalkFunctor (Type v) x).map f.1
    let : Subsingleton ((TopCat.Presheaf.stalkFunctor (Type v) x).obj P) :=
      coverPresheaf_stalk_subsingleton x
    let : Unique ((TopCat.Presheaf.stalkFunctor (Type v) x).obj P) :=
      { default := Classical.choice (coverPresheaf_stalk_nonempty hcover x)
        uniq := fun _ => Subsingleton.elim _ _ }
    let : Subsingleton ((TopCat.Presheaf.stalkFunctor (Type v) x).obj T.presheaf) :=
      terminalSheaf_stalk_subsingleton _ _
    let : Unique ((TopCat.Presheaf.stalkFunctor (Type v) x).obj T.presheaf) :=
      { default := Classical.choice (terminalSheaf_stalk_nonempty _ _)
        uniq := fun _ => Subsingleton.elim _ _ }
    let : IsIso u := by infer_instance
    let : IsIso (u ≫ g) := by
      rw [CategoryTheory.isIso_iff_bijective]
      constructor
      · intro a b h
        exact Subsingleton.elim _ _
      · intro b
        exact ⟨default, Subsingleton.elim _ _⟩
    exact IsIso.of_isIso_comp_left u g
  exact TopCat.Presheaf.isIso_of_stalkFunctor_map_iso f

private noncomputable def coverPresheaf_sheafification_to_terminal_iso
    {A B : Opens cofiniteCounterexampleSpace}
    (hcover : A ⊔ B = ⊤) :
    (CategoryTheory.presheafToSheaf
      (Opens.grothendieckTopology cofiniteCounterexampleSpace) (Type v)).obj
        (coverPresheaf A B) ≅ terminalSheaf cofiniteCounterexampleSpace := by
  let L := CategoryTheory.presheafToSheaf
    (Opens.grothendieckTopology cofiniteCounterexampleSpace) (Type v)
  let T := terminalSheaf cofiniteCounterexampleSpace
  let f : L.obj (coverPresheaf A B) ⟶ T :=
    (terminalSheaf_isTerminal _).from _
  let hIso : IsIso f := coverPresheaf_sheafification_to_terminal_isIso hcover
  exact @asIso _ _ _ _ f hIso

/-- Sheafification does not preserve arbitrary limits in general. -/
theorem sheafificationDoesNotPreserveAllLimits :
    ∃ (X : TopCat.{v}),
      ¬ PreservesLimits
        (CategoryTheory.presheafToSheaf
          (Opens.grothendieckTopology X) (Type v)) := by
  refine ⟨cofiniteCounterexampleSpace, ?_⟩
  intro h
  let L := CategoryTheory.presheafToSheaf
    (Opens.grothendieckTopology cofiniteCounterexampleSpace) (Type v)
  letI : HasLimits (TopCat.Sheaf (Type v) cofiniteCounterexampleSpace) :=
    sheaf_has_limits
  letI : PreservesLimits L := h
  let J := Discrete (ULift.{v} ℕ)
  letI : HasLimitsOfShape J (TopCat.Sheaf (Type v) cofiniteCounterexampleSpace) :=
    HasLimits.has_limits_of_shape J
  let F : J ⥤ TopCat.Presheaf (Type v) cofiniteCounterexampleSpace :=
    Discrete.functor (fun n =>
      coverPresheaf (cofiniteCounterexampleOpenA n.down)
        (cofiniteCounterexampleOpenB n.down))
  letI : HasLimit (F ⋙ L) :=
    (inferInstance : HasLimitsOfShape J
      (TopCat.Sheaf (Type v) cofiniteCounterexampleSpace)).has_limit (F ⋙ L)
  let Q := limit F
  let x₀ := cofiniteCounterexamplePoint 0
  have hQempty : IsEmpty (Q.stalk x₀) := by
    constructor
    intro z
    obtain ⟨U, zU, rfl⟩ := Types.jointly_surjective' z
    let V : Opens cofiniteCounterexampleSpace := (unop U).1
    have hxV : x₀ ∈ V := (unop U).2
    have hUV : ∀ n, V ≤ cofiniteCounterexampleOpenA n ∨
        V ≤ cofiniteCounterexampleOpenB n := by
      intro n
      let j : J := Discrete.mk (ULift.up n)
      let eU := limitObjIsoLimitCompEvaluation F (op V)
      let y := (limit.π
        (F ⋙ (evaluation (Opens cofiniteCounterexampleSpace)ᵒᵖ (Type v)).obj (op V)) j)
        (eU.hom zU)
      simpa [F, j, coverPresheaf, coverPrelocalPredicate] using y.property
    exact cofiniteCounterexampleNoCover x₀ hxV hUV
  let T := terminalSheaf cofiniteCounterexampleSpace
  let e : ∀ j : J, L.obj (F.obj j) ≅ T := fun j =>
    coverPresheaf_sheafification_to_terminal_iso
      (cofiniteCounterexampleOpenCover j.as.down)
  let c : Cone (F ⋙ L) :=
    { pt := T
      π := Discrete.natTrans (fun j => (e j).inv) }
  let cLim : LimitCone (F ⋙ L) := getLimitCone (F ⋙ L)
  let q : T ⟶ cLim.cone.pt := cLim.isLimit.lift c
  have htarget : Nonempty
      (TopCat.Presheaf.stalk cLim.cone.pt.1 x₀) := by
    let zT := Classical.choice (terminalSheaf_stalk_nonempty cofiniteCounterexampleSpace x₀)
    exact ⟨(TopCat.Presheaf.stalkFunctor (Type v) x₀).map q.1 zT⟩
  let eLim := preservesLimitIso L F
  let u := (TopCat.Presheaf.stalkFunctor (Type v) x₀).map
    (CategoryTheory.toSheafify
      (Opens.grothendieckTopology cofiniteCounterexampleSpace) Q)
  let m := (TopCat.Presheaf.stalkFunctor (Type v) x₀).map eLim.hom.1
  haveI : IsIso u := by infer_instance
  haveI : IsIso m := by infer_instance
  let um := u ≫ m
  haveI : IsIso um := by infer_instance
  rcases htarget with ⟨y⟩
  exact hQempty.false (inv um y)

/-! ## Stalks -/

/- Stalks commute with finite limits of set-valued sheaves. -/
theorem exists_sheafFiniteLimitStalkIso {X : TopCat.{v}} {J : Type v}
    [Category.{v} J] [FinCategory J] (F : J ⥤ TopCat.Sheaf (Type v) X) (x : X) :
    Nonempty ((sheafLimit F).presheaf.stalk x ≅
      limit (F ⋙ TopCat.Sheaf.forget (Type v) X ⋙
        TopCat.Presheaf.stalkFunctor (Type v) x)) := by
  let e := preservesLimitIso (TopCat.Sheaf.forget (Type v) X) F
  let e' := preservesLimitIso (TopCat.Presheaf.stalkFunctor (Type v) x)
    (F ⋙ TopCat.Sheaf.forget (Type v) X)
  let e'' := ((TopCat.Presheaf.stalkFunctor (Type v) x).mapIso e).trans e'
  change Nonempty ((TopCat.Presheaf.stalkFunctor (Type v) x).obj
    ((TopCat.Sheaf.forget (Type v) X).obj (limit F)) ≅ _)
  exact Nonempty.intro (by simpa only [CategoryTheory.Functor.assoc] using e'')

/- Stalks commute with finite limits of set-valued sheaves. -/
noncomputable def sheafFiniteLimitStalkIso {X : TopCat.{v}} {J : Type v}
    [Category.{v} J] [FinCategory J] (F : J ⥤ TopCat.Sheaf (Type v) X) (x : X) :
    (sheafLimit F).presheaf.stalk x ≅
      limit (F ⋙ TopCat.Sheaf.forget (Type v) X ⋙
        TopCat.Presheaf.stalkFunctor (Type v) x) :=
  Classical.choice (exists_sheafFiniteLimitStalkIso F x)

/- Stalks commute with arbitrary colimits of set-valued sheaves. -/
theorem exists_sheafColimitStalkIso {X : TopCat.{v}} {J : Type v}
    [Category.{v} J] (F : J ⥤ TopCat.Sheaf (Type v) X) (x : X) [HasColimit F]
    [HasColimit (F ⋙ TopCat.Sheaf.forget (Type v) X ⋙
      TopCat.Presheaf.stalkFunctor (Type v) x)] :
    Nonempty ((sheafColimit F).presheaf.stalk x ≅
      colimit (F ⋙ TopCat.Sheaf.forget (Type v) X ⋙
        TopCat.Presheaf.stalkFunctor (Type v) x)) := by
  let G := F ⋙ TopCat.Sheaf.forget (Type v) X
  let e := Classical.choice (exists_sheafColimitSheafificationIso F)
  let e₁ := (TopCat.Presheaf.stalkFunctor (Type v) x).mapIso e
  let e₂ := asIso ((TopCat.Presheaf.stalkFunctor (Type v) x).map
    (CategoryTheory.toSheafify (Opens.grothendieckTopology X) (colimit G)))
  let e₃ := preservesColimitIso (TopCat.Presheaf.stalkFunctor (Type v) x) G
  let e₄ := e₁.trans (e₂.symm.trans e₃)
  change Nonempty ((TopCat.Presheaf.stalkFunctor (Type v) x).obj
    (sheafColimit F).presheaf ≅ _)
  exact Nonempty.intro (by
    simpa only [G, CategoryTheory.Functor.assoc] using e₄)

/- Stalks commute with arbitrary colimits of set-valued sheaves. -/
noncomputable def sheafColimitStalkIso {X : TopCat.{v}} {J : Type v}
    [Category.{v} J] (F : J ⥤ TopCat.Sheaf (Type v) X) (x : X) [HasColimit F]
    [HasColimit (F ⋙ TopCat.Sheaf.forget (Type v) X ⋙
      TopCat.Presheaf.stalkFunctor (Type v) x)] :
    (sheafColimit F).presheaf.stalk x ≅
      colimit (F ⋙ TopCat.Sheaf.forget (Type v) X ⋙
        TopCat.Presheaf.stalkFunctor (Type v) x) :=
  Classical.choice (exists_sheafColimitStalkIso F x)

/-! ## Directed colimits of sheaves -/

/-- The topological meaning of quasi-compact for an open in this chapter. -/
def QuasiCompactOpen {X : TopCat.{v}} (U : Opens X) : Prop :=
  IsCompact (U : Set X)

/- The canonical map from the colimit of sections to sections of the sheaf
colimit. -/
noncomputable def directedColimitSectionsMapCore {X : TopCat.{v}} {I : Type v}
    [Preorder I] [Nonempty I] [IsDirectedOrder I]
    (F : I ⥤ TopCat.Sheaf (Type v) X) (U : Opens X) [HasColimit F]
    [HasColimit (F ⋙ TopCat.Sheaf.forget (Type v) X ⋙
      (evaluation (Opens X)ᵒᵖ (Type v)).obj (op U))] :
    colimit (F ⋙ TopCat.Sheaf.forget (Type v) X ⋙
      (evaluation (Opens X)ᵒᵖ (Type v)).obj (op U)) →
      (sheafColimit F).presheaf.obj (op U) :=
  colimit.desc
    (F ⋙ TopCat.Sheaf.forget (Type v) X ⋙
      (evaluation (Opens X)ᵒᵖ (Type v)).obj (op U))
    (Functor.mapCocone
      (TopCat.Sheaf.forget (Type v) X ⋙
        (evaluation (Opens X)ᵒᵖ (Type v)).obj (op U))
      (colimit.cocone F))

theorem exists_directedColimitSectionsMap {X : TopCat.{v}} {I : Type v}
    [Preorder I] [Nonempty I] [IsDirectedOrder I]
    (F : I ⥤ TopCat.Sheaf (Type v) X) (U : Opens X) [HasColimit F]
    [HasColimit (F ⋙ TopCat.Sheaf.forget (Type v) X ⋙
      (evaluation (Opens X)ᵒᵖ (Type v)).obj (op U))] :
    Nonempty (colimit (F ⋙ TopCat.Sheaf.forget (Type v) X ⋙
      (evaluation (Opens X)ᵒᵖ (Type v)).obj (op U)) →
      (sheafColimit F).presheaf.obj (op U)) := by
  exact ⟨directedColimitSectionsMapCore F U⟩

/- The canonical map from the colimit of sections to sections of the sheaf
colimit. -/
noncomputable def directedColimitSectionsMap {X : TopCat.{v}} {I : Type v}
    [Preorder I] [Nonempty I] [IsDirectedOrder I]
    (F : I ⥤ TopCat.Sheaf (Type v) X) (U : Opens X) [HasColimit F]
    [HasColimit (F ⋙ TopCat.Sheaf.forget (Type v) X ⋙
      (evaluation (Opens X)ᵒᵖ (Type v)).obj (op U))] :
    colimit (F ⋙ TopCat.Sheaf.forget (Type v) X ⋙
      (evaluation (Opens X)ᵒᵖ (Type v)).obj (op U)) →
      (sheafColimit F).presheaf.obj (op U) :=
  directedColimitSectionsMapCore F U

/-- All transition maps in a directed system are injective on sections over
an open. -/
def DirectedSectionTransitionsInjective {X : TopCat.{v}} {I : Type v}
    [Preorder I] (F : I ⥤ TopCat.Sheaf (Type v) X) : Prop :=
  ∀ {i j : I} (hij : i ≤ j) (U : Opens X),
    Function.Injective ((F.map (homOfLE hij)).1.app (op U))

/-- A finite open cover with quasi-compact pairwise intersections, cofinal
 among all open covers of `U`. -/
def HasCofinalFiniteQuasiCompactOpenCover {X : TopCat.{v}} (U : Opens X) : Prop :=
  ∀ (K : Type v) (V : K → Opens X),
    (⨆ k, V k) = U →
      ∃ (J : Type v) (_ : Finite J) (W : J → Opens X),
        (⨆ j, W j) = U ∧
          (∀ j, ∃ k, W j ≤ V k) ∧
          (∀ j j', QuasiCompactOpen (W j ⊓ W j'))

private theorem colimitPresheaf_isSeparated_of_injective
    {X : TopCat.{v}} {I : Type v} [Preorder I] [Nonempty I]
    [IsDirectedOrder I] (F : I ⥤ TopCat.Sheaf (Type v) X)
    [HasColimit F]
    (hF : DirectedSectionTransitionsInjective F) :
    Presieve.IsSeparated (Opens.grothendieckTopology X)
      (colimit (F ⋙ TopCat.Sheaf.forget (Type v) X)) := by
  let G := F ⋙ TopCat.Sheaf.forget (Type v) X
  let P := colimit G
  intro V S hS fam t₁ t₂ ht₁ ht₂
  let hcolimV := isColimitOfPreserves
    ((evaluation (Opens X)ᵒᵖ (Type v)).obj (op V)) (colimit.isColimit G)
  let cV := ((evaluation (Opens X)ᵒᵖ (Type v)).obj (op V)).mapCocone
    (colimit.cocone G)
  obtain ⟨i₁, xi₁, hxi₁⟩ := Types.jointly_surjective _ hcolimV t₁
  obtain ⟨i₂, xi₂, hyi₂⟩ := Types.jointly_surjective _ hcolimV t₂
  obtain ⟨i, hi₁', hi₂'⟩ := exists_ge_ge i₁ i₂
  let hi₁ : i₁ ⟶ i := homOfLE hi₁'
  let hi₂ : i₂ ⟶ i := homOfLE hi₂'
  let xi := (F.map hi₁).1.app (op V) xi₁
  let yi := (F.map hi₂).1.app (op V) xi₂
  have ht₁rep : t₁ = (colimit.ι G i).app (op V) xi := by
    calc
      t₁ = (colimit.ι G i₁).app (op V) xi₁ := hxi₁.symm
      _ = (colimit.ι G i).app (op V) xi := by
        exact ConcreteCategory.congr_hom ((cV.ι.naturality hi₁).symm) xi₁
  have ht₂rep : t₂ = (colimit.ι G i).app (op V) yi := by
    calc
      t₂ = (colimit.ι G i₂).app (op V) xi₂ := hyi₂.symm
      _ = (colimit.ι G i).app (op V) yi := by
        exact ConcreteCategory.congr_hom ((cV.ι.naturality hi₂).symm) xi₂
  have hloc : ∀ {Y : Opens X} (f : Y ⟶ V) (_ : S f),
      P.map f.op t₁ = P.map f.op t₂ := by
    intro Y f hf
    exact (ht₁ f hf).trans (ht₂ f hf).symm
  have hxi : xi = yi := by
    have hsheaf : Presieve.IsSheaf (Opens.grothendieckTopology X) (F.obj i).1 :=
      (isSheaf_iff_isSheaf_of_type _ _).mp (F.obj i).2
    apply hsheaf S hS |>.isSeparatedFor.ext
    intro Y f hf
    have hloc' := hloc f hf
    have hmap (z : (F.obj i).1.obj (op V)) :
        P.map f.op ((colimit.ι G i).app (op V) z) =
          (colimit.ι G i).app (op Y) ((F.obj i).1.map f.op z) := by
      exact ConcreteCategory.congr_hom ((colimit.ι G i).naturality f.op).symm z
    have hloc'' :
        (colimit.ι G i).app (op Y) ((F.obj i).1.map f.op xi) =
          (colimit.ι G i).app (op Y) ((F.obj i).1.map f.op yi) := by
      calc
        _ = P.map f.op ((colimit.ι G i).app (op V) xi) := (hmap xi).symm
        _ = P.map f.op t₁ := congrArg (P.map f.op) ht₁rep.symm
        _ = P.map f.op t₂ := hloc'
        _ = P.map f.op ((colimit.ι G i).app (op V) yi) :=
          congrArg (P.map f.op) ht₂rep
        _ = _ := hmap yi
    let hcolim := isColimitOfPreserves
      ((evaluation (Opens X)ᵒᵖ (Type v)).obj (op Y)) (colimit.isColimit G)
    obtain ⟨j, g, hg⟩ :=
      (Types.FilteredColimit.isColimit_eq_iff' hcolim _ _).mp hloc''
    let gij : i ≤ j := leOfHom g
    have hg' :
        ((F.map (homOfLE gij)).1.app (op Y))
            ((F.obj i).1.map f.op xi) =
          ((F.map (homOfLE gij)).1.app (op Y))
            ((F.obj i).1.map f.op yi) := by
      change ((F.map g).1.app (op Y))
          ((F.obj i).1.map f.op xi) =
        ((F.map g).1.app (op Y))
          ((F.obj i).1.map f.op yi) at hg
      convert hg using 1 <;> rfl
    exact (hF gij Y) hg'
  calc
    t₁ = (colimit.ι G i).app (op V) xi := ht₁rep
    _ = (colimit.ι G i).app (op V) yi := congrArg _ hxi
    _ = t₂ := ht₂rep.symm

/-- Injectivity of the canonical directed-colimit section map when all
transition maps are injective. -/
theorem directedColimitSectionsMap_injective_of_injective
    {X : TopCat.{v}} {I : Type v} [Preorder I] [Nonempty I]
    [IsDirectedOrder I] (F : I ⥤ TopCat.Sheaf (Type v) X) (U : Opens X)
    [HasColimit F]
    [HasColimit (F ⋙ TopCat.Sheaf.forget (Type v) X ⋙
      (evaluation (Opens X)ᵒᵖ (Type v)).obj (op U))]
    (hF : DirectedSectionTransitionsInjective F) :
    Function.Injective (directedColimitSectionsMap F U) := by
  let G := F ⋙ TopCat.Sheaf.forget (Type v) X
  let P := colimit G
  have hsep := colimitPresheaf_isSeparated_of_injective F hF
  let J := Opens.grothendieckTopology X
  let E := colimit.cocone G
  let hE := colimit.isColimit G
  let hc := CategoryTheory.Sheaf.isColimitSheafifyCocone E hE
  let hcC := CategoryTheory.Sheaf.sheafifyCocone E
  let e := (TopCat.Sheaf.forget (Type v) X).mapIso
    (IsColimit.coconePointUniqueUpToIso (colimit.isColimit F) hc)
  let H := G ⋙ (evaluation (Opens X)ᵒᵖ (Type v)).obj (op U)
  let cU := ((evaluation (Opens X)ᵒᵖ (Type v)).obj (op U)).mapCocone E
  let hU := isColimitOfPreserves
    ((evaluation (Opens X)ᵒᵖ (Type v)).obj (op U)) hE
  let eu := IsColimit.coconePointUniqueUpToIso hU (colimit.isColimit H)
  let K := TopCat.Sheaf.forget (Type v) X ⋙
    (evaluation (Opens X)ᵒᵖ (Type v)).obj (op U)
  have hfactor : ∀ z : colimit H,
      e.hom.app (op U) (directedColimitSectionsMap F U z) =
        (CategoryTheory.toSheafify J P).app (op U) (eu.inv z) := by
    intro z
    obtain ⟨i, zi, hzi⟩ := Types.jointly_surjective H (colimit.isColimit H) z
    rw [← hzi]
    have hcore := ConcreteCategory.congr_hom
      (colimit.ι_desc
        ((TopCat.Sheaf.forget (Type v) X ⋙
          (evaluation (Opens X)ᵒᵖ (Type v)).obj (op U)).mapCocone
            (colimit.cocone F)) i) zi
    have heu := ConcreteCategory.congr_hom
      (IsColimit.comp_coconePointUniqueUpToIso_inv hU (colimit.isColimit H) i) zi
    have hsheafleg := congrArg (fun q => q.app (op U))
      (CategoryTheory.Sheaf.sheafifyCocone_ι_app_val E i)
    have hsheafleg' := ConcreteCategory.congr_hom hsheafleg zi
    have he := IsColimit.comp_coconePointUniqueUpToIso_hom
      (colimit.isColimit F) hc i
    have he' := congrArg (fun q =>
      ((TopCat.Sheaf.forget (Type v) X).map q).app (op U)) he
    have he'' := ConcreteCategory.congr_hom he' zi
    have h1 :
        (ConcreteCategory.hom (e.hom.app (op U)))
            (directedColimitSectionsMap F U
              ((ConcreteCategory.hom ((colimit.cocone H).ι.app i)) zi)) =
          (ConcreteCategory.hom (e.hom.app (op U)))
            ((ConcreteCategory.hom (((colimit.cocone F).ι.app i).1.app (op U))) zi) := by
      exact congrArg (e.hom.app (op U)) hcore
    have hmap := K.map_comp_apply
      ((colimit.cocone F).ι.app i)
      ((colimit.isColimit F).coconePointUniqueUpToIso hc).hom zi
    have h2 :
        (ConcreteCategory.hom (e.hom.app (op U)))
            ((ConcreteCategory.hom (((colimit.cocone F).ι.app i).1.app (op U))) zi) =
          (ConcreteCategory.hom
            (((TopCat.Sheaf.forget (Type v) X).map
              ((colimit.cocone F).ι.app i ≫
                ((colimit.isColimit F).coconePointUniqueUpToIso hc).hom)).app
            (op U))) zi := by
      change (K.map ((colimit.isColimit F).coconePointUniqueUpToIso hc).hom)
          ((K.map ((colimit.cocone F).ι.app i)) zi) =
        (K.map (((colimit.cocone F).ι.app i ≫
          ((colimit.isColimit F).coconePointUniqueUpToIso hc).hom)) zi)
      exact hmap.symm
    have h3 :
        (ConcreteCategory.hom
            (((TopCat.Sheaf.forget (Type v) X).map
              ((colimit.cocone F).ι.app i ≫
                ((colimit.isColimit F).coconePointUniqueUpToIso hc).hom)).app
              (op U))) zi =
          (ConcreteCategory.hom ((hcC.ι.app i).hom.app (op U))) zi := by
      exact he''
    have h4 :
        (ConcreteCategory.hom ((hcC.ι.app i).hom.app (op U))) zi =
          (ConcreteCategory.hom ((CategoryTheory.toSheafify J P).app (op U)))
            ((ConcreteCategory.hom (cU.ι.app i)) zi) := by
      rw [← ConcreteCategory.comp_apply]
      change
        (ConcreteCategory.hom ((hcC.ι.app i).hom.app (op U))) zi =
          (ConcreteCategory.hom
            ((E.ι.app i ≫ CategoryTheory.toSheafify J E.pt).app (op U))) zi
      exact hsheafleg'
    have h5 :
        (ConcreteCategory.hom ((CategoryTheory.toSheafify J P).app (op U)))
            ((ConcreteCategory.hom (cU.ι.app i)) zi) =
          (ConcreteCategory.hom ((CategoryTheory.toSheafify J P).app (op U)))
            ((ConcreteCategory.hom eu.inv)
              ((ConcreteCategory.hom ((colimit.cocone H).ι.app i)) zi)) := by
      exact congrArg ((CategoryTheory.toSheafify J P).app (op U)) heu.symm
    exact h1.trans (h2.trans (h3.trans (h4.trans h5)))
  intro x y hxy
  have hxy' := congrArg (e.hom.app (op U)) hxy
  rw [hfactor x, hfactor y] at hxy'
  have hsep' : ∀ (V : Opens X) (S : J.Cover V)
      (x y : P.obj (op V)),
      (∀ I : S.Arrow, P.map I.f.op x = P.map I.f.op y) → x = y := by
    intro V S x y h
    apply (hsep S.1 S.2).ext
    intro Y f hf
    exact h ⟨Y, f, hf⟩
  have hplus : ∀ (V : Opens X) (S : J.Cover V)
      (x y : (J.plusObj P).obj (op V)),
      (∀ I : S.Arrow, (J.plusObj P).map I.f.op x =
        (J.plusObj P).map I.f.op y) → x = y := by
    intro V S x y h
    exact CategoryTheory.GrothendieckTopology.Plus.sep P S x y h
  have hto1 := CategoryTheory.GrothendieckTopology.Plus.inj_of_sep
    P hsep' U
  have hto2 := CategoryTheory.GrothendieckTopology.Plus.inj_of_sep
    (J.plusObj P) hplus U
  have htoConcrete : Function.Injective ((J.toSheafify P).app (op U)) := by
    dsimp [CategoryTheory.GrothendieckTopology.toSheafify]
    intro a b hab
    apply hto1
    apply hto2
    rw [CategoryTheory.GrothendieckTopology.plusMap_toPlus] at hab
    change (ConcreteCategory.hom
      ((J.toPlus P).app (op U) ≫
        (J.toPlus (J.plusObj P)).app (op U))) a =
      (ConcreteCategory.hom
        ((J.toPlus P).app (op U) ≫
          (J.toPlus (J.plusObj P)).app (op U))) b at hab
    simpa only [CategoryTheory.types_comp_apply] using hab
  have hto : Function.Injective ((CategoryTheory.toSheafify J P).app (op U)) := by
    let M := CategoryTheory.sheafifyLift J (J.toSheafify P)
      (CategoryTheory.GrothendieckTopology.sheafify_isSheaf J P)
    have hM := CategoryTheory.toSheafify_sheafifyLift
      (J := J) (P := P) (Q := J.sheafify P) (J.toSheafify P)
      (CategoryTheory.GrothendieckTopology.sheafify_isSheaf J P)
    intro a b hab
    apply htoConcrete
    have habM := congrArg (ConcreteCategory.hom (M.app (op U))) hab
    have hM' := congrArg (fun q => q.app (op U)) hM
    have hMa := ConcreteCategory.congr_hom hM' a
    have hMb := ConcreteCategory.congr_hom hM' b
    calc
      (ConcreteCategory.hom ((J.toSheafify P).app (op U))) a =
          (ConcreteCategory.hom (M.app (op U)))
            ((ConcreteCategory.hom ((CategoryTheory.toSheafify J P).app (op U))) a) := by
        simpa only [M, NatTrans.comp_app, CategoryTheory.types_comp_apply] using hMa.symm
      _ = (ConcreteCategory.hom (M.app (op U)))
          ((ConcreteCategory.hom ((CategoryTheory.toSheafify J P).app (op U))) b) := habM
      _ = (ConcreteCategory.hom ((J.toSheafify P).app (op U))) b := by
        simpa only [M, NatTrans.comp_app, CategoryTheory.types_comp_apply] using hMb
  have hinv := hto hxy'
  have hxy'' := congrArg (ConcreteCategory.hom eu.hom) hinv
  simpa using hxy''

/-- Injectivity of the canonical map over a quasi-compact open. -/
theorem directedColimitSectionsMap_injective_of_quasiCompact
    {X : TopCat.{v}} {I : Type v} [Preorder I] [Nonempty I]
    [IsDirectedOrder I] (F : I ⥤ TopCat.Sheaf (Type v) X) (U : Opens X)
    [HasColimit F]
    [HasColimit (F ⋙ TopCat.Sheaf.forget (Type v) X ⋙
      (evaluation (Opens X)ᵒᵖ (Type v)).obj (op U))]
    (hU : QuasiCompactOpen U) :
    Function.Injective (directedColimitSectionsMap F U) := by
  sorry

/-- Bijectivity over a quasi-compact open when all transition maps are
injective. -/
theorem directedColimitSectionsMap_bijective_of_quasiCompact_of_injective
    {X : TopCat.{v}} {I : Type v} [Preorder I] [Nonempty I]
    [IsDirectedOrder I] (F : I ⥤ TopCat.Sheaf (Type v) X) (U : Opens X)
    [HasColimit F]
    [HasColimit (F ⋙ TopCat.Sheaf.forget (Type v) X ⋙
      (evaluation (Opens X)ᵒᵖ (Type v)).obj (op U))]
    (hU : QuasiCompactOpen U)
    (hF : DirectedSectionTransitionsInjective F) :
    Function.Bijective (directedColimitSectionsMap F U) := by
  sorry

/-- Bijectivity when the open has a cofinal finite cover with quasi-compact
pairwise intersections. -/
theorem directedColimitSectionsMap_bijective_of_cofinal_cover
    {X : TopCat.{v}} {I : Type v} [Preorder I] [Nonempty I]
    [IsDirectedOrder I] (F : I ⥤ TopCat.Sheaf (Type v) X) (U : Opens X)
    [HasColimit F]
    [HasColimit (F ⋙ TopCat.Sheaf.forget (Type v) X ⋙
      (evaluation (Opens X)ᵒᵖ (Type v)).obj (op U))]
    (hU : HasCofinalFiniteQuasiCompactOpenCover U) :
    Function.Bijective (directedColimitSectionsMap F U) := by
  sorry

/-! ## The tail example -/

/-! The tail products occurring in the global-section computation. -/

/-- The directed system `∏_{m ≥ n} ℤ` with transition maps given by
restriction to a later tail, regarded as a diagram of abelian groups.
`ULift` only adjusts the universe to the one used by the sheaf counterexample. -/
abbrev tailIndex (n : ℕ) := {m : ℕ // n ≤ m}

def tailProductEquiv (n : ℕ) :
    ULift.{v} (∀ _ : tailIndex n, ℤ) ≃ (∀ _ : tailIndex n, ℤ) :=
  { toFun := ULift.down
    invFun := ULift.up
    left_inv := by intro x; cases x; rfl
    right_inv := by intro x; rfl }

instance tailProductBaseAddCommGroup (n : ℕ) :
    AddCommGroup (∀ _ : tailIndex n, ℤ) :=
  @Pi.addCommGroup (tailIndex n) (fun _ => ℤ) (fun _ => inferInstance)

noncomputable instance tailProductAddCommGroup (n : ℕ) :
    AddCommGroup (ULift.{v} (∀ _ : tailIndex n, ℤ)) :=
  (tailProductEquiv n).addCommGroup

def tailProductDiagram : ℕ ⥤ AddCommGrpCat.{v} where
  obj n := AddCommGrpCat.of (ULift.{v} (∀ _ : tailIndex n, ℤ))
  map f := AddCommGrpCat.ofHom {
    toFun := fun s => ⟨fun m => s.down ⟨m.1, le_trans (leOfHom f) m.2⟩⟩
    map_zero' := by sorry
    map_add' := by sorry }
  map_id := by
    intro n
    rfl
  map_comp := by
    intro n m k f g
    rfl

/-- Data expressing the tail-space counterexample to unrestricted sectionwise
directed colimits.  The fields deliberately retain the source's stalk and
global-section conclusions. -/
structure DirectedColimitSectionsCounterexample where
  X : TopCat.{v}
  s1 : X.carrier
  s2 : X.carrier
  xi : ℕ → X.carrier
  points : ∀ x : X.carrier, x = s1 ∨ x = s2 ∨ ∃ n, x = xi n
  s1_ne_s2 : s1 ≠ s2
  xi_injective : Function.Injective xi
  s1_ne_xi : ∀ n, s1 ≠ xi n
  s2_ne_xi : ∀ n, s2 ≠ xi n
  open_iff : ∀ U : Set X.carrier, IsOpen U ↔
    (U s1 → ∀ n, U (xi n)) ∧ (U s2 → ∀ n, U (xi n))
  U : ℕ → Opens X
  U_carrier : ∀ n x, (U n : Set X.carrier) x ↔
    ∃ m : ℕ, n ≤ m ∧ x = xi m
  j : ∀ n, (Opens.toTopCat X).obj (U n) ⟶ X
  j_is_inclusion : ∀ n, j n = Opens.inclusion' (U n)
  F : ℕ ⥤ TopCat.Sheaf AddCommGrpCat.{v} X
  F_is_pushforward_constant :
    ∀ n, F.obj n = (abelianSheafPushforward (j n)).obj
      ((CategoryTheory.constantSheaf
        (Opens.grothendieckTopology ((Opens.toTopCat X).obj (U n)))
        AddCommGrpCat).obj (AddCommGrpCat.of (ULift.{v} ℤ)))
  F_colimit_cocone : Cocone F
  F_colimit_is_colimit : IsColimit F_colimit_cocone
  stalk_tail_zero : ∀ {n m}, m < n →
    Nonempty ((F.obj n).presheaf.stalk (xi m) ≅ 0)
  M : AddCommGrpCat.{v}
  M_nontrivial : Nontrivial M
  M_is_tail_colimit : Nonempty (M ≅ colimit tailProductDiagram)
  stalk_s1 : Nonempty (F_colimit_cocone.pt.presheaf.stalk s1 ≅ M)
  stalk_s2 : Nonempty (F_colimit_cocone.pt.presheaf.stalk s2 ≅ M)
  stalk_colimit_tail_zero : ∀ n,
    Nonempty (F_colimit_cocone.pt.presheaf.stalk (xi n) ≅ 0)
  two_skyscraper_sum : TopCat.Sheaf AddCommGrpCat.{v} X
  two_skyscraper_sum_inl : abelianSkyscraperSheaf s1 M ⟶ two_skyscraper_sum
  two_skyscraper_sum_inr : abelianSkyscraperSheaf s2 M ⟶ two_skyscraper_sum
  two_skyscraper_sum_is_coproduct :
    IsColimit (BinaryCofan.mk two_skyscraper_sum_inl two_skyscraper_sum_inr)
  sheaf_is_two_skyscrapers :
    Nonempty (F_colimit_cocone.pt ≅ two_skyscraper_sum)
  global_sections :
    Nonempty (F_colimit_cocone.pt.presheaf.obj (op (⊤ : Opens X)) ≃+
      (M × M))
  colimit_global_sections :
    Nonempty (colimit (F ⋙ TopCat.Sheaf.forget AddCommGrpCat X ⋙
      (evaluation (Opens X)ᵒᵖ AddCommGrpCat).obj (op (⊤ : Opens X))) ≅ M)

/-- The tail-space data described in the source exists. -/
theorem exists_directedColimitSectionsCounterexample :
    Nonempty DirectedColimitSectionsCounterexample := by
  sorry

/-! ## Inverse limits of spectral spaces -/

/-- A diagram of spectral spaces and spectral transition maps. -/
def IsSpectralSpaceDiagram {I : Type u} [Category.{w} I]
    (X : I ⥤ TopCat.{v}) : Prop :=
  (∀ i, SpectralSpace (X.obj i)) ∧
    (∀ {j i} (a : j ⟶ i), IsSpectralMap (X.map a : X.obj j → X.obj i))

/-- The inverse-limit space of a diagram of topological spaces. -/
noncomputable abbrev spectralInverseLimitSpace {I : Type u} [Category.{w} I]
    (X : I ⥤ TopCat.{v}) [HasLimit X] : TopCat.{v} :=
  limit X

/-- The projection from the inverse-limit space to one of its factors. -/
noncomputable abbrev spectralInverseLimitProjection {I : Type u} [Category.{w} I]
    (X : I ⥤ TopCat.{v}) [HasLimit X] (i : I) :
    spectralInverseLimitSpace X ⟶ X.obj i :=
  limit.π X i


/-! The colimit transition maps go from an arrow `a : j ⟶ i` to a
refinement `a ≫ b : k ⟶ i`; hence the useful indexing category is the
opposite of the costructured-arrow category. -/

abbrev spectralPullbackSectionsIndex
    {I : Type u} [Category.{w} I] (i : I) :=
  (CostructuredArrow (𝟭 I) i)ᵒᵖ

/-- The section type attached to an arrow `a : j ⟶ i` in the inverse system. -/
noncomputable abbrev spectralPullbackSectionsAt
    {I : Type u} [Category.{w} I] (X : I ⥤ TopCat.{v}) (i : I)
    (G : TopCat.Sheaf (Type v) (X.obj i)) (Ui : Opens (X.obj i))
    (a : spectralPullbackSectionsIndex i) : Type v :=
  ((pullbackSheaf (X.map a.unop.hom)).obj G).presheaf.obj
    (op ((Opens.map (X.map a.unop.hom)).obj Ui))

/-- The canonical transition on sections induced by refinement of inverse-system
arrows. -/
noncomputable def spectralPullbackSectionsTransition
    {I : Type u} [Category.{w} I] (X : I ⥤ TopCat.{v}) (i : I)
    (G : TopCat.Sheaf (Type v) (X.obj i)) (Ui : Opens (X.obj i))
    {a b : spectralPullbackSectionsIndex i} (h : a ⟶ b) :
    spectralPullbackSectionsAt X i G Ui a →
      spectralPullbackSectionsAt X i G Ui b := by
  let f := X.map h.unop.left
  let fa := X.map a.unop.hom
  let fb := X.map b.unop.hom
  have hcomp : f ≫ fa = fb := by
    rw [← X.map_comp]
    simpa using congrArg X.map (CostructuredArrow.w h.unop)
  let ψ : (pullbackSheaf f).obj ((pullbackSheaf fa).obj G) ⟶
      (pullbackSheaf fb).obj G := by
    rw [← hcomp]
    exact (pullbackSheafCompIso f fa).inv.app G
  let ξ : FMap f ((pullbackSheaf fa).obj G) ((pullbackSheaf fb).obj G) :=
    pullbackSheafHomEquiv f _ _ ψ
  intro s
  have hopen : (Opens.map f).obj ((Opens.map fa).obj Ui) =
      (Opens.map fb).obj Ui := by
    rw [← Opens.map_comp_obj, hcomp]
  simpa [spectralPullbackSectionsAt, f, fa, fb, ψ, ξ, fMapAt, hopen] using
    fMapAt ξ ((Opens.map fa).obj Ui) s

/-- The diagram of pullback sections indexed by all arrows into `i`.
Its object part is the displayed source expression; the morphism part uses
the canonical pullback comparison for a map of arrows. -/
structure SpectralPullbackSectionsDiagramData
    {I : Type u} [Category.{w} I] (X : I ⥤ TopCat.{v}) (i : I)
    (G : TopCat.Sheaf (Type v) (X.obj i)) (Ui : Opens (X.obj i)) where
  diagram : spectralPullbackSectionsIndex i ⥤ Type v
  obj_eq : ∀ a, diagram.obj a = spectralPullbackSectionsAt X i G Ui a
  map_eq : ∀ {a b} (h : a ⟶ b),
    eqToHom (obj_eq a).symm ≫ diagram.map h ≫ eqToHom (obj_eq b) =
      spectralPullbackSectionsTransition X i G Ui h

theorem exists_spectralPullbackSectionsDiagram
    {I : Type u} [Category.{w} I] (X : I ⥤ TopCat.{v}) (i : I)
    (G : TopCat.Sheaf (Type v) (X.obj i)) (Ui : Opens (X.obj i)) :
    Nonempty (SpectralPullbackSectionsDiagramData X i G Ui) := by
  sorry

/-- The diagram of pullback sections indexed by all arrows into `i`.
Its object part is the displayed source expression; the morphism part uses
the canonical pullback comparison for a map of arrows. -/
noncomputable def spectralPullbackSectionsDiagram
    {I : Type u} [Category.{w} I] (X : I ⥤ TopCat.{v}) (i : I)
    (G : TopCat.Sheaf (Type v) (X.obj i)) (Ui : Opens (X.obj i)) :
    spectralPullbackSectionsIndex i ⥤ Type v :=
  (Classical.choice (exists_spectralPullbackSectionsDiagram X i G Ui)).diagram

theorem spectralPullbackSectionsDiagram_obj
    {I : Type u} [Category.{w} I] (X : I ⥤ TopCat.{v}) (i : I)
    (G : TopCat.Sheaf (Type v) (X.obj i)) (Ui : Opens (X.obj i))
    (a : spectralPullbackSectionsIndex i) :
    (spectralPullbackSectionsDiagram X i G Ui).obj a =
      spectralPullbackSectionsAt X i G Ui a :=
  (Classical.choice (exists_spectralPullbackSectionsDiagram X i G Ui)).obj_eq a

/-- The colimit of the pullback-section diagram over arrows `a : j ⟶ i`. -/
noncomputable abbrev spectralPullbackSectionsColimit
    {I : Type u} [Category.{w} I] (X : I ⥤ TopCat.{v}) (i : I)
    (G : TopCat.Sheaf (Type v) (X.obj i)) (Ui : Opens (X.obj i))
    [HasColimit (spectralPullbackSectionsDiagram X i G Ui)] : Type v :=
  colimit (spectralPullbackSectionsDiagram X i G Ui)

/-- Computation of sections after pulling a sheaf back to a spectral inverse
limit. -/
theorem exists_computePullbackToSpectralLimitSections
    {I : Type u} [Category.{w} I] [IsCofiltered I]
    (X : I ⥤ TopCat.{v}) [HasLimit X]
    (hX : IsSpectralSpaceDiagram X) (i : I)
    (G : TopCat.Sheaf (Type v) (X.obj i)) (Ui : Opens (X.obj i))
    (hUi : QuasiCompactOpen Ui)
    [HasColimit (spectralPullbackSectionsDiagram X i G Ui)] :
    Nonempty (spectralPullbackSectionsColimit X i G Ui ≃
      ((pullbackSheaf (spectralInverseLimitProjection X i)).obj G).presheaf.obj
        (op ((Opens.map (spectralInverseLimitProjection X i)).obj Ui))) := by
  sorry

/-- Computation of sections after pulling a sheaf back to a spectral inverse
limit. -/
noncomputable def computePullbackToSpectralLimitSections
    {I : Type u} [Category.{w} I] [IsCofiltered I]
    (X : I ⥤ TopCat.{v}) [HasLimit X]
    (hX : IsSpectralSpaceDiagram X) (i : I)
    (G : TopCat.Sheaf (Type v) (X.obj i)) (Ui : Opens (X.obj i))
    (hUi : QuasiCompactOpen Ui)
    [HasColimit (spectralPullbackSectionsDiagram X i G Ui)] :
    spectralPullbackSectionsColimit X i G Ui ≃
      ((pullbackSheaf (spectralInverseLimitProjection X i)).obj G).presheaf.obj
        (op ((Opens.map (spectralInverseLimitProjection X i)).obj Ui)) :=
  Classical.choice (exists_computePullbackToSpectralLimitSections X hX i G Ui hUi)

/-- A cofiltered system of sheaves and `f_a`-maps over a spectral diagram. -/
structure SpectralSheafSystem {I : Type u} [Category.{w} I]
    (X : I ⥤ TopCat.{v}) where
  sheaf : ∀ i, TopCat.Sheaf (Type v) (X.obj i)
  map : ∀ {j i} (a : j ⟶ i),
    FMap (X.map a) (sheaf i) (sheaf j)
  map_comp : ∀ {k j i} (b : k ⟶ j) (a : j ⟶ i),
    HEq (map (b ≫ a)) (fMapComp (map b) (map a))

/-- The canonical sheaf transition associated to an arrow in the inverse
system. -/
noncomputable def spectralSystemSheafTransition
    {I : Type u} [Category.{w} I] [IsCofiltered I]
    {X : I ⥤ TopCat.{v}} [HasLimit X]
    (S : SpectralSheafSystem X) {j i : I} (a : j ⟶ i) :
    (pullbackSheaf (spectralInverseLimitProjection X i)).obj (S.sheaf i) ⟶
      (pullbackSheaf (spectralInverseLimitProjection X j)).obj (S.sheaf j) := by
  let pj := spectralInverseLimitProjection X j
  let fa := X.map a
  let ψ : (pullbackSheaf fa).obj (S.sheaf i) ⟶ S.sheaf j :=
    (fMapPullbackHomEquiv fa (S.sheaf i) (S.sheaf j)).symm (S.map a)
  have hpi : pj ≫ fa = spectralInverseLimitProjection X i := limit.w X a
  let e :
      (pullbackSheaf (spectralInverseLimitProjection X i)).obj (S.sheaf i) ⟶
        (pullbackSheaf (pj ≫ fa)).obj (S.sheaf i) :=
    eqToHom (congrArg (fun q : spectralInverseLimitSpace X ⟶ X.obj i =>
      (pullbackSheaf q).obj (S.sheaf i)) hpi.symm)
  exact e ≫ (pullbackSheafCompIso pj fa).hom.app (S.sheaf i) ≫
    (pullbackSheaf pj).map ψ

/-- The canonical diagram of pullbacks of a spectral sheaf system. -/
noncomputable def spectralSystemSheafDiagram
    {I : Type u} [Category.{w} I] [IsCofiltered I]
    {X : I ⥤ TopCat.{v}} [HasLimit X]
    (S : SpectralSheafSystem X) : Iᵒᵖ ⥤
      TopCat.Sheaf (Type v) (spectralInverseLimitSpace X) where
  obj i :=
    (pullbackSheaf (spectralInverseLimitProjection X i.unop)).obj
      (S.sheaf i.unop)
  map a := spectralSystemSheafTransition S a.unop
  map_id := by
    intro i
    sorry
  map_comp := by
    intro i j k a b
    sorry

/-- A colimit presentation of the sheaf on the inverse-limit space. -/
structure SpectralSystemLimitSheafData
    {I : Type u} [Category.{w} I] [IsCofiltered I]
    {X : I ⥤ TopCat.{v}} [HasLimit X]
    (S : SpectralSheafSystem X) where
  cocone : Cocone (spectralSystemSheafDiagram S)
  isColimit : IsColimit cocone

/-- The sheaf on the inverse-limit space obtained as the colimit of the
pullbacks of a spectral sheaf system. -/
theorem exists_spectralSystemLimitSheaf
    {I : Type u} [Category.{w} I] [IsCofiltered I]
    {X : I ⥤ TopCat.{v}} [HasLimit X]
    (S : SpectralSheafSystem X) :
    Nonempty (SpectralSystemLimitSheafData S) := by
  sorry

noncomputable def spectralSystemLimitSheafData
    {I : Type u} [Category.{w} I] [IsCofiltered I]
    {X : I ⥤ TopCat.{v}} [HasLimit X]
    (S : SpectralSheafSystem X) :
    SpectralSystemLimitSheafData S :=
  Classical.choice (exists_spectralSystemLimitSheaf S)

/-- The sheaf on the inverse-limit space obtained as the colimit of the
pullbacks of a spectral sheaf system. -/
noncomputable def spectralSystemLimitSheaf
    {I : Type u} [Category.{w} I] [IsCofiltered I]
    {X : I ⥤ TopCat.{v}} [HasLimit X]
    (S : SpectralSheafSystem X) :
    TopCat.Sheaf (Type v) (spectralInverseLimitSpace X) :=
  (spectralSystemLimitSheafData S).cocone.pt

/-- The source-facing colimit of the sections
`F_j(f_a⁻¹(U_i))` over arrows `a : j ⟶ i`. -/
noncomputable abbrev spectralSystemSectionsAt
    {I : Type u} [Category.{w} I] [IsCofiltered I]
    {X : I ⥤ TopCat.{v}} [HasLimit X]
    (S : SpectralSheafSystem X) (i : I) (Ui : Opens (X.obj i))
    (a : spectralPullbackSectionsIndex i) : Type v :=
  (S.sheaf a.unop.left).presheaf.obj
    (op ((Opens.map (X.map a.unop.hom)).obj Ui))

/-- The transition on the source's section system induced by an `f`-map. -/
noncomputable def spectralSystemSectionsTransition
    {I : Type u} [Category.{w} I] [IsCofiltered I]
    {X : I ⥤ TopCat.{v}} [HasLimit X]
    (S : SpectralSheafSystem X) (i : I) (Ui : Opens (X.obj i))
    {a b : spectralPullbackSectionsIndex i} (h : a ⟶ b) :
    spectralSystemSectionsAt S i Ui a → spectralSystemSectionsAt S i Ui b := by
  let f := X.map h.unop.left
  let fa := X.map a.unop.hom
  let fb := X.map b.unop.hom
  have hcomp : f ≫ fa = fb := by
    rw [← X.map_comp]
    simpa using congrArg X.map (CostructuredArrow.w h.unop)
  let ξ : FMap f (S.sheaf a.unop.left) (S.sheaf b.unop.left) :=
    S.map h.unop.left
  intro s
  have hopen : (Opens.map f).obj ((Opens.map fa).obj Ui) =
      (Opens.map fb).obj Ui := by
    rw [← Opens.map_comp_obj, hcomp]
  simpa [spectralSystemSectionsAt, f, fa, fb, ξ, fMapAt, hopen] using
    fMapAt ξ ((Opens.map fa).obj Ui) s

structure SpectralSystemSectionsDiagramData
    {I : Type u} [Category.{w} I] [IsCofiltered I]
    {X : I ⥤ TopCat.{v}} [HasLimit X]
    (S : SpectralSheafSystem X) (i : I) (Ui : Opens (X.obj i)) :
    Type (max (u + 1) (w + 1) (v + 2)) where
  diagram : spectralPullbackSectionsIndex i ⥤ Type v
  obj_eq : ∀ a, diagram.obj a = spectralSystemSectionsAt S i Ui a
  map_eq : ∀ {a b} (h : a ⟶ b),
    eqToHom (obj_eq a).symm ≫ diagram.map h ≫ eqToHom (obj_eq b) =
      spectralSystemSectionsTransition S i Ui h

theorem exists_spectralSystemSectionsDiagram
    {I : Type u} [Category.{w} I] [IsCofiltered I]
    {X : I ⥤ TopCat.{v}} [HasLimit X]
    (S : SpectralSheafSystem X) (i : I) (Ui : Opens (X.obj i)) :
    Nonempty (SpectralSystemSectionsDiagramData S i Ui) := by
  sorry

/-- The source-facing colimit of the sections
`F_j(f_a⁻¹(U_i))` over arrows `a : j ⟶ i`. -/
noncomputable def spectralSystemSectionsDiagram
    {I : Type u} [Category.{w} I] [IsCofiltered I]
    {X : I ⥤ TopCat.{v}} [HasLimit X]
    (S : SpectralSheafSystem X) (i : I) (Ui : Opens (X.obj i)) :
    spectralPullbackSectionsIndex i ⥤ Type v :=
  (Classical.choice (exists_spectralSystemSectionsDiagram S i Ui)).diagram

theorem spectralSystemSectionsDiagram_obj
    {I : Type u} [Category.{w} I] [IsCofiltered I]
    {X : I ⥤ TopCat.{v}} [HasLimit X]
    (S : SpectralSheafSystem X) (i : I) (Ui : Opens (X.obj i))
    (a : spectralPullbackSectionsIndex i) :
    (spectralSystemSectionsDiagram S i Ui).obj a =
      spectralSystemSectionsAt S i Ui a :=
  (Classical.choice (exists_spectralSystemSectionsDiagram S i Ui)).obj_eq a

/-- The source-facing colimit of the sections
`F_j(f_a⁻¹(U_i))` over arrows `a : j ⟶ i`. -/
noncomputable def spectralSystemSectionsColimit
    {I : Type u} [Category.{w} I] [IsCofiltered I]
    {X : I ⥤ TopCat.{v}} [HasLimit X]
    (S : SpectralSheafSystem X) (i : I) (Ui : Opens (X.obj i))
    [HasColimit (spectralSystemSectionsDiagram S i Ui)] : Type v :=
  colimit (spectralSystemSectionsDiagram S i Ui)

/-- Sections of the colimit system descend along quasi-compact opens of a
spectral inverse-limit factor. -/
theorem exists_spectralSystemDescendOpensEquiv
    {I : Type u} [Category.{w} I] [IsCofiltered I]
    {X : I ⥤ TopCat.{v}} [HasLimit X]
    (hX : IsSpectralSpaceDiagram X) (S : SpectralSheafSystem X)
    (i : I) (Ui : Opens (X.obj i)) (hUi : QuasiCompactOpen Ui)
    [HasColimit (spectralSystemSectionsDiagram S i Ui)] :
    Nonempty (spectralSystemSectionsColimit S i Ui ≃
      (spectralSystemLimitSheaf S).presheaf.obj
        (op ((Opens.map (spectralInverseLimitProjection X i)).obj Ui))) := by
  sorry

/-- Sections of the colimit system descend along quasi-compact opens of a
spectral inverse-limit factor. -/
noncomputable def spectralSystemDescendOpensEquiv
    {I : Type u} [Category.{w} I] [IsCofiltered I]
    {X : I ⥤ TopCat.{v}} [HasLimit X]
    (hX : IsSpectralSpaceDiagram X) (S : SpectralSheafSystem X)
    (i : I) (Ui : Opens (X.obj i)) (hUi : QuasiCompactOpen Ui)
    [HasColimit (spectralSystemSectionsDiagram S i Ui)] :
    spectralSystemSectionsColimit S i Ui ≃
      (spectralSystemLimitSheaf S).presheaf.obj
        (op ((Opens.map (spectralInverseLimitProjection X i)).obj Ui)) :=
  Classical.choice (exists_spectralSystemDescendOpensEquiv hX S i Ui hUi)

end

end Formalization.Books.Sheaves.Unit22
