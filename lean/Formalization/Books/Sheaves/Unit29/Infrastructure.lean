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
open Formalization.Books.Sheaves.Unit03
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
  let hcC := CategoryTheory.Sheaf.sheafifyCocone E
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
  let : Subsingleton ((terminalSheaf X).presheaf.obj (op W.1)) := hsec W.1
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
  let : HasLimits (TopCat.Sheaf (Type v) cofiniteCounterexampleSpace) :=
    sheaf_has_limits
  let : PreservesLimits L := h
  let J := Discrete (ULift.{v} ℕ)
  let : HasLimitsOfShape J (TopCat.Sheaf (Type v) cofiniteCounterexampleSpace) :=
    HasLimits.has_limits_of_shape J
  let F : J ⥤ TopCat.Presheaf (Type v) cofiniteCounterexampleSpace :=
    Discrete.functor (fun n =>
      coverPresheaf (cofiniteCounterexampleOpenA n.down)
        (cofiniteCounterexampleOpenB n.down))
  let : HasLimit (F ⋙ L) :=
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
  have : IsIso u := by infer_instance
  have : IsIso m := by infer_instance
  let um := u ≫ m
  have : IsIso um := by infer_instance
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
  classical
  let G := F ⋙ TopCat.Sheaf.forget (Type v) X
  let P := colimit G
  let J := Opens.grothendieckTopology X
  let E := colimit.cocone G
  let hE := colimit.isColimit G
  let hc := CategoryTheory.Sheaf.isColimitSheafifyCocone E hE
  let hcC := CategoryTheory.Sheaf.sheafifyCocone E
  let e := (TopCat.Sheaf.forget (Type v) X).mapIso
    (IsColimit.coconePointUniqueUpToIso (colimit.isColimit F) hc)
  let H := G ⋙ (evaluation (Opens X)ᵒᵖ (Type v)).obj (op U)
  let cU := ((evaluation (Opens X)ᵒᵖ (Type v)).obj (op U)).mapCocone E
  let hU' := isColimitOfPreserves
    ((evaluation (Opens X)ᵒᵖ (Type v)).obj (op U)) hE
  let eu := IsColimit.coconePointUniqueUpToIso hU' (colimit.isColimit H)
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
      (IsColimit.comp_coconePointUniqueUpToIso_inv hU'
        (colimit.isColimit H) i) zi
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
    have hmap := (TopCat.Sheaf.forget (Type v) X ⋙
      (evaluation (Opens X)ᵒᵖ (Type v)).obj (op U)).map_comp_apply
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
      change ((TopCat.Sheaf.forget (Type v) X ⋙
          (evaluation (Opens X)ᵒᵖ (Type v)).obj (op U)).map
            ((colimit.isColimit F).coconePointUniqueUpToIso hc).hom)
          (((TopCat.Sheaf.forget (Type v) X ⋙
            (evaluation (Opens X)ᵒᵖ (Type v)).obj (op U)).map
              ((colimit.cocone F).ι.app i)) zi) = _
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
  have hcompact : ∀ (S : J.Cover U),
      ∃ T : Finset S.Arrow, ∀ x : X, x ∈ (U : Set X) →
        ∃ I ∈ T, x ∈ (I.Y : Set X) := by
    intro S
    have hcover : (U : Set X) ⊆ ⋃ I : S.Arrow, (I.Y : Set X) := by
      intro x hx
      rcases S.2 x hx with ⟨V, f, hf, hxV⟩
      exact Set.mem_iUnion.2 ⟨⟨V, f, hf⟩, hxV⟩
    obtain ⟨T, hT⟩ := (isCompact_iff_finite_subcover.mp hU)
      (fun I : S.Arrow => (I.Y : Set X))
      (fun I : S.Arrow => I.Y.2) hcover
    refine ⟨T, ?_⟩
    intro x hx
    rcases Set.mem_iUnion.mp (hT hx) with ⟨I, hI⟩
    rcases Set.mem_iUnion.mp hI with ⟨hIT, hxI⟩
    exact ⟨I, hIT, hxI⟩
  have hbound : ∀ {S : J.Cover U} (k : I) (T : Finset S.Arrow)
      (q : S.Arrow → I), ∃ l : I, k ≤ l ∧ ∀ a ∈ T, q a ≤ l := by
    intro S k T
    induction T using Finset.induction_on with
    | empty =>
        intro q
        exact ⟨k, le_rfl, by simp⟩
    | @insert a T ha ih =>
        intro q
        obtain ⟨k', hk, hkT⟩ := ih q
        obtain ⟨l, hal, hkl⟩ := exists_ge_ge (q a) k'
        refine ⟨l, hk.trans hkl, ?_⟩
        intro b hb
        rcases Finset.mem_insert.mp hb with rfl | hb
        · exact hal
        · exact (hkT b hb).trans hkl
  intro x y hxy
  have hxy' := congrArg (e.hom.app (op U)) hxy
  rw [hfactor x, hfactor y] at hxy'
  have hplus : Function.Injective ((J.toPlus (J.plusObj P)).app (op U)) :=
    CategoryTheory.GrothendieckTopology.Plus.inj_of_sep
      (J.plusObj P)
      (fun V S a b h => CategoryTheory.GrothendieckTopology.Plus.sep P S a b h)
      U
  have hab : (J.toPlus P).app (op U) (eu.inv x) =
      (J.toPlus P).app (op U) (eu.inv y) := by
    let M := CategoryTheory.sheafifyLift J (J.toSheafify P)
      (CategoryTheory.GrothendieckTopology.sheafify_isSheaf J P)
    have hM := CategoryTheory.toSheafify_sheafifyLift
      (J := J) (P := P) (Q := J.sheafify P) (J.toSheafify P)
      (CategoryTheory.GrothendieckTopology.sheafify_isSheaf J P)
    have hxyM := congrArg (ConcreteCategory.hom (M.app (op U))) hxy'
    have hM' := congrArg (fun q => q.app (op U)) hM
    have hMa := ConcreteCategory.congr_hom hM' (eu.inv x)
    have hMb := ConcreteCategory.congr_hom hM' (eu.inv y)
    have hxyConcrete :
        (ConcreteCategory.hom ((J.toSheafify P).app (op U))) (eu.inv x) =
          (ConcreteCategory.hom ((J.toSheafify P).app (op U))) (eu.inv y) := by
      calc
        (ConcreteCategory.hom ((J.toSheafify P).app (op U))) (eu.inv x) =
            (ConcreteCategory.hom (M.app (op U)))
              ((ConcreteCategory.hom ((CategoryTheory.toSheafify J P).app (op U)))
                (eu.inv x)) := by
          simpa only [M, NatTrans.comp_app, CategoryTheory.types_comp_apply] using hMa.symm
        _ = (ConcreteCategory.hom (M.app (op U)))
              ((ConcreteCategory.hom ((CategoryTheory.toSheafify J P).app (op U)))
                (eu.inv y)) := hxyM
        _ = (ConcreteCategory.hom ((J.toSheafify P).app (op U))) (eu.inv y) := by
          simpa only [M, NatTrans.comp_app, CategoryTheory.types_comp_apply] using hMb
    have hxy'' :
        (ConcreteCategory.hom ((J.toPlus (J.plusObj P)).app (op U)))
            ((ConcreteCategory.hom ((J.toPlus P).app (op U))) (eu.inv x)) =
          (ConcreteCategory.hom ((J.toPlus (J.plusObj P)).app (op U)))
            ((ConcreteCategory.hom ((J.toPlus P).app (op U))) (eu.inv y)) := by
      dsimp [CategoryTheory.GrothendieckTopology.toSheafify] at hxyConcrete
      rw [CategoryTheory.GrothendieckTopology.plusMap_toPlus] at hxyConcrete
      change (ConcreteCategory.hom
        ((J.toPlus P).app (op U) ≫
          (J.toPlus (J.plusObj P)).app (op U))) (eu.inv x) =
        (ConcreteCategory.hom
          ((J.toPlus P).app (op U) ≫
            (J.toPlus (J.plusObj P)).app (op U))) (eu.inv y) at hxyConcrete
      simpa only [CategoryTheory.types_comp_apply] using hxyConcrete
    simpa only using hplus hxy''
  simp only [CategoryTheory.GrothendieckTopology.Plus.toPlus_eq_mk] at hab
  rw [CategoryTheory.GrothendieckTopology.Plus.eq_mk_iff_exists] at hab
  obtain ⟨S, hSx, hSy, hS⟩ := hab
  obtain ⟨T, hT⟩ := hcompact S
  obtain ⟨i₁, a, ha⟩ := Types.jointly_surjective H hU' (eu.inv x)
  obtain ⟨i₂, b, hb⟩ := Types.jointly_surjective H hU' (eu.inv y)
  obtain ⟨k, hik, hjk⟩ := exists_ge_ge i₁ i₂
  let g₁ : i₁ ⟶ k := homOfLE hik
  let g₂ : i₂ ⟶ k := homOfLE hjk
  let a' := (F.map g₁).1.app (op U) a
  let b' := (F.map g₂).1.app (op U) b
  have ha' : eu.inv x = (colimit.ι G k).app (op U) a' := by
    calc
      eu.inv x = (colimit.ι G i₁).app (op U) a := ha.symm
      _ = (colimit.ι G k).app (op U) a' := by
        exact ConcreteCategory.congr_hom ((cU.ι.naturality g₁).symm) a
  have hb' : eu.inv y = (colimit.ι G k).app (op U) b' := by
    calc
      eu.inv y = (colimit.ι G i₂).app (op U) b := hb.symm
      _ = (colimit.ι G k).app (op U) b' := by
        exact ConcreteCategory.congr_hom ((cU.ι.naturality g₂).symm) b
  have hqexists : ∀ A : S.Arrow, ∃ j : I, ∃ g : k ⟶ j, ((F.map g).1.app (op A.Y))
        ((F.obj k).1.map A.f.op a') =
        ((F.map g).1.app (op A.Y))
          ((F.obj k).1.map A.f.op b') := by
    intro A
    let hcolim := isColimitOfPreserves
      ((evaluation (Opens X)ᵒᵖ (Type v)).obj (op A.Y)) (colimit.isColimit G)
    exact (Types.FilteredColimit.isColimit_eq_iff' hcolim _ _).mp (by
        have hI := congrArg (fun z => z A) hS
        change P.map A.f.op (eu.inv x) = P.map A.f.op (eu.inv y) at hI
        have hmap (z : (F.obj k).1.obj (op U)) :
            P.map A.f.op ((colimit.ι G k).app (op U) z) =
              (colimit.ι G k).app (op A.Y)
                ((F.obj k).1.map A.f.op z) := by
          exact ConcreteCategory.congr_hom ((colimit.ι G k).naturality A.f.op).symm z
        calc
          (colimit.ι G k).app (op A.Y)
              ((F.obj k).1.map A.f.op a') =
              P.map A.f.op ((colimit.ι G k).app (op U) a') := hmap a' |>.symm
          _ = P.map A.f.op (eu.inv x) := congrArg (P.map A.f.op) ha'.symm
          _ = P.map A.f.op (eu.inv y) := hI
          _ = P.map A.f.op ((colimit.ι G k).app (op U) b') :=
            congrArg (P.map A.f.op) hb'
          _ = (colimit.ι G k).app (op A.Y)
              ((F.obj k).1.map A.f.op b') := hmap b')
  choose q gq hq using hqexists
  obtain ⟨l, hkl, hl⟩ := hbound k T q
  let al := (F.map (homOfLE hkl)).1.app (op U) a'
  let bl := (F.map (homOfLE hkl)).1.app (op U) b'
  have hlocal : ∀ I : S.Arrow, I ∈ T →
      ((F.obj l).1.map I.f.op) al = ((F.obj l).1.map I.f.op) bl := by
    intro I hIT
    let hqI := homOfLE (hl I hIT)
    have hcomp : gq I ≫ hqI = homOfLE hkl := by
      apply Subsingleton.elim
    have hnat (g : k ⟶ l) (z : (F.obj k).1.obj (op U)) :
        (F.obj l).1.map I.f.op ((F.map g).1.app (op U) z) =
          (F.map g).1.app (op I.Y) ((F.obj k).1.map I.f.op z) := by
      have hn := ConcreteCategory.congr_hom
        ((F.map g).1.naturality I.f.op) z
      simpa only [CategoryTheory.types_comp_apply] using hn.symm
    have hcomp_apply (z : (F.obj k).1.obj (op I.Y)) :
        (F.map hqI).1.app (op I.Y) ((F.map (gq I)).1.app (op I.Y) z) =
          (F.map (gq I ≫ hqI)).1.app (op I.Y) z := by
      have hh := congrArg (fun q => q.1.app (op I.Y))
        (F.map_comp (gq I) hqI)
      have hh' := congrArg (fun q => q z) hh
      simpa only [TopCat.Sheaf.comp_app, CategoryTheory.types_comp_apply] using hh'.symm
    calc
      (F.obj l).1.map I.f.op al =
          (F.map (homOfLE hkl)).1.app (op I.Y)
            ((F.obj k).1.map I.f.op a') := hnat (homOfLE hkl) a'
      _ = (F.map (gq I ≫ hqI)).1.app (op I.Y)
            ((F.obj k).1.map I.f.op a') := by rw [hcomp]
      _ = (F.map hqI).1.app (op I.Y)
            ((F.map (gq I)).1.app (op I.Y)
              ((F.obj k).1.map I.f.op a')) := hcomp_apply _ |>.symm
      _ = (F.map hqI).1.app (op I.Y)
            ((F.map (gq I)).1.app (op I.Y)
              ((F.obj k).1.map I.f.op b')) := congrArg _ (hq I)
      _ = (F.map (gq I ≫ hqI)).1.app (op I.Y)
            ((F.obj k).1.map I.f.op b') := hcomp_apply _
      _ = (F.map (homOfLE hkl)).1.app (op I.Y)
            ((F.obj k).1.map I.f.op b') := by rw [hcomp]
      _ = (F.obj l).1.map I.f.op bl := (hnat (homOfLE hkl) b').symm
  let R : Presieve U := TopCat.Presheaf.presieveOfCoveringAux
    (fun I : T => I.1.Y) U
  have hR : R ∈ (Opens.grothendieckTopology X).toPretopology U := by
    rw [Opens.toPretopology_grothendieckTopology]
    intro x hx
    obtain ⟨I, hIT, hxI⟩ := hT x hx
    exact ⟨I.Y, I.f, ⟨⟨I, hIT⟩, rfl⟩, hxI⟩
  have hmem : Sieve.generate R ∈ J U := hR
  let S' : J.Cover U := ⟨Sieve.generate R, hmem⟩
  have hQ : ∀ {Y : Opens X} (f : Y ⟶ U) (hf : S' f),
      (F.obj l).1.map f.op al = (F.obj l).1.map f.op bl := by
    intro Y f hf
    have hle : Sieve.generate R ≤
        ⟨fun Z g => (F.obj l).1.map g.op al = (F.obj l).1.map g.op bl,
          by
            intro Z W g h hg
            have hh := congrArg ((F.obj l).1.map hg.op) h
            change (F.obj l).1.map (g.op ≫ hg.op) al =
              (F.obj l).1.map (g.op ≫ hg.op) bl
            rw [(F.obj l).1.map_comp]
            exact hh⟩ := by
      rw [Sieve.generate_le_iff]
      intro Z g hg
      obtain ⟨I, hI⟩ := hg
      subst hI
      simpa only [Subsingleton.elim g I.1.f] using hlocal I.1 I.2
    change Sieve.generate R f at hf
    exact hle f hf
  have hfinal : al = bl := by
    have hs : Presieve.IsSheaf J (F.obj l).1 :=
      (isSheaf_iff_isSheaf_of_type _ _).mp (F.obj l).2
    apply (hs S'.1 S'.2).isSeparatedFor.ext
    intro Y f hf
    exact hQ f hf
  have hp : (ConcreteCategory.hom eu.inv) x =
      (ConcreteCategory.hom eu.inv) y := by
    calc
      (ConcreteCategory.hom eu.inv) x = (colimit.ι G k).app (op U) a' := ha'
      _ = (colimit.ι G l).app (op U) al := by
        exact ConcreteCategory.congr_hom ((cU.ι.naturality (homOfLE hkl)).symm) a'
      _ = (colimit.ι G l).app (op U) bl := congrArg _ hfinal
      _ = (colimit.ι G k).app (op U) b' := by
        exact ConcreteCategory.congr_hom ((cU.ι.naturality (homOfLE hkl)).symm) b' |>.symm
      _ = (ConcreteCategory.hom eu.inv) y := hb'.symm
  have hp' := congrArg (ConcreteCategory.hom eu.hom) hp
  simpa using hp'

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
  classical
  refine ⟨directedColimitSectionsMap_injective_of_quasiCompact F U hU, ?_⟩
  let G := F ⋙ TopCat.Sheaf.forget (Type v) X
  let P := colimit G
  let J := Opens.grothendieckTopology X
  let E := colimit.cocone G
  let hE := colimit.isColimit G
  let hc := CategoryTheory.Sheaf.isColimitSheafifyCocone E hE
  let hcC := CategoryTheory.Sheaf.sheafifyCocone E
  let e := (TopCat.Sheaf.forget (Type v) X).mapIso
    (IsColimit.coconePointUniqueUpToIso (colimit.isColimit F) hc)
  let H := G ⋙ (evaluation (Opens X)ᵒᵖ (Type v)).obj (op U)
  let cU := ((evaluation (Opens X)ᵒᵖ (Type v)).obj (op U)).mapCocone E
  let hU' := isColimitOfPreserves
    ((evaluation (Opens X)ᵒᵖ (Type v)).obj (op U)) hE
  let eu := IsColimit.coconePointUniqueUpToIso hU' (colimit.isColimit H)
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
      (IsColimit.comp_coconePointUniqueUpToIso_inv hU'
        (colimit.isColimit H) i) zi
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
    have hmap := (TopCat.Sheaf.forget (Type v) X ⋙
      (evaluation (Opens X)ᵒᵖ (Type v)).obj (op U)).map_comp_apply
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
      change ((TopCat.Sheaf.forget (Type v) X ⋙
          (evaluation (Opens X)ᵒᵖ (Type v)).obj (op U)).map
            ((colimit.isColimit F).coconePointUniqueUpToIso hc).hom)
          (((TopCat.Sheaf.forget (Type v) X ⋙
            (evaluation (Opens X)ᵒᵖ (Type v)).obj (op U)).map
              ((colimit.cocone F).ι.app i)) zi) = _
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
  have hcompact : ∀ (S : J.Cover U),
      ∃ T : Finset S.Arrow, ∀ x : X, x ∈ (U : Set X) →
        ∃ I ∈ T, x ∈ (I.Y : Set X) := by
    intro S
    have hcover : (U : Set X) ⊆ ⋃ I : S.Arrow, (I.Y : Set X) := by
      intro x hx
      rcases S.2 x hx with ⟨V, f, hf, hxV⟩
      exact Set.mem_iUnion.2 ⟨⟨V, f, hf⟩, hxV⟩
    obtain ⟨T, hT⟩ := (isCompact_iff_finite_subcover.mp hU)
      (fun I : S.Arrow => (I.Y : Set X))
      (fun I : S.Arrow => I.Y.2) hcover
    refine ⟨T, ?_⟩
    intro x hx
    rcases Set.mem_iUnion.mp (hT hx) with ⟨I, hI⟩
    rcases Set.mem_iUnion.mp hI with ⟨hIT, hxI⟩
    exact ⟨I, hIT, hxI⟩
  have hbound : ∀ {S : J.Cover U} (k : I) (T : Finset S.Arrow)
      (q : S.Arrow → I), ∃ l : I, k ≤ l ∧ ∀ a ∈ T, q a ≤ l := by
    intro S k T
    induction T using Finset.induction_on with
    | empty =>
        intro q
        exact ⟨k, le_rfl, by simp⟩
    | @insert a T ha ih =>
        intro q
        obtain ⟨k', hk, hkT⟩ := ih q
        obtain ⟨l, hal, hkl⟩ := exists_ge_ge (q a) k'
        refine ⟨l, hk.trans hkl, ?_⟩
        intro b hb
        rcases Finset.mem_insert.mp hb with rfl | hb
        · exact hal
        · exact (hkT b hb).trans hkl
  have hsep := colimitPresheaf_isSeparated_of_injective F hF
  have hto : ∀ V : Opens X,
      Function.Injective ((CategoryTheory.toSheafify J P).app (op V)) := by
    intro V
    have hsep' : ∀ (W : Opens X) (S : J.Cover W)
        (x y : P.obj (op W)),
        (∀ I : S.Arrow, P.map I.f.op x = P.map I.f.op y) → x = y := by
      intro W S x y h
      apply (hsep S.1 S.2).ext
      intro Y f hf
      exact h ⟨Y, f, hf⟩
    have hplus : ∀ (W : Opens X) (S : J.Cover W)
        (x y : (J.plusObj P).obj (op W)),
        (∀ I : S.Arrow, (J.plusObj P).map I.f.op x =
          (J.plusObj P).map I.f.op y) → x = y := by
      intro W S x y h
      exact CategoryTheory.GrothendieckTopology.Plus.sep P S x y h
    have hto1 := CategoryTheory.GrothendieckTopology.Plus.inj_of_sep
      P hsep' V
    have hto2 := CategoryTheory.GrothendieckTopology.Plus.inj_of_sep
      (J.plusObj P) hplus V
    have htoConcrete : Function.Injective ((J.toSheafify P).app (op V)) := by
      dsimp [CategoryTheory.GrothendieckTopology.toSheafify]
      intro a b hab
      apply hto1
      apply hto2
      rw [CategoryTheory.GrothendieckTopology.plusMap_toPlus] at hab
      change (ConcreteCategory.hom
        ((J.toPlus P).app (op V) ≫
          (J.toPlus (J.plusObj P)).app (op V))) a =
        (ConcreteCategory.hom
          ((J.toPlus P).app (op V) ≫
            (J.toPlus (J.plusObj P)).app (op V))) b at hab
      simpa only [CategoryTheory.types_comp_apply] using hab
    let M := CategoryTheory.sheafifyLift J (J.toSheafify P)
      (CategoryTheory.GrothendieckTopology.sheafify_isSheaf J P)
    have hM := CategoryTheory.toSheafify_sheafifyLift
      (J := J) (P := P) (Q := J.sheafify P) (J.toSheafify P)
      (CategoryTheory.GrothendieckTopology.sheafify_isSheaf J P)
    intro a b hab
    apply htoConcrete
    have habM := congrArg (ConcreteCategory.hom (M.app (op V))) hab
    have hM' := congrArg (fun q => q.app (op V)) hM
    have hMa := ConcreteCategory.congr_hom hM' a
    have hMb := ConcreteCategory.congr_hom hM' b
    calc
      (ConcreteCategory.hom ((J.toSheafify P).app (op V))) a =
          (ConcreteCategory.hom (M.app (op V)))
            ((ConcreteCategory.hom ((CategoryTheory.toSheafify J P).app (op V))) a) := by
        simpa only [M, NatTrans.comp_app, CategoryTheory.types_comp_apply] using hMa.symm
      _ = (ConcreteCategory.hom (M.app (op V)))
          ((ConcreteCategory.hom ((CategoryTheory.toSheafify J P).app (op V))) b) := habM
      _ = (ConcreteCategory.hom ((J.toSheafify P).app (op V))) b := by
        simpa only [M, NatTrans.comp_app, CategoryTheory.types_comp_apply] using hMb
  intro y
  let z := (e.hom.app (op U)) y
  have hloc : Presheaf.IsLocallySurjective J (CategoryTheory.toSheafify J P) := by
    infer_instance
  let S : J.Cover U :=
    ⟨Presheaf.imageSieve (CategoryTheory.toSheafify J P) z,
      Presheaf.imageSieve_mem J (CategoryTheory.toSheafify J P) z⟩
  obtain ⟨T, hT⟩ := hcompact S
  let p : ∀ A : S.Arrow, P.obj (op A.Y) := fun A =>
    Presheaf.localPreimage (F := P) (CategoryTheory.toSheafify J P)
      (s := z) (V := A.Y) A.f (by
        change (Presheaf.imageSieve (CategoryTheory.toSheafify J P) z).arrows A.f
        simpa only [S] using A.hf)
  have hp : ∀ A : S.Arrow,
      (CategoryTheory.toSheafify J P).app (op A.Y) (p A) =
        (CategoryTheory.sheafify J P).map A.f.op z := by
    intro A
    apply Presheaf.app_localPreimage
  have hrep : ∀ A : S.Arrow, ∃ j : I, ∃ a : (F.obj j).1.obj (op A.Y),
      (colimit.ι G j).app (op A.Y) a = p A := by
    intro A
    exact Types.jointly_surjective _
      (isColimitOfPreserves ((evaluation (Opens X)ᵒᵖ (Type v)).obj (op A.Y))
        (colimit.isColimit G)) (p A)
  choose q a hqa using hrep
  obtain ⟨k, hk, hkT⟩ := hbound (Classical.choice (inferInstance : Nonempty I)) T q
  let b : ∀ A : T, (F.obj k).1.obj (op A.1.Y) := fun A =>
    (F.map (homOfLE (hkT A.1 A.2))).1.app (op A.1.Y) (a A.1)
  have hba : ∀ A : T,
      (colimit.ι G k).app (op A.1.Y) (b A) = p A.1 := by
    intro A
    calc
      (colimit.ι G k).app (op A.1.Y) (b A) =
          (colimit.ι G (q A.1)).app (op A.1.Y) (a A.1) := by
        have hh := congrArg (fun r => r.app (op A.1.Y))
          (E.ι.naturality (homOfLE (hkT A.1 A.2)))
        exact ConcreteCategory.congr_hom hh (a A.1)
      _ = p A.1 := hqa A.1
  let R : Presieve U := TopCat.Presheaf.presieveOfCoveringAux
    (fun A : T => A.1.Y) U
  have hR : R ∈ (Opens.grothendieckTopology X).toPretopology U := by
    rw [Opens.toPretopology_grothendieckTopology]
    intro x hx
    rcases hT x hx with ⟨A, hAT, hxA⟩
    let AT : T := ⟨A, hAT⟩
    exact ⟨AT.1.Y, AT.1.f, ⟨AT, rfl⟩, hxA⟩
  have hgen : Sieve.generate R ∈ J U := hR
  have hEq : Sieve.ofArrows (fun A : T => A.1.Y)
      (fun A : T => A.1.f) = Sieve.generate R := by
    apply le_antisymm
    · rw [Sieve.generate_le_iff, Presieve.ofArrows_le_iff]
      intro A
      exact Sieve.le_generate R _ _ ⟨A, rfl⟩
    · rw [Sieve.generate_le_iff]
      intro Y g hg
      obtain ⟨A, hA⟩ := hg
      subst Y
      simpa only [Subsingleton.elim g A.1.f] using
        (Sieve.ofArrows_mk (fun A : T => A.1.Y) (fun A : T => A.1.f) A)
  have hf : Sieve.ofArrows (fun A : T => A.1.Y)
      (fun A : T => A.1.f) ∈ J U := by
    rw [hEq]
    exact hgen
  have hsheafF : Presheaf.IsSheaf J (F.obj k).1 :=
    by simpa only [J] using (F.obj k).2
  have hcompat : ∀ {W : Opens X} {A B : T}
      (aW : W ⟶ A.1.Y) (bW : W ⟶ B.1.Y),
      aW ≫ A.1.f = bW ≫ B.1.f →
        (F.obj k).1.map aW.op (b A) =
          (F.obj k).1.map bW.op (b B) := by
    intro W A B aW bW hab
    have hna := NatTrans.naturality_apply
      (CategoryTheory.toSheafify J P) aW.op (p A.1)
    have hnb := NatTrans.naturality_apply
      (CategoryTheory.toSheafify J P) bW.op (p B.1)
    have hop : A.1.f.op ≫ aW.op = B.1.f.op ≫ bW.op := by
      exact congrArg Quiver.Hom.op hab
    have hP : P.map aW.op ((colimit.ι G k).app (op A.1.Y) (b A)) =
          P.map bW.op ((colimit.ι G k).app (op B.1.Y) (b B)) := by
      apply hto W
      calc
        (CategoryTheory.toSheafify J P).app (op W)
            (P.map aW.op ((colimit.ι G k).app (op A.1.Y) (b A))) =
          (CategoryTheory.toSheafify J P).app (op W)
            (P.map aW.op (p A.1)) := by
            rw [hba A]
        _ = (CategoryTheory.sheafify J P).map aW.op
            ((CategoryTheory.toSheafify J P).app (op A.1.Y) (p A.1)) := hna
        _ = (CategoryTheory.sheafify J P).map aW.op
            ((CategoryTheory.sheafify J P).map A.1.f.op z) := by
            rw [hp A.1]
        _ = (CategoryTheory.sheafify J P).map
            (A.1.f.op ≫ aW.op) z := by
            exact ((CategoryTheory.sheafify J P).map_comp_apply
              A.1.f.op aW.op z).symm
        _ = (CategoryTheory.sheafify J P).map
            (B.1.f.op ≫ bW.op) z := by rw [hop]
        _ = (CategoryTheory.sheafify J P).map bW.op
            ((CategoryTheory.sheafify J P).map B.1.f.op z) := by
            exact (CategoryTheory.sheafify J P).map_comp_apply
              B.1.f.op bW.op z
        _ = (CategoryTheory.sheafify J P).map bW.op
            ((CategoryTheory.toSheafify J P).app (op B.1.Y) (p B.1)) := by
            rw [hp B.1]
        _ = (CategoryTheory.toSheafify J P).app (op W)
            (P.map bW.op (p B.1)) := hnb.symm
        _ = (CategoryTheory.toSheafify J P).app (op W)
            (P.map bW.op ((colimit.ι G k).app (op B.1.Y) (b B))) := by
            rw [hba B]
    let hcolim := isColimitOfPreserves
      ((evaluation (Opens X)ᵒᵖ (Type v)).obj (op W)) (colimit.isColimit G)
    have hmapA : P.map aW.op ((colimit.ι G k).app (op A.1.Y) (b A)) =
        (colimit.ι G k).app (op W)
          ((F.obj k).1.map aW.op (b A)) := by
      exact ConcreteCategory.congr_hom
        ((colimit.ι G k).naturality aW.op).symm (b A)
    have hmapB : P.map bW.op ((colimit.ι G k).app (op B.1.Y) (b B)) =
        (colimit.ι G k).app (op W)
          ((F.obj k).1.map bW.op (b B)) := by
      exact ConcreteCategory.congr_hom
        ((colimit.ι G k).naturality bW.op).symm (b B)
    have hP' : (colimit.ι G k).app (op W)
          ((F.obj k).1.map aW.op (b A)) =
        (colimit.ι G k).app (op W)
          ((F.obj k).1.map bW.op (b B)) := by
      exact hmapA.symm.trans (hP.trans hmapB)
    obtain ⟨j, g, hg⟩ :=
      (Types.FilteredColimit.isColimit_eq_iff' hcolim _ _).mp hP'
    have hg' :
        ((F.map g).1.app (op W))
            ((F.obj k).1.map aW.op (b A)) =
          ((F.map g).1.app (op W))
            ((F.obj k).1.map bW.op (b B)) := by
      change ((F.map g).1.app (op W))
          ((F.obj k).1.map aW.op (b A)) =
        ((F.map g).1.app (op W))
          ((F.obj k).1.map bW.op (b B)) at hg
      exact hg
    exact (hF (leOfHom g) W) hg'
  let E₀ : Type v := ULift.{v} PUnit
  let e₀ : E₀ := ⟨PUnit.unit⟩
  have hfamily : ∀ {W : Opens X} {A B : T}
      (aW : W ⟶ A.1.Y) (bW : W ⟶ B.1.Y),
      aW ≫ A.1.f = bW ≫ B.1.f →
        (TypeCat.ofHom (fun _ : E₀ => b A)) ≫
            (F.obj k).1.map aW.op =
          (TypeCat.ofHom (fun _ : E₀ => b B)) ≫
          (F.obj k).1.map bW.op := by
    intro W A B aW bW hab
    apply TypeCat.Hom.ext
    apply TypeCat.Fun.ext
    funext u
    exact hcompat aW bW hab
  obtain ⟨g, hg, -⟩ :=
    CategoryTheory.Presheaf.IsSheaf.existsUnique_amalgamation_ofArrows
      hsheafF
      (E := E₀) (fun A : T => A.1.f) hf
      (fun A : T => TypeCat.ofHom (fun _ : E₀ => b A))
      (fun {W} {A B} aW bW hab => hfamily aW bW hab)
  let s := g e₀
  change (G.obj k).obj (op U) at s
  have hsg : ∀ A : T, (F.obj k).1.map A.1.f.op s = b A := by
    intro A
    have h := ConcreteCategory.congr_hom (hg A) e₀
    simpa only [s, TypeCat.ofHom_apply, CategoryTheory.types_comp_apply] using h
  have hmap : ∀ A : T,
      P.map A.1.f.op ((colimit.ι G k).app (op U) s) = p A.1 := by
    intro A
    have hn := ConcreteCategory.congr_hom
      ((colimit.ι G k).naturality A.1.f.op).symm s
    calc
      P.map A.1.f.op ((colimit.ι G k).app (op U) s) =
          (colimit.ι G k).app (op A.1.Y)
            ((F.obj k).1.map A.1.f.op s) := hn
      _ = (colimit.ι G k).app (op A.1.Y) (b A) := congrArg _ (hsg A)
      _ = p A.1 := hba A
  have hQ : Presieve.IsSheaf J (CategoryTheory.sheafify J P) :=
    (isSheaf_iff_isSheaf_of_type _ _).mp
      ((CategoryTheory.presheafToSheaf J (Type v)).obj P).2
  have hz :
      (CategoryTheory.toSheafify J P).app (op U)
          ((colimit.ι G k).app (op U) s) = z := by
    apply (hQ (Sieve.ofArrows (fun A : T => A.1.Y) (fun A : T => A.1.f)) hf).isSeparatedFor.ext
    intro W gW hgW
    obtain ⟨A, aW, haW⟩ := Sieve.ofArrows.exists hgW
    have hgenW : gW = aW ≫ A.1.f := Sieve.ofArrows.fac hgW
    subst gW
    have hna := NatTrans.naturality_apply
      (CategoryTheory.toSheafify J P) A.1.f.op
        ((colimit.ι G k).app (op U) s)
    have hpA := hp A.1
    have hmapA := hmap A
    calc
      (CategoryTheory.sheafify J P).map (A.1.f.op ≫ aW.op)
          ((CategoryTheory.toSheafify J P).app (op U)
            ((colimit.ι G k).app (op U) s)) =
          (CategoryTheory.sheafify J P).map aW.op
            ((CategoryTheory.sheafify J P).map A.1.f.op
              ((CategoryTheory.toSheafify J P).app (op U)
                ((colimit.ι G k).app (op U) s))) := by
        exact (CategoryTheory.sheafify J P).map_comp_apply
          A.1.f.op aW.op _
      _ = (CategoryTheory.sheafify J P).map aW.op
            ((CategoryTheory.toSheafify J P).app (op A.1.Y)
              (P.map A.1.f.op ((colimit.ι G k).app (op U) s))) := by
        rw [hna]
      _ = (CategoryTheory.sheafify J P).map aW.op
            ((CategoryTheory.toSheafify J P).app (op A.1.Y) (p A.1)) := by
        rw [hmapA]
      _ = (CategoryTheory.sheafify J P).map aW.op
            ((CategoryTheory.sheafify J P).map A.1.f.op z) := by
        rw [hpA]
      _ = (CategoryTheory.sheafify J P).map (A.1.f.op ≫ aW.op) z := by
        exact ((CategoryTheory.sheafify J P).map_comp_apply
          A.1.f.op aW.op z).symm
  let x := eu.hom ((colimit.ι G k).app (op U) s)
  refine ⟨x, ?_⟩
  have hxeu : (ConcreteCategory.hom eu.inv) x =
      (ConcreteCategory.hom ((colimit.ι G k).app (op U))) s := by
    dsimp [x]
    exact Iso.hom_inv_id_apply eu _
  have heq :
      (ConcreteCategory.hom (e.hom.app (op U)))
          (directedColimitSectionsMap F U x) =
        (ConcreteCategory.hom (e.hom.app (op U))) y := by
    have hfactor_x := hfactor x
    rw [hxeu] at hfactor_x
    exact hfactor_x.trans (hz.trans rfl)
  have hinv :
      (ConcreteCategory.hom (e.inv.app (op U)))
          ((ConcreteCategory.hom (e.hom.app (op U)))
            (directedColimitSectionsMap F U x)) =
        (ConcreteCategory.hom (e.inv.app (op U)))
          ((ConcreteCategory.hom (e.hom.app (op U))) y) :=
    congrArg (ConcreteCategory.hom (e.inv.app (op U))) heq
  exact (ConcreteCategory.congr_hom
      (e.hom_inv_id_app (op U)) (directedColimitSectionsMap F U x)).symm.trans
    (hinv.trans (ConcreteCategory.congr_hom
      (e.hom_inv_id_app (op U)) y))

/-- Injectivity of the canonical sheafification map over a quasi-compact open. -/
private theorem colimitPresheaf_toSheafify_injective_of_quasiCompact
    {X : TopCat.{v}} {I : Type v} [Preorder I] [Nonempty I]
    [IsDirectedOrder I] (F : I ⥤ TopCat.Sheaf (Type v) X) (U : Opens X)
    [HasColimit F]
    [HasColimit (F ⋙ TopCat.Sheaf.forget (Type v) X ⋙
      (evaluation (Opens X)ᵒᵖ (Type v)).obj (op U))]
    (hU : QuasiCompactOpen U) :
    Function.Injective ((CategoryTheory.toSheafify
      (Opens.grothendieckTopology X) (colimit (F ⋙
        TopCat.Sheaf.forget (Type v) X))).app (op U)) := by
  classical
  let G := F ⋙ TopCat.Sheaf.forget (Type v) X
  let P := colimit G
  let J := Opens.grothendieckTopology X
  let E := colimit.cocone G
  let hE := colimit.isColimit G
  let hc := CategoryTheory.Sheaf.isColimitSheafifyCocone E hE
  let hcC := CategoryTheory.Sheaf.sheafifyCocone E
  let e := (TopCat.Sheaf.forget (Type v) X).mapIso
    (IsColimit.coconePointUniqueUpToIso (colimit.isColimit F) hc)
  let H := G ⋙ (evaluation (Opens X)ᵒᵖ (Type v)).obj (op U)
  let cU := ((evaluation (Opens X)ᵒᵖ (Type v)).obj (op U)).mapCocone E
  let hU' := isColimitOfPreserves
    ((evaluation (Opens X)ᵒᵖ (Type v)).obj (op U)) hE
  let eu := IsColimit.coconePointUniqueUpToIso hU' (colimit.isColimit H)
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
      (IsColimit.comp_coconePointUniqueUpToIso_inv hU'
        (colimit.isColimit H) i) zi
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
    have hmap := (TopCat.Sheaf.forget (Type v) X ⋙
      (evaluation (Opens X)ᵒᵖ (Type v)).obj (op U)).map_comp_apply
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
      change ((TopCat.Sheaf.forget (Type v) X ⋙
          (evaluation (Opens X)ᵒᵖ (Type v)).obj (op U)).map
            ((colimit.isColimit F).coconePointUniqueUpToIso hc).hom)
          (((TopCat.Sheaf.forget (Type v) X ⋙
            (evaluation (Opens X)ᵒᵖ (Type v)).obj (op U)).map
              ((colimit.cocone F).ι.app i)) zi) = _
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
  let x' := eu.hom x
  let y' := eu.hom y
  have hsections :
      e.hom.app (op U) (directedColimitSectionsMap F U x') =
        e.hom.app (op U) (directedColimitSectionsMap F U y') := by
    have hx := hfactor x'
    have hy := hfactor y'
    dsimp [x', y'] at hx hy
    rw [Iso.hom_inv_id_apply eu x] at hx
    rw [Iso.hom_inv_id_apply eu y] at hy
    exact hx.trans (hxy.trans hy.symm)
  have hmap :
      directedColimitSectionsMap F U x' =
        directedColimitSectionsMap F U y' := by
    have h' := congrArg (ConcreteCategory.hom (e.inv.app (op U))) hsections
    have hmap' := (ConcreteCategory.congr_hom
      (e.hom_inv_id_app (op U)) _).symm.trans
      (h'.trans (ConcreteCategory.congr_hom
        (e.hom_inv_id_app (op U)) _))
    exact hmap'
  have hxy' := directedColimitSectionsMap_injective_of_quasiCompact F U hU hmap
  have h' := congrArg (ConcreteCategory.hom eu.inv) hxy'
  simpa [x', y'] using h'

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
  classical
  let G := F ⋙ TopCat.Sheaf.forget (Type v) X
  let P := colimit G
  let J := Opens.grothendieckTopology X
  let E := colimit.cocone G
  let hE := colimit.isColimit G
  let hc := CategoryTheory.Sheaf.isColimitSheafifyCocone E hE
  let hcC := CategoryTheory.Sheaf.sheafifyCocone E
  let e := (TopCat.Sheaf.forget (Type v) X).mapIso
    (IsColimit.coconePointUniqueUpToIso (colimit.isColimit F) hc)
  let H := G ⋙ (evaluation (Opens X)ᵒᵖ (Type v)).obj (op U)
  let cU := ((evaluation (Opens X)ᵒᵖ (Type v)).obj (op U)).mapCocone E
  let hU' := isColimitOfPreserves
    ((evaluation (Opens X)ᵒᵖ (Type v)).obj (op U)) hE
  let eu := IsColimit.coconePointUniqueUpToIso hU' (colimit.isColimit H)
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
      (IsColimit.comp_coconePointUniqueUpToIso_inv hU'
        (colimit.isColimit H) i) zi
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
    have hmap := (TopCat.Sheaf.forget (Type v) X ⋙
      (evaluation (Opens X)ᵒᵖ (Type v)).obj (op U)).map_comp_apply
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
      change ((TopCat.Sheaf.forget (Type v) X ⋙
          (evaluation (Opens X)ᵒᵖ (Type v)).obj (op U)).map
            ((colimit.isColimit F).coconePointUniqueUpToIso hc).hom)
          (((TopCat.Sheaf.forget (Type v) X ⋙
            (evaluation (Opens X)ᵒᵖ (Type v)).obj (op U)).map
              ((colimit.cocone F).ι.app i)) zi) = _
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
  have hcompact : ∀ (S : J.Cover U),
      ∃ T : Finset S.Arrow,
        (∀ x : X, x ∈ (U : Set X) → ∃ I ∈ T, x ∈ (I.Y : Set X)) ∧
        (∀ a ∈ T, ∀ b ∈ T, QuasiCompactOpen (a.Y ⊓ b.Y)) := by
    intro S
    have hSU : (⨆ a : S.Arrow, a.Y) = U := by
      apply le_antisymm
      · exact iSup_le fun a => leOfHom a.f
      · rw [← SetLike.coe_subset_coe]
        rw [Opens.coe_iSup]
        intro x hx
        rcases S.2 x hx with ⟨V, f, hf, hxV⟩
        exact Set.mem_iUnion.2 ⟨⟨V, f, hf⟩, hxV⟩
    obtain ⟨J₀, hfin, W, hW, hWref, hWqc⟩ := hU S.Arrow (fun a => a.Y) hSU
    letI : Finite J₀ := hfin
    letI : Fintype J₀ := Fintype.ofFinite J₀
    choose k hk using hWref
    let A : J₀ → S.Arrow := fun j =>
      ⟨W j, homOfLE (hk j) ≫ (k j).f,
        S.1.downward_closed (k j).hf (homOfLE (hk j))⟩
    refine ⟨Finset.univ.image A, ?_, ?_⟩
    · intro x hx
      obtain ⟨j, hxj⟩ := Opens.mem_iSup.mp
        (show x ∈ (⨆ j, W j) from by simpa [hW] using hx)
      exact ⟨A j, Finset.mem_image.2 ⟨j, Finset.mem_univ _, rfl⟩, hxj⟩
    · intro a ha b hb
      rcases Finset.mem_image.mp ha with ⟨j, -, hja⟩
      rcases Finset.mem_image.mp hb with ⟨j', -, hj'b⟩
      subst a
      subst b
      simpa [A] using hWqc j j'
  have hUqc : QuasiCompactOpen U := by
    obtain ⟨T, hT, hTqc⟩ := hcompact (⊤ : J.Cover U)
    have hcompactUnion : IsCompact (⋃ I ∈ T, (I.Y : Set X)) := by
      exact T.isCompact_biUnion (fun I hI => by
        change IsCompact (I.Y : Set X)
        simpa [QuasiCompactOpen, inf_idem] using hTqc I hI I hI)
    have hUeq : (U : Set X) = ⋃ I ∈ T, (I.Y : Set X) := by
      apply Set.Subset.antisymm
      · intro x hx
        rcases hT x hx with ⟨I, hI, hxI⟩
        exact Set.mem_iUnion.2 ⟨I, Set.mem_iUnion.2 ⟨hI, hxI⟩⟩
      · intro x hx
        rcases Set.mem_iUnion.mp hx with ⟨I, hx⟩
        rcases Set.mem_iUnion.mp hx with ⟨hI, hxI⟩
        exact (leOfHom I.f) hxI
    rw [QuasiCompactOpen]
    rw [hUeq]
    exact hcompactUnion
  refine ⟨directedColimitSectionsMap_injective_of_quasiCompact F U hUqc, ?_⟩
  have hbound : ∀ {α : Type v} (k : I) (T : Finset α)
      (q : α → I), ∃ l : I, k ≤ l ∧ ∀ a ∈ T, q a ≤ l := by
    intro α k T
    induction T using Finset.induction_on with
    | empty =>
        intro q
        exact ⟨k, le_rfl, by simp⟩
    | @insert a T ha ih =>
        intro q
        obtain ⟨k', hk, hkT⟩ := ih q
        obtain ⟨l, hal, hkl⟩ := exists_ge_ge (q a) k'
        refine ⟨l, hk.trans hkl, ?_⟩
        intro b hb
        rcases Finset.mem_insert.mp hb with rfl | hb
        · exact hal
        · exact (hkT b hb).trans hkl
  intro y
  let z := (e.hom.app (op U)) y
  have hloc : Presheaf.IsLocallySurjective J (CategoryTheory.toSheafify J P) := by
    infer_instance
  let S : J.Cover U :=
    ⟨Presheaf.imageSieve (CategoryTheory.toSheafify J P) z,
      Presheaf.imageSieve_mem J (CategoryTheory.toSheafify J P) z⟩
  obtain ⟨T, hT, hTqc⟩ := hcompact S
  let p : ∀ A : S.Arrow, P.obj (op A.Y) := fun A =>
    Presheaf.localPreimage (F := P) (CategoryTheory.toSheafify J P)
      (s := z) (V := A.Y) A.f (by
        change (Presheaf.imageSieve (CategoryTheory.toSheafify J P) z).arrows A.f
        simpa only [S] using A.hf)
  have hp : ∀ A : S.Arrow,
      (CategoryTheory.toSheafify J P).app (op A.Y) (p A) =
        (CategoryTheory.sheafify J P).map A.f.op z := by
    intro A
    apply Presheaf.app_localPreimage
  have hrep : ∀ A : T, ∃ j : I, ∃ a : (F.obj j).1.obj (op A.1.Y),
      (colimit.ι G j).app (op A.1.Y) a = p A.1 := by
    intro A
    exact Types.jointly_surjective _
      (isColimitOfPreserves ((evaluation (Opens X)ᵒᵖ (Type v)).obj (op A.1.Y))
        (colimit.isColimit G)) (p A.1)
  choose q a hqa using hrep
  have hpair : ∀ A B : T, ∃ l : I, ∃ hA : q A ≤ l, ∃ hB : q B ≤ l,
      ((F.map (homOfLE hA)).1.app
        (op (A.1.Y ⊓ B.1.Y)))
          ((F.obj (q A)).1.map (homOfLE inf_le_left).op (a A)) =
        ((F.map (homOfLE hB)).1.app
          (op (A.1.Y ⊓ B.1.Y)))
          ((F.obj (q B)).1.map (homOfLE inf_le_right).op (a B)) := by
    intro A B
    let W : Opens X := A.1.Y ⊓ B.1.Y
    have hW : QuasiCompactOpen W := hTqc A.1 A.2 B.1 B.2
    have htoW := colimitPresheaf_toSheafify_injective_of_quasiCompact F W hW
    let aW : W ⟶ A.1.Y := homOfLE inf_le_left
    let bW : W ⟶ B.1.Y := homOfLE inf_le_right
    have hP :
        P.map aW.op ((colimit.ι G (q A)).app (op A.1.Y) (a A)) =
          P.map bW.op ((colimit.ι G (q B)).app (op B.1.Y) (a B)) := by
      apply htoW
      have hna := NatTrans.naturality_apply
        (CategoryTheory.toSheafify J P) aW.op
          ((colimit.ι G (q A)).app (op A.1.Y) (a A))
      have hnb := NatTrans.naturality_apply
        (CategoryTheory.toSheafify J P) bW.op
          ((colimit.ι G (q B)).app (op B.1.Y) (a B))
      have hpa := hp A.1
      have hpb := hp B.1
      have hqa' := hqa A
      have hqb' := hqa B
      have hAB : aW ≫ A.1.f = bW ≫ B.1.f := Subsingleton.elim _ _
      have hop : A.1.f.op ≫ aW.op = B.1.f.op ≫ bW.op :=
        congrArg Quiver.Hom.op hAB
      calc
        (CategoryTheory.toSheafify J P).app (op W)
            (P.map aW.op ((colimit.ι G (q A)).app (op A.1.Y) (a A))) =
          (CategoryTheory.sheafify J P).map aW.op
            ((CategoryTheory.toSheafify J P).app (op A.1.Y)
              ((colimit.ι G (q A)).app (op A.1.Y) (a A))) := hna
        _ = (CategoryTheory.sheafify J P).map aW.op
            ((CategoryTheory.toSheafify J P).app (op A.1.Y) (p A.1)) := by
              rw [hqa']
        _ = (CategoryTheory.sheafify J P).map aW.op
            ((CategoryTheory.sheafify J P).map A.1.f.op z) := by
              rw [hpa]
        _ = (CategoryTheory.sheafify J P).map (A.1.f.op ≫ aW.op) z := by
              exact ((CategoryTheory.sheafify J P).map_comp_apply
                A.1.f.op aW.op z).symm
        _ = (CategoryTheory.sheafify J P).map (B.1.f.op ≫ bW.op) z := by
              rw [hop]
        _ = (CategoryTheory.sheafify J P).map bW.op
            ((CategoryTheory.sheafify J P).map B.1.f.op z) := by
              exact (CategoryTheory.sheafify J P).map_comp_apply
                B.1.f.op bW.op z
        _ = (CategoryTheory.sheafify J P).map bW.op
            ((CategoryTheory.toSheafify J P).app (op B.1.Y) (p B.1)) := by
              rw [hpb]
        _ = (CategoryTheory.toSheafify J P).app (op W)
            (P.map bW.op (p B.1)) := by
              have hnb' := hnb
              rw [hqb'] at hnb'
              exact hnb'.symm
        _ = (CategoryTheory.toSheafify J P).app (op W)
            (P.map bW.op ((colimit.ι G (q B)).app (op B.1.Y) (a B))) := by
              rw [hqb']
    let hcolim := isColimitOfPreserves
      ((evaluation (Opens X)ᵒᵖ (Type v)).obj (op W)) (colimit.isColimit G)
    have hmapA : P.map aW.op ((colimit.ι G (q A)).app (op A.1.Y) (a A)) =
        (colimit.ι G (q A)).app (op W)
          ((F.obj (q A)).1.map aW.op (a A)) := by
      exact ConcreteCategory.congr_hom
        ((colimit.ι G (q A)).naturality aW.op).symm (a A)
    have hmapB : P.map bW.op ((colimit.ι G (q B)).app (op B.1.Y) (a B)) =
        (colimit.ι G (q B)).app (op W)
          ((F.obj (q B)).1.map bW.op (a B)) := by
      exact ConcreteCategory.congr_hom
        ((colimit.ι G (q B)).naturality bW.op).symm (a B)
    obtain ⟨l, gA, gB, hg⟩ :=
      (Types.FilteredColimit.isColimit_eq_iff
        (G ⋙ (evaluation (Opens X)ᵒᵖ (Type v)).obj (op W)) hcolim).mp
        (hmapA.symm.trans (hP.trans hmapB))
    refine ⟨l, leOfHom gA, leOfHom gB, ?_⟩
    change ((F.map gA).1.app (op W))
          ((F.obj (q A)).1.map aW.op (a A)) =
        ((F.map gB).1.app (op W))
          ((F.obj (q B)).1.map bW.op (a B)) at hg
    convert hg using 1 <;> rfl
  choose r hrA hrB hrEq using hpair
  let pairs : Finset (T × T) := Finset.univ.product Finset.univ
  obtain ⟨k, hk, hkpair⟩ := hbound (Classical.choice (inferInstance : Nonempty I))
    pairs (fun AB => r AB.1 AB.2)
  have hqk : ∀ A : T, q A ≤ k := by
    intro A
    exact (hrA A A).trans
      (hkpair (A, A) (Finset.mem_product.mpr
        ⟨Finset.mem_univ A, Finset.mem_univ A⟩))
  let b : ∀ A : T, (F.obj k).1.obj (op A.1.Y) := fun A =>
    (F.map (homOfLE (hqk A))).1.app (op A.1.Y) (a A)
  have hcompat : ∀ {W : Opens X} {A B : T}
      (aW : W ⟶ A.1.Y) (bW : W ⟶ B.1.Y),
      aW ≫ A.1.f = bW ≫ B.1.f →
        (F.obj k).1.map aW.op (b A) =
          (F.obj k).1.map bW.op (b B) := by
    intro W A B aW bW hab
    have hle : W ≤ A.1.Y ⊓ B.1.Y :=
      le_inf (leOfHom aW) (leOfHom bW)
    let iW : W ⟶ A.1.Y ⊓ B.1.Y := homOfLE hle
    let iA : A.1.Y ⊓ B.1.Y ⟶ A.1.Y := homOfLE inf_le_left
    let iB : A.1.Y ⊓ B.1.Y ⟶ B.1.Y := homOfLE inf_le_right
    have hiA : iW ≫ iA = aW := Subsingleton.elim _ _
    have hiB : iW ≫ iB = bW := Subsingleton.elim _ _
    have hkr := hkpair (A, B) (Finset.mem_product.mpr
      ⟨Finset.mem_univ A, Finset.mem_univ B⟩)
    have hABk := congrArg
      ((F.map (homOfLE hkr)).1.app (op (A.1.Y ⊓ B.1.Y))) (hrEq A B)
    have hnA := NatTrans.naturality_apply
      (F.map (homOfLE hkr)).hom iA.op
        ((F.map (homOfLE (hrA A B))).1.app (op A.1.Y) (a A))
    have hnB := NatTrans.naturality_apply
      (F.map (homOfLE hkr)).hom iB.op
        ((F.map (homOfLE (hrB A B))).1.app (op B.1.Y) (a B))
    have hnA0 := NatTrans.naturality_apply
      (F.map (homOfLE (hrA A B))).hom iA.op (a A)
    have hnB0 := NatTrans.naturality_apply
      (F.map (homOfLE (hrB A B))).hom iB.op (a B)
    have hABk' :
        (F.obj k).1.map iA.op (b A) =
          (F.obj k).1.map iB.op (b B) := by
      dsimp [b]
      have hqkA : homOfLE (hqk A) =
          homOfLE (hrA A B) ≫ homOfLE hkr := Subsingleton.elim _ _
      have hqkB : homOfLE (hqk B) =
          homOfLE (hrB A B) ≫ homOfLE hkr := Subsingleton.elim _ _
      rw [hqkA, F.map_comp, hqkB, F.map_comp]
      simp only [TopCat.Sheaf.comp_app, CategoryTheory.types_comp_apply]
      rw [← hnA, ← hnB, ← hnA0, ← hnB0]
      exact hABk
    calc
      (F.obj k).1.map aW.op (b A) =
          (F.obj k).1.map (iA.op ≫ iW.op) (b A) := by rw [← hiA, op_comp]
      _ = (F.obj k).1.map iW.op ((F.obj k).1.map iA.op (b A)) := by
        exact (F.obj k).1.map_comp_apply iA.op iW.op (b A)
      _ = (F.obj k).1.map iW.op ((F.obj k).1.map iB.op (b B)) :=
        congrArg _ hABk'
      _ = (F.obj k).1.map (iB.op ≫ iW.op) (b B) := by
        exact ((F.obj k).1.map_comp_apply iB.op iW.op (b B)).symm
      _ = (F.obj k).1.map bW.op (b B) := by rw [← hiB, op_comp]
  let E₀ : Type v := ULift.{v} PUnit
  let e₀ : E₀ := ⟨PUnit.unit⟩
  have hfamily : ∀ {W : Opens X} {A B : T}
      (aW : W ⟶ A.1.Y) (bW : W ⟶ B.1.Y),
      aW ≫ A.1.f = bW ≫ B.1.f →
        (TypeCat.ofHom (fun _ : E₀ => b A)) ≫
            (F.obj k).1.map aW.op =
          (TypeCat.ofHom (fun _ : E₀ => b B)) ≫
          (F.obj k).1.map bW.op := by
    intro W A B aW bW hab
    apply TypeCat.Hom.ext
    apply TypeCat.Fun.ext
    funext u
    exact hcompat aW bW hab
  let R : Presieve U := TopCat.Presheaf.presieveOfCoveringAux
    (fun A : T => A.1.Y) U
  have hR : R ∈ (Opens.grothendieckTopology X).toPretopology U := by
    rw [Opens.toPretopology_grothendieckTopology]
    intro x hx
    rcases hT x hx with ⟨A, hAT, hxA⟩
    let AT : T := ⟨A, hAT⟩
    exact ⟨AT.1.Y, AT.1.f, ⟨AT, rfl⟩, hxA⟩
  have hgen : Sieve.generate R ∈ J U := hR
  have hEq : Sieve.ofArrows (fun A : T => A.1.Y)
      (fun A : T => A.1.f) = Sieve.generate R := by
    apply le_antisymm
    · rw [Sieve.generate_le_iff, Presieve.ofArrows_le_iff]
      intro A
      exact Sieve.le_generate R _ _ ⟨A, rfl⟩
    · rw [Sieve.generate_le_iff]
      intro Y g hg
      obtain ⟨A, hA⟩ := hg
      subst Y
      simpa only [Subsingleton.elim g A.1.f] using
        (Sieve.ofArrows_mk (fun A : T => A.1.Y) (fun A : T => A.1.f) A)
  have hf : Sieve.ofArrows (fun A : T => A.1.Y)
      (fun A : T => A.1.f) ∈ J U := by
    rw [hEq]
    exact hgen
  obtain ⟨g, hg, -⟩ :=
    CategoryTheory.Presheaf.IsSheaf.existsUnique_amalgamation_ofArrows
      (by simpa only [J] using (F.obj k).2)
      (E := E₀) (fun A : T => A.1.f)
      hf
      (fun A : T => TypeCat.ofHom (fun _ : E₀ => b A))
      (fun {W} {A B} aW bW hab => hfamily aW bW hab)
  let s := g e₀
  change (G.obj k).obj (op U) at s
  have hsg : ∀ A : T, (F.obj k).1.map A.1.f.op s = b A := by
    intro A
    have h := ConcreteCategory.congr_hom (hg A) e₀
    simpa only [s, TypeCat.ofHom_apply, CategoryTheory.types_comp_apply] using h
  have hmap : ∀ A : T,
      P.map A.1.f.op ((colimit.ι G k).app (op U) s) = p A.1 := by
    intro A
    have hn := ConcreteCategory.congr_hom
      ((colimit.ι G k).naturality A.1.f.op).symm s
    calc
      P.map A.1.f.op ((colimit.ι G k).app (op U) s) =
          (colimit.ι G k).app (op A.1.Y)
            ((F.obj k).1.map A.1.f.op s) := hn
      _ = (colimit.ι G k).app (op A.1.Y) (b A) := congrArg _ (hsg A)
      _ = p A.1 := by
        have hqaA := hqa A
        have hqkA := hqk A
        have hkA := hqkA
        rw [← hqaA]
        have hh := congrArg (fun r => r.app (op A.1.Y))
          (E.ι.naturality (homOfLE hkA))
        exact ConcreteCategory.congr_hom
          hh (a A)
  have hQ : Presieve.IsSheaf J (CategoryTheory.sheafify J P) :=
    (isSheaf_iff_isSheaf_of_type _ _).mp
      ((CategoryTheory.presheafToSheaf J (Type v)).obj P).2
  have hz :
      (CategoryTheory.toSheafify J P).app (op U)
          ((colimit.ι G k).app (op U) s) = z := by
    apply (hQ (Sieve.ofArrows (fun A : T => A.1.Y) (fun A : T => A.1.f)
      ) hf).isSeparatedFor.ext
    intro W gW hgW
    obtain ⟨A, aW, haW⟩ := Sieve.ofArrows.exists hgW
    have hgenW : gW = aW ≫ A.1.f := Sieve.ofArrows.fac hgW
    subst gW
    have hna := NatTrans.naturality_apply
      (CategoryTheory.toSheafify J P) A.1.f.op
        ((colimit.ι G k).app (op U) s)
    calc
      (CategoryTheory.sheafify J P).map (A.1.f.op ≫ aW.op)
          ((CategoryTheory.toSheafify J P).app (op U)
            ((colimit.ι G k).app (op U) s)) =
          (CategoryTheory.sheafify J P).map aW.op
            ((CategoryTheory.sheafify J P).map A.1.f.op
              ((CategoryTheory.toSheafify J P).app (op U)
                ((colimit.ι G k).app (op U) s))) := by
        exact (CategoryTheory.sheafify J P).map_comp_apply
          A.1.f.op aW.op _
      _ = (CategoryTheory.sheafify J P).map aW.op
            ((CategoryTheory.toSheafify J P).app (op A.1.Y)
              (P.map A.1.f.op ((colimit.ι G k).app (op U) s))) := by
        rw [hna]
      _ = (CategoryTheory.sheafify J P).map aW.op
            ((CategoryTheory.toSheafify J P).app (op A.1.Y) (p A.1)) := by
        rw [hmap A]
      _ = (CategoryTheory.sheafify J P).map aW.op
            ((CategoryTheory.sheafify J P).map A.1.f.op z) := by
        rw [hp A.1]
      _ = (CategoryTheory.sheafify J P).map (A.1.f.op ≫ aW.op) z := by
        exact ((CategoryTheory.sheafify J P).map_comp_apply
          A.1.f.op aW.op z).symm
  let x := eu.hom ((colimit.ι G k).app (op U) s)
  refine ⟨x, ?_⟩
  have hxeu : (ConcreteCategory.hom eu.inv) x =
      (ConcreteCategory.hom ((colimit.ι G k).app (op U))) s := by
    dsimp [x]
    exact Iso.hom_inv_id_apply eu _
  have heq :
      (ConcreteCategory.hom (e.hom.app (op U)))
          (directedColimitSectionsMap F U x) =
        (ConcreteCategory.hom (e.hom.app (op U))) y := by
    have hfactor_x := hfactor x
    rw [hxeu] at hfactor_x
    exact hfactor_x.trans (hz.trans rfl)
  have hinv := congrArg (ConcreteCategory.hom (e.inv.app (op U))) heq
  exact (ConcreteCategory.congr_hom
      (e.hom_inv_id_app (op U)) (directedColimitSectionsMap F U x)).symm.trans
    (hinv.trans (ConcreteCategory.congr_hom
      (e.hom_inv_id_app (op U)) y))

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
    map_zero' := by
      apply ULift.ext
      funext m
      rfl
    map_add' := by
      intro s t
      apply ULift.ext
      funext m
      rfl }
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

/- The identity law for an `f`-map over an identity continuous map. -/
noncomputable def spectralSystemIdentityFMap {X : TopCat.{v}}
    (F : TopCat.Sheaf (Type v) X) : FMap (𝟙 X) F F :=
  fMapOfFamily {
    app := fun U V h s => restriction (F := F.presheaf) (by simpa using h) s
    naturality := by
      intro U U' V V' hUU' hVV' hU hU' s
      have hU'V' : U' ≤ V' := by simpa using hU'
      have hUV : U ≤ V := by simpa using hU
      rw [restriction_restriction (F := F.presheaf)]
      rw [restriction_restriction (F := F.presheaf)]
  }

/-- A cofiltered system of sheaves and `f_a`-maps over a spectral diagram. -/
structure SpectralSheafSystem {I : Type u} [Category.{w} I]
    (X : I ⥤ TopCat.{v}) where
  sheaf : ∀ i, TopCat.Sheaf (Type v) (X.obj i)
  map : ∀ {j i} (a : j ⟶ i),
    FMap (X.map a) (sheaf i) (sheaf j)
  map_id : ∀ i, HEq (map (𝟙 i)) (spectralSystemIdentityFMap (sheaf i))
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

private theorem fMapAt_identity_of_eq
    {Y : TopCat.{v}} (F : TopCat.Sheaf (Type v) Y)
    {f : Y ⟶ Y} (hf : f = 𝟙 Y) (ξ : FMap f F F)
    (hξ : HEq ξ (spectralSystemIdentityFMap F)) (V : Opens Y)
    (s : F.presheaf.obj (op V)) :
    HEq (fMapAt ξ V s) s := by
  cases hf
  cases V
  have hξ' : ξ = spectralSystemIdentityFMap F := eq_of_heq hξ
  rw [hξ']
  apply heq_of_eq
  change restriction (F := F.presheaf) _ s = s
  convert restriction_self (F := F.presheaf) s using 1 <;> apply Subsingleton.elim

theorem exists_spectralSystemSectionsDiagram
    {I : Type u} [Category.{w} I] [IsCofiltered I]
    {X : I ⥤ TopCat.{v}} [HasLimit X]
    (S : SpectralSheafSystem X) (i : I) (Ui : Opens (X.obj i)) :
    Nonempty (SpectralSystemSectionsDiagramData S i Ui) := by
  sorry
  /- Original proof attempt:
  let D : spectralPullbackSectionsIndex i ⥤ Type v := {
    obj := fun a => spectralSystemSectionsAt S i Ui a
    map := fun h => TypeCat.ofHom (spectralSystemSectionsTransition S i Ui h)
    map_id := by
      intro a
      apply ConcreteCategory.hom_ext
      intro s
      dsimp [spectralSystemSectionsTransition]
      let F := S.sheaf (unop a).left
      let hfa : X.map (𝟙 (unop a).left) = 𝟙 (X.obj (unop a).left) :=
        X.map_id _
      symm
      apply eq_cast_iff_heq.mpr
      exact (fMapAt_identity_of_eq F hfa (S.map (𝟙 (unop a).left))
        (S.map_id _) _ s).symm
    map_comp := by
      intro a b c f g
      apply ConcreteCategory.hom_ext
      intro s
      dsimp [spectralSystemSectionsTransition] }
  refine ⟨{ diagram := D, obj_eq := ?_, map_eq := ?_ }⟩
  · intro a
    rfl
  · intro a b h
    simp [D]
  -/

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
