import Formalization.Books.Sheaves.Unit21.ContinuousMaps
import Formalization.Books.Sheaves.Unit27.Skyscraper
import Formalization.Books.Sheaves.Unit28.LimitsPresheaves
import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.Algebra.Group.ULift
import Mathlib.Algebra.Ring.Pi
import Mathlib.Topology.Spectral.Basic
import Mathlib.Topology.Spectral.Hom

/-!
# Sheaves on Spaces, Chapter 29: Limits and colimits of sheaves

This file formalizes `books/sheaves.tex:3400-3714`.  Limits are taken in the
canonical category of sheaves, colimits are represented by sheafification of
the pointwise presheaf colimit, and equalities of section or stalk objects are
presented by canonical isomorphisms or equivalences.  The directed-colimit
lemma, its tail-space counterexample, and the two spectral inverse-limit
statements are included in source order.
-/

namespace Formalization.Books.Sheaves.Unit29

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Formalization.Books.Sheaves.Unit21
open Formalization.Books.Sheaves.Unit27
open scoped ZeroObject

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

/-- Set-valued sheaves have all limits when the value category does. -/
theorem sheaf_has_limits {X : TopCat.{v}} {C : Type (v + 1)}
    [Category.{v} C] [HasLimits C] : HasLimits (TopCat.Sheaf C X) := by
  infer_instance

/-- Set-valued sheaves have colimits. -/
theorem sheaf_has_colimits {X : TopCat.{v}}
    [HasWeakSheafify (Opens.grothendieckTopology X) (Type v)] :
    HasColimitsOfSize.{v, v} (TopCat.Sheaf (Type v) X) := by
  sorry

/-- The source's assertion that both limits and colimits exist. -/
theorem sheaf_limits_and_colimits_exist {X : TopCat.{v}}
    [HasWeakSheafify (Opens.grothendieckTopology X) (Type v)] :
    HasLimits (TopCat.Sheaf (Type v) X) ∧
      HasColimitsOfSize.{v, v} (TopCat.Sheaf (Type v) X) := by
  exact ⟨sheaf_has_limits, sheaf_has_colimits⟩

/-- Sections of a sheaf limit are the limit of the sections. -/
theorem exists_sheafLimitSectionsIso {X : TopCat.{v}} {J : Type v}
    [Category.{v} J] (F : J ⥤ TopCat.Sheaf (Type v) X) (U : Opens X) :
    Nonempty ((sheafLimit F).presheaf.obj (op U) ≅
      limit (F ⋙ TopCat.Sheaf.forget (Type v) X ⋙
        (evaluation (Opens X)ᵒᵖ (Type v)).obj (op U))) := by
  sorry

/-- A chosen sectionwise comparison isomorphism for a sheaf limit. -/
noncomputable def sheafLimitSectionsIso {X : TopCat.{v}} {J : Type v}
    [Category.{v} J] (F : J ⥤ TopCat.Sheaf (Type v) X) (U : Opens X) :
    (sheafLimit F).presheaf.obj (op U) ≅
      limit (F ⋙ TopCat.Sheaf.forget (Type v) X ⋙
        (evaluation (Opens X)ᵒᵖ (Type v)).obj (op U)) :=
  Classical.choice (exists_sheafLimitSectionsIso F U)

/-- A sheaf colimit is the sheafification of the presheaf colimit. -/
theorem exists_sheafColimitSheafificationIso {X : TopCat.{v}}
    {J : Type v} [Category.{v} J]
    (F : J ⥤ TopCat.Sheaf (Type v) X) [HasColimit F]
    [HasColimit (F ⋙ TopCat.Sheaf.forget (Type v) X)] :
    Nonempty ((sheafColimit F).presheaf ≅
        (CategoryTheory.presheafToSheaf (Opens.grothendieckTopology X) (Type v)).obj
        (colimit (F ⋙ TopCat.Sheaf.forget (Type v) X)) |>.1) := by
  sorry

/-- A chosen sheaf-colimit/sheafification comparison isomorphism. -/
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

/-- Sheaf inclusion need not preserve arbitrary colimits. -/
theorem sheafForgetDoesNotPreserveAllColimits :
    ∃ (X : TopCat.{v}),
      ¬ PreservesColimits (TopCat.Sheaf.forget (Type v) X) := by
  sorry

/-- Sheaf inclusion need not preserve finite colimits. -/
theorem sheafForgetDoesNotPreserveFiniteColimits :
    ∃ (X : TopCat.{v}),
      ¬ PreservesFiniteColimits (TopCat.Sheaf.forget (Type v) X) := by
  sorry

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

/-- Sheafification need not preserve arbitrary limits. -/
theorem sheafificationDoesNotPreserveAllLimits :
    ∃ (X : TopCat.{v}),
      ¬ PreservesLimits
        (CategoryTheory.presheafToSheaf
          (Opens.grothendieckTopology X) (Type v)) := by
  sorry

/-! ## Stalks -/

/-- Stalks commute with finite limits of set-valued sheaves. -/
theorem exists_sheafFiniteLimitStalkIso {X : TopCat.{v}} {J : Type v}
    [Category.{v} J] [FinCategory J] (F : J ⥤ TopCat.Sheaf (Type v) X) (x : X) :
    Nonempty ((sheafLimit F).presheaf.stalk x ≅
      limit (F ⋙ TopCat.Sheaf.forget (Type v) X ⋙
        TopCat.Presheaf.stalkFunctor (Type v) x)) := by
  sorry

/-- A chosen finite-limit/stalk comparison isomorphism. -/
noncomputable def sheafFiniteLimitStalkIso {X : TopCat.{v}} {J : Type v}
    [Category.{v} J] [FinCategory J] (F : J ⥤ TopCat.Sheaf (Type v) X) (x : X) :
    (sheafLimit F).presheaf.stalk x ≅
      limit (F ⋙ TopCat.Sheaf.forget (Type v) X ⋙
        TopCat.Presheaf.stalkFunctor (Type v) x) :=
  Classical.choice (exists_sheafFiniteLimitStalkIso F x)

/-- Stalks commute with arbitrary colimits of set-valued sheaves. -/
theorem exists_sheafColimitStalkIso {X : TopCat.{v}} {J : Type v}
    [Category.{v} J] (F : J ⥤ TopCat.Sheaf (Type v) X) (x : X) [HasColimit F]
    [HasColimit (F ⋙ TopCat.Sheaf.forget (Type v) X ⋙
      TopCat.Presheaf.stalkFunctor (Type v) x)] :
    Nonempty ((sheafColimit F).presheaf.stalk x ≅
      colimit (F ⋙ TopCat.Sheaf.forget (Type v) X ⋙
        TopCat.Presheaf.stalkFunctor (Type v) x)) := by
  sorry

/-- A chosen colimit/stalk comparison isomorphism. -/
noncomputable def sheafColimitStalkIso {X : TopCat.{v}} {J : Type v}
    [Category.{v} J] (F : J ⥤ TopCat.Sheaf (Type v) X) (x : X) [HasColimit F]
    [HasColimit (F ⋙ TopCat.Sheaf.forget (Type v) X ⋙
      TopCat.Presheaf.stalkFunctor (Type v) x)] :
    (sheafColimit F).presheaf.stalk x ≅
      colimit (F ⋙ TopCat.Sheaf.forget (Type v) X ⋙
        TopCat.Presheaf.stalkFunctor (Type v) x) :=
  Classical.choice (exists_sheafColimitStalkIso F x)

/-! ## Directed colimits of sheaves -/

/-- The source's quasi-compactness predicate for an open. -/
def QuasiCompactOpen {X : TopCat.{v}} (U : Opens X) : Prop :=
  IsCompact (U : Set X)

/-- The canonical map from a colimit of sections to sections of a sheaf
colimit. -/
theorem exists_directedColimitSectionsMap {X : TopCat.{v}} {I : Type v}
    [Preorder I] [Nonempty I] [IsDirectedOrder I]
    (F : I ⥤ TopCat.Sheaf (Type v) X) (U : Opens X) [HasColimit F]
    [HasColimit (F ⋙ TopCat.Sheaf.forget (Type v) X ⋙
      (evaluation (Opens X)ᵒᵖ (Type v)).obj (op U))] :
    Nonempty (colimit (F ⋙ TopCat.Sheaf.forget (Type v) X ⋙
      (evaluation (Opens X)ᵒᵖ (Type v)).obj (op U)) →
      (sheafColimit F).presheaf.obj (op U)) := by
  sorry

/-- A chosen canonical map from a colimit of sections to sections of a sheaf
colimit. -/
noncomputable def directedColimitSectionsMap {X : TopCat.{v}} {I : Type v}
    [Preorder I] [Nonempty I] [IsDirectedOrder I]
    (F : I ⥤ TopCat.Sheaf (Type v) X) (U : Opens X) [HasColimit F]
    [HasColimit (F ⋙ TopCat.Sheaf.forget (Type v) X ⋙
      (evaluation (Opens X)ᵒᵖ (Type v)).obj (op U))] :
    colimit (F ⋙ TopCat.Sheaf.forget (Type v) X ⋙
      (evaluation (Opens X)ᵒᵖ (Type v)).obj (op U)) →
      (sheafColimit F).presheaf.obj (op U) :=
  Classical.choice (exists_directedColimitSectionsMap F U)

/-- All transition maps in a directed system are injective on sections. -/
def DirectedSectionTransitionsInjective {X : TopCat.{v}} {I : Type v}
    [Preorder I] (F : I ⥤ TopCat.Sheaf (Type v) X) : Prop :=
  ∀ {i j : I} (hij : i ≤ j) (U : Opens X),
    Function.Injective ((F.map (homOfLE hij)).1.app (op U))

/-- A finite open cover with quasi-compact pairwise intersections, cofinal
among all open covers of `U`. -/
def HasCofinalFiniteQuasiCompactOpenCover {X : TopCat.{v}} (U : Opens X) : Prop :=
  ∀ (K : Type v) (_ : Finite K) (V : K → Opens X),
    (⨆ k, V k) = U →
      ∃ (J : Type v) (_ : Finite J) (W : J → Opens X),
        (⨆ j, W j) = U ∧
          (∀ j, ∃ k, W j ≤ V k) ∧
          (∀ j j', QuasiCompactOpen (W j ⊓ W j'))

/-- Injectivity when all transition maps are injective. -/
theorem directedColimitSectionsMap_injective_of_injective
    {X : TopCat.{v}} {I : Type v} [Preorder I] [Nonempty I]
    [IsDirectedOrder I] (F : I ⥤ TopCat.Sheaf (Type v) X) (U : Opens X)
    [HasColimit F]
    [HasColimit (F ⋙ TopCat.Sheaf.forget (Type v) X ⋙
      (evaluation (Opens X)ᵒᵖ (Type v)).obj (op U))]
    (hF : DirectedSectionTransitionsInjective F) :
    Function.Injective (directedColimitSectionsMap F U) := by
  sorry

/-- Injectivity over a quasi-compact open. -/
theorem directedColimitSectionsMap_injective_of_quasiCompact
    {X : TopCat.{v}} {I : Type v} [Preorder I] [Nonempty I]
    [IsDirectedOrder I] (F : I ⥤ TopCat.Sheaf (Type v) X) (U : Opens X)
    [HasColimit F]
    [HasColimit (F ⋙ TopCat.Sheaf.forget (Type v) X ⋙
      (evaluation (Opens X)ᵒᵖ (Type v)).obj (op U))]
    (hU : QuasiCompactOpen U) :
    Function.Injective (directedColimitSectionsMap F U) := by
  sorry

/-- Bijectivity over a quasi-compact open when transitions are injective. -/
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

/-- Bijectivity when a finite quasi-compact-intersection cover is cofinal. -/
theorem directedColimitSectionsMap_bijective_of_cofinal_cover
    {X : TopCat.{v}} {I : Type v} [Preorder I] [Nonempty I]
    [IsDirectedOrder I] (F : I ⥤ TopCat.Sheaf (Type v) X) (U : Opens X)
    [HasColimit F]
    [HasColimit (F ⋙ TopCat.Sheaf.forget (Type v) X ⋙
      (evaluation (Opens X)ᵒᵖ (Type v)).obj (op U))]
    (hU : HasCofinalFiniteQuasiCompactOpenCover U) :
    Function.Bijective (directedColimitSectionsMap F U) := by
  sorry

/-! ## The tail-space counterexample -/

/-- The tail index set in the source's global-section counterexample. -/
abbrev tailIndex (n : ℕ) := {m : ℕ // n ≤ m}

/-- The universe-adjusting equivalence used for tail products. -/
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

/-- The directed system of tail products `∏_{m ≥ n} ℤ`. -/
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

/-- Data expressing all conclusions of the source's tail-space example. -/
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
    ∀ n, F.obj n = (TopCat.Sheaf.pushforward AddCommGrpCat (j n)).obj
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
  two_skyscraper_sum_inl :
    abelianSkyscraperSheaf s1 M ⟶ two_skyscraper_sum
  two_skyscraper_sum_inr :
    abelianSkyscraperSheaf s2 M ⟶ two_skyscraper_sum
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

/-- The tail-space counterexample described in the source exists. -/
theorem exists_directedColimitSectionsCounterexample :
    Nonempty DirectedColimitSectionsCounterexample := by
  sorry

/-! ## Inverse limits of spectral spaces -/

/-- A diagram of spectral spaces with spectral transition maps. -/
def IsSpectralSpaceDiagram {I : Type u} [Category.{w} I]
    (X : I ⥤ TopCat.{v}) : Prop :=
  (∀ i, SpectralSpace (X.obj i)) ∧
    (∀ {j i} (a : j ⟶ i), IsSpectralMap (X.map a : X.obj j → X.obj i))

/-- The inverse-limit space of a diagram of topological spaces. -/
noncomputable abbrev spectralInverseLimitSpace {I : Type u} [Category.{w} I]
    (X : I ⥤ TopCat.{v}) [HasLimit X] : TopCat.{v} :=
  limit X

/-- The projection from the inverse-limit space to one factor. -/
noncomputable abbrev spectralInverseLimitProjection
    {I : Type u} [Category.{w} I] (X : I ⥤ TopCat.{v}) [HasLimit X] (i : I) :
    spectralInverseLimitSpace X ⟶ X.obj i :=
  limit.π X i

/-- The index category of arrows into a fixed factor. -/
abbrev spectralPullbackSectionsIndex
    {I : Type u} [Category.{w} I] (i : I) :=
  (CostructuredArrow (𝟭 I) i)ᵒᵖ

/-- The section type attached to an arrow into `i`. -/
noncomputable abbrev spectralPullbackSectionsAt
    {I : Type u} [Category.{w} I] (X : I ⥤ TopCat.{v}) (i : I)
    (G : TopCat.Sheaf (Type v) (X.obj i)) (Ui : Opens (X.obj i))
    (a : spectralPullbackSectionsIndex i) : Type v :=
  ((pullbackSheaf (X.map a.unop.hom)).obj G).presheaf.obj
    (op ((Opens.map (X.map a.unop.hom)).obj Ui))

/-- The transition map on pullback sections induced by refinement. -/
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

/-- Data for the diagram of pullback sections. -/
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

/-- The diagram of pullback sections indexed by arrows into `i`. -/
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

/-- The colimit of pullback sections over arrows into `i`. -/
noncomputable abbrev spectralPullbackSectionsColimit
    {I : Type u} [Category.{w} I] (X : I ⥤ TopCat.{v}) (i : I)
    (G : TopCat.Sheaf (Type v) (X.obj i)) (Ui : Opens (X.obj i))
    [HasColimit (spectralPullbackSectionsDiagram X i G Ui)] : Type v :=
  colimit (spectralPullbackSectionsDiagram X i G Ui)

/-- Computation of pullback sections on a quasi-compact open after passage to
a spectral inverse limit. -/
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

/-- A chosen pullback-section computation equivalence. -/
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

/-! ## A cofiltered system of sheaves -/

/-- A cofiltered system of sheaves and `f`-maps over a spectral diagram. -/
structure SpectralSheafSystem {I : Type u} [Category.{w} I]
    (X : I ⥤ TopCat.{v}) where
  sheaf : ∀ i, TopCat.Sheaf (Type v) (X.obj i)
  map : ∀ {j i} (a : j ⟶ i),
    FMap (X.map a) (sheaf i) (sheaf j)
  map_comp : ∀ {k j i} (b : k ⟶ j) (a : j ⟶ i),
    HEq (map (b ≫ a)) (fMapComp (map b) (map a))

/-- The transition on pullbacks induced by a spectral sheaf-system map. -/
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

/-- Data for the diagram of pullbacks of a spectral sheaf system. -/
structure SpectralSystemSheafDiagramData
    {I : Type u} [Category.{w} I] [IsCofiltered I]
    {X : I ⥤ TopCat.{v}} [HasLimit X]
    (S : SpectralSheafSystem X) where
  diagram : Iᵒᵖ ⥤ TopCat.Sheaf (Type v) (spectralInverseLimitSpace X)
  obj_eq : ∀ i, diagram.obj i =
    (pullbackSheaf (spectralInverseLimitProjection X i.unop)).obj
      (S.sheaf i.unop)
  map_eq : ∀ {i j} (a : i ⟶ j),
    eqToHom (obj_eq i).symm ≫ diagram.map a ≫ eqToHom (obj_eq j) =
      spectralSystemSheafTransition S a.unop

theorem exists_spectralSystemSheafDiagram
    {I : Type u} [Category.{w} I] [IsCofiltered I]
    {X : I ⥤ TopCat.{v}} [HasLimit X]
    (S : SpectralSheafSystem X) :
    Nonempty (SpectralSystemSheafDiagramData S) := by
  sorry

noncomputable def spectralSystemSheafDiagramData
    {I : Type u} [Category.{w} I] [IsCofiltered I]
    {X : I ⥤ TopCat.{v}} [HasLimit X]
    (S : SpectralSheafSystem X) : SpectralSystemSheafDiagramData S :=
  Classical.choice (exists_spectralSystemSheafDiagram S)

/-- The diagram of pullbacks of a spectral sheaf system. -/
noncomputable def spectralSystemSheafDiagram
    {I : Type u} [Category.{w} I] [IsCofiltered I]
    {X : I ⥤ TopCat.{v}} [HasLimit X]
    (S : SpectralSheafSystem X) :
    Iᵒᵖ ⥤ TopCat.Sheaf (Type v) (spectralInverseLimitSpace X) :=
  (spectralSystemSheafDiagramData S).diagram

theorem spectralSystemSheafDiagram_obj
    {I : Type u} [Category.{w} I] [IsCofiltered I]
    {X : I ⥤ TopCat.{v}} [HasLimit X]
    (S : SpectralSheafSystem X) (i : Iᵒᵖ) :
    (spectralSystemSheafDiagram S).obj i =
      (pullbackSheaf (spectralInverseLimitProjection X i.unop)).obj
        (S.sheaf i.unop) :=
  (spectralSystemSheafDiagramData S).obj_eq i

/-- Data for the colimit sheaf on the inverse-limit space. -/
structure SpectralSystemLimitSheafData
    {I : Type u} [Category.{w} I] [IsCofiltered I]
    {X : I ⥤ TopCat.{v}} [HasLimit X]
    (S : SpectralSheafSystem X) where
  cocone : Cocone (spectralSystemSheafDiagram S)
  isColimit : IsColimit cocone

/-- The colimit sheaf in the inverse-limit construction exists. -/
theorem exists_spectralSystemLimitSheaf
    {I : Type u} [Category.{w} I] [IsCofiltered I]
    {X : I ⥤ TopCat.{v}} [HasLimit X]
    (S : SpectralSheafSystem X) :
    Nonempty (SpectralSystemLimitSheafData S) := by
  sorry

noncomputable def spectralSystemLimitSheafData
    {I : Type u} [Category.{w} I] [IsCofiltered I]
    {X : I ⥤ TopCat.{v}} [HasLimit X]
    (S : SpectralSheafSystem X) : SpectralSystemLimitSheafData S :=
  Classical.choice (exists_spectralSystemLimitSheaf S)

/-- The sheaf on the inverse-limit space obtained as this colimit. -/
noncomputable def spectralSystemLimitSheaf
    {I : Type u} [Category.{w} I] [IsCofiltered I]
    {X : I ⥤ TopCat.{v}} [HasLimit X]
    (S : SpectralSheafSystem X) :
    TopCat.Sheaf (Type v) (spectralInverseLimitSpace X) :=
  (spectralSystemLimitSheafData S).cocone.pt

/-! ## Sections of the inverse-limit sheaf -/

/-- The source-facing section type `F_j(f_a⁻¹(U_i))`. -/
noncomputable abbrev spectralSystemSectionsAt
    {I : Type u} [Category.{w} I] [IsCofiltered I]
    {X : I ⥤ TopCat.{v}} [HasLimit X]
    (S : SpectralSheafSystem X) (i : I) (Ui : Opens (X.obj i))
    (a : spectralPullbackSectionsIndex i) : Type v :=
  (S.sheaf a.unop.left).presheaf.obj
    (op ((Opens.map (X.map a.unop.hom)).obj Ui))

/-- The transition map on the source's section system. -/
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

/-- Data for the diagram of source-facing section types. -/
structure SpectralSystemSectionsDiagramData
    {I : Type u} [Category.{w} I] [IsCofiltered I]
    {X : I ⥤ TopCat.{v}} [HasLimit X]
    (S : SpectralSheafSystem X) (i : I) (Ui : Opens (X.obj i)) where
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

/-- The colimit of the source's section system. -/
noncomputable def spectralSystemSectionsColimit
    {I : Type u} [Category.{w} I] [IsCofiltered I]
    {X : I ⥤ TopCat.{v}} [HasLimit X]
    (S : SpectralSheafSystem X) (i : I) (Ui : Opens (X.obj i))
    [HasColimit (spectralSystemSectionsDiagram S i Ui)] : Type v :=
  colimit (spectralSystemSectionsDiagram S i Ui)

/-- Sections of the inverse-limit colimit sheaf descend along quasi-compact
opens of a spectral factor. -/
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

/-- A chosen descent equivalence for sections on a quasi-compact open. -/
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

end Formalization.Books.Sheaves.Unit29
