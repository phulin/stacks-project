import Formalization.Books.Sheaves.Unit22.LimitsPresheaves
import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.Topology.Spectral.Basic
import Mathlib.Topology.Spectral.Hom

/-!
# Sheaves on Spaces, Chapter 22, Section 8: Limits and colimits of sheaves

This file records the canonical limit/colimit constructions for sheaves, their
section and stalk comparisons, the directed-colimit lemma, its counterexample,
and the two inverse-limit statements for spectral spaces.
-/

namespace Formalization.Books.Sheaves.Unit22

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
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
  infer_instance

/-- The sectionwise formula for a limit of set-valued sheaves. -/
noncomputable def sheafLimitSectionsIso {X : TopCat.{v}} {J : Type v}
    [Category.{v} J] (F : J ⥤ TopCat.Sheaf (Type v) X) (U : Opens X) :
    (sheafLimit F).presheaf.obj (op U) ≅
      limit (F ⋙ TopCat.Sheaf.forget (Type v) X ⋙
        (evaluation (Opens X)ᵒᵖ (Type v)).obj (op U)) := by
  let e₁ := preservesLimitIso (TopCat.Sheaf.forget (Type v) X) F
  let e₂ := preservesLimitIso
    ((evaluation (Opens X)ᵒᵖ (Type v)).obj (op U))
    (F ⋙ TopCat.Sheaf.forget (Type v) X)
  simpa [sheafLimit] using e₁.trans e₂

/-- Sheafification identifies a sheaf colimit with the sheafification of the
pointwise presheaf colimit. -/
noncomputable def sheafColimitSheafificationIso {X : TopCat.{v}}
    {J : Type v} [Category.{v} J]
    (F : J ⥤ TopCat.Sheaf (Type v) X) [HasColimit F]
    [HasColimit (F ⋙ TopCat.Sheaf.forget (Type v) X)] :
    (sheafColimit F).presheaf ≅
        (CategoryTheory.presheafToSheaf (Opens.grothendieckTopology X) (Type v)).obj
        (colimit (F ⋙ TopCat.Sheaf.forget (Type v) X)) |>.1 := by
  let E := colimit.cocone (F ⋙ TopCat.Sheaf.forget (Type v) X)
  let hE := colimit.isColimit (F ⋙ TopCat.Sheaf.forget (Type v) X)
  let e := (colimit.isColimit F).uniqueUpToIso
    (CategoryTheory.Sheaf.isColimitSheafifyCocone E hE)
  simpa [E] using (TopCat.Sheaf.forget (Type v) X).mapIso e

/-- The inclusion of sheaves into presheaves preserves limits. -/
theorem sheafForgetPreservesLimits {X : TopCat.{v}} {C : Type (v + 1)}
    [Category.{v} C] [HasLimits C] :
    PreservesLimits (TopCat.Sheaf.forget C X) := by
  infer_instance

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

/-- Sheafification does not preserve arbitrary limits in general. -/
theorem sheafificationDoesNotPreserveAllLimits :
    ∃ (X : TopCat.{v}),
      ¬ PreservesLimits
        (CategoryTheory.presheafToSheaf
          (Opens.grothendieckTopology X) (Type v)) := by
  sorry

/-! ## Stalks -/

/-- Stalks commute with finite limits of set-valued sheaves. -/
noncomputable def sheafFiniteLimitStalkIso {X : TopCat.{v}} {J : Type v}
    [Category.{v} J] [Finite J] (F : J ⥤ TopCat.Sheaf (Type v) X) (x : X) :
    (sheafLimit F).presheaf.stalk x ≅
      limit (F ⋙ TopCat.Sheaf.forget (Type v) X ⋙
        TopCat.Presheaf.stalkFunctor (Type v) x) := by
  let e := preservesLimitIso (TopCat.Sheaf.forget (Type v) X) F
  simpa [sheafLimit] using
    ((TopCat.Presheaf.stalkFunctor (Type v) x).mapIso e).trans
      (presheafFiniteLimitStalkIso
        (F ⋙ TopCat.Sheaf.forget (Type v) X) x)

/-- Stalks commute with arbitrary colimits of set-valued sheaves. -/
noncomputable def sheafColimitStalkIso {X : TopCat.{v}} {J : Type v}
    [Category.{v} J] (F : J ⥤ TopCat.Sheaf (Type v) X) (x : X) [HasColimit F]
    [HasColimit (F ⋙ TopCat.Sheaf.forget (Type v) X ⋙
      TopCat.Presheaf.stalkFunctor (Type v) x)] :
    (sheafColimit F).presheaf.stalk x ≅
      colimit (F ⋙ TopCat.Sheaf.forget (Type v) X ⋙
        TopCat.Presheaf.stalkFunctor (Type v) x) := by
  let P := colimit (F ⋙ TopCat.Sheaf.forget (Type v) X)
  let e := sheafColimitSheafificationIso F
  let e' := (TopCat.Presheaf.stalkFunctor (Type v) x).mapIso e
  simpa [P] using e'.trans <|
    (TopCat.Presheaf.sheafifyStalkIso P x).trans
      (presheafColimitStalkIso
        (F ⋙ TopCat.Sheaf.forget (Type v) X) x)

/-! ## Directed colimits of sheaves -/

/-- The topological meaning of quasi-compact for an open in this chapter. -/
def QuasiCompactOpen {X : TopCat.{v}} (U : Opens X) : Prop :=
  IsCompact (U : Set X)

/-- The canonical map from the colimit of sections to sections of the sheaf
colimit. -/
noncomputable def directedColimitSectionsMap {X : TopCat.{v}} {I : Type v}
    [Preorder I] [Nonempty I] [IsDirectedOrder I]
    (F : I ⥤ TopCat.Sheaf (Type v) X) (U : Opens X) [HasColimit F]
    [HasColimit (F ⋙ TopCat.Sheaf.forget (Type v) X ⋙
      (evaluation (Opens X)ᵒᵖ (Type v)).obj (op U))] :
      colimit (F ⋙ TopCat.Sheaf.forget (Type v) X ⋙
      (evaluation (Opens X)ᵒᵖ (Type v)).obj (op U)) →
      (sheafColimit F).presheaf.obj (op U) := by
  let H := F ⋙ TopCat.Sheaf.forget (Type v) X ⋙
    (evaluation (Opens X)ᵒᵖ (Type v)).obj (op U)
  let c : Cocone H :=
    { pt := (sheafColimit F).presheaf.obj (op U)
      ι :=
        { app := fun i => (colimit.ι F i).hom.app (op U)
          naturality := by
            intro i j f
            simpa using congrArg (fun k => k.hom.app (op U))
              ((colimit.ι F).naturality f) } }
  exact colimit.desc H c

/-- All transition maps in a directed system are injective on sections over
an open. -/
def DirectedSectionTransitionsInjective {X : TopCat.{v}} {I : Type v}
    [Preorder I] (F : I ⥤ TopCat.Sheaf (Type v) X) (U : Opens X) : Prop :=
  ∀ {i j : I} (hij : i ≤ j),
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

/-- Injectivity of the canonical directed-colimit section map when all
transition maps are injective. -/
theorem directedColimitSectionsMap_injective_of_injective
    {X : TopCat.{v}} {I : Type v} [Preorder I] [Nonempty I]
    [IsDirectedOrder I] (F : I ⥤ TopCat.Sheaf (Type v) X) (U : Opens X)
    [HasColimit F]
    [HasColimit (F ⋙ TopCat.Sheaf.forget (Type v) X ⋙
      (evaluation (Opens X)ᵒᵖ (Type v)).obj (op U))]
    (hF : DirectedSectionTransitionsInjective F U) :
    Function.Injective (directedColimitSectionsMap F U) := by
  sorry

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
    (hF : DirectedSectionTransitionsInjective F U) :
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

/-- Data expressing the tail-space counterexample to unrestricted sectionwise
directed colimits.  The fields deliberately retain the source's stalk and
global-section conclusions. -/
structure DirectedColimitSectionsCounterexample where
  X : TopCat.{v}
  s1 : X.carrier
  s2 : X.carrier
  xi : ℕ → X.carrier
  open_iff : ∀ U : Set X.carrier, IsOpen U ↔
    (U s1 → ∀ n, U (xi n)) ∧ (U s2 → ∀ n, U (xi n))
  U : ℕ → Opens X
  U_carrier : ∀ n x, (U n : Set X.carrier) x ↔
    ∃ m : ℕ, n ≤ m ∧ x = xi m
  j : ∀ n, (Opens.toTopCat X).obj (U n) ⟶ X
  j_is_inclusion : ∀ n, j n = Opens.inclusion' (U n)
  F : ℕ ⥤ TopCat.Sheaf (Type v) X
  F_is_pushforward_constant :
    ∀ n, F.obj n = (pushforwardSheaf (j n)).obj
      (Formalization.Books.Sheaves.Unit07.constantSheaf
        ((Opens.toTopCat X).obj (U n)) (ULift.{v} ℤ))
  F_colimit_cocone : Cocone F
  F_colimit_is_colimit : IsColimit F_colimit_cocone
  stalk_tail_zero : ∀ {n m}, m < n →
    Nonempty ((F.obj n).presheaf.stalk (xi m) ≃ PEmpty.{v})
  M : Type v
  M_nontrivial : Nontrivial M
  stalk_colimit_tail_zero : ∀ n,
    Nonempty (F_colimit_cocone.pt.presheaf.stalk (xi n) ≃ PEmpty.{v})
  two_skyscraper_sum : TopCat.Sheaf (Type v) X
  two_skyscraper_sum_inl : setSkyscraperSheaf s1 M ⟶ two_skyscraper_sum
  two_skyscraper_sum_inr : setSkyscraperSheaf s2 M ⟶ two_skyscraper_sum
  two_skyscraper_sum_is_coproduct :
    IsColimit (BinaryCofan.mk two_skyscraper_sum_inl two_skyscraper_sum_inr)
  sheaf_is_two_skyscrapers :
    Nonempty (F_colimit_cocone.pt ≅ two_skyscraper_sum)
  global_sections :
    Nonempty (F_colimit_cocone.pt.presheaf.obj (op (⊤ : Opens X)) ≃ M × M)
  colimit_global_sections :
    Nonempty (colimit (F ⋙ TopCat.Sheaf.forget (Type v) X ⋙
      (evaluation (Opens X)ᵒᵖ (Type v)).obj (op (⊤ : Opens X))) ≃ M)

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

/-- The section type attached to an arrow `a : j ⟶ i` in the inverse system. -/
noncomputable abbrev spectralPullbackSectionsAt
    {I : Type u} [Category.{w} I] (X : I ⥤ TopCat.{v}) (i : I)
    (G : TopCat.Sheaf (Type v) (X.obj i)) (Ui : Opens (X.obj i))
    (a : CostructuredArrow (𝟭 I) i) : Type v :=
  ((pullbackSheaf (X.map a.hom)).obj G).presheaf.obj
    (op ((Opens.map (X.map a.hom)).obj Ui))

/-- The diagram of pullback sections indexed by all arrows into `i`.
Its object part is the displayed source expression; the morphism part uses
the canonical pullback comparison for a map of arrows. -/
noncomputable def spectralPullbackSectionsDiagram
    {I : Type u} [Category.{w} I] (X : I ⥤ TopCat.{v}) (i : I)
    (G : TopCat.Sheaf (Type v) (X.obj i)) (Ui : Opens (X.obj i)) :
    CostructuredArrow (𝟭 I) i ⥤ Type v := by
  sorry

/-- The colimit of the pullback-section diagram over arrows `a : j ⟶ i`. -/
noncomputable abbrev spectralPullbackSectionsColimit
    {I : Type u} [Category.{w} I] (X : I ⥤ TopCat.{v}) (i : I)
    (G : TopCat.Sheaf (Type v) (X.obj i)) (Ui : Opens (X.obj i))
    [HasColimit (spectralPullbackSectionsDiagram X i G Ui)] : Type v :=
  colimit (spectralPullbackSectionsDiagram X i G Ui)

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
        (op ((Opens.map (spectralInverseLimitProjection X i)).obj Ui)) := by
  sorry

/-- A cofiltered system of sheaves and `f_a`-maps over a spectral diagram. -/
structure SpectralSheafSystem {I : Type u} [Category.{w} I]
    (X : I ⥤ TopCat.{v}) where
  sheaf : ∀ i, TopCat.Sheaf (Type v) (X.obj i)
  map : ∀ {j i} (a : j ⟶ i),
    FMap (X.map a) (sheaf i) (sheaf j)
  map_comp : ∀ {k j i} (b : k ⟶ j) (a : j ⟶ i),
    HEq (map (b ≫ a)) (fMapComp (map b) (map a))

/-- The sheaf on the inverse-limit space obtained as the colimit of the
pullbacks of a spectral sheaf system. -/
noncomputable def spectralSystemLimitSheaf
    {I : Type u} [Category.{w} I] [IsCofiltered I]
    {X : I ⥤ TopCat.{v}} [HasLimit X]
    (S : SpectralSheafSystem X) :
    TopCat.Sheaf (Type v) (spectralInverseLimitSpace X) := by
  sorry

/-- The source-facing colimit of the sections
`F_j(f_a⁻¹(U_i))` over arrows `a : j ⟶ i`. -/
noncomputable def spectralSystemSectionsColimit
    {I : Type u} [Category.{w} I] [IsCofiltered I]
    {X : I ⥤ TopCat.{v}} [HasLimit X]
    (S : SpectralSheafSystem X) (i : I) (Ui : Opens (X.obj i)) : Type v := by
  sorry

/-- Sections of the colimit system descend along quasi-compact opens of a
spectral inverse-limit factor. -/
noncomputable def spectralSystemDescendOpensEquiv
    {I : Type u} [Category.{w} I] [IsCofiltered I]
    {X : I ⥤ TopCat.{v}} [HasLimit X]
    (hX : IsSpectralSpaceDiagram X) (S : SpectralSheafSystem X)
    (i : I) (Ui : Opens (X.obj i)) (hUi : QuasiCompactOpen Ui) :
    spectralSystemSectionsColimit S i Ui ≃
      (spectralSystemLimitSheaf S).presheaf.obj
        (op ((Opens.map (spectralInverseLimitProjection X i)).obj Ui)) := by
  sorry

end

end Formalization.Books.Sheaves.Unit22
