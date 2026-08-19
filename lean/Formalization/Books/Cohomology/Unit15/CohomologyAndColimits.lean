import Formalization.Books.Cohomology.Unit03.DerivedFunctors
import Formalization.Books.Sheaves.Unit22.AbelianSheaves
import Formalization.Books.Sheaves.Unit31.Infrastructure
import Formalization.Books.Topology.Unit24.LimitsOfSpectralSpaces
import Mathlib.Topology.QuasiSeparated

/-!
# Cohomology of Sheaves, Chapter 15: cohomology and colimits

This file records the filtered-colimit comparison maps, the cohomology
colimit theorem on quasi-separated spaces, the basis criterion for higher
direct images, and the cohomology colimit statement for inverse limits of
spectral spaces.  The categorical colimit and pullback constructions are the
canonical Mathlib and earlier-chapter constructions; proposition-valued
source results are theorem interfaces whose proofs belong to the prove stage.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open Opposite
open Set
open TopologicalSpace
open Formalization.Books.Cohomology.Unit02
open Formalization.Books.Cohomology.Unit03
open Formalization.Books.Sheaves.Unit08
open Formalization.Books.Sheaves.Unit10
open Formalization.Books.Sheaves.Unit22
open Formalization.Books.Topology.Unit24

universe v

namespace Formalization.Books.Cohomology.Unit15

/-! ## Filtered-colimit comparison maps -/

/- The source's directed sets are represented by filtered indexing categories.
   This is the canonical category-theoretic form of a directed system. -/

/- The canonical map
   `colim H^q(U, F_i) → H^q(U, colim F_i)` for sheaves of modules. -/
noncomputable def ringedSpaceModuleCohomologyColimitComparison
    {X : RingedSpace.{v}} {I : Type v} [Category.{v} I] [IsFiltered I]
    (F : I ⥤ Mod X.structureSheaf) (U : Opens X.carrier) (q : ℕ) :
    colimit (F ⋙ ringedSpaceModuleSectionsCohomology X U (q : ℤ)) ⟶
      (ringedSpaceModuleSectionsCohomology X U (q : ℤ)).obj (colimit F) :=
  colimit.desc _
    (Functor.mapCocone
      (ringedSpaceModuleSectionsCohomology X U (q : ℤ))
      (colimit.cocone F))

/- The source's warning that these maps need not be isomorphisms, even in
   degree zero, is recorded as an existence assertion. -/
theorem ringedSpaceModuleCohomologyColimitComparison_not_always_isIso :
    ¬ ∀ (X : RingedSpace.{v}) (I : Type v) [Category.{v} I] [IsFiltered I]
        (F : I ⥤ Mod X.structureSheaf) (U : Opens X.carrier),
        IsIso (ringedSpaceModuleCohomologyColimitComparison F U 0) := by
  sorry

/- The topological hypotheses from the first lemma of the source. -/
def HasQuasiCompactOpenBasis (X : TopCat.{v}) : Prop :=
  ∃ B : Set (Set X), IsTopologicalBasis B ∧
    ∀ U : Set X, U ∈ B → IsCompact U

/- The first source lemma, with the canonical comparison map exposed. -/
theorem quasiSeparated_cohomology_colimit
    {X : RingedSpace.{v}}
    (hBasis : HasQuasiCompactOpenBasis (TopCat.of X.carrier))
    (hIntersections : QuasiSeparatedSpace X.carrier)
    {I : Type v} [Category.{v} I] [IsFiltered I]
    (F : I ⥤ Mod X.structureSheaf) (U : Opens X.carrier)
    (hU : IsCompact (U : Set X.carrier)) (q : ℕ) :
    IsIso (ringedSpaceModuleCohomologyColimitComparison F U q) := by
  sorry

/-! ## Higher direct images -/

/- Cohomology on an open is the earlier global cohomology functor after the
   canonical restriction of sheaves to the open subspace. -/
noncomputable def abelianSheafOpenCohomology
    (X : TopCat.{v}) (U : Opens X) (p : ℕ) :
    Ab X ⥤ AddCommGrpCat.{v} :=
  openSheafRestriction AddCommGrpCat.{v} U ⋙
    abelianSheafCohomology (openSubspace U) (p : ℤ)

/- The canonical map
   `colim H^p(U, F_i) → H^p(U, colim F_i)` for abelian sheaves. -/
noncomputable def abelianSheafOpenCohomologyColimitComparison
    {X : TopCat.{v}} {I : Type v} [Category.{v} I] [IsFiltered I]
    (F : I ⥤ Ab X) (U : Opens X) (p : ℕ) :
    colimit (F ⋙ abelianSheafOpenCohomology X U p) ⟶
      (abelianSheafOpenCohomology X U p).obj (colimit F) :=
  colimit.desc _
    (Functor.mapCocone
      (abelianSheafOpenCohomology X U p) (colimit.cocone F))

/- The basis condition in the higher-direct-image lemma.  Its comparison
   maps are precisely the sectionwise maps used in the source hypothesis. -/
def HigherDirectImageColimitBasis
    {X Y : TopCat.{v}} (f : X ⟶ Y) {I : Type v}
    [Category.{v} I] [IsFiltered I] (F : I ⥤ Ab X) (p : ℕ) : Prop :=
  ∃ B : Set (Set Y), IsTopologicalBasis B ∧
    ∀ V : Opens Y, (V : Set Y) ∈ B →
      IsIso (abelianSheafOpenCohomologyColimitComparison F
        ((Opens.map f).obj V) p)

/- The higher-direct-image colimit lemma. -/
theorem higher_direct_image_colimit
    {X Y : TopCat.{v}} (f : X ⟶ Y) {I : Type v}
    [Category.{v} I] [IsFiltered I] (F : I ⥤ Ab X) (p : ℕ)
    (hBasis : HigherDirectImageColimitBasis f F p) :
    Nonempty
      ((abelianSheafHigherDirectImage f (p : ℤ)).obj (colimit F) ≅
        colimit (F ⋙ abelianSheafHigherDirectImage f (p : ℤ))) := by
  sorry

/-! ## Cohomology on a cofiltered inverse limit of spectral spaces -/

/- The source's system of abelian sheaves and `f`-maps. -/
structure SpectralAbelianSheafSystem
    {I : Type v} [Category.{v} I] (X : I ⥤ TopCat.{v}) where
  sheaf : ∀ i, Ab (X.obj i)
  map : ∀ {j i} (a : j ⟶ i),
    (abelianSheafPullback (X.map a)).obj (sheaf i) ⟶ sheaf j
  map_comp : ∀ {k j i} (b : k ⟶ j) (a : j ⟶ i),
    (abelianSheafPullbackCompIso (X.map b) (X.map a)).hom.app (sheaf i) ≫
        (abelianSheafPullback (X.map b)).map (map a) ≫ map b =
      eqToHom (congrArg (fun g : X.obj k ⟶ X.obj i =>
        (abelianSheafPullback g).obj (sheaf i)) (X.map_comp b a).symm) ≫
        map (b ≫ a)

/- The transition map on the inverse-limit space associated to one arrow in
   the spectral diagram. -/
noncomputable def spectralAbelianSheafTransition
    {I : Type v} [Category.{v} I] [IsCofiltered I]
    (X : I ⥤ TopCat.{v}) [HasLimit X]
    (S : SpectralAbelianSheafSystem X) {j i : I} (a : j ⟶ i) :
    (abelianSheafPullback (spectralInverseLimitProjection X i)).obj
        (S.sheaf i) ⟶
      (abelianSheafPullback (spectralInverseLimitProjection X j)).obj
        (S.sheaf j) := by
  let pj := spectralInverseLimitProjection X j
  let pi := spectralInverseLimitProjection X i
  let fa := X.map a
  have hpi : pj ≫ fa = pi := limit.w X a
  let e :
      (abelianSheafPullback pi).obj (S.sheaf i) ⟶
        (abelianSheafPullback (pj ≫ fa)).obj (S.sheaf i) :=
    eqToHom (congrArg (fun q : spectralInverseLimitSpace X ⟶ X.obj i =>
      (abelianSheafPullback q).obj (S.sheaf i)) hpi.symm)
  exact e ≫
    (abelianSheafPullbackCompIso pj fa).hom.app (S.sheaf i) ≫
      (abelianSheafPullback pj).map (S.map a)

/- The colimit diagram `a : j ⟶ i ↦ f_a^{-1} F_j` on the inverse-limit
   space. -/
noncomputable def spectralAbelianSheafSystemDiagram
    {I : Type v} [Category.{v} I] [IsCofiltered I]
    (X : I ⥤ TopCat.{v}) [HasLimit X]
    (S : SpectralAbelianSheafSystem X) : Iᵒᵖ ⥤
      Ab (spectralInverseLimitSpace X) where
  obj i :=
    (abelianSheafPullback (spectralInverseLimitProjection X i.unop)).obj
      (S.sheaf i.unop)
  map a := spectralAbelianSheafTransition X S a.unop
  map_id := by
    intro i
    sorry
  map_comp := by
    intro i j k a b
    sorry

/- The sheaf `F = colim p_i^{-1} F_i` from the source. -/
noncomputable abbrev spectralAbelianSheafSystemLimitSheaf
    {I : Type v} [Category.{v} I] [IsCofiltered I]
    (X : I ⥤ TopCat.{v}) [HasLimit X]
    (S : SpectralAbelianSheafSystem X) :
    Ab (spectralInverseLimitSpace X) :=
  colimit (spectralAbelianSheafSystemDiagram X S)

/- A source-facing diagram for the local cohomology groups appearing in the
   displayed colimit.  Its object equation exposes exactly
   `H^p(f_a^{-1}(U_i), F_j)` while leaving the canonical transition maps in
   the already-available functorial cohomology API. -/
structure SpectralAbelianSheafLocalCohomologyData
    {I : Type v} [Category.{v} I] [IsCofiltered I]
    (X : I ⥤ TopCat.{v}) [HasLimit X]
    (S : SpectralAbelianSheafSystem X) (i : I) (Ui : Opens (X.obj i))
    (p : ℕ) where
  diagram : spectralPullbackSectionsIndex i ⥤ AddCommGrpCat.{v}
  object_iso : ∀ a,
    Nonempty
      (diagram.obj a ≅
        (abelianSheafOpenCohomology (X.obj a.unop.left)
          ((Opens.map (X.map a.unop.hom)).obj Ui) p).obj
          (S.sheaf a.unop.left))

/- The canonical transition maps supplied by the `f`-maps form such a
   diagram; the construction is deferred with the theorem proofs. -/
theorem exists_spectralAbelianSheafLocalCohomologyData
    {I : Type v} [Category.{v} I] [IsCofiltered I]
    (X : I ⥤ TopCat.{v}) [HasLimit X]
    (S : SpectralAbelianSheafSystem X) (i : I)
    (Ui : Opens (X.obj i)) (p : ℕ) :
    Nonempty (SpectralAbelianSheafLocalCohomologyData X S i Ui p) := by
  sorry

/- The local cohomology colimit theorem. -/
theorem spectral_cohomology_colimit
    {I : Type v} [Category.{v} I] [IsCofiltered I]
    (X : I ⥤ TopCat.{v}) [HasLimit X]
    (hX : IsSpectralDiagram X)
    (S : SpectralAbelianSheafSystem X) (i : I)
    (Ui : Opens (X.obj i)) (hUi : IsCompact (Ui : Set (X.obj i)))
    (p : ℕ) (D : SpectralAbelianSheafLocalCohomologyData X S i Ui p) :
    Nonempty
      (colimit D.diagram ≅
        (abelianSheafOpenCohomology (spectralInverseLimitSpace X)
          ((Opens.map (spectralInverseLimitProjection X i)).obj Ui) p).obj
          (spectralAbelianSheafSystemLimitSheaf X S)) := by
  sorry

/- The global-cohomology diagram used in the final sentence of the source. -/
structure SpectralAbelianSheafGlobalCohomologyData
    {I : Type v} [Category.{v} I] [IsCofiltered I]
    (X : I ⥤ TopCat.{v}) [HasLimit X]
    (S : SpectralAbelianSheafSystem X) (p : ℕ) where
  diagram : Iᵒᵖ ⥤ AddCommGrpCat.{v}
  object_iso : ∀ i,
    Nonempty
      (diagram.obj (op i) ≅
        (abelianSheafCohomology (X.obj i) (p : ℤ)).obj (S.sheaf i))

theorem exists_spectralAbelianSheafGlobalCohomologyData
    {I : Type v} [Category.{v} I] [IsCofiltered I]
    (X : I ⥤ TopCat.{v}) [HasLimit X]
    (S : SpectralAbelianSheafSystem X) (p : ℕ) :
    Nonempty (SpectralAbelianSheafGlobalCohomologyData X S p) := by
  sorry

/- The source's “in particular” assertion for global cohomology. -/
theorem spectral_global_cohomology_colimit
    {I : Type v} [Category.{v} I] [IsCofiltered I]
    (X : I ⥤ TopCat.{v}) [HasLimit X]
    (hX : IsSpectralDiagram X)
    (S : SpectralAbelianSheafSystem X) (p : ℕ)
    (D : SpectralAbelianSheafGlobalCohomologyData X S p) :
    Nonempty
      (colimit D.diagram ≅
        (abelianSheafCohomology (spectralInverseLimitSpace X) (p : ℤ)).obj
          (spectralAbelianSheafSystemLimitSheaf X S)) := by
  sorry

end Formalization.Books.Cohomology.Unit15
