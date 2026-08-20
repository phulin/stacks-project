import Formalization.Books.Cohomology.Unit20.FilteredComplexes
import Formalization.Books.Cohomology.Unit09
import Mathlib.AlgebraicTopology.SimplicialObject.Basic

/-!
# Cohomology of Sheaves, Chapter 20, Section 4: Godement resolution
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open Opposite
open TopologicalSpace
open Formalization.Books.Cohomology.Unit08
open Formalization.Books.Cohomology.Unit09
open Formalization.Books.Cohomology.Unit20
open Formalization.Books.Derived.Unit08
open Formalization.Books.Sheaves.Unit10
open Formalization.Books.Sheaves.Unit25

universe v

namespace Formalization.Books.Cohomology.Unit20

structure DiscreteRingedSpaceData (X : RingedSpace.{v}) where
  discrete : RingedSpace.{v}
  map : RingedSpaceHom discrete X
  flat : FlatRingedSpaceHomData map

theorem exists_discreteRingedSpaceData (X : RingedSpace.{v}) :
    Nonempty (DiscreteRingedSpaceData X) := by
  sorry

noncomputable def discreteRingedSpaceData (X : RingedSpace.{v}) :
    DiscreteRingedSpaceData X :=
  Classical.choice (exists_discreteRingedSpaceData X)

noncomputable def godementMonad (X : RingedSpace.{v}) :
    Mod X.structureSheaf ⥤ Mod X.structureSheaf :=
  (discreteRingedSpaceData X).flat.pullback ⋙
    Formalization.Books.Sheaves.Unit26.ringedSpaceModulePushforward
      (discreteRingedSpaceData X).map

noncomputable def godementCosimplicialTerm
    (X : RingedSpace.{v}) : ℕ →
      (Mod X.structureSheaf ⥤ Mod X.structureSheaf)
  | 0 => 𝟭 _
  | n + 1 => godementMonad X ⋙ godementCosimplicialTerm X n

noncomputable def godementAugmentation (X : RingedSpace.{v}) :
    𝟭 (Mod X.structureSheaf) ⟶ godementCosimplicialTerm X 1 :=
  (discreteRingedSpaceData X).flat.adjunction.unit

structure GodementCosimplicialData (X : RingedSpace.{v}) where
  object : CosimplicialObject (Mod X.structureSheaf ⥤ Mod X.structureSheaf)
  augmentation : 𝟭 (Mod X.structureSheaf) ⟶
    object.obj (SimplexCategory.mk 1)
  term : ∀ n : ℕ, Nonempty
    (object.obj (SimplexCategory.mk n) ≅ godementCosimplicialTerm X n)
  term_zero : Nonempty
    (object.obj (SimplexCategory.mk 0) ≅ 𝟭 (Mod X.structureSheaf))
  term_one : Nonempty
    (object.obj (SimplexCategory.mk 1) ≅ godementCosimplicialTerm X 1)
  augmented : Prop
  homotopy_equivalent_after_pullback : Prop

theorem exists_godementCosimplicialData (X : RingedSpace.{v}) :
    Nonempty (GodementCosimplicialData X) := by
  sorry

noncomputable def godementCosimplicialData (X : RingedSpace.{v}) :
    GodementCosimplicialData X :=
  Classical.choice (exists_godementCosimplicialData X)

/-! The augmented Godement resolution of a single sheaf.  The differential
    is indexed over `ℤ` so that its exactness is expressed by ordinary
    `ShortComplex.Exact` fields, including the augmentation. -/

structure GodementResolution
    {X : RingedSpace.{v}} (F : Mod X.structureSheaf) where
  term : ℤ → Mod X.structureSheaf
  augmentation : F ⟶ term 0
  differential : ∀ n : ℤ, term n ⟶ term (n + 1)
  augmentation_square : augmentation ≫ differential 0 = 0
  differential_square : ∀ n : ℤ,
    differential n ≫ differential (n + 1) = 0
  exact_augmentation :
    (ShortComplex.mk augmentation (differential 0) augmentation_square).Exact
  exact_terms : ∀ n : ℤ,
    (ShortComplex.mk (differential n) (differential (n + 1))
      (differential_square n)).Exact
  flasque : ∀ n : ℤ, FlasqueModule X (term n)
  stalkwise_homotopy_equivalence : ∀ x : X, Prop

theorem exists_godementResolution
    {X : RingedSpace.{v}} (F : Mod X.structureSheaf) :
    Nonempty (GodementResolution F) := by
  sorry

noncomputable def godementResolution
    {X : RingedSpace.{v}} (F : Mod X.structureSheaf) :
    GodementResolution F :=
  Classical.choice (exists_godementResolution F)

structure BoundedBelowGodementResolutionData
    {X : RingedSpace.{v}} (K : ModuleComplex X) where
  resolution : ModuleComplex X
  map : K ⟶ resolution
  quasiIso : QuasiIso map
  boundedBelow : IsBoundedBelow resolution
  termwiseFlasque : ∀ n : ℤ, FlasqueModule X (resolution.X n)
  stalkwiseHomotopyEquivalence : ∀ x : X, Prop

theorem exists_boundedBelowGodementResolution
    {X : RingedSpace.{v}} (K : ModuleComplex X)
    (hK : IsBoundedBelow K) :
    Nonempty (BoundedBelowGodementResolutionData K) := by
  sorry

end Formalization.Books.Cohomology.Unit20
