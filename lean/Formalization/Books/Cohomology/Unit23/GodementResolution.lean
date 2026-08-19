import Formalization.Books.Cohomology.Unit09
import Formalization.Books.Sheaves.Unit26.RingedSpaceModules
import Formalization.Books.Categories.Unit23.ExactFunctors
import Formalization.Books.Simplicial.Unit33.Godement
import Formalization.Books.Simplicial.Unit28.HomotopiesAndCosimplicialObjects
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.Topology.Category.TopCat.Basic

/-!
# Cohomology of Sheaves, Chapter 23: Godement resolution

This file records the discrete-space construction, its augmented cosimplicial
standard resolution, and the two resolution statements in the source.  The
categorical statements use the existing sheaf-module, stalk, cosimplicial,
cochain-complex, and homotopy APIs.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open Opposite
open TopologicalSpace
open Formalization.Books.Cohomology.Unit09
open Formalization.Books.Categories.Unit23
open Formalization.Books.Sheaves.Unit10
open Formalization.Books.Sheaves.Unit22
open Formalization.Books.Simplicial.Unit28

universe v

namespace Formalization.Books.Cohomology.Unit23

/-! ## The discrete ringed space -/

/-- The discrete topological space with the same underlying points as `X`. -/
abbrev godementDiscreteTopologicalSpace (X : RingedSpace.{v}) : TopCat.{v} :=
  TopCat.discrete.obj X.carrier

/-- The evident continuous map from the discrete space of points to `X`. -/
noncomputable def godementContinuousMap (X : RingedSpace.{v}) :
    godementDiscreteTopologicalSpace X ⟶ X.carrier :=
  @TopCat.ofHom (X.carrier : Type v) (X.carrier : Type v) ⊥ X.carrier.str
    (@ContinuousMap.mk (X.carrier : Type v) (X.carrier : Type v) ⊥ X.carrier.str
      id (by exact continuous_bot))

/-- The inverse-image structure sheaf on the discrete space. -/
noncomputable abbrev godementDiscreteStructureSheaf (X : RingedSpace.{v}) :
    RingSheaf (godementDiscreteTopologicalSpace X) :=
  (moduleRingSheafPullback (godementContinuousMap X)).obj X.structureSheaf

/-- The ringed space used in the Godement construction. -/
noncomputable abbrev godementDiscreteRingedSpace (X : RingedSpace.{v}) :
    RingedSpace.{v} where
  carrier := godementDiscreteTopologicalSpace X
  structureSheaf := godementDiscreteStructureSheaf X

/-- The canonical morphism from the discrete ringed space to `X`. -/
noncomputable abbrev godementRingedSpaceHom (X : RingedSpace.{v}) :
    RingedSpaceHom (godementDiscreteRingedSpace X) X where
  continuous := godementContinuousMap X
  sharp := moduleSheafPullbackUnit (godementContinuousMap X) X.structureSheaf

instance godementMap_isContinuous (X : RingedSpace.{v}) :
    (Opens.map (godementContinuousMap X)).IsContinuous
      (Opens.grothendieckTopology (X.carrier : TopCat))
      (Opens.grothendieckTopology
        (godementDiscreteRingedSpace X).carrier) := by
  apply Functor.isContinuous_of_coverPreserving
  · exact compatiblePreserving_opens_map (godementContinuousMap X)
  · exact coverPreserving_opens_map (godementContinuousMap X)

/-! The module pushforward is available without an adjointness hypothesis; the
pullback API records the canonical right-adjoint instance explicitly. -/

/-- The direct-image functor on sheaves of modules. -/
noncomputable def godementModulePushforwardFunctor (X : RingedSpace.{v}) :
    Mod (godementDiscreteRingedSpace X).structureSheaf ⥤
      Mod X.structureSheaf :=
  ringedSpaceModulePushforward (godementRingedSpaceHom X)

/-- A chosen instance witnessing the adjointness required by the canonical
module pullback construction. -/
noncomputable def godementModulePushforward_isRightAdjoint
    (X : RingedSpace.{v}) :
    (SheafOfModules.pushforward.{v}
      (F := Opens.map (godementContinuousMap X))
      (godementRingedSpaceHom X).sharp).IsRightAdjoint := by
  sorry

/-- The inverse-image functor on sheaves of modules. -/
noncomputable def godementModulePullbackFunctor (X : RingedSpace.{v}) :
    Mod X.structureSheaf ⥤
    Mod (godementDiscreteRingedSpace X).structureSheaf := by
  letI := godementModulePushforward_isRightAdjoint X
  exact ringedSpaceModulePullback (godementRingedSpaceHom X)

/-- The adjoint pair of inverse image and direct image used by Godement. -/
noncomputable def godementModuleAdjunction (X : RingedSpace.{v}) :
    godementModulePullbackFunctor X ⊣ godementModulePushforwardFunctor X := by
  letI := godementModulePushforward_isRightAdjoint X
  exact ringedSpaceModuleAdjunction (godementRingedSpaceHom X)

/-- In the sheaf-module formulation, flatness of the Godement morphism is the
exactness of its inverse-image functor. -/
theorem godementRingedSpaceHom_isFlat (X : RingedSpace.{v}) :
    IsExact (godementModulePullbackFunctor X) := by
  sorry

instance godementModulePullback_preservesZeroMorphisms
    (X : RingedSpace.{v}) :
    (godementModulePullbackFunctor X).PreservesZeroMorphisms := by
  sorry

/- The source also uses the corresponding reflection of exactness on the
discrete space.  We record it for the three-term complexes that occur in the
proof, using Mathlib's canonical `ShortComplex` interface. -/
theorem godementPullback_exact_iff
    (X : RingedSpace.{v}) (S : ShortComplex (Mod X.structureSheaf)) :
    S.Exact ↔ (S.map (godementModulePullbackFunctor X)).Exact := by
  sorry

/-! ## The endofunctor and its cosimplicial resolution -/

/-- The endofunctor `f_* f^*` on sheaves of modules on `X`. -/
noncomputable def godementEndofunctor (X : RingedSpace.{v}) :
    Mod X.structureSheaf ⥤ Mod X.structureSheaf :=
  godementModulePullbackFunctor X ⋙ godementModulePushforwardFunctor X

/-- The degree-`n` endofunctor in the Godement resolution. -/
abbrev godementTermFunctor (X : RingedSpace.{v}) (n : ℕ) :
    Mod X.structureSheaf ⥤ Mod X.structureSheaf :=
  Formalization.Books.Simplicial.Unit33.godementDegree
    (godementEndofunctor X) n

/-- The degree-`n` Godement term on a sheaf `F`. -/
abbrev godementResolutionTerm (X : RingedSpace.{v})
    (F : Mod X.structureSheaf) (n : ℕ) : Mod X.structureSheaf :=
  (godementTermFunctor X n).obj F

/-- An augmented cosimplicial object of endofunctors with the degree formula
of the Godement resolution.  The canonical construction is the standard
resolution associated to the pullback/pushforward adjunction. -/
structure GodementCosimplicialData (X : RingedSpace.{v}) where
  augmented :
    CosimplicialObject.Augmented (Mod X.structureSheaf ⥤ Mod X.structureSheaf)
  left_eq : augmented.left = 𝟭 (Mod X.structureSheaf)
  degree : ∀ n : ℕ,
    augmented.right.obj (SimplexCategory.mk n) = godementTermFunctor X n

/-- Existence of the standard augmented cosimplicial Godement object. -/
theorem godementCosimplicialData_exists (X : RingedSpace.{v}) :
    Nonempty (GodementCosimplicialData X) := by
  sorry

/-- A chosen augmented cosimplicial Godement object. -/
noncomputable def godementCosimplicialData (X : RingedSpace.{v}) :
    GodementCosimplicialData X :=
  Classical.choice (godementCosimplicialData_exists X)

/-- The augmented cosimplicial Godement object. -/
abbrev godementCosimplicialObject (X : RingedSpace.{v}) :
    CosimplicialObject (Mod X.structureSheaf ⥤ Mod X.structureSheaf) :=
  (godementCosimplicialData X).augmented.right

/-- The augmentation of the endofunctor-valued Godement object. -/
abbrev godementCosimplicialAugmentation (X : RingedSpace.{v}) :
    (CosimplicialObject.const
      (Mod X.structureSheaf ⥤ Mod X.structureSheaf)).obj
      (godementCosimplicialData X).augmented.left ⟶
      godementCosimplicialObject X :=
  (godementCosimplicialData X).augmented.hom

/-- Postcomposition of endofunctors on `X` with `f^*`. -/
noncomputable def godementPostcomposePullback (X : RingedSpace.{v}) :
    (Mod X.structureSheaf ⥤ Mod X.structureSheaf) ⥤
      (Mod X.structureSheaf ⥤
        Mod (godementDiscreteRingedSpace X).structureSheaf) :=
  (Functor.whiskeringRight (Mod X.structureSheaf)
    (Mod X.structureSheaf)
    (Mod (godementDiscreteRingedSpace X).structureSheaf)).obj
      (godementModulePullbackFunctor X)

/-- The pullback of the Godement augmentation is a homotopy equivalence. -/
theorem godementPullbackAugmentation_isHomotopyEquivalence
    (X : RingedSpace.{v}) :
    IsHomotopyEquivalence
      (((CosimplicialObject.whiskering
        (Mod X.structureSheaf ⥤ Mod X.structureSheaf)
        (Mod X.structureSheaf ⥤
          Mod (godementDiscreteRingedSpace X).structureSheaf)).obj
        (godementPostcomposePullback X)).map
        (godementCosimplicialAugmentation X)) := by
  sorry

/-! ## Evaluation on a sheaf and stalks -/

/-- Evaluation of the functor-valued Godement object at `F`. -/
noncomputable def godementResolutionAugmented
    (X : RingedSpace.{v}) (F : Mod X.structureSheaf) :
    CosimplicialObject.Augmented (Mod X.structureSheaf) :=
  (CosimplicialObject.Augmented.whiskering
    (Mod X.structureSheaf ⥤ Mod X.structureSheaf)
    (Mod X.structureSheaf)).obj
    ((evaluation (Mod X.structureSheaf) (Mod X.structureSheaf)).obj F)
    |>.obj (godementCosimplicialData X).augmented

/-- The cochain complex associated to the evaluated Godement cosimplicial
object. -/
noncomputable def godementResolutionCochainComplex
    (X : RingedSpace.{v}) (F : Mod X.structureSheaf) :
    CochainComplex (Mod X.structureSheaf) ℕ :=
  associatedCochainComplexAdditive
    (godementResolutionAugmented X F).right

/-- The terms of the evaluated cosimplicial object are the displayed
`f_* f^*` iterates. -/
theorem godementResolutionCochainComplex_term_formula
    (X : RingedSpace.{v}) (F : Mod X.structureSheaf) (n : ℕ) :
    (godementResolutionCochainComplex X F).X n =
      godementResolutionTerm X F n := by
  sorry

/- The proof of the source lemma uses the stronger fact that direct images
from the discrete space are flasque. -/
theorem godementModulePushforward_isFlasque
    (X : RingedSpace.{v})
    (H : Mod (godementDiscreteRingedSpace X).structureSheaf) :
    FlasqueModule X ((godementModulePushforwardFunctor X).obj H) := by
  sorry

/-- Every term of the Godement resolution is flasque. -/
theorem godementResolutionTerm_isFlasque
    (X : RingedSpace.{v}) (F : Mod X.structureSheaf) (n : ℕ) :
    FlasqueModule X (godementResolutionTerm X F n) := by
  sorry

/-- The stalk functor on sheaves of `O_X`-modules at `x`. -/
abbrev godementStalkFunctor (X : RingedSpace.{v}) (x : X.carrier) :
    Mod X.structureSheaf ⥤
      ModuleCat.{v} (TopCat.Presheaf.stalk (C := RingCat.{v})
        X.structureSheaf.obj x) :=
  moduleStalkFunctor X.structureSheaf x

/-- The stalk of a sheaf of modules. -/
abbrev godementStalkModule (X : RingedSpace.{v})
    (F : Mod X.structureSheaf) (x : X.carrier) :=
  (godementStalkFunctor X x).obj F

/-- The stalkwise cochain complex of the Godement resolution. -/
noncomputable def godementStalkCochainComplex
    (X : RingedSpace.{v}) (F : Mod X.structureSheaf) (x : X.carrier) :
    CochainComplex
      (ModuleCat.{v} (TopCat.Presheaf.stalk (C := RingCat.{v})
        X.structureSheaf.obj x)) ℕ :=
  associatedCochainComplexAdditive
    (((CosimplicialObject.whiskering
      (Mod X.structureSheaf) (ModuleCat.{v}
        (TopCat.Presheaf.stalk (C := RingCat.{v}) X.structureSheaf.obj x))).obj
      (godementStalkFunctor X x)).obj
      (godementResolutionAugmented X F).right)

/-- Data for the source's stalkwise homotopy-equivalence statement. -/
structure GodementStalkResolutionData
    (X : RingedSpace.{v}) (F : Mod X.structureSheaf) (x : X.carrier) where
  augmentation :
    (CochainComplex.single₀ _).obj (godementStalkModule X F x) ⟶
      godementStalkCochainComplex X F x
  homotopy_equivalence :
    HomologicalComplex.homotopyEquivalences _ (ComplexShape.up ℕ) augmentation

/-- Existence of the stalkwise homotopy-equivalence data. -/
theorem godementStalkResolutionData_exists
    (X : RingedSpace.{v}) (F : Mod X.structureSheaf) (x : X.carrier) :
    Nonempty (GodementStalkResolutionData X F x) := by
  sorry

/-- A chosen stalkwise Godement resolution map. -/
noncomputable def godementStalkResolutionData
    (X : RingedSpace.{v}) (F : Mod X.structureSheaf) (x : X.carrier) :
    GodementStalkResolutionData X F x :=
  Classical.choice (godementStalkResolutionData_exists X F x)

/-- The stalkwise Godement augmentation is a homotopy equivalence. -/
theorem godementStalkResolution_homotopyEquivalence
    (X : RingedSpace.{v}) (F : Mod X.structureSheaf) (x : X.carrier) :
    HomologicalComplex.homotopyEquivalences _ (ComplexShape.up ℕ)
      (godementStalkResolutionData X F x).augmentation :=
  (godementStalkResolutionData X F x).homotopy_equivalence

/-! ## Bounded-below complexes -/

/-- The complete output data of the bounded-below Godement resolution lemma. -/
structure GodementBoundedBelowResolutionData
    (X : RingedSpace.{v}) (F : CochainComplex (Mod X.structureSheaf) ℤ) where
  complex : CochainComplex (Mod X.structureSheaf) ℤ
  map : F ⟶ complex
  quasi_isomorphism : QuasiIso map
  bounded_below : ∃ n : ℤ, complex.IsStrictlyGE n
  termwise_flasque : ∀ n : ℤ, FlasqueModule X (complex.X n)
  stalkwise_homotopy_equivalence : ∀ x : X.carrier,
    HomologicalComplex.homotopyEquivalences _ (ComplexShape.up ℤ)
      (((godementStalkFunctor X x).mapHomologicalComplex (ComplexShape.up ℤ)).map map)

/-- The bounded-below Godement resolution exists for every bounded-below
complex of sheaves of modules. -/
theorem godementBoundedBelowResolutionData_exists
    (X : RingedSpace.{v}) (F : CochainComplex (Mod X.structureSheaf) ℤ)
    (hF : ∃ n : ℤ, F.IsStrictlyGE n) :
    Nonempty (GodementBoundedBelowResolutionData X F) := by
  sorry

/-- A chosen bounded-below Godement resolution. -/
noncomputable def godementBoundedBelowResolutionData
    (X : RingedSpace.{v}) (F : CochainComplex (Mod X.structureSheaf) ℤ)
    (hF : ∃ n : ℤ, F.IsStrictlyGE n) :
    GodementBoundedBelowResolutionData X F :=
  Classical.choice (godementBoundedBelowResolutionData_exists X F hF)

/- The source lemma in projection form: the chosen map is a quasi-isomorphism,
the target is bounded below and termwise flasque, and all stalk maps are
homotopy equivalences. -/
theorem godementResolution_boundedBelow
    (X : RingedSpace.{v}) (F : CochainComplex (Mod X.structureSheaf) ℤ)
    (hF : ∃ n : ℤ, F.IsStrictlyGE n) :
    ∃ (G : CochainComplex (Mod X.structureSheaf) ℤ) (φ : F ⟶ G),
      QuasiIso φ ∧
      (∃ n : ℤ, G.IsStrictlyGE n) ∧
      (∀ n : ℤ, FlasqueModule X (G.X n)) ∧
      (∀ x : X.carrier,
        HomologicalComplex.homotopyEquivalences _ (ComplexShape.up ℤ)
          (((godementStalkFunctor X x).mapHomologicalComplex
            (ComplexShape.up ℤ)).map φ)) := by
  let D := godementBoundedBelowResolutionData X F hF
  exact ⟨D.complex, D.map, D.quasi_isomorphism, D.bounded_below,
    D.termwise_flasque, D.stalkwise_homotopy_equivalence⟩

end Formalization.Books.Cohomology.Unit23
