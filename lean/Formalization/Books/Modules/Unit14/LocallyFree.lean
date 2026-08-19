import Formalization.Books.Modules.Unit11.FinitePresentation
import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
import Mathlib.CategoryTheory.Retract
import Mathlib.Topology.LocallyConstant.Basic

/-!
# Sheaves of Modules, Chapter 14: Locally free sheaves

The source definition is expressed with Mathlib's canonical locally-free
predicate.  The finite and fixed-rank variants below package the corresponding
finite local-generator data, while the theorem interfaces retain the source's
ringed-space hypotheses and categorical maps.
-/

namespace Formalization.Books.Modules.Unit14

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Formalization.Books.Modules.Unit03
open Formalization.Books.Modules.Unit10
open Formalization.Books.Modules.Unit11
open Formalization.Books.Sheaves.Unit10
open Formalization.Books.Sheaves.Unit22

universe v

noncomputable section

local notation "Mod" => Formalization.Books.Sheaves.Unit10.Mod

/-! ## Definition `definition-locally-free` -/

/- The source's local isomorphism-to-a-direct-sum definition is Mathlib's
   `SheafOfModules.IsLocallyFree`, whose `LocalGeneratorsData` records the
   covering opens and whose local generator maps are isomorphisms. -/

/-- A sheaf of modules is locally free. -/
abbrev IsLocallyFree {X : RingedSpace.{v}} (F : Mod X.structureSheaf) : Prop :=
  SheafOfModules.IsLocallyFree F

/-- A locally free sheaf whose local bases can be chosen finite. -/
def IsFiniteLocallyFree {X : RingedSpace.{v}} (F : Mod X.structureSheaf) : Prop :=
  ∃ q : SheafOfModules.LocalGeneratorsData.{v} F,
    q.IsLocallyFreeData ∧ ∀ i, Finite (q.generators i).I

/-- A locally free sheaf whose local bases all have cardinality `r`. -/
def IsFiniteLocallyFreeOfRank {X : RingedSpace.{v}}
    (F : Mod X.structureSheaf) (r : ℕ) : Prop :=
  ∃ q : SheafOfModules.LocalGeneratorsData.{v} F,
    q.IsLocallyFreeData ∧
      ∀ i, Nonempty ((q.generators i).I ≃ ULift.{v} (Fin r))

/-- A direct summand, expressed as a categorical retract in the module category. -/
abbrev IsDirectSummand {X : RingedSpace.{v}}
    (F H : Mod X.structureSheaf) : Prop :=
  Nonempty (Retract F H)

/-! The source's first warning about finite and infinite direct sums. -/

/-- Finite direct sums of locally free sheaves are locally free. -/
theorem finite_directSum_isLocallyFree
    {X : RingedSpace.{v}} {I : Type v} [Finite I]
    (F : I → Mod X.structureSheaf)
    (hF : ∀ i, IsLocallyFree (F i)) :
    IsLocallyFree (sheafModuleCoproduct X.structureSheaf F) := by
  sorry

/-- Finite direct sums of finite locally free sheaves are finite locally free. -/
theorem finite_directSum_isFiniteLocallyFree
    {X : RingedSpace.{v}} {I : Type v} [Finite I]
    (F : I → Mod X.structureSheaf)
    (hF : ∀ i, IsFiniteLocallyFree (F i)) :
    IsFiniteLocallyFree (sheafModuleCoproduct X.structureSheaf F) := by
  sorry

/-- The assertion that arbitrary infinite direct sums preserve local freeness. -/
def InfiniteDirectSumsPreserveLocallyFree : Prop :=
  ∀ (X : RingedSpace.{v}) (I : Type v) (_ : Infinite I)
    (F : I → Mod X.structureSheaf),
    (∀ i, IsLocallyFree (F i)) →
      IsLocallyFree (sheafModuleCoproduct X.structureSheaf F)

/-- Infinite direct sums of locally free sheaves are not locally free in general. -/
theorem not_infiniteDirectSumsPreserveLocallyFree :
    ¬ InfiniteDirectSumsPreserveLocallyFree := by
  sorry

/-- An explicit existential form of the infinite-direct-sum warning. -/
def HasInfiniteLocallyFreeDirectSumFailure (X : RingedSpace.{v}) : Prop :=
  ∃ (I : Type v) (_ : Infinite I) (F : I → Mod X.structureSheaf),
    (∀ i, IsLocallyFree (F i)) ∧
      ¬ IsLocallyFree (sheafModuleCoproduct X.structureSheaf F)

theorem exists_infinite_locallyFree_directSum_failure :
    ∃ X : RingedSpace.{v}, HasInfiniteLocallyFreeDirectSumFailure X := by
  sorry

/-! ## Lemmas `lemma-locally-free-quasi-coherent` and
`lemma-pullback-locally-free` -/

/-- A locally free sheaf is quasi-coherent. -/
theorem locallyFree_isQuasiCoherent
    {X : RingedSpace.{v}} {F : Mod X.structureSheaf}
    (hF : IsLocallyFree F) :
    IsQuasiCoherent F := by
  sorry

/-- Pullback along a morphism of ringed spaces preserves local freeness. -/
theorem pullback_isLocallyFree
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y)
    (G : Mod Y.structureSheaf) (hG : IsLocallyFree G)
    [((SheafOfModules.pushforward (F := Opens.map f.continuous)
      f.sharp).IsRightAdjoint)] :
    IsLocallyFree ((sheafModuleRingedSpacePullback f).obj G) := by
  sorry

/-! ## Lemma `lemma-rank` -/

/-- The source's nonzero-stalk hypothesis for the structure sheaf. -/
def StructureSheafHasNonzeroStalks (X : RingedSpace.{v}) : Prop :=
  ∀ x : X,
    Nontrivial (TopCat.Presheaf.stalk (C := RingCat) X.structureSheaf.obj x)

/-- The finite cardinality, or `∞`, of an index type. -/
noncomputable def localFreeIndexRank (I : Type v) : WithTop ℕ :=
  by
    classical
    exact if h : Finite I then
      letI := Fintype.ofFinite I
      Fintype.card I
    else
      ⊤

/-- A rank function has the source's local-cardinality property. -/
def IsLocallyFreeRank
    {X : RingedSpace.{v}} (F : Mod X.structureSheaf)
    (r : X → WithTop ℕ) : Prop :=
  IsLocallyConstant r ∧
    ∀ (x : X) (U : Opens X.carrier) (I : Type v),
      x ∈ U →
      Nonempty (((openModuleRestrictionFunctor X U).obj F) ≅
        (SheafOfModules.free (R := (ringedOpenSubspace X U).structureSheaf) I)) →
      r x = localFreeIndexRank I

/-- A locally free sheaf on a space with nonzero structure-sheaf stalks has a
locally constant rank function. -/
theorem exists_locallyFree_rank
    {X : RingedSpace.{v}} (hX : StructureSheafHasNonzeroStalks X)
    {F : Mod X.structureSheaf} (hF : IsLocallyFree F) :
    ∃ r : X → WithTop ℕ, IsLocallyFreeRank F r := by
  sorry

/-! ## Lemma `lemma-map-finite-locally-free` -/

/-- A map between finite locally free sheaves of the same rank is an
isomorphism exactly when it is an epimorphism. -/
theorem finiteLocallyFreeOfRank_map_isIso_iff_epi
    {X : RingedSpace.{v}} {r : ℕ}
    {F G : Mod X.structureSheaf}
    (φ : F ⟶ G)
    (hF : IsFiniteLocallyFreeOfRank F r)
    (hG : IsFiniteLocallyFreeOfRank G r) :
    IsIso φ ↔ Epi φ := by
  sorry

/-! ## Lemma `lemma-direct-summand-of-locally-free-is-locally-free` -/

/-- All stalks of the structure sheaf are local rings. -/
def StructureSheafHasLocalStalks (X : RingedSpace.{v}) : Prop :=
  ∀ x : X,
    IsLocalRing (TopCat.Presheaf.stalk (C := RingCat) X.structureSheaf.obj x)

/-- A direct summand of a finite locally free sheaf is finite locally free when
the structure-sheaf stalks are local rings. -/
theorem directSummand_of_finiteLocallyFree_isFiniteLocallyFree
    {X : RingedSpace.{v}} (hX : StructureSheafHasLocalStalks X)
    {F H : Mod X.structureSheaf}
    (hH : IsFiniteLocallyFree H)
    (hFH : IsDirectSummand F H) :
    IsFiniteLocallyFree F := by
  sorry

end

end Formalization.Books.Modules.Unit14
