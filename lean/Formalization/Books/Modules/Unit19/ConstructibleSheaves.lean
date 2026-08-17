import Formalization.Books.Sheaves.Unit16.ExactnessAndPoints
import Formalization.Books.Sheaves.Unit22.ClosedImmersions
import Formalization.Books.Sheaves.Unit22.OpenImmersions
import Formalization.Books.Topology.Unit23.SpectralSpaces
import Mathlib.CategoryTheory.Filtered.Basic

/-!
# Modules, Chapter 19, Section 1: Constructible sheaves of sets

The source section is formalized here using the canonical set-valued sheaf,
pushforward, pullback, colimit, spectral-space, and subsheaf interfaces from
the earlier chapters and from Mathlib.
-/

namespace Formalization.Books.Modules.Unit19

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Formalization.Books.Sheaves.Unit07
open Formalization.Books.Sheaves.Unit16
open Formalization.Books.Sheaves.Unit21
open Formalization.Books.Sheaves.Unit22

universe u

noncomputable section

/-! ## The coproducts and finite coequalizer presentations in the source -/

/-- The coproduct of extensions by the empty set of constant sheaves on opens.

The `U` and `S` arguments are allowed to be indexed by an arbitrary type so
that the same construction can be used for the source's arbitrary coproduct
and its finite coproducts.
-/
noncomputable def openExtensionCoproduct {X : TopCat.{u}} (I : Type u)
    (U : I → Opens X) (S : I → Type u) : TopCat.Sheaf (Type u) X :=
  letI : HasColimitsOfSize.{u, u} (TopCat.Sheaf (Type u) X) :=
    Formalization.Books.Sheaves.Unit22.sheaf_has_colimits (X := X)
  colimit (Discrete.functor fun i =>
    (Formalization.Books.Sheaves.Unit22.openSetSheafExtensionByEmpty (U i)).obj
      (Formalization.Books.Sheaves.Unit07.constantSheaf
        (Formalization.Books.Sheaves.Unit22.openSubspace (U i)) (S i)))

/-- The set of quasi-compact open subsets of a topological space. -/
def quasiCompactOpenBasis (X : TopCat.{u}) : Set (Opens X) :=
  {U : Opens X | IsCompact (U : Set X)}

/-- A finite coequalizer presentation by extensions of finite constant sheaves.

The two maps are retained explicitly, together with the colimit cocone, so
the displayed coequalizer in the source is available as a usable categorical
interface rather than only as an informal predicate.
-/
structure FiniteOpenCoequalizerPresentation
    {X : TopCat.{u}} (B : Set (Opens X))
    (F : TopCat.Sheaf (Type u) X) where
  m : ℕ
  n : ℕ
  U : Fin n → Opens X
  V : Fin m → Opens X
  U_mem : ∀ a, U a ∈ B
  V_mem : ∀ b, V b ∈ B
  S : Fin n → Type u
  T : Fin m → Type u
  finiteS : ∀ a, Finite (S a)
  finiteT : ∀ b, Finite (T b)
  left :
    openExtensionCoproduct (X := X) (ULift.{u} (Fin m))
        (fun i => V i.down) (fun i => T i.down) ⟶
      openExtensionCoproduct (X := X) (ULift.{u} (Fin n))
        (fun i => U i.down) (fun i => S i.down)
  right :
    openExtensionCoproduct (X := X) (ULift.{u} (Fin m))
        (fun i => V i.down) (fun i => T i.down) ⟶
      openExtensionCoproduct (X := X) (ULift.{u} (Fin n))
        (fun i => U i.down) (fun i => S i.down)
  augmentation :
    openExtensionCoproduct (X := X) (ULift.{u} (Fin n))
        (fun i => U i.down) (fun i => S i.down) ⟶ F
  relation_condition : left ≫ augmentation = right ≫ augmentation
  isColimit : IsColimit (Cofork.ofπ augmentation relation_condition)

/-- A sheaf has the finite coequalizer presentation used in the source. -/
def IsFiniteOpenCoequalizerSheaf {X : TopCat.{u}} (B : Set (Opens X))
    (F : TopCat.Sheaf (Type u) X) : Prop :=
  Nonempty (FiniteOpenCoequalizerPresentation B F)

/-- A filtered colimit presentation whose stages have the source's finite form. -/
structure FilteredFiniteOpenCoequalizerColimit
    {X : TopCat.{u}} (B : Set (Opens X))
    (F : TopCat.Sheaf (Type u) X) where
  index : Type u
  [indexCategory : Category index]
  [indexFiltered : IsFiltered index]
  diagram : index ⥤ TopCat.Sheaf (Type u) X
  stagesInPresentation : ∀ i, IsFiniteOpenCoequalizerSheaf B (diagram.obj i)
  cocone : Cocone diagram
  isColimit : IsColimit cocone
  targetIso : cocone.pt ≅ F

/-! ## The four assertions in the source section -/

/-- Every sheaf of sets is covered by a coproduct of extended finite constants.

The source proof chooses singleton constants, but its statement permits an
arbitrary finite set at each basis open, which is recorded here exactly.
-/
theorem lemma_surjection {X : TopCat.{u}} (B : Set (Opens X))
    (hB : Opens.IsBasis B) (F : TopCat.Sheaf (Type u) X) :
    ∃ (I : Type u) (U : I → Opens X) (S : I → Type u),
      (∀ i, U i ∈ B) ∧ (∀ i, Finite (S i)) ∧
        ∃ φ : openExtensionCoproduct (X := X) I U S ⟶ F,
          SheafSurjective φ := by
  sorry

/-- Every sheaf is a filtered colimit of finite coequalizer presentations. -/
theorem lemma_filtered_colimit_constructibles {X : TopCat.{u}}
    (B : Set (Opens X)) (hB : Opens.IsBasis B)
    (hB_quasiCompact : ∀ U : Opens X, U ∈ B → IsCompact (U : Set X))
    (F : TopCat.Sheaf (Type u) X) :
    Nonempty (FilteredFiniteOpenCoequalizerColimit B F) := by
  sorry

/-- A finite coequalizer presentation descends from a spectral space to a
finite sober space, with finite-stalk sheaf pullback. -/
theorem lemma_constructible_comes_from_finite {X : TopCat.{u}}
    [SpectralSpace (X : Type u)]
    (F : TopCat.Sheaf (Type u) X)
    (hF : IsFiniteOpenCoequalizerSheaf (quasiCompactOpenBasis X) F) :
    ∃ (Y : TopCat.{u}),
      Finite (Y : Type u) ∧ QuasiSober (Y : Type u) ∧ T0Space (Y : Type u) ∧
        ∃ (f : X ⟶ Y), IsSpectralMap f ∧
          ∃ (G : TopCat.Sheaf (Type u) Y),
            (∀ y : Y, Finite (G.presheaf.stalk y)) ∧
              Nonempty ((pullbackSheaf f).obj G ≅ F) := by
  sorry

/-- Constructible-closed subsets, i.e. closed subsets for the constructible
topology of a spectral space. -/
abbrev IsConstructibleClosed {X : TopCat.{u}} (Z : Set X) : Prop :=
  @IsClosed (X : Type u) (constructibleTopology (X : Type u)) Z

/-- A finite product of pushforwards of constant sheaves from subspaces. -/
noncomputable def constructibleClosedPushforwardProduct
    {X : TopCat.{u}} (n : ℕ) (Z : Fin n → Set X)
    (S : Fin n → Type u) : TopCat.Sheaf (Type u) X :=
  limit (Discrete.functor fun i =>
    (pushforwardSheaf (Formalization.Books.Sheaves.Unit22.closedInclusion (Z i))).obj
      (Formalization.Books.Sheaves.Unit07.constantSheaf
        (Formalization.Books.Sheaves.Unit22.closedSubspace (Z i)) (S i)))

/-- A sheaf with a finite presentation embeds, up to isomorphism, into a
finite product of constant pushforwards from constructible-closed subsets. -/
theorem lemma_constructible_in_constant {X : TopCat.{u}}
    [SpectralSpace (X : Type u)]
    (F : TopCat.Sheaf (Type u) X)
    (hF : IsFiniteOpenCoequalizerSheaf (quasiCompactOpenBasis X) F) :
    ∃ (n : ℕ) (Z : Fin n → Set X) (S : Fin n → Type u),
      (∀ i, IsConstructibleClosed (Z i)) ∧ (∀ i, Finite (S i)) ∧
        ∃ H : TopCat.Sheaf (Type u) X,
          Nonempty (F ≅ H) ∧
            IsSubsheaf H.presheaf
              (constructibleClosedPushforwardProduct n Z S).presheaf := by
  sorry

end
end Formalization.Books.Modules.Unit19
