import Formalization.Books.Categories.Unit23.ExactFunctors
import Formalization.Books.Modules.Unit08.LocallyGenerated
import Formalization.Books.Sheaves.Unit07.Sheaves
import Formalization.Books.Sheaves.Unit11.Stalks
import Formalization.Books.Sheaves.Unit15.AlgebraicStructures
import Formalization.Books.Sheaves.Unit16.ExactnessAndPoints
import Formalization.Books.Sheaves.Unit27.Skyscraper
import Formalization.Books.Sheaves.Unit31.OpenImmersions
import Mathlib.Data.ZMod.Basic
import Mathlib.CategoryTheory.Sites.Limits

/-!
# Exercises, Chapter 32: Sheaves

This file contains the reusable objects appearing in the exercises in the
chapter on sheaves.  The categorical constructions are the canonical Mathlib
and earlier-book constructions; the proposition-valued exercise statements are
in `Statements.lean`.
-/

namespace Formalization.Books.Exercises.Unit32

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open _root_.Topology
open scoped ZeroObject

open Formalization.Books.Sheaves.Unit07
open Formalization.Books.Sheaves.Unit08
open Formalization.Books.Sheaves.Unit11
open Formalization.Books.Sheaves.Unit15
open Formalization.Books.Sheaves.Unit16
open Formalization.Books.Sheaves.Unit27
open Formalization.Books.Sheaves.Unit31

universe u v w

noncomputable section

/-! ## Basic sheaf categories and stalk maps -/

/-- The category of sheaves of sets on `X`. -/
abbrev SetSheaves (X : TopCat.{v}) := TopCat.Sheaf (Type v) X

/-- The category of sheaves of abelian groups on `X`. -/
abbrev AbelianSheaves (X : TopCat.{v}) := Ab X

/-- The map on stalks induced by a morphism of sheaves of sets. -/
noncomputable abbrev setStalkMap {X : TopCat.{v}}
    {F G : SetSheaves X} (φ : F ⟶ G) (x : X) :
    F.presheaf.stalk x → G.presheaf.stalk x :=
  (TopCat.Presheaf.stalkFunctor (Type v) x).map φ.hom

/-- The map on stalks induced by a morphism of abelian sheaves. -/
noncomputable abbrev abelianStalkMap {X : TopCat.{v}}
    {F G : AbelianSheaves X} (φ : F ⟶ G) (x : X) :
    F.presheaf.stalk x ⟶ G.presheaf.stalk x :=
  (TopCat.Presheaf.stalkFunctor (AddCommGrpCat.{v}) x).map φ.hom

/-! ## Pushforward, pullback, and open immersions -/

/-- Pushforward of sheaves of sets along a continuous map. -/
noncomputable abbrev sheafPushforward {X Y : TopCat.{v}} (f : X ⟶ Y) :
    SetSheaves X ⥤ SetSheaves Y :=
  TopCat.Sheaf.pushforward (Type v) f

/-- Pullback of sheaves of sets along a continuous map. -/
noncomputable abbrev sheafPullback {X Y : TopCat.{v}} (f : X ⟶ Y) :
    SetSheaves Y ⥤ SetSheaves X :=
  TopCat.Sheaf.pullback (Type v) f

/-- The pullback/pushforward adjunction for sheaves of sets. -/
noncomputable def sheafPullbackPushforwardAdjunction
    {X Y : TopCat.{v}} (f : X ⟶ Y) :
    sheafPullback f ⊣ sheafPushforward f :=
  TopCat.Sheaf.pullbackPushforwardAdjunction (Type v) f

/-- The extension-by-empty functor for sheaves of sets on an open subspace. -/
noncomputable abbrev extensionByEmpty {X : TopCat.{v}} (U : Opens X) :
    SetSheaves (openSubspace U) ⥤ SetSheaves X :=
  openSetSheafExtensionByEmpty U

/-- Restriction of sheaves of sets to an open subspace. -/
noncomputable abbrev restrictionToOpen {X : TopCat.{v}} (U : Opens X) :
    SetSheaves X ⥤ SetSheaves (openSubspace U) :=
  openSheafRestriction (Type v) U

/-- The extension-by-empty/restriction adjunction. -/
noncomputable def extensionByEmptyAdjunction {X : TopCat.{v}} (U : Opens X) :
    extensionByEmpty U ⊣ restrictionToOpen U :=
  openSheafExtensionAdjunction (Type v) U

/-- The extension-by-zero functor for abelian sheaves on an open subspace. -/
noncomputable abbrev extensionByZero {X : TopCat.{v}} (U : Opens X) :
    AbelianSheaves (openSubspace U) ⥤ AbelianSheaves X :=
  openAbelianSheafExtensionFunctor U

/-- Restriction of abelian sheaves to an open subspace. -/
noncomputable abbrev abelianRestrictionToOpen {X : TopCat.{v}} (U : Opens X) :
    AbelianSheaves X ⥤ AbelianSheaves (openSubspace U) :=
  openSheafRestriction AddCommGrpCat U

/-- The extension-by-zero/restriction adjunction. -/
noncomputable def extensionByZeroAdjunction {X : TopCat.{v}} (U : Opens X) :
    extensionByZero U ⊣ abelianRestrictionToOpen U :=
  openAbelianSheafExtensionAdjunction U

/-- The integral constant sheaf used in the generation exercise. -/
noncomputable abbrev integerConstantSheaf {X : TopCat.{v}} : AbelianSheaves X :=
  Formalization.Books.Modules.Unit08.integralConstantSheaf

/-- Extension by zero of the integral constant sheaf on an open. -/
noncomputable def integerExtensionByZero {X : TopCat.{v}} (U : Opens X) :
    AbelianSheaves X :=
  (extensionByZero U).obj
    (integerConstantSheaf (X := openSubspace U))

/-! ## The real-line skyscraper example -/

/-- The real line as a topological category. -/
abbrev realLine : TopCat := Formalization.Books.Modules.Unit08.realLine

/-- The origin of the real line. -/
abbrev realOrigin : realLine := (0 : ℝ)

/-- The constant sheaf with value `ZMod 2` on the real line. -/
def realConstantZModTwo : SetSheaves realLine :=
  Formalization.Books.Sheaves.Unit07.constantSheaf realLine (ZMod 2)

/-- The skyscraper sheaf at the origin with value `ZMod 2`. -/
noncomputable def realOriginSkyscraper : SetSheaves realLine :=
  Formalization.Books.Sheaves.Unit27.setSkyscraperSheaf realOrigin (ZMod 2)

/-- The stalk map from the constant sheaf to its value at the origin. -/
noncomputable def realConstantZModTwoStalkMap :
    realConstantZModTwo.presheaf.stalk realOrigin → ZMod 2 :=
  (Formalization.Books.Sheaves.Unit11.constantSheafStalkEquiv
    (X := realLine) (ZMod 2) realOrigin).symm

/-- The canonical map from the constant sheaf to the origin skyscraper. -/
noncomputable def realConstantToOriginSkyscraper :
    realConstantZModTwo ⟶ realOriginSkyscraper :=
  (Formalization.Books.Sheaves.Unit27.setStalkSkyscraperHomEquiv
    realOrigin realConstantZModTwo (ZMod 2))
    (TypeCat.ofHom realConstantZModTwoStalkMap)

/-- The zero map with the same source and target as the canonical map. -/
noncomputable def realConstantToOriginSkyscraperZero :
    realConstantZModTwo ⟶ realOriginSkyscraper :=
  (Formalization.Books.Sheaves.Unit27.setStalkSkyscraperHomEquiv
    realOrigin realConstantZModTwo (ZMod 2))
    (TypeCat.ofHom (fun _ => 0))

/-- The kernel subsheaf of the canonical constant-to-skyscraper map. -/
noncomputable def realKernelSheaf : SetSheaves realLine :=
  limit (parallelPair realConstantToOriginSkyscraper
    realConstantToOriginSkyscraperZero)

/-- The inclusion of the kernel subsheaf in the constant sheaf. -/
noncomputable def realKernelInclusion :
    realKernelSheaf ⟶ realConstantZModTwo :=
  limit.π (parallelPair realConstantToOriginSkyscraper
    realConstantToOriginSkyscraperZero) WalkingParallelPair.zero

/-- The additive constant sheaf with value `ZMod 2`. -/
noncomputable def realAbelianConstantZModTwo : AbelianSheaves realLine :=
  (CategoryTheory.constantSheaf
    (Opens.grothendieckTopology realLine) AddCommGrpCat).obj
      (AddCommGrpCat.of (ZMod 2))

/-- The additive skyscraper sheaf at the origin with value `ZMod 2`. -/
noncomputable def realAbelianOriginSkyscraper : AbelianSheaves realLine :=
  Formalization.Books.Sheaves.Unit27.abelianSkyscraperSheaf realOrigin
    (AddCommGrpCat.of (ZMod 2))

/-- Existence of the canonical additive constant-to-skyscraper map. -/
theorem exists_realAbelianConstantToOriginSkyscraper :
    Nonempty (realAbelianConstantZModTwo ⟶ realAbelianOriginSkyscraper) := by
  sorry

/-- A chosen additive constant-to-skyscraper map. -/
noncomputable def realAbelianConstantToOriginSkyscraper :
    realAbelianConstantZModTwo ⟶ realAbelianOriginSkyscraper :=
  Classical.choice exists_realAbelianConstantToOriginSkyscraper

/-- The zero map from the additive constant sheaf to the additive skyscraper. -/
noncomputable def realAbelianConstantToOriginSkyscraperZero :
    realAbelianConstantZModTwo ⟶ realAbelianOriginSkyscraper :=
  0

/-- The additive kernel sheaf in the real-line example. -/
noncomputable def realIdealSheaf : AbelianSheaves realLine :=
  limit (parallelPair realAbelianConstantToOriginSkyscraper
    realAbelianConstantToOriginSkyscraperZero)

/-- The inclusion of the additive kernel in the constant additive sheaf. -/
noncomputable def realIdealSheafInclusion :
    realIdealSheaf ⟶ realAbelianConstantZModTwo :=
  limit.π (parallelPair realAbelianConstantToOriginSkyscraper
    realAbelianConstantToOriginSkyscraperZero) WalkingParallelPair.zero

/-! ## Ideal sheaves and generation -/

/-- The additive-group part of a commutative ring, used to state the image
condition for an ideal sheaf without crossing two forgetful functors. -/
def commRingToAddCommGrp : CommRingCat ⥤ AddCommGrpCat where
  obj R := AddCommGrpCat.of (R : Type)
  map f := AddCommGrpCat.ofHom f.hom.toAddMonoidHom
  map_id R := by rfl
  map_comp f g := by rfl

/-- A sheaf of abelian groups is an ideal sheaf in a specified sheaf of
commutative rings when its presheaf inclusion has ideal image on every open. -/
def IsIdealSheafIn {X : TopCat.{v}} (O : TopCat.Sheaf CommRingCat X)
    (I : AbelianSheaves X) : Prop :=
  ∃ ι : I.presheaf ⋙ (forget AddCommGrpCat) ⟶
      O.presheaf ⋙ commRingToAddCommGrp ⋙ (forget AddCommGrpCat),
    ∀ U : Opens X,
      ∃ J : Ideal (O.presheaf.obj (op U)),
        Set.range (ι.app (op U)) = (J : Set (O.presheaf.obj (op U)))

/-! ## Direct sums and the quotient exercise -/

/-- The restriction map on the sectionwise direct sum of a family of abelian
sheaves. -/
noncomputable def abelianSheafDirectSumMap
    {X : TopCat.{v}} {I : Type v} (F : I → AbelianSheaves X)
    {U V : (Opens X)ᵒᵖ} (f : U ⟶ V) :
    (DirectSum I (fun i : I => ((F i).presheaf.obj U : Type v))) →+
      (DirectSum I (fun i : I => ((F i).presheaf.obj V : Type v))) := by
  classical
  exact DirectSum.toAddMonoid (fun i =>
    (DirectSum.of (fun i : I => ((F i).presheaf.obj V : Type v) ) i).comp
      ((F i).presheaf.map f).hom)

/-- The presheaf whose sections are the direct sums of the sections of the
given family. -/
noncomputable def abelianSheafDirectSumPresheaf
    {X : TopCat.{v}} {I : Type v} (F : I → AbelianSheaves X) :
    TopCat.Presheaf AddCommGrpCat X where
  obj U := AddCommGrpCat.of
    (DirectSum I (fun i : I => ((F i).presheaf.obj U : Type v)))
  map {U V} f := AddCommGrpCat.ofHom (abelianSheafDirectSumMap F f)
  map_id U := by
    classical
    apply AddCommGrpCat.hom_ext
    apply DirectSum.addHom_ext
    intro i s
    simp [abelianSheafDirectSumMap]
  map_comp f g := by
    classical
    apply AddCommGrpCat.hom_ext
    apply DirectSum.addHom_ext
    intro i s
    simp [abelianSheafDirectSumMap]

/-- A chosen direct sum of a family of abelian sheaves.  The colimit field is
the universal property used by the quotient exercise; its canonical
sheafification presentation is recorded in `Statements.lean`. -/
structure AbelianSheafDirectSum {X : TopCat.{v}} {I : Type v}
    (F : I → AbelianSheaves X) where
  carrier : AbelianSheaves X
  injection : ∀ i : I, F i ⟶ carrier
  isColimit : IsColimit (Cofan.mk carrier injection)

/-- Existence of the direct-sum sheaf, supplied by the sheafification of the
sectionwise presheaf direct sum. -/
theorem exists_directSumSheafOfAbelianSheaves
    {X : TopCat.{v}} {I : Type v} (F : I → AbelianSheaves X) :
    Nonempty (AbelianSheafDirectSum F) := by
  sorry

/-- The chosen direct-sum data for a family of abelian sheaves. -/
noncomputable def directSumSheafData
    {X : TopCat.{v}} {I : Type v} (F : I → AbelianSheaves X) :
    AbelianSheafDirectSum F :=
  Classical.choice (exists_directSumSheafOfAbelianSheaves F)

/-- The sheaf underlying the chosen direct-sum data. -/
noncomputable abbrev directSumSheafOfAbelianSheaves {X : TopCat.{v}} {I : Type v}
    (F : I → AbelianSheaves X) : AbelianSheaves X :=
  (directSumSheafData F).carrier

/-- The injections into the chosen direct-sum sheaf. -/
noncomputable abbrev directSumSheafInjection
    {X : TopCat.{v}} {I : Type v} (F : I → AbelianSheaves X) (i : I) :
    F i ⟶ directSumSheafOfAbelianSheaves F :=
  (directSumSheafData F).injection i

/-- The colimit universal property of the chosen direct-sum sheaf. -/
noncomputable def directSumSheaf_isColimit
    {X : TopCat.{v}} {I : Type v} (F : I → AbelianSheaves X) :
    IsColimit (Cofan.mk (directSumSheafOfAbelianSheaves F)
      (directSumSheafInjection F)) :=
  (directSumSheafData F).isColimit

/-- The chosen direct-sum sheaf is the sheaf associated to the sectionwise
direct-sum presheaf. -/
theorem directSumSheaf_is_associated_to_presheaf
    {X : TopCat.{v}} {I : Type v} (F : I → AbelianSheaves X) :
    Nonempty (directSumSheafOfAbelianSheaves F ≅
      (CategoryTheory.presheafToSheaf
        (Opens.grothendieckTopology X) AddCommGrpCat).obj
        (abelianSheafDirectSumPresheaf F)) := by
  sorry

/-- The index of all integral extension-by-zero maps into an abelian sheaf. -/
abbrev integerGeneratorIndex {X : TopCat.{v}} (F : AbelianSheaves X) :=
  Σ U : Opens X, integerExtensionByZero U ⟶ F

/-- The direct sum of all integral extension-by-zero generators of `F`. -/
noncomputable def integerGeneratorDirectSum {X : TopCat.{v}}
    (F : AbelianSheaves X) : AbelianSheaves X :=
  directSumSheafOfAbelianSheaves
    (fun i : integerGeneratorIndex F => integerExtensionByZero i.1)

/-- The canonical map from the generator direct sum to `F`. -/
noncomputable def integerGeneratorMap {X : TopCat.{v}}
    (F : AbelianSheaves X) : integerGeneratorDirectSum F ⟶ F :=
  Cofan.IsColimit.desc (directSumSheaf_isColimit
    (fun i : integerGeneratorIndex F => integerExtensionByZero i.1))
    (fun i => i.2)

/-! ## Algebraic structure type bridge -/

/-- The standard earlier-chapter algebraic-structure theorem specialized to
abelian groups. -/
noncomputable instance addCommGrpAlgebraicStructureType :
    AlgebraicStructureType (AddCommGrpCat.{v}) (forget AddCommGrpCat) := by
  let : (forget AddCommGrpCat).Faithful := by infer_instance
  let : HasLimitsOfSize.{v, v} (AddCommGrpCat.{v}) := by infer_instance
  let : PreservesLimitsOfSize.{v, v} (forget AddCommGrpCat) := by infer_instance
  let : HasFilteredColimitsOfSize.{v, v} (AddCommGrpCat.{v}) := by infer_instance
  let : PreservesFilteredColimitsOfSize.{v, v} (forget AddCommGrpCat) := by infer_instance
  let : (forget AddCommGrpCat).ReflectsIsomorphisms := by infer_instance
  exact ⟨⟩

/-! ## Pointwise products -/

/-- The pointwise product presheaf of a family of abelian groups. -/
noncomputable def productOverPointsPresheaf {X : TopCat.{v}}
    (A : X → AddCommGrpCat) : TopCat.Presheaf AddCommGrpCat X :=
  Formalization.Books.Sheaves.Unit15.pointwiseProductPresheaf
    (F := forget AddCommGrpCat) A

/-- The pointwise product sheaf of abelian groups. -/
noncomputable def productOverPointsSheaf {X : TopCat.{v}}
  (A : X → AddCommGrpCat) : AbelianSheaves X :=
  ⟨productOverPointsPresheaf A, by
    change TopCat.Presheaf.IsSheaf
      (Formalization.Books.Sheaves.Unit15.pointwiseProductPresheaf
        (F := forget AddCommGrpCat) A)
    exact (Formalization.Books.Sheaves.Unit09.categoryValuedSheaf_iff_isSheaf
      (F := Formalization.Books.Sheaves.Unit15.pointwiseProductPresheaf
        (F := forget AddCommGrpCat) A)).1
      (Formalization.Books.Sheaves.Unit15.pointwiseProductPresheaf_isSheaf
        (F := forget AddCommGrpCat) A)⟩

/-- The constant `ZMod 2` family used to exhibit a nontrivial product stalk. -/
def realBooleanAbelianFamily : realLine → AddCommGrpCat :=
  fun _ => AddCommGrpCat.of (ZMod 2)

/-- The corresponding pointwise product sheaf on the real line. -/
noncomputable def realBooleanProductSheaf : AbelianSheaves realLine :=
  productOverPointsSheaf realBooleanAbelianFamily

/-! ## Basis-local modified products -/

/-- Basis subgroups used in the modified product construction. -/
structure ModifiedProductData {X : TopCat.{v}}
    (A : X → AddCommGrpCat) where
  basis : Set (Opens X)
  isBasis : Opens.IsBasis basis
  subgroup : ∀ U : Opens X, U ∈ basis →
    AddSubgroup (∀ x : U, A x)
  restriction_mem : ∀ {U V : Opens X} (hU : U ∈ basis) (hV : V ∈ basis)
    (h : U ≤ V) (s : ∀ x : V, A x),
    s ∈ subgroup V hV →
      (fun x : U => s ⟨x, h x.2⟩) ∈ subgroup U hU

/-!
The local predicate is kept as a separate interface because the source gives
the basis-subgroup data abstractly.  Its `pred` field is exactly the displayed
local section condition; the restriction field is the basis-refinement step.
-/
def modifiedProductLocalPredicate {X : TopCat.{v}}
    {A : X → AddCommGrpCat} (D : ModifiedProductData A) :
    TopCat.LocalPredicate (fun x : X => A x) := by
  classical
  let P : TopCat.PrelocalPredicate (fun x : X => A x) := {
    pred := fun {U} s =>
      ∀ x : U, ∃ (V : Opens X) (hV : V ∈ D.basis)
        (hxV : x.1 ∈ V) (hVU : V ≤ U),
        (fun y : V => s ⟨y, hVU y.2⟩) ∈ D.subgroup V hV
    res := by
      intro U V i s hs x
      rcases hs (i x) with ⟨W, hW, hxW, hWV, hsW⟩
      have hxWU : x.1 ∈ W ⊓ U := ⟨by simpa using hxW, x.2⟩
      rcases (Opens.isBasis_iff_nbhd.mp D.isBasis hxWU) with
        ⟨W', hW', hxW', hW'WU⟩
      refine ⟨W', hW', hxW', hW'WU.trans inf_le_right, ?_⟩
      have hW'W : W' ≤ W := hW'WU.trans inf_le_left
      have hmem := D.restriction_mem hW' hW hW'W
        (fun y : W => s ⟨y, hWV y.2⟩) hsW
      convert hmem using 1
      funext y
      rfl }
  exact P.sheafify

/-- The set-valued sheaf of sections satisfying the modified-product local
condition. -/
noncomputable def modifiedProductSetSheaf
    {X : TopCat.{v}} {A : X → AddCommGrpCat}
    (D : ModifiedProductData A) : SetSheaves X :=
  TopCat.subsheafToTypes (modifiedProductLocalPredicate D)

/-! ## Exact functors which are not stalks -/

/-! The site-level sheaf category has the finite-colimit instance needed to
state exactness of the constant functor on the empty space. -/

noncomputable instance topCatSheaf_hasFiniteColimits
    {C : Type u} [Category.{v} C] [HasFiniteColimits C]
    (X : TopCat.{w})
    [HasWeakSheafify (Opens.grothendieckTopology X) C] :
    HasFiniteColimits (TopCat.Sheaf C X) := by
  change HasFiniteColimits (CategoryTheory.Sheaf
    (Opens.grothendieckTopology X) C)
  infer_instance

/-- A functor on sheaves of sets is a stalk functor up to natural isomorphism. -/
def IsStalkFunctor {X : TopCat.{v}}
    (F : SetSheaves X ⥤ Type v) : Prop :=
  ∃ x : X, Nonempty
    (F ≅ TopCat.Sheaf.forget (Type v) X ⋙
      TopCat.Presheaf.stalkFunctor (Type v) x)

/-- The empty topological space. -/
abbrev emptySpace : TopCat := TopCat.of Empty

/-- The constant `PUnit` functor on sheaves over the empty space. -/
noncomputable def emptySpaceFunctor :
    SetSheaves emptySpace ⥤ Type 0 :=
  (Functor.const _).obj (PUnit : Type 0)

end

end Formalization.Books.Exercises.Unit32
