import Formalization.Books.Categories.Unit23.ExactFunctors
import Formalization.Books.Sheaves.Unit07.Sheaves
import Formalization.Books.Sheaves.Unit08.AbelianSheaves
import Formalization.Books.Sheaves.Unit11.Stalks
import Formalization.Books.Sheaves.Unit15.AlgebraicStructures
import Formalization.Books.Sheaves.Unit16.ExactnessAndPoints
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Category.Grp.Zero
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Topology.Sheaves.AddCommGrpCat
import Mathlib.Topology.Sheaves.Limits
import Mathlib.Topology.Sheaves.Functors
import Mathlib.Topology.Sheaves.SheafCondition.Sites
import Mathlib.Topology.Sheaves.Skyscraper
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

universe u v w

noncomputable section

/-! ## Open subspaces and extension by an initial object

The open-immersion chapter has a transitive dependency on a currently
unfinished module-presheaf file.  The constructions below are the same
sectionwise initial-object construction, expressed directly with the stable
topological-sheaf API needed by this chapter. -/

abbrev openSubspace {X : TopCat.{v}} (U : Opens X) : TopCat.{v} :=
  (Opens.toTopCat X).obj U

abbrev openInclusion {X : TopCat.{v}} (U : Opens X) : openSubspace U ⟶ X :=
  Opens.inclusion' U

noncomputable abbrev openPresheafRestriction (C : Type u) [Category.{v} C]
    [HasColimits C] {X : TopCat.{v}} (U : Opens X) :
    TopCat.Presheaf C X ⥤ TopCat.Presheaf C (openSubspace U) :=
  TopCat.Presheaf.pullback C (openInclusion U)

abbrev openSheafRestriction (C : Type u) [Category.{v} C]
    {X : TopCat.{v}} (U : Opens X) :
    TopCat.Sheaf C X ⥤ TopCat.Sheaf C (openSubspace U) :=
  TopologicalSpace.Opens.sheafRestrict U

noncomputable def openPresheafExtensionByInitial (C : Type u)
    [Category.{v} C] [HasInitial C] {X : TopCat.{v}} (U : Opens X) :
    TopCat.Presheaf C (openSubspace U) ⥤ TopCat.Presheaf C X := by
  classical
  let j := Opens.map (openInclusion U)
  exact {
    obj := fun F => {
      obj := fun V => if V.unop ≤ U then F.obj (j.op.obj V) else ⊥_ C
      map := by
        intro V W i
        by_cases hV : V.unop ≤ U
        · have hW : W.unop ≤ U := by
            exact (show W.unop ≤ V.unop from leOfHom i.unop).trans hV
          exact eqToHom (by simp [hV]) ≫ F.map (j.op.map i) ≫
            eqToHom (by simp [hW])
        · exact eqToHom (by simp [hV]) ≫ initial.to _
      map_id := by
        intro V
        by_cases hV : V.unop ≤ U
        · simp [hV]
        · simp only [if_neg hV]
          apply (initialIsInitial : IsInitial (⊥_ C)).hom_ext
      map_comp := by
        intro V W T i k
        by_cases hV : V.unop ≤ U
        · have hW : W.unop ≤ U := by
            exact (show W.unop ≤ V.unop from leOfHom i.unop).trans hV
          have hT : T.unop ≤ U := by
            exact (show T.unop ≤ W.unop from leOfHom k.unop).trans hW
          simp [hV, hW, hT, Functor.map_comp]
        · simp [hV]
    }
    map := fun {F G} φ => {
      app := fun V => if hV : V.unop ≤ U then
          eqToHom (by simp [hV]) ≫ φ.app (j.op.obj V) ≫
            eqToHom (by simp [hV])
        else eqToHom (by simp [hV]) ≫ initial.to _
      naturality := by
        intro V W i
        by_cases hV : V.unop ≤ U
        · have hW : W.unop ≤ U := by
            exact (show W.unop ≤ V.unop from leOfHom i.unop).trans hV
          simp [hV, hW]
        · simp [hV]
      }
    map_id := by
      intro F
      ext V
      dsimp
      split_ifs with hV
      · simp
      · apply (initialIsInitial : IsInitial (⊥_ C)).hom_ext
    map_comp := by
      intro F G H φ ψ
      ext V
      dsimp
      split_ifs with hV
      · simp
      · apply (initialIsInitial : IsInitial (⊥_ C)).hom_ext
  }

noncomputable def openSheafExtensionByInitial (C : Type u)
    [Category.{v} C] [HasInitial C] {X : TopCat.{v}} (U : Opens X)
    [HasWeakSheafify (Opens.grothendieckTopology X) C] :
    TopCat.Sheaf C (openSubspace U) ⥤ TopCat.Sheaf C X :=
  TopCat.Sheaf.forget C (openSubspace U) ⋙
    openPresheafExtensionByInitial C U ⋙
    CategoryTheory.presheafToSheaf (Opens.grothendieckTopology X) C

noncomputable abbrev openSetSheafExtensionByEmpty
    {X : TopCat.{v}} (U : Opens X)
    [HasWeakSheafify (Opens.grothendieckTopology X) (Type v)] :
    Sh.{v, v} (openSubspace U) ⥤ Sh.{v, v} X :=
  openSheafExtensionByInitial (Type v) U

noncomputable abbrev openAbelianSheafExtensionByZero
    {X : TopCat.{v}} (U : Opens X)
    [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat] :
    Formalization.Books.Sheaves.Unit08.Ab.{v, v} (openSubspace U) ⥤
      Formalization.Books.Sheaves.Unit08.Ab.{v, v} X :=
  openSheafExtensionByInitial AddCommGrpCat U

noncomputable def openSheafExtensionAdjunction (C : Type u)
    [Category.{v} C] [HasInitial C] {X : TopCat.{v}} (U : Opens X)
    [HasWeakSheafify (Opens.grothendieckTopology X) C] :
    openSheafExtensionByInitial C U ⊣ openSheafRestriction C U := by
  sorry

noncomputable abbrev openAbelianSheafExtensionAdjunction
    {X : TopCat.{v}} (U : Opens X)
    [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat] :
    openAbelianSheafExtensionByZero U ⊣
      openSheafRestriction AddCommGrpCat U :=
  openSheafExtensionAdjunction AddCommGrpCat U

/-! ## Pushforward, pullback, and open immersions -/

/-- Pushforward of sheaves of sets along a continuous map. -/
noncomputable abbrev sheafPushforward {X Y : TopCat.{v}} (f : X ⟶ Y) :
    Sh.{v, v} X ⥤ Sh.{v, v} Y :=
  TopCat.Sheaf.pushforward (Type v) f

/-- Pullback of sheaves of sets along a continuous map. -/
noncomputable abbrev sheafPullback {X Y : TopCat.{v}} (f : X ⟶ Y) :
    Sh.{v, v} Y ⥤ Sh.{v, v} X :=
  TopCat.Sheaf.pullback (Type v) f

/-- The pullback/pushforward adjunction for sheaves of sets. -/
noncomputable def sheafPullbackPushforwardAdjunction
    {X Y : TopCat.{v}} (f : X ⟶ Y) :
    sheafPullback f ⊣ sheafPushforward f :=
  TopCat.Sheaf.pullbackPushforwardAdjunction (Type v) f

/-- The extension-by-empty functor for sheaves of sets on an open subspace. -/
noncomputable abbrev extensionByEmpty {X : TopCat.{v}} (U : Opens X) :
    Sh.{v, v} (openSubspace U) ⥤ Sh.{v, v} X :=
  openSetSheafExtensionByEmpty U

/-- Restriction of sheaves of sets to an open subspace. -/
noncomputable abbrev restrictionToOpen {X : TopCat.{v}} (U : Opens X) :
    Sh.{v, v} X ⥤ Sh.{v, v} (openSubspace U) :=
  openSheafRestriction (Type v) U

/-- The extension-by-empty/restriction adjunction. -/
noncomputable def extensionByEmptyAdjunction {X : TopCat.{v}} (U : Opens X) :
    extensionByEmpty U ⊣ restrictionToOpen U :=
  openSheafExtensionAdjunction (Type v) U

/-- The extension-by-zero functor for abelian sheaves on an open subspace. -/
noncomputable abbrev extensionByZero {X : TopCat.{v}} (U : Opens X) :
    Formalization.Books.Sheaves.Unit08.Ab.{v, v} (openSubspace U) ⥤
      Formalization.Books.Sheaves.Unit08.Ab.{v, v} X :=
  openAbelianSheafExtensionByZero U

/-- Restriction of abelian sheaves to an open subspace. -/
noncomputable abbrev abelianRestrictionToOpen {X : TopCat.{v}} (U : Opens X) :
    Formalization.Books.Sheaves.Unit08.Ab.{v, v} X ⥤
      Formalization.Books.Sheaves.Unit08.Ab.{v, v} (openSubspace U) :=
  openSheafRestriction AddCommGrpCat U

/-- The extension-by-zero/restriction adjunction. -/
noncomputable def extensionByZeroAdjunction {X : TopCat.{v}} (U : Opens X) :
    extensionByZero U ⊣ abelianRestrictionToOpen U :=
  openAbelianSheafExtensionAdjunction U

/-! ## Integral generators and local generation -/

noncomputable def integralConstantSheaf {X : TopCat.{v}} :
    Formalization.Books.Sheaves.Unit08.Ab.{v, v} X :=
  (CategoryTheory.constantSheaf (Opens.grothendieckTopology X)
      AddCommGrpCat).obj (AddCommGrpCat.of (ULift.{v} ℤ))

noncomputable def integralDirectSum {X : TopCat.{v}} (I : Type v) :
    Formalization.Books.Sheaves.Unit08.Ab.{v, v} X :=
  letI : HasColimitsOfShape (Discrete I)
      (TopCat.Sheaf AddCommGrpCat.{v} X) :=
    CategoryTheory.Sheaf.instHasColimitsOfShape
      (J := Opens.grothendieckTopology X) (D := AddCommGrpCat.{v}) (K := Discrete I)
  ∐ fun _ : I => integralConstantSheaf (X := X)

noncomputable def additiveGlobalGenerationMap
    {X : TopCat.{v}}
    {F : Formalization.Books.Sheaves.Unit08.Ab.{v, v} X}
    {I : Type v}
    (s : I → (integralConstantSheaf (X := X) ⟶ F)) :
    integralDirectSum I ⟶ F :=
  letI : HasColimitsOfShape (Discrete I)
      (TopCat.Sheaf AddCommGrpCat.{v} X) :=
    CategoryTheory.Sheaf.instHasColimitsOfShape
      (J := Opens.grothendieckTopology X) (D := AddCommGrpCat.{v}) (K := Discrete I)
  Cofan.IsColimit.desc (coproductIsCoproduct _) s

def additiveGloballyGenerated {X : TopCat.{v}}
    (F : Formalization.Books.Sheaves.Unit08.Ab.{v, v} X) : Prop :=
  ∃ (I : Type v) (s : I → (integralConstantSheaf (X := X) ⟶ F)),
    Epi (additiveGlobalGenerationMap s)

def additiveLocallyGenerated {X : TopCat.{v}}
    (F : Formalization.Books.Sheaves.Unit08.Ab.{v, v} X) : Prop :=
  ∀ x : X, ∃ U : Opens X, x ∈ U ∧
    additiveGloballyGenerated ((openSheafRestriction AddCommGrpCat U).obj F)

/-- The integral constant sheaf used in the generation exercise. -/
noncomputable abbrev integerConstantSheaf {X : TopCat.{v}} :
    Formalization.Books.Sheaves.Unit08.Ab.{v, v} X :=
  integralConstantSheaf (X := X)

/-- Extension by zero of the integral constant sheaf on an open. -/
noncomputable def integerExtensionByZero {X : TopCat.{v}} (U : Opens X) :
    Formalization.Books.Sheaves.Unit08.Ab.{v, v} X :=
  (extensionByZero U).obj
    (integerConstantSheaf (X := openSubspace U))

/-! ## The real-line skyscraper example -/

def IsSetSkyscraperSheaf {X : TopCat.{v}} (F : Sh.{v, v} X) : Prop :=
  by
    classical
    exact ∃ x : X, ∃ A : Type v, Nonempty (F ≅ skyscraperSheaf x A)

/-- The real line as a topological category. -/
abbrev realLine : TopCat := TopCat.of ℝ

/-- The origin of the real line. -/
abbrev realOrigin : realLine := (0 : ℝ)

/-- The constant sheaf with value `ZMod 2` on the real line. -/
def realConstantZModTwo : Sh.{0, 0} realLine :=
  Formalization.Books.Sheaves.Unit07.constantSheaf realLine (ZMod 2)

/-! The same constant object with its commutative-ring structure. -/

/-- The constant `ZMod 2` sheaf of commutative rings on the real line. -/
noncomputable def realRingConstantZModTwo : TopCat.Sheaf CommRingCat realLine :=
  (CategoryTheory.constantSheaf
    (Opens.grothendieckTopology realLine) CommRingCat).obj
      (CommRingCat.of (ZMod 2))

/-- The skyscraper sheaf at the origin with value `ZMod 2`. -/
noncomputable def realOriginSkyscraper : Sh.{0, 0} realLine :=
  by classical exact skyscraperSheaf realOrigin (ZMod 2)

/-! The source writes this skyscraper as the direct image from the closed
singleton `{0}`.  We keep the concrete direct-image presentation alongside
Mathlib's canonical skyscraper presentation. -/

/-- The singleton subspace `{0} ⊂ ℝ` used in the textbook's direct image. -/
abbrev realOriginSubspace : TopCat := TopCat.of {x : ℝ // x = 0}

/-- The inclusion of the singleton origin subspace into the real line. -/
noncomputable def realOriginSubspaceInclusion :
    realOriginSubspace ⟶ realLine :=
  TopCat.ofHom
    { toFun := fun x : {x : ℝ // x = 0} => (x : ℝ)
      continuous_toFun := continuous_subtype_val }

/-- The constant `ZMod 2` sheaf on the singleton origin subspace. -/
def realOriginSubspaceConstantZModTwo : Sh.{0, 0} realOriginSubspace :=
  Formalization.Books.Sheaves.Unit07.constantSheaf realOriginSubspace (ZMod 2)

/-- The direct image `i_* O_Z` from the singleton origin subspace. -/
noncomputable def realOriginDirectImage : Sh.{0, 0} realLine :=
  (sheafPushforward realOriginSubspaceInclusion).obj
    realOriginSubspaceConstantZModTwo

/-- The stalk map from the constant sheaf to its value at the origin. -/
noncomputable def realConstantZModTwoStalkMap :
    realConstantZModTwo.presheaf.stalk realOrigin → ZMod 2 :=
  (Formalization.Books.Sheaves.Unit11.constantSheafStalkEquiv
    (X := realLine) (ZMod 2) realOrigin).symm

/-- The canonical map from the constant sheaf to the origin skyscraper. -/
noncomputable def realConstantToOriginSkyscraper :
    realConstantZModTwo ⟶ realOriginSkyscraper :=
  by
    classical
    exact (stalkSkyscraperSheafAdjunction realOrigin).homEquiv
      realConstantZModTwo (ZMod 2) (TypeCat.ofHom realConstantZModTwoStalkMap)

/-- The zero map with the same source and target as the canonical map. -/
noncomputable def realConstantToOriginSkyscraperZero :
    realConstantZModTwo ⟶ realOriginSkyscraper :=
  by
    classical
    exact (stalkSkyscraperSheafAdjunction realOrigin).homEquiv
      realConstantZModTwo (ZMod 2) (TypeCat.ofHom (fun _ => 0))

/-- The kernel subsheaf of the canonical constant-to-skyscraper map. -/
noncomputable def realKernelSheaf : Sh.{0, 0} realLine :=
  limit (parallelPair realConstantToOriginSkyscraper
    realConstantToOriginSkyscraperZero)

/-- The inclusion of the kernel subsheaf in the constant sheaf. -/
noncomputable def realKernelInclusion :
    realKernelSheaf ⟶ realConstantZModTwo :=
  limit.π (parallelPair realConstantToOriginSkyscraper
    realConstantToOriginSkyscraperZero) WalkingParallelPair.zero

/-- The additive constant sheaf with value `ZMod 2`. -/
noncomputable def realAbelianConstantZModTwo :
    Formalization.Books.Sheaves.Unit08.Ab.{0, 0} realLine :=
  (CategoryTheory.constantSheaf
    (Opens.grothendieckTopology realLine) AddCommGrpCat).obj
      (AddCommGrpCat.of (ZMod 2))

/-- The additive skyscraper sheaf at the origin with value `ZMod 2`. -/
noncomputable def realAbelianOriginSkyscraper :
    Formalization.Books.Sheaves.Unit08.Ab.{0, 0} realLine :=
  by classical exact skyscraperSheaf realOrigin (AddCommGrpCat.of (ZMod 2))

/-- The sections on the top open of the origin skyscraper are its value. -/
noncomputable def realOriginSkyscraperTopSectionsIso :
    realAbelianOriginSkyscraper.presheaf.obj (op (⊤ : Opens realLine)) ≅
      AddCommGrpCat.of (ZMod 2) := by
  classical
  dsimp [realAbelianOriginSkyscraper]
  change (if realOrigin ∈ (⊤ : Opens realLine) then AddCommGrpCat.of (ZMod 2)
  else terminal AddCommGrpCat) ≅ AddCommGrpCat.of (ZMod 2)
  have h : realOrigin ∈ (⊤ : Opens realLine) := by simp
  rw [if_pos h]

/-- The canonical additive constant-to-skyscraper map, obtained from the
constant-sheaf adjunction and the top-open section of the skyscraper. -/
noncomputable def realAbelianConstantToOriginSkyscraper :
  realAbelianConstantZModTwo ⟶ realAbelianOriginSkyscraper :=
  letI : ∀ U : Opens realLine, Decidable (realOrigin ∈ U) := fun _ => Classical.dec _
  let hTop : IsTerminal (⊤ : Opens realLine) :=
    isTerminalTop
  ((CategoryTheory.constantSheafAdj
      (Opens.grothendieckTopology realLine) AddCommGrpCat
      (T := (⊤ : Opens realLine)) hTop).homEquiv
    (AddCommGrpCat.of (ZMod 2)) realAbelianOriginSkyscraper).symm
      (realOriginSkyscraperTopSectionsIso.inv ≫
        (CategoryTheory.sheafSectionsNatIsoEvaluation
          (Opens.grothendieckTopology realLine) AddCommGrpCat
          (X := (⊤ : Opens realLine))).inv.app realAbelianOriginSkyscraper)

/-- The zero map from the additive constant sheaf to the additive skyscraper. -/
noncomputable def realAbelianConstantToOriginSkyscraperZero :
    realAbelianConstantZModTwo ⟶ realAbelianOriginSkyscraper :=
  0

/-- The additive kernel sheaf in the real-line example. -/
noncomputable def realIdealSheaf :
    Formalization.Books.Sheaves.Unit08.Ab.{0, 0} realLine :=
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
def commRingToAddCommGrp : CommRingCat.{v} ⥤ AddCommGrpCat.{v} where
  obj R := AddCommGrpCat.of (R : Type v)
  map f := AddCommGrpCat.ofHom f.hom.toAddMonoidHom
  map_id R := by rfl
  map_comp f g := by rfl

/-- A sheaf of abelian groups is an ideal sheaf in a specified sheaf of
commutative rings when its presheaf inclusion has ideal image on every open. -/
def IsIdealSheafIn {X : TopCat.{v}} (O : TopCat.Sheaf CommRingCat X)
    (I : Formalization.Books.Sheaves.Unit08.Ab.{v, v} X) : Prop :=
  ∃ ι : I.presheaf ⟶ O.presheaf ⋙ commRingToAddCommGrp,
    Mono ι ∧ ∀ U : Opens X,
      ∃ J : Ideal (O.presheaf.obj (op U)),
        Set.range (ι.app (op U)) = (J : Set (O.presheaf.obj (op U)))

/-! ## Direct sums and the quotient exercise -/

/-- The restriction map on the sectionwise direct sum of a family of abelian
sheaves. -/
noncomputable def abelianSheafDirectSumMap
    {X : TopCat.{v}} {I : Type v}
    (F : I → Formalization.Books.Sheaves.Unit08.Ab.{v, v} X)
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
    {X : TopCat.{v}} {I : Type v}
    (F : I → Formalization.Books.Sheaves.Unit08.Ab.{v, v} X) :
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

/-! The coproduct in the category of abelian sheaves is the direct sum of a
family of abelian sheaves. -/
noncomputable def directSumSheafOfAbelianSheaves {X : TopCat.{v}} {I : Type v}
    (F : I → Formalization.Books.Sheaves.Unit08.Ab.{v, v} X) :
    Formalization.Books.Sheaves.Unit08.Ab.{v, v} X :=
  letI : HasColimitsOfShape (Discrete I) (TopCat.Sheaf AddCommGrpCat.{v} X) :=
    CategoryTheory.Sheaf.instHasColimitsOfShape
      (J := Opens.grothendieckTopology X) (D := AddCommGrpCat.{v}) (K := Discrete I)
  ∐ F

/-- The injections into the direct-sum sheaf. -/
noncomputable def directSumSheafInjection
    {X : TopCat.{v}} {I : Type v}
    (F : I → Formalization.Books.Sheaves.Unit08.Ab.{v, v} X) (i : I) :
    F i ⟶ directSumSheafOfAbelianSheaves F :=
  letI : HasColimitsOfShape (Discrete I) (TopCat.Sheaf AddCommGrpCat.{v} X) :=
    CategoryTheory.Sheaf.instHasColimitsOfShape
      (J := Opens.grothendieckTopology X) (D := AddCommGrpCat.{v}) (K := Discrete I)
  Sigma.ι F i

/-- The colimit universal property of the direct-sum sheaf. -/
noncomputable def directSumSheaf_isColimit
    {X : TopCat.{v}} {I : Type v}
    (F : I → Formalization.Books.Sheaves.Unit08.Ab.{v, v} X) :
    IsColimit (Cofan.mk (directSumSheafOfAbelianSheaves F)
      (directSumSheafInjection F)) :=
  letI : HasColimitsOfShape (Discrete I) (TopCat.Sheaf AddCommGrpCat.{v} X) :=
    CategoryTheory.Sheaf.instHasColimitsOfShape
      (J := Opens.grothendieckTopology X) (D := AddCommGrpCat.{v}) (K := Discrete I)
  coproductIsCoproduct F

/-- The direct-sum sheaf is the sheaf associated to the sectionwise
direct-sum presheaf. -/
theorem directSumSheaf_is_associated_to_presheaf
    {X : TopCat.{v}} {I : Type v}
    (F : I → Formalization.Books.Sheaves.Unit08.Ab.{v, v} X) :
    Nonempty (directSumSheafOfAbelianSheaves F ≅
      (CategoryTheory.presheafToSheaf
        (Opens.grothendieckTopology X) AddCommGrpCat).obj
        (abelianSheafDirectSumPresheaf F)) := by
  sorry

/-- The index of all integral extension-by-zero maps into an abelian sheaf. -/
abbrev integerGeneratorIndex {X : TopCat.{v}}
    (F : Formalization.Books.Sheaves.Unit08.Ab.{v, v} X) :=
  Σ U : Opens X, integerExtensionByZero U ⟶ F

/-- The direct sum of all integral extension-by-zero generators of `F`. -/
noncomputable def integerGeneratorDirectSum {X : TopCat.{v}}
    (F : Formalization.Books.Sheaves.Unit08.Ab.{v, v} X) :
    Formalization.Books.Sheaves.Unit08.Ab.{v, v} X :=
  directSumSheafOfAbelianSheaves
    (fun i : integerGeneratorIndex F => integerExtensionByZero i.1)

/-- The canonical map from the generator direct sum to `F`. -/
noncomputable def integerGeneratorMap {X : TopCat.{v}}
    (F : Formalization.Books.Sheaves.Unit08.Ab.{v, v} X) :
    integerGeneratorDirectSum F ⟶ F :=
  Cofan.IsColimit.desc (directSumSheaf_isColimit
    (fun i : integerGeneratorIndex F => integerExtensionByZero i.1))
    (fun i => i.2)

/-! ## Algebraic structure type bridge -/

/-- The standard earlier-chapter algebraic-structure theorem specialized to
abelian groups. -/
noncomputable instance addCommGrpAlgebraicStructureType :
    AlgebraicStructureType (AddCommGrpCat.{v}) (forget AddCommGrpCat) := by
  exact
    (Formalization.Books.Sheaves.Unit15.standardAlgebraicStructureTypes.{v, v, v}).2.1

/-! ## Pointwise products -/

/-- The pointwise product presheaf of a family of abelian groups. -/
noncomputable def productOverPointsPresheaf {X : TopCat.{v}}
    (A : X → AddCommGrpCat) : TopCat.Presheaf AddCommGrpCat X :=
  Formalization.Books.Sheaves.Unit15.pointwiseProductPresheaf
    (F := forget AddCommGrpCat) A

/-- The pointwise product sheaf of abelian groups. -/
noncomputable def productOverPointsSheaf {X : TopCat.{v}}
  (A : X → AddCommGrpCat) :
    Formalization.Books.Sheaves.Unit08.Ab.{v, v} X :=
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
noncomputable def realBooleanProductSheaf :
    Formalization.Books.Sheaves.Unit08.Ab.{0, 0} realLine :=
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
def modifiedProductPrelocalPredicate {X : TopCat.{v}}
    {A : X → AddCommGrpCat} (D : ModifiedProductData A) :
    TopCat.PrelocalPredicate (fun x : X => A x) := by
  classical
  exact {
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

def modifiedProductLocalPredicate {X : TopCat.{v}}
    {A : X → AddCommGrpCat} (D : ModifiedProductData A) :
    TopCat.LocalPredicate (fun x : X => A x) :=
  (modifiedProductPrelocalPredicate D).sheafify

/-!
The sheafified predicate is closed under the pointwise additive operations.
These closure facts let the source's modified product be represented by the
canonical category-valued sheaf rather than by a parallel set-only object.
-/

noncomputable def modifiedProductSectionSubgroup {X : TopCat.{v}}
    {A : X → AddCommGrpCat} (D : ModifiedProductData A) (U : Opens X) :
    AddSubgroup (∀ x : U, A x) where
  carrier := fun s => (modifiedProductPrelocalPredicate D).sheafify.pred s
  zero_mem' := by
    apply (modifiedProductPrelocalPredicate D).sheafifyOf
    intro x
    rcases (Opens.isBasis_iff_nbhd.mp D.isBasis x.2) with
      ⟨V, hV, hxV, hVU⟩
    refine ⟨V, hV, hxV, hVU, ?_⟩
    have hz : (0 : ∀ y : V, A y) ∈ D.subgroup V hV :=
      (D.subgroup V hV).zero_mem
    convert hz using 1
    funext y
    rfl
  add_mem' := by
    intro s t hs ht
    exact (modifiedProductPrelocalPredicate D).sheafify_inductionOn₂'
      (modifiedProductPrelocalPredicate D)
      (modifiedProductPrelocalPredicate D)
      (fun {x} a b => a + b)
      (fun {U V : Opens X} {a : ∀ x : U, A x} {b : ∀ x : V, A x} hs ht => by
        intro x
        rcases hs ⟨x.1, x.2.1⟩ with
          ⟨W, hW, hxW, hWU, hsW⟩
        rcases ht ⟨x.1, x.2.2⟩ with
          ⟨Z, hZ, hxZ, hZV, htZ⟩
        have hxWZ : x.1 ∈ W ⊓ Z := ⟨hxW, hxZ⟩
        rcases (Opens.isBasis_iff_nbhd.mp D.isBasis hxWZ) with
          ⟨K, hK, hxK, hKWZ⟩
        have hKW : K ≤ W := hKWZ.trans inf_le_left
        have hKZ : K ≤ Z := hKWZ.trans inf_le_right
        have hKU : K ≤ U := hKW.trans hWU
        have hKV : K ≤ V := hKZ.trans hZV
        have hsK := D.restriction_mem hK hW hKW
          (fun y : W => a ⟨y, hWU y.2⟩) hsW
        have htK := D.restriction_mem hK hZ hKZ
          (fun y : Z => b ⟨y, hZV y.2⟩) htZ
        refine ⟨K, hK, hxK, le_inf hKU hKV, ?_⟩
        have hsum := (D.subgroup K hK).add_mem hsK htK
        convert hsum using 1
        funext y
        rfl)
      hs ht
  neg_mem' := by
    intro s hs
    exact (modifiedProductPrelocalPredicate D).sheafify_inductionOn'
      (fun {x} a => -a)
      (fun hs => by
        intro x
        rcases hs x with ⟨V, hV, hxV, hVU, hsV⟩
        refine ⟨V, hV, hxV, hVU, ?_⟩
        have hneg := (D.subgroup V hV).neg_mem hsV
        convert hneg using 1
        funext y
        rfl)
      hs

/-- The additive presheaf of sections satisfying the modified-product local
condition. -/
noncomputable def modifiedProductAbelianPresheaf {X : TopCat.{v}}
    {A : X → AddCommGrpCat} (D : ModifiedProductData A) :
    TopCat.Presheaf AddCommGrpCat X where
  obj U := AddCommGrpCat.of (modifiedProductSectionSubgroup D U.unop)
  map {U V} f := AddCommGrpCat.ofHom {
    toFun := fun s =>
      ⟨fun x => s.1 (f.unop x),
        (modifiedProductPrelocalPredicate D).sheafify.res f.unop s.1 s.2⟩
    map_zero' := by
      ext x
      rfl
    map_add' := by
      intro s t
      ext x
      rfl }
  map_id U := by
    apply AddCommGrpCat.hom_ext
    ext s x
    rfl
  map_comp f g := by
    apply AddCommGrpCat.hom_ext
    ext s x
    rfl

/-- The set-valued sheaf of sections satisfying the modified-product local
condition. -/
noncomputable def modifiedProductSetSheaf
    {X : TopCat.{v}} {A : X → AddCommGrpCat}
    (D : ModifiedProductData A) : Sh.{v, v} X :=
  TopCat.subsheafToTypes (modifiedProductLocalPredicate D)

/-! The same construction with its canonical additive-group structure. -/

/-- The modified product as a sheaf of abelian groups. -/
noncomputable def modifiedProductAbelianSheaf {X : TopCat.{v}}
    {A : X → AddCommGrpCat} (D : ModifiedProductData A) :
    Formalization.Books.Sheaves.Unit08.Ab.{v, v} X :=
  ⟨modifiedProductAbelianPresheaf D, by
    apply (Formalization.Books.Sheaves.Unit09.categoryValuedSheaf_iff_isSheaf
      (modifiedProductAbelianPresheaf D)).1
    refine Formalization.Books.Sheaves.Unit09.categoryValuedSheaf_of_underlying_isSheaf
      (forget AddCommGrpCat) (modifiedProductAbelianPresheaf D) ?_
    change TopCat.Presheaf.IsSheaf (modifiedProductSetSheaf D).presheaf
    exact (modifiedProductSetSheaf D).property⟩

/-! ## Exact functors which are not stalks -/

/-- A functor on sheaves of sets is a stalk functor up to natural isomorphism. -/
def IsStalkFunctor {X : TopCat.{v}}
    (F : Sh.{v, v} X ⥤ Type v) : Prop :=
  ∃ x : X, Nonempty
    (F ≅ TopCat.Sheaf.forget (Type v) X ⋙
      TopCat.Presheaf.stalkFunctor (Type v) x)

end

end Formalization.Books.Exercises.Unit32
