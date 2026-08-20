import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
import Formalization.Books.Derived.Unit10.DistinguishedTriangles
import Formalization.Books.Derived.Unit11.DerivedCategories
import Formalization.Books.Derived.Unit14.Core
import Formalization.Books.Derived.Unit14.DerivedFunctors
import Formalization.Books.Homology.Unit27.Injectives

/-!
# Derived Categories, Chapter 20: injective resolutions

This file records the bounded-below injective-complex computation of right
derived functors, the right-acyclicity of injectives, and the existence
interfaces supplied by enough injectives.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Preadditive
open CategoryTheory.Pretriangulated
open Formalization.Books.Derived.Unit08
open Formalization.Books.Derived.Unit10
open Formalization.Books.Derived.Unit11
open Formalization.Books.Derived.Unit14
open Formalization.Books.Categories.Unit22
open Formalization.Books.Categories.Unit27
open Formalization.Books.Homology.Unit03
open Formalization.Books.Homology.Unit27
open scoped CategoryTheory.Pretriangulated.Opposite ZeroObject

universe v u v' u' w w'

namespace Formalization.Books.Derived.Unit20

/-! ## Injective complexes -/

/-- Every term of a bounded-below complex is injective. -/
def IsTermwiseInjectiveComplex
    {A : Type u} [Category.{v} A] [Abelian A]
    (I : CompPlus A) : Prop :=
  ∀ n : ℤ, Injective (I.obj.X n)

/-- A bounded-below complex computes the right derived functor of a functor on
the homotopy category. -/
def ComputesRightDerivedComplex
    {A : Type u} [Category.{v} A] [Abelian A]
    {D : Type u'} [Category.{v'} D] [AdditiveCategory D]
    (F : KPlus A ⥤ D) (I : CompPlus A) : Prop :=
  ComputesRightDerived (quasiIsoPlusProperty A)
    (boundedQuasiIsoProperty_properties A).1 F
    ((HomotopyCategory.Plus.quotient A).obj I)

/- The functor on `K⁺(A)` obtained by applying an additive functor termwise and
then passing to the bounded-below derived category of its target. -/
noncomputable def rightDerivedSourceFunctor
    {A : Type u} [Category.{v} A] [Abelian A]
    {B : Type u'} [Category.{v'} B] [Abelian B]
    [HasDerivedCategory.{w} B]
    (F : A ⥤ B) [F.Additive] :
    KPlus A ⥤ DPlus B :=
  F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh

/- An object is right acyclic for an additive functor when its stalk complex
computes the associated right derived functor. -/
noncomputable def RightAcyclic
    {A : Type u} [Category.{v} A] [Abelian A]
    {B : Type u'} [Category.{v'} B] [Abelian B]
    [HasDerivedCategory.{w} B]
    (F : A ⥤ B) [F.Additive] (X : A) : Prop :=
  ComputesRightDerived (quasiIsoPlusProperty A)
    (boundedQuasiIsoProperty_properties A).1
    (rightDerivedSourceFunctor F)
    ((HomotopyCategory.Plus.singleFunctor A 0).obj X)

/-- A bounded-below termwise injective complex computes any exact right
derived functor. -/
theorem termwiseInjectiveComplex_computes
    {A : Type u} [Category.{v} A] [Abelian A]
    {D : Type u'} [Category.{v'} D] [AdditiveCategory D]
    [HasZeroObject D] [HasShift D ℤ]
    [∀ n : ℤ, (shiftFunctor D n).Additive]
    [Pretriangulated D] [CategoryTheory.IsTriangulated D]
    (F : KPlus A ⥤ D)
    (_hF : Nonempty (ExactTriangulatedFunctorData F))
    (I : CompPlus A) (hI : IsTermwiseInjectiveComplex I) :
    ComputesRightDerivedComplex F I := by
  let _ : HasDerivedCategory A := HasDerivedCategory.standard A
  let S : MorphismProperty (KPlus A) := quasiIsoPlusProperty A
  let hS : SaturatedMultiplicativeSystem S :=
    by simpa [S] using (boundedQuasiIsoProperty_properties A).1
  let X : KPlus A := (HomotopyCategory.Plus.quotient A).obj I
  let _ : LeftMultiplicativeSystem S := hS.1.1
  let _ : IsFiltered (LeftDenominatorCategory S X) :=
    left_denominator_category_is_filtered X
  have hK : CochainComplex.IsKInjective X.1.as := by
    change CochainComplex.IsKInjective I.obj
    obtain ⟨n, hn⟩ := I.property
    let _ : I.obj.IsStrictlyGE n := hn
    let _ : ∀ n : ℤ, Injective (I.obj.X n) := hI
    exact CochainComplex.isKInjective_of_injective I.obj n
  let Qh := DerivedCategory.Plus.Qh (C := A)
  have hRetract : ∀ s : LeftDenominatorCategory S X,
      ∃ r : s.right ⟶ X, s.hom ≫ r = 𝟙 X := by
    intro s
    let _ : IsIso (Qh.map s.hom) :=
      Localization.inverts Qh S s.hom s.prop
    obtain ⟨r, hr⟩ :=
      (DerivedCategory.Plus.Qh_map_bijective_of_isKInjective s.right X hK).surjective
        (inv (Qh.map s.hom))
    refine ⟨r, ?_⟩
    apply
      (DerivedCategory.Plus.Qh_map_bijective_of_isKInjective X X hK).injective
    rw [Functor.map_comp, hr]
    simp
  let r : ∀ s : LeftDenominatorCategory S X, s.right ⟶ X :=
    fun s => (hRetract s).choose
  have hr (s : LeftDenominatorCategory S X) : s.hom ≫ r s = 𝟙 X :=
    (hRetract s).choose_spec
  have hRetractUnique (s : LeftDenominatorCategory S X)
      (a b : s.right ⟶ X) (ha : s.hom ≫ a = 𝟙 X)
      (hb : s.hom ≫ b = 𝟙 X) : a = b := by
    let _ : IsIso (Qh.map s.hom) :=
      Localization.inverts Qh S s.hom s.prop
    apply
      (DerivedCategory.Plus.Qh_map_bijective_of_isKInjective s.right X hK).injective
    apply (cancel_epi (Qh.map s.hom)).1
    rw [← Qh.map_comp, ← Qh.map_comp, ha, hb]
  let M := rightDerivedDiagram S F X
  let c : Cocone M :=
    { pt := F.obj X
      ι :=
        { app := fun s => F.map (r s)
          naturality := by
            intro s t f
            change F.map f.right ≫ F.map (r t) = F.map (r s) ≫ 𝟙 _
            simp only [Category.comp_id]
            rw [← F.map_comp]
            exact congrArg (fun q => F.map q)
              (hRetractUnique s (f.right ≫ r t) (r s)
                (by rw [← Category.assoc, MorphismProperty.Under.w f, hr]) (hr s)) } }
  have hr₀ : r (rightDerivedIdentityIndex S X) = 𝟙 X := by
    apply hRetractUnique (rightDerivedIdentityIndex S X)
      (r (rightDerivedIdentityIndex S X)) (𝟙 X)
    · exact hr (rightDerivedIdentityIndex S X)
    · change (𝟙 X) ≫ 𝟙 X = 𝟙 X
      simp
  have hc : IsEssentiallyConstantInd M c := by
    refine ⟨rightDerivedIdentityIndex S X, 𝟙 _, ?_, ?_⟩
    · change 𝟙 (F.obj X) ≫ F.map (r (rightDerivedIdentityIndex S X)) = 𝟙 (F.obj X)
      rw [hr₀]
      simp
    · intro j
      let g : j ⟶ rightDerivedIdentityIndex S X :=
        MorphismProperty.Under.homMk (r j) (hr j)
      refine ⟨rightDerivedIdentityIndex S X, 𝟙 _, g, ?_⟩
      dsimp [rightDerivedIdentityIndex, MorphismProperty.Under.mk]
      dsimp [M, c, g, rightDerivedDiagram, rightDerivedIdentityIndex,
        MorphismProperty.Under.mk]
      simp
  let hX : rightDerivedDefined S hS F X := ⟨c, hc⟩
  let c' := rightDerivedCocone S hS F X hX
  have hc' : IsEssentiallyConstantInd M c' := by
    exact Classical.choose_spec hX
  obtain ⟨i, s, hs, hfactor⟩ := hc'
  let gi : i ⟶ rightDerivedIdentityIndex S X :=
    MorphismProperty.Under.homMk (r i) (hr i)
  have hgi : M.map gi ≫ c'.ι.app (rightDerivedIdentityIndex S X) = c'.ι.app i :=
    c'.w gi
  obtain ⟨k, f, g, hfg⟩ := hfactor (rightDerivedIdentityIndex S X)
  let gk : k ⟶ rightDerivedIdentityIndex S X :=
    MorphismProperty.Under.homMk (r k) (hr k)
  have hgk : g ≫ gk = 𝟙 (rightDerivedIdentityIndex S X) := by
    dsimp [rightDerivedIdentityIndex, MorphismProperty.Under.mk] at g gk ⊢
    apply MorphismProperty.Under.Hom.ext
    rw [MorphismProperty.Comma.comp_right]
    dsimp [MorphismProperty.Under.homMk]
    change g.right ≫ r k = 𝟙 X
    have hg : g.right = k.hom := by
      simpa using MorphismProperty.Under.w g
    rw [hg, hr k]
  let a := c'.ι.app (rightDerivedIdentityIndex S X)
  let b := s ≫ M.map gi
  let q := s ≫ M.map f ≫ M.map gk
  have hba : b ≫ a = 𝟙 c'.pt := by
    dsimp [b]
    rw [Category.assoc, hgi, hs]
  have haq : a ≫ q = 𝟙 (M.obj (rightDerivedIdentityIndex S X)) := by
    calc
      a ≫ q = (a ≫ s ≫ M.map f) ≫ M.map gk := by simp [q, Category.assoc]
      _ = M.map g ≫ M.map gk := by rw [hfg]
      _ = M.map (g ≫ gk) := by rw [M.map_comp]
      _ = 𝟙 (M.obj (rightDerivedIdentityIndex S X)) := by rw [hgk]; simp
  have hbq : b = q := by
    calc
      b = b ≫ 𝟙 (M.obj (rightDerivedIdentityIndex S X)) := by simp
      _ = b ≫ (a ≫ q) := by rw [haq]
      _ = (b ≫ a) ≫ q := by simp [Category.assoc]
      _ = q := by
        rw [hba]
        apply Category.id_comp
        
  have ha : IsIso a := by
    let _ : IsIso a := IsIso.mk ⟨q, haq, by rw [← hbq, hba]; simp⟩
    infer_instance
  refine ⟨hX, ?_⟩
  have haFinal : IsIso ((rightDerivedCocone S hS F X hX).ι.app
      ({ left := ⟨⟨⟩⟩, right := X, hom := 𝟙 X, prop := S.id_mem X } :
        LeftDenominatorCategory S X)) := by
    simpa [c', a, rightDerivedIdentityIndex, MorphismProperty.Under.mk] using ha
  have hcomp : IsIso (𝟙 (F.obj X) ≫
      (rightDerivedCocone S hS F X hX).ι.app
        ({ left := ⟨⟨⟩⟩, right := X, hom := 𝟙 X, prop := S.id_mem X } :
          LeftDenominatorCategory S X)) := by
    let leg : F.obj X ⟶ (rightDerivedCocone S hS F X hX).pt := by
      dsimp [rightDerivedDiagram, MorphismProperty.Under.mk]
      exact (rightDerivedCocone S hS F X hX).ι.app
        ({ left := ⟨⟨⟩⟩, right := X, hom := 𝟙 X, prop := S.id_mem X } :
          LeftDenominatorCategory S X)
    have hleg : IsIso leg := by
      dsimp [leg]
      exact haFinal
    let _ : IsIso leg := hleg
    have hcomp' : IsIso (𝟙 (F.obj X) ≫ leg) := by infer_instance
    simpa [leg, rightDerivedDiagram, MorphismProperty.Under.mk] using hcomp'
  simpa [rightDerivedCanonicalMap, rightDerivedValue, rightDerivedDiagram,
    rightDerivedIdentityIndex, MorphismProperty.Under.mk] using hcomp

/-- An injective object is right acyclic for every additive functor. -/
theorem injective_rightAcyclic
    {A : Type u} [Category.{v} A] [Abelian A]
    {B : Type u'} [Category.{v'} B] [Abelian B]
    [HasDerivedCategory.{w} B]
    (F : A ⥤ B) [F.Additive] (I : A) [Injective I] :
    RightAcyclic F I := by
  sorry

/-! ## Enough injectives -/

/-- Enough injectives make an exact functor on `K⁺` right derivable. -/
theorem rightDerived_everywhere_defined_of_enoughInjectives
    {A : Type u} [Category.{v} A] [Abelian A] [EnoughInjectives A]
    {D : Type u'} [Category.{v'} D] [AdditiveCategory D]
    [HasZeroObject D] [HasShift D ℤ]
    [∀ n : ℤ, (shiftFunctor D n).Additive]
    [Pretriangulated D] [CategoryTheory.IsTriangulated D]
    (F : KPlus A ⥤ D) (hF : Nonempty (ExactTriangulatedFunctorData F)) :
    RightDerivable (quasiIsoPlusProperty A)
      (boundedQuasiIsoProperty_properties A).1 F := by
  sorry

/-- For an additive functor between abelian categories, Mathlib's canonical
bounded-below right-derived functor is defined everywhere when the source has
enough injectives. -/
theorem additive_rightDerived_everywhere_defined_of_enoughInjectives
    {A : Type u} [Category.{v} A] [Abelian A] [EnoughInjectives A]
    {B : Type u'} [Category.{v'} B] [Abelian B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} B]
    (F : A ⥤ B) [F.Additive] :
    ∃ (RF : DPlus A ⥤ DPlus B)
      (α : F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh ⟶
        DerivedCategory.Plus.Qh ⋙ RF),
      RF.IsRightDerivedFunctor α (quasiIsoPlusProperty A) := by
  exact ⟨F.rightDerivedFunctorPlus, F.rightDerivedFunctorPlusUnit, inferInstance⟩

end Formalization.Books.Derived.Unit20
