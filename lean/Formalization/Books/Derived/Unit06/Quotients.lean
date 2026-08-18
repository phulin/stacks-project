import Formalization.Books.Derived.Unit05.Localization

/-!
# Derived Categories, Chapter 6: quotients of triangulated categories

The source's Verdier quotient is expressed with Mathlib's canonical
ObjectProperty.trW morphism property and the localization construction.
The declarations in this file keep the source's kernels, saturation
conditions, and universal properties visible without duplicating the
underlying categorical infrastructure.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Preadditive
open CategoryTheory.Pretriangulated
open Formalization.Books.Categories.Unit27
open Formalization.Books.Derived.Unit03
open Formalization.Books.Derived.Unit05
open Formalization.Books.Homology.Unit03
open scoped CategoryTheory.Pretriangulated.Opposite ZeroObject

universe v u

namespace Formalization.Books.Derived.Unit06

/-! ## Saturated subcategories -/

section SaturatedSubcategories

variable {C : Type u} [Category.{v} C] [AdditiveCategory C]
  [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C]

/- The source's phrase "isomorphic to an object of the subcategory" is
   represented by ObjectProperty.isoClosure, the canonical strictly-full
   closure operation. -/

/-- A full pretriangulated subcategory is saturated when it is closed under
direct summands, expressed through binary biproducts and isomorphism closure. -/
def IsSaturated (P : ObjectProperty C) : Prop :=
  ∀ ⦃X Y : C⦄, P.isoClosure (X ⊞ Y) →
    P.isoClosure X ∧ P.isoClosure Y

/-- The source's epaissse condition: in a distinguished triangle, if the
second and third objects belong to the subcategory up to isomorphism, then
so do the first and second objects. -/
def IsEpaissse (P : ObjectProperty C) : Prop :=
  ∀ ⦃X S Y T : C⦄ (a : X ⟶ S) (b : X ⟶ Y) (c : S ⟶ Y)
    (d : Y ⟶ T) (e : T ⟶ X⟦(1 : ℤ)⟧),
    a ≫ c = b → Triangle.mk b d e ∈ distTriang C →
    P.isoClosure S → P.isoClosure T →
    P.isoClosure X ∧ P.isoClosure Y

/- The source's strict-full saturated pretriangulated-subcategory package.
   When the ambient category is triangulated, the earlier
   `Derived.Unit03.TriangulatedSubcategory` interface supplies the remaining
   triangulated-subcategory assertion. -/
def IsStrictlyFullSaturatedPretriangulated (P : ObjectProperty C) : Prop :=
  P.IsClosedUnderIsomorphisms ∧ P.IsTriangulated ∧ IsSaturated P

/-- Saturation and the source's epaissse condition are equivalent. -/
theorem isSaturated_iff_isEpaissse (P : ObjectProperty C)
    [P.IsTriangulated] :
    IsSaturated P ↔ IsEpaissse P := by
  sorry

end SaturatedSubcategories

/-! ## Kernels of exact and homological functors -/

section ExactFunctorKernels

variable {C D : Type*} [Category* C] [Category* D]
  [AdditiveCategory C] [AdditiveCategory D]
  [HasShift C ℤ] [HasShift D ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive]
  [∀ n : ℤ, (shiftFunctor D n).Additive]
  [Pretriangulated C] [Pretriangulated D]

/-- The object property underlying the kernel of an exact functor. -/
def exactFunctorKernel (F : C ⥤ D) : ObjectProperty C :=
  fun X => IsZero (F.obj X)

/-- The kernel of an exact functor is strictly full, saturated, and
pretriangulated. -/
theorem exactFunctorKernel_properties
    (F : C ⥤ D) [F.CommShift ℤ] [F.IsTriangulated] :
    IsStrictlyFullSaturatedPretriangulated (exactFunctorKernel F) := by
  let hClosed : (exactFunctorKernel F).IsClosedUnderIsomorphisms :=
    ⟨fun e hX => hX.of_iso (F.mapIso e).symm⟩
  let hPres : PreservesBinaryBiproducts F :=
    ⟨fun {X Y} => preservesBinaryBiproduct_of_preservesBiproduct F X Y⟩
  refine ⟨hClosed, ?_, ?_⟩
  · exact
      { exists_zero := ⟨0, ⟨isZero_zero C, F.map_isZero (isZero_zero C)⟩⟩
        toIsStableUnderShift := ⟨fun a => ⟨fun X hX =>
          ((shiftFunctor D a).map_isZero hX).of_iso ((F.commShiftIso a).app X)⟩⟩
        toIsTriangulatedClosed₂ :=
          ⟨fun T hT h₁ h₃ =>
            ⟨T.obj₂,
              (F.mapTriangle.obj T).isZero₂_of_isZero₁₃
                (F.map_distinguished T hT) h₁ h₃,
              ⟨Iso.refl _⟩⟩⟩ }
  · intro X Y h
    obtain ⟨Z, hZ, ⟨e⟩⟩ := h
    have hXY : IsZero (F.obj (X ⊞ Y)) := hZ.of_iso (F.mapIso e)
    have hPresXY : PreservesBinaryBiproduct X Y F := hPres.preserves
    have hB : IsZero (F.obj X ⊞ F.obj Y) :=
      hXY.of_iso (@Functor.mapBiprod _ _ _ _ _ _ F X Y _ _ hPresXY).symm
    obtain ⟨hX, hY⟩ := (biprod_isZero_iff _ _).1 hB
    exact ⟨⟨X, hX, ⟨Iso.refl X⟩⟩, ⟨Y, hY, ⟨Iso.refl Y⟩⟩⟩

end ExactFunctorKernels

section HomologicalFunctorKernels

variable {C A : Type*} [Category* C] [Category* A]
  [AdditiveCategory C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C] [Abelian A]

/-- The canonical Mathlib kernel of a homological functor is the source's
subcategory on which every shifted value vanishes. -/
abbrev homologicalFunctorKernel (H : C ⥤ A) : ObjectProperty C :=
  H.homologicalKernel

/-- The kernel of a homological functor is strictly full, saturated, and
pretriangulated. -/
theorem homologicalFunctorKernel_properties
    (H : C ⥤ A) [H.IsHomological] :
    IsStrictlyFullSaturatedPretriangulated (homologicalFunctorKernel H) := by
  refine ⟨inferInstance, inferInstance, ?_⟩
  intro X Y h
  obtain ⟨Z, hZ, ⟨e⟩⟩ := h
  have hXY : homologicalFunctorKernel H (X ⊞ Y) :=
    (homologicalFunctorKernel H).prop_of_iso e.symm hZ
  let hPresH : PreservesBinaryBiproducts H :=
    ⟨fun {X Y} => preservesBinaryBiproduct_of_preservesBiproduct H X Y⟩
  have hX : homologicalFunctorKernel H X := by
    intro n
    let hPresShift : PreservesBinaryBiproducts (shiftFunctor C n) :=
      ⟨fun {X Y} =>
        preservesBinaryBiproduct_of_preservesBiproduct (shiftFunctor C n) X Y⟩
    have hPresShiftXY : PreservesBinaryBiproduct X Y (shiftFunctor C n) :=
      hPresShift.preserves
    have hB : IsZero (H.obj ((shiftFunctor C n).obj X ⊞
        (shiftFunctor C n).obj Y)) := by
      exact (hXY n).of_iso (H.mapIso
        (@Functor.mapBiprod _ _ _ _ _ _ (shiftFunctor C n) X Y _ _ hPresShiftXY).symm)
    have hPresHXY : PreservesBinaryBiproduct ((shiftFunctor C n).obj X)
        ((shiftFunctor C n).obj Y) H := hPresH.preserves
    have hB' : IsZero (H.obj ((shiftFunctor C n).obj X) ⊞
        H.obj ((shiftFunctor C n).obj Y)) :=
      hB.of_iso (@Functor.mapBiprod _ _ _ _ _ _ H
        ((shiftFunctor C n).obj X) ((shiftFunctor C n).obj Y) _ _ hPresHXY).symm
    exact ((biprod_isZero_iff _ _).1 hB').1
  have hY : homologicalFunctorKernel H Y := by
    intro n
    let hPresShift : PreservesBinaryBiproducts (shiftFunctor C n) :=
      ⟨fun {X Y} =>
        preservesBinaryBiproduct_of_preservesBiproduct (shiftFunctor C n) X Y⟩
    have hPresShiftXY : PreservesBinaryBiproduct X Y (shiftFunctor C n) :=
      hPresShift.preserves
    have hB : IsZero (H.obj ((shiftFunctor C n).obj X ⊞
        (shiftFunctor C n).obj Y)) := by
      exact (hXY n).of_iso (H.mapIso
        (@Functor.mapBiprod _ _ _ _ _ _ (shiftFunctor C n) X Y _ _ hPresShiftXY).symm)
    have hPresHXY : PreservesBinaryBiproduct ((shiftFunctor C n).obj X)
        ((shiftFunctor C n).obj Y) H := hPresH.preserves
    have hB' : IsZero (H.obj ((shiftFunctor C n).obj X) ⊞
        H.obj ((shiftFunctor C n).obj Y)) :=
      hB.of_iso (@Functor.mapBiprod _ _ _ _ _ _ H
        ((shiftFunctor C n).obj X) ((shiftFunctor C n).obj Y) _ _ hPresHXY).symm
    exact ((biprod_isZero_iff _ _).1 hB').2
  exact ⟨⟨X, hX, ⟨Iso.refl X⟩⟩, ⟨Y, hY, ⟨Iso.refl Y⟩⟩⟩

/-- Objects whose homology vanishes in all sufficiently negative degrees. -/
def homologicalKernelBelow (H : C ⥤ A) : ObjectProperty C :=
  fun X => ∃ N : ℤ, ∀ n : ℤ, n ≤ N → IsZero ((homologicalDegree H n).obj X)

/-- Objects whose homology vanishes in all sufficiently positive degrees. -/
def homologicalKernelAbove (H : C ⥤ A) : ObjectProperty C :=
  fun X => ∃ N : ℤ, ∀ n : ℤ, N ≤ n → IsZero ((homologicalDegree H n).obj X)

/-- Objects whose homology vanishes outside a bounded range. -/
def homologicalKernelBounded (H : C ⥤ A) : ObjectProperty C :=
  homologicalKernelBelow H ⊓ homologicalKernelAbove H

/-- The three boundedness kernels are strictly full, saturated, and
pretriangulated. -/
theorem homologicalKernel_bounded_properties
    (H : C ⥤ A) [H.IsHomological] :
    IsStrictlyFullSaturatedPretriangulated (homologicalKernelBelow H) ∧
      IsStrictlyFullSaturatedPretriangulated (homologicalKernelAbove H) ∧
      IsStrictlyFullSaturatedPretriangulated (homologicalKernelBounded H) := by
  let hBelowClosed : (homologicalKernelBelow H).IsClosedUnderIsomorphisms :=
    ⟨fun e hX => by
      obtain ⟨N, hN⟩ := hX
      refine ⟨N, fun n hn => (hN n hn).of_iso
        ((homologicalDegree H n).mapIso e.symm)⟩⟩
  have hBelowShift : ∀ (a : ℤ) (X : C), homologicalKernelBelow H X →
      homologicalKernelBelow H (X⟦a⟧) := by
    intro a X hX
    obtain ⟨N, hN⟩ := hX
    refine ⟨N - a, ?_⟩
    intro b hb
    apply (hN (a + b) (by omega)).of_iso
    exact H.mapIso ((shiftFunctorAdd C a b).app X).symm
  have hBelowExt : ∀ (T : Triangle C), T ∈ distTriang C →
      homologicalKernelBelow H T.obj₁ → homologicalKernelBelow H T.obj₃ →
      (homologicalKernelBelow H).isoClosure T.obj₂ := by
    intro T hT h₁ h₃
    obtain ⟨N₁, h₁N⟩ := h₁
    obtain ⟨N₃, h₃N⟩ := h₃
    refine ⟨T.obj₂, ⟨min N₁ N₃, ?_⟩, ⟨Iso.refl _⟩⟩
    intro n hn
    exact
      (H.map_distinguished_exact _ (Triangle.shift_distinguished T hT n)).isZero_of_both_zeros
        (h₁N n (by omega) |>.eq_of_src _ _)
        (h₃N n (by omega) |>.eq_of_tgt _ _)
  let hBelowTri : (homologicalKernelBelow H).IsTriangulated :=
    { exists_zero := ⟨0, ⟨isZero_zero C, by
        change ∃ N : ℤ, ∀ n : ℤ, n ≤ N → IsZero ((homologicalDegree H n).obj 0)
        exact ⟨0, fun n _ =>
          H.map_isZero ((shiftFunctor C n).map_isZero (isZero_zero C))⟩⟩⟩
      toIsStableUnderShift := ⟨fun a => ⟨hBelowShift a⟩⟩
      toIsTriangulatedClosed₂ := ⟨hBelowExt⟩ }
  let hAboveClosed : (homologicalKernelAbove H).IsClosedUnderIsomorphisms :=
    ⟨fun e hX => by
      obtain ⟨N, hN⟩ := hX
      refine ⟨N, fun n hn => (hN n hn).of_iso
        ((homologicalDegree H n).mapIso e.symm)⟩⟩
  have hAboveShift : ∀ (a : ℤ) (X : C), homologicalKernelAbove H X →
      homologicalKernelAbove H (X⟦a⟧) := by
    intro a X hX
    obtain ⟨N, hN⟩ := hX
    refine ⟨N - a, ?_⟩
    intro b hb
    apply (hN (a + b) (by omega)).of_iso
    exact H.mapIso ((shiftFunctorAdd C a b).app X).symm
  have hAboveExt : ∀ (T : Triangle C), T ∈ distTriang C →
      homologicalKernelAbove H T.obj₁ → homologicalKernelAbove H T.obj₃ →
      (homologicalKernelAbove H).isoClosure T.obj₂ := by
    intro T hT h₁ h₃
    obtain ⟨N₁, h₁N⟩ := h₁
    obtain ⟨N₃, h₃N⟩ := h₃
    refine ⟨T.obj₂, ⟨max N₁ N₃, ?_⟩, ⟨Iso.refl _⟩⟩
    intro n hn
    exact
      (H.map_distinguished_exact _ (Triangle.shift_distinguished T hT n)).isZero_of_both_zeros
        (h₁N n (by omega) |>.eq_of_src _ _)
        (h₃N n (by omega) |>.eq_of_tgt _ _)
  let hAboveTri : (homologicalKernelAbove H).IsTriangulated :=
    { exists_zero := ⟨0, ⟨isZero_zero C, by
        change ∃ N : ℤ, ∀ n : ℤ, N ≤ n → IsZero ((homologicalDegree H n).obj 0)
        exact ⟨0, fun n _ =>
          H.map_isZero ((shiftFunctor C n).map_isZero (isZero_zero C))⟩⟩⟩
      toIsStableUnderShift := ⟨fun a => ⟨hAboveShift a⟩⟩
      toIsTriangulatedClosed₂ := ⟨hAboveExt⟩ }
  let hPresH : PreservesBinaryBiproducts H :=
    ⟨fun {X Y} => preservesBinaryBiproduct_of_preservesBiproduct H X Y⟩
  have hComponent : ∀ (X Y : C) (n : ℤ),
      IsZero (H.obj ((X ⊞ Y)⟦n⟧)) →
        IsZero (H.obj (X⟦n⟧)) ∧ IsZero (H.obj (Y⟦n⟧)) := by
    intro X Y n h
    let hPresShift : PreservesBinaryBiproducts (shiftFunctor C n) :=
      ⟨fun {X Y} =>
        preservesBinaryBiproduct_of_preservesBiproduct (shiftFunctor C n) X Y⟩
    have hPresShiftXY : PreservesBinaryBiproduct X Y (shiftFunctor C n) :=
      hPresShift.preserves
    have hB : IsZero (H.obj ((shiftFunctor C n).obj X ⊞
        (shiftFunctor C n).obj Y)) :=
      h.of_iso (H.mapIso
        (@Functor.mapBiprod _ _ _ _ _ _ (shiftFunctor C n) X Y _ _ hPresShiftXY).symm)
    have hPresHXY : PreservesBinaryBiproduct ((shiftFunctor C n).obj X)
        ((shiftFunctor C n).obj Y) H := hPresH.preserves
    have hB' : IsZero (H.obj ((shiftFunctor C n).obj X) ⊞
        H.obj ((shiftFunctor C n).obj Y)) :=
      hB.of_iso (@Functor.mapBiprod _ _ _ _ _ _ H
        ((shiftFunctor C n).obj X) ((shiftFunctor C n).obj Y) _ _ hPresHXY).symm
    exact (biprod_isZero_iff _ _).1 hB'
  have hBelowSat : IsSaturated (homologicalKernelBelow H) := by
    intro X Y h
    obtain ⟨Z, hZ, ⟨e⟩⟩ := h
    have hXY : homologicalKernelBelow H (X ⊞ Y) :=
      hBelowClosed.of_iso e.symm hZ
    obtain ⟨N, hN⟩ := hXY
    have hX : homologicalKernelBelow H X :=
      ⟨N, fun n hn => (hComponent X Y n (hN n hn)).1⟩
    have hY : homologicalKernelBelow H Y :=
      ⟨N, fun n hn => (hComponent X Y n (hN n hn)).2⟩
    exact ⟨⟨X, hX, ⟨Iso.refl X⟩⟩, ⟨Y, hY, ⟨Iso.refl Y⟩⟩⟩
  have hAboveSat : IsSaturated (homologicalKernelAbove H) := by
    intro X Y h
    obtain ⟨Z, hZ, ⟨e⟩⟩ := h
    have hXY : homologicalKernelAbove H (X ⊞ Y) :=
      hAboveClosed.of_iso e.symm hZ
    obtain ⟨N, hN⟩ := hXY
    have hX : homologicalKernelAbove H X :=
      ⟨N, fun n hn => (hComponent X Y n (hN n hn)).1⟩
    have hY : homologicalKernelAbove H Y :=
      ⟨N, fun n hn => (hComponent X Y n (hN n hn)).2⟩
    exact ⟨⟨X, hX, ⟨Iso.refl X⟩⟩, ⟨Y, hY, ⟨Iso.refl Y⟩⟩⟩
  let hBoundedClosed : (homologicalKernelBounded H).IsClosedUnderIsomorphisms :=
    ⟨fun e hX => ⟨hBelowClosed.of_iso e hX.1, hAboveClosed.of_iso e hX.2⟩⟩
  let hBoundedTri : (homologicalKernelBounded H).IsTriangulated :=
    { exists_zero := ⟨0, ⟨isZero_zero C, by
        change homologicalKernelBelow H 0 ∧ homologicalKernelAbove H 0
        constructor
        · change ∃ N : ℤ, ∀ n : ℤ, n ≤ N → IsZero ((homologicalDegree H n).obj 0)
          exact ⟨0, fun n _ =>
            H.map_isZero ((shiftFunctor C n).map_isZero (isZero_zero C))⟩
        · change ∃ N : ℤ, ∀ n : ℤ, N ≤ n → IsZero ((homologicalDegree H n).obj 0)
          exact ⟨0, fun n _ =>
            H.map_isZero ((shiftFunctor C n).map_isZero (isZero_zero C))⟩⟩⟩
      toIsStableUnderShift := ⟨fun a => ⟨fun X hX =>
        ⟨hBelowShift a X hX.1, hAboveShift a X hX.2⟩⟩⟩
      toIsTriangulatedClosed₂ := ⟨fun T hT h₁ h₃ => by
        obtain ⟨Z, hZ, ⟨e⟩⟩ := hBelowExt T hT h₁.1 h₃.1
        obtain ⟨Z', hZ', ⟨e'⟩⟩ := hAboveExt T hT h₁.2 h₃.2
        have hZ₂ : homologicalKernelAbove H T.obj₂ :=
          hAboveClosed.of_iso e'.symm hZ'
        have hZ₃ : homologicalKernelAbove H Z :=
          hAboveClosed.of_iso e hZ₂
        exact ⟨Z, ⟨hZ, hZ₃⟩, ⟨e⟩⟩⟩ }
  have hBoundedSat : IsSaturated (homologicalKernelBounded H) := by
    intro X Y h
    obtain ⟨Z, hZ, ⟨e⟩⟩ := h
    have hXYBelow : homologicalKernelBelow H (X ⊞ Y) :=
      hBelowClosed.of_iso e.symm hZ.1
    have hXYAbove : homologicalKernelAbove H (X ⊞ Y) :=
      hAboveClosed.of_iso e.symm hZ.2
    obtain ⟨NBelow, hNBelow⟩ := hXYBelow
    obtain ⟨NAbove, hNAbove⟩ := hXYAbove
    have hXBelow : homologicalKernelBelow H X :=
      ⟨NBelow, fun n hn => (hComponent X Y n (hNBelow n hn)).1⟩
    have hYBelow : homologicalKernelBelow H Y :=
      ⟨NBelow, fun n hn => (hComponent X Y n (hNBelow n hn)).2⟩
    have hXAbove : homologicalKernelAbove H X :=
      ⟨NAbove, fun n hn => (hComponent X Y n (hNAbove n hn)).1⟩
    have hYAbove : homologicalKernelAbove H Y :=
      ⟨NAbove, fun n hn => (hComponent X Y n (hNAbove n hn)).2⟩
    have hX : homologicalKernelBounded H X := ⟨hXBelow, hXAbove⟩
    have hY : homologicalKernelBounded H Y := ⟨hYBelow, hYAbove⟩
    exact ⟨⟨X, hX, ⟨Iso.refl X⟩⟩, ⟨Y, hY, ⟨Iso.refl Y⟩⟩⟩
  exact ⟨⟨hBelowClosed, hBelowTri, hBelowSat⟩,
    ⟨hAboveClosed, hAboveTri, hAboveSat⟩,
    ⟨hBoundedClosed, hBoundedTri, hBoundedSat⟩⟩

end HomologicalFunctorKernels

/-! ## The kernel-category notation -/

section KernelCategory

variable {C D A : Type*} [Category* C] [Category* D] [Category* A]
  [AdditiveCategory C] [AdditiveCategory D]
  [HasShift C ℤ] [HasShift D ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive]
  [∀ n : ℤ, (shiftFunctor D n).Additive]
  [Pretriangulated C] [Pretriangulated D] [Abelian A]

/- The source's Ker(F) and Ker(H) are represented by the two canonical
object properties above: exactFunctorKernel F and
homologicalFunctorKernel H. -/

abbrev kernelOfExactFunctor (F : C ⥤ D) : ObjectProperty C :=
  exactFunctorKernel F

abbrev kernelOfHomologicalFunctor (H : C ⥤ A) : ObjectProperty C :=
  homologicalFunctorKernel H

end KernelCategory

/-! ## The cone morphism property and its saturation -/

section MultiplicativeSystem

variable {C : Type u} [Category.{v} C] [AdditiveCategory C]
  [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C]

/-- The source's multiplicative system attached to a subcategory, using
Mathlib's canonical cone-morphism property and the source's isomorphism
closure convention. -/
abbrev quotientMorphismProperty (P : ObjectProperty C) : MorphismProperty C :=
  P.isoClosure.trW

/-- Membership in the quotient morphism property is exactly the existence of
a distinguished triangle whose third object lies in the subcategory up to
isomorphism. -/
theorem quotientMorphismProperty_iff (P : ObjectProperty C)
    {X Y : C} (f : X ⟶ Y) :
    quotientMorphismProperty P f ↔
      ∃ (Z : C) (g : Y ⟶ Z) (h : Z ⟶ X⟦(1 : ℤ)⟧)
        (_ : Triangle.mk f g h ∈ distTriang C), P.isoClosure Z := by
  rfl

/-- The quotient morphism property is a compatible multiplicative system for
a full triangulated subcategory. -/
theorem quotientMorphismProperty_isMultiplicative
    (P : ObjectProperty C) [CategoryTheory.IsTriangulated C]
    [P.IsTriangulated] :
    MultiplicativeSystem (quotientMorphismProperty P) ∧
      CompatibleWithTriangulation (quotientMorphismProperty P) := by
  exact ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩

/-- Saturation of the cone-morphism system is equivalent to saturation of the
underlying triangulated subcategory. -/
theorem quotientMorphismProperty_isSaturated_iff
    (P : ObjectProperty C) [CategoryTheory.IsTriangulated C]
    [P.IsTriangulated] :
    SaturatedMultiplicativeSystem (quotientMorphismProperty P) ↔
      IsSaturated P := by
  let W : MorphismProperty C := quotientMorphismProperty P
  have hZero (R : C) (hR : P.isoClosure R) : IsZero (W.Q.obj R) := by
    have hf : W (0 : (0 : C) ⟶ R) := by
      change P.isoClosure.trW (0 : (0 : C) ⟶ R)
      exact ⟨R, 𝟙 R, 0, contractible_distinguished₁ R, hR⟩
    letI : IsIso (W.Q.map (0 : (0 : C) ⟶ R)) :=
      MorphismProperty.Q_inverts W _ hf
    exact (W.Q.map_isZero (isZero_zero C)).of_iso
      (asIso (W.Q.map (0 : (0 : C) ⟶ R)))
  constructor
  · intro hW
    intro X Y hXY
    have hQsum : IsZero (W.Q.obj (X ⊞ Y)) := hZero _ hXY
    have hQX : IsZero (W.Q.obj X) := by
      refine ⟨fun Z f g => ?_⟩
      calc
        f = f ≫ W.Q.map biprod.inl ≫ W.Q.map biprod.fst := by simp
        _ = g ≫ W.Q.map biprod.inl ≫ W.Q.map biprod.fst := by
          rw [hQsum.eq_of_tgt (f ≫ W.Q.map biprod.inl)
            (g ≫ W.Q.map biprod.inl)]
        _ = g := by simp
    have hQY : IsZero (W.Q.obj Y) := by
      refine ⟨fun Z f g => ?_⟩
      calc
        f = f ≫ W.Q.map biprod.inr ≫ W.Q.map biprod.snd := by simp
        _ = g ≫ W.Q.map biprod.inr ≫ W.Q.map biprod.snd := by
          rw [hQsum.eq_of_tgt (f ≫ W.Q.map biprod.inr)
            (g ≫ W.Q.map biprod.inr)]
        _ = g := by simp
    have hCharX := kernel_localization_characterization (S := W) X
    have hCharY := kernel_localization_characterization (S := W) Y
    have h0X : W (0 : (0 : C) ⟶ X) :=
      (hCharX.2.2.2 hW).1 hQX
    have h0Y : W (0 : (0 : C) ⟶ Y) :=
      (hCharY.2.2.2 hW).1 hQY
    have hX : P.isoClosure X := by
      change P.isoClosure.trW (0 : (0 : C) ⟶ X) at h0X
      obtain ⟨K, f, g, hT, hK⟩ := h0X
      obtain ⟨e, _⟩ := exists_iso_of_arrow_iso
        (Triangle.mk (0 : (0 : C) ⟶ X) f g)
        (Triangle.mk (0 : (0 : C) ⟶ X) (𝟙 X) 0) hT
        (contractible_distinguished₁ X)
        (Arrow.isoMk (Iso.refl _) (Iso.refl _) (by simp))
      exact ⟨K, hK, ⟨asIso e.hom.hom₃⟩⟩
    have hY : P.isoClosure Y := by
      change P.isoClosure.trW (0 : (0 : C) ⟶ Y) at h0Y
      obtain ⟨K, f, g, hT, hK⟩ := h0Y
      obtain ⟨e, _⟩ := exists_iso_of_arrow_iso
        (Triangle.mk (0 : (0 : C) ⟶ Y) f g)
        (Triangle.mk (0 : (0 : C) ⟶ Y) (𝟙 Y) 0) hT
        (contractible_distinguished₁ Y)
        (Arrow.isoMk (Iso.refl _) (Iso.refl _) (by simp))
      exact ⟨K, hK, ⟨asIso e.hom.hom₃⟩⟩
    exact ⟨hX, hY⟩
  · intro hSat
    refine ⟨(quotientMorphismProperty_isMultiplicative P).1, ?_⟩
    intro X Y Z T f g h hfg hgh
    letI : IsIso (W.Q.map (f ≫ g)) :=
      MorphismProperty.Q_inverts W _ hfg
    letI : IsIso (W.Q.map (g ≫ h)) :=
      MorphismProperty.Q_inverts W _ hgh
    letI : IsIso (W.Q.map g) := by
      apply isIso_of_adjacent_composites (W.Q.map f) (W.Q.map g) (W.Q.map h)
      · rw [← W.Q.map_comp]
        infer_instance
      · rw [← W.Q.map_comp]
        infer_instance
    obtain ⟨K, u, v, hT⟩ := distinguished_cocone_triangle g
    have hTQ : W.Q.mapTriangle.obj (Triangle.mk g u v) ∈ distTriang _ :=
      W.Q.map_distinguished _ hT
    have hKzero : IsZero (W.Q.obj K) := by
      apply Triangle.isZero₃_of_isIso₁ _ hTQ
      change IsIso (W.Q.map g)
      infer_instance
    have hsum : ∃ K' : C, P.isoClosure (K ⊞ K') :=
      (quotientFunctor_kernel_iff P K).1 hKzero
    obtain ⟨K', hsum⟩ := hsum
    have hK : P.isoClosure K := (hSat hsum).1
    change P.isoClosure.trW g
    exact ⟨K, u, v, hT, hK⟩

end MultiplicativeSystem

/-! ## The Verdier quotient and its universal property -/

section QuotientCategory

variable {C : Type u} [Category.{v} C] [AdditiveCategory C]
  [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C]

/-- The quotient category by the full subcategory represented by P. -/
abbrev quotientCategory (P : ObjectProperty C) : Type _ :=
  (quotientMorphismProperty P).Localization

/-- The quotient functor into the Verdier quotient. -/
abbrev quotientFunctor (P : ObjectProperty C) : C ⥤ quotientCategory P :=
  (quotientMorphismProperty P).Q

/-- The quotient functor is exact. -/
theorem quotientFunctor_isExact (P : ObjectProperty C)
    [CategoryTheory.IsTriangulated C] [P.IsTriangulated] :
    (quotientFunctor P).IsTriangulated := by
  infer_instance

/-- A functor which inverts the quotient morphisms factors through the
quotient category. -/
noncomputable def quotientFactor {E : Type*} [Category* E]
    (P : ObjectProperty C) (F : C ⥤ E)
    (hF : (quotientMorphismProperty P).IsInvertedBy F) :
    quotientCategory P ⥤ E :=
  Localization.Construction.lift F hF

/-- The factorization supplied by the localization construction composes
with the quotient functor to the original functor. -/
theorem quotientFactor_fac {E : Type*} [Category* E]
    (P : ObjectProperty C) (F : C ⥤ E)
    (hF : (quotientMorphismProperty P).IsInvertedBy F) :
    quotientFunctor P ⋙ quotientFactor P F hF = F :=
  Localization.Construction.fac F hF

/-- The factorization through the quotient is unique as a functor. -/
theorem quotientFactor_unique {E : Type*} [Category* E]
    (P : ObjectProperty C) (F₁ F₂ : quotientCategory P ⥤ E)
    (h : quotientFunctor P ⋙ F₁ = quotientFunctor P ⋙ F₂) : F₁ = F₂ :=
  Localization.Construction.uniq F₁ F₂ h

/-- The Verdier quotient has the source's universal property for homological
functors and exact functors. -/
theorem quotient_universal_property
    {A D : Type*} [Category* A] [Category* D]
    [Abelian A] [AdditiveCategory D]
    [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive]
    [Pretriangulated D]
    (P : ObjectProperty C) [CategoryTheory.IsTriangulated C]
    [P.IsTriangulated]
    (H : C ⥤ A) [H.IsHomological]
    (hH : P ≤ homologicalFunctorKernel H) :
    ∃! H' : quotientCategory P ⥤ A,
      quotientFunctor P ⋙ H' = H ∧ H'.IsHomological := by
  letI : H.ShiftSequence ℤ := Functor.ShiftSequence.tautological H ℤ
  let hInv : (quotientMorphismProperty P).IsInvertedBy H := by
    intro X Y f hf
    change P.isoClosure.trW f at hf
    rw [ObjectProperty.trW_isoClosure] at hf
    have hf' : (homologicalFunctorKernel H).trW f :=
      ObjectProperty.trW_monotone hH _ hf
    have hAll := (Functor.mem_homologicalKernel_trW_iff H f).1 hf'
    exact (NatIso.isIso_map_iff (H.isoShiftZero ℤ) f).1 (hAll 0)
  let H' : quotientCategory P ⥤ A := quotientFactor P H hInv
  refine ⟨H', ⟨quotientFactor_fac P H hInv, ?_⟩, ?_⟩
  · exact Formalization.Books.Derived.Unit05.homological_localizationFactor_isHomological H hInv
  · intro H₁ h₁
    exact quotientFactor_unique P H₁ H'
      (h₁.1.trans (quotientFactor_fac P H hInv).symm)

theorem quotient_universal_property_exact
    {D : Type*} [Category* D] [Preadditive D] [HasZeroObject D]
    [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive]
    [Pretriangulated D]
    (P : ObjectProperty C) [CategoryTheory.IsTriangulated C]
    [P.IsTriangulated]
    (F : C ⥤ D) [F.CommShift ℤ] [F.IsTriangulated]
    (hF : P ≤ exactFunctorKernel F) :
    ∃! F' : quotientCategory P ⥤ D,
      quotientFunctor P ⋙ F' = F ∧
        IsExactLocalizationFactor
          (S := quotientMorphismProperty P) F' := by
  let hInv : (quotientMorphismProperty P).IsInvertedBy F := by
    intro X Y f hf
    change P.isoClosure.trW f at hf
    rw [ObjectProperty.trW_isoClosure] at hf
    obtain ⟨Z, g, h, hT, hZ⟩ := hf
    let T := Triangle.mk f g h
    have hFT : F.mapTriangle.obj T ∈ distTriang D :=
      F.map_distinguished T hT
    have hFZ : IsZero (F.obj Z) := hF Z hZ
    have hFZ' : IsZero (F.mapTriangle.obj T).obj₃ :=
      hFZ
    exact (Triangle.isZero₃_iff_isIso₁ _ hFT).1 hFZ'
  let F' : quotientCategory P ⥤ D := quotientFactor P F hInv
  refine ⟨F', ⟨quotientFactor_fac P F hInv, ?_⟩, ?_⟩
  · exact Formalization.Books.Derived.Unit05.exact_localizationFactor_isExact F hInv
  · intro F₁ h₁
    exact quotientFactor_unique P F₁ F'
      (h₁.1.trans (quotientFactor_fac P F hInv).symm)

end QuotientCategory

/-! ## The kernel of the quotient functor -/

section QuotientKernel

variable {C : Type u} [Category.{v} C] [AdditiveCategory C]
  [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C]

/-- The source's explicit object property for the kernel of the quotient
functor: objects which become a direct summand of an object of P. -/
def quotientKernel (P : ObjectProperty C) : ObjectProperty C :=
  fun Z => ∃ Z' : C, P.isoClosure (Z ⊞ Z')

/-- The explicit object description of the quotient kernel. -/
theorem quotientFunctor_kernel_iff (P : ObjectProperty C)
    [CategoryTheory.IsTriangulated C] [P.IsTriangulated]
    (Z : C) :
    exactFunctorKernel (quotientFunctor P) Z ↔ quotientKernel P Z := by
  change IsZero ((quotientMorphismProperty P).Q.obj Z) ↔ quotientKernel P Z
  let hK := kernel_localization_characterization
    (S := quotientMorphismProperty P) Z
  constructor
  · intro hZ
    have hB : KernelLocalizationBiproductTriangle
        (quotientMorphismProperty P) Z :=
      hK.2.2.1 (hK.2.1 (hK.1.mp hZ))
    obtain ⟨Z', X, Y, f, g, h, hT, hf⟩ := hB
    change P.isoClosure.trW f at hf
    obtain ⟨W, g', h', hT', hW⟩ := hf
    obtain ⟨e, _⟩ := exists_iso_of_arrow_iso
      (Triangle.mk f g h) (Triangle.mk f g' h') hT hT'
      (Arrow.isoMk (Iso.refl _) (Iso.refl _) (by simp))
    exact ⟨Z', W, hW, ⟨asIso e.hom.hom₃⟩⟩
  · rintro ⟨Z', hZZ'⟩
    apply hK.1.mpr
    apply hK.2.1.mpr
    apply hK.2.2.1.mpr
    let K := Z ⊞ Z'
    refine ⟨Z', (0 : C), K, (0 : (0 : C) ⟶ K),
      𝟙 K, (0 : K ⟶ (0 : C)⟦(1 : ℤ)⟧), ?_, ?_⟩
    · exact contractible_distinguished₁ K
    · change P.isoClosure.trW (0 : (0 : C) ⟶ K)
      exact ⟨K, 𝟙 K, 0, contractible_distinguished₁ K, hZZ'⟩

/-- The quotient kernel is the smallest strictly full saturated triangulated
subcategory containing the subcategory being quotiented out. -/
theorem quotientKernel_is_smallest (P : ObjectProperty C)
    [CategoryTheory.IsTriangulated C] [P.IsTriangulated] :
    IsStrictlyFullSaturatedPretriangulated (quotientKernel P) ∧
      P ≤ quotientKernel P ∧
      ∀ Q : ObjectProperty C,
        Q.IsClosedUnderIsomorphisms → Q.IsTriangulated → IsSaturated Q →
        quotientKernel P ≤ Q := by
  refine ⟨?_, ?_, ?_⟩
  · have hK := exactFunctorKernel_properties (F := quotientFunctor P)
    have heq : exactFunctorKernel (quotientFunctor P) = quotientKernel P := by
      ext Z
      exact quotientFunctor_kernel_iff P Z
    rw [← heq]
    exact hK
  · intro Z hZ
    refine ⟨0, ⟨Z, hZ, ⟨?_⟩⟩⟩
    refine { hom := biprod.fst, inv := biprod.inl, ?_, ?_ }
    · simp
    · simp
  · sorry

end QuotientKernel

/-! ## Operations on multiplicative systems and subcategories -/

section Operations

variable {C : Type u} [Category.{v} C] [AdditiveCategory C]
  [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C]

/-- The subcategory B(S) = Ker(Q) attached to a localization system. -/
abbrev localizationKernel (S : MorphismProperty C) : ObjectProperty C :=
  IsZeroAfterLocalization S

/-- The operation from full triangulated subcategories to cone-morphism
properties. -/
abbrev subcategoryOperation (P : ObjectProperty C) : MorphismProperty C :=
  quotientMorphismProperty P

/-- The operation from a morphism property to the arrows inverted by its
localization. -/
abbrev localizationOperation (S : MorphismProperty C) : MorphismProperty C :=
  invertedByLocalization S

/-- The two operations are order preserving. -/
theorem operations_monotone_subcategory
    {P Q : ObjectProperty C} (hPQ : P ≤ Q) :
    subcategoryOperation P ≤ subcategoryOperation Q := by
  unfold subcategoryOperation quotientMorphismProperty
  exact ObjectProperty.trW_monotone (ObjectProperty.monotone_isoClosure hPQ)

theorem operations_monotone_localization
    {S T : MorphismProperty C} [CategoryTheory.IsTriangulated C]
    [CompatibleWithTriangulation S] [CompatibleWithTriangulation T]
    (hS : MultiplicativeSystem S) (hT : MultiplicativeSystem T)
    (hST : S ≤ T) :
    localizationKernel S ≤ localizationKernel T := by
  sorry

/-- The first composite is the saturation of a multiplicative system. -/
theorem operations_morphismProperty_saturation
    {S : MorphismProperty C} [CategoryTheory.IsTriangulated C]
    [CompatibleWithTriangulation S] (hS : MultiplicativeSystem S) :
    subcategoryOperation (localizationKernel S) = saturationClosure S := by
  sorry

end Operations

section SaturationClosure

variable {C : Type u} [Category.{v} C]

/-- The saturation closure is the smallest saturated multiplicative system
containing the original one. -/
theorem operations_morphismProperty_saturation_smallest
    {S : MorphismProperty C} (hS : MultiplicativeSystem S) :
    S ≤ saturationClosure S ∧
      SaturatedMultiplicativeSystem (saturationClosure S) ∧
      ∀ V : MorphismProperty C, SaturatedMultiplicativeSystem V → S ≤ V →
        saturationClosure S ≤ V :=
  saturationClosure_is_smallest hS

end SaturationClosure

section Operations

variable {C : Type u} [Category.{v} C] [AdditiveCategory C]
  [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C]

/-- The second composite is the saturation of a triangulated subcategory. -/
theorem operations_subcategory_saturation
    (P : ObjectProperty C) [CategoryTheory.IsTriangulated C]
    [P.IsTriangulated] :
    localizationKernel (subcategoryOperation P) = quotientKernel P := by
  sorry

/- The source warns that the two operations are not mutually inverse before
   saturation; the saturation statements above and below record the precise
   inverse form. -/
/-- The two operations become inverse on saturated systems and saturated
strictly full triangulated subcategories. -/
theorem operations_restrict_to_saturated_inverse
    {S : MorphismProperty C} {P : ObjectProperty C}
    [CategoryTheory.IsTriangulated C] [P.IsTriangulated]
    [CompatibleWithTriangulation S]
    (hS : SaturatedMultiplicativeSystem S)
    (hP : IsStrictlyFullSaturatedPretriangulated P) :
    localizationOperation S = S ∧ quotientKernel P = P := by
  sorry

end Operations

/-! ## Acyclic objects and homological functors -/

section AcyclicFunctor

variable {C A : Type*} [Category* C] [Category* A]
  [AdditiveCategory C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C] [Abelian A]

/-- The homological-functor morphism property is a saturated compatible
multiplicative system. -/
theorem acyclic_morphismProperty_isSaturated
    (H : C ⥤ A) [H.IsHomological] :
    SaturatedMultiplicativeSystem (homologicalFunctorMorphismProperty H) ∧
      CompatibleWithTriangulation (homologicalFunctorMorphismProperty H) :=
  homologicalFunctorMorphismProperty_saturated H

/-- The cone-morphism system of the homological kernel is the class of maps
which are isomorphisms in every homological degree. -/
theorem acyclic_kernel_morphismProperty_eq
    (H : C ⥤ A) [CategoryTheory.IsTriangulated C] [H.IsHomological] :
    subcategoryOperation (homologicalFunctorKernel H) =
      homologicalFunctorMorphismProperty H := by
  sorry

/-- A homological functor factors through the quotient by its acyclic kernel. -/
theorem acyclic_homologicalFunctor_factors
    (H : C ⥤ A) [CategoryTheory.IsTriangulated C] [H.IsHomological] :
    ∃! H' : quotientCategory (homologicalFunctorKernel H) ⥤ A,
      quotientFunctor (homologicalFunctorKernel H) ⋙ H' = H ∧
        H'.IsHomological := by
  sorry

end AcyclicFunctor

end Formalization.Books.Derived.Unit06
