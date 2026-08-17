import Mathlib.Algebra.Homology.DerivedCategory.Plus
import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import Mathlib.Algebra.Homology.ExactSequence
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import Mathlib.CategoryTheory.Abelian.RightDerived
import Mathlib.CategoryTheory.Functor.OfSequence
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import Mathlib.CategoryTheory.Limits.Shapes.Countable
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.CategoryTheory.Triangulated.Yoneda
import Formalization.Books.Derived.Unit04.ElementaryResults
import Formalization.Books.Derived.Unit11.DerivedCategories

/-!
# Derived Categories, Chapter 33: derived colimits

This file records the definitions and theorem interfaces in the chapter.  The
proofs of the substantive results are deferred, while coproduct maps,
sequential systems, and the canonical hom-colimit cocones use Mathlib's
categorical constructions directly.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Preadditive
open CategoryTheory.Pretriangulated
open CategoryTheory.Triangulated
open Formalization.Books.Derived.Unit04
open Formalization.Books.Derived.Unit11
open Formalization.Books.Homology.Unit03
open scoped CategoryTheory.Pretriangulated.Opposite ZeroObject

universe v u v' u' w

namespace Formalization.Books.Derived.Unit33

/-! ## Derived colimits and their presentations -/

abbrev SequentialSystem (C : Type u) [Category.{v} C] := ℕ ⥤ C

variable {C : Type u} [Category.{v} C] [AdditiveCategory C]
  [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C]

/-- The transition map in a sequential system. -/
abbrev sequentialTransition (F : SequentialSystem C) (n : ℕ) :
    F.obj n ⟶ F.obj (n + 1) := F.map (homOfLE (Nat.le_succ n))

/-- The map `1 - f` on the coproduct used to define a homotopy colimit. -/
noncomputable def hocolimDifferenceMap (F : SequentialSystem C)
    [HasCoproduct (fun n => F.obj n)] :
    (∐ fun n => F.obj n) ⟶ ∐ fun n => F.obj n :=
  Sigma.desc (fun n =>
    Sigma.ι (fun n => F.obj n) n -
      sequentialTransition F n ≫ Sigma.ι (fun n => F.obj n) (n + 1))

/-- A morphism of sequential systems induces the corresponding map of
coproducts. -/
noncomputable def sequentialCoproductMap {D : Type u'} [Category.{v'} D]
    (F G : SequentialSystem D) (a : F ⟶ G)
    [HasCoproduct (fun n => F.obj n)] [HasCoproduct (fun n => G.obj n)] :
    (∐ fun n => F.obj n) ⟶ ∐ fun n => G.obj n :=
  Sigma.desc (fun n => a.app n ≫ Sigma.ι (fun n => G.obj n) n)

/-- The defining distinguished triangle for a derived colimit. -/
def IsDerivedColimit (F : SequentialSystem C) (K : C)
    [HasCoproduct (fun n => F.obj n)] : Prop :=
  ∃ (i : (∐ fun n => F.obj n) ⟶ K)
    (c : K ⟶ (∐ fun n => F.obj n)⟦(1 : ℤ)⟧),
    Triangle.mk (hocolimDifferenceMap F) i c ∈ distTriang C

/-- A chosen stagewise presentation of a derived colimit.  Compatibility is
recorded for every arrow of the preorder; the adjacent-stage formulation in
the source is the special case `m = n`, `n = n + 1`. -/
structure DerivedColimitPresentation (F : SequentialSystem C) (K : C)
    [HasCoproduct (fun n => F.obj n)] where
  ι : ∀ n, F.obj n ⟶ K
  compatible : ∀ {m n : ℕ} (f : m ⟶ n), F.map f ≫ ι n = ι m
  c : K ⟶ (∐ fun n => F.obj n)⟦(1 : ℤ)⟧
  distinguished :
    Triangle.mk (hocolimDifferenceMap F) (Sigma.desc ι) c ∈ distTriang C

@[simp, reassoc]
theorem DerivedColimitPresentation.compatible_succ
    {F : SequentialSystem C} {K : C}
    [HasCoproduct (fun n => F.obj n)]
    (p : DerivedColimitPresentation F K) (n : ℕ) :
    sequentialTransition F n ≫ p.ι (n + 1) = p.ι n :=
  p.compatible (homOfLE (Nat.le_succ n))

/-- A presentation has the source's compact coproduct map as its second
triangle morphism. -/
noncomputable def DerivedColimitPresentation.coproductMap
    {F : SequentialSystem C} {K : C}
    [HasCoproduct (fun n => F.obj n)]
    (p : DerivedColimitPresentation F K) :
    (∐ fun n => F.obj n) ⟶ K :=
  Sigma.desc p.ι

/-- The existence assertion supplied by TR1 once the coproduct exists. -/
theorem exists_isDerivedColimit (F : SequentialSystem C)
    [HasCoproduct (fun n => F.obj n)] : ∃ K : C, IsDerivedColimit F K := by
  sorry

/-- A chosen homotopy colimit, used only when an existence witness has been
fixed. -/
noncomputable def homotopyColimit (F : SequentialSystem C)
    [HasCoproduct (fun n => F.obj n)] (hF : ∃ K : C, IsDerivedColimit F K) : C :=
  Classical.choose hF

theorem homotopyColimit_isDerivedColimit (F : SequentialSystem C)
    [HasCoproduct (fun n => F.obj n)] (hF : ∃ K : C, IsDerivedColimit F K) :
    IsDerivedColimit F (homotopyColimit F hF) := by
  exact Classical.choose_spec hF

/-- Every defining triangle can be equipped with the compatible stage maps
used in the source's uniqueness remark. -/
theorem presentation_of_isDerivedColimit
    {F : SequentialSystem C} {K : C}
    [HasCoproduct (fun n => F.obj n)] (hK : IsDerivedColimit F K) :
    Nonempty (DerivedColimitPresentation F K) := by
  sorry

/-- The TR3 uniqueness statement for two presented derived colimits. -/
theorem derivedColimit_iso_of_presentations
    {F : SequentialSystem C} {K K' : C}
    [HasCoproduct (fun n => F.obj n)]
    (p : DerivedColimitPresentation F K)
    (p' : DerivedColimitPresentation F K') :
    ∃ e : K ≅ K',
      (∀ n, p.ι n ≫ e.hom = p'.ι n) ∧ e.hom ≫ p'.c = p.c := by
  sorry

/-- Functoriality of presented derived colimits. -/
theorem derivedColimit_map
    {F G : SequentialSystem C}
    {K L : C} [HasCoproduct (fun n => F.obj n)]
    [HasCoproduct (fun n => G.obj n)]
    (a : F ⟶ G) (p : DerivedColimitPresentation F K)
    (q : DerivedColimitPresentation G L) :
    ∃ φ : K ⟶ L,
      (∀ n, p.ι n ≫ φ = a.app n ≫ q.ι n) ∧
        φ ≫ q.c = p.c ≫ (sequentialCoproductMap F G a)⟦(1 : ℤ)⟧' := by
  sorry

/-! ## Passing to a cofinal subsequence -/

/-- The sequential system obtained by restricting along a strictly increasing
sequence of indices. -/
abbrev subsequenceSystem (F : SequentialSystem C) (s : ℕ → ℕ)
    (hs : StrictMono s) : SequentialSystem C :=
  Functor.ofSequence
    (fun n => F.map (homOfLE (hs.monotone (Nat.le_succ n))))

theorem derivedColimit_subsequence_iso
    {F : SequentialSystem C} (s : ℕ → ℕ) (hs : StrictMono s)
    {K K' : C}
    [HasCoproduct (fun n => (subsequenceSystem F s hs).obj n)]
    [HasCoproduct (fun n => F.obj n)]
    (p : DerivedColimitPresentation (subsequenceSystem F s hs) K)
    (q : DerivedColimitPresentation F K') :
    ∃ e : K ≅ K', ∀ i, p.ι i ≫ e.hom = q.ι (s i) := by
  sorry

/-! ## The Hom exact sequence -/

/-- The inverse-system of Hom groups occurring in the map-out-of-hocolim
sequence. -/
abbrev homInverseSystem (D : Type u') [Category.{v'} D] [Preadditive D]
    (F : ℕ ⥤ D) (L : D) :
    ℕᵒᵖ ⥤ AddCommGrpCat.{v'} :=
  F.op ⋙ preadditiveYoneda.obj L

/-- The object denoted `R¹ lim` in the source, using Mathlib's right-derived
functor of the inverse-limit functor. -/
noncomputable instance limitFunctor_additive :
    (lim : (ℕᵒᵖ ⥤ AddCommGrpCat.{w}) ⥤ AddCommGrpCat.{w}).Additive where
  map_add := by
    intro F G f g
    apply limit.hom_ext
    intro j
    simp [limMap_π]

noncomputable abbrev firstDerivedLimit
    (M : ℕᵒᵖ ⥤ AddCommGrpCat.{w})
    [HasInjectiveResolutions (ℕᵒᵖ ⥤ AddCommGrpCat.{w})] : AddCommGrpCat.{w} :=
  ((lim : (ℕᵒᵖ ⥤ AddCommGrpCat.{w}) ⥤ AddCommGrpCat.{w}).rightDerived 1).obj M

/-- The exact sequence describing maps out of a homotopy colimit. -/
theorem hom_from_homotopyColimit_exact
    {F : SequentialSystem C} {K L : C}
    [HasCoproduct (fun n => F.obj n)]
    (p : DerivedColimitPresentation F K)
    [HasInjectiveResolutions (ℕᵒᵖ ⥤ AddCommGrpCat.{v})] :
    ∃ α : firstDerivedLimit
      (@homInverseSystem.{v, u} C (inferInstance : Category.{v} C)
        (inferInstance : Preadditive C) F (L⟦(-1 : ℤ)⟧)) ⟶
        (preadditiveCoyoneda.obj (Opposite.op K)).obj L,
      ∃ β : (preadditiveCoyoneda.obj (Opposite.op K)).obj L ⟶
        (lim : (ℕᵒᵖ ⥤ AddCommGrpCat.{v}) ⥤ AddCommGrpCat.{v}).obj
          (@homInverseSystem.{v, u} C (inferInstance : Category.{v} C)
            (inferInstance : Preadditive C) F L),
        (ComposableArrows.mk₄
          (0 : (0 : AddCommGrpCat.{v}) ⟶
            firstDerivedLimit
              (@homInverseSystem.{v, u} C (inferInstance : Category.{v} C)
                (inferInstance : Preadditive C) F (L⟦(-1 : ℤ)⟧)))
          α β
          (0 : (lim : (ℕᵒᵖ ⥤ AddCommGrpCat.{v}) ⥤ AddCommGrpCat.{v}).obj
            (@homInverseSystem.{v, u} C (inferInstance : Category.{v} C)
              (inferInstance : Preadditive C) F L) ⟶ (0 : AddCommGrpCat.{v}))).Exact := by
  sorry

/-! ## Countable direct sums in derived categories -/

/-- The termwise coproduct of a countable family of complexes. -/
noncomputable def termwiseCoproductComplex
    {A : Type u} [Category.{v} A] [Abelian A]
    {I : Type u'} [Countable I] (K : I → CochainComplex A ℤ)
    [HasCountableCoproducts A] : CochainComplex A ℤ :=
  ∐ K

/-- Exact countable direct sums in the abelian category give countable
coproducts in its derived category. -/
instance derivedCategory_hasCountableCoproducts
    (A : Type u) [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A] [HasCountableCoproducts A]
    [CountableAB4 A] :
    HasCountableCoproducts (DerivedCategory A) := by
  sorry

/-- In particular, the derived category of abelian groups has all sequential
homotopy colimits.  The generic abelian-category statement also applies to
`D(Ab)` by taking `A` to be the category of abelian groups. -/
theorem derivedCategory_homotopyColimit_exists
    {A : Type u} [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A] [HasCountableCoproducts A]
    [CountableAB4 A] (F : ℕ ⥤ DerivedCategory A) :
    ∃ K : DerivedCategory A, IsDerivedColimit F K := by
  apply exists_isDerivedColimit F

/-- The canonical derived-category cofan represented by a termwise sum. -/
noncomputable def derivedTermwiseCoproductCofan
    {A : Type u} [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A] {I : Type u'} [Countable I]
    (K : I → CochainComplex A ℤ)
    [HasCountableCoproducts A] [CountableAB4 A] :
    Cofan (fun i => (DerivedCategory.Q : CochainComplex A ℤ ⥤
      DerivedCategory A).obj (K i)) :=
  Cofan.mk
    (DerivedCategory.Q.obj (termwiseCoproductComplex K))
    (fun i => DerivedCategory.Q.map (Sigma.ι K i))

noncomputable def derivedTermwiseCoproductCofan_isColimit
    {A : Type u} [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A] {I : Type u'} [Countable I]
    (K : I → CochainComplex A ℤ)
    [HasCountableCoproducts A] [CountableAB4 A] :
    IsColimit (derivedTermwiseCoproductCofan K) := by
  sorry

/-! ## Computing sequential colimits -/

/-- The canonical map from the coproduct of a sequential system to its
ordinary colimit. -/
noncomputable def coproductToSequentialColimit
    {A : Type u} [Category.{v} A] [Preadditive A]
    (F : SequentialSystem A) [HasCoproduct (fun n => F.obj n)]
    [HasColimit F] :
    (∐ fun n => F.obj n) ⟶ colimit F :=
  Sigma.desc (fun n => colimit.ι F n)

/-- Exact sequential colimits supply the countable coproduct and exactness
classes used by the later derived-category statements. -/
theorem exact_sequential_colimits_give_countable_direct_sums
    (A : Type u) [Category.{v} A] [Abelian A]
    [HasColimitsOfShape ℕ A] [HasExactColimitsOfShape ℕ A] :
    ∃ hA : HasCountableCoproducts A, @CountableAB4 A _ hA := by
  sorry

/-- The source's short exact sequence computing a sequential colimit. -/
theorem sequential_colimit_exact_sequence
    {A : Type u} [Category.{v} A] [Abelian A]
    [HasColimitsOfShape ℕ A] [HasExactColimitsOfShape ℕ A]
    [HasCountableCoproducts A] [CountableAB4 A]
    (F : SequentialSystem A) :
    (ComposableArrows.mk₄
      (0 : (0 : A) ⟶ ∐ fun n => F.obj n)
      (hocolimDifferenceMap F)
      (coproductToSequentialColimit F)
      (0 : colimit F ⟶ (0 : A))).Exact := by
  sorry

/-! ## Ordinary colimits as homotopy colimits -/

/-- The system in the derived category obtained from a system of complexes. -/
abbrev derivedComplexSystem
    {A : Type u} [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A]
    (L : SequentialSystem (CochainComplex A ℤ)) :
    SequentialSystem (DerivedCategory A) :=
  L ⋙ (DerivedCategory.Q : CochainComplex A ℤ ⥤ DerivedCategory A)

/-- The termwise ordinary colimit of a sequential system of complexes. -/
noncomputable def termwiseColimitComplex
    {A : Type u} [Category.{v} A] [Abelian A]
    (L : SequentialSystem (CochainComplex A ℤ)) [HasColimit L] :
    CochainComplex A ℤ :=
  colimit L

theorem termwiseColimit_isDerivedColimit
    {A : Type u} [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A]
    [HasColimitsOfShape ℕ A] [HasExactColimitsOfShape ℕ A]
    [HasCountableCoproducts A] [CountableAB4 A]
    (L : SequentialSystem (CochainComplex A ℤ)) :
    IsDerivedColimit (derivedComplexSystem L)
      (DerivedCategory.Q.obj (termwiseColimitComplex L)) := by
  sorry

/-! ## Homological functors and compact objects -/

/-- A source-facing name for preservation of countable direct sums. -/
abbrev CommutesWithCountableDirectSums {D A : Type*}
    [Category* D] [Category* A] (H : D ⥤ A) : Prop :=
  PreservesColimitsOfShape (Discrete ℕ) H

theorem homologicalFunctor_derivedColimit_iso_colimit
    {D : Type u} [Category.{v} D] [AdditiveCategory D]
    [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive]
    [Pretriangulated D] [HasCountableCoproducts D]
    {A : Type u'} [Category.{v'} A] [Abelian A]
    [HasColimitsOfShape ℕ A] [HasExactColimitsOfShape ℕ A]
    [HasCountableCoproducts A]
    (H : D ⥤ A) [H.IsHomological]
    [PreservesColimitsOfShape (Discrete ℕ) H]
    {F : SequentialSystem D} {K : D}
    [HasCoproduct (fun n => F.obj n)]
    (p : DerivedColimitPresentation F K) :
    Nonempty (H.obj K ≅ colimit (F ⋙ H)) := by
  sorry

/-- The canonical coproduct comparison for a representable functor.  Being an
isomorphism is the categorical form of the source's bijection of Hom groups. -/
def IsCountablyCompact {D : Type u} [Category.{v} D]
    [AdditiveCategory D] [HasCountableCoproducts D] (K : D) : Prop :=
  ∀ E : ℕ → D,
    IsIso (sigmaComparison (preadditiveCoyoneda.obj (Opposite.op K)) E)

/-- The cocone of maps out of a compact object induced by a derived-colimit
presentation. -/
noncomputable def homColimitCocone
    {D : Type u} [Category.{v} D] [AdditiveCategory D]
    [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive]
    [Pretriangulated D]
    {F : SequentialSystem D} {L : D}
    [HasCoproduct (fun n => F.obj n)]
    (H : D ⥤ AddCommGrpCat)
    (p : DerivedColimitPresentation F L) : Cocone (F ⋙ H) :=
  { pt := H.obj L
    ι :=
      { app := fun n => H.map (p.ι n)
        naturality := by
          intro m n f
          dsimp
          simp only [Category.comp_id]
          simpa only [H.map_comp] using congrArg H.map (p.compatible f) } }

/-- The canonical map from the colimit of Hom groups to the Hom group of a
presented derived colimit. -/
noncomputable def compactHomColimitMap
    {D : Type u} [Category.{v} D] [AdditiveCategory D]
    [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive]
    [Pretriangulated D]
    {F : SequentialSystem D} {L K : D}
    [HasCoproduct (fun n => F.obj n)]
    (p : DerivedColimitPresentation F L) :
    colimit (F ⋙ preadditiveCoyoneda.obj (Opposite.op K)) ⟶
      (preadditiveCoyoneda.obj (Opposite.op K)).obj L :=
  colimit.desc (F ⋙ preadditiveCoyoneda.obj (Opposite.op K))
    (homColimitCocone (preadditiveCoyoneda.obj (Opposite.op K)) p)

theorem compact_hom_colimit_map_isIso
    {D : Type u} [Category.{v} D] [AdditiveCategory D]
    [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive]
    [Pretriangulated D] [HasCountableCoproducts D]
    {F : SequentialSystem D} {L K : D}
    [HasCoproduct (fun n => F.obj n)]
    (p : DerivedColimitPresentation F L)
    (hK : IsCountablyCompact K) :
    IsIso (compactHomColimitMap (D := D) (F := F) (L := L) (K := K) p) := by
  sorry

theorem compact_hom_colimit_map_bijective
    {D : Type u} [Category.{v} D] [AdditiveCategory D]
    [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive]
    [Pretriangulated D] [HasCountableCoproducts D]
    {F : SequentialSystem D} {L K : D}
    [HasCoproduct (fun n => F.obj n)]
    (p : DerivedColimitPresentation F L)
    (hK : IsCountablyCompact K) :
    Function.Bijective
      (compactHomColimitMap (D := D) (F := F) (L := L) (K := K) p) := by
  sorry

end Formalization.Books.Derived.Unit33
