import Formalization.Books.Duality.Unit01.TraceMaps

namespace Formalization.Books.Duality.Unit01

open CategoryTheory

universe u

noncomputable section

variable [SchemeDerivedContext Scheme] [SchemeDerivedOperations Scheme]

structure PullbackComparisonData {X Y : Scheme.{u}} (f : X ⟶ Y)
    (a : RightAdjointData f) where
  map : ∀ K : DerivedObject Y,
    Tensor ((LPullback f).obj K) (a.rightAdjoint.obj (StructureSheaf Y)) ⟶
      a.rightAdjoint.obj K
  isIso : ∀ K, IsIso (map K)

def CompareWithPullback {X Y : Scheme.{u}} (f : X ⟶ Y)
    (a : RightAdjointData f) (K : DerivedObject Y) : Prop :=
  ∃ c : Tensor ((LPullback f).obj K) (a.rightAdjoint.obj (StructureSheaf Y)) ⟶
      a.rightAdjoint.obj K, IsIso c

def equation_compare_with_pullback {X Y : Scheme.{u}} (f : X ⟶ Y)
    (a : RightAdjointData f) (K : DerivedObject Y) : Prop :=
  CompareWithPullback f a K

theorem lemma_compare_with_pullback_perfect {X Y : Scheme.{u}}
    (f : X ⟶ Y) (a : RightAdjointData f)
    (hperfect : Prop) : Nonempty (PullbackComparisonData f a) := by
  sorry

theorem lemma_restriction_compare_with_pullback {X Y : Scheme.{u}}
    (f : X ⟶ Y) (a : RightAdjointData f) (K : DerivedObject Y)
    (hrestriction : Prop) : CompareWithPullback f a K := by
  sorry

theorem lemma_compare_on_open {X Y : Scheme.{u}} (f : X ⟶ Y)
    (a : RightAdjointData f) (K : DerivedObject Y) (hopen : Prop) :
    CompareWithPullback f a K := by
  sorry

theorem lemma_transitivity_compare_with_pullback {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (a : RightAdjointData f)
    (b : RightAdjointData g) (hcomposition : Prop) :
    hcomposition →
      CompareWithPullback g b (StructureSheaf Z) →
        CompareWithPullback f a ((LPullback g).obj (StructureSheaf Z)) := by
  sorry

end

end Formalization.Books.Duality.Unit01
