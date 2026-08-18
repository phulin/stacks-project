import Formalization.Books.Duality.Unit01.EffectiveCartier

namespace Formalization.Books.Duality.Unit01

open CategoryTheory

universe u

noncomputable section

variable [SchemeDerivedContext Scheme] [SchemeDerivedOperations Scheme]

structure ProjectiveBundleDualizingData {X Y : Scheme.{u}} (f : X ⟶ Y)
    (a : RightAdjointData f) (n : ℕ) (L : DerivedObject Y) where
  dualizingObject : DerivedObject X
  comparison : Isomorphic dualizingObject (a.rightAdjoint.obj (StructureSheaf Y))

theorem lemma_upper_shriek_P1 {X Y : Scheme.{u}} (f : X ⟶ Y)
    (a : RightAdjointData f) (n : ℕ) (L : DerivedObject Y)
    (hprojective : Prop) : Nonempty (ProjectiveBundleDualizingData f a n L) := by
  sorry

structure BaseChangeFailure where
  square : CartesianSquare Scheme
  a : RightAdjointData square.f
  a' : RightAdjointData square.f'
  witness : ∃ K : DerivedObject square.Y,
    ∃ b : BaseChangeData square a a', ¬ IsIso (BaseChangeMap b K)

theorem example_base_change_wrong : Nonempty BaseChangeFailure := by
  sorry

structure RingedSpaceExtData (Y X : Type u) where
  normal : Type u
  ext : ℕ → Type u
  firstExt : Nonempty (normal ≃ ext 1)

theorem lemma_ext (Y X : Type u) (d : RingedSpaceExtData Y X) :
    Nonempty (d.normal ≃ d.ext 1) := by
  exact d.firstExt

structure RegularIdealExtData (Y X : Type u) where
  ext : ℕ → Type u
  exterior : ℕ → Type u
  comparison : ∀ i, Nonempty (exterior i ≃ ext i)

theorem lemma_regular_ideal_ext (Y X : Type u) (d : RegularIdealExtData Y X) :
    ∀ i, Nonempty (d.exterior i ≃ d.ext i) := by
  exact d.comparison

theorem lemma_regular_immersion_ext (Y X : Type u) (d : RegularIdealExtData Y X)
    (r : ℕ) : Nonempty (d.exterior r ≃ d.ext r) := by
  exact d.comparison r

structure SecondOrderThickeningData (Y X : Type u) where
  idealQuotient : Type u
  middle : Type u
  left : idealQuotient → middle
  right : middle → X
  ambient : Type u
  ambient_eq : ambient = Y
  exactness : Prop

def equation_second_order_thickening (Y X : Type u) : Prop :=
  Nonempty (SecondOrderThickeningData Y X)

theorem lemma_regular_immersion {X Y : Scheme.{u}} (i : X ⟶ Y)
    (a : RightAdjointData i) (r : ℕ) (normalDeterminant : DerivedObject X)
    (hregular : Prop) :
    Isomorphic (Shift normalDeterminant (-r))
      (a.rightAdjoint.obj (StructureSheaf Y)) := by
  sorry

theorem lemma_smooth_proper {X Y : Scheme.{u}} (f : X ⟶ Y)
    (a : RightAdjointData f) (d : ℕ) (canonicalBundle : DerivedObject X)
    (hsmoothProper : Prop) :
    Isomorphic (Shift canonicalBundle d)
      (a.rightAdjoint.obj (StructureSheaf Y)) := by
  sorry

end

end Formalization.Books.Duality.Unit01
