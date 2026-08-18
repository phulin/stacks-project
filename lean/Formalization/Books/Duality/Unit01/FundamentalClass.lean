import Formalization.Books.Duality.Unit01.RelativeDualizingComplexes

namespace Formalization.Books.Duality.Unit01

open CategoryTheory

universe u

noncomputable section

variable [SchemeDerivedContext Scheme] [SchemeDerivedOperations Scheme]

structure DeterminantData {X Y : Scheme.{u}} (f : X ⟶ Y) where
  determinant : DerivedObject X
  rank : ℕ
  invertible : IsInvertibleObject determinant

structure FundamentalClassData {X Y : Scheme.{u}} (f : X ⟶ Y)
    (a : RightAdjointData f) where
  determinantData : DeterminantData f
  classMap : determinantData.determinant ⟶ a.rightAdjoint.obj (StructureSheaf Y)
  isomorphism : Isomorphic determinantData.determinant
    (a.rightAdjoint.obj (StructureSheaf Y))

theorem lemma_determinant {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hperfect : IsPerfectProperMorphism f) : Nonempty (DeterminantData f) := by
  sorry

theorem lemma_fundamental_class_lci {X Y : Scheme.{u}} (f : X ⟶ Y)
    (a : RightAdjointData f) (hlci : Prop) : Nonempty (FundamentalClassData f a) := by
  sorry

theorem lemma_fundamental_class_almost_lci {X Y : Scheme.{u}} (f : X ⟶ Y)
    (a : RightAdjointData f) (halmostLci : Prop) : Nonempty (FundamentalClassData f a) := by
  sorry

end

end Formalization.Books.Duality.Unit01
