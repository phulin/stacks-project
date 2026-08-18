import Formalization.Books.Duality.Unit27.ProperOverFields

namespace Formalization.Books.Duality.Unit01

open CategoryTheory

universe u

noncomputable section

variable [SchemeDerivedContext Scheme] [SchemeDerivedOperations Scheme]

def relative_dualizing_complex {X Y : Scheme.{u}} (f : X ⟶ Y)
    (a : RightAdjointData f) : DerivedObject X :=
  RelativeDualizingComplex f a

def definition_relative_dualizing_complex {X Y : Scheme.{u}} (f : X ⟶ Y)
    (a : RightAdjointData f) : DerivedObject X :=
  relative_dualizing_complex f a

structure RelativeDualizingAlgebraData {X Y : Scheme.{u}} (f : X ⟶ Y)
    (a : RightAdjointData f) where
  complex : DerivedObject X
  comparison : Isomorphic complex (relative_dualizing_complex f a)
  algebraStructure : Prop

theorem lemma_relative_dualizing_complex_algebra {X Y : Scheme.{u}}
    (f : X ⟶ Y) (a : RightAdjointData f) :
    Nonempty (RelativeDualizingAlgebraData f a) := by
  sorry

theorem lemma_relative_dualizing_RHom {X Y : Scheme.{u}} (f : X ⟶ Y)
    (a : RightAdjointData f) (K M : DerivedObject X)
    (hM : IsPseudoCoherent M) :
    Isomorphic K (InternalHom M (relative_dualizing_complex f a)) := by
  sorry

theorem lemma_uniqueness_relative_dualizing {X Y : Scheme.{u}}
    (f : X ⟶ Y) (a : RightAdjointData f)
    (d d' : RelativeDualizingAlgebraData f a) :
    Isomorphic d.complex d'.complex := by
  sorry

theorem lemma_existence_relative_dualizing {X Y : Scheme.{u}}
    (f : X ⟶ Y) (a : RightAdjointData f) :
    Nonempty (RelativeDualizingAlgebraData f a) := by
  exact lemma_relative_dualizing_complex_algebra f a

theorem lemma_base_change_relative_dualizing {S X Y : Scheme.{u}}
    (square : CartesianSquare Scheme) (a : RightAdjointData square.f)
    (a' : RightAdjointData square.f') (b : BaseChangeData square a a') :
    IsIsoBaseChange b := by
  sorry

theorem lemma_flat_proper_relative_dualizing {X Y : Scheme.{u}}
    (f : X ⟶ Y) (a : RightAdjointData f)
    (hgeometry : IsProperFlatFinitePresentation f) :
    Nonempty (RelativeDualizingAlgebraData f a) := by
  sorry

def remark_relative_dualizing_complex_bis {X Y : Scheme.{u}}
    (f : X ⟶ Y) (a : RightAdjointData f) : Prop :=
  IsDualizingComplexOn (relative_dualizing_complex f a)

theorem lemma_compactifyable_relative_dualizing {X Y : Scheme.{u}}
    (f : X ⟶ Y) (a : RightAdjointData f) (hcompactifyable : Prop) :
    Nonempty (RelativeDualizingAlgebraData f a) := by
  sorry

theorem lemma_relative_dualizing_composition {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (a : RightAdjointData f)
    (b : RightAdjointData g) (c : RightAdjointData (f ≫ g)) :
    Isomorphic (relative_dualizing_complex (f ≫ g)
      c) (relative_dualizing_complex f a) := by
  sorry

end

end Formalization.Books.Duality.Unit01
