import Formalization.Books.Duality.Unit01.FiniteMorphisms

namespace Formalization.Books.Duality.Unit01

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

universe u

noncomputable section

variable [SchemeDerivedContext Scheme] [SchemeDerivedOperations Scheme]

def CommutesWithDirectSums {X Y : Scheme.{u}} {f : X ⟶ Y}
    (a : RightAdjointData f) : Prop :=
  ∀ K : ℕ → DerivedObject Y,
    Isomorphic (a.rightAdjoint.obj (DirectSum K))
      (DirectSum (fun n => a.rightAdjoint.obj (K n)))

structure SupportPullbackData {X Y : Scheme.{u}} (f : X ⟶ Y) where
  preimage : SchemeDerivedContext.supportLabel Y → SchemeDerivedContext.supportLabel X

def SupportedOnPreimage {X Y : Scheme.{u}} (f : X ⟶ Y)
    (a : RightAdjointData f) (s : SupportPullbackData f) : Prop :=
  ∀ (T : SchemeDerivedContext.supportLabel Y) (K : DerivedObject Y),
    IsSupportedOn T K → IsSupportedOn (s.preimage T) (a.rightAdjoint.obj K)

structure ProperFlatRelativeData {X Y : Scheme.{u}} (f : X ⟶ Y)
    (a : RightAdjointData f) where
  support : SupportPullbackData f
  supportedOnPreimage : SupportedOnPreimage f a support
  restrictionProperty : Prop
  compareWithPullback : ∀ K : DerivedObject Y, CompareWithPullback f a K

def IsProperFlatFinitePresentation {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop :=
  IsProperMorphism f ∧ IsFlatMorphism f ∧ IsFinitePresentationMorphism f

theorem lemma_proper_flat {X Y : Scheme.{u}} (f : X ⟶ Y)
    (a : RightAdjointData f) (hgeometry : IsProperFlatFinitePresentation f) :
    CommutesWithDirectSums a := by
  sorry

theorem lemma_proper_flat_relative {X Y : Scheme.{u}} (f : X ⟶ Y)
    (a : RightAdjointData f) (hgeometry : IsProperFlatFinitePresentation f) :
    Nonempty (ProperFlatRelativeData f a) := by
  sorry

theorem lemma_compare_with_pullback_flat_proper {X Y : Scheme.{u}}
    (f : X ⟶ Y) (a : RightAdjointData f)
    (hgeometry : IsProperFlatFinitePresentation f) :
    ∀ K : DerivedObject Y, CompareWithPullback f a K := by
  sorry

theorem lemma_proper_flat_base_change {S X Y : Scheme.{u}}
    (square : CartesianSquare Scheme) (a : RightAdjointData square.f)
    (a' : RightAdjointData square.f')
    (hgeometry : IsProperFlatFinitePresentation square.f)
    (b : BaseChangeData square a a') : IsIsoBaseChange b := by
  sorry

def RelativeDualizingComplex {X Y : Scheme.{u}} (f : X ⟶ Y)
    (a : RightAdjointData f) : DerivedObject X :=
  a.rightAdjoint.obj (StructureSheaf Y)

structure RelativeCupProductData {X Y : Scheme.{u}} (f : X ⟶ Y)
    (a : RightAdjointData f) where
  K : DerivedObject X
  M : DerivedObject X
  pseudoCoherentM : SchemeDerivedContext.isPseudoCoherent X M
  dualityMap : Tensor K M ⟶ RelativeDualizingComplex f a
  internalHomComparison : Isomorphic K (InternalHom M (RelativeDualizingComplex f a))
  inducedDuality : Isomorphic ((RPushforward f).obj K)
    (InternalHom ((RPushforward f).obj M) (StructureSheaf Y))

structure RelativeDualizingProperties {X Y : Scheme.{u}} (f : X ⟶ Y)
    (a : RightAdjointData f) where
  relativelyPerfect : IsPerfectObject (RelativeDualizingComplex f a)
  positiveCohomologyVanishing : Prop
  selfDual : Isomorphic (StructureSheaf X)
    (InternalHom (RelativeDualizingComplex f a) (RelativeDualizingComplex f a))

theorem remark_relative_dualizing_complex {X Y : Scheme.{u}} (f : X ⟶ Y)
    (a : RightAdjointData f) :
    RelativeDualizingComplex f a = a.rightAdjoint.obj (StructureSheaf Y) := by
  rfl

theorem remark_relative_dualizing_complex_relative_cup_product
    {X Y : Scheme.{u}} (f : X ⟶ Y) (a : RightAdjointData f)
    (d : RelativeCupProductData f a) : Nonempty (RelativeCupProductData f a) := by
  exact ⟨d⟩

theorem lemma_properties_relative_dualizing {X Y : Scheme.{u}} (f : X ⟶ Y)
    (a : RightAdjointData f) (hgeometry : IsProperFlatFinitePresentation f)
    : Nonempty (RelativeDualizingProperties f a) := by
  sorry

structure RigidityData {X Y : Scheme.{u}} (f : X ⟶ Y)
    (a : RightAdjointData f) where
  preRigid : Isomorphic (StructureSheaf X) (StructureSheaf X)
  rigid : Isomorphic (RelativeDualizingComplex f a) (RelativeDualizingComplex f a)

def equation_pre_rigid {X Y : Scheme.{u}} (f : X ⟶ Y)
    (_a : RightAdjointData f) : Prop :=
  Isomorphic (StructureSheaf X) (StructureSheaf X)

def equation_rigid {X Y : Scheme.{u}} (f : X ⟶ Y)
    (a : RightAdjointData f) : Prop :=
  Isomorphic (RelativeDualizingComplex f a) (RelativeDualizingComplex f a)

theorem lemma_van_den_bergh {X Y : Scheme.{u}} (f : X ⟶ Y)
    (a : RightAdjointData f) (hgeometry : IsProperFlatFinitePresentation f)
    : Nonempty (RigidityData f a) := by
  sorry

def remark_van_den_bergh {X Y : Scheme.{u}} (f : X ⟶ Y)
    (a : RightAdjointData f) : Prop :=
  Nonempty (RigidityData f a)

end

end Formalization.Books.Duality.Unit01
