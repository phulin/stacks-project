import Formalization.Books.Duality.Unit16.UpperShriek

namespace Formalization.Books.Duality.Unit01

open CategoryTheory

universe u

noncomputable section

variable [SchemeDerivedContext Scheme] [SchemeDerivedOperations Scheme]

def UpperShriekRestrictsToPullback {X Y : Scheme.{u}} (f : X ⟶ Y)
    (a : RightAdjointData f) : Prop :=
  ∀ K : DerivedObject Y, Isomorphic ((LPullback f).obj K) (a.rightAdjoint.obj K)

def UpperShriekPreservesCoherent {X Y : Scheme.{u}} (f : X ⟶ Y)
    (a : RightAdjointData f) : Prop :=
  ∀ K : DerivedObject Y, IsCoherent K → IsCoherent (a.rightAdjoint.obj K)

def UpperShriekPreservesDualizing {X Y : Scheme.{u}} (f : X ⟶ Y)
    (a : RightAdjointData f) : Prop :=
  IsDualizingComplexOn (a.rightAdjoint.obj (StructureSheaf Y))

structure PerfectComparison {X Y : Scheme.{u}} (f : X ⟶ Y)
    (a : RightAdjointData f) where
  comparison : ∀ K : DerivedObject Y, IsPerfectObject K →
    Isomorphic ((LPullback f).obj K) (a.rightAdjoint.obj K)

def FlatShriekRelativelyPerfect {X Y : Scheme.{u}} (f : X ⟶ Y)
    (a : RightAdjointData f) : Prop :=
  IsPerfectObject (a.rightAdjoint.obj (StructureSheaf Y))

theorem lemma_shriek_open_immersion {X Y : Scheme.{u}} (f : X ⟶ Y)
    (a : RightAdjointData f) (hopen : IsOpenImmersionMorphism f) :
    UpperShriekRestrictsToPullback f a := by
  sorry

theorem lemma_restrict_before_or_after {X Y : Scheme.{u}} (f : X ⟶ Y)
    (a : RightAdjointData f) (hrestriction : Prop) : UpperShriekRestrictsToPullback f a := by
  sorry

theorem lemma_shriek_affine_line {X Y : Scheme.{u}} (f : X ⟶ Y)
    (a : RightAdjointData f) (K : DerivedObject Y) (hline : Prop) :
    Isomorphic (a.rightAdjoint.obj K)
      (Shift ((LPullback f).obj K) 1) := by
  sorry

theorem lemma_shriek_closed_immersion {X Y : Scheme.{u}} (f : X ⟶ Y)
    (a : RightAdjointData f) (hclosed : IsClosedImmersionMorphism f) :
    ∀ K : DerivedObject Y, Isomorphic (a.rightAdjoint.obj K) (ExactSupportOnSource f K) := by
  sorry

def RemarkLocalCalculationShriek {X Y : Scheme.{u}} (f : X ⟶ Y)
    (a : RightAdjointData f) : Prop :=
  UpperShriekPreservesCoherent f a

def remark_local_calculation_shriek {X Y : Scheme.{u}} (f : X ⟶ Y)
    (a : RightAdjointData f) : Prop :=
  RemarkLocalCalculationShriek f a

theorem lemma_shriek_coherent {X Y : Scheme.{u}} (f : X ⟶ Y)
    (a : RightAdjointData f) (hgeometry : Prop) : UpperShriekPreservesCoherent f a := by
  sorry

theorem lemma_shriek_dualizing {X Y : Scheme.{u}} (f : X ⟶ Y)
    (a : RightAdjointData f) (hgeometry : Prop) : UpperShriekPreservesDualizing f a := by
  sorry

theorem lemma_shriek_via_duality {X Y : Scheme.{u}} (f : X ⟶ Y)
    (a : RightAdjointData f) (K : DerivedObject Y)
    (ωY : DerivedObject Y) (ωX : DerivedObject X)
    (hωY : IsDualizingComplexOn ωY) (hωX : IsDualizingComplexOn ωX) :
    Isomorphic (a.rightAdjoint.obj K)
      (InternalHom ((LPullback f).obj (InternalHom K ωY)) ωX) := by
  sorry

theorem lemma_perfect_comparison_shriek {X Y : Scheme.{u}} (f : X ⟶ Y)
    (a : RightAdjointData f) (hperfect : IsPerfectProperMorphism f) :
    Nonempty (PerfectComparison f a) := by
  sorry

theorem lemma_flat_shriek_relatively_perfect {X Y : Scheme.{u}} (f : X ⟶ Y)
    (a : RightAdjointData f) (hflat : IsFlatMorphism f) : FlatShriekRelativelyPerfect f a := by
  sorry

theorem lemma_lci_shriek {X Y : Scheme.{u}} (f : X ⟶ Y)
    (a : RightAdjointData f) (hlci : Prop) :
    IsInvertibleObject (a.rightAdjoint.obj (StructureSheaf Y)) ∧
      (∀ K : DerivedObject Y, IsPerfectObject K →
        IsPerfectObject (a.rightAdjoint.obj K)) := by
  sorry

end

end Formalization.Books.Duality.Unit01
