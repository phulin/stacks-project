import Formalization.Books.Duality.Unit01.ClosedImmersionBaseChange

namespace Formalization.Books.Duality.Unit01

open CategoryTheory
open AlgebraicGeometry

universe u

noncomputable section

variable [SchemeDerivedContext Scheme] [SchemeDerivedOperations Scheme]

def AffineSheafHom {X Y : Scheme.{u}} (f : X ⟶ Y) (K : DerivedObject Y) :
    DerivedObject X :=
  (LPullback f).obj (InternalHom ((RPushforward f).obj (StructureSheaf X)) K)

structure AffineSheafHomData {X Y : Scheme.{u}} (f : X ⟶ Y) where
  rightAdjoint : DerivedObject Y ⥤ DerivedObject X
  adjunction : Nonempty (Adjunction (RPushforward f) rightAdjoint)
  objectwise : ∀ K : DerivedObject Y,
    Isomorphic (rightAdjoint.obj K) (AffineSheafHom f K)

theorem lemma_compute_sheafhom_affine {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsAffineHom f] : Nonempty (AffineSheafHomData f) := by
  sorry

theorem lemma_sheafhom_affine_adjoint {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsAffineHom f] : Nonempty (RightAdjointData f) := by
  sorry

theorem lemma_sheafhom_affine_ext {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : DerivedObject Y) :
    AffineSheafHom f K =
      (LPullback f).obj (InternalHom ((RPushforward f).obj (StructureSheaf X)) K) := by
  rfl

def FiniteTwistedPreservesBoundedBelow {X Y : Scheme.{u}}
    (f : X ⟶ Y) (a : RightAdjointData f) : Prop :=
  ∀ K : DerivedObject Y, IsBoundedBelow K → IsBoundedBelow (a.rightAdjoint.obj K)

def FiniteTwistedAffineComparison {X Y : Scheme.{u}}
    (f : X ⟶ Y) (a : RightAdjointData f) : Prop :=
  ∀ K : DerivedObject Y, Isomorphic (a.rightAdjoint.obj K) (AffineSheafHom f K)

theorem lemma_finite_twisted {X Y : Scheme.{u}} (f : X ⟶ Y)
    (a : RightAdjointData f) (hfinite : IsFiniteMorphism f)
    (hpseudoCoherent : Prop) :
    FiniteTwistedPreservesBoundedBelow f a ∧ FiniteTwistedAffineComparison f a := by
  sorry

theorem remark_trace_map_finite {X Y : Scheme.{u}} (f : X ⟶ Y)
    (a : RightAdjointData f) (K : DerivedObject Y) :
    ∃ t : (RPushforward f).obj (a.rightAdjoint.obj K) ⟶ K, t = Trace a K := by
  sorry

end

end Formalization.Books.Duality.Unit01
