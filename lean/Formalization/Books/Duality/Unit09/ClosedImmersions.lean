import Formalization.Books.Duality.Unit08.CompareWithPullback

namespace Formalization.Books.Duality.Unit01

open CategoryTheory

universe u

noncomputable section

variable [SchemeDerivedContext Scheme] [SchemeDerivedOperations Scheme]

def ExactSupport {X Z : Scheme.{u}} (i : Z ⟶ X) (K : DerivedObject X) :=
  InternalHom ((RPushforward i).obj (StructureSheaf Z)) K

def ExactSupportOnSource {X Z : Scheme.{u}} (i : Z ⟶ X) (K : DerivedObject X) :
    DerivedObject Z :=
  InternalHom (StructureSheaf Z) ((LPullback i).obj K)

structure ExactSupportComparison {X Z : Scheme.{u}} (i : Z ⟶ X)
    (K : DerivedObject X) where
  object : DerivedObject X
  comparison : Nonempty (object ≅ ExactSupport i K)

theorem lemma_compute_sheaf_with_exact_support {X Z : Scheme.{u}}
    (i : Z ⟶ X) (K : DerivedObject X) (hi : Prop) :
    Nonempty (ExactSupportComparison i K) := by
  sorry

theorem lemma_sheaf_with_exact_support_adjoint {X Z : Scheme.{u}}
    (i : Z ⟶ X) (a : RightAdjointData i) (K : DerivedObject X) :
    Nonempty (ExactSupportComparison i K) := by
  sorry

theorem lemma_sheaf_with_exact_support_ext {X Z : Scheme.{u}}
    (i : Z ⟶ X) (K : DerivedObject X) (n : ℤ) :
    Nonempty (ExactSupportComparison i K) := by
  sorry

theorem lemma_sheaf_with_exact_support_internal_home {X Z : Scheme.{u}}
    (i : Z ⟶ X) (K L : DerivedObject X) :
    Nonempty (ExactSupportComparison i (InternalHom K L)) := by
  sorry

theorem lemma_sheaf_with_exact_support_quasi_coherent {X Z : Scheme.{u}}
    (i : Z ⟶ X) (K : DerivedObject X) (hK : IsQuasiCoherent K) :
    Nonempty (ExactSupportComparison i K) := by
  sorry

theorem lemma_sheaf_with_exact_support_coherent {X Z : Scheme.{u}}
    (i : Z ⟶ X) (K : DerivedObject X) (hK : IsCoherent K) :
    Nonempty (ExactSupportComparison i K) := by
  sorry

theorem lemma_twisted_inverse_image_closed {X Z : Scheme.{u}}
    (i : Z ⟶ X) (a : RightAdjointData i) (K : DerivedObject X) :
    Nonempty (ExactSupportComparison i K) := by
  sorry

def example_trace_closed_immersion {X Z : Scheme.{u}}
    (i : Z ⟶ X) (a : RightAdjointData i) (K : DerivedObject X) :
    (RPushforward i).obj (a.rightAdjoint.obj K) ⟶ K :=
  Trace a K

end

end Formalization.Books.Duality.Unit01
