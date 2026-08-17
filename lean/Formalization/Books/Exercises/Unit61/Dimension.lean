import Formalization.Books.Topology.Unit20.DimensionFunctions

import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Spectrum.Prime.Noetherian
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.Topology.KrullDimension
import Mathlib.Topology.Sober

/-!
# Exercises, Chapter 61: Dimension

The source's five-point diagram is encoded directly in the specialization
order.  Immediate specialization is reused from the earlier topology
chapter, and the dimension is Mathlib's topological Krull dimension.
-/

namespace Formalization.Books.Exercises.Unit61

open Set _root_.Topology TopologicalSpace
open Formalization.Books.Topology.Unit20

universe u v

noncomputable section

/-- The five-point specialization diagram from the source. -/
def HasFivePointSpecializationDiagram
    (X : Type u) [TopologicalSpace X] (x y z u v : X) : Prop :=
  x ≠ y ∧ x ≠ z ∧ x ≠ u ∧ x ≠ v ∧
    y ≠ z ∧ y ≠ u ∧ y ≠ v ∧
    z ≠ u ∧ z ≠ v ∧ u ≠ v ∧
    x ⤳ u ∧ x ⤳ y ∧ y ⤳ z ∧ v ⤳ u ∧ v ⤳ z

/-- The displayed diagram forces dimension at least two in a sober space. -/
theorem specialization_diagram_dimension_lower_bound
    {X : Type u} [TopologicalSpace X] [QuasiSober X] [T0Space X]
    {x y z u v : X}
    (hdiagram : HasFivePointSpecializationDiagram X x y z u v) :
    (2 : WithBot ℕ∞) ≤ topologicalKrullDim X := by
  sorry

/-- The lower bound is sharp: the diagram occurs in a sober space of
dimension two. -/
theorem exists_sober_specialization_diagram_dimension_two :
    ∃ (X : Type u) (inst : TopologicalSpace X),
      @QuasiSober X inst ∧ @T0Space X inst ∧
        ∃ x y z u v : X,
          @HasFivePointSpecializationDiagram X inst x y z u v ∧
            @topologicalKrullDim X inst = (2 : WithBot ℕ∞) := by
  sorry

/-- In the finite-type spectrum case, the last displayed specialization
cannot itself be immediate when the first branch `x ↝ u` is immediate. -/
theorem finite_type_spectrum_last_specialization_not_immediate
    {k : Type u} {A : Type v} [Field k] [CommRing A] [Algebra k A]
    [Algebra.FiniteType k A]
    {x y z u v : PrimeSpectrum A}
    (hdiagram : HasFivePointSpecializationDiagram (PrimeSpectrum A) x y z u v)
    (hxu : IsImmediateSpecialization x u) :
    ¬ IsImmediateSpecialization v z := by
  sorry

end

end Formalization.Books.Exercises.Unit61
