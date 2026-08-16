import Mathlib.AlgebraicGeometry.Geometrically.Reduced
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.Topology.Constructible

-- The declarations below use the canonical scheme-theoretic fibre API.

namespace AlgebraicGeometry

open CategoryTheory Limits TopologicalSpace Topology

universe u

variable {X Y : Scheme.{u}}

/-- The set of points of the base whose scheme-theoretic fibres are geometrically reduced. -/
def geometricallyReducedFiberLocus (f : X ⟶ Y) : Set Y :=
  {y | GeometricallyReduced (f.fiberToSpecResidueField y)}

/-!
The source's “finite type” hypotheses are expressed using Mathlib's canonical
factorization into `LocallyOfFiniteType` and `QuasiCompact`.
-/

/- The generic nonreduced fibre persists on a nonempty open neighbourhood. -/
lemma nonreduced_in_neighbourhood (f : X ⟶ Y) [IrreducibleSpace Y]
    [LocallyOfFiniteType f] [QuasiCompact f]
    (hη : ¬ IsReduced (f.fiber (genericPoint Y))) :
    ∃ V : Y.Opens, V ≠ ⊥ ∧ ∀ (y : Y), y ∈ V → ¬ IsReduced (f.fiber y) := by
  sorry

/- Base change preserves the geometrically reduced fibre locus. -/
lemma base_change_fibres_geometrically_reduced (f : X ⟶ Y) {Y' : Scheme.{u}}
    (g : Y' ⟶ Y) :
    geometricallyReducedFiberLocus (pullback.snd f g) =
      g ⁻¹' geometricallyReducedFiberLocus f := by
  sorry

/- The failure of geometric reducedness at the generic fibre persists on a nonempty open. -/
lemma not_geometrically_reduced_in_neighbourhood (f : X ⟶ Y)
    [IrreducibleSpace Y] [LocallyOfFiniteType f] [QuasiCompact f]
    (hη : ¬ GeometricallyReduced (f.fiberToSpecResidueField (genericPoint Y))) :
    ∃ V : Y.Opens, V ≠ ⊥ ∧
      ∀ (y : Y), y ∈ V → ¬ GeometricallyReduced (f.fiberToSpecResidueField y) := by
  sorry

/- A geometrically reduced generic fibre spreads to a nonempty open. -/
lemma geometrically_reduced_generic_fibre (f : X ⟶ Y) [IrreducibleSpace Y]
    [LocallyOfFiniteType f] [QuasiCompact f]
    (hη : GeometricallyReduced (f.fiberToSpecResidueField (genericPoint Y))) :
    ∃ V : Y.Opens, V ≠ ⊥ ∧ GeometricallyReduced (f ∣_ V) := by
  sorry

/- The geometrically reduced fibre locus is locally constructible for the stated finiteness
   hypotheses. -/
lemma geometrically_reduced_constructible (f : X ⟶ Y)
    [QuasiCompact f] [LocallyOfFinitePresentation f] :
    IsLocallyConstructible (geometricallyReducedFiberLocus f) := by
  sorry

/- The source notes that the dominance hypothesis below is automatic for a flat morphism. -/
lemma flat_irreducible_components_dominate
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (f : X ⟶ Spec (.of R)) [Flat f] :
    ∀ C ∈ irreducibleComponents X, Dense (f '' C) := by
  sorry

/- A proper morphism over a DVR with reduced special fibre is reduced, as is its generic fibre,
   provided every irreducible component dominates the base. -/
lemma proper_flat_over_dvr_reduced_fibre
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (f : X ⟶ Spec (.of R)) [IsProper f]
    (hdom : ∀ C ∈ irreducibleComponents X, Dense (f '' C))
    (hs : IsReduced (f.fiber (IsLocalRing.closedPoint R))) :
    IsReduced X ∧ IsReduced (f.fiber (genericPoint (Spec (.of R)))) := by
  sorry

/- For a flat proper morphism of finite presentation, the geometrically reduced fibre locus is
   open. -/
lemma geometrically_reduced_open (f : X ⟶ Y) [Flat f] [IsProper f]
    [LocallyOfFinitePresentation f] :
    IsOpen (geometricallyReducedFiberLocus f) := by
  sorry

end AlgebraicGeometry
