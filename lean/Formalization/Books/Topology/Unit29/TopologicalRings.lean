import Formalization.Books.Topology.Unit29.TopologicalGroups
import Mathlib.Topology.Algebra.Ring.Basic
import Mathlib.Topology.Algebra.Ring.Ideal
import Mathlib.Topology.Category.TopCommRingCat

/-!
# Topology, Chapter 29: Topological rings

The source uses commutative rings with `1`.  Mathlib's `IsTopologicalRing` and
`TopCommRingCat` are therefore the canonical interfaces for the definitions and category
statements in this part of the chapter.
-/

namespace Formalization.Books.Topology.Unit29

open CategoryTheory CategoryTheory.Limits
open Set TopologicalSpace

universe u v

noncomputable section

section Basic

variable {R S : Type u}

/-- A bundled topological commutative ring from the unbundled data in the source definition. -/
def topologicalRingObject (R : Type u) [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] : TopCommRingCat.{u} :=
  TopCommRingCat.of R

/-- A homomorphism of topological rings, in the underlying form used by `TopCommRingCat`. -/
abbrev TopologicalRingHom [CommRing R] [CommRing S] [TopologicalSpace R] [TopologicalSpace S] :=
  { f : R →+* S // Continuous f }

/-- The quotient topology on the target of a ring homomorphism. -/
@[instance_reducible]
def quotientRingTopology [CommRing R] [CommRing S] [TopologicalSpace R]
    (f : R →+* S) : TopologicalSpace S :=
  TopologicalSpace.coinduced f inferInstance

/-- The additive group of a topological ring is a topological additive group. -/
theorem topologicalRing_additive_group [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] : IsTopologicalAddGroup R := by
  exact IsTopologicalRing.to_topologicalAddGroup

/-- A subring with its induced topology is a topological ring. -/
theorem topologicalRing_subring [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    (S : Subring R) : IsTopologicalRing S := by
  infer_instance

/-- A surjective ring quotient with its quotient topology is a topological ring. -/
theorem topologicalRing_surjective_quotient [CommRing R] [CommRing S] [TopologicalSpace R]
    [IsTopologicalRing R] (f : R →+* S) (hf : Function.Surjective f) :
    letI : TopologicalSpace S := quotientRingTopology f
    IsTopologicalRing S := by
  sorry

end Basic

section Category

theorem topological_rings_have_limits : HasLimits (TopCommRingCat.{u}) := by
  sorry

theorem topological_ring_limits_commute_with_topological_spaces :
    PreservesLimits (forget₂ TopCommRingCat.{u} TopCat.{u}) := by
  sorry

theorem topological_ring_limits_commute_with_commutative_rings :
    PreservesLimits (forget₂ TopCommRingCat.{u} CommRingCat.{u}) := by
  sorry

theorem topological_rings_have_colimits : HasColimits (TopCommRingCat.{u}) := by
  sorry

theorem topological_ring_colimits_commute_with_commutative_rings :
    PreservesColimits (forget₂ TopCommRingCat.{u} CommRingCat.{u}) := by
  sorry

end Category

end

end Formalization.Books.Topology.Unit29
