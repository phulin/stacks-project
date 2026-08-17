import Mathlib.Topology.Irreducible

/-!
# A Guide to the Literature, Chapter 2: Deligne--Mumford

The source's remarks about foundational results being given without proof and
about two proofs of irreducibility are bibliographic and proof-narrative
remarks.  The project does not yet provide the moduli space of curves or the
geometric results needed to identify an arbitrary presentation with it, so
the irreducibility assertion is not stated as a theorem here.
-/

namespace Formalization.Books.Guide.Unit02

universe u

/-! ## Irreducibility of the moduli space of curves -/

/-- A presentation-level topological carrier for the moduli space of curves of
a fixed genus.  The topology is kept explicit because the current project
does not provide the moduli space itself. -/
structure ModuliSpaceOfCurves (g : ℕ) where
  carrier : Type u
  topology : TopologicalSpace carrier

/-- Irreducibility of a chosen moduli-space presentation. -/
def IsIrreducibleModuliSpace {g : ℕ} (M : ModuliSpaceOfCurves.{u} g) : Prop :=
  @IrreducibleSpace M.carrier M.topology

end Formalization.Books.Guide.Unit02
