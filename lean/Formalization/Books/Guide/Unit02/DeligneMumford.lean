import Mathlib.Topology.Irreducible

/-!
# A Guide to the Literature, Chapter 2: Deligne--Mumford

The source's remarks about foundational results being given without proof and
about two proofs of irreducibility are bibliographic and proof-narrative
remarks; the mathematical assertion itself is recorded below.
-/

namespace Formalization.Books.Guide.Unit02

universe u

/-! ## Irreducibility of the moduli space of curves -/

/-- A presentation-level carrier for the moduli space of curves of a fixed
genus.  The topology is kept explicit because the current project does not
provide the moduli space itself. -/
structure ModuliSpaceOfCurves (g : ℕ) where
  carrier : Type u
  topology : TopologicalSpace carrier
  isModuliSpace : Prop

/-- Irreducibility of a chosen moduli-space presentation. -/
def IsIrreducibleModuliSpace {g : ℕ} (M : ModuliSpaceOfCurves.{u} g) : Prop :=
  @IrreducibleSpace M.carrier M.topology

/-- Deligne--Mumford's irreducibility assertion for the moduli space of
curves of any given genus.  The proof is deferred to the proving stage. -/
theorem moduliSpaceOfCurves_isIrreducible (g : ℕ)
    (M : ModuliSpaceOfCurves.{u} g) (hM : M.isModuliSpace) :
    IsIrreducibleModuliSpace M := by
  sorry

end Formalization.Books.Guide.Unit02
