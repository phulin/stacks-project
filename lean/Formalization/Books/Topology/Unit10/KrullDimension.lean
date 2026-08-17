import Mathlib.Topology.KrullDimension
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.Sets.Opens
import Mathlib.Topology.WithTopology

/-!
# Topology, Chapter 10: Krull dimension

The source's chains of irreducible closed subsets are represented by
Mathlib's `IrreducibleCloseds` and `LTSeries` types.  The global dimension is
Mathlib's canonical `topologicalKrullDim`; the local dimension is the
infimum of the dimensions of the open neighbourhood subspaces.
-/

namespace Formalization.Books.Topology.Unit10

open Set Function _root_.Topology TopologicalSpace

universe u v

section KrullDimension

variable {X : Type u} [TopologicalSpace X]

/-! ### Chains and global dimension -/

theorem irreducibleClosedChain_term_isClosed_isIrreducible
    (C : LTSeries (IrreducibleCloseds X)) (i : Fin (C.length + 1)) :
    IsClosed (C i : Set X) ∧ IsIrreducible (C i : Set X) := by
  exact ⟨(C i).isClosed, (C i).isIrreducible⟩

theorem irreducibleClosedChain_adjacent_strict
    (C : LTSeries (IrreducibleCloseds X)) (i : Fin C.length) :
    C (Fin.castSucc i) < C i.succ := by
  exact C.step i

theorem krullDimension_eq_iSup_chainLength :
    topologicalKrullDim X =
      ⨆ C : LTSeries (IrreducibleCloseds X), (C.length : WithBot ℕ∞) := by
  rfl

theorem krullDimension_eq_bot_iff :
    topologicalKrullDim X = ⊥ ↔ IsEmpty X := by
  sorry

/-! ### Dimension at a point -/

/-- The Krull dimension of `X` at `x`, as the infimum over open neighbourhoods. -/
noncomputable def krullDimensionAt (x : X) : WithBot ℕ∞ :=
  ⨅ U : OpenNhdsOf x, topologicalKrullDim (U : Set X)

theorem krullDimensionAt_le (x : X) {U : Set X} (hU : IsOpen U) (hx : x ∈ U) :
    krullDimensionAt x ≤ topologicalKrullDim U := by
  change (⨅ V : OpenNhdsOf x, topologicalKrullDim (V : Set X)) ≤
    topologicalKrullDim U
  exact iInf_le (fun V : OpenNhdsOf x => topologicalKrullDim (V : Set X))
    (⟨⟨U, hU⟩, hx⟩ : OpenNhdsOf x)

theorem krullDimension_mono_of_open_subset
    {U' U : Set X} (hU' : IsOpen U') (hU : IsOpen U) (hsub : U' ⊆ U) :
    topologicalKrullDim U' ≤ topologicalKrullDim U := by
  sorry

theorem krullDimensionAt_isLeast (x : X) :
    IsLeast
      {d : WithBot ℕ∞ |
        ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ topologicalKrullDim U = d}
      (krullDimensionAt x) := by
  sorry

theorem krullDimensionAt_hasBasis (x : X) :
    (𝓝 x).HasBasis
      (fun U : Set X =>
        IsOpen U ∧ x ∈ U ∧ topologicalKrullDim U = krullDimensionAt x)
      (fun U => U) := by
  sorry

/-! ### Local and global dimensions -/

theorem krullDimension_eq_iSup_krullDimensionAt :
    topologicalKrullDim X = ⨆ x : X, krullDimensionAt x := by
  sorry

/-! ### Examples -/

/-- `Fin n → ℝ` is the usual coordinate model of Euclidean `n`-space. -/
theorem krullDimension_euclideanSpace (n : ℕ) :
    topologicalKrullDim (Fin n → ℝ) = 0 := by
  sorry

/- The following topology has open sets `∅`, `{generic}`, and the whole
   space.  The constructors correspond to the source's `s` and `η`. -/
inductive KrullTwoPointSpace where
  | special
  | generic

def krullTwoPointOpenGenerators : Set (Set KrullTwoPointSpace) :=
  {({KrullTwoPointSpace.generic} : Set KrullTwoPointSpace)}

@[instance_reducible]
def krullTwoPointTopology : TopologicalSpace KrullTwoPointSpace :=
  TopologicalSpace.generateFrom krullTwoPointOpenGenerators

instance krullTwoPointSpace_topologicalSpace :
    TopologicalSpace KrullTwoPointSpace :=
  krullTwoPointTopology

theorem krullTwoPointSpace_isOpen_iff {U : Set KrullTwoPointSpace} :
    IsOpen U ↔
      U = ∅ ∨ U = {KrullTwoPointSpace.generic} ∨ U = Set.univ := by
  sorry

theorem krullDimension_twoPointSpace_maximal_chain :
    ∃ C : LTSeries (IrreducibleCloseds KrullTwoPointSpace),
      C.length = 1 ∧
        (C.head : Set KrullTwoPointSpace) = {KrullTwoPointSpace.special} ∧
        (C.last : Set KrullTwoPointSpace) = Set.univ ∧
        (C.length : WithBot ℕ∞) = topologicalKrullDim KrullTwoPointSpace := by
  sorry

theorem krullDimension_twoPointSpace :
    topologicalKrullDim KrullTwoPointSpace = 1 := by
  sorry

/-- The finite-chain generalization of the two-point example. -/
@[instance_reducible]
def krullFiniteChainTopology (n : ℕ) : TopologicalSpace (Fin (n + 1)) :=
  TopologicalSpace.generateFrom
    (Set.range (fun i : Fin (n + 1) => Set.Ici i))

abbrev KrullFiniteChainSpace (n : ℕ) :=
  WithTopology (Fin (n + 1)) (krullFiniteChainTopology n)

theorem krullDimension_finiteChain (n : ℕ) :
    topologicalKrullDim (KrullFiniteChainSpace n) = n := by
  sorry

/-! ### Equidimensional spaces -/

/-- Every irreducible component of `X` has the same Krull dimension. -/
def Equidimensional : Prop :=
  ∃ d : WithBot ℕ∞,
    ∀ C ∈ irreducibleComponents X, topologicalKrullDim C = d

end KrullDimension

end Formalization.Books.Topology.Unit10
