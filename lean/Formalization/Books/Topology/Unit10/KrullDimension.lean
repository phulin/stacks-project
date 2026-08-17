import Mathlib.Topology.KrullDimension
import Mathlib.Topology.Instances.Rat
import Mathlib.Topology.Order

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

/-- A chain of irreducible closed subsets of `X`. -/
abbrev IrreducibleClosedChain (X : Type u) [TopologicalSpace X] :=
  LTSeries (IrreducibleCloseds X)

/-- The length of a chain of irreducible closed subsets. -/
abbrev irreducibleClosedChainLength (C : IrreducibleClosedChain X) : ℕ :=
  C.length

theorem irreducibleClosedChain_term_isClosed_isIrreducible
    (C : IrreducibleClosedChain X) (i : Fin (C.length + 1)) :
    IsClosed (C i : Set X) ∧ IsIrreducible (C i : Set X) := by
  exact ⟨(C i).isClosed, (C i).isIrreducible⟩

theorem irreducibleClosedChain_adjacent_strict
    (C : IrreducibleClosedChain X) (i : Fin C.length) :
    C (Fin.castSucc i) < C i.succ := by
  exact C.step i

/-- The source's Krull dimension, with Mathlib's `WithBot ℕ∞` value type. -/
noncomputable abbrev krullDimension (X : Type u) [TopologicalSpace X] : WithBot ℕ∞ :=
  topologicalKrullDim X

theorem krullDimension_eq_iSup_chainLength :
    krullDimension X =
      ⨆ C : IrreducibleClosedChain X, (C.length : WithBot ℕ∞) := by
  rfl

theorem krullDimension_eq_bot_iff :
    krullDimension X = ⊥ ↔ IsEmpty X := by
  sorry

/-! ### Dimension at a point -/

/-- The type of open neighbourhoods of a point. -/
abbrev KrullOpenNeighborhood (x : X) :=
  {U : Set X // IsOpen U ∧ x ∈ U}

/-- The Krull dimension of `X` at `x`, as the infimum over open neighbourhoods. -/
noncomputable def krullDimensionAt (x : X) : WithBot ℕ∞ :=
  ⨅ U : KrullOpenNeighborhood x, krullDimension (U : Set X)

theorem krullDimensionAt_le (x : X) {U : Set X} (hU : IsOpen U) (hx : x ∈ U) :
    krullDimensionAt x ≤ krullDimension U := by
  change (⨅ V : KrullOpenNeighborhood x, krullDimension (V : Set X)) ≤
    krullDimension U
  exact iInf_le (fun V : KrullOpenNeighborhood x => krullDimension (V : Set X))
    (⟨U, hU, hx⟩ : KrullOpenNeighborhood x)

theorem krullDimensionAt_isLeast (x : X) :
    IsLeast
      {d : WithBot ℕ∞ |
        ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ krullDimension U = d}
      (krullDimensionAt x) := by
  sorry

theorem krullDimension_mono_of_open_subset
    {U' U : Set X} (hU' : IsOpen U') (hU : IsOpen U) (hsub : U' ⊆ U) :
    krullDimension U' ≤ krullDimension U := by
  sorry

theorem krullDimensionAt_hasBasis (x : X) :
    (𝓝 x).HasBasis
      (fun U : Set X =>
        IsOpen U ∧ x ∈ U ∧ krullDimension U = krullDimensionAt x)
      (fun U => U) := by
  sorry

/-! ### Local and global dimensions -/

theorem krullDimension_eq_iSup_krullDimensionAt :
    krullDimension X = ⨆ x : X, krullDimensionAt x := by
  sorry

/-! ### Examples -/

/-- `Fin n → ℝ` is the usual coordinate model of Euclidean `n`-space. -/
theorem krullDimension_euclideanSpace (n : ℕ) :
    krullDimension (Fin n → ℝ) = 0 := by
  sorry

/- The following topology has open sets `∅`, `{generic}`, and the whole
   space.  The constructors correspond to the source's `s` and `η`. -/
inductive KrullTwoPointSpace where
  | special
  | generic

def krullTwoPointOpenBasis : Set (Set KrullTwoPointSpace) :=
  {({KrullTwoPointSpace.generic} : Set KrullTwoPointSpace)}

@[instance_reducible]
def krullTwoPointTopology : TopologicalSpace KrullTwoPointSpace :=
  TopologicalSpace.generateFrom krullTwoPointOpenBasis

instance krullTwoPointSpace_topologicalSpace :
    TopologicalSpace KrullTwoPointSpace :=
  krullTwoPointTopology

theorem krullTwoPointSpace_isOpen_iff {U : Set KrullTwoPointSpace} :
    IsOpen U ↔
      U = ∅ ∨ U = {KrullTwoPointSpace.generic} ∨ U = Set.univ := by
  sorry

theorem krullDimension_twoPointSpace_maximal_chain :
    ∃ C : IrreducibleClosedChain KrullTwoPointSpace,
      C.length = 1 ∧
        (C.head : Set KrullTwoPointSpace) = {KrullTwoPointSpace.special} ∧
        (C.last : Set KrullTwoPointSpace) = Set.univ ∧
        (C.length : WithBot ℕ∞) = krullDimension KrullTwoPointSpace := by
  sorry

theorem krullDimension_twoPointSpace :
    krullDimension KrullTwoPointSpace = 1 := by
  sorry

/-- The finite-chain generalization of the two-point example. -/
@[instance_reducible]
def krullFiniteChainTopology (n : ℕ) : TopologicalSpace (Fin (n + 1)) :=
  TopologicalSpace.generateFrom
    (Set.range (fun i : Fin (n + 1) => Set.Ici i))

abbrev KrullFiniteChainSpace (n : ℕ) :=
  WithTopology (Fin (n + 1)) (krullFiniteChainTopology n)

theorem krullDimension_finiteChain (n : ℕ) :
    krullDimension (KrullFiniteChainSpace n) = n := by
  sorry

/-! ### Equidimensional spaces -/

/-- Every irreducible component of `X` has the same Krull dimension. -/
def Equidimensional : Prop :=
  ∃ d : WithBot ℕ∞,
    ∀ C ∈ irreducibleComponents X, krullDimension C = d

end KrullDimension

end Formalization.Books.Topology.Unit10
