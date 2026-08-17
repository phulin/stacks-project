import Mathlib.SetTheory.ZFC.Basic
import Mathlib.AlgebraicGeometry.Scheme

/-!
# Set Theory, Chapter 1: Introduction

The introductory source section uses the standard set-theoretic encodings of
topological spaces and ordered pairs to explain how mathematical structures
can be described in ZFC.  Mathlib already supplies the canonical bundled
interfaces for topological spaces, ringed spaces, locally ringed spaces, and
schemes, so this file does not duplicate those definitions.  The set-coded
predicates below record the missing set-theoretic interfaces.
-/

universe u

open scoped ZFSet

namespace Formalization.Books.Sets.Unit01

/-!
The imported declarations are the source-faithful interfaces for the
geometric terminology:

* `TopologicalSpace X` is a topology on the type `X`;
* `AlgebraicGeometry.RingedSpace` is a sheafed topological space of
  commutative rings;
* `AlgebraicGeometry.LocallyRingedSpace` adds locality of every stalk; and
* `AlgebraicGeometry.Scheme` extends a locally ringed space with local affine
  presentations.

In particular, the source's definitions of scheme, locally ringed space,
ringed space, and topological space are already represented by these
canonical declarations.

The source's final observation that the property of being a scheme can be
expressed by a complete set-theoretic formula is a metamathematical statement
about the syntax of first-order set theory, rather than a concrete formula or
theorem in this chapter; it therefore needs no additional Lean declaration.
-/

/-- A ZF set has the Kuratowski ordered-pair form. -/
def IsOrderedPair (S : ZFSet.{u}) : Prop :=
  ∃ a b : ZFSet.{u}, S = ZFSet.pair a b

/--
`d` is a collection of subsets of `c` satisfying the topology axioms.

The last clause quantifies over arbitrary ZF-set-indexed subcollections of
`d`, so it is the set-theoretic version of closure under arbitrary unions.
-/
def IsTopologyOn (c d : ZFSet.{u}) : Prop :=
  d ⊆ ZFSet.powerset c ∧
    ∅ ∈ d ∧
    c ∈ d ∧
    (∀ U ∈ d, ∀ V ∈ d, U ∩ V ∈ d) ∧
    (∀ A : ZFSet.{u}, A ⊆ d → ⋃₀ A ∈ d)

/-- A ZF set encodes a topological space as its carrier and open-set family. -/
def IsTopologicalSpaceEncoding (S : ZFSet.{u}) : Prop :=
  ∃ c d : ZFSet.{u}, S = ZFSet.pair c d ∧ IsTopologyOn c d

end Formalization.Books.Sets.Unit01
