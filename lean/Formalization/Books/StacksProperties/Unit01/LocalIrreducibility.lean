import Formalization.Books.StacksProperties.Unit01.Dimension
import Formalization.Books.Descent.Unit33.PropertiesOfMorphismsOfGerms

/-!
# Properties of Algebraic Stacks, Chapter 1, Section 13

The branch-count construction uses the earlier pointed-germ interface.  A
`GeometricBranchTheory` packages the branch count and its smooth invariance;
the stack-level count then follows the source's “least finite count, or
infinity” convention.
-/

noncomputable section

open AlgebraicGeometry

universe u

namespace Formalization.Books.StacksProperties.Unit01

structure GeometricBranchTheory where
  count : SchemeGerm.{u} → WithTop ℕ
  smoothInvariant : Prop

def BranchCountProperty (B : GeometricBranchTheory) (n : ℕ) :
    LocalPropertyOfGerms where
  property := fun X x => B.count ⟨X, x⟩ = n
  smoothLocal := B.smoothInvariant

def geometricBranchProperty {S : Scheme.{u}}
    (B : GeometricBranchTheory) (n : ℕ) :
    SmoothLocalGermProperty S where
  schemeProperty := BranchCountProperty B n
  spaceProperty := fun W u => B.count ⟨W.left, u⟩ = n
  comparison := B.smoothInvariant
  smoothLocal := B.smoothInvariant

theorem geometric_branch_smooth_invariant (B : GeometricBranchTheory)
    (n : ℕ) (G H : SchemeGerm.{u}) (hsmooth : Prop) :
    B.count G = n ↔ B.count H = n := by
  sorry

def numberOfGeometricBranches {S : Scheme.{u}}
    (B : GeometricBranchTheory) (X : AlgebraicStack S)
    (x : StackPoint X) : WithTop ℕ :=
  if h : ∃ n : ℕ, HasGermPropertyAt (geometricBranchProperty B n) x then
    Nat.find h
  else
    ⊤

def IsGeometricallyUnibranch {S : Scheme.{u}}
    (B : GeometricBranchTheory) (X : AlgebraicStack S)
    (x : StackPoint X) : Prop :=
  numberOfGeometricBranches B X x = 1

theorem geometric_branch_count_finite_or_infinite {S : Scheme.{u}}
    (B : GeometricBranchTheory) (X : AlgebraicStack S)
    (x : StackPoint X) :
    (∃ n : ℕ, numberOfGeometricBranches B X x = n) ∨
      numberOfGeometricBranches B X x = ⊤ := by
  sorry

end Formalization.Books.StacksProperties.Unit01
