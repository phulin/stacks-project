import Formalization.Books.StacksProperties.Unit12.Dimension
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
  smoothInvariant : ∀ {G H : SchemeGerm.{u}} (f : SchemeGerm.Hom G H),
    Smooth f.map → count G = count H

def SmoothBranchInvariant (B : GeometricBranchTheory) : Prop :=
  ∀ {G H : SchemeGerm.{u}} (f : SchemeGerm.Hom G H),
    Smooth f.map → B.count G = B.count H

def BranchCountProperty (B : GeometricBranchTheory) (n : ℕ) :
    LocalPropertyOfGerms where
  property := fun X x => B.count ⟨X, x⟩ = n
  smoothLocal := SmoothBranchInvariant B

def geometricBranchProperty {S : Scheme.{u}}
    (B : GeometricBranchTheory) (n : ℕ) :
    SmoothLocalGermProperty S where
  schemeProperty := BranchCountProperty B n
  spaceProperty := fun W u => B.count ⟨W.left, u⟩ = n
  comparison := fun W u => Iff.rfl
  smoothLocal := by
    exact B.smoothInvariant

theorem geometric_branch_smooth_invariant (B : GeometricBranchTheory)
    (n : ℕ) {G H : SchemeGerm.{u}} (f : SchemeGerm.Hom G H)
    (hsmooth : Smooth f.map) :
    B.count G = n ↔ B.count H = n := by
  rw [B.smoothInvariant f hsmooth]

def numberOfGeometricBranches {S : Scheme.{u}}
    (B : GeometricBranchTheory) (X : AlgebraicStack S)
    (x : StackPoint X) : WithTop ℕ :=
  by
    classical
    exact if h : ∃ n : ℕ, HasGermPropertyAt (geometricBranchProperty B n) x then
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
  classical
  unfold numberOfGeometricBranches
  split_ifs with h
  · left
    exact ⟨Nat.find h, rfl⟩
  · exact Or.inr rfl

end Formalization.Books.StacksProperties.Unit01
