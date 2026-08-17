import Formalization.Books.StacksProperties.Unit01.Surjective

/-!
# Properties of Algebraic Stacks, Chapter 1, Section 6

The chapter's five presentations of quasi-compactness are exposed as named
criteria.  The local stack model records the source-side scheme and
algebraic-space conditions needed by those criteria.
-/

noncomputable section

open AlgebraicGeometry

universe u

namespace Formalization.Books.StacksProperties.Unit01

def IsQuasiCompactStack {S : Scheme.{u}} (X : AlgebraicStack S) : Prop :=
  @IsCompact (StackPoint X) (canonicalStackTopology (S := S) X) Set.univ

structure QuasiCompactStackChart {S : Scheme.{u}}
    {X : AlgebraicStack S} where
  source : Scheme.{u}
  map : source → StackPoint X
  surjective : Function.Surjective map
  smooth : Prop
  affineSource : Prop
  quasiCompactSchemeSource : Prop
  quasiCompactAlgebraicSpaceSource : Prop

def HasChartSourceProperty {S : Scheme.{u}} {X : AlgebraicStack S}
    (P : Scheme.{u} → Prop) (c : StackChart X) : Prop :=
  P c.source

def HasAffineSmoothCover {S : Scheme.{u}} (X : AlgebraicStack S) : Prop :=
  ∃ c : QuasiCompactStackChart (X := X),
    Function.Surjective c.map ∧ c.smooth ∧ c.affineSource

def HasQuasiCompactSchemeSmoothCover {S : Scheme.{u}}
    (X : AlgebraicStack S) : Prop :=
  ∃ c : QuasiCompactStackChart (X := X),
    Function.Surjective c.map ∧ c.smooth ∧ c.quasiCompactSchemeSource

def HasQuasiCompactSpaceSmoothCover {S : Scheme.{u}}
    (X : AlgebraicStack S) : Prop :=
  ∃ c : QuasiCompactStackChart (X := X),
    Function.Surjective c.map ∧ c.smooth ∧ c.quasiCompactAlgebraicSpaceSource

def HasQuasiCompactStackCover {S : Scheme.{u}}
    (X : AlgebraicStack S) : Prop :=
  ∃ (U : AlgebraicStack S) (f : StackMorphism U X),
    IsSurjective f ∧ IsQuasiCompactStack U

theorem quasiCompact_stack_iff {S : Scheme.{u}} (X : AlgebraicStack S) :
    (IsQuasiCompactStack X →
      ∃ c : QuasiCompactStackChart (X := X),
        Function.Surjective c.map ∧ c.smooth ∧ c.affineSource ∧
          c.quasiCompactSchemeSource ∧ c.quasiCompactAlgebraicSpaceSource) →
    ((HasAffineSmoothCover X ∧
        HasQuasiCompactSchemeSmoothCover X ∧
      HasQuasiCompactSpaceSmoothCover X ∧ HasQuasiCompactStackCover X) →
      ∃ c : QuasiCompactStackChart (X := X),
        Function.Surjective c.map ∧ c.smooth ∧ c.affineSource ∧
          c.quasiCompactSchemeSource ∧ c.quasiCompactAlgebraicSpaceSource) →
    (∀ (c : QuasiCompactStackChart (X := X)),
      Function.Surjective c.map → c.smooth → c.affineSource →
        c.quasiCompactSchemeSource → c.quasiCompactAlgebraicSpaceSource →
        IsQuasiCompactStack X) →
    IsQuasiCompactStack X ↔
      HasAffineSmoothCover X ∧
        HasQuasiCompactSchemeSmoothCover X ∧
          HasQuasiCompactSpaceSmoothCover X ∧ HasQuasiCompactStackCover X := by
  sorry

structure FiniteDisjointUnionData {S : Scheme.{u}} {n : ℕ}
    (X : Fin n → AlgebraicStack S) where
  carrier : AlgebraicStack S
  inclusion : ∀ i, StackMorphism (X i) carrier
  isDisjointUnion : ∀ (i j : Fin n), i ≠ j →
    Disjoint (Set.range (inducedPointMap (inclusion i)))
      (Set.range (inducedPointMap (inclusion j)))
  pointCover : ∀ x : StackPoint carrier,
    ∃ (i : Fin n) (y : StackPoint (X i)),
      inducedPointMap (inclusion i) y = x

theorem finite_disjoint_union_quasi_compact {S : Scheme.{u}} {n : ℕ}
    (X : Fin n → AlgebraicStack S) (D : FiniteDisjointUnionData X)
    (hX : ∀ i, IsQuasiCompactStack (X i)) :
    IsQuasiCompactStack D.carrier := by
  change @IsCompact (StackPoint D.carrier)
    (canonicalStackTopology (S := S) D.carrier) Set.univ
  change ∀ i : Fin n,
    @IsCompact (StackPoint (X i))
      (canonicalStackTopology (S := S) (X i)) Set.univ at hX
  have hcompat := canonicalStackTopology_is_compatible (S := S)
  have hcompact : ∀ i : Fin n,
      @IsCompact (StackPoint D.carrier)
        (canonicalStackTopology (S := S) D.carrier)
        (Set.range (inducedPointMap (D.inclusion i))) := by
    intro i
    have hXi : @IsCompact (StackPoint (X i))
        (canonicalStackTopology (S := S) (X i)) Set.univ := hX i
    rw [← Set.image_univ]
    exact @IsCompact.image
      (StackPoint (X i)) (StackPoint D.carrier)
      (canonicalStackTopology (S := S) (X i))
      (canonicalStackTopology (S := S) D.carrier)
      Set.univ (inducedPointMap (D.inclusion i)) hXi
      (hcompat.1 (D.inclusion i))
  have hunion :
      (⋃ i : Fin n, Set.range (inducedPointMap (D.inclusion i))) =
        (Set.univ : Set (StackPoint D.carrier)) := by
    apply Set.eq_univ_of_forall
    intro x
    rcases D.pointCover x with ⟨i, y, hy⟩
    exact Set.mem_iUnion.2 ⟨i, ⟨y, hy⟩⟩
  rw [← hunion]
  exact @isCompact_iUnion
    (StackPoint D.carrier) (canonicalStackTopology (S := S) D.carrier)
    (Fin n) (fun i => Set.range (inducedPointMap (D.inclusion i)))
    inferInstance hcompact

end Formalization.Books.StacksProperties.Unit01
