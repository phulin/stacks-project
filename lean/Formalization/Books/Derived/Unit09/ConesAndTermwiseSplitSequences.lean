import Mathlib.Algebra.Homology.HomotopyCategory.DegreewiseSplit
import Mathlib.CategoryTheory.ComposableArrows.Basic
import Formalization.Books.Derived.Unit08.HomotopyCategory

/-!
# Derived Categories, Chapter 9: cones and termwise split sequences

The source's cone is Mathlib's canonical `CochainComplex.mappingCone`.  Its
homotopy-category triangle, its functoriality for squares commuting up to
homotopy, and the comparison with degreewise split sequences are already
available in Mathlib.  This file exposes those APIs with the source's
terminology and records the remaining theorem interfaces.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Preadditive
open CategoryTheory.Pretriangulated
open Formalization.Books.Derived.Unit08
open Formalization.Books.Homology.Unit03
open HomologicalComplex

universe v u

namespace Formalization.Books.Derived.Unit09

/-! ## Complexes, shifts, and canonical cones -/

/-- The source's `Comp(𝒜)`, represented by integer-indexed cochain complexes. -/
abbrev BookComplex (C : Type u) [Category.{v} C] [AdditiveCategory C] :=
  Formalization.Books.Derived.Unit08.Comp C

/-- The source's `K(𝒜)`, represented by the homotopy category of cochain complexes. -/
abbrev BookHomotopyCategory (C : Type u) [Category.{v} C] [AdditiveCategory C] :=
  Formalization.Books.Derived.Unit08.K C

/-- The shift functor on the source's homotopy category. -/
abbrev homotopyShift
    (C : Type u) [Category.{v} C] [AdditiveCategory C] (n : ℤ) :
    BookHomotopyCategory C ⥤ BookHomotopyCategory C :=
  CategoryTheory.shiftFunctor (BookHomotopyCategory C) n

/-- The zero shift is canonically the identity. -/
noncomputable def homotopyShiftZero
    (C : Type u) [Category.{v} C] [AdditiveCategory C] :
    homotopyShift C 0 ≅ 𝟭 (BookHomotopyCategory C) :=
  CategoryTheory.shiftFunctorZero (BookHomotopyCategory C) ℤ

/-- Two successive shifts identify with the shift by the sum. -/
noncomputable def homotopyShiftAdd
    (C : Type u) [Category.{v} C] [AdditiveCategory C] (n m : ℤ) :
    homotopyShift C n ⋙ homotopyShift C m ≅ homotopyShift C (n + m) :=
  (CategoryTheory.shiftFunctorAdd (BookHomotopyCategory C) n m).symm

/-- The canonical mapping cone of a morphism of cochain complexes. -/
abbrev Cone
    {C : Type u} [Category.{v} C] [AdditiveCategory C]
    {K L : BookComplex C} (f : K ⟶ L) : BookComplex C :=
  CochainComplex.mappingCone f

/-- The canonical inclusion of the target into a mapping cone. -/
noncomputable def coneInclusion
    {C : Type u} [Category.{v} C] [AdditiveCategory C]
    {K L : BookComplex C} (f : K ⟶ L) : L ⟶ Cone f :=
  CochainComplex.mappingCone.inr f

/-- The canonical third map from a mapping cone to the shifted source. -/
noncomputable def coneProjection
    {C : Type u} [Category.{v} C] [AdditiveCategory C]
    {K L : BookComplex C} (f : K ⟶ L) :
    Cone f ⟶ (CategoryTheory.shiftFunctor (BookComplex C) (1 : ℤ)).obj K :=
  (CochainComplex.mappingCone.triangle f).mor₃

/-- The canonical cone triangle in complexes. -/
noncomputable def coneTriangle
    {C : Type u} [Category.{v} C] [AdditiveCategory C]
    {K L : BookComplex C} (f : K ⟶ L) :
    Triangle (BookComplex C) :=
  CochainComplex.mappingCone.triangle f

/-- The canonical cone triangle in the homotopy category. -/
abbrev coneTriangleh
    {C : Type u} [Category.{v} C] [AdditiveCategory C]
    {K L : BookComplex C} (f : K ⟶ L) :
    Triangle (BookHomotopyCategory C) :=
  CochainComplex.mappingCone.triangleh f

@[simp]
theorem coneTriangle_mor₁
    {C : Type u} [Category.{v} C] [AdditiveCategory C]
    {K L : BookComplex C} (f : K ⟶ L) :
    (coneTriangle f).mor₁ = f := rfl

@[simp]
theorem coneTriangle_mor₂
    {C : Type u} [Category.{v} C] [AdditiveCategory C]
    {K L : BookComplex C} (f : K ⟶ L) :
    (coneTriangle f).mor₂ = coneInclusion f := rfl

@[simp]
theorem coneTriangle_mor₃
    {C : Type u} [Category.{v} C] [AdditiveCategory C]
    {K L : BookComplex C} (f : K ⟶ L) :
    (coneTriangle f).mor₃ = coneProjection f := rfl

theorem coneTriangleh_distinguished
    {C : Type u} [Category.{v} C] [AdditiveCategory C]
    {K L : BookComplex C} (f : K ⟶ L) :
    coneTriangleh f ∈ distTriang (BookHomotopyCategory C) := by
  exact HomotopyCategory.mappingCone_triangleh_distinguished f

/-! ## Functoriality and factorization through cones -/

/-- The cone map associated to a chosen homotopy-commutative square.

The explicit homotopy is an argument, recording the source's warning that
the resulting cone map is not canonical when the square only commutes up to
homotopy.
-/
noncomputable def coneMapOfHomotopy
    {C : Type u} [Category.{v} C] [AdditiveCategory C]
    {K₁ L₁ K₂ L₂ : BookComplex C}
    {f₁ : K₁ ⟶ L₁} {f₂ : K₂ ⟶ L₂}
    {a : K₁ ⟶ K₂} {b : L₁ ⟶ L₂}
    (H : Homotopy (f₁ ≫ b) (a ≫ f₂)) : Cone f₁ ⟶ Cone f₂ :=
  CochainComplex.mappingCone.mapOfHomotopy H

/-- Functoriality of the cone for a square commuting up to homotopy. -/
noncomputable def coneTriangleMapOfHomotopy
    {C : Type u} [Category.{v} C] [AdditiveCategory C]
    {K₁ L₁ K₂ L₂ : BookComplex C}
    {f₁ : K₁ ⟶ L₁} {f₂ : K₂ ⟶ L₂}
    {a : K₁ ⟶ K₂} {b : L₁ ⟶ L₂}
    (H : Homotopy (f₁ ≫ b) (a ≫ f₂)) :
    coneTriangleh f₁ ⟶ coneTriangleh f₂ :=
  CochainComplex.mappingCone.trianglehMapOfHomotopy H

theorem functorial_cone
    {C : Type u} [Category.{v} C] [AdditiveCategory C]
    {K₁ L₁ K₂ L₂ : BookComplex C}
    {f₁ : K₁ ⟶ L₁} {f₂ : K₂ ⟶ L₂}
    {a : K₁ ⟶ K₂} {b : L₁ ⟶ L₂}
    (H : Homotopy (f₁ ≫ b) (a ≫ f₂)) :
    (coneTriangleMapOfHomotopy H).hom₁ =
        (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map a ∧
      (coneTriangleMapOfHomotopy H).hom₂ =
        (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map b ∧
      (coneTriangleMapOfHomotopy H).hom₃ =
        (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map
          (coneMapOfHomotopy H) := by
  sorry

theorem map_from_cone
    {C : Type u} [Category.{v} C] [AdditiveCategory C]
    {K L M : BookComplex C} (f : K ⟶ L) (g : L ⟶ M)
    (H : Homotopy (f ≫ g) 0) :
    (∃ u : Cone f ⟶ M, coneInclusion f ≫ u = g) ∧
      (∃ u : K ⟶ (coneTriangle g).invRotate.obj₁,
        u ≫ (coneTriangle g).invRotate.mor₁ = f) := by
  sorry

/-! ## Termwise split maps and replacements -/

/-- A map of cochain complexes is termwise split injective. -/
def termwiseSplitInjection
    {C : Type u} [Category.{v} C] [AdditiveCategory C]
    {K L : BookComplex C} (f : K ⟶ L) : Prop :=
  ∀ n : ℤ, IsSplitMono (f.f n)

/-- A map of cochain complexes is termwise split surjective. -/
def termwiseSplitSurjection
    {C : Type u} [Category.{v} C] [AdditiveCategory C]
    {K L : BookComplex C} (f : K ⟶ L) : Prop :=
  ∀ n : ℤ, IsSplitEpi (f.f n)

theorem make_commute_map_injection
    {C : Type u} [Category.{v} C] [AdditiveCategory C]
    {A B C' D : BookComplex C}
    {f : A ⟶ B} {a : A ⟶ C'} {b : B ⟶ D} {g : C' ⟶ D}
    (H : Homotopy (f ≫ b) (a ≫ g))
    (hf : termwiseSplitInjection f) :
    ∃ b' : B ⟶ D, Nonempty (Homotopy b b') ∧ f ≫ b' = a ≫ g := by
  sorry

theorem make_commute_map_surjection
    {C : Type u} [Category.{v} C] [AdditiveCategory C]
    {A B C' D : BookComplex C}
    {f : A ⟶ B} {a : A ⟶ C'} {b : B ⟶ D} {g : C' ⟶ D}
    (H : Homotopy (f ≫ b) (a ≫ g))
    (hg : termwiseSplitSurjection g) :
    ∃ a' : A ⟶ C', Nonempty (Homotopy a a') ∧ f ≫ b = a' ≫ g := by
  sorry

theorem make_injective
    {C : Type u} [Category.{v} C] [AdditiveCategory C]
    {K L : BookComplex C} (α : K ⟶ L) :
    ∃ (L' : BookComplex C) (i : K ⟶ L') (π : L' ⟶ L),
      i ≫ π = α ∧
      termwiseSplitInjection i ∧
      ∃ s : L ⟶ L',
        s ≫ π = 𝟙 L ∧
        Nonempty (Homotopy (π ≫ s) (𝟙 L')) ∧
        ((IsBoundedBelow K ∧ IsBoundedBelow L) → IsBoundedBelow L') ∧
        ((IsBoundedAbove K ∧ IsBoundedAbove L) → IsBoundedAbove L') ∧
        ((IsBounded K ∧ IsBounded L) → IsBounded L') := by
  sorry

theorem make_surjective
    {C : Type u} [Category.{v} C] [AdditiveCategory C]
    {K L : BookComplex C} (α : K ⟶ L) :
    ∃ (K' : BookComplex C) (i : K ⟶ K') (π : K' ⟶ L),
      i ≫ π = α ∧
      termwiseSplitSurjection π ∧
      ∃ s : K' ⟶ K,
        i ≫ s = 𝟙 K ∧
        Nonempty (Homotopy (s ≫ i) (𝟙 K')) ∧
        ((IsBoundedBelow K ∧ IsBoundedBelow L) → IsBoundedBelow K') ∧
        ((IsBoundedAbove K ∧ IsBoundedAbove L) → IsBoundedAbove K') ∧
        ((IsBounded K ∧ IsBounded L) → IsBounded K') := by
  sorry

/-! ## Termwise split exact sequences and their triangles -/

/-- A termwise split exact sequence, expressed by degreewise Mathlib splittings.

The splittings are the categorical form of the source's specified direct-sum
decompositions `Bⁿ = Aⁿ ⊕ Cⁿ`, with `r` the projection to `Aⁿ` and `s` the
section from `Cⁿ`.
-/
structure TermwiseSplitExactSequence
    {C : Type u} [Category.{v} C] [AdditiveCategory C]
    (A B D : BookComplex C) where
  f : A ⟶ B
  g : B ⟶ D
  zero : f ≫ g = 0
  splitting : ∀ n : ℤ,
    ((ShortComplex.mk f g zero).map
      (HomologicalComplex.eval C (ComplexShape.up ℤ) n)).Splitting

def termwiseSplitShortComplex
    {C : Type u} [Category.{v} C] [AdditiveCategory C]
    {A B D : BookComplex C} (S : TermwiseSplitExactSequence A B D) :
    ShortComplex (BookComplex C) :=
  ShortComplex.mk S.f S.g S.zero

def termwiseSplitSection
    {C : Type u} [Category.{v} C] [AdditiveCategory C]
    {A B D : BookComplex C} (S : TermwiseSplitExactSequence A B D) (n : ℤ) :
    D.X n ⟶ B.X n :=
  (S.splitting n).s

def termwiseSplitProjection
    {C : Type u} [Category.{v} C] [AdditiveCategory C]
    {A B D : BookComplex C} (S : TermwiseSplitExactSequence A B D) (n : ℤ) :
    B.X n ⟶ A.X n :=
  (S.splitting n).r

def termwiseSplitConnectingFamily
    {C : Type u} [Category.{v} C] [AdditiveCategory C]
    {A B D : BookComplex C} (S : TermwiseSplitExactSequence A B D) (n : ℤ) :
    D.X n ⟶ A.X (n + 1) :=
  termwiseSplitSection S n ≫ B.d n (n + 1) ≫ termwiseSplitProjection S (n + 1)

noncomputable def termwiseSplitConnectingMap
    {C : Type u} [Category.{v} C] [AdditiveCategory C]
    {A B D : BookComplex C} (S : TermwiseSplitExactSequence A B D) :
    D ⟶ (CategoryTheory.shiftFunctor (BookComplex C) (1 : ℤ)).obj A :=
  CochainComplex.homOfDegreewiseSplit (termwiseSplitShortComplex S) S.splitting

theorem termwiseSplitConnectingMap_f
    {C : Type u} [Category.{v} C] [AdditiveCategory C]
    {A B D : BookComplex C} (S : TermwiseSplitExactSequence A B D) (n : ℤ) :
    (termwiseSplitConnectingMap S).f n = termwiseSplitConnectingFamily S n := by
  sorry

noncomputable def termwiseSplitTriangleWith
    {C : Type u} [Category.{v} C] [AdditiveCategory C]
    {A B D : BookComplex C} (S : TermwiseSplitExactSequence A B D)
    (σ : ∀ n : ℤ,
      ((termwiseSplitShortComplex S).map
        (HomologicalComplex.eval C (ComplexShape.up ℤ) n)).Splitting) :
    Triangle (BookComplex C) :=
  CochainComplex.triangleOfDegreewiseSplit (termwiseSplitShortComplex S) σ

abbrev termwiseSplitTriangle
    {C : Type u} [Category.{v} C] [AdditiveCategory C]
    {A B D : BookComplex C} (S : TermwiseSplitExactSequence A B D) :
    Triangle (BookComplex C) :=
  termwiseSplitTriangleWith S S.splitting

abbrev termwiseSplitTrianglehWith
    {C : Type u} [Category.{v} C] [AdditiveCategory C]
    {A B D : BookComplex C} (S : TermwiseSplitExactSequence A B D)
    (σ : ∀ n : ℤ,
      ((termwiseSplitShortComplex S).map
        (HomologicalComplex.eval C (ComplexShape.up ℤ) n)).Splitting) :
    Triangle (BookHomotopyCategory C) :=
  (HomotopyCategory.quotient C (ComplexShape.up ℤ)).mapTriangle.obj
    (termwiseSplitTriangleWith S σ)

abbrev termwiseSplitTriangleh
    {C : Type u} [Category.{v} C] [AdditiveCategory C]
    {A B D : BookComplex C} (S : TermwiseSplitExactSequence A B D) :
    Triangle (BookHomotopyCategory C) :=
  termwiseSplitTrianglehWith S S.splitting

theorem triangle_independent_splittings
    {C : Type u} [Category.{v} C] [AdditiveCategory C]
    {A B D : BookComplex C} (S : TermwiseSplitExactSequence A B D)
    (σ σ' : ∀ n : ℤ,
      ((termwiseSplitShortComplex S).map
        (HomologicalComplex.eval C (ComplexShape.up ℤ) n)).Splitting) :
    Nonempty (Homotopy
      (CochainComplex.homOfDegreewiseSplit (termwiseSplitShortComplex S) σ)
      (CochainComplex.homOfDegreewiseSplit (termwiseSplitShortComplex S) σ')) ∧
      ∃ e : termwiseSplitTrianglehWith S σ ≅ termwiseSplitTrianglehWith S σ',
        e.hom.hom₁ = 𝟙 _ ∧ e.hom.hom₂ = 𝟙 _ ∧ e.hom.hom₃ = 𝟙 _ := by
  sorry

/-! ## Consequences in the homotopy category -/

theorem nilpotent
    {C : Type u} [Category.{v} C] [AdditiveCategory C]
    {A₁ B₁ D₁ A₂ B₂ D₂ A₃ B₃ D₃ : BookComplex C}
    (S₁ : TermwiseSplitExactSequence A₁ B₁ D₁)
    (S₂ : TermwiseSplitExactSequence A₂ B₂ D₂)
    (S₃ : TermwiseSplitExactSequence A₃ B₃ D₃)
    (b : B₁ ⟶ B₂) (b' : B₂ ⟶ B₃)
    (h₁ : (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map S₁.f ≫
      (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map b = 0)
    (h₂ : (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map b ≫
      (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map S₂.g = 0)
    (h₃ : (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map S₂.f ≫
      (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map b' = 0)
    (h₄ : (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map b' ≫
      (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map S₃.g = 0) :
    (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map (b ≫ b') = 0 := by
  sorry

theorem third_isomorphism
    {C : Type u} [Category.{v} C] [AdditiveCategory C]
    {K₁ L₁ K₂ L₂ : BookComplex C}
    {f₁ : K₁ ⟶ L₁} {f₂ : K₂ ⟶ L₂}
    (t : coneTriangleh f₁ ⟶ coneTriangleh f₂)
    [IsIso t.hom₁] [IsIso t.hom₂] : IsIso t.hom₃ := by
  sorry

theorem triangle_morphism_isomorphism_of_first_two
    {C : Type u} [Category.{v} C] [AdditiveCategory C]
    {K₁ L₁ K₂ L₂ : BookComplex C}
    {f₁ : K₁ ⟶ L₁} {f₂ : K₂ ⟶ L₂}
    (t : coneTriangleh f₁ ⟶ coneTriangleh f₂)
    [IsIso t.hom₁] [IsIso t.hom₂] : IsIso t := by
  apply Triangle.isIso_of_isIsos t
  · infer_instance
  · infer_instance
  · exact third_isomorphism t

/-! ## Cones and termwise split sequences agree up to isomorphism -/

theorem same_up_to_isomorphisms_of_termwise_split
    {C : Type u} [Category.{v} C] [AdditiveCategory C]
    {A B D : BookComplex C} (S : TermwiseSplitExactSequence A B D) :
    ∃ e : termwiseSplitTriangleh S ≅ coneTriangleh S.f,
      e.hom.hom₁ = 𝟙 _ ∧ e.hom.hom₂ = 𝟙 _ := by
  sorry

theorem same_up_to_isomorphisms_of_map
    {C : Type u} [Category.{v} C] [AdditiveCategory C]
    {K L : BookComplex C} (f : K ⟶ L) :
    ∃ (M N : BookComplex C) (S : TermwiseSplitExactSequence K M N),
      ∃ e : termwiseSplitTriangleh S ≅ coneTriangleh f,
        e.hom.hom₁ = 𝟙 _ := by
  sorry

/-! ## Simultaneous termwise split replacements -/

def adjacentMap
    {C : Type u} [Category.{v} C] [AdditiveCategory C]
    {n : ℕ} (F : ComposableArrows (BookComplex C) n) (i : Fin n) :
    F.obj ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ ⟶
      F.obj ⟨Nat.succ i.val, Nat.succ_lt_succ i.isLt⟩ :=
  F.map (homOfLE (show
    (⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ : Fin (n + 1)) ≤
      ⟨Nat.succ i.val, Nat.succ_lt_succ i.isLt⟩ by simp))

theorem sequence_maps_split
    {C : Type u} [Category.{v} C] [AdditiveCategory C]
    {n : ℕ} (A : ComposableArrows (BookComplex C) n) :
    ∃ (B : ComposableArrows (BookComplex C) n) (φ : B ⟶ A),
      (∀ i : Fin n, termwiseSplitInjection (adjacentMap B i)) ∧
      (∀ i : Fin (n + 1),
        HomologicalComplex.homotopyEquivalences C (ComplexShape.up ℤ) (φ.app i)) ∧
      ((∀ i : Fin (n + 1), IsBoundedBelow (A.obj i)) →
        ∀ i : Fin (n + 1), IsBoundedBelow (B.obj i)) ∧
      ((∀ i : Fin (n + 1), IsBoundedAbove (A.obj i)) →
        ∀ i : Fin (n + 1), IsBoundedAbove (B.obj i)) ∧
      ((∀ i : Fin (n + 1), IsBounded (A.obj i)) →
        ∀ i : Fin (n + 1), IsBounded (B.obj i)) := by
  sorry

/-! ## Rotation -/

/-- The canonical inverse rotation of the associated termwise split triangle. -/
noncomputable def termwiseSplitInverseRotate
    {C : Type u} [Category.{v} C] [AdditiveCategory C]
    {A B D : BookComplex C} (S : TermwiseSplitExactSequence A B D) :
    Triangle (BookComplex C) :=
  (termwiseSplitTriangle S).invRotate

abbrev termwiseSplitInverseRotateh
    {C : Type u} [Category.{v} C] [AdditiveCategory C]
    {A B D : BookComplex C} (S : TermwiseSplitExactSequence A B D) :
    Triangle (BookHomotopyCategory C) :=
  ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).mapTriangle.obj
    (termwiseSplitInverseRotate S))

theorem rotate_triangle
    {C : Type u} [Category.{v} C] [AdditiveCategory C]
    {A B D : BookComplex C} (S : TermwiseSplitExactSequence A B D) :
    Nonempty (termwiseSplitInverseRotateh S ≅
      coneTriangleh (termwiseSplitInverseRotate S).mor₁) := by
  sorry

noncomputable def coneTermwiseSplitSequence
    {C : Type u} [Category.{v} C] [AdditiveCategory C]
    {K L : BookComplex C} (f : K ⟶ L) :
    TermwiseSplitExactSequence
      (CochainComplex.mappingCone.triangle f).rotate.obj₁
      (CochainComplex.mappingCone.triangle f).rotate.obj₂
      (CochainComplex.mappingCone.triangle f).rotate.obj₃ where
  f := (CochainComplex.mappingCone.triangle f).rotate.mor₁
  g := (CochainComplex.mappingCone.triangle f).rotate.mor₂
  zero := by
    change CochainComplex.mappingCone.inr f ≫
      (CochainComplex.mappingCone.triangle f).mor₃ = 0
    exact CochainComplex.mappingCone.inr_triangleδ f
  splitting := fun n => by
    simpa [termwiseSplitShortComplex,
      CochainComplex.mappingCone.triangleRotateShortComplex] using
      (CochainComplex.mappingCone.triangleRotateShortComplexSplitting f n)

theorem rotate_cone
    {C : Type u} [Category.{v} C] [AdditiveCategory C]
    {K L : BookComplex C} (f : K ⟶ L) :
    Nonempty (termwiseSplitTriangleh (coneTermwiseSplitSequence f) ≅
      (coneTriangleh f).rotate) := by
  sorry

end Formalization.Books.Derived.Unit09
