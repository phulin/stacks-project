import Formalization.Books.Dga.Unit25.Core

/-!
# Totalizations of homogeneous morphisms

This file packages the standard passage from homogeneous Hom groups to the
direct-sum Hom modules used by the examples in the chapter.  The category
laws are fields of the presentation: their proofs are proposition-level
interfaces, while the resulting category and graded-category declarations
have ordinary, non-axiomatic bodies.
-/

noncomputable section

open CategoryTheory
open DirectSum
open scoped DirectSum

universe u v w

namespace Formalization.Books.Dga.Unit25

/-- Data for a category obtained by totalizing `ℤ`-graded homogeneous Hom
types.  `total_comp_degree` is the degree-preservation condition on the
direct-sum composition, and `total_comp_lof` records its value on homogeneous
generators. -/
structure TotalGradedCategoryData (R : Type u) (O : Type v)
    (H : O → O → ℤ → Type w)
    [CommRing R]
    [∀ X Y n, AddCommGroup (H X Y n)]
    [∀ X Y n, Module R (H X Y n)] where
  homogeneous_id : ∀ X : O, H X X 0
  homogeneous_comp : ∀ {X Y Z : O} {i j : ℤ},
    H X Y i → H Y Z j → H X Z (i + j)
  total_comp : ∀ {X Y Z : O},
    DirectSum ℤ (fun n => H X Y n) →
      DirectSum ℤ (fun n => H Y Z n) →
        DirectSum ℤ (fun n => H X Z n)
  total_comp_add_left : ∀ {X Y Z : O}
    (f f' : DirectSum ℤ (fun n => H X Y n))
    (g : DirectSum ℤ (fun n => H Y Z n)),
    total_comp (f + f') g = total_comp f g + total_comp f' g
  total_comp_add_right : ∀ {X Y Z : O}
    (f : DirectSum ℤ (fun n => H X Y n))
    (g g' : DirectSum ℤ (fun n => H Y Z n)),
    total_comp f (g + g') = total_comp f g + total_comp f g'
  total_comp_smul_left : ∀ {X Y Z : O} (r : R)
    (f : DirectSum ℤ (fun n => H X Y n))
    (g : DirectSum ℤ (fun n => H Y Z n)),
    total_comp (r • f) g = r • total_comp f g
  total_comp_smul_right : ∀ {X Y Z : O} (r : R)
    (f : DirectSum ℤ (fun n => H X Y n))
    (g : DirectSum ℤ (fun n => H Y Z n)),
    total_comp f (r • g) = r • total_comp f g
  total_comp_lof : ∀ {X Y Z : O} {i j : ℤ}
    (f : H X Y i) (g : H Y Z j),
    total_comp
        (DirectSum.lof R ℤ (fun n => H X Y n) i f)
        (DirectSum.lof R ℤ (fun n => H Y Z n) j g) =
      DirectSum.lof R ℤ (fun n => H X Z n) (i + j)
        (homogeneous_comp f g)
  total_comp_degree : ∀ {X Y Z : O} {i j : ℤ}
    (f : directSumComponent R (fun n => H X Y n) i)
    (g : directSumComponent R (fun n => H Y Z n) j),
    total_comp (f : DirectSum ℤ (fun n => H X Y n))
        (g : DirectSum ℤ (fun n => H Y Z n)) ∈
      directSumComponent R (fun n => H X Z n) (i + j)
  total_id : ∀ X : O, DirectSum ℤ (fun n => H X X n)
  total_id_eq_lof : ∀ X,
    total_id X = DirectSum.lof R ℤ (fun n => H X X n) 0 (homogeneous_id X)
  total_id_comp : ∀ {X Y : O}
    (f : DirectSum ℤ (fun n => H X Y n)),
    total_comp (total_id X) f = f
  total_comp_id : ∀ {X Y : O}
    (f : DirectSum ℤ (fun n => H X Y n)),
    total_comp f (total_id Y) = f
  total_assoc : ∀ {W X Y Z : O}
    (f : DirectSum ℤ (fun n => H W X n))
    (g : DirectSum ℤ (fun n => H X Y n))
    (h : DirectSum ℤ (fun n => H Y Z n)),
    total_comp (total_comp f g) h = total_comp f (total_comp g h)

/-- A type synonym for the objects of a totalized category. -/
structure TotalGradedObject
    {R : Type u} {O : Type v} {H : O → O → ℤ → Type w}
    [CommRing R]
    [∀ X Y n, AddCommGroup (H X Y n)]
    [∀ X Y n, Module R (H X Y n)]
    (D : TotalGradedCategoryData R O H) where
  underlying : O

namespace TotalGradedCategoryData

variable {R : Type u} {O : Type v} {H : O → O → ℤ → Type w}
  [CommRing R]
  [∀ X Y n, AddCommGroup (H X Y n)]
  [∀ X Y n, Module R (H X Y n)]
  (D : TotalGradedCategoryData R O H)

/-- The direct-sum Hom module belonging to two totalized objects. -/
abbrev hom (X Y : TotalGradedObject D) : Type _ :=
  DirectSum ℤ (fun n => H X.underlying Y.underlying n)

/-- The identity morphism in the totalized category. -/
def identity (X : TotalGradedObject D) : hom D X X := D.total_id X.underlying

instance category : Category (TotalGradedObject D) where
  Hom X Y := hom D X Y
  id X := identity D X
  comp f g := D.total_comp f g
  id_comp f := D.total_id_comp f
  comp_id f := D.total_comp_id f
  assoc f g h := D.total_assoc f g h

instance preadditive : Preadditive (TotalGradedObject D) where
  homGroup X Y := by
    exact inferInstanceAs (AddCommGroup (hom D X Y))
  add_comp := by
    intro X Y Z f f' g
    exact D.total_comp_add_left f f' g
  comp_add := by
    intro X Y Z f g g'
    exact D.total_comp_add_right f g g'

instance linear : CategoryTheory.Linear R (TotalGradedObject D) where
  homModule X Y := by
    exact inferInstanceAs (Module R (hom D X Y))
  smul_comp := by
    intro X Y Z r f g
    exact D.total_comp_smul_left r f g
  comp_smul := by
    intro X Y Z f r g
    exact D.total_comp_smul_right r f g

instance gradedCategory : GradedCategory R (TotalGradedObject D) where
  hom X Y := by
    change GradedModuleData R (hom D X Y) ℤ
    exact directSumGradedModuleData R (fun n => H X.underlying Y.underlying n)
  comp_homogeneous f g := D.total_comp_degree f g
  id_homogeneous X := by
    exact ⟨D.homogeneous_id X.underlying,
      (D.total_id_eq_lof X.underlying).symm⟩
  
@[simp] theorem totalized_identity_eq_lof (X : TotalGradedObject D) :
    identity D X =
      DirectSum.lof R ℤ (fun n => H X.underlying X.underlying n) 0
        (D.homogeneous_id X.underlying) :=
  D.total_id_eq_lof X.underlying

theorem totalized_homogeneous_composition
    {X Y Z : TotalGradedObject D} {i j : ℤ}
    (f : H X.underlying Y.underlying i)
    (g : H Y.underlying Z.underlying j) :
    (D.total_comp
        (DirectSum.lof R ℤ (fun n => H X.underlying Y.underlying n) i f)
        (DirectSum.lof R ℤ (fun n => H Y.underlying Z.underlying n) j g)) =
      DirectSum.lof R ℤ (fun n => H X.underlying Z.underlying n) (i + j)
        (D.homogeneous_comp f g) :=
  D.total_comp_lof f g

end TotalGradedCategoryData

end Formalization.Books.Dga.Unit25
