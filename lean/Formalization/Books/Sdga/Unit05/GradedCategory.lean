import Formalization.Books.Sdga.Unit02.Core

/-! # 5. The graded category of sheaves of graded modules -/

namespace Sdga

universe u v

variable {R : Type u} [CommRing R]

def gradedCategoryHom {S : RingedSite.{u,v} R} {A : GradedAlgebra S}
    (M N : GradedModule S A) (k : ℤ) := HomogeneousMap M N k

def gradedCategoryComposition {S : RingedSite.{u,v} R} {A : GradedAlgebra S}
    {M N P : GradedModule S A} {k l : ℤ}
    (g : gradedCategoryHom N P l) (f : gradedCategoryHom M N k) :=
  HomogeneousMap.comp g f

def gradedCategoryIdentity {S : RingedSite.{u,v} R} {A : GradedAlgebra S}
    (M : GradedModule S A) : gradedCategoryHom M M 0 where
  app n U x := cast
    (congrArg (fun q : ℤ => M.component q U) (Int.add_zero n).symm) x
  module_map := by
    intro n m U x a
    have transport_action : ∀ (p q : ℤ) (h : p = q) (y : M.component p U), HEq
        (M.action p m U y a)
        (M.action q m U
          (cast (congrArg (fun q => M.component q U) h) y) a) := by
      intro p q h y
      cases h
      rfl
    have haction := transport_action n (n + 0) (Int.add_zero n).symm x
    exact HEq.trans
      (cast_heq (congrArg (fun q => M.component q U)
        (Int.add_zero (n + m)).symm) (M.action n m U x a)) haction

structure GradedCategoryOfModules {S : RingedSite.{u,v} R}
    (A : GradedAlgebra S) where
  objects : Type (max (u + 1) v)
  hom : objects → objects → ℤ → Prop
  identities : Prop
  composition : Prop
  associativity : Prop

def gradedCategoryOfModules {S : RingedSite.{u,v} R} (A : GradedAlgebra S) :
    GradedCategoryOfModules A where
  objects := GradedModule S A
  hom := fun M N k => Nonempty (gradedCategoryHom M N k)
  identities := ∀ (M : GradedModule S A),
    Nonempty (gradedCategoryHom M M 0)
  composition :=
    ∀ (M _N P : GradedModule S A) (k l : ℤ),
      Nonempty (gradedCategoryHom M P (k + l))
  associativity :=
    ∀ (M : GradedModule S A),
      HEq (gradedCategoryComposition (gradedCategoryIdentity M)
        (gradedCategoryIdentity M)) (gradedCategoryIdentity M)

theorem graded_category_hom_is_module_map
    {S : RingedSite.{u,v} R} {A : GradedAlgebra S}
    {M N : GradedModule S A} {k : ℤ} (f : gradedCategoryHom M N k) :
    HomogeneousMap.isModuleMap f := by
  exact f.module_map

theorem graded_category_composition_degree
    {S : RingedSite.{u,v} R} {A : GradedAlgebra S}
    {M N P : GradedModule S A} {k l : ℤ}
    (g : gradedCategoryHom N P l) (f : gradedCategoryHom M N k) :
    gradedCategoryComposition g f = HomogeneousMap.comp g f := by
  rfl

end Sdga
