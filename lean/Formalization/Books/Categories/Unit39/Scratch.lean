import Mathlib.CategoryTheory.Groupoid.Basic
import Mathlib.CategoryTheory.Skeletal

namespace Scratch

open CategoryTheory
open CategoryTheory.Functor

noncomputable section

def IsSetoid (C : Type* ) [Category* C] : Prop :=
  IsGroupoid C ∧ ∀ X : C, ∀ f : X ⟶ X, f = 𝟙 X

theorem isSetoid_iff_isGroupoid_and_hom_subsingleton
    {C : Type*} [Category* C] :
    IsSetoid C ↔
      IsGroupoid C ∧ ∀ X Y : C, Subsingleton (X ⟶ Y) := by
  constructor
  · rintro ⟨hgroup, hid⟩
    refine ⟨hgroup, ?_⟩
    intro X Y
    constructor
    intro f g
    letI : IsIso g := hgroup.all_isIso g
    apply (cancel_mono (inv g)).1
    rw [hid X (f ≫ inv g)]
    simp
  · rintro ⟨hgroup, hhom⟩
    exact ⟨hgroup, fun X f => Subsingleton.elim _ _⟩

abbrev SetoidObjectClasses (C : Type*) [Category* C] :=
  ThinSkeleton C

theorem setoidObjectClasses_eq_iff
    {C : Type*} [Category* C] {X Y : C} :
    (ThinSkeleton.mk X : SetoidObjectClasses C) = ThinSkeleton.mk Y ↔
      Nonempty (X ≅ Y) := by
  exact Quotient.eq

theorem isDiscrete_iff_every_morphism_is_eqToHom
    {C : Type*} [Category* C] :
    IsDiscrete C ↔
      ∀ {X Y : C} (f : X ⟶ Y), ∃ h : X = Y, f = eqToHom h := by
  constructor
  · intro h X Y f
    exact ⟨h.eq_of_hom f, @Subsingleton.elim _ (h.subsingleton X Y) _ _⟩
  · intro h
    refine ⟨?_, ?_⟩
    · intro X Y
      constructor
      intro f g
      rcases h f with ⟨hf, hff⟩
      rcases h g with ⟨hg, hgg⟩
      rw [hff, hgg]
    · intro X Y f
      exact (h f).choose

theorem object_classes_are_discrete
    {C : Type*} [Category* C] (hC : IsSetoid C) :
    IsDiscrete (SetoidObjectClasses C) := by
  refine ⟨?_, ?_⟩
  · intro X Y
    constructor
    intro f g
    exact Subsingleton.elim _ _
  · intro X Y f
    revert f
    refine Quotient.inductionOn X ?_
    intro X
    refine Quotient.inductionOn Y ?_
    intro Y f
    apply setoidObjectClasses_eq_iff.mpr
    have hXY : Nonempty (X ⟶ Y) := by
      exact leOfHom f
    letI : IsGroupoid C := hC.1
    exact ⟨asIso (Classical.choice hXY)⟩

theorem skeleton_equivalence
    {C : Type*} [Category* C] (hC : IsSetoid C) :
    Nonempty (Skeleton C ≌ C) ∧
      IsDiscrete (Skeleton C) := by
  have hhom : ∀ X Y : C, Subsingleton (X ⟶ Y) :=
    (isSetoid_iff_isGroupoid_and_hom_subsingleton.mp hC).2
  letI : IsGroupoid C := hC.1
  refine ⟨⟨skeletonEquivalence C⟩, ?_⟩
  apply (isDiscrete_iff_every_morphism_is_eqToHom).mpr
  intro X Y f
  let e : (fromSkeleton C).obj X ≅ (fromSkeleton C).obj Y :=
    asIso ((fromSkeleton C).map f)
  have hXY : X = Y := skeleton_skeletal C
    ⟨(fromSkeleton C).preimageIso e⟩
  refine ⟨hXY, ?_⟩
  apply (fromSkeleton C).map_injective
  exact Subsingleton.elim _ _

theorem object_classes_equivalence
    {C : Type*} [Category* C] (hC : IsSetoid C) :
    Nonempty (SetoidObjectClasses C ≌ C) ∧
      IsDiscrete (SetoidObjectClasses C) := by
  sorry

/-
  have hhom : ∀ X Y : C, Subsingleton (X ⟶ Y) :=
    (isSetoid_iff_isGroupoid_and_hom_subsingleton.mp hC).2
  have homOfLE_out :
      ∀ {X Y : SetoidObjectClasses C}, X ≤ Y →
        Nonempty (Quotient.out X ⟶ Quotient.out Y) := by
    intro X Y h
    refine Quotient.inductionOn₂ X Y ?_
    intro X Y h
    exact h
  let F : SetoidObjectClasses C ⥤ C :=
    { obj := Quotient.out
      map := fun {X Y} f => Classical.choice (homOfLE_out (leOfHom f))
      map_id := by
        intro X
        apply hhom
      map_comp := by
        intro X Y Z f g
        apply hhom }
  let unitIso : 𝟭 (SetoidObjectClasses C) ≅ F ⋙ toThinSkeleton C :=
    NatIso.ofComponents
      (fun X => eqToIso (Quotient.out_eq X).symm)
      (by
        intro X Y f
        apply Subsingleton.elim)
  let counitIso : toThinSkeleton C ⋙ F ≅ 𝟭 C :=
    NatIso.ofComponents
      (fun X => Nonempty.some (Quotient.exact (Quotient.out_eq (ThinSkeleton.mk X))))
      (by
        intro X Y f
        exact (hhom ((toThinSkeleton C ⋙ F).obj X) ((toThinSkeleton C ⋙ F).obj Y)).elim _ _)
  letI : F.IsEquivalence :=
    Functor.IsEquivalence.mk' F unitIso counitIso
  exact ⟨⟨F.asEquivalence⟩, object_classes_are_discrete hC⟩
-/

end
end Scratch
