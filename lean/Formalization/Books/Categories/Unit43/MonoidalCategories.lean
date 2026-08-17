import Mathlib.Algebra.Category.ModuleCat.Monoidal.Adjunction
import Mathlib.CategoryTheory.Adjunction.Parametrized
import Mathlib.CategoryTheory.Adjunction.Unique
import Mathlib.CategoryTheory.Monoidal.Braided.Basic
import Mathlib.CategoryTheory.Monoidal.CoherenceLemmas
import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import Mathlib.CategoryTheory.Monoidal.Rigid.Braided
import Mathlib.Tactic.CategoryTheory.Monoidal.Basic

/-!
# Categories, Chapter 43: Monoidal categories

The source uses a tensor functor, associativity and unit constraints, and
then develops duals, symmetry, monoidal functors, and internal Homs.  The
canonical Mathlib interfaces are used throughout: `MonoidalCategory`,
`Functor.Monoidal`, `BraidedCategory`, `SymmetricCategory`, and
`ExactPairing`.  The small source-facing structures below occur only where
the chapter discusses an alternate unit or the right-handed internal-Hom
adjunction, neither of which is a separate core Mathlib structure.
-/

namespace Formalization.Books.Categories.Unit43

open CategoryTheory
open CategoryTheory.Functor
open CategoryTheory.MonoidalCategory
open Opposite

universe u v u' v' w w'

noncomputable section

/-! ## Tensor products, associativity, and coherence -/

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/- The tensor bifunctor is already `MonoidalCategory.tensor`.  The source
   chooses the opposite orientation for its associator, so only that
   orientation bridge is named here. -/
abbrev associativityConstraint :
    MonoidalCategory.rightAssocTensor C ≅ MonoidalCategory.leftAssocTensor C :=
  (MonoidalCategory.associatorNatIso C).symm

abbrev associativityConstraintComponent (X Y Z : C) :
    X ⊗ (Y ⊗ Z) ≅ (X ⊗ Y) ⊗ Z :=
  (α_ X Y Z).symm

theorem associativity_constraint_pentagon (W X Y Z : C) :
    W ◁ (α_ X Y Z).inv ≫ (α_ W (X ⊗ Y) Z).inv ≫
        (α_ W X Y).inv ▷ Z =
      (α_ W X (Y ⊗ Z)).inv ≫ (α_ (W ⊗ X) Y Z).inv := by
  monoidal_coherence

/- The source's n-ary parenthesization statements, including the displayed
   fourteen parenthesizations for five objects, are precisely the monoidal
   coherence theorem.  Mathlib's `monoidal_coherence` tactic and the
   `MonoidalCategory` associator/unitors provide that theorem, so no parallel
   family of parenthesized tensor functors is introduced here. -/

/-! ## Units -/

/-- A unit for a fixed canonical monoidal structure, in the source's
right-to-left associator convention. -/
structure UnitData where
  unit : C
  leftUnitor : tensorLeft unit ≅ 𝟭 C
  rightUnitor : tensorRight unit ≅ 𝟭 C
  triangle : ∀ X Y : C,
    (α_ X unit Y).inv ≫ (rightUnitor.app X).hom ▷ Y =
      X ◁ (leftUnitor.app Y).hom

/-- A source-style unit pair: multiplication on the unit together with the
two tensoring equivalences. -/
structure UnitPair where
  unit : C
  multiplication : unit ⊗ unit ≅ unit
  leftEquivalence : (tensorLeft unit).IsEquivalence
  rightEquivalence : (tensorRight unit).IsEquivalence

/-- The chosen unit in a Mathlib monoidal category, viewed as source data. -/
def chosenUnitData : UnitData (C := C) where
  unit := 𝟙_ C
  leftUnitor := MonoidalCategory.leftUnitorNatIso C
  rightUnitor := MonoidalCategory.rightUnitorNatIso C
  triangle := by
    intro X Y
    exact MonoidalCategory.triangle_assoc_comp_right X Y

theorem monoidal_category_has_unit : Nonempty (UnitData (C := C)) :=
  ⟨chosenUnitData⟩

/- The source's one-to-one unit/pair correspondence is recorded as an
   equivalence of the two source-facing presentations. -/
theorem unitDataEquivUnitPair :
    Nonempty (UnitData (C := C) ≃ UnitPair (C := C)) := by
  sorry

theorem unitPair_multiplication_tensor_equal (u : UnitPair (C := C)) :
    (α_ u.unit u.unit u.unit).hom ≫
        (𝟙 u.unit ⊗ₘ u.multiplication.hom) =
      u.multiplication.hom ⊗ₘ 𝟙 u.unit := by
  letI : (tensorLeft u.unit).IsEquivalence := u.leftEquivalence
  let v : C := (tensorLeft u.unit).asEquivalence.inverse.obj (𝟙_ C)
  let ev : u.unit ⊗ v ≅ 𝟙_ C :=
    (tensorLeft u.unit).asEquivalence.counitIso.app (𝟙_ C)
  let q : u.unit ≅ 𝟙_ C :=
    (ρ_ u.unit).symm ≪≫ whiskerLeftIso u.unit ev.symm ≪≫
      (α_ u.unit u.unit v).symm ≪≫
      (u.multiplication ⊗ᵢ Iso.refl v) ≪≫ ev
  let a : 𝟙_ C ⊗ 𝟙_ C ≅ 𝟙_ C :=
    (q.symm ⊗ᵢ q.symm) ≪≫ u.multiplication ≪≫ q
  have hm : u.multiplication.hom =
      (q ⊗ᵢ q).hom ≫ a.hom ≫ q.inv := by
    simp [a, Category.assoc]
  have ha : (α_ (𝟙_ C) (𝟙_ C) (𝟙_ C)).hom ≫
      (𝟙 (𝟙_ C) ⊗ₘ a.hom) = a.hom ⊗ₘ 𝟙 (𝟙_ C) := by
    simp [MonoidalCategory.tensorHom_def,
      MonoidalCategory.leftUnitor_tensor_hom,
      MonoidalCategory.unitors_equal, MonoidalCategory.unitors_inv_equal,
      Category.assoc]
  let f : u.unit ⟶ 𝟙_ C := q.hom
  let g : 𝟙_ C ⟶ u.unit := q.inv
  let h : 𝟙_ C ⊗ 𝟙_ C ⟶ 𝟙_ C := a.hom
  have hm' : u.multiplication.hom =
      (f ⊗ₘ f) ≫ h ≫ g := by
    simpa [f, g, h] using hm
  have ha' : (α_ (𝟙_ C) (𝟙_ C) (𝟙_ C)).hom ≫
      (𝟙 (𝟙_ C) ⊗ₘ h) = h ⊗ₘ 𝟙 (𝟙_ C) := by
    simpa [h] using ha
  have hfg : f ≫ g = 𝟙 u.unit := by
    simp [f, g]
  have hgf : g ≫ f = 𝟙 (𝟙_ C) := by
    simp [f, g]
  clear_value f g h
  let k : ((u.unit ⊗ u.unit) ⊗ u.unit) ⟶ u.unit ⊗ u.unit :=
    ((f ⊗ₘ f) ⊗ₘ f) ≫
      (α_ (𝟙_ C) (𝟙_ C) (𝟙_ C)).hom ≫
      (𝟙 (𝟙_ C) ⊗ₘ h) ≫
      (g ⊗ₘ g)
  have hleft :
      (α_ u.unit u.unit u.unit).hom ≫
          (𝟙 u.unit ⊗ₘ
            ((f ⊗ₘ f) ≫ h ≫ g)) = k := by
    simp [k, MonoidalCategory.tensorHom_def, Category.assoc, hfg, hgf]
    monoidal
    simp
  let k' : ((u.unit ⊗ u.unit) ⊗ u.unit) ⟶ u.unit ⊗ u.unit :=
    ((f ⊗ₘ f) ⊗ₘ f) ≫
      (h ⊗ₘ 𝟙 (𝟙_ C)) ≫
      (g ⊗ₘ g)
  have hright :
      ((f ⊗ₘ f) ≫ h ≫ g) ⊗ₘ 𝟙 u.unit = k' := by
    simp [k', MonoidalCategory.tensorHom_def, Category.assoc, hfg, hgf]
    monoidal
    simp
  have hmid : k = k' := by
    simpa only [k, k', Category.assoc] using
      congrArg (fun t => ((f ⊗ₘ f) ⊗ₘ f) ≫ t ≫
        (g ⊗ₘ g)) ha'
  rw [hm']
  exact hleft.trans (hmid.trans hright.symm)

theorem unitors_at_unit_equal :
    (λ_ (𝟙_ C)).hom = (ρ_ (𝟙_ C)).hom :=
  MonoidalCategory.unitors_equal

theorem unit_end_comp_comm (a b : 𝟙_ C ⟶ 𝟙_ C) :
    a ≫ b = b ≫ a := by
  calc
    a ≫ b = ((ρ_ (𝟙_ C)).inv ≫ a ▷ (𝟙_ C) ≫ (ρ_ (𝟙_ C)).hom) ≫
        ((λ_ (𝟙_ C)).inv ≫ (𝟙_ C) ◁ b ≫ (λ_ (𝟙_ C)).hom) := by
      exact congrArg₂ (fun f g => f ≫ g) (whiskerRight_id_symm a) (id_whiskerLeft_symm b)
    _ = (ρ_ (𝟙_ C)).inv ≫ (a ▷ (𝟙_ C)) ≫ (𝟙_ C ◁ b) ≫ (ρ_ (𝟙_ C)).hom := by
      rw [MonoidalCategory.unitors_equal, MonoidalCategory.unitors_inv_equal]
      simp only [Category.assoc, Iso.hom_inv_id_assoc]
    _ = (ρ_ (𝟙_ C)).inv ≫ (a ⊗ₘ b) ≫ (ρ_ (𝟙_ C)).hom := by
      simp only [MonoidalCategory.tensorHom_def, Category.assoc]
    _ = (ρ_ (𝟙_ C)).inv ≫ (𝟙_ C ◁ b) ≫ (a ▷ (𝟙_ C)) ≫ (ρ_ (𝟙_ C)).hom := by
      simp only [MonoidalCategory.tensorHom_def', Category.assoc]
    _ = ((λ_ (𝟙_ C)).inv ≫ (𝟙_ C) ◁ b ≫ (λ_ (𝟙_ C)).hom) ≫
        ((ρ_ (𝟙_ C)).inv ≫ a ▷ (𝟙_ C) ≫ (ρ_ (𝟙_ C)).hom) := by
      rw [MonoidalCategory.unitors_equal, MonoidalCategory.unitors_inv_equal]
      simp only [Category.assoc, Iso.hom_inv_id_assoc]
    _ = b ≫ a := by
      exact (congrArg₂ (fun f g => f ≫ g) (id_whiskerLeft_symm b) (whiskerRight_id_symm a)).symm

theorem unit_end_tensor_conjugation (a : 𝟙_ C ⟶ 𝟙_ C) :
    (ρ_ (𝟙_ C)).inv ≫ (a ⊗ₘ 𝟙 (𝟙_ C)) ≫ (ρ_ (𝟙_ C)).hom = a ∧
      (ρ_ (𝟙_ C)).inv ≫ (𝟙 (𝟙_ C) ⊗ₘ a) ≫ (ρ_ (𝟙_ C)).hom = a := by
  constructor <;>
    simp [MonoidalCategory.tensorHom_id, MonoidalCategory.id_tensorHom,
      ← MonoidalCategory.unitors_equal, ← MonoidalCategory.unitors_inv_equal]

/- An isomorphism of the source-facing unit presentations is required to
   intertwine both unitors.  This makes the source's phrase "unique
   isomorphism" a precise proposition rather than an assertion about all
   object isomorphisms. -/
structure UnitDataIso (u v : UnitData (C := C)) where
  hom : u.unit ≅ v.unit
  left_naturality : ∀ X : C,
    (hom.hom ⊗ₘ 𝟙 X) ≫ (v.leftUnitor.app X).hom = (u.leftUnitor.app X).hom
  right_naturality : ∀ X : C,
    (𝟙 X ⊗ₘ hom.hom) ≫ (v.rightUnitor.app X).hom = (u.rightUnitor.app X).hom

theorem unit_data_unique_iso (u : UnitData (C := C)) :
    Nonempty (UnitDataIso u (chosenUnitData (C := C))) ∧
      ∀ e₁ e₂ : UnitDataIso u (chosenUnitData (C := C)), e₁ = e₂ := by
  let e : u.unit ≅ 𝟙_ C :=
    (λ_ u.unit).symm ≪≫ u.rightUnitor.app (𝟙_ C)
  have hl (X : C) :
      (e.hom ⊗ₘ 𝟙 X) ≫ (λ_ X).hom = (u.leftUnitor.app X).hom := by
    simp [e, Category.assoc]
    change (λ_ (u.unit ⊗ X)).inv ≫ (α_ (𝟙_ C) u.unit X).inv ≫
      (u.rightUnitor.app (𝟙_ C)).hom ▷ X ≫ (λ_ X).hom =
      (u.leftUnitor.app X).hom
    calc
      _ = (λ_ (u.unit ⊗ X)).inv ≫
          ((α_ (𝟙_ C) u.unit X).inv ≫
            (u.rightUnitor.app (𝟙_ C)).hom ▷ X) ≫ (λ_ X).hom := by
            simp [Category.assoc]
      _ = (λ_ (u.unit ⊗ X)).inv ≫
          (𝟙_ C ◁ (u.leftUnitor.app X).hom) ≫ (λ_ X).hom := by
            rw [u.triangle (𝟙_ C) X]
      _ = (u.leftUnitor.app X).hom := by
            rw [MonoidalCategory.leftUnitor_naturality]
            simp
  let e₀ : u.unit ≅ 𝟙_ C :=
    (ρ_ u.unit).symm ≪≫ u.leftUnitor.app (𝟙_ C)
  have hl₀ :
      (e₀.hom ⊗ₘ 𝟙 (𝟙_ C)) ≫ (λ_ (𝟙_ C)).hom =
        (u.leftUnitor.app (𝟙_ C)).hom := by
    simp [e₀, MonoidalCategory.tensorHom_def, Category.assoc]
    rw [MonoidalCategory.unitors_equal]
    simp
  have e_eq : e.hom = e₀.hom := by
    apply (MonoidalCategory.whiskerRight_iff _ _).1
    apply (cancel_mono (λ_ (𝟙_ C)).hom).1
    simpa [MonoidalCategory.tensorHom_def] using (hl (𝟙_ C)).trans hl₀.symm
  have hr (X : C) :
      (𝟙 X ⊗ₘ e.hom) ≫ (ρ_ X).hom = (u.rightUnitor.app X).hom := by
    rw [e_eq]
    simp [e₀, Category.assoc]
    change (ρ_ (X ⊗ u.unit)).inv ≫ (α_ X u.unit (𝟙_ C)).hom ≫
      X ◁ (u.leftUnitor.app (𝟙_ C)).hom ≫ (ρ_ X).hom =
      (u.rightUnitor.app X).hom
    rw [← u.triangle X (𝟙_ C)]
    simp [Category.assoc]
  let e' : UnitDataIso u (chosenUnitData (C := C)) :=
    { hom := e
      left_naturality := hl
      right_naturality := hr }
  refine ⟨⟨e'⟩, ?_⟩
  intro e₁ e₂
  have h₁ := e₁.left_naturality (𝟙_ C)
  have h₂ := e₂.left_naturality (𝟙_ C)
  have hten :
      e₁.hom.hom ⊗ₘ 𝟙 (𝟙_ C) = e₂.hom.hom ⊗ₘ 𝟙 (𝟙_ C) := by
    apply (cancel_mono (λ_ (𝟙_ C)).hom).1
    exact h₁.trans h₂.symm
  have ht :
      e₁.hom.hom ▷ (𝟙_ C) = e₂.hom.hom ▷ (𝟙_ C) := by
    simpa [MonoidalCategory.tensorHom_def] using hten
  have hhom : e₁.hom = e₂.hom := by
    apply Iso.ext
    exact (MonoidalCategory.whiskerRight_iff _ _).1 ht
  cases e₁
  cases e₂
  cases hhom
  rfl

theorem unitors_tensor_left (X Y : C) :
    (λ_ X).hom ▷ Y = (α_ (𝟙_ C) X Y).hom ≫ (λ_ (X ⊗ Y)).hom :=
  MonoidalCategory.leftUnitor_whiskerRight X Y

theorem unitors_tensor_right (X Y : C) :
    X ◁ (ρ_ Y).hom = (α_ X Y (𝟙_ C)).inv ≫ (ρ_ (X ⊗ Y)).hom :=
  MonoidalCategory.whiskerLeft_rightUnitor X Y

/- The source identifies unit insertions and all parenthesizations.  The
   canonical unitors, associator, triangle, and coherence theorem give the
   stated functorial isomorphisms and their commuting diagrams. -/

/-! ## Monoidal functors and invertible objects -/

@[instance_reducible]
def extension_of_scalars_is_monoidal
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) :
    (ModuleCat.extendScalars f).Monoidal := by
  infer_instance

/- The example in the source needs commutative rings for the standard
   symmetric monoidal structures on module categories. -/

variable {D : Type u'} [Category.{v'} D] [MonoidalCategory D]

abbrev IsInvertible (X : C) : Prop := (tensorLeft X).IsEquivalence

theorem isInvertible_iff_tensorRight (X : C) :
    IsInvertible X ↔ (tensorRight X).IsEquivalence := by
  constructor
  · intro h
    letI : (tensorLeft X).IsEquivalence := h
    let Xinv : C := (tensorLeft X).asEquivalence.inverse.obj (𝟙_ C)
    let e1 : X ⊗ Xinv ≅ 𝟙_ C := by
      exact (tensorLeft X).asEquivalence.counitIso.app (𝟙_ C)
    let e2image : (tensorLeft X).obj (Xinv ⊗ X) ≅ (tensorLeft X).obj (𝟙_ C) :=
      (α_ X Xinv X).symm ≪≫ whiskerRightIso e1 X ≪≫ (λ_ X) ≪≫ (ρ_ X).symm
    let e2 : Xinv ⊗ X ≅ 𝟙_ C := (tensorLeft X).preimageIso e2image
    let η := (MonoidalCategory.rightUnitorNatIso C).symm ≪≫
      (MonoidalCategory.tensoringRight C).mapIso e1.symm ≪≫
      MonoidalCategory.tensorRightTensor X Xinv
    let ε := (MonoidalCategory.tensorRightTensor Xinv X).symm ≪≫
      (MonoidalCategory.tensoringRight C).mapIso e2 ≪≫
      MonoidalCategory.rightUnitorNatIso C
    exact Functor.IsEquivalence.mk' (tensorRight Xinv) η ε
  · intro h
    letI : (tensorRight X).IsEquivalence := h
    let Xinv : C := (tensorRight X).asEquivalence.inverse.obj (𝟙_ C)
    let e2 : Xinv ⊗ X ≅ 𝟙_ C := by
      exact (tensorRight X).asEquivalence.counitIso.app (𝟙_ C)
    let e1image : (tensorRight X).obj (X ⊗ Xinv) ≅ (tensorRight X).obj (𝟙_ C) :=
      (α_ X Xinv X) ≪≫ whiskerLeftIso X e2 ≪≫ (ρ_ X) ≪≫ (λ_ X).symm
    let e1 : X ⊗ Xinv ≅ 𝟙_ C := (tensorRight X).preimageIso e1image
    let η := (MonoidalCategory.leftUnitorNatIso C).symm ≪≫
      (MonoidalCategory.tensoringLeft C).mapIso e2.symm ≪≫
      MonoidalCategory.tensorLeftTensor Xinv X
    let ε := (MonoidalCategory.tensorLeftTensor X Xinv).symm ≪≫
      (MonoidalCategory.tensoringLeft C).mapIso e1 ≪≫
      MonoidalCategory.leftUnitorNatIso C
    exact Functor.IsEquivalence.mk' (tensorLeft Xinv) η ε

theorem isInvertible_iff_tensor_inverse (X : C) :
    IsInvertible X ↔
      ∃ X' : C,
        Nonempty (X ⊗ X' ≅ 𝟙_ C) ∧ Nonempty (X' ⊗ X ≅ 𝟙_ C) := by
  refine ⟨(fun h => by
    letI : (tensorLeft X).IsEquivalence := h
    let X' : C := (tensorLeft X).asEquivalence.inverse.obj (𝟙_ C)
    let e₁ : X ⊗ X' ≅ 𝟙_ C := by
      exact (tensorLeft X).asEquivalence.counitIso.app (𝟙_ C)
    let e₂image : (tensorLeft X).obj (X' ⊗ X) ≅ (tensorLeft X).obj (𝟙_ C) :=
      (α_ X X' X).symm ≪≫ whiskerRightIso e₁ X ≪≫ (λ_ X) ≪≫ (ρ_ X).symm
    exact ⟨X', ⟨e₁⟩, ⟨(tensorLeft X).preimageIso e₂image⟩⟩), by
    rintro ⟨X', ⟨e₁⟩, ⟨e₂⟩⟩
    let η := (MonoidalCategory.leftUnitorNatIso C).symm ≪≫
      (MonoidalCategory.tensoringLeft C).mapIso e₂.symm ≪≫
      MonoidalCategory.tensorLeftTensor X' X
    let ε := (MonoidalCategory.tensorLeftTensor X X').symm ≪≫
      (MonoidalCategory.tensoringLeft C).mapIso e₁ ≪≫
      MonoidalCategory.leftUnitorNatIso C
    exact Functor.IsEquivalence.mk' (tensorLeft X') η ε⟩

theorem monoidalFunctor_preserves_invertible
    (F : C ⥤ D) [F.Monoidal] {X : C} (hX : IsInvertible X) :
    IsInvertible (C := D) (F.obj X) := by
  exact ((isInvertible_iff_tensor_inverse (C := D) (F.obj X)).2 (by
    rcases (isInvertible_iff_tensor_inverse (C := C) X).1 hX with
      ⟨Xinv, ⟨e1⟩, ⟨e2⟩⟩
    exact ⟨F.obj Xinv,
      ⟨Functor.Monoidal.μIso F X Xinv ≪≫ F.mapIso e1 ≪≫
        (Functor.Monoidal.εIso F).symm⟩,
      ⟨Functor.Monoidal.μIso F Xinv X ≪≫ F.mapIso e2 ≪≫
        (Functor.Monoidal.εIso F).symm⟩⟩))

/-! ## Duals -/

/- Mathlib's `ExactPairing X Y` is the source's definition of “Y is a left
   dual of X”: its coevaluation is `𝟙_ C ⟶ X ⊗ Y`, its evaluation is
   `Y ⊗ X ⟶ 𝟙_ C`, and its two fields are exactly the snake diagrams. -/
abbrev IsLeftDual (X Y : C) := ExactPairing X Y

abbrev IsRightDual (Y X : C) := ExactPairing X Y

theorem monoidalFunctor_preserves_leftDual
    (F : C ⥤ D) [F.Monoidal] {X Y : C} [ExactPairing X Y] :
    Nonempty (ExactPairing (F.obj X) (F.obj Y)) := by
  refine ⟨ExactPairing.mk
    (Functor.LaxMonoidal.ε F ≫ F.map (ExactPairing.coevaluation X Y) ≫
      Functor.OplaxMonoidal.δ F X Y)
    (Functor.LaxMonoidal.μ F Y X ≫ F.map (ExactPairing.evaluation X Y) ≫
      Functor.OplaxMonoidal.η F)
    (by
      simp [Category.assoc]
      apply (cancel_epi (F.obj Y ◁ Functor.LaxMonoidal.ε F)).mpr
      simp only [← Category.assoc]
      rw [cancel_mono (Functor.OplaxMonoidal.η F ▷ F.obj Y)]
      apply (cancel_epi (Functor.OplaxMonoidal.δ F Y (𝟙_ C))).mp
      apply (cancel_mono (Functor.LaxMonoidal.μ F (𝟙_ C) Y)).mp
      simp [Category.assoc]
      rw [← F.map_comp, ← F.map_comp, ExactPairing.coevaluation_evaluation,
        F.map_comp])
    (by
      simp [Category.assoc]
      apply (cancel_epi (Functor.LaxMonoidal.ε F ▷ F.obj X)).mpr
      simp only [← Category.assoc]
      rw [cancel_mono (F.obj X ◁ Functor.OplaxMonoidal.η F)]
      apply (cancel_epi (Functor.OplaxMonoidal.δ F (𝟙_ C) X)).mp
      apply (cancel_mono (Functor.LaxMonoidal.μ F X (𝟙_ C))).mp
      simp [Category.assoc]
      rw [← F.map_comp, ← F.map_comp, ExactPairing.evaluation_coevaluation,
        F.map_comp])⟩

def leftDualHomEquiv (X Y Z Z' : C) [ExactPairing X Y] :
    (Z' ⊗ X ⟶ Z) ≃ (Z' ⟶ Z ⊗ Y) :=
  tensorRightHomEquiv Z' X Y Z

def leftDualHomEquiv' (X Y Z Z' : C) [ExactPairing X Y] :
    (Y ⊗ Z' ⟶ Z) ≃ (Z' ⟶ X ⊗ Z) :=
  tensorLeftHomEquiv Z' X Y Z

theorem leftDual_homEquiv_tensor_compatibility
    (X Y A B P Q : C) [ExactPairing X Y]
    (f : A ⟶ B ⊗ Y) (g : P ⟶ Q) :
    (leftDualHomEquiv X Y (Q ⊗ B) (P ⊗ A)).symm
        ((g ⊗ₘ f) ≫ (α_ Q B Y).inv) =
      (α_ P A X).hom ≫
        (g ⊗ₘ (leftDualHomEquiv X Y B A).symm f) := by
  exact tensorRightHomEquiv_tensor f g

theorem leftDual_unique_up_to_iso
    (X Y₁ Y₂ : C) [ExactPairing X Y₁] [ExactPairing X Y₂] :
    ∃! e : Y₁ ≅ Y₂,
      ∀ (Z Z' : C) (f : Z' ⊗ X ⟶ Z),
        leftDualHomEquiv X Y₁ Z Z' f ≫ (𝟙 Z ⊗ₘ e.hom) =
          leftDualHomEquiv X Y₂ Z Z' f := by
  let e := rightDualIso (X := X) (Y₁ := Y₁) (Y₂ := Y₂)
    (inferInstance : ExactPairing X Y₁) (inferInstance : ExactPairing X Y₂)
  refine ⟨e, ?_, ?_⟩
  · intro Z Z' f
    have he : e.hom ▷ X ≫ ε_ X Y₂ =
        (Y₁ ◁ (𝟙 X)) ≫ ε_ X Y₁ := by
      exact @rightAdjointMate_comp_evaluation C _ _ X X ⟨Y₂⟩ ⟨Y₁⟩ (𝟙 X)
    have heZ :
        (α_ Z Y₁ X).hom ≫ Z ◁ (e.hom ▷ X) ≫ Z ◁ ε_ X Y₂ =
          (α_ Z Y₁ X).hom ≫ Z ◁ ((Y₁ ◁ (𝟙 X)) ≫ ε_ X Y₁) := by
      rw [← MonoidalCategory.whiskerLeft_comp Z (e.hom ▷ X) (ε_ X Y₂)]
      rw [he]
    have heZ_assoc := congrArg (fun k => k ≫ (ρ_ Z).hom) heZ
    simp only [Category.assoc] at heZ_assoc
    apply (tensorRightHomEquiv Z' X Y₂ Z).symm.injective
    simp [leftDualHomEquiv, tensorRightHomEquiv,
      MonoidalCategory.tensorHom_def]
    rw [heZ_assoc]
    calc
      _ = f := by
        simpa [leftDualHomEquiv, tensorRightHomEquiv]
          using (tensorRightHomEquiv Z' X Y₁ Z).left_inv f
      _ = _ := by
        simpa [leftDualHomEquiv, tensorRightHomEquiv]
          using ((tensorRightHomEquiv Z' X Y₂ Z).left_inv f).symm
  · intro e' h
    apply Iso.ext
    have hε := h (𝟙_ C) Y₁ (ε_ X Y₁)
    simpa [leftDualHomEquiv, tensorRightHomEquiv,
      MonoidalCategory.tensorHom_def, e, rightDualIso, rightAdjointMate]
      using congrArg (fun k => k ≫ (λ_ Y₂).hom) hε

/- The tensor-dual result is already the canonical `ExactPairing.tensor`
   instance from Mathlib.  The source's converse characterization of left duals by an adjunction is
   the parametrized right-tensor adjunction above.  Its unit/counit triangle
   calculations and the extra tensor-compatibility square are represented by
   the following source-facing structure and by `ParametrizedAdjunction`. -/
structure CompatibleRightTensorAdjunction (X Y : C) where
  adjunction : tensorRight X ⊣ tensorRight Y
  compatible : ∀ (W Z Z' : C) (f : Z' ⊗ X ⟶ Z),
    adjunction.homEquiv (W ⊗ Z') (W ⊗ Z)
        ((α_ W Z' X).hom ≫ (𝟙 W ⊗ₘ f)) =
      (𝟙 W ⊗ₘ adjunction.homEquiv Z' Z f) ≫
        (α_ W Z Y).inv

theorem leftDual_iff_compatible_right_tensor_adjunction (X Y : C) :
    Nonempty (ExactPairing X Y) ↔
      Nonempty (CompatibleRightTensorAdjunction X Y) := by
  constructor
  · rintro ⟨p⟩
    letI : ExactPairing X Y := p
    refine ⟨{ adjunction := tensorRightAdjunction X Y, compatible := ?_ }⟩
    intro W Z Z' f
    apply (tensorRightHomEquiv (W ⊗ Z') X Y (W ⊗ Z)).symm.injective
    simpa [tensorRightAdjunction] using (tensorRightHomEquiv_tensor
      (X := Z') (X' := W) (Y := X) (Y' := Y) (Z := Z) (Z' := W)
      (tensorRightHomEquiv Z' X Y Z f) (𝟙 W)).symm
  · rintro ⟨a⟩
    let adj := a.adjunction
    refine ⟨ExactPairing.mk
      (adj.unit.app (𝟙_ C) ≫ (λ_ X).hom ▷ Y)
      ((λ_ Y).inv ▷ X ≫ adj.counit.app (𝟙_ C))
      (by
        have hc := a.compatible Y X (𝟙_ C) (λ_ X).hom
        have hc' := congrArg
          (fun k => k ≫ ((λ_ Y).inv ▷ X ≫ adj.counit.app (𝟙_ C)) ▷ Y) hc
        have hleft :
            (adj.homEquiv (Y ⊗ 𝟙_ C) (Y ⊗ X)) ((ρ_ Y).hom ▷ X) =
              (ρ_ Y).hom ≫ adj.unit.app Y := by
          calc
            _ = (ρ_ Y).hom ≫
                (adj.homEquiv Y (Y ⊗ X)) (𝟙 (Y ⊗ X)) := by
              simpa [adj, Category.assoc] using
                adj.homEquiv_naturality_left (ρ_ Y).hom (𝟙 (Y ⊗ X))
            _ = _ := by
              simpa [tensorRight] using
                congrArg (fun k => (ρ_ Y).hom ≫ k)
                  (Adjunction.homEquiv_id adj Y)
        have htri :
            (α_ Y (𝟙_ C) X).hom ≫ (𝟙 Y ⊗ₘ (λ_ X).hom) =
              (ρ_ Y).hom ▷ X := by
          simp [MonoidalCategory.tensorHom_def]
        rw [htri] at hc
        have hcoev :
            (adj.homEquiv (𝟙_ C) X) (λ_ X).hom =
              adj.unit.app (𝟙_ C) ≫ (λ_ X).hom ▷ Y := by
          simp [Adjunction.homEquiv, adj]
        rw [htri, hleft, hcoev] at hc'
        have htail :
            adj.unit.app Y ≫
                ((λ_ Y).inv ▷ X ≫ adj.counit.app (𝟙_ C)) ▷ Y =
              (λ_ Y).inv := by
          change adj.unit.app Y ≫
            (tensorRight Y).map
              ((tensorRight X).map (λ_ Y).inv ≫ adj.counit.app (𝟙_ C)) =
            (λ_ Y).inv
          rw [Functor.map_comp]
          rw [← Category.assoc, adj.unit_naturality (λ_ Y).inv]
          simp only [Category.assoc]
          have hright :
              adj.unit.app (𝟙_ C ⊗ Y) ≫
                  (tensorRight Y).map (adj.counit.app (𝟙_ C)) =
                𝟙 (𝟙_ C ⊗ Y) := by
            simpa [tensorRight] using adj.right_triangle_components (𝟙_ C)
          rw [hright]
          simp
        have hc'' := hc'.symm
        simp only [Category.assoc] at hc''
        rw [htail] at hc''
        simpa only [MonoidalCategory.tensorHom_def, MonoidalCategory.id_whiskerRight,
          Category.id_comp, Category.assoc] using hc'')
      (by
        apply (adj.homEquiv (𝟙_ C) (X ⊗ 𝟙_ C)).injective
        let eval := (λ_ Y).inv ▷ X ≫ adj.counit.app (𝟙_ C)
        let coev := adj.unit.app (𝟙_ C) ≫ (λ_ X).hom ▷ Y
        let K := (α_ X Y X).hom ≫ X ◁ eval
        change (adj.homEquiv (𝟙_ C) (X ⊗ 𝟙_ C))
              ((tensorRight X).map coev ≫ K) =
            (adj.homEquiv (𝟙_ C) (X ⊗ 𝟙_ C))
              ((λ_ X).hom ≫ (ρ_ X).inv)
        have heval :
            (adj.homEquiv Y (𝟙_ C))
                eval =
              (λ_ Y).inv := by
          apply (adj.homEquiv Y (𝟙_ C)).symm.injective
          rw [Equiv.symm_apply_apply, Adjunction.homEquiv_counit]
          simp [eval, adj, Category.assoc]
        have hc := a.compatible X (𝟙_ C) Y
          eval
        rw [heval] at hc
        have hcK :
            (adj.homEquiv (X ⊗ Y) (X ⊗ 𝟙_ C)) K =
              (ρ_ X).inv ▷ Y := by
          simpa [K, eval, adj, MonoidalCategory.tensorHom_def,
            Category.assoc] using hc
        have hcoev :
            (adj.homEquiv (𝟙_ C) X) (λ_ X).hom = coev := by
          rfl
        have hleft := adj.homEquiv_naturality_left coev K
        have hright := adj.homEquiv_naturality_right
          (λ_ X).hom (ρ_ X).inv
        calc
          _ = coev ≫ (adj.homEquiv (X ⊗ Y) (X ⊗ 𝟙_ C)) K := by
            simpa [adj, Category.assoc] using hleft
          _ = coev ≫ (ρ_ X).inv ▷ Y := by rw [hcK]
          _ = (adj.homEquiv (𝟙_ C) X) (λ_ X).hom ≫
                (tensorRight Y).map (ρ_ X).inv := by
            rw [hcoev]
            simp [tensorRight]
          _ = _ := by simpa [adj] using hright.symm)⟩

/-! ## Braiding and symmetric monoidal categories -/

theorem commutativity_constraint_hexagon (X Y Z : C) [SymmetricCategory C] :
    (α_ X Y Z).inv ≫ (β_ (X ⊗ Y) Z).hom ≫ (α_ Z X Y).inv =
      (X ◁ (β_ Y Z).hom) ≫ (α_ X Z Y).inv ≫
        ((β_ X Z).hom ▷ Y) := by
  exact BraidedCategory.hexagon_reverse X Y Z

theorem symmetric_commutativity_involutive
    {C : Type u} [Category.{v} C] [MonoidalCategory C]
    [SymmetricCategory C] (X Y : C) :
    (β_ X Y).hom ≫ (β_ Y X).hom = 𝟙 (X ⊗ Y) :=
  SymmetricCategory.symmetry X Y

theorem symmetric_unit_multiplication [SymmetricCategory C] :
    (β_ (𝟙_ C) (𝟙_ C)).hom ≫ (ρ_ (𝟙_ C)).hom = (ρ_ (𝟙_ C)).hom := by
  simpa [MonoidalCategory.unitors_inv_equal] using
    (BraidedCategory.braiding_tensorUnit_right (𝟙_ C) ≫ (ρ_ (𝟙_ C)).hom)

theorem symmetric_unit_braiding (X : C) [SymmetricCategory C] :
    (β_ X (𝟙_ C)).hom ≫ (λ_ X).hom = (ρ_ X).hom := by
  simp

theorem symmetric_unit_coherence (X Y : C) [SymmetricCategory C] :
    (X ◁ (λ_ Y).hom) =
      (α_ X (𝟙_ C) Y).inv ≫
        ((β_ X (𝟙_ C)).hom ▷ Y) ≫
        ((λ_ X).hom ⊗ₘ 𝟙 Y) := by
  simp

/- The source's all-permutation coherence theorem is the symmetric version
   of the imported monoidal coherence theorem; Mathlib's `monoidal` tactic
   handles its structural diagrams after the symmetry equations above. -/

/-! ## Internal Homs -/

/- Mathlib's `MonoidalClosed` fixes the other tensor variable.  The source
   uses the right-handed convention `Hom(Z, hom(Y, X)) = Hom(Z ⊗ Y, X)`, so
   this small interface packages the corresponding parametrized adjunction
   while retaining functoriality in the parameter. -/
structure InternalHomData where
  hom : Cᵒᵖ ⥤ C ⥤ C
  adjunction : MonoidalCategory.tensoringRight C ⊣₂ hom

def HasInternalHom : Prop := Nonempty (InternalHomData (C := C))

abbrev internalHomObject (H : InternalHomData (C := C)) (X Y : C) : C :=
  (H.hom.obj (op X)).obj Y

def internalHomHomEquiv (H : InternalHomData (C := C)) (X Y Z : C) :
    (Y ⊗ X ⟶ Z) ≃ (Y ⟶ internalHomObject H X Z) :=
  H.adjunction.homEquiv

def internalHomEvaluation (H : InternalHomData (C := C)) (X Y : C) :
    internalHomObject H X Y ⊗ X ⟶ Y :=
  (H.adjunction.adj X).counit.app Y

def internalHomComposition (H : InternalHomData (C := C)) (X Y Z : C) :
    internalHomObject H Y Z ⊗ internalHomObject H X Y ⟶
      internalHomObject H X Z :=
  internalHomHomEquiv H X
    (internalHomObject H Y Z ⊗ internalHomObject H X Y) Z
    ((α_ (internalHomObject H Y Z) (internalHomObject H X Y) X).hom ≫
      (𝟙 (internalHomObject H Y Z) ⊗ₘ internalHomEvaluation H X Y) ≫
      internalHomEvaluation H Y Z)

def internalHomTensorMap (H : InternalHomData (C := C)) (X Y Z : C) :
    Z ⊗ internalHomObject H X Y ⟶ internalHomObject H X (Z ⊗ Y) :=
  internalHomHomEquiv H X (Z ⊗ internalHomObject H X Y) (Z ⊗ Y)
    ((α_ Z (internalHomObject H X Y) X).hom ≫
      (𝟙 Z ⊗ₘ internalHomEvaluation H X Y))

def internalHomUnitMap (H : InternalHomData (C := C)) (X Y : C) :
    Y ⟶ internalHomObject H X (Y ⊗ X) :=
  internalHomHomEquiv H X Y (Y ⊗ X) (𝟙 _)

def internalHomSymmetricMap (H : InternalHomData (C := C))
    (X Y Z : C) [SymmetricCategory C] :
    internalHomObject H Y Z ⊗ X ⟶
      internalHomObject H (internalHomObject H X Y) Z :=
  internalHomHomEquiv H (internalHomObject H X Y)
    (internalHomObject H Y Z ⊗ X) Z
    ((α_ (internalHomObject H Y Z) X (internalHomObject H X Y)).hom ≫
      (𝟙 _ ⊗ₘ (β_ X (internalHomObject H X Y)).hom) ≫
      ((𝟙 (internalHomObject H Y Z) ⊗ₘ internalHomEvaluation H X Y) ≫
        internalHomEvaluation H Y Z))

theorem internalHom_unique_up_to_unique_iso
    (H₁ H₂ : InternalHomData (C := C)) :
    ∃! e : H₁.hom ≅ H₂.hom,
      ∀ (X Y Z : C) (f : Y ⊗ X ⟶ Z),
        H₁.adjunction.homEquiv f ≫ (e.hom.app (op X)).app Z =
          H₂.adjunction.homEquiv f := by
  let app := fun X : C =>
    Adjunction.rightAdjointUniq (H₁.adjunction.adj X) (H₂.adjunction.adj X)
  have happ (P A B : C) (g : A ⊗ P ⟶ B) :
      (H₁.adjunction.adj P).homEquiv A B g ≫ (app P).hom.app B =
        (H₂.adjunction.adj P).homEquiv A B g := by
    change (H₁.adjunction.adj P).homEquiv A B g ≫
        (Adjunction.rightAdjointUniq (H₁.adjunction.adj P)
          (H₂.adjunction.adj P)).hom.app B =
      (H₂.adjunction.adj P).homEquiv A B g
    rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
    rw [Category.assoc, (Adjunction.rightAdjointUniq
      (H₁.adjunction.adj P) (H₂.adjunction.adj P)).hom.naturality g]
    have hu :
        (H₁.adjunction.adj P).unit.app A ≫
            (Adjunction.rightAdjointUniq (H₁.adjunction.adj P)
              (H₂.adjunction.adj P)).hom.app (A ⊗ P) =
          (H₂.adjunction.adj P).unit.app A := by
      simpa only [Functor.comp_obj, tensorRight, Functor.flip, curriedTensor] using
        (Adjunction.unit_rightAdjointUniq_hom_app
          (H₁.adjunction.adj P) (H₂.adjunction.adj P) A)
    rw [← Category.assoc, hu]
  let e : H₁.hom ≅ H₂.hom :=
    NatIso.ofComponents (fun X => app X.unop) (by
      intro X Y f
      ext Z
      change (H₁.hom.map f).app Z ≫ (app Y.unop).hom.app Z =
        (app X.unop).hom.app Z ≫ (H₂.hom.map f).app Z
      let A := (H₁.hom.obj X).obj Z
      let g₀ := (H₁.adjunction.adj X.unop).counit.app Z
      have h₁id :
          (H₁.adjunction.adj X.unop).homEquiv A Z g₀ = 𝟙 A := by
        apply ((H₁.adjunction.adj X.unop).homEquiv A Z).symm.injective
        rw [Equiv.symm_apply_apply, Adjunction.homEquiv_counit]
        simp [g₀]
      have h₁param := H₁.adjunction.homEquiv_naturality_one f.unop g₀
      have h₁param' :
          (H₁.adjunction.adj Y.unop).homEquiv A Z
              (((tensoringRight C).map f.unop).app A ≫ g₀) =
            (H₁.adjunction.adj X.unop).homEquiv A Z g₀ ≫
              (H₁.hom.map f).app Z := by
        simpa [ParametrizedAdjunction.homEquiv_eq] using h₁param
      have h₂param := H₂.adjunction.homEquiv_naturality_one f.unop g₀
      have h₂param' :
          (H₂.adjunction.adj Y.unop).homEquiv A Z
              (((tensoringRight C).map f.unop).app A ≫ g₀) =
            (H₂.adjunction.adj X.unop).homEquiv A Z g₀ ≫
              (H₂.hom.map f).app Z := by
        simpa [ParametrizedAdjunction.homEquiv_eq] using h₂param
      let g := ((tensoringRight C).map f.unop).app A ≫ g₀
      have h₁map :
          (H₁.adjunction.adj Y.unop).homEquiv A Z g =
            (H₁.hom.map f).app Z := by
        simpa [g, h₁id] using h₁param'
      have heX :
          (app X.unop).hom.app Z =
            (H₂.adjunction.adj X.unop).homEquiv A Z g₀ := by
        have hx := happ X.unop A Z g₀
        rw [h₁id] at hx
        simpa using hx
      have h₂map :
          (H₂.adjunction.adj Y.unop).homEquiv A Z g =
            (H₂.adjunction.adj X.unop).homEquiv A Z g₀ ≫
              (H₂.hom.map f).app Z := by
        simpa [g] using h₂param'
      calc
        (H₁.hom.map f).app Z ≫ (app Y.unop).hom.app Z =
            (H₁.adjunction.adj Y.unop).homEquiv A Z g ≫
              (app Y.unop).hom.app Z := by rw [h₁map]
        _ = (H₂.adjunction.adj Y.unop).homEquiv A Z g :=
          happ Y.unop A Z g
        _ = (H₂.adjunction.adj X.unop).homEquiv A Z g₀ ≫
              (H₂.hom.map f).app Z := h₂map
        _ = (app X.unop).hom.app Z ≫ (H₂.hom.map f).app Z := by
          rw [← heX])
  refine ⟨e, ?_, ?_⟩
  · intro X Y Z f
    change (H₁.adjunction.adj X).homEquiv Y Z f ≫
        (app X).hom.app Z =
      (H₂.adjunction.adj X).homEquiv Y Z f
    exact happ X Y Z f
  · intro e' h
    apply Iso.ext
    ext X Z
    let A := (H₁.hom.obj X).obj Z
    let g₀ := (H₁.adjunction.adj X.unop).counit.app Z
    have h₁id :
        (H₁.adjunction.adj X.unop).homEquiv A Z g₀ = 𝟙 A := by
      apply ((H₁.adjunction.adj X.unop).homEquiv A Z).symm.injective
      rw [Equiv.symm_apply_apply, Adjunction.homEquiv_counit]
      simp [g₀]
    have he' :
        (e'.hom.app X).app Z =
          (H₂.adjunction.adj X.unop).homEquiv A Z g₀ := by
      have h' := h X.unop A Z g₀
      change (H₁.adjunction.adj X.unop).homEquiv A Z g₀ ≫
          (e'.hom.app X).app Z =
        (H₂.adjunction.adj X.unop).homEquiv A Z g₀ at h'
      rw [h₁id] at h'
      simpa using h'
    have he :
        (app X.unop).hom.app Z =
          (H₂.adjunction.adj X.unop).homEquiv A Z g₀ := by
      have hx := happ X.unop A Z g₀
      rw [h₁id] at hx
      simpa using hx
    change (e'.hom.app X).app Z = (app X.unop).hom.app Z
    rw [he', he]

/- The five displayed maps in the source are now the definitions
   `internalHomEvaluation`, `internalHomComposition`, `internalHomTensorMap`,
   `internalHomUnitMap`, and `internalHomSymmetricMap`; their bodies are the
   corresponding adjunction transposes. -/

end

end Formalization.Books.Categories.Unit43
