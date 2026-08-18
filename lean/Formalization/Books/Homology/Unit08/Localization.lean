import Formalization.Books.Categories.Unit27.Localization
import Formalization.Books.Homology.Unit03.PreadditiveAndAdditiveCategories
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Localization.CalculusOfFractions.Preadditive
import Mathlib.CategoryTheory.Preadditive.Opposite
import Mathlib.CategoryTheory.Preadditive.Transfer
import Mathlib.CategoryTheory.Limits.ExactFunctor
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

/-!
# Homological Algebra, Chapter 8: Localization

This file records the statements in the `Localization` section of
*Homological Algebra*.  The calculus-of-fractions declarations from
`Formalization.Books.Categories.Unit27.Localization` and Mathlib's canonical
preadditive localization construction are reused throughout.  In particular,
the common-denominator identities and their duals used in the source proof
are already available as `exists_common_left_denominator`,
`left_fraction_eq_iff_postcomp`, `left_fraction_comp`, and the corresponding
right-fraction declarations.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open Formalization.Books.Categories.Unit27

universe v u

namespace Formalization.Books.Homology.Unit08

/-! ## Preadditive and additive localizations -/

/- Mathlib constructs the canonical structure in the left-calculus case. -/
theorem localization_preadditive_left
    {C : Type u} {D : Type*} [Category.{v} C] [Category* D]
    [Preadditive C] {W : MorphismProperty C} (L : C ⥤ D)
    [L.IsLocalization W] [hW : LeftMultiplicativeSystem W] :
    ∃! p : Preadditive D, @Functor.Additive C D _ _ _ p L := by
  refine ⟨CategoryTheory.Localization.preadditive L W, ?_, ?_⟩
  · exact CategoryTheory.Localization.functor_additive L W
  · intro p hp
    apply Preadditive.ext; funext X Y; apply AddCommGroup.ext; funext f g
    letI : L.EssSurj := CategoryTheory.Localization.essSurj L W
    let eX := L.objObjPreimageIso X
    let eY := L.objObjPreimageIso Y
    let u := eX.hom ≫ f ≫ eY.inv
    let v := eX.hom ≫ g ≫ eY.inv
    obtain ⟨φ, hu, hv⟩ := CategoryTheory.Localization.exists_leftFraction₂ L W u v
    letI : Preadditive D := p
    letI : Functor.Additive L := hp
    have hfp : f + g =
        eX.inv ≫ φ.add.map L (CategoryTheory.Localization.inverts L W) ≫ eY.hom := by
      calc
        f + g = (eX.inv ≫ u ≫ eY.hom) +
            (eX.inv ≫ v ≫ eY.hom) := by simp [u, v, Category.assoc]
        _ = eX.inv ≫ (u + v) ≫ eY.hom := by
          simp only [Preadditive.comp_add, Preadditive.add_comp, Category.assoc]
        _ = eX.inv ≫ φ.add.map L (CategoryTheory.Localization.inverts L W) ≫ eY.hom := by
          rw [hu, hv, ← MorphismProperty.LeftFraction₂.map_add]
    let q := CategoryTheory.Localization.preadditive L W
    letI : Preadditive D := q
    letI : Functor.Additive L := CategoryTheory.Localization.functor_additive L W
    have hq : f + g =
        eX.inv ≫ φ.add.map L (CategoryTheory.Localization.inverts L W) ≫ eY.hom := by
      calc
        f + g = (eX.inv ≫ u ≫ eY.hom) +
            (eX.inv ≫ v ≫ eY.hom) := by simp [u, v, Category.assoc]
        _ = eX.inv ≫ (u + v) ≫ eY.hom := by
          simp only [Preadditive.comp_add, Preadditive.add_comp, Category.assoc]
        _ = eX.inv ≫ φ.add.map L (CategoryTheory.Localization.inverts L W) ≫ eY.hom := by
          rw [hu, hv, ← MorphismProperty.LeftFraction₂.map_add]
    exact hfp.trans hq.symm

/- The right-calculus statement is the dual part of the source lemma. -/
theorem localization_preadditive_right
    {C : Type u} {D : Type*} [Category.{v} C] [Category* D]
    [Preadditive C] {W : MorphismProperty C} (L : C ⥤ D)
    [L.IsLocalization W] (hW : RightMultiplicativeSystem W) :
    ∃! p : Preadditive D, @Functor.Additive C D _ _ _ p L := by
  letI : RightMultiplicativeSystem W := hW
  let pop := CategoryTheory.Localization.preadditive L.op W.op
  letI : Preadditive Dᵒᵖ := pop
  let hFF := Functor.FullyFaithful.ofFullyFaithful (opOp D)
  let pD := Preadditive.ofFullyFaithful hFF
  letI : Preadditive D := pD
  have hpop : (@CategoryTheory.instPreadditiveOpposite D _ pD) = pop := by
    apply Preadditive.ext; funext X Y; apply AddCommGroup.ext; funext f g
    apply Quiver.Hom.unop_inj
    rw [unop_add]
    apply hFF.homEquiv.injective
    simp only [pD, Equiv.add_def]
    apply (opEquiv _ _).injective
    rw [Equiv.apply_symm_apply]
    change f + g = f + g
    rfl
  refine ⟨pD, ?_, ?_⟩
  · constructor
    intro X Y f g
    apply Quiver.Hom.op_inj
    rw [op_add]
    rw [hpop]
    letI : Functor.Additive L.op := CategoryTheory.Localization.functor_additive L.op W.op
    have h := Functor.Additive.map_add (F := L.op) (f := f.op) (g := g.op)
    simpa only [Functor.op_map, unop_add, Quiver.Hom.unop_op] using h
  · intro q hq
    letI : Preadditive D := q
    letI : Functor.Additive L := hq
    letI : Preadditive Dᵒᵖ := @CategoryTheory.instPreadditiveOpposite D _ q
    letI : W.op.HasLeftCalculusOfFractions := inferInstance
    have hopq : Functor.Additive L.op := by infer_instance
    obtain ⟨p', hp', huniq⟩ :=
      localization_preadditive_left (W := W.op) L.op
    have hqop : (@CategoryTheory.instPreadditiveOpposite D _ q) = p' :=
      huniq (@CategoryTheory.instPreadditiveOpposite D _ q) hopq
    have hpop' : p' = pop := by
      symm
      apply huniq
      exact CategoryTheory.Localization.functor_additive L.op W.op
    have hqpdop :
        (@CategoryTheory.instPreadditiveOpposite D _ q) =
          @CategoryTheory.instPreadditiveOpposite D _ pD :=
      hqop.trans (hpop'.trans hpop.symm)
    apply Preadditive.ext; funext X Y; apply AddCommGroup.ext; funext f g
    apply Quiver.Hom.op_inj
    change
      ((@CategoryTheory.instPreadditiveOpposite D _ q).homGroup
          (Opposite.op Y) (Opposite.op X)).add f.op g.op =
        ((@CategoryTheory.instPreadditiveOpposite D _ pD).homGroup
          (Opposite.op Y) (Opposite.op X)).add f.op g.op
    exact congrArg (fun r : Preadditive Dᵒᵖ =>
      (r.homGroup (Opposite.op Y) (Opposite.op X)).add f.op g.op) hqpdop

theorem localization_preadditive
    {C : Type u} {D : Type*} [Category.{v} C] [Category* D]
    [Preadditive C] {W : MorphismProperty C} (L : C ⥤ D)
    [L.IsLocalization W]
    (hW : LeftMultiplicativeSystem W ∨ RightMultiplicativeSystem W) :
    ∃! p : Preadditive D, @Functor.Additive C D _ _ _ p L := by
  rcases hW with hW | hW
  · letI : LeftMultiplicativeSystem W := hW
    exact localization_preadditive_left (W := W) L
  · exact localization_preadditive_right (W := W) L hW

theorem localization_additive_left
    {C : Type u} {D : Type*} [Category.{v} C] [Category* D]
    [Formalization.Books.Homology.Unit03.AdditiveCategory C]
    {W : MorphismProperty C} (L : C ⥤ D)
    [L.IsLocalization W] [hW : LeftMultiplicativeSystem W] :
    ∃ hD : Formalization.Books.Homology.Unit03.AdditiveCategory D,
      @Functor.Additive C D _ _ _ hD.toPreadditive L := by
  obtain ⟨p, hp, _⟩ :=
    localization_preadditive_left (W := W) L
  letI : Preadditive D := p
  letI : Functor.Additive L := hp
  letI : L.EssSurj := CategoryTheory.Localization.essSurj L W
  have hprod : HasFiniteProducts D :=
    Functor.hasFiniteProducts_of_additive_of_essSurj L
  let hD : Formalization.Books.Homology.Unit03.AdditiveCategory D :=
    { toPreadditive := p
      toHasFiniteProducts := hprod }
  exact ⟨hD, hp⟩

theorem localization_additive_right
    {C : Type u} {D : Type*} [Category.{v} C] [Category* D]
    [Formalization.Books.Homology.Unit03.AdditiveCategory C]
    {W : MorphismProperty C} (L : C ⥤ D)
    [L.IsLocalization W] [hW : RightMultiplicativeSystem W] :
    ∃ hD : Formalization.Books.Homology.Unit03.AdditiveCategory D,
      @Functor.Additive C D _ _ _ hD.toPreadditive L := by
  sorry

theorem localization_additive
    {C : Type u} {D : Type*} [Category.{v} C] [Category* D]
    [Formalization.Books.Homology.Unit03.AdditiveCategory C]
    {W : MorphismProperty C} (L : C ⥤ D)
    [L.IsLocalization W]
    (hW : LeftMultiplicativeSystem W ∨ RightMultiplicativeSystem W) :
    ∃ hD : Formalization.Books.Homology.Unit03.AdditiveCategory D,
      @Functor.Additive C D _ _ _ hD.toPreadditive L := by
  sorry

/-! ## The kernel of the localization functor -/

/- `IsZero (L.obj X)` is the canonical categorical formulation of the source's
  assertion `Q(X) = 0`; in an additive category it is equivalent to equality
  with the chosen zero object. -/
theorem localization_zero_iff
    {C : Type u} {D : Type*} [Category.{v} C] [Category* D]
    [Formalization.Books.Homology.Unit03.AdditiveCategory C]
    {W : MorphismProperty C} (L : C ⥤ D)
    [L.IsLocalization W]
    (hW : MultiplicativeSystem W) (X : C) :
    (IsZero (L.obj X) ↔ ∃ Y : C, W (0 : X ⟶ Y)) ∧
      (IsZero (L.obj X) ↔ ∃ Z : C, W (0 : Z ⟶ X)) := by
  sorry

/-! ## Kernels, cokernels, and exactness -/

/- `PreservesColimit (parallelPair f 0) L` and
  `PreservesLimit (parallelPair f 0) L` express that `L` commutes with the
  corresponding cokernel and kernel, respectively. -/
theorem localization_has_cokernels_of_left
    {C : Type u} {D : Type*} [Category.{v} C] [Category* D]
    [Abelian C] {W : MorphismProperty C} (L : C ⥤ D)
    [L.IsLocalization W] (hW : LeftMultiplicativeSystem W) :
    ∃ hD : Formalization.Books.Homology.Unit03.AdditiveCategory D,
      HasCokernels D ∧
        ∀ {X Y : C} (f : X ⟶ Y),
          PreservesColimit (parallelPair f 0) L := by
  sorry

theorem localization_has_kernels_of_right
    {C : Type u} {D : Type*} [Category.{v} C] [Category* D]
    [Abelian C] {W : MorphismProperty C} (L : C ⥤ D)
    [L.IsLocalization W] (hW : RightMultiplicativeSystem W) :
    ∃ hD : Formalization.Books.Homology.Unit03.AdditiveCategory D,
      HasKernels D ∧
        ∀ {X Y : C} (f : X ⟶ Y),
          PreservesLimit (parallelPair f 0) L := by
  sorry

theorem localization_is_abelian
    {C : Type u} {D : Type*} [Category.{v} C] [Category* D]
    [Abelian C] {W : MorphismProperty C} (L : C ⥤ D)
    [L.IsLocalization W] (hW : MultiplicativeSystem W) :
    ∃ hD : Abelian D, exactFunctor C D L := by
  sorry

end Formalization.Books.Homology.Unit08
