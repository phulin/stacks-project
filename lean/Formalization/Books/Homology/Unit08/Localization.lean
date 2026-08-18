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
  obtain ⟨p, hp, _⟩ :=
    localization_preadditive_right (W := W) L hW
  letI : Preadditive D := p
  letI : Functor.Additive L := hp
  letI : L.EssSurj := CategoryTheory.Localization.essSurj L W
  have hprod : HasFiniteProducts D :=
    Functor.hasFiniteProducts_of_additive_of_essSurj L
  let hD : Formalization.Books.Homology.Unit03.AdditiveCategory D :=
    { toPreadditive := p
      toHasFiniteProducts := hprod }
  exact ⟨hD, hp⟩

theorem localization_additive
    {C : Type u} {D : Type*} [Category.{v} C] [Category* D]
    [Formalization.Books.Homology.Unit03.AdditiveCategory C]
    {W : MorphismProperty C} (L : C ⥤ D)
    [L.IsLocalization W]
    (hW : LeftMultiplicativeSystem W ∨ RightMultiplicativeSystem W) :
    ∃ hD : Formalization.Books.Homology.Unit03.AdditiveCategory D,
      @Functor.Additive C D _ _ _ hD.toPreadditive L := by
  rcases hW with hW | hW
  · exact localization_additive_left (W := W) L
  · exact localization_additive_right (W := W) L

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
  letI : LeftMultiplicativeSystem W := hW.1
  letI : RightMultiplicativeSystem W := hW.2
  obtain ⟨hD, hL⟩ := localization_additive (W := W) L (Or.inl hW.1)
  letI : Formalization.Books.Homology.Unit03.AdditiveCategory D := hD
  letI : Functor.Additive L := hL
  constructor
  · constructor
    · intro hX
      have hid : L.map (𝟙 X) = L.map (0 : X ⟶ X) := by
        rw [L.map_id, L.map_zero]
        exact hX.eq_of_src _ _
      obtain ⟨Y, s, hs, hsz⟩ :=
        (MorphismProperty.map_eq_iff_postcomp (L := L) (W := W) (𝟙 X) 0).1 hid
      have hs0 : s = 0 := by
        simpa using hsz
      refine ⟨Y, ?_⟩
      rw [← hs0]
      exact hs
    · rintro ⟨Y, hs⟩
      rw [IsZero.iff_id_eq_zero]
      have hmap : L.map (0 : X ⟶ Y) = 0 := by
        exact L.map_zero X Y
      calc
        𝟙 (L.obj X) =
            L.map (0 : X ⟶ Y) ≫
              (CategoryTheory.Localization.isoOfHom L W (0 : X ⟶ Y) hs).inv :=
          (CategoryTheory.Localization.isoOfHom_hom_inv_id L W (0 : X ⟶ Y) hs).symm
        _ = 0 := by rw [hmap, zero_comp]
  · constructor
    · intro hX
      have hid : L.map (𝟙 X) = L.map (0 : X ⟶ X) := by
        rw [L.map_id, L.map_zero]
        exact hX.eq_of_tgt _ _
      obtain ⟨Z, s, hs, hsz⟩ :=
        (MorphismProperty.map_eq_iff_precomp (L := L) (W := W) (𝟙 X) 0).1 hid
      have hs0 : s = 0 := by
        simpa using hsz
      refine ⟨Z, ?_⟩
      rw [← hs0]
      exact hs
    · rintro ⟨Y, hs⟩
      rw [IsZero.iff_id_eq_zero]
      have hmap : L.map (0 : Y ⟶ X) = 0 := by
        exact L.map_zero Y X
      calc
        𝟙 (L.obj X) =
            (CategoryTheory.Localization.isoOfHom L W (0 : Y ⟶ X) hs).inv ≫
              L.map (0 : Y ⟶ X) :=
          (CategoryTheory.Localization.isoOfHom_inv_hom_id L W (0 : Y ⟶ X) hs).symm
        _ = 0 := by rw [hmap, comp_zero]

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
  let hC : Formalization.Books.Homology.Unit03.AdditiveCategory C :=
    { toPreadditive := inferInstance
      toHasFiniteProducts := inferInstance }
  letI : Formalization.Books.Homology.Unit03.AdditiveCategory C := hC
  letI : LeftMultiplicativeSystem W := hW
  obtain ⟨hD, hL⟩ := localization_additive_left (W := W) L
  letI : Formalization.Books.Homology.Unit03.AdditiveCategory D := hD
  letI : Functor.Additive L := hL
  letI : PreservesFiniteColimits (leftLocalizationFunctor W) :=
    left_localization_preserves_finite_colimits
  let e := CategoryTheory.Localization.uniq (leftLocalizationFunctor W) L W
  letI : PreservesFiniteColimits e.functor := inferInstance
  letI : PreservesFiniteColimits ((leftLocalizationFunctor W) ⋙ e.functor) :=
    comp_preservesFiniteColimits (leftLocalizationFunctor W) e.functor
  have hpres : PreservesFiniteColimits L :=
    preservesFiniteColimits_of_natIso
      (CategoryTheory.Localization.compUniqFunctor
        (leftLocalizationFunctor W) L W)
  refine ⟨hD, ?_, ?_⟩
  · exact ⟨fun f => by
      obtain ⟨g, ⟨eg⟩⟩ :=
        (CategoryTheory.Localization.essSurj_mapArrow L W).mem_essImage (Arrow.mk f)
      letI : PreservesFiniteColimits L := hpres
      have : HasColimit (parallelPair (L.map g.hom) 0) :=
        ⟨_, (CokernelCofork.ofπ (cokernel.π g.hom)
            (by simp)).mapIsColimit
          (cokernelIsCokernel g.hom) L⟩
      let e0 : (parallelPair f 0).obj WalkingParallelPair.zero ≅
          (parallelPair (L.map g.hom) 0).obj WalkingParallelPair.zero := by
        change Arrow.leftFunc.obj (Arrow.mk f) ≅
          Arrow.leftFunc.obj (L.mapArrow.obj g)
        exact Arrow.leftFunc.mapIso eg.symm
      let e1 : (parallelPair f 0).obj WalkingParallelPair.one ≅
          (parallelPair (L.map g.hom) 0).obj WalkingParallelPair.one := by
        change Arrow.rightFunc.obj (Arrow.mk f) ≅
          Arrow.rightFunc.obj (L.mapArrow.obj g)
        exact Arrow.rightFunc.mapIso eg.symm
      exact hasColimit_of_iso (show parallelPair f 0 ≅
          parallelPair (L.map g.hom) 0 from
        parallelPair.ext e0 e1
          (by
            dsimp [e0, e1]
            exact eg.inv.w.symm)
          (by dsimp [e0, e1]; rw [zero_comp, comp_zero]))⟩
  · letI : PreservesFiniteColimits L := hpres
    intro X Y f
    exact inferInstance

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
