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
    ∃ _hD : Formalization.Books.Homology.Unit03.AdditiveCategory D,
      HasKernels D ∧
        ∀ {X Y : C} (f : X ⟶ Y),
          PreservesLimit (parallelPair f 0) L := by
  let hC : Formalization.Books.Homology.Unit03.AdditiveCategory C :=
    { toPreadditive := inferInstance
      toHasFiniteProducts := inferInstance }
  let _hC : Formalization.Books.Homology.Unit03.AdditiveCategory C := hC
  let _hW : RightMultiplicativeSystem W := hW
  obtain ⟨hD, hL⟩ := localization_additive_right (W := W) L
  let _hD : Formalization.Books.Homology.Unit03.AdditiveCategory D := hD
  let _hL : Functor.Additive L := hL
  let _hRightPres : PreservesFiniteLimits (rightLocalizationFunctor W) :=
    right_localization_preserves_finite_limits
  let e := CategoryTheory.Localization.uniq (rightLocalizationFunctor W) L W
  let _hePres : PreservesFiniteLimits e.functor := inferInstance
  let _hCompPres : PreservesFiniteLimits ((rightLocalizationFunctor W) ⋙ e.functor) :=
    comp_preservesFiniteLimits (rightLocalizationFunctor W) e.functor
  have hpres : PreservesFiniteLimits L :=
    preservesFiniteLimits_of_natIso
      (CategoryTheory.Localization.compUniqFunctor
        (rightLocalizationFunctor W) L W)
  refine ⟨hD, ?_, ?_⟩
  · exact ⟨fun f => by
      obtain ⟨g, ⟨eg⟩⟩ :=
        (CategoryTheory.Localization.essSurj_mapArrow_of_hasRightCalculusOfFractions
          (L := L) (W := W)).mem_essImage (Arrow.mk f)
      let _hpres : PreservesFiniteLimits L := hpres
      have : HasLimit (parallelPair (L.map g.hom) 0) :=
        ⟨_, (KernelFork.ofι (kernel.ι g.hom)
            (by simp)).mapIsLimit
          (kernelIsKernel g.hom) L⟩
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
      exact hasLimit_of_iso ((show parallelPair f 0 ≅
          parallelPair (L.map g.hom) 0 from
        parallelPair.ext e0 e1
          (by
            dsimp [e0, e1]
            exact eg.inv.w.symm)
          (by dsimp [e0, e1]; rw [zero_comp, comp_zero])).symm)⟩
  · let _hpres : PreservesFiniteLimits L := hpres
    intro X Y f
    exact inferInstance

theorem localization_is_abelian
    {C : Type u} {D : Type*} [Category.{v} C] [Category* D]
    [Abelian C] {W : MorphismProperty C} (L : C ⥤ D)
    [L.IsLocalization W] (hW : MultiplicativeSystem W) :
    ∃ _hD : Abelian D, exactFunctor C D L := by
  let hC : Formalization.Books.Homology.Unit03.AdditiveCategory C :=
    { toPreadditive := inferInstance
      toHasFiniteProducts := inferInstance }
  let _hC : Formalization.Books.Homology.Unit03.AdditiveCategory C := hC
  let _hLeft : LeftMultiplicativeSystem W := hW.1
  let _hRight : RightMultiplicativeSystem W := hW.2
  obtain ⟨hD, hL⟩ := localization_additive_left (W := W) L
  let _hD : Formalization.Books.Homology.Unit03.AdditiveCategory D := hD
  let _hL : Functor.Additive L := hL
  let _hLeftPres : PreservesFiniteColimits (leftLocalizationFunctor W) :=
    left_localization_preserves_finite_colimits
  let eL := CategoryTheory.Localization.uniq (leftLocalizationFunctor W) L W
  let _heLeftPres : PreservesFiniteColimits eL.functor := inferInstance
  let _hCompLeftPres : PreservesFiniteColimits ((leftLocalizationFunctor W) ⋙ eL.functor) :=
    comp_preservesFiniteColimits (leftLocalizationFunctor W) eL.functor
  have hpresColimits : PreservesFiniteColimits L :=
    preservesFiniteColimits_of_natIso
      (CategoryTheory.Localization.compUniqFunctor
        (leftLocalizationFunctor W) L W)
  let _hRightPres : PreservesFiniteLimits (rightLocalizationFunctor W) :=
    right_localization_preserves_finite_limits
  let eR := CategoryTheory.Localization.uniq (rightLocalizationFunctor W) L W
  let _heRightPres : PreservesFiniteLimits eR.functor := inferInstance
  let _hCompRightPres : PreservesFiniteLimits ((rightLocalizationFunctor W) ⋙ eR.functor) :=
    comp_preservesFiniteLimits (rightLocalizationFunctor W) eR.functor
  have hpresLimits : PreservesFiniteLimits L :=
    preservesFiniteLimits_of_natIso
      (CategoryTheory.Localization.compUniqFunctor
        (rightLocalizationFunctor W) L W)
  let _hpresColimits : PreservesFiniteColimits L := hpresColimits
  let _hpresLimits : PreservesFiniteLimits L := hpresLimits
  have hAbelian : Abelian D := by
    apply Abelian.mk'
    intro X Y f
    obtain ⟨g, ⟨eg⟩⟩ :=
      (CategoryTheory.Localization.essSurj_mapArrow L W).mem_essImage (Arrow.mk f)
    change Arrow.mk (L.map g.hom) ≅ Arrow.mk f at eg
    have himageKernel : IsLimit (KernelFork.ofι (f := Abelian.factorThruImage g.hom)
        (kernel.ι g.hom) (by
          apply (cancel_mono (Abelian.image.ι g.hom)).1
          rw [Category.assoc]
          rw [Abelian.image.fac, kernel.condition, zero_comp])) := by
      refine Fork.IsLimit.mk' _ (fun s => ?_)
      refine ⟨kernel.lift g.hom s.ι ?_, kernel.lift_ι _ _ _, ?_⟩
      · calc
          s.ι ≫ g.hom =
              (s.ι ≫ Abelian.factorThruImage g.hom) ≫ Abelian.image.ι g.hom := by
            rw [Category.assoc, Abelian.image.fac]
          _ = 0 := by simp
      · intro m hm
        apply (kernelIsKernel g.hom).hom_ext
        intro j
        rcases j with (_ | _)
        · change m ≫ kernel.ι g.hom =
            kernel.lift g.hom s.ι _ ≫ kernel.ι g.hom
          simpa only [KernelFork.ι_ofι] using
            hm.trans (kernel.lift_ι _ _ _).symm
        · simp
    let hs : CategoryTheory.Abelian.AbelianStruct g.hom :=
      { kernelFork := KernelFork.ofι (kernel.ι g.hom) (kernel.condition g.hom)
        isLimitKernelFork := kernelIsKernel g.hom
        cokernelCofork := CokernelCofork.ofπ (cokernel.π g.hom)
          (cokernel.condition g.hom)
        isColimitCokernelCofork := cokernelIsCokernel g.hom
        image := Abelian.image g.hom
        imageπ := Abelian.factorThruImage g.hom
        imageIsCokernel := Abelian.epiIsCokernelOfKernel _ himageKernel
        imageι := Abelian.image.ι g.hom
        imageIsKernel := kernelIsKernel (cokernel.π g.hom)
        fac := by simp }
    have hmap : Nonempty (CategoryTheory.Abelian.AbelianStruct (L.map g.hom)) := by
      refine ⟨{
        kernelFork := KernelFork.ofι (L.map hs.kernelFork.ι) (by
          rw [← L.map_comp, hs.kernelFork.condition, L.map_zero])
        isLimitKernelFork :=
          (KernelFork.isLimitMapConeEquiv _ L).1
            (isLimitOfPreserves L hs.isLimitKernelFork)
        cokernelCofork := CokernelCofork.ofπ (L.map hs.cokernelCofork.π) (by
          rw [← L.map_comp, hs.cokernelCofork.condition, L.map_zero])
        isColimitCokernelCofork :=
          (CokernelCofork.isColimitMapCoconeEquiv _ L).1
            (isColimitOfPreserves L hs.isColimitCokernelCofork)
        image := L.obj hs.image
        imageπ := L.map hs.imageπ
        ι_imageπ := by
          change L.map hs.kernelFork.ι ≫ L.map hs.imageπ = 0
          rw [← L.map_comp, hs.ι_imageπ, L.map_zero]
        imageIsCokernel :=
          (CokernelCofork.isColimitMapCoconeEquiv _ L).1
            (isColimitOfPreserves L hs.imageIsCokernel)
        imageι := L.map hs.imageι
        imageι_π := by
          change L.map hs.imageι ≫ L.map hs.cokernelCofork.π = 0
          rw [← L.map_comp, hs.imageι_π, L.map_zero]
        imageIsKernel :=
          (isLimitMapConeForkEquiv' L hs.imageι_π).1
            (isLimitOfPreserves L hs.imageIsKernel)
        fac := by
          rw [← L.map_comp]
          simp }⟩
    obtain ⟨a⟩ := hmap
    let el := Arrow.leftFunc.mapIso eg
    let er := Arrow.rightFunc.mapIso eg
    change L.obj g.left ≅ X at el
    change L.obj g.right ≅ Y at er
    have hleft : el.hom ≫ f = L.map g.hom ≫ er.hom := by
      change eg.hom.left ≫ f = L.map g.hom ≫ eg.hom.right
      exact eg.hom.w
    have hpre : f ≫ er.inv = el.inv ≫ L.map g.hom := by
      rw [← cancel_mono er.hom]
      simp only [Category.assoc]
      rw [← hleft]
      simp
    let kf : KernelFork f :=
      KernelFork.ofι (a.kernelFork.ι ≫ el.hom) (by
        calc
          (a.kernelFork.ι ≫ el.hom) ≫ f =
              a.kernelFork.ι ≫ (el.hom ≫ f) := Category.assoc _ _ _
          _ = a.kernelFork.ι ≫ (L.map g.hom ≫ er.hom) := by rw [hleft]
          _ = 0 := by simp [← Category.assoc, a.kernelFork.condition])
    let cf : CokernelCofork f :=
      CokernelCofork.ofπ (er.inv ≫ a.cokernelCofork.π) (by
        calc
          f ≫ (er.inv ≫ a.cokernelCofork.π) =
              (f ≫ er.inv) ≫ a.cokernelCofork.π :=
                (Category.assoc _ _ _).symm
          _ = (el.inv ≫ L.map g.hom) ≫ a.cokernelCofork.π := by rw [hpre]
          _ = el.inv ≫ (L.map g.hom ≫ a.cokernelCofork.π) :=
            Category.assoc _ _ _
          _ = 0 := by rw [a.cokernelCofork.condition, comp_zero])
    refine ⟨{
      kernelFork := kf
      isLimitKernelFork := Fork.isLimitOfIsos a.kernelFork a.isLimitKernelFork kf
        el er (Iso.refl _)
        (by exact hleft) (by simp only [comp_zero, zero_comp])
        (by simp [kf, el])
      cokernelCofork := cf
      isColimitCokernelCofork := Cofork.isColimitOfIsos a.cokernelCofork
        a.isColimitCokernelCofork cf el er (Iso.refl _)
        (by exact hleft) (by simp only [comp_zero, zero_comp])
        (by simp [cf, er])
      image := a.image
      imageπ := el.inv ≫ a.imageπ
      ι_imageπ := by
        change (a.kernelFork.ι ≫ el.hom) ≫ (el.inv ≫ a.imageπ) = 0
        simp [Category.assoc, a.ι_imageπ]
      imageIsCokernel :=
        Cofork.isColimitOfIsos
          (CokernelCofork.ofπ a.imageπ a.ι_imageπ) a.imageIsCokernel
          (CokernelCofork.ofπ (el.inv ≫ a.imageπ) (by
            change (a.kernelFork.ι ≫ el.hom) ≫ (el.inv ≫ a.imageπ) = 0
            simp [Category.assoc, a.ι_imageπ]))
          (Iso.refl _) el (Iso.refl _)
          (by simp [kf]) (by simp) (by simp)
      imageι := a.imageι ≫ er.hom
      imageι_π := by
        dsimp [cf]
        simp [Category.assoc, a.imageι_π]
      imageIsKernel :=
        Fork.isLimitOfIsos (KernelFork.ofι a.imageι a.imageι_π) a.imageIsKernel
          (KernelFork.ofι (a.imageι ≫ er.hom) (by
            dsimp [cf]
            simp [Category.assoc, a.imageι_π]))
          er (Iso.refl _) (Iso.refl _)
          (by simp [cf]) (by simp) (by simp)
      fac := by
        calc
          (el.inv ≫ a.imageπ) ≫ (a.imageι ≫ er.hom) =
              el.inv ≫ (a.imageπ ≫ a.imageι) ≫ er.hom := by
                simp [Category.assoc]
          _ = el.inv ≫ L.map g.hom ≫ er.hom := by rw [a.fac]
          _ = f := by
            rw [← hleft]
            simp }⟩
  refine ⟨hAbelian, ?_⟩
  rw [exactFunctor_iff]
  exact ⟨hpresLimits, hpresColimits⟩

end Formalization.Books.Homology.Unit08
