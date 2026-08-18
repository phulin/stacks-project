import Formalization.Books.Stacks.Unit02.Foundation
import Mathlib.Tactic.CategoryTheory.Bicategory.PureCoherence
import Mathlib.Tactic.CategoryTheory.Bicategory.Basic

/-!
# Stacks, Unit 3: descent transport interfaces

These declarations retain their established namespace for downstream compatibility,
but are owned by the source unit corresponding to this file path.
-/

namespace Formalization.Books.Stacks.Unit01

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Pseudofunctor
open Formalization.Books.Categories.Unit31
open Opposite

open scoped CategoryTheory.Pseudofunctor.StrongTrans

universe t w v u

variable {C : Type u} [Category.{v} C]

/-! ### Transport of descent data along a fibred morphism

The component of a strong transformation sends the objects in a descent
datum to objects in the target fibres.  Its naturality isomorphisms transport
the gluing morphisms.  The coherence fields below are deliberately kept in
the standard `Pseudofunctor.DescentData` presentation, so later stack
arguments can use Mathlib's descent-data functors directly.
-/

private theorem whisker_middle_three
    {C : Type u} [Category.{v} C]
    {X₀ X₁ X₂ X₃ X₄ X₅ X₆ X₇ : C}
    {a₁ : X₀ ⟶ X₁} {a₂ : X₁ ⟶ X₂} {a₃ : X₂ ⟶ X₃}
    {a₄ : X₃ ⟶ X₄} {a₅ : X₄ ⟶ X₅} {a₆ : X₅ ⟶ X₆}
    {a₇ : X₆ ⟶ X₇} {b : X₂ ⟶ X₅} (h : a₃ ≫ a₄ ≫ a₅ = b) :
    a₁ ≫ a₂ ≫ a₃ ≫ a₄ ≫ a₅ ≫ a₆ ≫ a₇ =
      a₁ ≫ a₂ ≫ b ≫ a₆ ≫ a₇ := by
  simpa only [Category.assoc] using congrArg
    (fun k => (a₁ ≫ a₂) ≫ k ≫ (a₆ ≫ a₇)) h

noncomputable def transportedDescentHom
    {C : Type u} [Category.{v} C] {F G : FiberedCategory C}
    (η : FiberedMorphism F G) {ι : Type t} {U : C} {X : ι → C}
    {f : ∀ i, X i ⟶ U} (D : F.DescentData f) {Y : C} (q : Y ⟶ U)
    {i₁ i₂ : ι} (f₁ : Y ⟶ X i₁) (f₂ : Y ⟶ X i₂)
    (hf₁ : f₁ ≫ f i₁ = q := by cat_disch)
    (hf₂ : f₂ ≫ f i₂ = q := by cat_disch) :
    (G.map f₁.op.toLoc).toFunctor.obj
          ((η.app (.mk (op (X i₁)))).toFunctor.obj (D.obj i₁)) ⟶
      (G.map f₂.op.toLoc).toFunctor.obj
          ((η.app (.mk (op (X i₂)))).toFunctor.obj (D.obj i₂)) :=
  (η.naturality f₁.op.toLoc).inv.toNatTrans.app (D.obj i₁) ≫
    (η.app (.mk (op Y))).toFunctor.map (D.hom q f₁ f₂ hf₁ hf₂) ≫
      (η.naturality f₂.op.toLoc).hom.toNatTrans.app (D.obj i₂)

private theorem transportedDescentHom_pullHom
    {C : Type u} [Category.{v} C] {F G : FiberedCategory C}
    (η : FiberedMorphism F G) {ι : Type t} {U : C} {X : ι → C}
    {f : ∀ i, X i ⟶ U} (D : F.DescentData f)
    {Y' Y : C} (g : Y' ⟶ Y) (q : Y ⟶ U) (q' : Y' ⟶ U)
    (hq : g ≫ q = q') {i₁ i₂ : ι}
    (f₁ : Y ⟶ X i₁) (f₂ : Y ⟶ X i₂)
    (hf₁ : f₁ ≫ f i₁ = q) (hf₂ : f₂ ≫ f i₂ = q)
    (gf₁ : Y' ⟶ X i₁) (gf₂ : Y' ⟶ X i₂)
    (hgf₁ : g ≫ f₁ = gf₁) (hgf₂ : g ≫ f₂ = gf₂) :
    Pseudofunctor.LocallyDiscreteOpToCat.pullHom
        (transportedDescentHom η D q f₁ f₂ hf₁ hf₂) g gf₁ gf₂ =
      transportedDescentHom η D q' gf₁ gf₂ := by
  subst gf₁
  subst gf₂
  subst q'
  dsimp [transportedDescentHom]
  rw [← D.pullHom_hom g q (g ≫ q) (by simp) f₁ f₂ hf₁ hf₂
    (g ≫ f₁) (g ≫ f₂) rfl rfl]
  simp [Pseudofunctor.LocallyDiscreteOpToCat.pullHom,
    Pseudofunctor.mapComp'_eq_mapComp, Functor.map_comp, Category.assoc]
  rw [Pseudofunctor.StrongTrans.naturality_comp_inv_app η
        f₁.op.toLoc g.op.toLoc (D.obj i₁),
    Pseudofunctor.StrongTrans.naturality_comp_hom_app η
        f₂.op.toLoc g.op.toLoc (D.obj i₂)]
  simp only [Category.assoc, ← (η.app (.mk (op Y'))).toFunctor.map_comp_assoc,
    Cat.Hom.inv_hom_id_toNatTrans_app]
  have hF₁ :
      (F.mapComp f₁.op.toLoc g.op.toLoc).inv.toNatTrans.app (D.obj i₁) ≫
          (F.mapComp f₁.op.toLoc g.op.toLoc).hom.toNatTrans.app (D.obj i₁) ≫
        (F.map g.op.toLoc).toFunctor.map (D.hom q f₁ f₂ hf₁ hf₂) ≫
          𝟙 ((F.map f₂.op.toLoc ≫ F.map g.op.toLoc).toFunctor.obj (D.obj i₂)) =
      (F.map g.op.toLoc).toFunctor.map (D.hom q f₁ f₂ hf₁ hf₂) := by
    simp [← Category.assoc]
  have hF₁' := congrArg ((η.app (.mk (op Y'))).toFunctor.map) hF₁
  rw [hF₁']
  have hηg := NatIso.naturality_1
    (Cat.Hom.toNatIso (η.naturality g.op.toLoc))
    (D.hom q f₁ f₂ hf₁ hf₂)
  simp only [Cat.Hom.toNatIso, Cat.Hom.comp_toFunctor, Functor.comp_map] at hηg
  exact (whisker_middle_three hηg).symm

private theorem transportedDescentHom_naturality
    {C : Type u} [Category.{v} C] {F G : FiberedCategory C}
    (η : FiberedMorphism F G) {ι : Type t} {U : C} {X : ι → C}
    {f : ∀ i, X i ⟶ U} {D₁ D₂ : F.DescentData f} (φ : D₁ ⟶ D₂)
    {Y : C} (q : Y ⟶ U) {i₁ i₂ : ι}
    (f₁ : Y ⟶ X i₁) (f₂ : Y ⟶ X i₂)
    (hf₁ : f₁ ≫ f i₁ = q) (hf₂ : f₂ ≫ f i₂ = q) :
    (G.map f₁.op.toLoc).toFunctor.map
          ((η.app (.mk (op (X i₁)))).toFunctor.map (φ.hom i₁)) ≫
        transportedDescentHom η D₂ q f₁ f₂ hf₁ hf₂ =
      transportedDescentHom η D₁ q f₁ f₂ hf₁ hf₂ ≫
        (G.map f₂.op.toLoc).toFunctor.map
          ((η.app (.mk (op (X i₂)))).toFunctor.map (φ.hom i₂)) := by
  dsimp [transportedDescentHom]
  simp only [Category.assoc]
  have h₁ :
      (G.map f₁.op.toLoc).toFunctor.map
          ((η.app (.mk (op (X i₁)))).toFunctor.map (φ.hom i₁)) ≫
        (η.naturality f₁.op.toLoc).inv.toNatTrans.app (D₂.obj i₁) =
      (η.naturality f₁.op.toLoc).inv.toNatTrans.app (D₁.obj i₁) ≫
        (η.app (.mk (op Y))).toFunctor.map
          ((F.map f₁.op.toLoc).toFunctor.map (φ.hom i₁)) := by
    have h := NatIso.naturality_1
      (Cat.Hom.toNatIso (η.naturality f₁.op.toLoc)).symm (φ.hom i₁)
    simpa only [Cat.Hom.toNatIso, Iso.symm_hom, Iso.symm_inv,
      Cat.Hom.comp_toFunctor, Functor.comp_map, Category.assoc,
      Cat.Hom.inv_hom_id_toNatTrans_app_assoc, Category.id_comp]
      using congrArg (fun k =>
        (η.naturality f₁.op.toLoc).inv.toNatTrans.app (D₁.obj i₁) ≫ k) h
  have h₂ :
      (η.naturality f₂.op.toLoc).hom.toNatTrans.app (D₁.obj i₂) ≫
        (G.map f₂.op.toLoc).toFunctor.map
          ((η.app (.mk (op (X i₂)))).toFunctor.map (φ.hom i₂)) =
      (η.app (.mk (op Y))).toFunctor.map
          ((F.map f₂.op.toLoc).toFunctor.map (φ.hom i₂)) ≫
        (η.naturality f₂.op.toLoc).hom.toNatTrans.app (D₂.obj i₂) := by
    have h := NatIso.naturality_2
      (Cat.Hom.toNatIso (η.naturality f₂.op.toLoc)) (φ.hom i₂)
    simpa only [Cat.Hom.toNatIso, Iso.symm_hom, Iso.symm_inv,
      Cat.Hom.comp_toFunctor, Functor.comp_map, Category.assoc,
      Cat.Hom.inv_hom_id_toNatTrans_app, Category.comp_id]
      using congrArg (fun k =>
        k ≫ (η.naturality f₂.op.toLoc).hom.toNatTrans.app (D₂.obj i₂)) h
  have h₁' := congrArg (fun k =>
    k ≫ (η.app (.mk (op Y))).toFunctor.map
        (D₂.hom q f₁ f₂ hf₁ hf₂) ≫
      (η.naturality f₂.op.toLoc).hom.toNatTrans.app (D₂.obj i₂)) h₁
  have h₂' := congrArg (fun k =>
    (η.naturality f₁.op.toLoc).inv.toNatTrans.app (D₁.obj i₁) ≫
      (η.app (.mk (op Y))).toFunctor.map
        (D₁.hom q f₁ f₂ hf₁ hf₂) ≫ k) h₂
  simp only [Category.assoc] at h₁' h₂'
  rw [h₁', h₂']
  have h₃ := congrArg ((η.app (.mk (op Y))).toFunctor.map)
    (φ.comm q f₁ f₂ hf₁ hf₂)
  simpa only [Functor.map_comp, Category.assoc] using congrArg (fun k =>
    (η.naturality f₁.op.toLoc).inv.toNatTrans.app (D₁.obj i₁) ≫ k ≫
      (η.naturality f₂.op.toLoc).hom.toNatTrans.app (D₂.obj i₂)) h₃

noncomputable def descentDataFunctor
    {C : Type u} [Category.{v} C] {F G : FiberedCategory C}
    (η : FiberedMorphism F G) {ι : Type t} {U : C} {X : ι → C}
    (f : ∀ i, X i ⟶ U) : F.DescentData f ⥤ G.DescentData f where
  obj D :=
    { obj i := (η.app (.mk (op (X i)))).toFunctor.obj (D.obj i)
      hom Y q i₁ i₂ f₁ f₂ hf₁ hf₂ :=
        transportedDescentHom η D q f₁ f₂ hf₁ hf₂
      pullHom_hom := by
        intro Y' Y g q q' hq i₁ i₂ f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂
        exact transportedDescentHom_pullHom η D g q q' hq
          f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂
      hom_self := by
        intros Y q i g hg
        have h := D.hom_self q g hg
        dsimp [transportedDescentHom]
        rw [h]
        simp
      hom_comp := by
        intros Y q i₁ i₂ i₃ f₁ f₂ f₃ hf₁ hf₂ hf₃
        dsimp [transportedDescentHom]
        simp only [Category.assoc, Cat.Hom.hom_inv_id_toNatTrans_app_assoc]
        rw [← (η.app (.mk (op Y))).toFunctor.map_comp_assoc]
        simpa only [Category.assoc] using
          congrArg (fun k =>
            (η.naturality f₁.op.toLoc).inv.toNatTrans.app (D.obj i₁) ≫ k ≫
              (η.naturality f₃.op.toLoc).hom.toNatTrans.app (D.obj i₃))
            (congrArg ((η.app (.mk (op Y))).toFunctor.map)
              (D.hom_comp q f₁ f₂ f₃ hf₁ hf₂ hf₃)) }
  map {D₁ D₂} φ :=
    { hom i := (η.app (.mk (op (X i)))).toFunctor.map (φ.hom i)
      comm := by
        intros Y q i₁ i₂ f₁ f₂ hf₁ hf₂
        exact transportedDescentHom_naturality η φ q f₁ f₂ hf₁ hf₂ }
  map_id D := by
    apply Pseudofunctor.DescentData.hom_ext
    intro i
    simp
  map_comp φ ψ := by
    apply Pseudofunctor.DescentData.hom_ext
    intro i
    simp

/- Essential surjectivity is the only part of descent transport which is not
   inherited pointwise from the fibre functors.

   Proof roadmap:

   1. For `D : G.DescentData f`, choose in every fibre an object `A i` and an
      isomorphism `e i : η(A i) ≅ D.obj i` using fibrewise essential
      surjectivity.
   2. Conjugate each gluing morphism of `D` by the `e i` and by the naturality
      isomorphisms of `η`.  Lift the resulting morphism through the full
      fibre functor to define the gluing morphism of `A`.
   3. Prove pullback compatibility, identities, and the cocycle condition by
      applying the faithful fibre functor.  After `map_preimage`, these are
      exactly the corresponding fields of `D`.
   4. Assemble the `e i` into an isomorphism
      `descentDataFunctor η f |>.obj A ≅ D`; its naturality is the equation
      used when defining the lifted gluing maps. -/
theorem descentDataFunctor_essSurj
    {C : Type u} [Category.{v} C] {F G : FiberedCategory C}
    (η : FiberedMorphism F G) (hη : FiberwiseEquivalence η)
    {ι : Type t} {U : C} {X : ι → C}
    (f : ∀ i, X i ⟶ U) :
    (descentDataFunctor η f).EssSurj := by
  sorry

/- The transport functor is an equivalence whenever the fibred morphism is a
fibrewise equivalence.  The proof is the descent-data version of transporting
objects and gluing morphisms through the fibrewise full-faithful and
essentially-surjective components of `η`. -/
theorem descentDataFunctor_is_equivalence
    {C : Type u} [Category.{v} C] {F G : FiberedCategory C}
    (η : FiberedMorphism F G) (hη : FiberwiseEquivalence η)
    {ι : Type t} {U : C} {X : ι → C}
    (f : ∀ i, X i ⟶ U) :
    (descentDataFunctor η f).IsEquivalence := by
  rcases hη with ⟨hff, hess⟩
  let (V : C) : (η.app (.mk (op V))).toFunctor.IsEquivalence := by
    rcases hff V with ⟨h⟩
    exact { faithful := h.faithful, full := h.full, essSurj := hess V }
  constructor
  · constructor
    intro D₁ D₂ φ ψ h
    apply Pseudofunctor.DescentData.hom_ext
    intro i
    apply (η.app (.mk (op (X i)))).toFunctor.map_injective
    simpa only [descentDataFunctor] using congrArg (fun k => k.hom i) h
  · constructor
    intro D₁ D₂ φ
    let ψ : D₁ ⟶ D₂ :=
      { hom i := (η.app (.mk (op (X i)))).toFunctor.preimage (φ.hom i)
        comm := by
          intro Y q i₁ i₂ f₁ f₂ hf₁ hf₂
          apply (η.app (.mk (op Y))).toFunctor.map_injective
          simp only [Functor.map_comp]
          have h₁ := NatIso.naturality_1
            (Cat.Hom.toNatIso (η.naturality f₁.op.toLoc)).symm
              ((η.app (.mk (op (X i₁)))).toFunctor.preimage (φ.hom i₁))
          have h₂ := NatIso.naturality_2
            (Cat.Hom.toNatIso (η.naturality f₂.op.toLoc))
              ((η.app (.mk (op (X i₂)))).toFunctor.preimage (φ.hom i₂))
          have h₁' := h₁
          have h₂' := h₂
          simp only [Cat.Hom.toNatIso, Iso.symm_hom, Iso.symm_inv,
            Cat.Hom.comp_toFunctor, Functor.comp_map] at h₁' h₂'
          rw [← h₁', ← h₂']
          apply (cancel_mono
            ((η.naturality f₂.op.toLoc).hom.toNatTrans.app (D₂.obj i₂))).1
          apply (cancel_epi
            ((η.naturality f₁.op.toLoc).inv.toNatTrans.app (D₁.obj i₁))).1
          simp only [Category.assoc,
            Cat.Hom.inv_hom_id_toNatTrans_app_assoc]
          rw [(η.app (.mk (op (X i₁)))).toFunctor.map_preimage (φ.hom i₁),
            (η.app (.mk (op (X i₂)))).toFunctor.map_preimage (φ.hom i₂)]
          simp only [Cat.Hom.inv_hom_id_toNatTrans_app]
          simpa only [descentDataFunctor, transportedDescentHom,
            Category.assoc, Category.comp_id,
            Functor.comp_obj, Cat.Hom.comp_toFunctor] using
            φ.comm q f₁ f₂ hf₁ hf₂ }
    refine ⟨ψ, ?_⟩
    apply Pseudofunctor.DescentData.hom_ext
    intro i
    simpa only [descentDataFunctor] using
      (η.app (.mk (op (X i)))).toFunctor.map_preimage (φ.hom i)
  · exact descentDataFunctor_essSurj η ⟨hff, hess⟩ f

noncomputable def descentDataEquivalence
    {C : Type u} [Category.{v} C] {F G : FiberedCategory C}
    (η : FiberedMorphism F G) (hη : FiberwiseEquivalence η)
    {ι : Type t} {U : C} {X : ι → C}
    (f : ∀ i, X i ⟶ U) : F.DescentData f ≌ G.DescentData f := by
  letI : (descentDataFunctor η f).IsEquivalence :=
    descentDataFunctor_is_equivalence η hη f
  exact (descentDataFunctor η f).asEquivalence

/- The comparison is already present before choosing an inverse equivalence.

   Proof roadmap:

   * At a fibre object over `U`, both composites have component at `i` given
     by applying `η` after pullback along `f i`, in opposite orders.
   * Use `η.naturality (f i).op.toLoc` for the component isomorphism.
   * Prove compatibility with every descent gluing map by the naturality of
     those same isomorphisms; `transportedDescentHom` was defined in exactly
     the conjugated form needed for this calculation.
   * Finish with `Pseudofunctor.DescentData.hom_ext` componentwise. -/
theorem descentDataFunctor_toDescentData_iso
    {C : Type u} [Category.{v} C] {F G : FiberedCategory C}
    (η : FiberedMorphism F G)
    {ι : Type t} {U : C} {X : ι → C}
    (f : ∀ i, X i ⟶ U) :
    Nonempty
      (F.toDescentData f ⋙ descentDataFunctor η f ≅
        (η.app (.mk (op U))).toFunctor ⋙ G.toDescentData f) := by
  sorry

/- The comparison isomorphism records that transport commutes with the
canonical descent-data functors from the fibre over `U`. -/
theorem descentDataEquivalence_toDescentData_iso
    {C : Type u} [Category.{v} C] {F G : FiberedCategory C}
    (η : FiberedMorphism F G) (hη : FiberwiseEquivalence η)
    {ι : Type t} {U : C} {X : ι → C}
    (f : ∀ i, X i ⟶ U) :
    Nonempty
      (F.toDescentData f ⋙ (descentDataEquivalence η hη f).functor ≅
        (η.app (.mk (op U))).toFunctor ⋙ G.toDescentData f) := by
  exact descentDataFunctor_toDescentData_iso η f

end Formalization.Books.Stacks.Unit01
