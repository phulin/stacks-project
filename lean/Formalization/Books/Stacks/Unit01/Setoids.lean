import Formalization.Books.Stacks.Unit01.Groupoids

/-!
# Stacks, Chapter 1, Section 6: stacks in setoids
-/

namespace Formalization.Books.Stacks.Unit01

open CategoryTheory
open CategoryTheory.Pseudofunctor
open Opposite

open scoped CategoryTheory.Pseudofunctor.StrongTrans

universe t v' v u' u

def StackInSetoids {C : Type u} [Category.{v} C]
    (F : FiberedCategory C) (J : GrothendieckTopology C) : Prop :=
  FiberwiseSetoid F ∧ Stack F J

def StackInSets {C : Type u} [Category.{v} C]
    (F : FiberedCategory C) (J : GrothendieckTopology C) : Prop :=
  FiberwiseSet F ∧ Stack F J

def ObjectIsoSetoid (K : Type u) [Category.{v} K] : Setoid K where
  r X Y := Nonempty (X ≅ Y)
  iseqv := {
    refl := fun X => ⟨Iso.refl X⟩
    symm := by
      intro X Y h
      rcases h with ⟨e⟩
      exact ⟨e.symm⟩
    trans := by
      intro X Y Z h₁ h₂
      rcases h₁ with ⟨e₁⟩
      rcases h₂ with ⟨e₂⟩
      exact ⟨e₁.trans e₂⟩ }

def ObjectIsomorphismClasses {C : Type u} [Category.{v} C]
    (F : FiberedCategory C) (U : C) :=
  Quotient (ObjectIsoSetoid (Fiber F U))

def ObjectClassPresheaf {C : Type u} [Category.{v} C]
    (F : FiberedCategory C) : Cᵒᵖ ⥤ Type w where
  obj U := ObjectIsomorphismClasses F U.unop
  map {U V} f := ↾(Quotient.map
    (fun x => (F.map f.toLoc).toFunctor.obj x)
    (by
      intro x y h
      rcases h with ⟨e⟩
      exact ⟨(F.map f.toLoc).toFunctor.mapIso e⟩))
  map_id := by
    intro U
    ext z
    refine Quotient.inductionOn z ?_
    intro x
    apply Quotient.sound
    exact ⟨(Cat.Hom.toNatIso (F.mapId (.mk U))).app x⟩
  map_comp := by
    intro U V W f g
    ext z
    refine Quotient.inductionOn z ?_
    intro x
    apply Quotient.sound
    exact ⟨(Cat.Hom.toNatIso (F.mapComp f.toLoc g.toLoc)).app x⟩

theorem object_class_presheaf_fibre {C : Type u} [Category.{v} C]
    (F : FiberedCategory C) (U : C) :
    (ObjectClassPresheaf F).obj (op U) = ObjectIsomorphismClasses F U := rfl

def RelativePair {C : Type u} [Category.{v} C]
    {F G : FiberedCategory C} (η : FiberedMorphism F G) (U : C)
    (y : Fiber G U) :=
  Σ x : Fiber F U, (η.app (.mk (op U))).toFunctor.obj x ⟶ y

def RelativePairSetoid {C : Type u} [Category.{v} C]
    {F G : FiberedCategory C} (η : FiberedMorphism F G) (U : C)
    (y : Fiber G U) : Setoid (RelativePair η U y) where
  r a b := ∃ e : a.1 ≅ b.1,
    (η.app (.mk (op U))).toFunctor.map e.hom ≫ b.2 = a.2
  iseqv := {
    refl := by
      intro a
      exact ⟨Iso.refl _, by simp⟩
    symm := by
      intro a b h
      rcases h with ⟨e, h⟩
      refine ⟨e.symm, ?_⟩
      calc
        (η.app (.mk (op U))).toFunctor.map e.symm.hom ≫ a.2 =
            (η.app (.mk (op U))).toFunctor.map e.symm.hom ≫
              ((η.app (.mk (op U))).toFunctor.map e.hom ≫ b.2) := by rw [h]
        _ = ((η.app (.mk (op U))).toFunctor.map e.symm.hom ≫
              (η.app (.mk (op U))).toFunctor.map e.hom) ≫ b.2 := by
          simp
        _ = b.2 := by
          rw [← Functor.map_comp]
          simp
    trans := by
      intro a b c h₁ h₂
      rcases h₁ with ⟨e₁, h₁⟩
      rcases h₂ with ⟨e₂, h₂⟩
      refine ⟨e₁.trans e₂, ?_⟩
      rw [Iso.trans_hom, Functor.map_comp, Category.assoc, h₂, h₁] }

def RelativePairClasses {C : Type u} [Category.{v} C]
    {F G : FiberedCategory C} (η : FiberedMorphism F G) (U : C)
    (y : Fiber G U) := Quotient (RelativePairSetoid η U y)

def relativePairClassesPresheaf {C : Type u} [Category.{v} C]
    {F G : FiberedCategory C} (η : FiberedMorphism F G) (U : C)
    (y : Fiber G U) : (Over C U)ᵒᵖ ⥤ Type w where
  obj T := RelativePairClasses η T.unop.left
    ((G.map T.unop.hom.op.toLoc).toFunctor.obj y)
  map {T₁ T₂} q := by
    exact ↾(Quotient.map
      (fun a : RelativePair η T₁.unop.left
        ((G.map T₁.unop.hom.op.toLoc).toFunctor.obj y) => by
        have hcomp :
            T₁.unop.hom.op.toLoc ≫ (Over.Hom.left q.unop).op.toLoc =
              T₂.unop.hom.op.toLoc := by
          rw [← Quiver.Hom.comp_toLoc, ← op_comp, q.unop.w]
        exact ⟨
          (F.map (Over.Hom.left q.unop).op.toLoc).toFunctor.obj a.1,
          (η.naturality (Over.Hom.left q.unop).op.toLoc).hom.toNatTrans.app a.1 ≫
            (G.map (Over.Hom.left q.unop).op.toLoc).toFunctor.map a.2 ≫
            (G.mapComp' T₁.unop.hom.op.toLoc
              (Over.Hom.left q.unop).op.toLoc T₂.unop.hom.op.toLoc hcomp).inv.toNatTrans.app y⟩)
      (by
        intro a b hab
        rcases hab with ⟨e, he⟩
        refine ⟨(F.map (Over.Hom.left q.unop).op.toLoc).toFunctor.mapIso e, ?_⟩
        rw [← he]
        simp only [Functor.mapIso_hom, Functor.map_comp, ← Category.assoc]
        have hnat := (η.naturality (Over.Hom.left q.unop).op.toLoc).hom.toNatTrans.naturality e.hom
        simp only [Cat.Hom.comp_toFunctor, Functor.comp_map] at hnat
        rw [hnat]))
  map_id := by
    intro X
    ext z
    refine Quotient.inductionOn z ?_
    intro a
    apply Quotient.sound
    refine ⟨(Cat.Hom.toNatIso (F.mapId (.mk (op X.unop.left)))).app a.1, ?_⟩
    simp [Cat.Hom.comp_toFunctor,
      CategoryTheory.Pseudofunctor.StrongTrans.naturality_id_hom_app,
      CategoryTheory.Pseudofunctor.mapComp'_comp_id_inv_app,
      Cat.Hom.id_toFunctor,
      Category.assoc]
  map_comp := by
    sorry

structure TwoCartesianSquare {C : Type u} [Category.{v} C]
    (A B C' D : FiberedCategory C) where
  left : FiberedMorphism A B
  right : FiberedMorphism A C'
  top : FiberedMorphism B D
  bottom : FiberedMorphism C' D
  commutes : left ≫ top ≅ right ≫ bottom
  isTwoPullback : IsTwoPullbackCone top bottom left right commutes

def FiberwiseFaithful {C : Type u} [Category.{v} C]
    {F G : FiberedCategory C} (η : FiberedMorphism F G) : Prop :=
  ∀ U : C, (η.app (.mk (op U))).toFunctor.Faithful

def LocallyEssentiallyInImage {C : Type u} [Category.{v} C]
    {F G : FiberedCategory C} (η : FiberedMorphism F G)
    (J : GrothendieckTopology C) : Prop :=
  ∀ (U : C) (y : Fiber G U),
        ∃ (ι : Type t) (X : ι → C) (f : ∀ i, X i ⟶ U),
      CoveringFamily J f ∧
        ∀ i, ∃ x : Fiber F (X i), Nonempty
          ((G.map (f i).op.toLoc).toFunctor.obj y ≅
            (η.app (.mk (op (X i)))).toFunctor.obj x)

structure RelativeSheafCondition {C : Type u} [Category.{v} C]
    (F G : FiberedCategory C) (J : GrothendieckTopology C) where
  map : FiberedMorphism F G
  sourceIsGroupoid : FiberwiseGroupoid F
  targetIsGroupoidStack : StackInGroupoids G J
  fibresFaithful : FiberwiseFaithful map
  pairPresheaf : ∀ (U : C) (_y : Fiber G U), (Over C U)ᵒᵖ ⥤ Type w
  pairPresheafPresentation : ∀ (U : C) (y : Fiber G U),
    Nonempty ((pairPresheaf U y) ≅ relativePairClassesPresheaf map U y)
  pairPresheavesAreSheaves : ∀ (U : C) (y : Fiber G U),
    Presheaf.IsSheaf (J.over U) (pairPresheaf U y)

theorem stack_in_sets_iff_object_class_presheaf_is_sheaf
    {C : Type u} [Category.{v} C]
    (F : FiberedCategory C) (J : GrothendieckTopology C)
    (hF : FiberwiseSet F) :
    StackInSets F J ↔
      Presheaf.IsSheaf J (ObjectClassPresheaf F) := by
  sorry

theorem stack_in_setoids_iff_object_class_presheaf_is_sheaf
    {C : Type u} [Category.{v} C]
    (F : FiberedCategory C) (J : GrothendieckTopology C)
    (hF : FiberwiseSetoid F) :
    StackInSetoids F J ↔
      Presheaf.IsSheaf J (ObjectClassPresheaf F) := by
  sorry

theorem stack_in_setoids_characterization {C : Type u} [Category.{v} C]
    (F : FiberedCategory C) (J : GrothendieckTopology C)
    (hF : FiberwiseSetoid F) :
    StackInSetoids F J ↔ Stack F J := by
  simp [StackInSetoids, hF]

theorem equivalent_stacks_in_setoids_preserve
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    {F G : FiberedCategory C} (η : FiberedMorphism F G)
    (hη : FiberwiseEquivalence η) :
    StackInSetoids F J ↔ StackInSetoids G J := by
  constructor
  · rintro ⟨hFsetoid, hFstack⟩
    have hGgroupstack :=
      (equivalent_stacks_in_groupoids_preserve η hη).mp
        ⟨hFsetoid.1, hFstack⟩
    refine ⟨⟨hGgroupstack.1, ?_⟩, hGgroupstack.2⟩
    intro U Y Z
    rcases hη.1 U with ⟨hηff⟩
    let hηess := hη.2 U
    let x := @Functor.objPreimage _ _ _ _ (η.app (.mk (op U))).toFunctor hηess Y
    let y := @Functor.objPreimage _ _ _ _ (η.app (.mk (op U))).toFunctor hηess Z
    let eY :=
      @Functor.objObjPreimageIso _ _ _ _ (η.app (.mk (op U))).toFunctor hηess Y
    let eZ :=
      @Functor.objObjPreimageIso _ _ _ _ (η.app (.mk (op U))).toFunctor hηess Z
    constructor
    intro a b
    let a' := hηff.preimage (eY.hom ≫ a ≫ eZ.inv)
    let b' := hηff.preimage (eY.hom ≫ b ≫ eZ.inv)
    have ha : (η.app (.mk (op U))).toFunctor.map a' =
        eY.hom ≫ a ≫ eZ.inv := hηff.map_preimage _
    have hb : (η.app (.mk (op U))).toFunctor.map b' =
        eY.hom ≫ b ≫ eZ.inv := hηff.map_preimage _
    have hab' : a' = b' := @Subsingleton.elim _ (hFsetoid.2 U x y) a' b'
    apply (cancel_epi eY.hom).1
    apply (cancel_mono eZ.inv).1
    calc
      (eY.hom ≫ a) ≫ eZ.inv = eY.hom ≫ a ≫ eZ.inv := by simp
      _ = (η.app (.mk (op U))).toFunctor.map a' := ha.symm
      _ = (η.app (.mk (op U))).toFunctor.map b' := by rw [hab']
      _ = eY.hom ≫ b ≫ eZ.inv := hb
      _ = (eY.hom ≫ b) ≫ eZ.inv := by simp
  · rintro ⟨hGsetoid, hGstack⟩
    have hFgroupstack :=
      (equivalent_stacks_in_groupoids_preserve η hη).mpr
        ⟨hGsetoid.1, hGstack⟩
    refine ⟨⟨hFgroupstack.1, ?_⟩, hFgroupstack.2⟩
    intro U X Y
    rcases hη.1 U with ⟨hηff⟩
    constructor
    intro a b
    apply hηff.map_injective
    exact @Subsingleton.elim _
      (hGsetoid.2 U
        ((η.app (.mk (op U))).toFunctor.obj X)
        ((η.app (.mk (op U))).toFunctor.obj Y))
      ((η.app (.mk (op U))).toFunctor.map a)
      ((η.app (.mk (op U))).toFunctor.map b)

theorem two_fibre_product_of_stacks_in_setoids
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    {F G H : FiberedCategory C} (hF : StackInSetoids F J)
    (hG : StackInSetoids G J) (hH : StackInSetoids H J)
    (f : FiberedMorphism F H) (g : FiberedMorphism G H) :
    ∃ P : TwoFiberProductCone F G H f g, StackInSetoids P.apex J := by
  sorry

theorem two_fibre_product_setoids_over_groupoid_stack
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    {F G H : FiberedCategory C} (hF : StackInSetoids F J)
    (hG : StackInSetoids G J) (hH : StackInGroupoids H J)
    (f : FiberedMorphism F H) (g : FiberedMorphism G H) :
    ∃ P : TwoFiberProductCone F G H f g, StackInSetoids P.apex J := by
  sorry

theorem faithful_descent_for_stacks_in_groupoids
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    {A B C' D : FiberedCategory C} (sq : TwoCartesianSquare A B C' D)
    (hlocal : LocallyEssentiallyInImage sq.bottom J)
    (hfaithful : FiberwiseFaithful sq.right)
    (hA : StackInGroupoids A J) (hB : StackInGroupoids B J)
    (hC' : StackInGroupoids C' J) (hD : StackInGroupoids D J) :
    FiberwiseFaithful sq.top := by
  sorry

theorem setoid_stack_descent
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    {A B C' D : FiberedCategory C} (sq : TwoCartesianSquare A B C' D)
    (hfullyFaithful : FiberwiseFullyFaithful sq.bottom)
    (hlocal : LocallyEssentiallyInImage sq.bottom J)
    (hA : StackInSetoids A J) (hB : StackInGroupoids B J)
    (hC' : StackInGroupoids C' J) (hD : StackInGroupoids D J) :
    StackInSetoids B J := by
  sorry

theorem relative_sheaf_over_groupoid_stack_is_stack
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    {F G : FiberedCategory C} (h : RelativeSheafCondition F G J) :
    StackInGroupoids F J := by
  sorry

end Formalization.Books.Stacks.Unit01
