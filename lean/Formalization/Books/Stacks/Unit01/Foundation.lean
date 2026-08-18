import Mathlib.CategoryTheory.Bicategory.FunctorBicategory.Pseudo
import Mathlib.Tactic.CategoryTheory.Bicategory.PureCoherence
import Mathlib.Tactic.CategoryTheory.Bicategory.Basic
import Mathlib.CategoryTheory.Sites.Descent.IsStack
import Mathlib.CategoryTheory.Groupoid.Discrete
import Formalization.Books.Categories.Unit31.TwoFibreProducts

/-!
# Stacks, Chapter 1: shared interfaces

Mathlib's descent library presents a fibred category by a pseudofunctor to
`Cat`.  The chapter files use that established presentation directly.
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

abbrev FiberedCategory (C : Type u) [Category.{v} C] :=
  Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{w, w}

abbrev Fiber (F : FiberedCategory C) (U : C) := F.obj (.mk (op U))

abbrev Over (C : Type u) [Category.{v} C] (U : C) := CategoryTheory.Over U

abbrev MorPresheaf (F : FiberedCategory C) {U : C}
    (x y : Fiber F U) : (Over C U)ᵒᵖ ⥤ Type w :=
  F.presheafHom x y

abbrev IsomSection (F : FiberedCategory C) {U : C} (x y : Fiber F U)
    (T : (Over C U)ᵒᵖ) := { f : (F.presheafHom x y).obj T // IsIso f }

def IsomPresheaf (F : FiberedCategory C) {U : C} (x y : Fiber F U) :
    (Over C U)ᵒᵖ ⥤ Type w where
  obj T := IsomSection F x y T
  map {T₁ T₂} q := ↾fun (f : { f : (F.presheafHom x y).obj T₁ // IsIso f }) =>
      (⟨(F.presheafHom x y).map q f.1, by
        rcases f.property.out with ⟨g, h₁, h₂⟩
        let g' : (F.presheafHom y x).obj T₁ := by
          simpa [Pseudofunctor.presheafHom] using g
        refine ⟨(F.presheafHom y x).map q g', ?_, ?_⟩
        · simpa [g', Pseudofunctor.presheafHom,
            Pseudofunctor.LocallyDiscreteOpToCat.pullHom] using
            congrArg (fun h => (F.presheafHom x x).map q h) h₁
        · simpa [g', Pseudofunctor.presheafHom,
            Pseudofunctor.LocallyDiscreteOpToCat.pullHom] using
            congrArg (fun h => (F.presheafHom y y).map q h) h₂⟩ :
        { f : (F.presheafHom x y).obj T₂ // IsIso f })
  map_id T := by
    ext f
    simp
  map_comp f g := by
    ext h
    simp

abbrev DescentData (F : FiberedCategory C) {ι : Type t} {U : C}
    {X : ι → C} (f : ∀ i, X i ⟶ U) := F.DescentData f

def EffectiveDescentData (F : FiberedCategory C) {ι : Type t} {U : C}
    {X : ι → C} (f : ∀ i, X i ⟶ U) (D : F.DescentData f) : Prop :=
  ∃ M, Nonempty ((F.toDescentData f).obj M ≅ D)

def CoveringFamily (J : GrothendieckTopology C) {ι : Type t} {U : C}
    {X : ι → C} (f : ∀ i, X i ⟶ U) : Prop :=
  Sieve.ofArrows X f ∈ J U

abbrev Prestack (F : FiberedCategory C) (J : GrothendieckTopology C) : Prop :=
  F.IsPrestack J

abbrev Stack (F : FiberedCategory C) (J : GrothendieckTopology C) : Prop :=
  F.IsStack J

def FiberwiseGroupoid (F : FiberedCategory C) : Prop :=
  ∀ U : C, IsGroupoid (Fiber F U)

def FiberwiseSetoid (F : FiberedCategory C) : Prop :=
  FiberwiseGroupoid F ∧
    ∀ (U : C) (X Y : Fiber F U), Subsingleton (X ⟶ Y)

def FiberwiseSet (F : FiberedCategory C) : Prop :=
  ∀ U : C, IsDiscrete (Fiber F U)

abbrev FiberedMorphism (F G : FiberedCategory C) := F ⟶ G

def FiberwiseFullyFaithful {F G : FiberedCategory C}
    (η : FiberedMorphism F G) : Prop :=
  ∀ U : C, Nonempty (η.app (.mk (op U))).toFunctor.FullyFaithful

def FiberwiseEssentiallySurjective {F G : FiberedCategory C}
    (η : FiberedMorphism F G) : Prop :=
  ∀ U : C, (η.app (.mk (op U))).toFunctor.EssSurj

def FiberwiseEquivalence {F G : FiberedCategory C}
    (η : FiberedMorphism F G) : Prop :=
  FiberwiseFullyFaithful η ∧ FiberwiseEssentiallySurjective η

/-! ### Transport of descent data along a fibred morphism

The component of a strong transformation sends the objects in a descent
datum to objects in the target fibres.  Its naturality isomorphisms transport
the gluing morphisms.  The coherence fields below are deliberately kept in
the standard `Pseudofunctor.DescentData` presentation, so later stack
arguments can use Mathlib's descent-data functors directly.
-/

noncomputable def descentDataFunctor
    {C : Type u} [Category.{v} C] {F G : FiberedCategory C}
    (η : FiberedMorphism F G) {ι : Type t} {U : C} {X : ι → C}
    (f : ∀ i, X i ⟶ U) : F.DescentData f ⥤ G.DescentData f where
  obj D :=
    { obj i := (η.app (.mk (op (X i)))).toFunctor.obj (D.obj i)
      hom Y q i₁ i₂ f₁ f₂ hf₁ hf₂ :=
        (η.naturality f₁.op.toLoc).inv.toNatTrans.app (D.obj i₁) ≫
          (η.app (.mk (op Y))).toFunctor.map
            (D.hom q f₁ f₂ hf₁ hf₂) ≫
          (η.naturality f₂.op.toLoc).hom.toNatTrans.app (D.obj i₂)
      pullHom_hom := by
        intros Y' Y g q q' hq i₁ i₂ f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂
        subst q'
        subst gf₁
        subst gf₂
        rw [← D.pullHom_hom g q (g ≫ q) rfl f₁ f₂ hf₁ hf₂
          (g ≫ f₁) (g ≫ f₂) rfl rfl]
        simp only [Pseudofunctor.LocallyDiscreteOpToCat.pullHom, op_comp,
          Quiver.Hom.comp_toLoc]
        simp only [Pseudofunctor.mapComp'_eq_mapComp]
        simp [Cat.Hom.comp_toFunctor, Functor.map_comp,
          Pseudofunctor.StrongTrans.naturality_comp_hom,
          Pseudofunctor.StrongTrans.naturality_comp_inv, Category.assoc]
        have hg :
            (η.naturality g.op.toLoc).inv.toNatTrans.app
                ((F.map f₁.op.toLoc).toFunctor.obj (D.obj i₁)) ≫
              (η.app (.mk (op Y'))).toFunctor.map
                ((F.map g.op.toLoc).toFunctor.map
                  (D.hom q f₁ f₂ hf₁ hf₂)) ≫
              (η.naturality g.op.toLoc).hom.toNatTrans.app
                ((F.map f₂.op.toLoc).toFunctor.obj (D.obj i₂)) =
            (G.map g.op.toLoc).toFunctor.map
              ((η.app (.mk (op Y))).toFunctor.map
                (D.hom q f₁ f₂ hf₁ hf₂)) := by
          have h := NatIso.naturality_1
            (Cat.Hom.toNatIso (η.naturality g.op.toLoc))
            (D.hom q f₁ f₂ hf₁ hf₂)
          simpa only [Cat.Hom.toNatIso, Cat.Hom.comp_toFunctor,
            Functor.comp_map] using h
        rw [← hg]
        rw [← (η.app (.mk (op Y'))).toFunctor.map_comp_assoc]
        rw [← (η.app (.mk (op Y'))).toFunctor.map_comp_assoc]
        simp only [Cat.Hom.inv_hom_id_toNatTrans_app,
          Category.assoc, Functor.map_id, Category.id_comp]
        simp
      hom_self := by
        intros Y q i g hg
        have h := D.hom_self q g hg
        rw [h]
        simp
      hom_comp := by
        intros Y q i₁ i₂ i₃ f₁ f₂ f₃ hf₁ hf₂ hf₃
        simp only [Category.assoc, Cat.Hom.hom_inv_id_toNatTrans_app_assoc,
          Category.id_comp]
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
        dsimp
        simp only [Category.assoc]
        change
          (G.map f₁.op.toLoc).toFunctor.map
                ((η.app (.mk (op (X i₁)))).toFunctor.map (φ.hom i₁)) ≫
              (η.naturality f₁.op.toLoc).inv.toNatTrans.app (D₂.obj i₁) ≫
            (η.app (.mk (op Y))).toFunctor.map
                (D₂.hom q f₁ f₂ hf₁ hf₂) ≫
              (η.naturality f₂.op.toLoc).hom.toNatTrans.app (D₂.obj i₂) =
            (η.naturality f₁.op.toLoc).inv.toNatTrans.app (D₁.obj i₁) ≫
              (η.app (.mk (op Y))).toFunctor.map
                (D₁.hom q f₁ f₂ hf₁ hf₂) ≫
              (η.naturality f₂.op.toLoc).hom.toNatTrans.app (D₁.obj i₂) ≫
            (G.map f₂.op.toLoc).toFunctor.map
                ((η.app (.mk (op (X i₂)))).toFunctor.map (φ.hom i₂))
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
        simpa only [Functor.map_comp, Category.assoc] using congrArg (fun k =>
          (η.naturality f₁.op.toLoc).inv.toNatTrans.app (D₁.obj i₁) ≫ k ≫
            (η.naturality f₂.op.toLoc).hom.toNatTrans.app (D₂.obj i₂))
          (congrArg ((η.app (.mk (op Y))).toFunctor.map)
            (φ.comm q f₁ f₂ hf₁ hf₂)) }

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
  sorry

noncomputable def descentDataEquivalence
    {C : Type u} [Category.{v} C] {F G : FiberedCategory C}
    (η : FiberedMorphism F G) (hη : FiberwiseEquivalence η)
    {ι : Type t} {U : C} {X : ι → C}
    (f : ∀ i, X i ⟶ U) : F.DescentData f ≌ G.DescentData f := by
  letI : (descentDataFunctor η f).IsEquivalence :=
    descentDataFunctor_is_equivalence η hη f
  exact (descentDataFunctor η f).asEquivalence

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
  sorry

structure Substack (F : FiberedCategory C) (J : GrothendieckTopology C) where
  value : FiberedCategory C
  inclusion : FiberedMorphism value F
  fullyFaithful : FiberwiseFullyFaithful inclusion
  stableUnderPullback : ∀ {U V : C} (f : V ⟶ U) (x : Fiber value U),
    ∃ y : Fiber value V,
      Nonempty (y ≅ (value.map f.op.toLoc).toFunctor.obj x)
  locallyEssentiallyInImage : ∀ (U : C) (x : Fiber F U),
    ∃ (ι : Type t) (X : ι → C) (f : ∀ i, X i ⟶ U),
      CoveringFamily J f ∧
        ∀ i, ∃ y : Fiber value (X i),
          Nonempty ((F.map (f i).op.toLoc).toFunctor.obj x ≅
            (inclusion.app (.mk (op (X i)))).toFunctor.obj y)

def IsTwoPullbackCone {F G H A : FiberedCategory C}
    (f : FiberedMorphism F H) (g : FiberedMorphism G H)
    (left : FiberedMorphism A F) (right : FiberedMorphism A G)
    (commutes : left ≫ f ≅ right ≫ g) : Prop :=
  ∀ (Q : FiberedCategory C) (a : FiberedMorphism Q F)
      (b : FiberedMorphism Q G) (α : a ≫ f ≅ b ≫ g),
    ∃ (u : FiberedMorphism Q A) (lam : u ≫ left ≅ a)
      (rho : u ≫ right ≅ b),
      (Bicategory.whiskerRight lam.hom f) ≫ α.hom =
          (Bicategory.associator u left f).hom ≫
            Bicategory.whiskerLeft u commutes.hom ≫
              (Bicategory.associator u right g).inv ≫
                (Bicategory.whiskerRight rho.hom g) ∧
        ∀ (v : FiberedMorphism Q A) (lam' : v ≫ left ≅ a)
          (rho' : v ≫ right ≅ b),
          (Bicategory.whiskerRight lam'.hom f) ≫ α.hom =
              (Bicategory.associator v left f).hom ≫
                Bicategory.whiskerLeft v commutes.hom ≫
                  (Bicategory.associator v right g).inv ≫
                    (Bicategory.whiskerRight rho'.hom g) →
            ∃! β : u ⟶ v,
              (Bicategory.whiskerRight β left) ≫ lam'.hom = lam.hom ∧
                (Bicategory.whiskerRight β right) ≫ rho'.hom = rho.hom

structure TwoFiberProductCone (F G H : FiberedCategory C)
    (f : FiberedMorphism F H) (g : FiberedMorphism G H) where
  apex : FiberedCategory C
  left : FiberedMorphism apex F
  right : FiberedMorphism apex G
  commutes : left ≫ f ≅ right ≫ g
  isTwoPullback : IsTwoPullbackCone f g left right commutes

/-! ### The canonical pointwise two-fibre product

The value of the two-fibre product over `U` is the iso-comma category of the
two component functors `f.app U` and `g.app U`.  The map on a morphism `q` of
the base is the iso-comma map induced by the three reindexing functors and the
two strong-transformation coherence isomorphisms.  The coherence fields of
the resulting pseudofunctor, and its bicategorical universal property, are
recorded below so that later stack arguments use one canonical cone.
-/

noncomputable def pointwiseTwoFiberProductReindex
    {C : Type u} [Category.{v} C]
    {F G H : FiberedCategory C} (f : FiberedMorphism F H)
    (g : FiberedMorphism G H) {U V : LocallyDiscrete Cᵒᵖ} (q : U ⟶ V) :
    IsoComma ((f.app U).toFunctor) ((g.app U).toFunctor) ⥤
      IsoComma ((f.app V).toFunctor) ((g.app V).toFunctor) :=
  isoCommaMap
    ((f.app V).toFunctor) ((g.app V).toFunctor)
    ((f.app U).toFunctor) ((g.app U).toFunctor)
    ((F.map q).toFunctor) ((G.map q).toFunctor) ((H.map q).toFunctor)
    (Cat.Hom.toNatIso (g.naturality q))
    (Cat.Hom.toNatIso (f.naturality q).symm)

noncomputable def pointwiseTwoFiberProductApex
    {C : Type u} [Category.{v} C]
    {F G H : FiberedCategory C} (f : FiberedMorphism F H)
    (g : FiberedMorphism G H) : FiberedCategory C :=
  LocallyDiscrete.mkPseudofunctor
    (fun U : Cᵒᵖ =>
      Cat.of (IsoComma ((f.app (.mk U)).toFunctor) ((g.app (.mk U)).toFunctor)))
    (fun {U V : Cᵒᵖ} q =>
      (pointwiseTwoFiberProductReindex f g (Discrete.mk q)).toCatHom)
    (fun U => by
      sorry)
    (fun {U V W : Cᵒᵖ} q r => by
      sorry)
    (fun {U V W X : Cᵒᵖ} q r s => by
      sorry)
    (fun {U V : Cᵒᵖ} q => by
      sorry)
    (fun {U V : Cᵒᵖ} q => by
      sorry)

noncomputable def pointwiseTwoFiberProductLeft
    {C : Type u} [Category.{v} C]
    {F G H : FiberedCategory C} (f : FiberedMorphism F H)
    (g : FiberedMorphism G H) :
    FiberedMorphism (pointwiseTwoFiberProductApex f g) F := by
  exact
    { app := fun U => by
        change Cat.of (IsoComma ((f.app U).toFunctor) ((g.app U).toFunctor)) ⟶ F.obj U
        exact (isoCommaLeft ((f.app U).toFunctor) ((g.app U).toFunctor)).toCatHom
      naturality := by
        intro U V q
        sorry
      naturality_naturality := by
        intro U V q r h
        sorry
      naturality_id := by
        intro U
        sorry
      naturality_comp := by
        intro U V W q r
        sorry }

noncomputable def pointwiseTwoFiberProductRight
    {C : Type u} [Category.{v} C]
    {F G H : FiberedCategory C} (f : FiberedMorphism F H)
    (g : FiberedMorphism G H) :
    FiberedMorphism (pointwiseTwoFiberProductApex f g) G := by
  exact
    { app := fun U => by
        change Cat.of (IsoComma ((f.app U).toFunctor) ((g.app U).toFunctor)) ⟶ G.obj U
        exact (isoCommaRight ((f.app U).toFunctor) ((g.app U).toFunctor)).toCatHom
      naturality := by
        intro U V q
        sorry
      naturality_naturality := by
        intro U V q r h
        sorry
      naturality_id := by
        intro U
        sorry
      naturality_comp := by
        intro U V W q r
        sorry }

noncomputable def pointwiseTwoFiberProductCommutes
    {C : Type u} [Category.{v} C]
    {F G H : FiberedCategory C} (f : FiberedMorphism F H)
    (g : FiberedMorphism G H) :
    pointwiseTwoFiberProductLeft f g ≫ f ≅
      pointwiseTwoFiberProductRight f g ≫ g := by
  refine Pseudofunctor.StrongTrans.isoMk (fun U => ?_) ?_
  · dsimp [pointwiseTwoFiberProductLeft, pointwiseTwoFiberProductRight,
      Pseudofunctor.StrongTrans.vcomp]
    exact Cat.Hom.isoMk
      (isoCommaComparisonIso ((f.app U).toFunctor) ((g.app U).toFunctor))
  · intro U V q
    sorry

noncomputable def pointwiseTwoFiberProductCone
    {C : Type u} [Category.{v} C]
    {F G H : FiberedCategory C} (f : FiberedMorphism F H)
    (g : FiberedMorphism G H) : TwoFiberProductCone F G H f g :=
  { apex := pointwiseTwoFiberProductApex f g
    left := pointwiseTwoFiberProductLeft f g
    right := pointwiseTwoFiberProductRight f g
    commutes := pointwiseTwoFiberProductCommutes f g
    isTwoPullback := by
      sorry }

theorem pointwiseTwoFiberProductCone_isTwoPullback
    {C : Type u} [Category.{v} C]
    {F G H : FiberedCategory C} (f : FiberedMorphism F H)
    (g : FiberedMorphism G H) :
    IsTwoPullbackCone f g
      (pointwiseTwoFiberProductCone f g).left
      (pointwiseTwoFiberProductCone f g).right
      (pointwiseTwoFiberProductCone f g).commutes :=
  (pointwiseTwoFiberProductCone f g).isTwoPullback

theorem pointwiseTwoFiberProductCone_apex_is_stack
    {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C) {F G H : FiberedCategory C}
    (hF : Stack F J) (hG : Stack G J) (hH : Stack H J)
    (f : FiberedMorphism F H) (g : FiberedMorphism G H) :
    Stack (pointwiseTwoFiberProductCone f g).apex J := by
  sorry

theorem pointwise_two_fibre_product_of_stacks
    {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C) {F G H : FiberedCategory C}
    (hF : Stack F J) (hG : Stack G J) (hH : Stack H J)
    (f : FiberedMorphism F H) (g : FiberedMorphism G H) :
    ∃ P : TwoFiberProductCone F G H f g, Stack P.apex J := by
  refine ⟨pointwiseTwoFiberProductCone f g, ?_⟩
  exact pointwiseTwoFiberProductCone_apex_is_stack J hF hG hH f g

def IsSheafification {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C)
    {P Q : Cᵒᵖ ⥤ Type w} (η : P ⟶ Q) : Prop :=
  Presheaf.IsSheaf J Q ∧
    ∀ (R : Cᵒᵖ ⥤ Type w), Presheaf.IsSheaf J R →
      ∀ f : P ⟶ R, ∃! g : Q ⟶ R, η ≫ g = f

def IsInducedMorphismPresheafMap {C : Type u} [Category.{v} C]
    {F G : FiberedCategory C} (η : FiberedMorphism F G) {U : C}
    (x y : Fiber F U)
    (φ : F.presheafHom x y ⟶
      G.presheafHom ((η.app (.mk (op U))).toFunctor.obj x)
        ((η.app (.mk (op U))).toFunctor.obj y)) : Prop :=
  ∀ (T : (Over C U)ᵒᵖ)
    (f : (F.map T.unop.hom.op.toLoc).toFunctor.obj x ⟶
      (F.map T.unop.hom.op.toLoc).toFunctor.obj y),
    (φ.app T) f =
      (η.naturality T.unop.hom.op.toLoc).inv.toNatTrans.app x ≫
        (η.app (.mk (op T.unop.left))).toFunctor.map f ≫
          (η.naturality T.unop.hom.op.toLoc).hom.toNatTrans.app y

structure Stackification (F : FiberedCategory C) (J : GrothendieckTopology C) where
  value : FiberedCategory C
  map : FiberedMorphism F value
  isStack : Stack value J
  locallyFromMap : ∀ (U : C) (x' : Fiber value U),
    ∃ (ι : Type t) (X : ι → C) (f : ∀ i, X i ⟶ U),
      CoveringFamily J f ∧
        ∀ i, ∃ x : Fiber F (X i), Nonempty
          ((value.map (f i).op.toLoc).toFunctor.obj x' ≅
            (map.app (.mk (op (X i)))).toFunctor.obj x)
  morphismPresheafMap : ∀ (U : C) (x y : Fiber F U),
    F.presheafHom x y ⟶
      value.presheafHom ((map.app (.mk (op U))).toFunctor.obj x)
        ((map.app (.mk (op U))).toFunctor.obj y)
  morphismPresheafMap_is_induced : ∀ (U : C) (x y : Fiber F U),
    IsInducedMorphismPresheafMap map x y (morphismPresheafMap U x y)
  morphismSheafification : ∀ (U : C) (x y : Fiber F U),
    IsSheafification (J.over U) (morphismPresheafMap U x y)

/- TODO(stacks-foundation): Treat `Stackification` as a foundational
construction, not as data to synthesize independently in every theorem.  The
proof order is: sheafify each morphism presheaf, construct objects by effective
descent, assemble reindexing/coherence, and finally prove the hom-category
universal property.  Groupoid stackification, inertia comparisons, and
pullback/localization results should only be attempted after that API exists. -/

structure RelativeInertiaObject {F G : FiberedCategory C}
    (η : FiberedMorphism F G) (U : C) where
  object : Fiber F U
  automorphism : object ≅ object
  fixed : (η.app (.mk (op U))).toFunctor.map automorphism.hom = 𝟙 _

structure AbsoluteInertiaObject (F : FiberedCategory C) (U : C) where
  object : Fiber F U
  automorphism : object ≅ object

end Formalization.Books.Stacks.Unit01

#check CategoryTheory.Pseudofunctor.StrongTrans.naturality_comp_hom
#check CategoryTheory.Pseudofunctor.StrongTrans.naturality_comp_inv
#check CategoryTheory.Pseudofunctor.StrongTrans.naturality_naturality_hom
#check CategoryTheory.Pseudofunctor.StrongTrans.naturality_naturality_inv
#check CategoryTheory.Pseudofunctor.mapComp'_hom_naturality
#check CategoryTheory.Pseudofunctor.mapComp'_inv_naturality
