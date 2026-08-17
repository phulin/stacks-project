import Formalization.Books.Categories.Unit40.RepresentableCategoriesFibredInGroupoids
import Formalization.Books.Categories.Unit41.TwoYonedaLemma
import Formalization.Books.Categories.Unit04.Products
import Formalization.Books.Categories.Unit06.FibreProducts

/-!
# Categories, Chapter 42: Representable 1-morphisms

The source studies representability of a morphism between categories fibred in
groupoids by pulling it back along every slice of the base.  Units 33--41
already provide the universe-polymorphic fibred-morphism, vertical iso-comma,
2-Yoneda, and representability interfaces used below.
-/

namespace Formalization.Books.Categories.Unit42

open CategoryTheory
open CategoryTheory.Functor
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty
open Opposite
open Formalization.Books.Categories.Unit31
open Formalization.Books.Categories.Unit33
open Formalization.Books.Categories.Unit34
open Formalization.Books.Categories.Unit35
open Formalization.Books.Categories.Unit40
open Formalization.Books.Categories.Unit41

universe uA vA uB vB uS vS uC vC

noncomputable section

/-! ## The 2-fibre product over a slice -/

/- `VerticalIsoComma` is the existing explicit category-valued construction
   of a 2-fibre product over a base.  The first factor below is the slice and
   the second factor is the source of `F`. -/
abbrev SlicePullbackCategory
    {X Y C : Type*} [Category* X] [Category* Y] [Category* C]
    {p : X ⥤ C} {q : Y ⥤ C}
    (F : FibredMorphism p q) (U : C)
    (G : FibredMorphism (Over.forget U) q) :=
  VerticalIsoComma G.functor F.functor
    (Over.forget U) p q G.over F.over

def slicePullbackBase
    {X Y C : Type*} [Category* X] [Category* Y] [Category* C]
    {p : X ⥤ C} {q : Y ⥤ C}
    (F : FibredMorphism p q) (U : C)
    (G : FibredMorphism (Over.forget U) q) :
    SlicePullbackCategory F U G ⥤ C :=
  verticalIsoCommaBase G.functor F.functor
    (Over.forget U) p q G.over F.over

def slicePullbackLeft
    {X Y C : Type*} [Category* X] [Category* Y] [Category* C]
    {p : X ⥤ C} {q : Y ⥤ C}
    (F : FibredMorphism p q) (U : C)
    (G : FibredMorphism (Over.forget U) q) :
    SlicePullbackCategory F U G ⥤ Over U :=
  (VerticalIsoCommaProperty G.functor F.functor
    (Over.forget U) p q G.over F.over).ι ⋙
      isoCommaLeft G.functor F.functor

def slicePullbackRight
    {X Y C : Type*} [Category* X] [Category* Y] [Category* C]
    {p : X ⥤ C} {q : Y ⥤ C}
    (F : FibredMorphism p q) (U : C)
    (G : FibredMorphism (Over.forget U) q) :
    SlicePullbackCategory F U G ⥤ X :=
  (VerticalIsoCommaProperty G.functor F.functor
    (Over.forget U) p q G.over F.over).ι ⋙
      isoCommaRight G.functor F.functor

/- This is the preparation lemma in the source.  It is stated using the
   actual projection to `C/U`, rather than only the composite to `C`. -/
theorem slicePullbackLeft_isFibredInGroupoids
    {X Y C : Type*} [Category* X] [Category* Y] [Category* C]
    {p : X ⥤ C} {q : Y ⥤ C}
    (hp : p.IsFibredInGroupoids) (hq : q.IsFibredInGroupoids)
    (F : FibredMorphism p q) (U : C)
    (G : FibredMorphism (Over.forget U) q) :
    (slicePullbackLeft F U G).IsFibredInGroupoids := by
  sorry

/- The source's definition of a representable 1-morphism. -/
def IsRepresentableFibredMorphism
    {X Y C : Type*} [Category* X] [Category* Y] [Category* C]
    {p : X ⥤ C} {q : Y ⥤ C}
    (_hp : p.IsFibredInGroupoids) (_hq : q.IsFibredInGroupoids)
    (F : FibredMorphism p q) : Prop :=
  ∀ (U : C) (G : FibredMorphism (Over.forget U) q),
    IsRepresentableCategoryFibredInGroupoids (slicePullbackLeft F U G)

/-! ## The fibre description -/

def sliceFibreObject {C : Type*} [Category* C] (U : C) (f : Over U) :
    Functor.Fiber (Over.forget U) f.left :=
  ⟨f, rfl⟩

def sliceMorphismIdentityValue
    {Y C : Type*} [Category* Y] [Category* C]
    {q : Y ⥤ C} (U : C)
    (G : FibredMorphism (Over.forget U) q) :
    Functor.Fiber q U :=
  ⟨G.functor.obj (Over.mk (𝟙 U)),
    Functor.congr_obj G.over (Over.mk (𝟙 U))⟩

def fibredMorphismFibreFunctor
    {X Y C : Type*} [Category* X] [Category* Y] [Category* C]
    {p : X ⥤ C} {q : Y ⥤ C} (F : FibredMorphism p q) (V : C) :
    Functor.Fiber p V ⥤ Functor.Fiber q V :=
  fibreFunctor p q F.functor F.over V

def sliceMorphismFibreFunctor
    {Y C : Type*} [Category* Y] [Category* C]
    {q : Y ⥤ C} (U : C) (G : FibredMorphism (Over.forget U) q) (V : C) :
    Functor.Fiber (Over.forget U) V ⥤ Functor.Fiber q V :=
  fibreFunctor (Over.forget U) q G.functor G.over V

/- `PullbackChoice` uses Mathlib's typeclass `IsFibered`, while the source
   presents fibredness in groupoids as an explicit hypothesis.  This wrapper
   carries the canonical `IsFibered` instance supplied by Unit 35 without
   changing the choice data itself. -/
def FibredPullbackChoice
    {Y C : Type*} [Category* Y] [Category* C]
    (q : Y ⥤ C) (hq : q.IsFibredInGroupoids) : Type _ :=
  letI : q.IsFibered :=
    ((fibredInGroupoids_iff_fibred_groupoid_fibres q).mp hq).2
  PullbackChoice q

noncomputable def defaultFibredPullbackChoice
    {Y C : Type*} [Category* Y] [Category* C]
    (q : Y ⥤ C) (hq : q.IsFibredInGroupoids) : FibredPullbackChoice q hq :=
  letI : q.IsFibered :=
    ((fibredInGroupoids_iff_fibred_groupoid_fibres q).mp hq).2
  PullbackChoice.default q

def chosenPullbackObject
    {Y C : Type*} [Category* Y] [Category* C]
    (q : Y ⥤ C) (hq : q.IsFibredInGroupoids)
    (P : FibredPullbackChoice q hq) {U : C}
    (y : Functor.Fiber q U) (f : Over U) :
    Functor.Fiber q f.left :=
  letI : q.IsFibered :=
    ((fibredInGroupoids_iff_fibred_groupoid_fibres q).mp hq).2
  P.pullback f.hom y

noncomputable def chosenPullbackMorphism
    {Y C : Type*} [Category* Y] [Category* C]
    (q : Y ⥤ C) (hq : q.IsFibredInGroupoids)
    (P : FibredPullbackChoice q hq) (U : C)
    (y : Functor.Fiber q U) :
    FibredMorphism (Over.forget U) q :=
  letI : q.IsFibered :=
    ((fibredInGroupoids_iff_fibred_groupoid_fibres q).mp hq).2
  { functor := twoYonedaPullbackFunctor q P U y
    over := twoYonedaPullbackFunctor_isOver q P U y
    preserves := twoYonedaPullbackFunctor_mapsStronglyCartesian q P U y }

def sliceMorphismAsTwoYonedaObject
    {Y C : Type*} [Category* Y] [Category* C]
    {q : Y ⥤ C} (U : C)
    (G : FibredMorphism (Over.forget U) q) :
    twoYonedaGroupoidMorphismCategory q U :=
  ⟨G.functor, G.over⟩

noncomputable def chosenPullbackAsTwoYonedaObject
    {Y C : Type*} [Category* Y] [Category* C]
    (q : Y ⥤ C) (hq : q.IsFibredInGroupoids)
    (P : FibredPullbackChoice q hq) (U : C)
    (y : Functor.Fiber q U) :
    twoYonedaGroupoidMorphismCategory q U :=
  let H := chosenPullbackMorphism q hq P U y
  ⟨H.functor, H.over⟩

theorem sliceMorphism_isomorphic_to_chosenPullback
    {Y C : Type*} [Category* Y] [Category* C]
    {q : Y ⥤ C} (U : C) (hq : q.IsFibredInGroupoids)
    (P : FibredPullbackChoice q hq)
    (G : FibredMorphism (Over.forget U) q) :
    Nonempty
      (sliceMorphismAsTwoYonedaObject U G ≅
        chosenPullbackAsTwoYonedaObject q hq P U
          (sliceMorphismIdentityValue U G)) := by
  sorry

structure RelativeFibrePair
    {X Y C : Type*} [Category* X] [Category* Y] [Category* C]
    {p : X ⥤ C} {q : Y ⥤ C} (F : FibredMorphism p q) (U : C)
    (hq : q.IsFibredInGroupoids) (P : FibredPullbackChoice q hq)
    (y : Functor.Fiber q U) (f : Over U) where
  x : Functor.Fiber p f.left
  phi : chosenPullbackObject q hq P y f ⟶
    (fibredMorphismFibreFunctor (p := p) (q := q) F f.left).obj x

structure RelativeFibrePairHom
    {X Y C : Type*} [Category* X] [Category* Y] [Category* C]
    {p : X ⥤ C} {q : Y ⥤ C} {F : FibredMorphism p q} {U : C}
    {hq : q.IsFibredInGroupoids} {P : FibredPullbackChoice q hq}
    {y : Functor.Fiber q U} {f : Over U}
    (A B : RelativeFibrePair F U hq P y f) where
  psi : A.x ⟶ B.x
  comm : A.phi ≫
      (fibredMorphismFibreFunctor (p := p) (q := q) F f.left).map psi = B.phi

@[ext]
lemma RelativeFibrePairHom.ext
    {X Y C : Type*} [Category* X] [Category* Y] [Category* C]
    {p : X ⥤ C} {q : Y ⥤ C} {F : FibredMorphism p q} {U : C}
    {hq : q.IsFibredInGroupoids} {P : FibredPullbackChoice q hq}
    {y : Functor.Fiber q U} {f : Over U}
    {A B : RelativeFibrePair F U hq P y f}
    {k l : RelativeFibrePairHom A B} (h : k.psi = l.psi) : k = l := by
  cases k
  cases l
  cases h
  rfl

instance relativeFibrePairCategory
    {X Y C : Type*} [Category* X] [Category* Y] [Category* C]
    {p : X ⥤ C} {q : Y ⥤ C} (F : FibredMorphism p q) (U : C)
    (hq : q.IsFibredInGroupoids) (P : FibredPullbackChoice q hq)
    (y : Functor.Fiber q U) (f : Over U) :
    Category (RelativeFibrePair F U hq P y f) where
  Hom A B := RelativeFibrePairHom A B
  id A :=
    { psi := 𝟙 A.x
      comm := by simp }
  comp k l :=
    { psi := k.psi ≫ l.psi
      comm := by
        rw [Functor.map_comp, ← Category.assoc, k.comm]
        exact l.comm }
  id_comp k := by
    apply RelativeFibrePairHom.ext
    simp
  comp_id k := by
    apply RelativeFibrePairHom.ext
    simp
  assoc k l m := by
    apply RelativeFibrePairHom.ext
    simp [Category.assoc]

abbrev RelativeFibrePairCategory
    {X Y C : Type*} [Category* X] [Category* Y] [Category* C]
    {p : X ⥤ C} {q : Y ⥤ C} (F : FibredMorphism p q) (U : C)
    (hq : q.IsFibredInGroupoids) (P : FibredPullbackChoice q hq)
    (y : Functor.Fiber q U) (f : Over U) :=
  RelativeFibrePair F U hq P y f

def relativeFibrePairIsoRelation
    {X Y C : Type*} [Category* X] [Category* Y] [Category* C]
    {p : X ⥤ C} {q : Y ⥤ C} (F : FibredMorphism p q) (U : C)
    (hq : q.IsFibredInGroupoids) (P : FibredPullbackChoice q hq)
    (y : Functor.Fiber q U) (f : Over U) :
    Setoid (RelativeFibrePairCategory F U hq P y f) where
  r A B := Nonempty (A ≅ B)
  iseqv :=
    { refl := fun A => ⟨Iso.refl A⟩
      symm := fun h => ⟨(Classical.choice h).symm⟩
      trans := fun h k =>
        ⟨(Classical.choice h).trans (Classical.choice k)⟩ }

abbrev RelativeFibrePairClass
    {X Y C : Type*} [Category* X] [Category* Y] [Category* C]
    {p : X ⥤ C} {q : Y ⥤ C} (F : FibredMorphism p q) (U : C)
    (hq : q.IsFibredInGroupoids) (P : FibredPullbackChoice q hq)
    (y : Functor.Fiber q U) (f : Over U) :=
  Quotient (relativeFibrePairIsoRelation F U hq P y f)

theorem relativeFibrePair_phi_isIso
    {X Y C : Type*} [Category* X] [Category* Y] [Category* C]
    {p : X ⥤ C} {q : Y ⥤ C} (F : FibredMorphism p q) (U : C)
    (hq : q.IsFibredInGroupoids) (P : FibredPullbackChoice q hq)
    (y : Functor.Fiber q U) (f : Over U)
    (A : RelativeFibrePairCategory F U hq P y f) : IsIso A.phi := by
  sorry

noncomputable def relativeFibrePair_phi_inv
    {X Y C : Type*} [Category* X] [Category* Y] [Category* C]
    {p : X ⥤ C} {q : Y ⥤ C} (F : FibredMorphism p q) (U : C)
    (hq : q.IsFibredInGroupoids) (P : FibredPullbackChoice q hq)
    (y : Functor.Fiber q U) (f : Over U)
    (A : RelativeFibrePairCategory F U hq P y f) :
    (fibredMorphismFibreFunctor (p := p) (q := q) F f.left).obj A.x ⟶
      chosenPullbackObject q hq P y f := by
  letI : IsIso A.phi := relativeFibrePair_phi_isIso F U hq P y f A
  exact inv A.phi

theorem relativeFibrePairHom_comm_iff
    {X Y C : Type*} [Category* X] [Category* Y] [Category* C]
    {p : X ⥤ C} {q : Y ⥤ C} (F : FibredMorphism p q) (U : C)
    (hq : q.IsFibredInGroupoids) (P : FibredPullbackChoice q hq)
    (y : Functor.Fiber q U) (f : Over U)
    (A B : RelativeFibrePairCategory F U hq P y f)
    (psi : A.x ⟶ B.x) :
    A.phi ≫
          (fibredMorphismFibreFunctor (p := p) (q := q) F f.left).map psi = B.phi ↔
      (fibredMorphismFibreFunctor (p := p) (q := q) F f.left).map psi =
        relativeFibrePair_phi_inv F U hq P y f A ≫ B.phi := by
  sorry

def pullbackFibreBaseObject
    {Y C : Type*} [Category* Y] [Category* C]
    {q : Y ⥤ C} (U : C)
    (G : FibredMorphism (Over.forget U) q) (f : Over U) :
    Functor.Fiber q f.left :=
  (sliceMorphismFibreFunctor U G f.left).obj (sliceFibreObject U f)

structure PullbackFibreObject
    {X Y C : Type*} [Category* X] [Category* Y] [Category* C]
    {p : X ⥤ C} {q : Y ⥤ C} (F : FibredMorphism p q) (U : C)
    (G : FibredMorphism (Over.forget U) q) (f : Over U) where
  x : Functor.Fiber p f.left
  phi : pullbackFibreBaseObject (q := q) U G f ⟶
    (fibredMorphismFibreFunctor (p := p) (q := q) F f.left).obj x

structure PullbackFibreHom
    {X Y C : Type*} [Category* X] [Category* Y] [Category* C]
    {p : X ⥤ C} {q : Y ⥤ C} {F : FibredMorphism p q} {U : C}
    {G : FibredMorphism (Over.forget U) q} {f : Over U}
  (A B : PullbackFibreObject F U G f) where
  psi : A.x ⟶ B.x
  comm : A.phi ≫
      (fibredMorphismFibreFunctor (p := p) (q := q) F f.left).map psi = B.phi

@[ext]
lemma PullbackFibreHom.ext
    {X Y C : Type*} [Category* X] [Category* Y] [Category* C]
    {p : X ⥤ C} {q : Y ⥤ C} {F : FibredMorphism p q} {U : C}
    {G : FibredMorphism (Over.forget U) q} {f : Over U}
    {A B : PullbackFibreObject F U G f}
    {k l : PullbackFibreHom A B} (h : k.psi = l.psi) : k = l := by
  cases k
  cases l
  cases h
  rfl

instance pullbackFibreCategory
    {X Y C : Type*} [Category* X] [Category* Y] [Category* C]
    {p : X ⥤ C} {q : Y ⥤ C} (F : FibredMorphism p q) (U : C)
    (G : FibredMorphism (Over.forget U) q) (f : Over U) :
    Category (PullbackFibreObject F U G f) where
  Hom A B := PullbackFibreHom A B
  id A :=
    { psi := 𝟙 A.x
      comm := by simp }
  comp k l :=
    { psi := k.psi ≫ l.psi
      comm := by
        rw [Functor.map_comp, ← Category.assoc, k.comm]
        exact l.comm }
  id_comp k := by
    apply PullbackFibreHom.ext
    simp
  comp_id k := by
    apply PullbackFibreHom.ext
    simp
  assoc k l m := by
    apply PullbackFibreHom.ext
    simp [Category.assoc]

abbrev PullbackFibreCategory
    {X Y C : Type*} [Category* X] [Category* Y] [Category* C]
    {p : X ⥤ C} {q : Y ⥤ C} (F : FibredMorphism p q) (U : C)
    (G : FibredMorphism (Over.forget U) q) (f : Over U) :=
  PullbackFibreObject F U G f

def pullbackFibreObjectIsoRelation
    {X Y C : Type*} [Category* X] [Category* Y] [Category* C]
    {p : X ⥤ C} {q : Y ⥤ C} (F : FibredMorphism p q) (U : C)
    (G : FibredMorphism (Over.forget U) q) (f : Over U) :
    Setoid (PullbackFibreCategory F U G f) where
  r A B := Nonempty (A ≅ B)
  iseqv :=
    { refl := fun A => ⟨Iso.refl A⟩
      symm := fun h => ⟨(Classical.choice h).symm⟩
      trans := fun h k =>
        ⟨(Classical.choice h).trans (Classical.choice k)⟩ }

abbrev PullbackFibreObjectClass
    {X Y C : Type*} [Category* X] [Category* Y] [Category* C]
    {p : X ⥤ C} {q : Y ⥤ C} (F : FibredMorphism p q) (U : C)
    (G : FibredMorphism (Over.forget U) q) (f : Over U) :=
  Quotient (pullbackFibreObjectIsoRelation F U G f)

theorem pullbackFibreObject_phi_isIso
    {X Y C : Type*} [Category* X] [Category* Y] [Category* C]
    {p : X ⥤ C} {q : Y ⥤ C} (hq : q.IsFibredInGroupoids)
    (F : FibredMorphism p q) (U : C)
    (G : FibredMorphism (Over.forget U) q) (f : Over U)
    (A : PullbackFibreCategory F U G f) : IsIso A.phi := by
  sorry

theorem identify_pullback_fibre
    {X Y C : Type*} [Category* X] [Category* Y] [Category* C]
    {p : X ⥤ C} {q : Y ⥤ C} (hp : p.IsFibredInGroupoids)
    (hq : q.IsFibredInGroupoids) (F : FibredMorphism p q) (U : C)
    (G : FibredMorphism (Over.forget U) q) (f : Over U) :
    Nonempty
      (Functor.Fiber (slicePullbackLeft F U G) f ≌
        PullbackFibreCategory F U G f) := by
  sorry

theorem identify_pullback_fibre_with_chosen_pullback
    {X Y C : Type*} [Category* X] [Category* Y] [Category* C]
    {p : X ⥤ C} {q : Y ⥤ C} (hp : p.IsFibredInGroupoids)
    (hq : q.IsFibredInGroupoids) (F : FibredMorphism p q) (U : C)
    (P : FibredPullbackChoice q hq)
    (G : FibredMorphism (Over.forget U) q) (f : Over U) :
    Nonempty
      (Functor.Fiber (slicePullbackLeft F U G) f ≌
        RelativeFibrePairCategory F U hq P
          (sliceMorphismIdentityValue U G) f) := by
  sorry

/-! ## Faithfulness and the presheaf criterion -/

theorem representable_fibredMorphism_fibrewise_faithful
    {X Y C : Type*} [Category* X] [Category* Y] [Category* C]
    {p : X ⥤ C} {q : Y ⥤ C}
    (hp : p.IsFibredInGroupoids) (hq : q.IsFibredInGroupoids)
    (F : FibredMorphism p q)
    (hF : IsRepresentableFibredMorphism hp hq F) :
    ∀ U : C, (fibredMorphismFibreFunctor F U).Faithful := by
  sorry

/- The source writes the values as isomorphism classes of pairs.  This
   structure records the presheaf, its values, and its restriction maps
   explicitly, while leaving the standard pullback construction available to
   the proof of the criterion. -/
structure RelativeFibrePresheafData
    {X : Type uA} {Y : Type uB} {C : Type uC}
    [Category.{vA} X] [Category.{vB} Y] [Category.{vC} C]
    {p : X ⥤ C} {q : Y ⥤ C} (F : FibredMorphism p q) (U : C)
    (hq : q.IsFibredInGroupoids)
    (pullbacksY : FibredPullbackChoice q hq)
    (y : Functor.Fiber q U) where
  presheaf : (Over U)ᵒᵖ ⥤ Type (max (max (max uA uB) (max vA vB)) (max uC vC))
  classEquiv : ∀ f : Over U,
    presheaf.obj (op f) ≃ RelativeFibrePairClass F U hq pullbacksY y f
  classRestriction : ∀ {f g : Over U} (_a : f ⟶ g),
    RelativeFibrePairClass F U hq pullbacksY y g →
      RelativeFibrePairClass F U hq pullbacksY y f
  classRestriction_id : ∀ f x, classRestriction (𝟙 f) x = x
  classRestriction_comp : ∀ {f g h : Over U} (a : f ⟶ g) (b : g ⟶ h) x,
    classRestriction (a ≫ b) x =
      classRestriction a (classRestriction b x)
  classEquiv_natural : ∀ {f g : Over U} (a : f ⟶ g)
    (x : presheaf.obj (op g)),
    classEquiv f (presheaf.map (op a) x) =
      classRestriction a (classEquiv g x)

def RelativeFibrePresheafData.IsRepresentable
    {X : Type uA} {Y : Type uB} {C : Type uC}
    [Category.{vA} X] [Category.{vB} Y] [Category.{vC} C]
    {p : X ⥤ C} {q : Y ⥤ C} {F : FibredMorphism p q} {U : C}
    {hq : q.IsFibredInGroupoids}
    {pullbacksY : FibredPullbackChoice q hq}
    {y : Functor.Fiber q U}
    (D : RelativeFibrePresheafData F U hq pullbacksY y) : Prop :=
  Functor.IsRepresentable D.presheaf

theorem criterion_for_representable_fibredMorphism
    {X Y C : Type*} [Category* X] [Category* Y] [Category* C]
    {p : X ⥤ C} {q : Y ⥤ C}
    (hp : p.IsFibredInGroupoids) (hq : q.IsFibredInGroupoids)
    (F : FibredMorphism p q) (pullbacksY : FibredPullbackChoice q hq)
    (hfaithful : ∀ U : C, (fibredMorphismFibreFunctor F U).Faithful)
    (hpresheaf : ∀ (U : C) (y : Functor.Fiber q U),
      ∃ D : RelativeFibrePresheafData F U hq pullbacksY y,
        D.IsRepresentable) :
    IsRepresentableFibredMorphism hp hq F := by
  sorry

/-! ## 2-products and the diagonal -/

theorem identityFunctor_isStronglyCartesian
    {C : Type*} [Category* C] {R S : C} (f : R ⟶ S) :
    (𝟭 C).IsStronglyCartesian f f := by
  let hf : (𝟭 C).IsHomLift f f := by
    exact Functor.IsHomLift.map f
  refine { toIsHomLift := hf, universal_property' := ?_ }
  intro c g φ hφ
  refine ⟨g, ⟨Functor.IsHomLift.map g, ?_⟩, ?_⟩
  · simpa using (CategoryTheory.IsHomLift.eq_of_isHomLift (𝟭 C) (g ≫ f) φ)
  · intro χ hχ
    simpa using
      (@CategoryTheory.IsHomLift.eq_of_isHomLift _ _ _ _
        (𝟭 C) _ _ g χ hχ.1).symm

theorem toBase_mapsStronglyCartesian
    {X C : Type*} [Category* X] [Category* C] (p : X ⥤ C) :
    MapsStronglyCartesian p (𝟭 C) p := by
  intro a b φ hφ
  change Functor.IsStronglyCartesian (𝟭 C)
    ((𝟭 C).map (p.map φ)) ((𝟭 C).map (p.map φ))
  exact identityFunctor_isStronglyCartesian _

def toBaseFibredMorphism
    {X C : Type*} [Category* X] [Category* C] (p : X ⥤ C) :
    FibredMorphism p (𝟭 C) where
  functor := p
  over := Functor.comp_id p
  preserves := toBase_mapsStronglyCartesian p

abbrev TwoProductCategory
    {X Y C : Type*} [Category* X] [Category* Y] [Category* C]
    (p : X ⥤ C) (q : Y ⥤ C) :=
  VerticalIsoComma p q p q (𝟭 C)
    (toBaseFibredMorphism p).over (toBaseFibredMorphism q).over

def twoProductBase
    {X Y C : Type*} [Category* X] [Category* Y] [Category* C]
    (p : X ⥤ C) (q : Y ⥤ C) :
    TwoProductCategory p q ⥤ C :=
  verticalIsoCommaBase p q p q (𝟭 C)
    (toBaseFibredMorphism p).over (toBaseFibredMorphism q).over

theorem twoProductBase_isFibredInGroupoids
    {X C : Type*} [Category* X] [Category* C]
    (p : X ⥤ C) (hp : p.IsFibredInGroupoids) :
    (twoProductBase p p).IsFibredInGroupoids := by
  sorry

def rawDiagonalFunctor
    {X C : Type*} [Category* X] [Category* C] (p : X ⥤ C) :
    X ⥤ TwoProductCategory p p where
  obj x :=
    { obj := (isoCommaDiagonal p).obj x
      property := by
        refine ⟨p.obj x, rfl, rfl, ?_⟩
        exact Functor.IsHomLift.map (𝟙 (p.obj x)) }
  map f := ObjectProperty.homMk ((isoCommaDiagonal p).map f)
  map_id := by
    intro x
    apply ObjectProperty.hom_ext
    rfl
  map_comp := by
    intro x y z f g
    apply ObjectProperty.hom_ext
    rfl

theorem rawDiagonalFunctor_over
    {X C : Type*} [Category* X] [Category* C] (p : X ⥤ C) :
    rawDiagonalFunctor p ⋙ twoProductBase p p = p := by
  rfl

theorem rawDiagonalFunctor_mapsStronglyCartesian
    {X C : Type*} [Category* X] [Category* C]
    (p : X ⥤ C) (hp : p.IsFibredInGroupoids) :
    MapsStronglyCartesian p (twoProductBase p p) (rawDiagonalFunctor p) := by
  sorry

def rawDiagonalMorphism
    {X C : Type*} [Category* X] [Category* C]
    (p : X ⥤ C) (hp : p.IsFibredInGroupoids) :
    FibredMorphism p (twoProductBase p p) where
  functor := rawDiagonalFunctor p
  over := rawDiagonalFunctor_over p
  preserves := rawDiagonalFunctor_mapsStronglyCartesian p hp

def IsRepresentableDiagonal
    {X C : Type*} [Category* X] [Category* C]
    (p : X ⥤ C) (hp : p.IsFibredInGroupoids) : Prop :=
  IsRepresentableFibredMorphism hp (twoProductBase_isFibredInGroupoids p hp)
    (rawDiagonalMorphism p hp)

theorem representable_diagonal_iff_slice_representable
    {X C : Type*} [Category* X] [Category* C]
    (p : X ⥤ C) (hp : p.IsFibredInGroupoids)
    [HasBinaryProducts C] [HasPullbacks C] :
    IsRepresentableDiagonal p hp ↔
      ∀ (U : C) (G : FibredMorphism (Over.forget U) p),
        IsRepresentableFibredMorphism
          (sliceProjection_isFibredInGroupoids U) hp G := by
  sorry

end

end Formalization.Books.Categories.Unit42
