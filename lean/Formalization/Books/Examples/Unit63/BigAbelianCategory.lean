import Formalization.Books.Homology.Unit06.Extensions
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.SetTheory.Ordinal.Basic
import Mathlib.SetTheory.Ordinal.Family

/-!
# Examples, Chapter 63: A big abelian category

The source constructs a category whose objects are abelian groups equipped with
ordinally indexed endomorphisms.  The canonical `Extension` and `Ext`
interfaces from Homological Algebra, Chapter 6 are reused for the extension
classes; the large-category example itself is recorded at a fixed universe
level, as usual in Lean.
-/

universe u

namespace Formalization.Books.Examples.Unit63

open CategoryTheory
open CategoryTheory.Limits

noncomputable section

/-! ## The category of ordinally operated abelian groups -/

/-- An abelian group together with an ordinal and one endomorphism for every
ordinal strictly below that ordinal.  The source's convention that the
operator is zero outside the indexing ordinal is implemented by
`BigAbelianObject.operatorAt`. -/
structure BigAbelianObject where
  carrier : Type
  [addCommGroup : AddCommGroup carrier]
  index : Ordinal.{u}
  operator : Set.Iio index → (carrier →+ carrier)

instance BigAbelianObject.instAddCommGroup (X : BigAbelianObject) :
    AddCommGroup X.carrier := X.addCommGroup

/-- Evaluate the displayed family at any ordinal, extending it by zero past
the object's indexing ordinal. -/
def BigAbelianObject.operatorAt (X : BigAbelianObject) (β : Ordinal.{u}) :
    X.carrier →+ X.carrier :=
  if hβ : β < X.index then X.operator ⟨β, hβ⟩ else 0

@[simp]
theorem BigAbelianObject.operatorAt_of_lt (X : BigAbelianObject)
    {β : Ordinal.{u}} (hβ : β < X.index) :
    X.operatorAt β = X.operator ⟨β, hβ⟩ := by
  simp [BigAbelianObject.operatorAt, hβ]

@[simp]
theorem BigAbelianObject.operatorAt_of_not_lt (X : BigAbelianObject)
    {β : Ordinal.{u}} (hβ : ¬β < X.index) :
    X.operatorAt β = 0 := by
  simp [BigAbelianObject.operatorAt, hβ]

/-- A morphism commutes with every ordinal operator after the zero extension
outside the two indexing ordinals. -/
structure BigAbelianMorphism (X Y : BigAbelianObject) where
  hom : X.carrier →+ Y.carrier
  commutes : ∀ β : Ordinal.{u},
    hom.comp (X.operatorAt β) = (Y.operatorAt β).comp hom

@[ext]
theorem BigAbelianMorphism.ext {X Y : BigAbelianObject}
    (f g : BigAbelianMorphism X Y) (h : f.hom = g.hom) : f = g := by
  cases f
  cases g
  cases h
  rfl

def bigAbelianMorphismZero (X Y : BigAbelianObject) :
    BigAbelianMorphism X Y :=
  { hom := 0
    commutes := by
      intro β
      simp }

def bigAbelianMorphismAdd {X Y : BigAbelianObject}
    (f g : BigAbelianMorphism X Y) : BigAbelianMorphism X Y :=
    { hom := f.hom + g.hom
      commutes := by
        intro β
        apply AddMonoidHom.ext
        intro x
        have hf : f.hom (X.operatorAt β x) =
            (Y.operatorAt β) (f.hom x) := by
          simpa only [AddMonoidHom.comp_apply] using
            congrArg (fun h : X.carrier →+ Y.carrier => h x) (f.commutes β)
        have hg : g.hom (X.operatorAt β x) =
            (Y.operatorAt β) (g.hom x) := by
          simpa only [AddMonoidHom.comp_apply] using
            congrArg (fun h : X.carrier →+ Y.carrier => h x) (g.commutes β)
        simp only [AddMonoidHom.comp_apply, AddMonoidHom.add_apply, map_add]
        rw [hf, hg] }

def bigAbelianMorphismNeg {X Y : BigAbelianObject}
    (f : BigAbelianMorphism X Y) : BigAbelianMorphism X Y :=
    { hom := -f.hom
      commutes := by
        intro β
        apply AddMonoidHom.ext
        intro x
        have hf : f.hom (X.operatorAt β x) =
            (Y.operatorAt β) (f.hom x) := by
          simpa only [AddMonoidHom.comp_apply] using
            congrArg (fun h : X.carrier →+ Y.carrier => h x) (f.commutes β)
        simp only [AddMonoidHom.comp_apply, AddMonoidHom.neg_apply]
        rw [hf]
        simp }

instance bigAbelianMorphismZeroInstance (X Y : BigAbelianObject) :
    Zero (BigAbelianMorphism X Y) := ⟨bigAbelianMorphismZero X Y⟩

instance bigAbelianMorphismAddInstance (X Y : BigAbelianObject) :
    Add (BigAbelianMorphism X Y) := ⟨fun f g => bigAbelianMorphismAdd f g⟩

instance bigAbelianMorphismNegInstance (X Y : BigAbelianObject) :
    Neg (BigAbelianMorphism X Y) := ⟨bigAbelianMorphismNeg⟩

instance bigAbelianMorphismSubInstance (X Y : BigAbelianObject) :
    Sub (BigAbelianMorphism X Y) := ⟨fun f g => f + -g⟩

@[simp]
theorem bigAbelianMorphismZero_hom (X Y : BigAbelianObject) :
    (0 : BigAbelianMorphism X Y).hom = 0 :=
  rfl

@[simp]
theorem bigAbelianMorphismAdd_hom {X Y : BigAbelianObject}
    (f g : BigAbelianMorphism X Y) :
    (f + g).hom = f.hom + g.hom :=
  rfl

@[simp]
theorem bigAbelianMorphismNeg_hom {X Y : BigAbelianObject}
    (f : BigAbelianMorphism X Y) :
    (-f).hom = -f.hom :=
  rfl

instance bigAbelianMorphismAddCommGroup (X Y : BigAbelianObject) :
    AddCommGroup (BigAbelianMorphism X Y) where
  add_assoc := by
    intro f g h
    apply BigAbelianMorphism.ext
    exact add_assoc f.hom g.hom h.hom
  add_zero := by
    intro f
    apply BigAbelianMorphism.ext
    simp
  zero_add := by
    intro f
    apply BigAbelianMorphism.ext
    simp
  neg_add_cancel := by
    intro f
    apply BigAbelianMorphism.ext
    simp
  add_comm := by
    intro f g
    apply BigAbelianMorphism.ext
    simp [add_comm]
  sub_eq_add_neg := by
    intro f g
    apply BigAbelianMorphism.ext
    rfl
  nsmul := nsmulRec
  zsmul := zsmulRec

instance bigAbelianCategory : Category BigAbelianObject where
  Hom := BigAbelianMorphism
  id X :=
    { hom := AddMonoidHom.id X.carrier
      commutes := by
        intro β
        simp }
  comp := fun {X Y Z} f g =>
    { hom := g.hom.comp f.hom
      commutes := by
        intro β
        ext x
        change g.hom (f.hom (X.operatorAt β x)) =
          (Z.operatorAt β) (g.hom (f.hom x))
        have hf : f.hom (X.operatorAt β x) =
            (Y.operatorAt β) (f.hom x) := by
          simpa only [AddMonoidHom.comp_apply] using
            congrArg (fun h : X.carrier →+ Y.carrier => h x) (f.commutes β)
        have hg : g.hom ((Y.operatorAt β) (f.hom x)) =
            (Z.operatorAt β) (g.hom (f.hom x)) := by
          simpa only [AddMonoidHom.comp_apply] using
            congrArg (fun h : Y.carrier →+ Z.carrier => h (f.hom x))
              (g.commutes β)
        exact (congrArg g.hom hf).trans hg }
  id_comp := by
    intro X Y f
    apply BigAbelianMorphism.ext
    ext x
    simp
  comp_id := by
    intro X Y f
    apply BigAbelianMorphism.ext
    ext x
    simp
  assoc := by
    intro W X Y Z f g h
    apply BigAbelianMorphism.ext
    ext x
    simp [AddMonoidHom.comp_apply]

@[simp]
theorem bigAbelianCategory_comp_hom {X Y Z : BigAbelianObject}
    (f : X ⟶ Y) (g : Y ⟶ Z) : (f ≫ g).hom = g.hom.comp f.hom :=
  rfl

@[instance_reducible]
def bigAbelianCategoryPreadditive : Preadditive BigAbelianObject where
  homGroup X Y := bigAbelianMorphismAddCommGroup X Y
  add_comp := by
    intro X Y Z f g h
    apply BigAbelianMorphism.ext
    dsimp only [CategoryStruct.comp, bigAbelianCategory]
    ext x
    change h.hom ((f.hom + g.hom) x) =
      h.hom (f.hom x) + h.hom (g.hom x)
    exact h.hom.map_add _ _
  comp_add := by
    intro X Y Z f g h
    apply BigAbelianMorphism.ext
    dsimp only [CategoryStruct.comp, bigAbelianCategory]
    ext x
    change (g.hom + h.hom) (f.hom x) =
      g.hom (f.hom x) + h.hom (f.hom x)
    rfl

attribute [instance] bigAbelianCategoryPreadditive

private theorem bigAbelianMorphism_commutes_apply {X Y : BigAbelianObject}
    (f : X ⟶ Y) (β : Ordinal.{u}) (x : X.carrier) :
    f.hom (X.operatorAt β x) = Y.operatorAt β (f.hom x) := by
  simpa only [AddMonoidHom.comp_apply] using
    congrArg (fun h : X.carrier →+ Y.carrier => h x) (f.commutes β)

private def bigAbelianSubobject (X : BigAbelianObject) (S : AddSubgroup X.carrier)
    (hS : ∀ β : Set.Iio X.index, ∀ x : S, X.operator β x ∈ S) :
    BigAbelianObject where
  carrier := S
  index := X.index
  operator := fun β =>
    { toFun := fun x => ⟨X.operator β x, hS β x⟩
      map_zero' := by simp
      map_add' := by
        intro x y
        ext
        simp }

private def bigAbelianSubobjectInclusion (X : BigAbelianObject)
    (S : AddSubgroup X.carrier)
    (hS : ∀ β : Set.Iio X.index, ∀ x : S, X.operator β x ∈ S) :
    bigAbelianSubobject X S hS ⟶ X :=
  { hom := S.subtype
    commutes := by
      intro β
      apply AddMonoidHom.ext
      intro x
      by_cases hβ : β < X.index
      · dsimp [BigAbelianObject.operatorAt, bigAbelianSubobject]
        simp only [dif_pos hβ]
        rfl
      · dsimp [BigAbelianObject.operatorAt, bigAbelianSubobject]
        simp only [dif_neg hβ]
        rfl }

private def bigAbelianQuotient (X : BigAbelianObject) (S : AddSubgroup X.carrier)
    (hS : ∀ β : Set.Iio X.index,
      S ≤ ((QuotientAddGroup.mk' S).comp (X.operator β)).ker) :
    BigAbelianObject where
  carrier := X.carrier ⧸ S
  addCommGroup := inferInstance
  index := X.index
  operator := fun β =>
    QuotientAddGroup.lift S ((QuotientAddGroup.mk' S).comp (X.operator β)) (hS β)

private def bigAbelianQuotientProjection (X : BigAbelianObject)
    (S : AddSubgroup X.carrier)
    (hS : ∀ β : Set.Iio X.index,
      S ≤ ((QuotientAddGroup.mk' S).comp (X.operator β)).ker) :
    X ⟶ bigAbelianQuotient X S hS :=
  letI : AddCommGroup (X.carrier ⧸ S) :=
    (bigAbelianQuotient X S hS).addCommGroup
  { hom := QuotientAddGroup.mk' S
    commutes := by
      intro β
      apply AddMonoidHom.ext
      intro x
      by_cases hβ : β < X.index
      · rw [BigAbelianObject.operatorAt_of_lt X hβ,
          BigAbelianObject.operatorAt_of_lt (bigAbelianQuotient X S hS) hβ]
        dsimp [bigAbelianQuotient, AddMonoidHom.comp_apply]
        change (QuotientAddGroup.mk' S) (X.operator ⟨β, hβ⟩ x) =
          (QuotientAddGroup.lift S
            ((QuotientAddGroup.mk' S).comp (X.operator ⟨β, hβ⟩))
            (hS ⟨β, hβ⟩)) ((QuotientAddGroup.mk' S) x)
        exact (QuotientAddGroup.lift_mk' S (hS ⟨β, hβ⟩) x).symm
      · simp [BigAbelianObject.operatorAt, bigAbelianQuotient, hβ,
          AddMonoidHom.comp_apply, QuotientAddGroup.lift_mk']
        change 0 = 0
        rfl }

private def bigAbelianKernel {X Y : BigAbelianObject} (f : X ⟶ Y) :
    BigAbelianObject :=
  bigAbelianSubobject X f.hom.ker (fun β x => by
    rw [AddMonoidHom.mem_ker]
    have hf := bigAbelianMorphism_commutes_apply f β.1 x.1
    rw [BigAbelianObject.operatorAt_of_lt X β.2] at hf
    rw [hf]
    have hx : f.hom x.1 = 0 := x.2
    rw [hx]
    exact (Y.operatorAt β).map_zero)

private def bigAbelianKernelInclusion {X Y : BigAbelianObject} (f : X ⟶ Y) :
    bigAbelianKernel f ⟶ X :=
  bigAbelianSubobjectInclusion X f.hom.ker _

private def bigAbelianKernelFork {X Y : BigAbelianObject} (f : X ⟶ Y) :
    KernelFork f :=
  KernelFork.ofι (bigAbelianKernelInclusion f) (by
    apply BigAbelianMorphism.ext
    apply AddMonoidHom.ext
    intro x
    change f.hom x.1 = 0
    exact x.2)

private def bigAbelianCokernel {X Y : BigAbelianObject} (f : X ⟶ Y) :
    BigAbelianObject :=
  bigAbelianQuotient Y f.hom.range (fun β => by
    intro y hy
    rcases hy with ⟨x, rfl⟩
    rw [AddMonoidHom.mem_ker]
    have hf := bigAbelianMorphism_commutes_apply f β.1 x
    rw [BigAbelianObject.operatorAt_of_lt Y β.2] at hf
    change QuotientAddGroup.mk' f.hom.range (Y.operator β (f.hom x)) = 0
    rw [← hf]
    change ((f.hom (X.operatorAt β x) : Y.carrier) :
      Y.carrier ⧸ f.hom.range) = 0
    rw [QuotientAddGroup.eq_zero_iff]
    exact ⟨X.operatorAt β x, rfl⟩)

private def bigAbelianCokernelProjection {X Y : BigAbelianObject} (f : X ⟶ Y) :
    Y ⟶ bigAbelianCokernel f :=
  bigAbelianQuotientProjection Y f.hom.range _

private theorem bigAbelianCokernel_operatorAt_mk {X Y : BigAbelianObject}
    (f : X ⟶ Y) (β : Ordinal.{u}) (y : Y.carrier) :
    (bigAbelianCokernel f).operatorAt β
        (QuotientAddGroup.mk' f.hom.range y) =
      QuotientAddGroup.mk' f.hom.range (Y.operatorAt β y) := by
  have hp := bigAbelianMorphism_commutes_apply
    (bigAbelianCokernelProjection f) β y
  change QuotientAddGroup.mk' f.hom.range (Y.operatorAt β y) =
    (bigAbelianCokernel f).operatorAt β
      (QuotientAddGroup.mk' f.hom.range y) at hp
  exact hp.symm

private def bigAbelianKernelLiftHom {X Y : BigAbelianObject} (f : X ⟶ Y)
    (s : KernelFork f) : s.pt.carrier →+ (bigAbelianKernel f).carrier :=
  by
    letI : AddCommGroup (bigAbelianKernel f).carrier :=
      (bigAbelianKernel f).addCommGroup
    exact s.ι.hom.codRestrict _ (by
      intro x
      rw [AddMonoidHom.mem_ker]
      have hs := congrArg (fun q : s.pt ⟶ Y => q.hom x) s.condition
      change f.hom ((Fork.ι s).hom x) = 0 at hs
      exact hs)

private theorem bigAbelianKernelLiftHom_apply {X Y : BigAbelianObject}
    (f : X ⟶ Y) (s : KernelFork f) (x : s.pt.carrier) :
    (bigAbelianKernelLiftHom f s x).1 =
      s.ι.hom x := by
  rfl

private theorem bigAbelianKernel_operatorAt_val {X Y : BigAbelianObject}
    (f : X ⟶ Y) (β : Ordinal.{u}) (z : (bigAbelianKernel f).carrier) :
    ((bigAbelianKernel f).operatorAt β z).1 =
      X.operatorAt β z.1 := by
  by_cases hβ : β < X.index
  · rw [BigAbelianObject.operatorAt_of_lt (bigAbelianKernel f) hβ,
      BigAbelianObject.operatorAt_of_lt X hβ]
    rfl
  · rw [BigAbelianObject.operatorAt_of_not_lt (bigAbelianKernel f) hβ,
      BigAbelianObject.operatorAt_of_not_lt X hβ]
    rfl

private def bigAbelianKernelLift {X Y : BigAbelianObject} (f : X ⟶ Y)
    (s : KernelFork f) : s.pt ⟶ bigAbelianKernel f :=
  { hom := bigAbelianKernelLiftHom f s
    commutes := by
      intro β
      apply AddMonoidHom.ext
      intro x
      apply Subtype.ext
      have hs := bigAbelianMorphism_commutes_apply s.ι β x
      by_cases hβ : β < X.index
      · simp_rw [AddMonoidHom.comp_apply]
        rw [bigAbelianKernelLiftHom_apply, bigAbelianKernel_operatorAt_val]
        exact hs
      · simp_rw [AddMonoidHom.comp_apply]
        rw [bigAbelianKernelLiftHom_apply, bigAbelianKernel_operatorAt_val]
        exact hs }

private def bigAbelianKernelIsLimit {X Y : BigAbelianObject} (f : X ⟶ Y) :
    IsLimit (bigAbelianKernelFork f) :=
  Fork.IsLimit.mk _
    (fun s => bigAbelianKernelLift f s)
    (fun s => by
      apply BigAbelianMorphism.ext
      apply AddMonoidHom.ext
      intro x
      rfl)
    (fun s m hm => by
      apply BigAbelianMorphism.ext
      apply AddMonoidHom.ext
      intro x
      apply Subtype.ext
      change (bigAbelianKernelInclusion f).hom (m.hom x) = s.ι.hom x
      have hm' := congrArg (fun q : s.pt ⟶ X => q.hom x) hm
      change (bigAbelianKernelFork f).ι.hom (m.hom x) = s.ι.hom x
      exact hm')

private def bigAbelianCokernelLiftHom {X Y : BigAbelianObject} (f : X ⟶ Y)
    (s : CokernelCofork f) : (bigAbelianCokernel f).carrier →+ s.pt.carrier := by
  letI : AddCommGroup (bigAbelianCokernel f).carrier :=
    (bigAbelianCokernel f).addCommGroup
  exact QuotientAddGroup.lift f.hom.range s.π.hom (by
    intro y hy
    rcases hy with ⟨x, rfl⟩
    rw [AddMonoidHom.mem_ker]
    have hs := congrArg (fun q : X ⟶ s.pt => q.hom x) s.condition
    change s.π.hom (f.hom x) = 0 at hs
    exact hs)

private theorem bigAbelianCokernelLiftHom_mk {X Y : BigAbelianObject} (f : X ⟶ Y)
    (s : CokernelCofork f) (y : Y.carrier) :
    bigAbelianCokernelLiftHom f s (QuotientAddGroup.mk' f.hom.range y) =
      s.π.hom y := by
  letI : AddCommGroup (bigAbelianCokernel f).carrier :=
    (bigAbelianCokernel f).addCommGroup
  let hker : f.hom.range ≤ s.π.hom.ker := by
    intro z hz
    rcases hz with ⟨x, rfl⟩
    have hs := congrArg (fun q : X ⟶ s.pt => q.hom x) s.condition
    change s.π.hom (f.hom x) = 0 at hs
    exact hs
  change (QuotientAddGroup.lift f.hom.range s.π.hom hker)
      ((QuotientAddGroup.mk' f.hom.range) y) = s.π.hom y
  exact QuotientAddGroup.lift_mk' f.hom.range hker y

private def bigAbelianCokernelLift {X Y : BigAbelianObject} (f : X ⟶ Y)
    (s : CokernelCofork f) : bigAbelianCokernel f ⟶ s.pt :=
  { hom := bigAbelianCokernelLiftHom f s
    commutes := by
      intro β
      apply AddMonoidHom.ext
      intro q
      obtain ⟨y, rfl⟩ := QuotientAddGroup.mk'_surjective f.hom.range q
      change bigAbelianCokernelLiftHom f s
          ((bigAbelianCokernel f).operatorAt β
            (QuotientAddGroup.mk' f.hom.range y)) =
        s.pt.operatorAt β
          (bigAbelianCokernelLiftHom f s
            (QuotientAddGroup.mk' f.hom.range y))
      rw [bigAbelianCokernel_operatorAt_mk,
        bigAbelianCokernelLiftHom_mk]
      exact bigAbelianMorphism_commutes_apply s.π β y }

private theorem bigAbelianCokernelLift_mk {X Y : BigAbelianObject} (f : X ⟶ Y)
    (s : CokernelCofork f) (y : Y.carrier) :
    (bigAbelianCokernelLift f s).hom
        (QuotientAddGroup.mk' f.hom.range y) = s.π.hom y := by
  exact bigAbelianCokernelLiftHom_mk f s y

private def bigAbelianCokernelIsColimit {X Y : BigAbelianObject} (f : X ⟶ Y) :
    IsColimit (CokernelCofork.ofπ (bigAbelianCokernelProjection f)
      (by
        apply BigAbelianMorphism.ext
        apply AddMonoidHom.ext
        intro x
        change (QuotientAddGroup.mk' f.hom.range) (f.hom x) = 0
        change ((f.hom x : Y.carrier) : Y.carrier ⧸ f.hom.range) = 0
        rw [QuotientAddGroup.eq_zero_iff]
        exact ⟨x, rfl⟩)) :=
  Cofork.IsColimit.mk _
    (fun s => bigAbelianCokernelLift f s)
    (fun s => by
      apply BigAbelianMorphism.ext
      apply AddMonoidHom.ext
      intro x
      change (bigAbelianCokernelLift f s).hom
          (QuotientAddGroup.mk' f.hom.range x) = s.π.hom x
      exact bigAbelianCokernelLift_mk f s x)
    (fun s m hm => by
      apply BigAbelianMorphism.ext
      apply AddMonoidHom.ext
      intro q
      obtain ⟨y, rfl⟩ := QuotientAddGroup.mk'_surjective f.hom.range q
      have hm' := congrArg (fun z : Y ⟶ s.pt => z.hom y) hm
      rw [bigAbelianCokernelLift_mk]
      change m.hom (QuotientAddGroup.mk' f.hom.range y) = s.π.hom y at hm'
      exact hm')

private def bigAbelianBinaryProduct (X Y : BigAbelianObject) : BigAbelianObject where
  carrier := X.carrier × Y.carrier
  index := max X.index Y.index
  operator := fun β =>
    { toFun := fun p => (X.operatorAt β p.1, Y.operatorAt β p.2)
      map_zero' := by simp
      map_add' := by
        intro p q
        ext <;> simp }

private def bigAbelianBinaryProductFst (X Y : BigAbelianObject) :
    bigAbelianBinaryProduct X Y ⟶ X :=
  { hom :=
      { toFun := Prod.fst
        map_zero' := by rfl
        map_add' := by intro p q; rfl }
    commutes := by
      intro β
      apply AddMonoidHom.ext
      intro p
      by_cases hX : β < X.index
      · have hP : β < max X.index Y.index := lt_of_lt_of_le hX (le_max_left _ _)
        change (((bigAbelianBinaryProduct X Y).operatorAt β) p).1 =
          (X.operatorAt β) p.1
        simp [BigAbelianObject.operatorAt, bigAbelianBinaryProduct, hX, hP]
        rfl
      · by_cases hP : β < max X.index Y.index
        · change (((bigAbelianBinaryProduct X Y).operatorAt β) p).1 =
            (X.operatorAt β) p.1
          simp [BigAbelianObject.operatorAt, bigAbelianBinaryProduct, hX, hP]
          rfl
        · change (((bigAbelianBinaryProduct X Y).operatorAt β) p).1 =
            (X.operatorAt β) p.1
          simp [BigAbelianObject.operatorAt, bigAbelianBinaryProduct, hX, hP]
          rfl }

private def bigAbelianBinaryProductSnd (X Y : BigAbelianObject) :
    bigAbelianBinaryProduct X Y ⟶ Y :=
  { hom :=
      { toFun := Prod.snd
        map_zero' := by rfl
        map_add' := by intro p q; rfl }
    commutes := by
      intro β
      apply AddMonoidHom.ext
      intro p
      by_cases hY : β < Y.index
      · have hP : β < max X.index Y.index := lt_of_lt_of_le hY (le_max_right _ _)
        change (((bigAbelianBinaryProduct X Y).operatorAt β) p).2 =
          (Y.operatorAt β) p.2
        simp [BigAbelianObject.operatorAt, bigAbelianBinaryProduct, hY, hP]
        rfl
      · by_cases hP : β < max X.index Y.index
        · change (((bigAbelianBinaryProduct X Y).operatorAt β) p).2 =
            (Y.operatorAt β) p.2
          simp [BigAbelianObject.operatorAt, bigAbelianBinaryProduct, hY, hP]
          rfl
        · change (((bigAbelianBinaryProduct X Y).operatorAt β) p).2 =
            (Y.operatorAt β) p.2
          simp [BigAbelianObject.operatorAt, bigAbelianBinaryProduct, hY, hP]
          rfl }

private def bigAbelianBinaryProductLiftHom {T X Y : BigAbelianObject}
    (f : T ⟶ X) (g : T ⟶ Y) :
    T.carrier →+ (bigAbelianBinaryProduct X Y).carrier :=
  by
    letI : AddCommGroup (bigAbelianBinaryProduct X Y).carrier :=
      (bigAbelianBinaryProduct X Y).addCommGroup
    exact AddMonoidHom.prod f.hom g.hom

private theorem bigAbelianBinaryProductLiftHom_fst {T X Y : BigAbelianObject}
    (f : T ⟶ X) (g : T ⟶ Y) (x : T.carrier) :
    (bigAbelianBinaryProductLiftHom f g x).1 = f.hom x := by
  rfl

private theorem bigAbelianBinaryProductLiftHom_snd {T X Y : BigAbelianObject}
    (f : T ⟶ X) (g : T ⟶ Y) (x : T.carrier) :
    (bigAbelianBinaryProductLiftHom f g x).2 = g.hom x := by
  rfl

private theorem bigAbelianBinaryProduct_operatorAt_fst {X Y : BigAbelianObject}
    (β : Ordinal.{u}) (p : (bigAbelianBinaryProduct X Y).carrier) :
    ((bigAbelianBinaryProduct X Y).operatorAt β p).1 = X.operatorAt β p.1 := by
  by_cases hβ : β < max X.index Y.index
  · rw [BigAbelianObject.operatorAt_of_lt
      (bigAbelianBinaryProduct X Y) hβ]
    rfl
  · have hX : ¬β < X.index := by
      intro h
      exact hβ (lt_of_lt_of_le h (le_max_left _ _))
    rw [BigAbelianObject.operatorAt_of_not_lt
      (bigAbelianBinaryProduct X Y) hβ,
      BigAbelianObject.operatorAt_of_not_lt X hX]
    rfl

private theorem bigAbelianBinaryProduct_operatorAt_snd {X Y : BigAbelianObject}
    (β : Ordinal.{u}) (p : (bigAbelianBinaryProduct X Y).carrier) :
    ((bigAbelianBinaryProduct X Y).operatorAt β p).2 = Y.operatorAt β p.2 := by
  by_cases hβ : β < max X.index Y.index
  · rw [BigAbelianObject.operatorAt_of_lt
      (bigAbelianBinaryProduct X Y) hβ]
    rfl
  · have hY : ¬β < Y.index := by
      intro h
      exact hβ (lt_of_lt_of_le h (le_max_right _ _))
    rw [BigAbelianObject.operatorAt_of_not_lt
      (bigAbelianBinaryProduct X Y) hβ,
      BigAbelianObject.operatorAt_of_not_lt Y hY]
    rfl

private def bigAbelianBinaryProductLift {T X Y : BigAbelianObject}
    (f : T ⟶ X) (g : T ⟶ Y) :
    T ⟶ bigAbelianBinaryProduct X Y :=
  { hom := bigAbelianBinaryProductLiftHom f g
    commutes := by
      intro β
      apply AddMonoidHom.ext
      intro x
      apply Prod.ext
      · have hf := bigAbelianMorphism_commutes_apply f β x
        by_cases hβ : β < max X.index Y.index
        · simp_rw [AddMonoidHom.comp_apply]
          rw [bigAbelianBinaryProductLiftHom_fst,
            bigAbelianBinaryProduct_operatorAt_fst]
          exact hf
        · have hX : ¬β < X.index := by
            intro h
            exact hβ (lt_of_lt_of_le h (le_max_left _ _))
          simp_rw [AddMonoidHom.comp_apply]
          rw [bigAbelianBinaryProductLiftHom_fst,
            bigAbelianBinaryProduct_operatorAt_fst]
          exact hf
      · have hg := bigAbelianMorphism_commutes_apply g β x
        by_cases hβ : β < max X.index Y.index
        · simp_rw [AddMonoidHom.comp_apply]
          rw [bigAbelianBinaryProductLiftHom_snd,
            bigAbelianBinaryProduct_operatorAt_snd]
          exact hg
        · have hY : ¬β < Y.index := by
            intro h
            exact hβ (lt_of_lt_of_le h (le_max_right _ _))
          simp_rw [AddMonoidHom.comp_apply]
          rw [bigAbelianBinaryProductLiftHom_snd,
            bigAbelianBinaryProduct_operatorAt_snd]
          exact hg }

private def bigAbelianBinaryProductFan (X Y : BigAbelianObject) : BinaryFan X Y :=
  BinaryFan.mk (bigAbelianBinaryProductFst X Y) (bigAbelianBinaryProductSnd X Y)

private def bigAbelianBinaryProductIsLimit (X Y : BigAbelianObject) :
    IsLimit (bigAbelianBinaryProductFan X Y) :=
  BinaryFan.IsLimit.mk _
    (fun f g => bigAbelianBinaryProductLift f g)
    (fun f g => by
      apply BigAbelianMorphism.ext
      apply AddMonoidHom.ext
      intro x
      rfl)
    (fun f g => by
      apply BigAbelianMorphism.ext
      apply AddMonoidHom.ext
      intro x
      rfl)
    (fun f g m hm₁ hm₂ => by
      apply BigAbelianMorphism.ext
      apply AddMonoidHom.ext
      intro x
      have h₁ := congrArg (fun q : _ ⟶ X => q.hom x) hm₁
      have h₂ := congrArg (fun q : _ ⟶ Y => q.hom x) hm₂
      exact Prod.ext h₁ h₂)

private instance bigAbelianHasLimitPair (X Y : BigAbelianObject) :
    HasLimit (pair X Y) :=
  ⟨bigAbelianBinaryProductFan X Y, bigAbelianBinaryProductIsLimit X Y⟩

private instance bigAbelianHasBinaryProducts : HasBinaryProducts BigAbelianObject :=
  hasBinaryProducts_of_hasLimit_pair (C := BigAbelianObject)

private def bigAbelianCategoryZeroObject : BigAbelianObject where
  carrier := PUnit
  addCommGroup := inferInstance
  index := 0
  operator := fun _ => 0

private def bigAbelianCategoryZeroIsZero : IsZero bigAbelianCategoryZeroObject where
  unique_to Y := ⟨{
    default := 0
    uniq := by
      intro f
      apply BigAbelianMorphism.ext
      apply AddMonoidHom.ext
      intro x
      cases x
      change f.hom 0 = 0
      exact f.hom.map_zero }⟩
  unique_from Y := ⟨{
    default := 0
    uniq := by
      intro f
      apply BigAbelianMorphism.ext
      apply AddMonoidHom.ext
      intro x
      cases f.hom x
      rfl }⟩

private instance bigAbelianHasTerminal : HasTerminal BigAbelianObject :=
  bigAbelianCategoryZeroIsZero.isTerminal.hasTerminal

private theorem bigAbelianCokernel_condition {X Y : BigAbelianObject}
    (f : X ⟶ Y) : f ≫ bigAbelianCokernelProjection f = 0 := by
  apply BigAbelianMorphism.ext
  apply AddMonoidHom.ext
  intro x
  change QuotientAddGroup.mk' f.hom.range (f.hom x) = 0
  change ((f.hom x : Y.carrier) : Y.carrier ⧸ f.hom.range) = 0
  exact (QuotientAddGroup.eq_zero_iff (f.hom x)).2 ⟨x, rfl⟩

private theorem bigAbelianMono_injective {X Y : BigAbelianObject} (f : X ⟶ Y)
    [Mono f] : Function.Injective f.hom := by
  have hι : bigAbelianKernelInclusion f = 0 := by
    apply (cancel_mono f).1
    rw [zero_comp]
    exact (bigAbelianKernelFork f).condition
  intro x y hxy
  have hsub : f.hom (x - y) = 0 := by
    rw [map_sub, hxy, sub_self]
  let z : (bigAbelianKernel f).carrier := ⟨x - y, hsub⟩
  have hz := congrArg (fun q : bigAbelianKernel f ⟶ X => q.hom z) hι
  have hz' : x - y = 0 := by
    dsimp [z, bigAbelianKernelInclusion, bigAbelianSubobjectInclusion] at hz
    exact hz
  exact sub_eq_zero.mp hz'

private theorem bigAbelianEpi_surjective {X Y : BigAbelianObject} (f : X ⟶ Y)
    [Epi f] : Function.Surjective f.hom := by
  have hq : bigAbelianCokernelProjection f = 0 := by
    apply (cancel_epi f).1
    rw [bigAbelianCokernel_condition]
    simp
  intro y
  have hy := congrArg (fun q : Y ⟶ bigAbelianCokernel f => q.hom y) hq
  change QuotientAddGroup.mk' f.hom.range y = 0 at hy
  change ((y : Y.carrier) : Y.carrier ⧸ f.hom.range) = 0 at hy
  exact (QuotientAddGroup.eq_zero_iff y).1 hy

private noncomputable def bigAbelianMonoRangeEquiv {X Y : BigAbelianObject}
    (f : X ⟶ Y) [Mono f] : X.carrier ≃+ f.hom.range :=
  AddMonoidHom.ofInjective (bigAbelianMono_injective f)

private noncomputable def bigAbelianNormalMonoRangeFactor
    {X Y : BigAbelianObject} (f : X ⟶ Y) [Mono f]
    (s : KernelFork (bigAbelianCokernelProjection f)) :
    s.pt.carrier →+ f.hom.range :=
  s.ι.hom.codRestrict _ (fun x => by
    have hs := congrArg (fun q : s.pt ⟶ bigAbelianCokernel f => q.hom x)
      s.condition
    change ((s.ι.hom x : Y.carrier) : Y.carrier ⧸ f.hom.range) = 0 at hs
    apply (QuotientAddGroup.eq_zero_iff (s.ι.hom x)).1
    exact hs)

private noncomputable def bigAbelianNormalMonoLiftHom
    {X Y : BigAbelianObject} (f : X ⟶ Y) [Mono f]
    (s : KernelFork (bigAbelianCokernelProjection f)) :
    s.pt.carrier →+ X.carrier :=
  (bigAbelianMonoRangeEquiv f).symm.toAddMonoidHom.comp
    (bigAbelianNormalMonoRangeFactor f s)

private theorem bigAbelianNormalMonoLiftHom_fac
    {X Y : BigAbelianObject} (f : X ⟶ Y) [Mono f]
    (s : KernelFork (bigAbelianCokernelProjection f)) :
    f.hom.comp (bigAbelianNormalMonoLiftHom f s) = s.ι.hom := by
  apply AddMonoidHom.ext
  intro x
  have he := congrArg Subtype.val
    ((bigAbelianMonoRangeEquiv f).apply_symm_apply
      (bigAbelianNormalMonoRangeFactor f s x))
  simpa [bigAbelianMonoRangeEquiv, bigAbelianNormalMonoRangeFactor,
    bigAbelianNormalMonoLiftHom, AddMonoidHom.comp_apply] using he

private noncomputable def bigAbelianNormalMonoLift
    {X Y : BigAbelianObject} (f : X ⟶ Y) [Mono f]
    (s : KernelFork (bigAbelianCokernelProjection f)) : s.pt ⟶ X :=
  { hom := bigAbelianNormalMonoLiftHom f s
    commutes := by
      intro β
      apply AddMonoidHom.ext
      intro x
      apply bigAbelianMono_injective f
      have hs := bigAbelianMorphism_commutes_apply s.ι β x
      have hlx := congrArg
        (fun q : s.pt.carrier →+ Y.carrier => q x)
        (bigAbelianNormalMonoLiftHom_fac f s)
      have hlt := congrArg
        (fun q : s.pt.carrier →+ Y.carrier => q (s.pt.operatorAt β x))
        (bigAbelianNormalMonoLiftHom_fac f s)
      have hlx' : f.hom (bigAbelianNormalMonoLiftHom f s x) = s.ι.hom x := by
        simpa only [AddMonoidHom.comp_apply] using hlx
      calc
        f.hom (bigAbelianNormalMonoLiftHom f s (s.pt.operatorAt β x)) =
            s.ι.hom (s.pt.operatorAt β x) := hlt
        _ = Y.operatorAt β (s.ι.hom x) := hs
        _ = Y.operatorAt β (f.hom (bigAbelianNormalMonoLiftHom f s x)) := by
          rw [hlx']
        _ = f.hom (X.operatorAt β (bigAbelianNormalMonoLiftHom f s x)) :=
          (bigAbelianMorphism_commutes_apply f β
            (bigAbelianNormalMonoLiftHom f s x)).symm }

private def bigAbelianNormalMono {X Y : BigAbelianObject} (f : X ⟶ Y)
    [Mono f] : NormalMono f where
  Z := bigAbelianCokernel f
  g := bigAbelianCokernelProjection f
  w := bigAbelianCokernel_condition f
  isLimit := by
    refine Fork.IsLimit.mk _ (fun s => bigAbelianNormalMonoLift f s)
      (fun s => ?_) (fun s m hm => ?_)
    · apply BigAbelianMorphism.ext
      apply AddMonoidHom.ext
      intro x
      exact congrArg (fun q : s.pt.carrier →+ Y.carrier => q x)
        (bigAbelianNormalMonoLiftHom_fac f s)
    · apply BigAbelianMorphism.ext
      apply AddMonoidHom.ext
      intro x
      apply bigAbelianMono_injective f
      have hm' := congrArg (fun q : s.pt ⟶ Y => q.hom x) hm
      have hl' := congrArg (fun q : s.pt.carrier →+ Y.carrier => q x)
        (bigAbelianNormalMonoLiftHom_fac f s)
      have hm'' : f.hom (m.hom x) = s.ι.hom x := by
        simpa [bigAbelianCategory_comp_hom] using hm'
      have hl'' : f.hom ((bigAbelianNormalMonoLift f s).hom x) = s.ι.hom x := by
        simpa [bigAbelianNormalMonoLift] using hl'
      exact hm''.trans hl''.symm

private noncomputable def bigAbelianNormalEpiLiftHom
    {X Y : BigAbelianObject} (f : X ⟶ Y) [Epi f]
    (s : CokernelCofork (bigAbelianKernelInclusion f)) :
    Y.carrier →+ s.pt.carrier :=
  (AddMonoidHom.liftOfSurjective f.hom (bigAbelianEpi_surjective f)) ⟨s.π.hom, by
    intro x hx
    let z : (bigAbelianKernel f).carrier := ⟨x, hx⟩
    have hs := congrArg (fun q : bigAbelianKernel f ⟶ s.pt => q.hom z) s.condition
    change s.π.hom x = 0 at hs
    exact hs⟩

private theorem bigAbelianNormalEpiLiftHom_fac
    {X Y : BigAbelianObject} (f : X ⟶ Y) [Epi f]
    (s : CokernelCofork (bigAbelianKernelInclusion f)) :
    (bigAbelianNormalEpiLiftHom f s).comp f.hom = s.π.hom := by
  ext x
  simp [bigAbelianNormalEpiLiftHom]

private noncomputable def bigAbelianNormalEpiLift
    {X Y : BigAbelianObject} (f : X ⟶ Y) [Epi f]
    (s : CokernelCofork (bigAbelianKernelInclusion f)) : Y ⟶ s.pt :=
  { hom := bigAbelianNormalEpiLiftHom f s
    commutes := by
      intro β
      apply AddMonoidHom.ext
      intro y
      obtain ⟨x, rfl⟩ := bigAbelianEpi_surjective f y
      have hf := bigAbelianMorphism_commutes_apply f β x
      have hs := bigAbelianMorphism_commutes_apply s.π β x
      have hlt := congrArg
        (fun q : X.carrier →+ s.pt.carrier => q (X.operatorAt β x))
        (bigAbelianNormalEpiLiftHom_fac f s)
      have hlx := congrArg
        (fun q : X.carrier →+ s.pt.carrier => q x)
        (bigAbelianNormalEpiLiftHom_fac f s)
      have hlx' : bigAbelianNormalEpiLiftHom f s (f.hom x) = s.π.hom x := by
        simpa only [AddMonoidHom.comp_apply] using hlx
      calc
        bigAbelianNormalEpiLiftHom f s (Y.operatorAt β (f.hom x)) =
            bigAbelianNormalEpiLiftHom f s (f.hom (X.operatorAt β x)) := by
              rw [hf]
        _ = s.π.hom (X.operatorAt β x) := hlt
        _ = s.pt.operatorAt β (s.π.hom x) := hs
        _ = s.pt.operatorAt β
            (bigAbelianNormalEpiLiftHom f s (f.hom x)) := by rw [hlx'] }

private def bigAbelianNormalEpi {X Y : BigAbelianObject} (f : X ⟶ Y)
    [Epi f] : NormalEpi f where
  W := bigAbelianKernel f
  g := bigAbelianKernelInclusion f
  w := (bigAbelianKernelFork f).condition
  isColimit := by
    refine Cofork.IsColimit.mk _ (fun s => bigAbelianNormalEpiLift f s)
      (fun s => ?_) (fun s m hm => ?_)
    · apply BigAbelianMorphism.ext
      apply AddMonoidHom.ext
      intro x
      exact congrArg (fun q : X.carrier →+ s.pt.carrier => q x)
        (bigAbelianNormalEpiLiftHom_fac f s)
    · apply BigAbelianMorphism.ext
      apply AddMonoidHom.ext
      intro y
      obtain ⟨x, rfl⟩ := bigAbelianEpi_surjective f y
      have hm' := congrArg (fun q : X ⟶ s.pt => q.hom x) hm
      have hl' := congrArg (fun q : X.carrier →+ s.pt.carrier => q x)
        (bigAbelianNormalEpiLiftHom_fac f s)
      simpa [bigAbelianCategory_comp_hom, bigAbelianNormalEpiLift] using
        hm'.trans hl'.symm

/- The source says that the routine verification that this category is
abelian is omitted.  This is the exact category-level interface used below;
its proof is intentionally deferred to the proof stage. -/
@[instance_reducible]
instance bigAbelianCategory_abelian : Abelian BigAbelianObject where
  toPreadditive := bigAbelianCategoryPreadditive
  has_finite_products := by
    exact hasFiniteProducts_of_has_binary_and_terminal
  has_kernels := by
    exact ⟨fun f => ⟨bigAbelianKernelFork f, bigAbelianKernelIsLimit f⟩⟩
  has_cokernels := by
    exact ⟨fun f => ⟨CokernelCofork.ofπ (bigAbelianCokernelProjection f)
      (bigAbelianCokernel_condition f), bigAbelianCokernelIsColimit f⟩⟩
  normalMonoOfMono := by
    intro X Y f inst
    exact ⟨bigAbelianNormalMono f⟩
  normalEpiOfEpi := by
    intro X Y f inst
    exact ⟨bigAbelianNormalEpi f⟩

/-! ## The zero-operator object and the ordinal-indexed extensions -/

/-- The object `Z = (ℤ, ∅, 0)` from the source. -/
abbrev bigAbelianZeroObject : BigAbelianObject where
  carrier := ℤ
  index := 0
  operator := fun _ => 0

@[simp]
theorem bigAbelianZeroObject_operatorAt (β : Ordinal.{u}) :
    bigAbelianZeroObject.operatorAt β = 0 := by
  simp [BigAbelianObject.operatorAt, bigAbelianZeroObject]

/-- The endomorphism represented by the matrix
`((0, 1), (0, 0))` on `ℤ ⊕ ℤ`. -/
def bigAbelianNilpotentOperator : (ℤ × ℤ) →+ (ℤ × ℤ) where
  toFun := fun p => (p.2, 0)
  map_zero' := by simp
  map_add' := by
    intro p q
    simp

/-- The middle object used for the extension indexed by `α`. -/
abbrev bigAbelianOrdinalMiddle (α : Ordinal.{u}) : BigAbelianObject where
  carrier := ℤ × ℤ
  index := α + 1
  operator := fun β =>
    if β.1 = α then bigAbelianNilpotentOperator else 0

theorem bigAbelianOrdinalMiddle_operatorAt_eq_nilpotent
    (α : Ordinal.{u}) :
    (bigAbelianOrdinalMiddle α).operatorAt α =
      bigAbelianNilpotentOperator := by
  have hα : α < α + 1 := by
    simpa only [Order.succ_eq_add_one] using (Order.lt_succ α)
  simp [BigAbelianObject.operatorAt, bigAbelianOrdinalMiddle, hα]

theorem bigAbelianOrdinalMiddle_operatorAt_eq_zero_of_ne
    (α β : Ordinal.{u}) (hβ : β ≠ α) :
    (bigAbelianOrdinalMiddle α).operatorAt β = 0 := by
  by_cases hlt : β < α + 1
  · simp [BigAbelianObject.operatorAt, bigAbelianOrdinalMiddle, hlt, hβ]
  · simp [BigAbelianObject.operatorAt, bigAbelianOrdinalMiddle, hlt]

/-- The inclusion of the first copy of `ℤ` into the middle group. -/
def bigAbelianOrdinalInclusion (α : Ordinal.{u}) :
    bigAbelianZeroObject ⟶ bigAbelianOrdinalMiddle α where
  hom :=
    { toFun := fun (n : ℤ) => (n, 0)
      map_zero' := by simp
      map_add' := by
        intro m n
        simp }
  commutes := by
    intro β
    apply AddMonoidHom.ext
    intro n
    by_cases hβ : β < α + 1
    · by_cases hβα : β = α
      · subst β
        rw [bigAbelianZeroObject_operatorAt,
          bigAbelianOrdinalMiddle_operatorAt_eq_nilpotent]
        simp [AddMonoidHom.comp_apply, bigAbelianNilpotentOperator]
        rfl
      · rw [bigAbelianZeroObject_operatorAt,
          bigAbelianOrdinalMiddle_operatorAt_eq_zero_of_ne α β hβα]
        simp
    · rw [bigAbelianZeroObject_operatorAt,
        BigAbelianObject.operatorAt_of_not_lt (bigAbelianOrdinalMiddle α) hβ]
      simp

/-- The projection of the middle group onto the second copy of `ℤ`. -/
def bigAbelianOrdinalProjection (α : Ordinal.{u}) :
    bigAbelianOrdinalMiddle α ⟶ bigAbelianZeroObject where
  hom :=
    { toFun := fun (p : ℤ × ℤ) => p.2
      map_zero' := by simp
      map_add' := by
        intro p q
        simp }
  commutes := by
    intro β
    apply AddMonoidHom.ext
    intro p
    by_cases hβ : β < α + 1
    · by_cases hβα : β = α
      · subst β
        rw [bigAbelianOrdinalMiddle_operatorAt_eq_nilpotent,
          bigAbelianZeroObject_operatorAt]
        simp [AddMonoidHom.comp_apply, bigAbelianNilpotentOperator]
      · rw [bigAbelianOrdinalMiddle_operatorAt_eq_zero_of_ne α β hβα,
          bigAbelianZeroObject_operatorAt]
        simp
    · rw [BigAbelianObject.operatorAt_of_not_lt (bigAbelianOrdinalMiddle α) hβ,
        bigAbelianZeroObject_operatorAt]
      simp

theorem bigAbelianOrdinalExtension_zero (α : Ordinal.{u}) :
    bigAbelianOrdinalInclusion α ≫ bigAbelianOrdinalProjection α = 0 := by
  apply BigAbelianMorphism.ext
  dsimp only [CategoryStruct.comp, bigAbelianCategory]
  apply AddMonoidHom.ext
  intro n
  simp [bigAbelianOrdinalInclusion, bigAbelianOrdinalProjection]

private def bigAbelianOrdinalKernelLiftHom (α : Ordinal.{u})
    (s : KernelFork (bigAbelianOrdinalProjection α)) :
    s.pt.carrier →+ bigAbelianZeroObject.{u}.carrier :=
  { toFun := fun x => (s.ι.hom x).1
    map_zero' := by simp
    map_add' := by
      intro x y
      simp }

private theorem bigAbelianOrdinalKernelLiftHom_commutes (α : Ordinal.{u})
    (s : KernelFork (bigAbelianOrdinalProjection α)) (β : Ordinal.{u})
    (x : s.pt.carrier) :
    bigAbelianOrdinalKernelLiftHom α s (s.pt.operatorAt β x) =
      bigAbelianZeroObject.{u}.operatorAt β
        (bigAbelianOrdinalKernelLiftHom α s x) := by
  rw [bigAbelianZeroObject_operatorAt]
  change (s.ι.hom (s.pt.operatorAt β x)).1 = 0
  have hs := congrArg Prod.fst (bigAbelianMorphism_commutes_apply s.ι β x)
  have hc := congrArg (fun q : s.pt ⟶ bigAbelianZeroObject => q.hom x) s.condition
  change (s.ι.hom x).2 = 0 at hc
  by_cases hβα : β = α
  · subst β
    rw [bigAbelianOrdinalMiddle_operatorAt_eq_nilpotent,
      bigAbelianNilpotentOperator] at hs
    exact hs.trans hc
  · rw [bigAbelianOrdinalMiddle_operatorAt_eq_zero_of_ne α β hβα] at hs
    exact hs

private def bigAbelianOrdinalKernelLift (α : Ordinal.{u})
    (s : KernelFork (bigAbelianOrdinalProjection α)) :
    s.pt ⟶ bigAbelianZeroObject.{u} :=
  { hom := bigAbelianOrdinalKernelLiftHom α s
    commutes := by
      intro β
      apply AddMonoidHom.ext
      intro x
      exact bigAbelianOrdinalKernelLiftHom_commutes α s β x }

private def bigAbelianOrdinalKernelIsLimit (α : Ordinal.{u}) :
    IsLimit (KernelFork.ofι (bigAbelianOrdinalInclusion α)
      (bigAbelianOrdinalExtension_zero α)) :=
  Fork.IsLimit.mk _
    (fun s => bigAbelianOrdinalKernelLift α s)
    (fun s => by
      apply BigAbelianMorphism.ext
      apply AddMonoidHom.ext
      intro x
      have hc := congrArg (fun q : s.pt ⟶ bigAbelianZeroObject => q.hom x) s.condition
      change (s.ι.hom x).2 = 0 at hc
      change ((s.ι.hom x).1, 0) = s.ι.hom x
      exact Prod.ext rfl hc.symm)
    (fun s m hm => by
      apply BigAbelianMorphism.ext
      apply AddMonoidHom.ext
      intro x
      have hm' := congrArg (fun q : s.pt ⟶ bigAbelianOrdinalMiddle α => q.hom x) hm
      change (m.hom x, 0) = s.ι.hom x at hm'
      exact congrArg Prod.fst hm')

private theorem bigAbelianOrdinalInclusion_mono (α : Ordinal.{u}) :
    Mono (bigAbelianOrdinalInclusion α) := by
  constructor
  intro Z g h w
  apply BigAbelianMorphism.ext
  apply AddMonoidHom.ext
  intro x
  have hx := congrArg (fun q : Z ⟶ bigAbelianOrdinalMiddle α => q.hom x) w
  change (g.hom x, 0) = (h.hom x, 0) at hx
  exact congrArg Prod.fst hx

private theorem bigAbelianOrdinalProjection_epi (α : Ordinal.{u}) :
    Epi (bigAbelianOrdinalProjection α) := by
  constructor
  intro Z g h w
  apply BigAbelianMorphism.ext
  apply AddMonoidHom.ext
  intro y
  have hy := congrArg
    (fun q : bigAbelianOrdinalMiddle α ⟶ Z => q.hom (0, y)) w
  change g.hom y = h.hom y at hy
  exact hy

theorem bigAbelianOrdinalExtension_shortExact (α : Ordinal.{u}) :
    (ShortComplex.mk (bigAbelianOrdinalInclusion α)
      (bigAbelianOrdinalProjection α) (bigAbelianOrdinalExtension_zero α)).ShortExact := by
  refine ShortComplex.ShortExact.mk' ?_
    (bigAbelianOrdinalInclusion_mono α) (bigAbelianOrdinalProjection_epi α)
  exact ShortComplex.exact_of_f_is_kernel
    (ShortComplex.mk (bigAbelianOrdinalInclusion α)
      (bigAbelianOrdinalProjection α) (bigAbelianOrdinalExtension_zero α))
    (bigAbelianOrdinalKernelIsLimit α)

/-- The short-exact extension of `Z` by `Z` whose only nonzero operator is at
`α`. -/
def bigAbelianOrdinalExtension (α : Ordinal.{u}) :
    Formalization.Books.Homology.Unit06.Extension
      BigAbelianObject bigAbelianZeroObject bigAbelianZeroObject where
  middle := bigAbelianOrdinalMiddle α
  inclusion := bigAbelianOrdinalInclusion α
  projection := bigAbelianOrdinalProjection α
  zero := bigAbelianOrdinalExtension_zero α
  shortExact := bigAbelianOrdinalExtension_shortExact α

/-- The corresponding isomorphism class in the canonical `Ext` quotient. -/
def bigAbelianOrdinalExtensionClass (α : Ordinal.{u}) :
    Formalization.Books.Homology.Unit06.Ext
      bigAbelianZeroObject bigAbelianZeroObject :=
  Formalization.Books.Homology.Unit06.extensionClass
    (bigAbelianOrdinalExtension α)

/-- Different ordinals give different extension classes. -/
theorem bigAbelianOrdinalExtensionClass_injective :
    Function.Injective bigAbelianOrdinalExtensionClass := by
  sorry

/-! ## The proper-class conclusion -/

/-- A fixed-universe formulation of the source's “proper class” conclusion.

Mathlib's `Small` predicate is the canonical statement that a type can be
represented in a lower universe, so its negation is used here rather than a
parallel equivalence predicate. -/
def IsUniverseLarge (X : Type (u + 1)) : Prop :=
  ¬ Small.{u} X

theorem isUniverseLarge_of_injective_ordinal
    {X : Type (u + 1)} (f : Ordinal.{u} → X)
    (hf : Function.Injective f) : IsUniverseLarge X := by
  intro hX
  rcases hX.equiv_small with ⟨Y, ⟨e⟩⟩
  exact (not_injective_of_ordinal.{u, u} (e ∘ f)) (by
    intro α β hαβ
    apply hf
    exact e.injective hαβ)

/-- The extension classes of `Z` by `Z` are not a set at the small universe. -/
theorem bigAbelianExt_is_universe_large :
    IsUniverseLarge
      (Formalization.Books.Homology.Unit06.Ext
        bigAbelianZeroObject.{u} bigAbelianZeroObject.{u}) :=
  isUniverseLarge_of_injective_ordinal
    (X := Formalization.Books.Homology.Unit06.Ext
      bigAbelianZeroObject.{u} bigAbelianZeroObject.{u})
    bigAbelianOrdinalExtensionClass bigAbelianOrdinalExtensionClass_injective

/-- In any derived-category model identifying the degree-one morphism
collection with the Yoneda `Ext` collection, the derived morphisms are
universe-large as well. -/
theorem bigAbelianDerivedHom_is_universe_large
    (H : Type (u + 1))
    (hH : Nonempty (H ≃
    Formalization.Books.Homology.Unit06.Ext
        bigAbelianZeroObject.{u} bigAbelianZeroObject.{u})) :
    IsUniverseLarge H := by
  rcases hH with ⟨eH⟩
  intro hHsmall
  rcases hHsmall.equiv_small with ⟨Y, ⟨eY⟩⟩
  exact bigAbelianExt_is_universe_large (Small.mk' (eH.symm.trans eY))

/-- The chapter's final existence statement. -/
theorem exists_big_abelian_category_with_proper_class_ext :
    ∃ (C : Type (u + 1)) (_ : Category.{0} C) (_ : Abelian C)
      (M N : C),
      IsUniverseLarge
        (Formalization.Books.Homology.Unit06.Ext M N) := by
  exact ⟨BigAbelianObject, inferInstance, inferInstance,
    bigAbelianZeroObject, bigAbelianZeroObject,
    bigAbelianExt_is_universe_large⟩

end

end Formalization.Books.Examples.Unit63
