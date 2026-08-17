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

/- The source says that the routine verification that this category is
abelian is omitted.  This is the exact category-level interface used below;
its proof is intentionally deferred to the proof stage. -/
@[instance_reducible]
instance bigAbelianCategory_abelian : Abelian BigAbelianObject where
  toPreadditive := bigAbelianCategoryPreadditive
  has_finite_products := by
    sorry
  has_kernels := by
    sorry
  has_cokernels := by
    sorry
  normalMonoOfMono := by
    sorry
  normalEpiOfEpi := by
    sorry

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

theorem bigAbelianOrdinalExtension_shortExact (α : Ordinal.{u}) :
    (ShortComplex.mk (bigAbelianOrdinalInclusion α)
      (bigAbelianOrdinalProjection α) (bigAbelianOrdinalExtension_zero α)).ShortExact := by
  sorry

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
