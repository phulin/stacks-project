import Formalization.Books.Categories.Unit20.CofilteredLimits
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.CategoryTheory.Filtered.Basic
import Mathlib.CategoryTheory.Limits.Final
import Mathlib.CategoryTheory.Presentable.Directed
import Mathlib.CategoryTheory.Limits.Shapes.Preorder.Basic
import Mathlib.CategoryTheory.Limits.Types.Images
import Mathlib.CategoryTheory.SingleObj
import Mathlib.Order.Antisymmetrization
import Mathlib.Data.Fintype.Order
import Mathlib.CategoryTheory.Whiskering

/-!
# Categories, Chapter 21: Limits and colimits over preordered sets

The book uses the usual order-theoretic terminology for thin categories.  This
file uses Mathlib's canonical `Preorder`, `PartialOrder`, and `IsDirectedOrder`
interfaces, and records the source's additional nonempty condition in
`IsDirectedSet`.  A system is already exactly a functor from the associated
preorder category, so no parallel structure is introduced for its transition
maps.
-/

namespace Formalization.Books.Categories.Unit21

open CategoryTheory
open CategoryTheory.Limits

universe u v u' v' w w'

noncomputable section

/-! ## 21. Limits and colimits over preordered sets -/

/- A directed set in the source is a nonempty preorder in which every pair has
   a common upper bound.  Mathlib's `IsDirectedOrder` supplies the latter
   property, but intentionally does not encode nonemptiness. -/
def IsDirectedSet (I : Type u) [Preorder I] : Prop :=
  Nonempty I ∧ IsDirectedOrder I

/- The category associated to a preorder is Mathlib's `Preorder.smallCategory`.
   Conversely, a thin category carries the preorder given by existence of a
   morphism. -/
@[instance_reducible] def preorderOfThinCategory (C : Type u) [Category C]
    [Quiver.IsThin C] : Preorder C where
  le X Y := Nonempty (X ⟶ Y)
  le_refl X := ⟨𝟙 X⟩
  le_trans X Y Z hXY hYZ := ⟨hXY.some ≫ hYZ.some⟩

theorem preorderOfThinCategory_le_iff
    (C : Type u) [Category C] [Quiver.IsThin C] (X Y : C) :
    letI : Preorder C := preorderOfThinCategory C
    X ≤ Y ↔ Nonempty (X ⟶ Y) := by
  rfl

/- A system and an inverse system are precisely diagrams over the preorder and
   its opposite.  Functoriality supplies the identity and composition laws for
   the transition maps in the source. -/
abbrev System (I : Type u) [Preorder I] (C : Type v) [Category.{w} C] := I ⥤ C

abbrev InverseSystem (I : Type u) [Preorder I] (C : Type v) [Category.{w} C] := Iᵒᵖ ⥤ C

abbrev SystemColimit {I : Type u} [Preorder I]
    {C : Type v} [Category.{w} C] (M : System I C) [HasColimit M] : C :=
  colimit M

abbrev InverseSystemLimit {I : Type u} [Preorder I]
    {C : Type v} [Category.{w} C] (M : InverseSystem I C) [HasLimit M] : C :=
  limit M

abbrev IsDirectedSystem {I : Type u} [Preorder I]
    {C : Type v} [Category.{w} C] (_M : System I C) : Prop :=
  IsDirectedSet I

abbrev IsDirectedInverseSystem {I : Type u} [Preorder I]
    {C : Type v} [Category.{w} C] (_M : InverseSystem I C) : Prop :=
  IsDirectedSet I

/-! ### Passing from a preorder to its antisymmetrization -/

abbrev PreorderQuotient (I : Type u) [Preorder I] :=
  Antisymmetrization I (· ≤ ·)

def preorderQuotientProjection (I : Type u) [Preorder I] :
    I ⥤ PreorderQuotient I :=
  (toAntisymmetrization_mono (α := I)).functor

theorem preorderQuotient_is_directed
    (I : Type u) [Preorder I] (hI : IsDirectedSet I) :
    IsDirectedSet (PreorderQuotient I) := by
  sorry

theorem preorderQuotientProjection_is_final
    (I : Type u) [Preorder I] :
    Functor.Final (preorderQuotientProjection I) := by
  sorry

theorem preorderQuotientProjection_op_is_initial
    (I : Type u) [Preorder I] :
    Functor.Initial (preorderQuotientProjection I).op := by
  let _ : Functor.Final (preorderQuotientProjection I) :=
    preorderQuotientProjection_is_final I
  infer_instance

abbrev pullbackSystem {I : Type u} [Preorder I]
    {C : Type v} [Category.{w} C]
    (N : System (PreorderQuotient I) C) : System I C :=
  preorderQuotientProjection I ⋙ N

abbrev pullbackInverseSystem {I : Type u} [Preorder I]
    {C : Type v} [Category.{w} C]
    (N : InverseSystem (PreorderQuotient I) C) : InverseSystem I C :=
  (preorderQuotientProjection I).op ⋙ N

theorem hasColimit_pullbackSystem_iff
    {I : Type u} [Preorder I] {C : Type v} [Category.{w} C]
    (N : System (PreorderQuotient I) C) :
    HasColimit N ↔ HasColimit (pullbackSystem N) := by
  let _ : Functor.Final (preorderQuotientProjection I) :=
    preorderQuotientProjection_is_final I
  exact (Functor.Final.hasColimit_comp_iff
    (F := preorderQuotientProjection I) (G := N)).symm

theorem hasColimit_pullbackSystem_of_hasColimit
    {I : Type u} [Preorder I] {C : Type v} [Category.{w} C]
    (N : System (PreorderQuotient I) C) [HasColimit N] :
    HasColimit (pullbackSystem N) := by
  let _ : Functor.Final (preorderQuotientProjection I) :=
    preorderQuotientProjection_is_final I
  infer_instance

theorem hasColimit_of_pullbackSystem
    {I : Type u} [Preorder I] {C : Type v} [Category.{w} C]
    (N : System (PreorderQuotient I) C) [HasColimit (pullbackSystem N)] :
    HasColimit N := by
  let _ : Functor.Final (preorderQuotientProjection I) :=
    preorderQuotientProjection_is_final I
  exact Functor.Final.hasColimit_of_comp (preorderQuotientProjection I)

noncomputable def colimitIso_pullbackSystem
    {I : Type u} [Preorder I] {C : Type v} [Category.{w} C]
    (N : System (PreorderQuotient I) C) [HasColimit N]
    [HasColimit (pullbackSystem N)] :
    colimit (pullbackSystem N) ≅ colimit N := by
  letI : Functor.Final (preorderQuotientProjection I) :=
    preorderQuotientProjection_is_final I
  exact Functor.Final.colimitIso (preorderQuotientProjection I) N

theorem hasLimit_pullbackInverseSystem_iff
    {I : Type u} [Preorder I] {C : Type v} [Category.{w} C]
    (N : InverseSystem (PreorderQuotient I) C) :
    HasLimit N ↔ HasLimit (pullbackInverseSystem N) := by
  let _ : Functor.Initial (preorderQuotientProjection I).op :=
    preorderQuotientProjection_op_is_initial I
  exact (Functor.Initial.hasLimit_comp_iff
    (F := (preorderQuotientProjection I).op) (G := N)).symm

theorem hasLimit_pullbackInverseSystem_of_hasLimit
    {I : Type u} [Preorder I] {C : Type v} [Category.{w} C]
    (N : InverseSystem (PreorderQuotient I) C)
    [HasLimit N] : HasLimit (pullbackInverseSystem N) := by
  let _ : Functor.Initial (preorderQuotientProjection I).op :=
    preorderQuotientProjection_op_is_initial I
  infer_instance

theorem hasLimit_of_pullbackInverseSystem
    {I : Type u} [Preorder I] {C : Type v} [Category.{w} C]
    (N : InverseSystem (PreorderQuotient I) C)
    [HasLimit (pullbackInverseSystem N)] : HasLimit N := by
  let _ : Functor.Initial (preorderQuotientProjection I).op :=
    preorderQuotientProjection_op_is_initial I
  exact Functor.Initial.hasLimit_of_comp (preorderQuotientProjection I).op

noncomputable def limitIso_pullbackInverseSystem
    {I : Type u} [Preorder I] {C : Type v} [Category.{w} C]
    (N : InverseSystem (PreorderQuotient I) C) [HasLimit N]
    [HasLimit (pullbackInverseSystem N)] :
    limit N ≅ limit (pullbackInverseSystem N) := by
  letI : Functor.Initial (preorderQuotientProjection I).op :=
    preorderQuotientProjection_op_is_initial I
  exact (Functor.Initial.limitIso (preorderQuotientProjection I).op N).symm

/- The section is the canonical order embedding supplied by Mathlib. -/
noncomputable def preorderQuotientSection (I : Type u) [Preorder I] :
    PreorderQuotient I ⥤ I :=
  (OrderEmbedding.ofAntisymmetrization I).monotone.functor

def inverseSystemPullbackFunctor
    {I : Type u} [Preorder I] {C : Type v} [Category.{w} C] :
    (InverseSystem (PreorderQuotient I) C) ⥤ (InverseSystem I C) :=
  (Functor.whiskeringLeft (Iᵒᵖ) ((PreorderQuotient I)ᵒᵖ) C).obj
    (preorderQuotientProjection I).op

noncomputable def inverseSystemSectionFunctor
    {I : Type u} [Preorder I] {C : Type v} [Category.{w} C] :
    (InverseSystem I C) ⥤ (InverseSystem (PreorderQuotient I) C) :=
  (Functor.whiskeringLeft ((PreorderQuotient I)ᵒᵖ) (Iᵒᵖ) C).obj
    (preorderQuotientSection I).op

theorem inverseSystemPullback_section_iso
    {I : Type u} [Preorder I] {C : Type v} [Category.{w} C] :
    Nonempty (𝟭 (InverseSystem (PreorderQuotient I) C) ≅
      inverseSystemPullbackFunctor (I := I) (C := C) ⋙
        inverseSystemSectionFunctor (I := I) (C := C)) := by
  sorry

theorem inverseSystemSection_pullback_iso
    {I : Type u} [Preorder I] {C : Type v} [Category.{w} C] :
    Nonempty (inverseSystemSectionFunctor (I := I) (C := C) ⋙
        inverseSystemPullbackFunctor (I := I) (C := C) ≅
      𝟭 (InverseSystem I C)) := by
  sorry

theorem inverseSystemPullbackFunctor_is_equivalence
    {I : Type u} [Preorder I] {C : Type v} [Category.{w} C] :
    (inverseSystemPullbackFunctor (I := I) (C := C)).IsEquivalence := by
  apply Functor.IsEquivalence.mk' (inverseSystemSectionFunctor (I := I) (C := C))
  · exact (inverseSystemPullback_section_iso (I := I) (C := C)).some
  · exact (inverseSystemSection_pullback_iso (I := I) (C := C)).some

/-! ### Directed systems and filtered categories -/

theorem isDirectedSystem_iff
    {I : Type u} [Preorder I] {C : Type v} [Category.{w} C]
    (M : System I C) : IsDirectedSystem M ↔ IsDirectedSet I := Iff.rfl

theorem isDirectedInverseSystem_iff
    {I : Type u} [Preorder I] {C : Type v} [Category.{w} C]
    (M : InverseSystem I C) : IsDirectedInverseSystem M ↔ IsDirectedSet I := Iff.rfl

theorem filtered_category_has_directed_replacement
    (I : Type u) [SmallCategory I] [IsFiltered I] :
    ∃ (J : Type u) (_ : PartialOrder J) (_ : IsDirectedOrder J)
      (_ : Nonempty J) (F : J ⥤ I), Functor.Final F := by
  exact IsFiltered.exists_directed I

theorem directed_replacement_hasColimit_of_comp
    {I : Type u} {J : Type v} [Category I] [Category J]
    {C : Type u'} [Category.{v'} C] (F : J ⥤ I) [Functor.Final F]
    (M : I ⥤ C) [HasColimit (F ⋙ M)] : HasColimit M := by
  exact Functor.Final.hasColimit_of_comp F

noncomputable def directed_replacement_colimit_iso
    {I : Type u} {J : Type v} [Category I] [Category J]
    {C : Type u'} [Category.{v'} C] (F : J ⥤ I) [Functor.Final F]
    (M : I ⥤ C) [HasColimit (F ⋙ M)] [HasColimit M] :
    colimit (F ⋙ M) ≅ colimit M := by
  exact Functor.Final.colimitIso F M

theorem directed_replacement_hasLimit_of_comp
    {I : Type u} {J : Type v} [Category I] [Category J]
    {C : Type u'} [Category.{v'} C] (F : J ⥤ I) [Functor.Final F]
    (M : Iᵒᵖ ⥤ C) [HasLimit (F.op ⋙ M)] : HasLimit M := by
  exact Functor.Initial.hasLimit_of_comp F.op

noncomputable def directed_replacement_limit_iso
    {I : Type u} {J : Type v} [Category I] [Category J]
    {C : Type u'} [Category.{v'} C] (F : J ⥤ I) [Functor.Final F]
    (M : Iᵒᵖ ⥤ C) [HasLimit (F.op ⋙ M)] [HasLimit M] :
    limit M ≅ limit (F.op ⋙ M) := by
  exact (Functor.Initial.limitIso F.op M).symm

/-! ### Finite directed indices and the idempotent example -/

theorem finite_directed_preorder_has_greatest
    (I : Type u) [Finite I] [Preorder I] [Nonempty I] [IsDirectedOrder I] :
    ∃ i : I, ∀ j : I, j ≤ i := by
  obtain ⟨i, hi⟩ := Finite.exists_le (id : I → I)
  exact ⟨i, fun j => hi j⟩

theorem hasColimit_of_finite_directed_system
    {I : Type u} [Finite I] [Preorder I] [Nonempty I] [IsDirectedOrder I]
    {C : Type v} [Category.{w} C] (M : System I C) : HasColimit M := by
  sorry

theorem finite_directed_system_colimit_iso_stage
    {I : Type u} [Finite I] [Preorder I] [Nonempty I] [IsDirectedOrder I]
    {C : Type v} [Category.{w} C] (M : System I C) [HasColimit M]
    (i : I) (hi : ∀ j : I, j ≤ i) :
    Nonempty (colimit M ≅ M.obj i) := by
  sorry

/- The source's finite filtered example is the one-object category of the
   two-element monoid with an absorbing idempotent. -/
inductive IdempotentArrow
  | identity
  | idempotent
  deriving DecidableEq

instance idempotentArrow_fintype : Fintype IdempotentArrow where
  elems := {IdempotentArrow.identity, IdempotentArrow.idempotent}
  complete := by
    intro x
    cases x <;> simp

def idempotentArrowMul : IdempotentArrow → IdempotentArrow → IdempotentArrow
  | .identity, a => a
  | .idempotent, _ => .idempotent

instance idempotentArrow_monoid : Monoid IdempotentArrow where
  one := .identity
  mul := idempotentArrowMul
  one_mul := by intro a; cases a <;> rfl
  mul_one := by intro a; cases a <;> rfl
  mul_assoc := by intro a b c; cases a <;> cases b <;> cases c <;> rfl

abbrev IdempotentCategory := SingleObj IdempotentArrow

def idempotentMorphism : Quiver.Hom.{0, 0}
    (SingleObj.star IdempotentArrow) (SingleObj.star IdempotentArrow) :=
  IdempotentArrow.idempotent

theorem idempotentMorphism_squared :
    idempotentMorphism ≫ idempotentMorphism = idempotentMorphism := by
  change IdempotentArrow.idempotent * IdempotentArrow.idempotent =
    IdempotentArrow.idempotent
  rfl

theorem idempotentMorphism_ne_identity :
    idempotentMorphism ≠
      (𝟙 (SingleObj.star IdempotentArrow) : Quiver.Hom.{0, 0}
        (SingleObj.star IdempotentArrow) (SingleObj.star IdempotentArrow)) := by
  intro h
  change IdempotentArrow.idempotent = IdempotentArrow.identity at h
  cases h

theorem idempotentCategory_is_finite : Finite IdempotentCategory := by
  infer_instance

theorem idempotentCategory_is_filtered : IsFiltered IdempotentCategory := by
  refine { cocone_objs := ?_, cocone_maps := ?_ }
  · intro X Y
    cases X
    cases Y
    exact ⟨_, 𝟙 _, 𝟙 _, trivial⟩
  · intro X Y f g
    cases X
    cases Y
    refine ⟨_, idempotentMorphism, ?_⟩
    cases f <;> cases g <;> rfl

theorem idempotentCategory_colimit_is_image
    (M : IdempotentCategory ⥤ Type u') :
    Nonempty (colimit M ≃ Types.Image (M.map idempotentMorphism)) := by
  sorry

/-! ### Finite nonempty inverse systems -/

theorem nonempty_limit_of_finite_nonempty_directed_inverse_system
    {I : Type v} [Preorder I] [Small.{u} I]
    [IsDirectedOrder I] [Nonempty I]
    (S : InverseSystem I (Type u))
    [∀ i : Iᵒᵖ, Finite (S.obj i)] [∀ i : Iᵒᵖ, Nonempty (S.obj i)] :
    Nonempty (limit S) := by
  apply Formalization.Books.Categories.Unit20.nonempty_limit_of_finite_nonempty_cofiltered_diagram S
  exact Formalization.Books.Categories.Unit20.isCofilteredDiagram_of_isCofiltered S

end

end Formalization.Books.Categories.Unit21
