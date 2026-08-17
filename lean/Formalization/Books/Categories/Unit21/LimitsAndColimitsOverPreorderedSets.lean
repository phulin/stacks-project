import Formalization.Books.Categories.Unit20.CofilteredLimits
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.CategoryTheory.Filtered.Basic
import Mathlib.CategoryTheory.Limits.Final
import Mathlib.CategoryTheory.Presentable.Directed
import Mathlib.CategoryTheory.Limits.Shapes.Preorder.Basic
import Mathlib.CategoryTheory.Limits.Types.Images
import Mathlib.CategoryTheory.SingleObj
import Mathlib.CategoryTheory.FinCategory.Basic
import Mathlib.Order.Antisymmetrization
import Mathlib.Order.Directed
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
  refine ⟨Nonempty.map (toAntisymmetrization (α := I) (· ≤ ·)) hI.1, ?_⟩
  let _ : IsDirectedOrder I := hI.2
  exact ⟨fun a b =>
    Antisymmetrization.induction_on (· ≤ ·) a (fun a =>
      Antisymmetrization.induction_on (· ≤ ·) b (fun b =>
        let ⟨c, hac, hbc⟩ := directed_of (· ≤ ·) a b
        ⟨toAntisymmetrization (· ≤ ·) c, hac, hbc⟩))⟩

theorem preorderQuotientProjection_is_final
    (I : Type u) [Preorder I] :
    Functor.Final (preorderQuotientProjection I) := by
  refine { out := fun d => ?_ }
  let i : I := ofAntisymmetrization (· ≤ ·) d
  let u : StructuredArrow d (preorderQuotientProjection I) :=
    StructuredArrow.mk (homOfLE (show d ≤ toAntisymmetrization (· ≤ ·) i by
      simp [i]))
  apply isConnected_of_isInitial
  let h : ∀ x : StructuredArrow d (preorderQuotientProjection I), u ⟶ x := fun x => by
    have hix : i ≤ x.right := by
      have h : toAntisymmetrization (· ≤ ·) (ofAntisymmetrization (· ≤ ·) d) ≤
          toAntisymmetrization (· ≤ ·) x.right := by
        simpa [preorderQuotientProjection] using x.hom.le
      exact (toAntisymmetrization_le_toAntisymmetrization_iff).mp h
    have hux : u.right ≤ x.right := by simpa [u] using hix
    exact StructuredArrow.homMk (f := u) (f' := x) (homOfLE hux)
      (by apply Subsingleton.elim)
  exact IsInitial.ofUniqueHom h (fun x m => by
    apply StructuredArrow.hom_ext
    exact Subsingleton.elim _ _)

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
    (N : System (PreorderQuotient I) C) [HasColimit N] :
    letI : Functor.Final (preorderQuotientProjection I) :=
      preorderQuotientProjection_is_final I
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
    (N : InverseSystem (PreorderQuotient I) C) [HasLimit N] :
    letI : Functor.Initial (preorderQuotientProjection I).op :=
      preorderQuotientProjection_op_is_initial I
    limit N ≅ limit (pullbackInverseSystem N) := by
  letI : Functor.Initial (preorderQuotientProjection I).op :=
    preorderQuotientProjection_op_is_initial I
  exact (Functor.Initial.limitIso (preorderQuotientProjection I).op N).symm

/- The section is the canonical order embedding supplied by Mathlib. -/
noncomputable def preorderQuotientSection (I : Type u) [Preorder I] :
    PreorderQuotient I ⥤ I :=
  (OrderEmbedding.ofAntisymmetrization I).monotone.functor

def systemPullbackFunctor
    {I : Type u} [Preorder I] {C : Type v} [Category.{w} C] :
    (System (PreorderQuotient I) C) ⥤ (System I C) :=
  (Functor.whiskeringLeft I (PreorderQuotient I) C).obj
    (preorderQuotientProjection I)

noncomputable def systemSectionFunctor
    {I : Type u} [Preorder I] {C : Type v} [Category.{w} C] :
    (System I C) ⥤ (System (PreorderQuotient I) C) :=
  (Functor.whiskeringLeft (PreorderQuotient I) I C).obj
    (preorderQuotientSection I)

theorem systemPullback_section_iso
    {I : Type u} [Preorder I] {C : Type v} [Category.{w} C] :
    Nonempty (𝟭 (System (PreorderQuotient I) C) ≅
      systemPullbackFunctor (I := I) (C := C) ⋙
        systemSectionFunctor (I := I) (C := C)) := by
  let e : ∀ q : PreorderQuotient I,
      q = (preorderQuotientSection I ⋙ preorderQuotientProjection I).obj q :=
    fun q => by
      simp [preorderQuotientProjection, preorderQuotientSection]
  refine ⟨NatIso.ofComponents (fun N => ?_) ?_⟩
  · refine NatIso.ofComponents (fun q => ?_) ?_
    change N.obj q ≅ N.obj ((preorderQuotientSection I ⋙ preorderQuotientProjection I).obj q)
    exact eqToIso (congrArg N.obj (e q))
    intro q q' f
    change N.map f ≫ (eqToIso (congrArg N.obj (e q'))).hom =
      (eqToIso (congrArg N.obj (e q))).hom ≫
        N.map ((preorderQuotientSection I ⋙ preorderQuotientProjection I).map f)
    rw [eqToIso.hom, eqToIso.hom, ← eqToHom_map N (e q'),
      ← eqToHom_map N (e q), ← N.map_comp, ← N.map_comp]
    congr 1
  · intro N N' α
    ext q
    change α.app q ≫ (eqToIso (congrArg N'.obj (e q))).hom =
      (eqToIso (congrArg N.obj (e q))).hom ≫
        α.app ((preorderQuotientSection I ⋙ preorderQuotientProjection I).obj q)
    simpa [eqToIso.hom, eqToHom_map] using
      (α.naturality (eqToHom (e q))).symm

theorem systemSection_pullback_iso
    {I : Type u} [Preorder I] {C : Type v} [Category.{w} C] :
    Nonempty (systemSectionFunctor (I := I) (C := C) ⋙
        systemPullbackFunctor (I := I) (C := C) ≅
      𝟭 (System I C)) := by
  let r : I → I := (preorderQuotientProjection I ⋙ preorderQuotientSection I).obj
  have hir : ∀ i : I, i ≤ r i := by
    intro i
    change i ≤ ofAntisymmetrization (· ≤ ·) (toAntisymmetrization (· ≤ ·) i)
    apply (toAntisymmetrization_le_toAntisymmetrization_iff).mp
    simp
  have hri : ∀ i : I, r i ≤ i := by
    intro i
    change ofAntisymmetrization (· ≤ ·) (toAntisymmetrization (· ≤ ·) i) ≤ i
    apply (toAntisymmetrization_le_toAntisymmetrization_iff).mp
    simp
  refine ⟨NatIso.ofComponents (fun M => ?_) ?_⟩
  · refine NatIso.ofComponents (fun i => ?_) ?_
    · change M.obj (r i) ≅ M.obj i
      exact
        { hom := M.map (homOfLE (hri i))
          inv := M.map (homOfLE (hir i))
          hom_inv_id := by
            rw [← M.map_comp, ← M.map_id]
            congr 1
          inv_hom_id := by
            rw [← M.map_comp, ← M.map_id]
            congr 1 }
    · intro i j f
      change M.map ((preorderQuotientProjection I ⋙ preorderQuotientSection I).map f) ≫
          M.map (homOfLE (hri j)) =
        M.map (homOfLE (hri i)) ≫ M.map f
      rw [← M.map_comp, ← M.map_comp]
      congr 1
  · intro M M' α
    ext i
    change α.app (r i) ≫ M'.map (homOfLE (hri i)) =
      M.map (homOfLE (hri i)) ≫ α.app i
    exact (α.naturality (homOfLE (hri i))).symm

theorem systemPullbackFunctor_is_equivalence
    {I : Type u} [Preorder I] {C : Type v} [Category.{w} C] :
    (systemPullbackFunctor (I := I) (C := C)).IsEquivalence := by
  apply Functor.IsEquivalence.mk' (systemSectionFunctor (I := I) (C := C))
  · exact (systemPullback_section_iso (I := I) (C := C)).some
  · exact (systemSection_pullback_iso (I := I) (C := C)).some

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
  let e : ∀ q : (PreorderQuotient I)ᵒᵖ,
      q = ((preorderQuotientSection I).op ⋙
        (preorderQuotientProjection I).op).obj q :=
    fun q => by
      simp [preorderQuotientProjection, preorderQuotientSection]
  refine ⟨NatIso.ofComponents (fun N => ?_) ?_⟩
  · refine NatIso.ofComponents (fun q => ?_) ?_
    change N.obj q ≅ N.obj (((preorderQuotientSection I).op ⋙
      (preorderQuotientProjection I).op).obj q)
    exact eqToIso (congrArg N.obj (e q))
    intro q q' f
    change N.map f ≫ (eqToIso (congrArg N.obj (e q'))).hom =
      (eqToIso (congrArg N.obj (e q))).hom ≫
        N.map (((preorderQuotientSection I).op ⋙
          (preorderQuotientProjection I).op).map f)
    rw [eqToIso.hom, eqToIso.hom, ← eqToHom_map N (e q'),
      ← eqToHom_map N (e q), ← N.map_comp, ← N.map_comp]
    congr 1
  · intro N N' α
    ext q
    change α.app q ≫ (eqToIso (congrArg N'.obj (e q))).hom =
      (eqToIso (congrArg N.obj (e q))).hom ≫
        α.app (((preorderQuotientSection I).op ⋙
          (preorderQuotientProjection I).op).obj q)
    simpa [eqToIso.hom, eqToHom_map] using
      (α.naturality (eqToHom (e q))).symm

theorem inverseSystemSection_pullback_iso
    {I : Type u} [Preorder I] {C : Type v} [Category.{w} C] :
    Nonempty (inverseSystemSectionFunctor (I := I) (C := C) ⋙
        inverseSystemPullbackFunctor (I := I) (C := C) ≅
      𝟭 (InverseSystem I C)) := by
  let r : I → I := (preorderQuotientProjection I ⋙ preorderQuotientSection I).obj
  have hir : ∀ i : I, i ≤ r i := by
    intro i
    change i ≤ ofAntisymmetrization (· ≤ ·) (toAntisymmetrization (· ≤ ·) i)
    apply (toAntisymmetrization_le_toAntisymmetrization_iff).mp
    simp
  have hri : ∀ i : I, r i ≤ i := by
    intro i
    change ofAntisymmetrization (· ≤ ·) (toAntisymmetrization (· ≤ ·) i) ≤ i
    apply (toAntisymmetrization_le_toAntisymmetrization_iff).mp
    simp
  refine ⟨NatIso.ofComponents (fun M => ?_) ?_⟩
  · refine NatIso.ofComponents (fun i => ?_) ?_
    · change M.obj (Opposite.op (r i.unop)) ≅ M.obj i
      exact
        { hom := M.map (homOfLE (hir i.unop)).op
          inv := M.map (homOfLE (hri i.unop)).op
          hom_inv_id := by
            rw [← M.map_comp, ← M.map_id]
            congr 1
          inv_hom_id := by
            rw [← M.map_comp, ← M.map_id]
            congr 1 }
    · intro i j f
      change M.map (((preorderQuotientProjection I).op ⋙
        (preorderQuotientSection I).op).map f) ≫
          M.map (homOfLE (hir j.unop)).op =
        M.map (homOfLE (hir i.unop)).op ≫ M.map f
      rw [← M.map_comp, ← M.map_comp]
      congr 1
  · intro M M' α
    ext i
    change α.app (((preorderQuotientProjection I).op ⋙
        (preorderQuotientSection I).op).obj i) ≫
      M'.map (homOfLE (hir i.unop)).op =
      M.map (homOfLE (hir i.unop)).op ≫ α.app i
    exact (α.naturality (homOfLE (hir i.unop)).op).symm

theorem inverseSystemPullbackFunctor_is_equivalence
    {I : Type u} [Preorder I] {C : Type v} [Category.{w} C] :
    (inverseSystemPullbackFunctor (I := I) (C := C)).IsEquivalence := by
  apply Functor.IsEquivalence.mk' (inverseSystemSectionFunctor (I := I) (C := C))
  · exact (inverseSystemPullback_section_iso (I := I) (C := C)).some
  · exact (inverseSystemSection_pullback_iso (I := I) (C := C)).some

/-! ### Directed systems and filtered categories -/

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
    (M : I ⥤ C) [HasColimit (F ⋙ M)] :
    letI : HasColimit M := Functor.Final.hasColimit_of_comp F
    colimit (F ⋙ M) ≅ colimit M := by
  letI : HasColimit M := Functor.Final.hasColimit_of_comp F
  exact Functor.Final.colimitIso F M

theorem directed_replacement_hasLimit_of_comp
    {I : Type u} {J : Type v} [Category I] [Category J]
    {C : Type u'} [Category.{v'} C] (F : J ⥤ I) [Functor.Final F]
    (M : Iᵒᵖ ⥤ C) [HasLimit (F.op ⋙ M)] : HasLimit M := by
  exact Functor.Initial.hasLimit_of_comp F.op

noncomputable def directed_replacement_limit_iso
    {I : Type u} {J : Type v} [Category I] [Category J]
    {C : Type u'} [Category.{v'} C] (F : J ⥤ I) [Functor.Final F]
    (M : Iᵒᵖ ⥤ C) [HasLimit (F.op ⋙ M)] :
    letI : HasLimit M := Functor.Initial.hasLimit_of_comp F.op
    limit M ≅ limit (F.op ⋙ M) := by
  letI : HasLimit M := Functor.Initial.hasLimit_of_comp F.op
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
  obtain ⟨i, hi⟩ := finite_directed_preorder_has_greatest I
  let _ : OrderTop I := { top := i, le_top := hi }
  infer_instance

theorem finite_directed_system_colimit_iso_stage
    {I : Type u} [Finite I] [Preorder I] [Nonempty I] [IsDirectedOrder I]
    {C : Type v} [Category.{w} C] (M : System I C)
    (i : I) (hi : ∀ j : I, j ≤ i) :
    letI : HasColimit M := hasColimit_of_finite_directed_system M
    Nonempty (colimit M ≅ M.obj i) := by
  let _ : HasColimit M := hasColimit_of_finite_directed_system M
  let hterm : IsTerminal i :=
    IsTerminal.ofUniqueHom (fun j => homOfLE (hi j))
      (fun j f => Subsingleton.elim _ _)
  exact ⟨IsColimit.coconePointUniqueUpToIso (colimit.isColimit M)
    (colimitOfDiagramTerminal hterm M)⟩

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

instance idempotentCategory_finCategory : FinCategory IdempotentCategory :=
  SingleObj.finCategoryOfFintype IdempotentArrow

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
  let c : M.CoconeTypes :=
    { pt := Types.Image (M.map idempotentMorphism)
      ι := fun _ => Set.rangeFactorization (M.map idempotentMorphism)
      ι_naturality := by
        intro j j' f
        have hj : j = SingleObj.star IdempotentArrow := Subsingleton.elim _ _
        have hj' : j' = SingleObj.star IdempotentArrow := Subsingleton.elim _ _
        subst j
        subst j'
        change
          (Set.rangeFactorization (ConcreteCategory.hom (M.map idempotentMorphism)) ∘
              ConcreteCategory.hom (M.map f)) =
            Set.rangeFactorization (ConcreteCategory.hom (M.map idempotentMorphism))
        cases f with
        | identity =>
            funext x
            simp only [Function.comp_apply]
            have h : (IdempotentArrow.identity :
                SingleObj.star IdempotentArrow ⟶ SingleObj.star IdempotentArrow) =
                (1 : IdempotentArrow) := by
              rfl
            rw [h, ← SingleObj.id_as_one IdempotentArrow (SingleObj.star IdempotentArrow),
              M.map_id]
            simp
        | idempotent =>
            funext x
            apply Subtype.ext
            change (M.map idempotentMorphism ≫ M.map idempotentMorphism) x =
              M.map idempotentMorphism x
            rw [← M.map_comp, idempotentMorphism_squared] }
  have hc : c.IsColimit := by
    refine ⟨?_, ?_⟩
    · intro x y hxy
      obtain ⟨i, xi, rfl⟩ := M.ιColimitType_jointly_surjective x
      obtain ⟨j, yj, rfl⟩ := M.ιColimitType_jointly_surjective y
      cases i
      cases j
      apply M.ιColimitType_eq_of_map_eq_map xi yj
        (k := SingleObj.star IdempotentArrow) idempotentMorphism idempotentMorphism
      exact congrArg Subtype.val hxy
    · intro z
      obtain ⟨x, hx⟩ := z.property
      refine ⟨M.ιColimitType (SingleObj.star IdempotentArrow) x, ?_⟩
      change Set.rangeFactorization (M.map idempotentMorphism) x = z
      apply Subtype.ext
      exact hx
  exact ⟨(Types.colimitEquivColimitType M).trans hc.equiv⟩

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
