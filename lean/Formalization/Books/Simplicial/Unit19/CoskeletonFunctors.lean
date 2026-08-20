import Formalization.Books.Simplicial.Unit12.TruncatedSimplicialObjects
import Mathlib.AlgebraicTopology.SimplicialObject.Coskeletal
import Mathlib.AlgebraicTopology.SimplicialSet.FiniteProd
import Mathlib.CategoryTheory.Functor.KanExtension.Pointwise
import Mathlib.CategoryTheory.Adjunction.Unique
import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits
import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts
import Mathlib.CategoryTheory.RepresentedBy
import Mathlib.Data.Finite.Sigma

/-!
# Simplicial Methods, Chapter 19: Coskeleton functors

The source's coskeleton is Mathlib's right Kan extension along the inclusion of
the truncated simplex category.  This file keeps that canonical interface and
adds source-facing names for the pointwise limit, the compatible-tuple
construction, and the inductive tower.
-/

namespace Formalization.Books.Simplicial.Unit19

open CategoryTheory
open CategoryTheory.Limits
open Opposite
open scoped _root_.Simplicial

universe v u v₁ u₁ v₂ u₂

/-! ## The right Kan extension and its mapping property -/

/-- The source's assertion that a particular truncated object has a coskeleton. -/
abbrev HasCoskeleton {C : Type u} [Category.{v} C] (n : ℕ)
    (U : SimplicialObject.Truncated C n) : Prop :=
  (SimplexCategory.Truncated.inclusion n).op.HasRightKanExtension U

/-- The source's assertion that the whole `n`-coskeleton functor exists. -/
abbrev HasCoskeletonFunctor {C : Type u} [Category.{v} C] (n : ℕ) : Prop :=
  ∀ U : SimplicialObject.Truncated C n, HasCoskeleton n U

abbrev truncInclusion (n : ℕ) := (SimplexCategory.Truncated.inclusion n).op

/-- A chosen coskeleton of a single truncated simplicial object. -/
noncomputable def coskeleton {C : Type u} [Category.{v} C] (n : ℕ)
    (U : SimplicialObject.Truncated C n) [HasCoskeleton n U] :
    SimplicialObject C :=
  Functor.rightKanExtension (truncInclusion n) U

/-- The counit `skₙ (coskₙ U) ⟶ U` of the chosen right Kan extension. -/
noncomputable def coskeletonCounit {C : Type u} [Category.{v} C] (n : ℕ)
    (U : SimplicialObject.Truncated C n) [HasCoskeleton n U] :
    truncInclusion n ⋙ coskeleton n U ⟶ U :=
  Functor.rightKanExtensionCounit (truncInclusion n) U

/-- The source's displayed mapping-property equivalence. -/
noncomputable def coskeletonHomEquiv {C : Type u} [Category.{v} C] (n : ℕ)
    (U : SimplicialObject.Truncated C n) [HasCoskeleton n U]
    (V : SimplicialObject C) :
    (V ⟶ coskeleton n U) ≃
      (truncInclusion n ⋙ V ⟶ U) :=
  letI : (coskeleton n U).IsRightKanExtension (coskeletonCounit n U) := by
    dsimp [coskeleton, coskeletonCounit]
    infer_instance
  Functor.homEquivOfIsRightKanExtension (coskeleton n U)
    (coskeletonCounit n U) V

/-- Uniqueness of the coskeleton up to the canonical unique isomorphism. -/
noncomputable def coskeletonUniqueIso {C : Type u} [Category.{v} C] (n : ℕ)
    (U : SimplicialObject.Truncated C n) [HasCoskeleton n U]
    (V : SimplicialObject C) (α : truncInclusion n ⋙ V ⟶ U)
    [V.IsRightKanExtension α] :
    coskeleton n U ≅ V :=
  letI : (coskeleton n U).IsRightKanExtension (coskeletonCounit n U) := by
    dsimp [coskeleton, coskeletonCounit]
    infer_instance
  Functor.rightKanExtensionUnique (coskeleton n U)
    (coskeletonCounit n U) V α

/-! ## The truncated overcategory and the pointwise limit formula -/

/-!
`coskeletonIndex m n` is Mathlib's `StructuredArrow` presentation of the
opposite of the source's full subcategory
`(Δ/[n])_{≤m}`.  Keeping the structured-arrow presentation makes the
pointwise Kan-extension API directly usable.
-/
abbrev coskeletonIndex (m n : ℕ) :=
  StructuredArrow (op (SimplexCategory.mk n)) (truncInclusion m)

/-- The diagram called `U(n)` in the source. -/
def coskeletonIndexDiagram {C : Type u} [Category.{v} C] (m n : ℕ)
    (U : SimplicialObject.Truncated C m) : coskeletonIndex m n ⥤ C :=
  StructuredArrow.proj _ _ ⋙ U

/-- The functor `φ̄` induced by a simplex map `φ : [n] ⟶ [n']`. -/
def coskeletonIndexMap {m n n' : ℕ}
    (φ : SimplexCategory.mk n ⟶ SimplexCategory.mk n') :
    coskeletonIndex m n ⥤ coskeletonIndex m n' :=
  StructuredArrow.map φ.op

theorem coskeletonIndexDiagram_map {C : Type u} [Category.{v} C]
    {m n n' : ℕ} (U : SimplicialObject.Truncated C m)
    (φ : SimplexCategory.mk n ⟶ SimplexCategory.mk n') :
    coskeletonIndexMap φ ⋙ coskeletonIndexDiagram m n' U =
      coskeletonIndexDiagram m n U := by
  rfl

/-- The pointwise value of the coskeleton at degree `n`. -/
noncomputable def pointwiseCoskeletonValue {C : Type u} [Category.{v} C]
    (m n : ℕ) (U : SimplicialObject.Truncated C m)
    [ (truncInclusion m).HasPointwiseRightKanExtension U] : C :=
  letI : HasLimit (coskeletonIndexDiagram m n U) := by
    dsimp [coskeletonIndexDiagram]
    infer_instance
  limit (coskeletonIndexDiagram m n U)

/-- The pointwise coskeleton functor, with its genuine limit-based body. -/
noncomputable def pointwiseCoskeleton {C : Type u} [Category.{v} C] (m : ℕ)
    [∀ U : SimplicialObject.Truncated C m, HasCoskeleton m U] :
    SimplicialObject.Truncated C m ⥤ SimplicialObject C :=
  SimplicialObject.Truncated.cosk (C := C) m

/-- The pointwise counit used to define the face maps from the limit. -/
noncomputable def pointwiseCoskeletonCounit {C : Type u} [Category.{v} C]
    (m : ℕ) (U : SimplicialObject.Truncated C m)
    [ (truncInclusion m).HasPointwiseRightKanExtension U] :
    truncInclusion m ⋙
        (Functor.pointwiseRightKanExtension (truncInclusion m)) U ⟶ U :=
  Functor.pointwiseRightKanExtensionCounit (truncInclusion m) U

theorem pointwiseCoskeleton_obj_formula {C : Type u} [Category.{v} C]
    (m n : ℕ)
    [∀ U : SimplicialObject.Truncated C m, HasCoskeleton m U]
    [∀ U : SimplicialObject.Truncated C m,
      (truncInclusion m).HasPointwiseRightKanExtension U]
    (U : SimplicialObject.Truncated C m) :
    Nonempty (((pointwiseCoskeleton m).obj U).obj
        (op (SimplexCategory.mk n)) ≅ pointwiseCoskeletonValue m n U) := by
  exact ⟨Functor.ranObjObjIsoLimit (truncInclusion m) U (op (SimplexCategory.mk n))⟩

theorem has_coskeleton_of_has_finite_limits {C : Type u} [Category.{v} C]
    [HasFiniteLimits C] (m : ℕ) (U : SimplicialObject.Truncated C m) :
    HasCoskeleton m U := by
  let : (truncInclusion m).HasPointwiseRightKanExtension U := by
    intro X
    have : Finite (SimplexCategory.Truncated m) :=
      Finite.of_injective
        (fun x => ⟨x.1.len, Nat.lt_succ_of_le x.2⟩ :
          SimplexCategory.Truncated m → Fin (m + 1))
        (by
          intro x y h
          cases x with
          | mk x hx =>
            cases y with
            | mk y hy =>
              congr
              exact SimplexCategory.ext (Fin.ext_iff.mp h))
    have : Fintype (SimplexCategory.Truncated m) := Fintype.ofFinite _
    have : Fintype ((SimplexCategory.Truncated m)ᵒᵖ) :=
      Fintype.ofEquiv _ equivToOpposite
    let : ∀ T : (SimplexCategory.Truncated m)ᵒᵖ,
        Finite (X ⟶ (truncInclusion m).obj T) := fun T =>
      Finite.of_injective (fun f => f.unop.toOrderHom.toFun)
        (by
          intro f g h
          apply Opposite.unop_injective
          apply SimplexCategory.Hom.ext
          exact DFunLike.ext _ _ (fun i => congrFun h i))
    let : ∀ T : (SimplexCategory.Truncated m)ᵒᵖ,
        Fintype (X ⟶ (truncInclusion m).obj T) := fun T => Fintype.ofFinite _
    let : Fintype (StructuredArrow X (truncInclusion m)) :=
      Fintype.ofInjective
        (fun j : StructuredArrow X (truncInclusion m) =>
          (⟨j.right, j.hom⟩ : Σ T, X ⟶ (truncInclusion m).obj T))
        (by
          rintro ⟨⟨⟩, jr, jh⟩ ⟨⟨⟩, kr, kh⟩ h
          cases h
          rfl)
    let : ∀ j k : StructuredArrow X (truncInclusion m), Finite (j ⟶ k) :=
      fun j k =>
        Finite.of_injective (fun f => f.right.unop.hom.toOrderHom.toFun)
          (by
            intro f g h
            apply Comma.hom_ext f g
            · exact Subsingleton.elim _ _
            · apply Opposite.unop_injective
              apply SimplexCategory.Truncated.Hom.ext
              exact DFunLike.ext _ _ (fun i => congrFun h i))
    let : FinCategory (StructuredArrow X (truncInclusion m)) :=
      { fintypeObj := inferInstance
        fintypeHom := fun j k => Fintype.ofFinite _ }
    infer_instance
  exact
    (Functor.pointwiseRightKanExtensionIsPointwiseRightKanExtension
      (truncInclusion m) U).hasRightKanExtension

theorem has_coskeleton_functor_of_has_finite_limits {C : Type u} [Category.{v} C]
    [HasFiniteLimits C] (m : ℕ) : HasCoskeletonFunctor (C := C) m := by
  intro U
  exact has_coskeleton_of_has_finite_limits m U

/-- In degrees at most `m`, the indexing category has the terminal-simplex
limit described in the source. -/
theorem has_trivial_coskeleton_limit {C : Type u} [Category.{v} C]
    (m n : ℕ) (h : n ≤ m) (U : SimplicialObject.Truncated C m) :
    HasLimit (coskeletonIndexDiagram m n U) := by
  let Y : (SimplexCategory.Truncated m)ᵒᵖ := op ⟨SimplexCategory.mk n, h⟩
  let := SimplexCategory.Truncated.inclusion.fullyFaithful m
  let : HasInitial (coskeletonIndex m n) :=
    (StructuredArrow.mkIdInitial (T := truncInclusion m) (Y := Y)).hasInitial
  infer_instance

noncomputable def trivialCoskeletonLimit {C : Type u} [Category.{v} C]
    (m n : ℕ) (h : n ≤ m) (U : SimplicialObject.Truncated C m) : C :=
  letI := has_trivial_coskeleton_limit m n h U
  limit (coskeletonIndexDiagram m n U)

theorem trivial_coskeleton_limit_iso {C : Type u} [Category.{v} C]
    (m n : ℕ) (h : n ≤ m) (U : SimplicialObject.Truncated C m) :
    Nonempty (trivialCoskeletonLimit m n h U ≅
      U.obj (op ⟨SimplexCategory.mk n, by exact h⟩)) := by
  let Y : (SimplexCategory.Truncated m)ᵒᵖ := op ⟨SimplexCategory.mk n, h⟩
  let := SimplexCategory.Truncated.inclusion.fullyFaithful m
  let hY := StructuredArrow.mkIdInitial (T := truncInclusion m) (Y := Y)
  let : HasLimit (coskeletonIndexDiagram m n U) := has_trivial_coskeleton_limit m n h U
  exact ⟨(limit.isLimit (coskeletonIndexDiagram m n U)).conePointUniqueUpToIso
    (limitOfDiagramInitial hY (coskeletonIndexDiagram m n U))⟩

theorem recover_coskeleton {C : Type u} [Category.{v} C] (n : ℕ)
    (U : SimplicialObject.Truncated C n) [HasCoskeleton n U]
    [ (truncInclusion n).HasPointwiseRightKanExtension U] :
    IsIso (coskeletonCounit n U) := by
  sorry

/-! ## The zero-truncated example -/

/-- A zero-truncated object obtained from an object of `C`. -/
def zeroTruncatedObject {C : Type u} [Category.{v} C] (X : C) :
    SimplicialObject.Truncated C 0 :=
  (Functor.const _).obj X

/-- The exact source assumption of finite nonempty self-products. -/
abbrev HasFiniteNonemptySelfProducts (C : Type u) [Category.{v} C] : Prop :=
  ∀ (X : C) (n : ℕ),
    HasLimit (Discrete.functor (fun _ : Fin (n + 1) => X))

/-- The chosen `(n+1)`-fold self-product. -/
noncomputable def finiteSelfProduct {C : Type u} [Category.{v} C]
    (X : C) (n : ℕ) (h : HasFiniteNonemptySelfProducts C) : C :=
  letI := h X n
  limit (Discrete.functor (fun _ : Fin (n + 1) => X))

private theorem has_nonempty_product_of_has_binary_products {C : Type u}
    [Category.{v} C] [HasBinaryProducts C] :
    ∀ (n : ℕ) (f : Fin (n + 1) → C),
      HasLimit (Discrete.functor f)
  | 0, f =>
      HasLimit.mk ⟨Fan.mk (f 0)
          (fun j => eqToHom (congrArg f (Fin.eq_zero j).symm)),
        Fan.IsLimit.mk _ (fun s => s.proj 0)
          (fun s j => by
            have hj : j = 0 := Fin.eq_zero j
            subst hj
            simp)
          (fun s m hm => by simpa using hm 0)⟩
  | n + 1, f =>
      let _ := has_nonempty_product_of_has_binary_products n
        (fun i : Fin (n + 1) => f i.succ)
      HasLimit.mk ⟨_, extendFanIsLimit f (limit.isLimit _) (limit.isLimit _)⟩

private theorem zero_truncated_object_eq
    (j : (SimplexCategory.Truncated 0)ᵒᵖ) :
    j = op ⟨SimplexCategory.mk 0, by simp⟩ := by
  apply Opposite.unop_injective
  apply ObjectProperty.FullSubcategory.ext
  apply SimplexCategory.ext
  simpa only [SimplexCategory.len_mk] using (unop j).property.antisymm (by simp)

private theorem zero_truncated_hom_eq
    {a b : (SimplexCategory.Truncated 0)ᵒᵖ} (f : a ⟶ b) :
    f = eqToHom ((zero_truncated_object_eq a).trans
      (zero_truncated_object_eq b).symm) := by
  have ha := zero_truncated_object_eq a
  have hb := zero_truncated_object_eq b
  cases ha
  cases hb
  apply Opposite.unop_injective
  apply ObjectProperty.hom_ext _
  apply SimplexCategory.Hom.ext_zero_left
  apply Fin.ext
  simp only [SimplexCategory.len_mk]
  omega

private theorem zero_truncated_hom_subsingleton
    (a b : (SimplexCategory.Truncated 0)ᵒᵖ) :
    Subsingleton (a ⟶ b) :=
  ⟨fun f g => (zero_truncated_hom_eq f).trans (zero_truncated_hom_eq g).symm⟩

private noncomputable def zero_truncated_functor_iso {C : Type u}
    [Category.{v} C] (U : SimplicialObject.Truncated C 0) :
    U ≅ zeroTruncatedObject
      (U.obj (op ⟨SimplexCategory.mk 0, by simp⟩)) := by
  refine NatIso.ofComponents
    (fun j => eqToIso (congrArg U.obj (zero_truncated_object_eq j))) ?_
  intro a b f
  dsimp [zeroTruncatedObject]
  rw [zero_truncated_hom_eq f]
  simp [eqToHom_map]

private def zeroCoskeletonIndexToDiscrete (n : ℕ) :
    coskeletonIndex 0 n ⥤ Discrete (Fin (n + 1)) where
  obj j := ⟨j.hom.unop.toOrderHom 0⟩
  map {j k} f := Discrete.eqToHom (by
    apply Fin.ext
    have hobj : j.right = k.right :=
      (zero_truncated_object_eq j.right).trans (zero_truncated_object_eq k.right).symm
    have hr : f.right = eqToHom hobj := zero_truncated_hom_eq f.right
    have hw := f.w
    rw [hr] at hw
    simp at hw
    simpa using congrArg (fun g => (g.unop.toOrderHom 0).val) hw)
  map_id _ := by simp
  map_comp _ _ := by simp

private def zeroCoskeletonIndexObject (n : ℕ) (i : Fin (n + 1)) :
    coskeletonIndex 0 n :=
  let Y : (SimplexCategory.Truncated 0)ᵒᵖ :=
    op ⟨SimplexCategory.mk 0, by simp⟩
  let f : (op (SimplexCategory.mk n) : SimplexCategoryᵒᵖ) ⟶
      (truncInclusion 0).obj Y := by
    change (op (SimplexCategory.mk n) : SimplexCategoryᵒᵖ) ⟶
      op (SimplexCategory.mk 0)
    exact (SimplexCategory.const (SimplexCategory.mk 0)
      (SimplexCategory.mk n) i).op
  StructuredArrow.mk f

private def zeroCoskeletonIndexFromDiscrete (n : ℕ) :
    Discrete (Fin (n + 1)) ⥤ coskeletonIndex 0 n where
  obj i := zeroCoskeletonIndexObject n i.as
  map := by
    intro i j f
    exact eqToHom (congrArg (zeroCoskeletonIndexObject n) (Discrete.eq_of_hom f))
  map_id _ := by simp
  map_comp _ _ := by simp

private theorem zero_index_from_to_obj_eq (n : ℕ) (j : coskeletonIndex 0 n) :
    (zeroCoskeletonIndexFromDiscrete n).obj
        ((zeroCoskeletonIndexToDiscrete n).obj j) = j := by
  rcases j with ⟨left, right, hom⟩
  cases zero_truncated_object_eq right
  dsimp [zeroCoskeletonIndexFromDiscrete, zeroCoskeletonIndexToDiscrete,
    zeroCoskeletonIndexObject]
  refine StructuredArrow.obj_ext _ _ rfl ?_
  simp only [eqToHom_refl]
  simpa using congrArg Quiver.Hom.op
    (SimplexCategory.eq_const_of_zero hom.unop).symm

private theorem zero_index_to_from_obj_eq (n : ℕ) (i : Discrete (Fin (n + 1))) :
    (zeroCoskeletonIndexToDiscrete n).obj
        ((zeroCoskeletonIndexFromDiscrete n).obj i) = i := by
  cases i with
  | mk i =>
      apply Discrete.ext
      dsimp [zeroCoskeletonIndexToDiscrete, zeroCoskeletonIndexFromDiscrete]
      change (SimplexCategory.const (SimplexCategory.mk 0)
        (SimplexCategory.mk n) i).toOrderHom 0 = i
      rfl

private noncomputable def zeroCoskeletonIndexEquivalence (n : ℕ) :
    coskeletonIndex 0 n ≌ Discrete (Fin (n + 1)) := by
  let F := zeroCoskeletonIndexToDiscrete n
  let G := zeroCoskeletonIndexFromDiscrete n
  exact CategoryTheory.Equivalence.mk F G (NatIso.ofComponents
      (fun j => eqToIso (zero_index_from_to_obj_eq n j).symm)
      (fun f => by
        apply StructuredArrow.hom_ext
        exact @Subsingleton.elim _ (zero_truncated_hom_subsingleton _ _) _ _))
      (NatIso.ofComponents
      (fun i => eqToIso (zero_index_to_from_obj_eq n i))
      (fun f => by apply Subsingleton.elim))

private theorem has_limit_zero_coskeleton_index {C : Type u}
    [Category.{v} C]
    (U : SimplicialObject.Truncated C 0)
    (hP : HasFiniteNonemptySelfProducts C) (n : ℕ) :
    HasLimit (coskeletonIndexDiagram 0 n U) := by
  let e := zeroCoskeletonIndexEquivalence n
  let X := U.obj (op ⟨SimplexCategory.mk 0, by simp⟩)
  let : HasLimit (Discrete.functor (fun _ : Fin (n + 1) => X)) := hP X n
  let : HasLimit
      (e.functor ⋙ Discrete.functor (fun _ : Fin (n + 1) => X)) :=
    hasLimit_equivalence_comp e
  let α : e.functor ⋙ Discrete.functor (fun _ : Fin (n + 1) => X) ≅
      coskeletonIndexDiagram 0 n U :=
    NatIso.ofComponents
      (fun j => U.mapIso (eqToIso (zero_truncated_object_eq
        ((StructuredArrow.proj _ _).obj j)).symm))
      (fun f => by
        dsimp [X, coskeletonIndexDiagram]
        have hmap :
            (Discrete.functor (fun _ : Fin (n + 1) => X)).map (e.functor.map f) =
              𝟙 X := by
          let hp : X = X := rfl
          change eqToHom hp = 𝟙 X
          simp
        rw [hmap, Category.id_comp, ← U.map_comp]
        congr 1
        rw [zero_truncated_hom_eq
          ((StructuredArrow.proj (op (SimplexCategory.mk n))
            (truncInclusion 0)).map f)]
        simp)
  exact hasLimit_of_iso α

private noncomputable def zero_coskeleton_limit_iso {C : Type u}
    [Category.{v} C]
    (U : SimplicialObject.Truncated C 0)
    (hP : HasFiniteNonemptySelfProducts C) (n : ℕ)
    [HasLimit (coskeletonIndexDiagram 0 n U)] :
    limit (coskeletonIndexDiagram 0 n U) ≅
      finiteSelfProduct (U.obj (op ⟨SimplexCategory.mk 0, by simp⟩)) n hP := by
  let e := zeroCoskeletonIndexEquivalence n
  let X := U.obj (op ⟨SimplexCategory.mk 0, by simp⟩)
  letI : HasLimit (Discrete.functor (fun _ : Fin (n + 1) => X)) := hP X n
  letI : HasLimit
      (e.functor ⋙ Discrete.functor (fun _ : Fin (n + 1) => X)) :=
    hasLimit_equivalence_comp e
  let α : e.functor ⋙ Discrete.functor (fun _ : Fin (n + 1) => X) ≅
      coskeletonIndexDiagram 0 n U :=
    NatIso.ofComponents
      (fun j => U.mapIso (eqToIso (zero_truncated_object_eq
        ((StructuredArrow.proj _ _).obj j)).symm))
      (fun f => by
        dsimp [X, coskeletonIndexDiagram]
        have hmap :
            (Discrete.functor (fun _ : Fin (n + 1) => X)).map (e.functor.map f) =
              𝟙 X := by
          let hp : X = X := rfl
          change eqToHom hp = 𝟙 X
          simp
        rw [hmap, Category.id_comp, ← U.map_comp]
        congr 1
        rw [zero_truncated_hom_eq
          ((StructuredArrow.proj (op (SimplexCategory.mk n))
            (truncInclusion 0)).map f)]
        simp)
  exact HasLimit.isoOfEquivalence e α

/-- The source's proposed degree formula for `cosk₀ X`. -/
noncomputable def coskZero {C : Type u} [Category.{v} C] (X : C)
    [HasCoskeleton 0 (zeroTruncatedObject X)] : SimplicialObject C :=
  coskeleton 0 (zeroTruncatedObject X)

theorem cosk_zero_mapping_property {C : Type u} [Category.{v} C] (X : C)
    [HasCoskeleton 0 (zeroTruncatedObject X)] (V : SimplicialObject C) :
    Nonempty ((V ⟶ coskZero X) ≃
      (truncInclusion 0 ⋙ V ⟶ zeroTruncatedObject X)) := by
  exact ⟨by
    simpa only [coskZero] using coskeletonHomEquiv 0 (zeroTruncatedObject X) V⟩

theorem cosk_zero_degree_formula {C : Type u} [Category.{v} C]
    (X : C) (h : HasFiniteNonemptySelfProducts C)
    [HasCoskeleton 0 (zeroTruncatedObject X)] (n : ℕ) :
    Nonempty ((coskZero X).obj (op (SimplexCategory.mk n)) ≅
      finiteSelfProduct X n h) := by
  let U := zeroTruncatedObject X
  let : (truncInclusion 0).HasPointwiseRightKanExtension U := by
    rintro ⟨⟨k⟩⟩
    exact has_limit_zero_coskeleton_index U h k
  let : HasLimit (coskeletonIndexDiagram 0 n U) :=
    has_limit_zero_coskeleton_index U h n
  let : (coskZero X).IsRightKanExtension (coskeletonCounit 0 U) := by
    dsimp [coskZero, coskeleton, coskeletonCounit]
    infer_instance
  let e : coskZero X ≅
      Functor.pointwiseRightKanExtension (truncInclusion 0) U :=
    Functor.rightKanExtensionUnique (coskZero X) (coskeletonCounit 0 U)
      (Functor.pointwiseRightKanExtension (truncInclusion 0) U)
      (Functor.pointwiseRightKanExtensionCounit (truncInclusion 0) U)
  let q : (Functor.pointwiseRightKanExtension (truncInclusion 0) U).obj
      (op (SimplexCategory.mk n)) ≅ limit (coskeletonIndexDiagram 0 n U) :=
    Functor.RightExtension.IsPointwiseRightKanExtensionAt.isoLimit
      ((Functor.pointwiseRightKanExtensionIsPointwiseRightKanExtension
        (truncInclusion 0) U) (op (SimplexCategory.mk n)))
  exact ⟨e.app (op (SimplexCategory.mk n)) ≪≫ q ≪≫
    zero_coskeleton_limit_iso U h n⟩

theorem has_coskeleton_zero_of_has_binary_products {C : Type u}
    [Category.{v} C] [HasBinaryProducts C] (X : C) :
    HasCoskeleton 0 (zeroTruncatedObject X) := by
  let : (truncInclusion 0).HasPointwiseRightKanExtension
      (zeroTruncatedObject X) := by
    rintro ⟨⟨n⟩⟩
    exact has_limit_zero_coskeleton_index (zeroTruncatedObject X)
      (fun Y k => has_nonempty_product_of_has_binary_products k (fun _ => Y)) n
  exact
    (Functor.pointwiseRightKanExtensionIsPointwiseRightKanExtension
      (truncInclusion 0) (zeroTruncatedObject X)).hasRightKanExtension

theorem has_coskeleton_functor_zero_of_has_binary_products {C : Type u}
    [Category.{v} C] [HasBinaryProducts C] :
    HasCoskeletonFunctor (C := C) 0 := by
  intro U
  let e := zero_truncated_functor_iso U
  exact (Functor.hasRightExtension_iff_of_iso₂ (truncInclusion 0) e).mpr
    (has_coskeleton_zero_of_has_binary_products
      (U.obj (op ⟨SimplexCategory.mk 0, by simp⟩)))

/-! ## The compatible tuple used to add one level -/

/-- The face `U_{n+1} ⟶ U_n` in a `(n+1)`-truncated object. -/
def truncatedFace {C : Type u} [Category.{v} C] (n : ℕ)
    (U : SimplicialObject.Truncated C (n + 1)) (i : Fin (n + 2)) :
    U.obj (op ⟨SimplexCategory.mk (n + 1), by simp⟩) ⟶
      U.obj (op ⟨SimplexCategory.mk n, by simp⟩) :=
  U.map (SimplexCategory.Truncated.δ (n + 1) i (by simp) (by simp)).op

/-- A compatible family of `(n+2)` maps into `U_{n+1}`.

The parameter `n` is shifted by one relative to the source's notation, so
the tuple has the source's length `((n+1)+2)` and its entries lie in
`U_{n+1}`.
-/
def CompatibleBoundary {C : Type u} [Category.{v} C] (n : ℕ)
    (U : SimplicialObject.Truncated C (n + 1)) (T : C) : Type v :=
  { f : Fin (n + 3) →
      (T ⟶ U.obj (op ⟨SimplexCategory.mk (n + 1), by simp⟩)) //
    ∀ (i j : Fin (n + 3)) (hij : i < j),
      f i ≫ truncatedFace n U ⟨j.val - 1, by omega⟩ =
        f j ≫ truncatedFace n U ⟨i.val, by omega⟩ }

/-- The compatible-tuple functor is contravariant in the test object. -/
def compatibleBoundaryFunctor {C : Type u} [Category.{v} C] (n : ℕ)
    (U : SimplicialObject.Truncated C (n + 1)) :
    Cᵒᵖ ⥤ Type v where
  obj T := CompatibleBoundary n U T.unop
  map := fun {T₁ T₂} (f : T₁ ⟶ T₂) =>
    TypeCat.homEquiv.symm (fun (q : CompatibleBoundary n U T₁.unop) =>
      (⟨fun i => f.unop ≫ q.1 i, by
          intro i j hij
          simpa only [Category.assoc] using
            congrArg (fun h => f.unop ≫ h) (q.2 i j hij)⟩ :
        CompatibleBoundary n U T₂.unop))
  map_id := by
    intro T
    apply ConcreteCategory.hom_ext
    intro q
    apply Subtype.ext
    funext i
    change (𝟙 T).unop ≫ q.1 i = q.1 i
    simp
  map_comp := by
    intro T₁ T₂ T₃ f g
    apply TypeCat.homEquiv.injective
    funext q
    apply Subtype.ext
    funext i
    change (g.unop ≫ f.unop) ≫ q.1 i =
      g.unop ≫ (f.unop ≫ q.1 i)
    simp only [Category.assoc]

/-- The two-face map used in the face relation. -/
def twoFace {n : ℕ} (i j : Fin (n + 2)) (_hij : i < j) :
    SimplexCategory.mk n ⟶ SimplexCategory.mk (n + 2) :=
  SimplexCategory.δ i ≫ SimplexCategory.δ j.succ

theorem twoFace_eq {n : ℕ} (i j : Fin (n + 2)) (hij : i < j) :
    twoFace i j hij =
      SimplexCategory.δ j ≫ SimplexCategory.δ i.castSucc := by
  simpa [twoFace] using (SimplexCategory.δ_comp_δ (Nat.le_of_lt hij))

private theorem compatibleBoundary_factor_eq {C : Type u} [Category.{v} C]
    (n : ℕ) (U : SimplicialObject.Truncated C (n + 1)) {T : C}
    (q : CompatibleBoundary n U T) {Δ : SimplexCategory} (hΔ : Δ.len ≤ n + 1)
    (alpha : Δ ⟶ SimplexCategory.mk ((n + 1) + 1))
    {i j : Fin (n + 3)} (hij : i < j)
    (ψ φ : Δ ⟶ SimplexCategory.mk (n + 1))
    (hα : alpha = ψ ≫ SimplexCategory.δ i)
    (hβ : alpha = φ ≫ SimplexCategory.δ j) :
    q.1 i ≫ U.map (SimplexCategory.Truncated.Hom.tr ψ (by omega) (by simp)).op =
      q.1 j ≫ U.map (SimplexCategory.Truncated.Hom.tr φ (by omega) (by simp)).op := by
  have aux :
      ∀ {i j : Fin (n + 3)} (hij : i < j)
      (ψ φ : Δ ⟶ SimplexCategory.mk (n + 1)),
      alpha = ψ ≫ SimplexCategory.δ i →
      alpha = φ ≫ SimplexCategory.δ j →
      q.1 i ≫ U.map (SimplexCategory.Truncated.Hom.tr ψ (by omega) (by simp)).op =
        q.1 j ≫ U.map (SimplexCategory.Truncated.Hom.tr φ (by omega) (by simp)).op := by
    intro i j hij ψ φ hα hβ
    have factor_miss : ∀ x, ψ.toOrderHom x ≠ j.pred hij.ne_zero := by
      intro x hx
      have ha := congrArg (fun f => f.toOrderHom x) hα
      have hb := congrArg (fun f => f.toOrderHom x) hβ
      simp only [SimplexCategory.comp_toOrderHom, OrderHom.comp_coe,
        Function.comp_apply] at ha hb
      dsimp [SimplexCategory.δ, SimplexCategory.mkHom] at ha hb
      rw [hx] at ha
      have hval :
          i.succAboveOrderEmb.toOrderHom (j.pred hij.ne_zero) = j := by
        simpa only [Fin.succAboveOrderEmb_apply, OrderEmbedding.toOrderHom_coe] using
          Fin.succAbove_pred_of_lt i j hij
      rw [hval] at ha
      have hne : ∀ y : Fin (n + 2), (SimplexCategory.δ j).toOrderHom y ≠ j := by
        intro y
        simp [SimplexCategory.δ, SimplexCategory.mkHom]
      exact hne (φ.toOrderHom x) ((ha.symm.trans hb).symm)
    obtain ⟨ξ, hξ⟩ :=
      SimplexCategory.eq_comp_δ_of_not_surjective' ψ (j.pred hij.ne_zero)
        (by exact factor_miss)
    let i' : Fin (n + 2) := ⟨i.val, by omega⟩
    let r : Fin (n + 2) := j.pred hij.ne_zero
    have hi'j : i'.castSucc < j := by
      simpa [i'] using hij
    have hδ :
        SimplexCategory.δ r ≫ SimplexCategory.δ i =
          SimplexCategory.δ i' ≫ SimplexCategory.δ j := by
      simpa [i', r] using
        (SimplexCategory.δ_comp_δ' (i := i') (j := j) hi'j).symm
    have hφ : φ = ξ ≫ SimplexCategory.δ i' := by
      apply (cancel_mono (SimplexCategory.δ j)).1
      calc
        φ ≫ SimplexCategory.δ j = alpha := hβ.symm
        _ = ψ ≫ SimplexCategory.δ i := hα
        _ = (ξ ≫ SimplexCategory.δ r) ≫ SimplexCategory.δ i := by rw [hξ]
        _ = ξ ≫ (SimplexCategory.δ r ≫ SimplexCategory.δ i) := by
          simp [Category.assoc]
        _ = ξ ≫ (SimplexCategory.δ i' ≫ SimplexCategory.δ j) := by rw [hδ]
        _ = (ξ ≫ SimplexCategory.δ i') ≫ SimplexCategory.δ j := by
          simp [Category.assoc]
    rw [hξ, hφ, SimplexCategory.Truncated.Hom.tr_comp,
      SimplexCategory.Truncated.Hom.tr_comp]
    simp only [op_comp, Functor.map_comp]
    have hq := q.2 i j hij
    simp only [truncatedFace] at hq
    have hrj :
        (⟨j.val - 1, by omega⟩ : Fin (n + 2)) = r := by
      apply Fin.ext
      simp [r]
    have hii : (⟨i.val, by omega⟩ : Fin (n + 2)) = i' := by
      apply Fin.ext
      rfl
    rw [hrj, hii] at hq
    simpa using congrArg (fun z =>
      z ≫ U.map (SimplexCategory.Truncated.Hom.tr ξ hΔ (by simp)).op) hq
  by_cases h : i = j
  · subst j
    have hψ : ψ = φ := by
      apply (cancel_mono (SimplexCategory.δ i)).1
      exact hα.symm.trans hβ
    subst φ
    rfl
  · obtain hlt | hlt := lt_or_gt_of_ne h
    · exact aux hij ψ φ hα hβ
    · exact (aux hlt φ ψ hβ hα).symm

theorem formula_limit_of_representable {C : Type u} [Category.{v} C]
    (n : ℕ) (U : SimplicialObject.Truncated C (n + 1)) (Uplus : C)
    (hRep : (compatibleBoundaryFunctor n U).RepresentableBy Uplus)
    [HasLimit (coskeletonIndexDiagram (n + 1) (n + 2) U)] :
    Nonempty (Uplus ≅ limit (coskeletonIndexDiagram (n + 1) (n + 2) U)) := by
  let index := coskeletonIndex (n + 1) (n + 2)
  let D := coskeletonIndexDiagram (n + 1) (n + 2) U
  let targetEq :
      (SimplexCategory.mk (n + 2) : SimplexCategory) =
        SimplexCategory.mk ((n + 1) + 1) := by
    congr 1
  let alpha (j : index) :
      j.right.unop.1 ⟶ SimplexCategory.mk ((n + 1) + 1) :=
    j.hom.unop ≫ eqToHom targetEq
  have alpha_not_surjective (j : index) :
      ¬ Function.Surjective (alpha j).toOrderHom := by
    intro hs
    have hEpi : Epi (alpha j) := (SimplexCategory.epi_iff_surjective).2 hs
    let _ : Epi (alpha j) := hEpi
    have hlen := SimplexCategory.len_le_of_epi (alpha j)
    have hk := j.right.unop.property
    dsimp [alpha] at hlen
    omega
  let facIdx (j : index) : Fin (n + 3) :=
    Classical.choose
      (SimplexCategory.eq_comp_δ_of_not_surjective (alpha j)
        (alpha_not_surjective j))
  let facMap (j : index) : j.right.unop.1 ⟶ SimplexCategory.mk (n + 1) :=
    Classical.choose
      (Classical.choose_spec
        (SimplexCategory.eq_comp_δ_of_not_surjective (alpha j)
          (alpha_not_surjective j)))
  have facEq (j : index) :
      alpha j = facMap j ≫ SimplexCategory.δ (facIdx j) :=
    Classical.choose_spec
      (Classical.choose_spec
        (SimplexCategory.eq_comp_δ_of_not_surjective (alpha j)
          (alpha_not_surjective j)))
  let faceArrow (i : Fin (n + 3)) :
      (op (SimplexCategory.mk (n + 2)) : SimplexCategoryᵒᵖ) ⟶
        (truncInclusion (n + 1)).obj
          (op ⟨SimplexCategory.mk (n + 1), by simp⟩) :=
    (SimplexCategory.δ i ≫ eqToHom targetEq.symm).op
  let faceObj (i : Fin (n + 3)) : index := StructuredArrow.mk (faceArrow i)
  let faceToJ (j : index) :
      faceObj (facIdx j) ⟶ j :=
    StructuredArrow.homMk
      (SimplexCategory.Truncated.Hom.tr (n := n + 1) (facMap j)
        j.right.unop.property (by simp)).op (by
        apply Opposite.unop_injective
        change facMap j ≫ (SimplexCategory.δ (facIdx j) ≫
          eqToHom targetEq.symm) = j.hom.unop
        rw [← Category.assoc, ← facEq j]
        simp [alpha])
  have hαf {j k : index} (f : j ⟶ k) :
      alpha k = f.right.unop.hom ≫ alpha j := by
    have hw0 := f.w
    change j.hom ≫ (f.right.unop.hom).op = k.hom at hw0
    have hw : f.right.unop.hom ≫ j.hom.unop = k.hom.unop := by
      exact congrArg Opposite.unop hw0
    simpa [alpha, Category.assoc] using
      congrArg (fun z => z ≫ eqToHom targetEq) hw.symm
  have hcomp {j k : index} (f : j ⟶ k)
      :
      (SimplexCategory.Truncated.Hom.tr (n := n + 1) (facMap j)
        j.right.unop.property (by simp)).op ≫ f.right =
      (SimplexCategory.Truncated.Hom.tr (n := n + 1)
        (f.right.unop.hom ≫ facMap j)
        k.right.unop.property (by simp)).op := by
    apply Opposite.unop_injective
    exact (SimplexCategory.Truncated.Hom.tr_comp' (n := n + 1)
      (f := f.right.unop.hom)
      (g := SimplexCategory.Truncated.Hom.tr (n := n + 1) (facMap j)
        j.right.unop.property (by simp))
      (ha := k.right.unop.property)).symm
  let component (q : CompatibleBoundary n U Uplus) (j : index) :
      Uplus ⟶ D.obj j :=
    q.1 (facIdx j) ≫
      U.map (SimplexCategory.Truncated.Hom.tr (n := n + 1) (facMap j)
        j.right.unop.property (by simp)).op
  let boundaryCone (q : CompatibleBoundary n U Uplus) : Cone D :=
    { pt := Uplus
      π := ( { app := fun j => component q j
               naturality := by
                 intro j k f
                 have hfac :
                     alpha k =
                       (f.right.unop.hom ≫ facMap j) ≫
                         SimplexCategory.δ (facIdx j) := by
                   rw [hαf f, facEq j]
                   simp [Category.assoc]
                 have hfactor :
                     q.1 (facIdx j) ≫
                         U.map (SimplexCategory.Truncated.Hom.tr (n := n + 1)
                           (f.right.unop.hom ≫ facMap j)
                           k.right.unop.property (by simp)).op =
                       q.1 (facIdx k) ≫
                         U.map (SimplexCategory.Truncated.Hom.tr (n := n + 1)
                           (facMap k) k.right.unop.property (by simp)).op := by
                   by_cases heq : facIdx j = facIdx k
                   · rw [← heq]
                     have hmap : f.right.unop.hom ≫ facMap j = facMap k := by
                       apply (cancel_mono (SimplexCategory.δ (facIdx j))).1
                       calc
                         (f.right.unop.hom ≫ facMap j) ≫
                             SimplexCategory.δ (facIdx j) = alpha k := hfac.symm
                         _ = facMap k ≫ SimplexCategory.δ (facIdx j) := by
                           simpa [heq] using facEq k
                     rw [hmap]
                   · obtain hlt | hgt := lt_or_gt_of_ne heq
                     · exact compatibleBoundary_factor_eq n U q
                         k.right.unop.property (alpha k) hlt
                         (f.right.unop.hom ≫ facMap j) (facMap k) hfac (facEq k)
                     · exact (compatibleBoundary_factor_eq n U q
                         k.right.unop.property (alpha k) hgt
                         (facMap k) (f.right.unop.hom ≫ facMap j) (facEq k) hfac).symm
                 dsimp [component, D]
                 have hDmap :
                     (coskeletonIndexDiagram (n + 1) (n + 2) U).map f =
                       U.map f.right := by
                   rfl
                 rw [hDmap]
                 rw [Category.id_comp]
                 have hmap_comp :
                     U.map (SimplexCategory.Truncated.Hom.tr
                       (f.right.unop.hom ≫ facMap j)
                       k.right.unop.property (by simp)).op =
                       U.map (SimplexCategory.Truncated.Hom.tr (facMap j)
                         j.right.unop.property (by simp)).op ≫ U.map f.right := by
                   rw [← hcomp f]
                   exact U.map_comp _ _
                 calc
                   q.1 (facIdx k) ≫
                         U.map (SimplexCategory.Truncated.Hom.tr (facMap k)
                           k.right.unop.property (by simp)).op =
                       q.1 (facIdx j) ≫
                         U.map (SimplexCategory.Truncated.Hom.tr
                           (f.right.unop.hom ≫ facMap j)
                           k.right.unop.property (by simp)).op := hfactor.symm
                   _ = q.1 (facIdx j) ≫
                         (U.map (SimplexCategory.Truncated.Hom.tr (facMap j)
                           j.right.unop.property (by simp)).op ≫ U.map f.right) := by
                     exact congrArg (fun z => q.1 (facIdx j) ≫ z) hmap_comp
                   _ = (q.1 (facIdx j) ≫
                         U.map (SimplexCategory.Truncated.Hom.tr (facMap j)
                           j.right.unop.property (by simp)).op) ≫ U.map f.right := by
                     simp only [Category.assoc]
                 } : ((Functor.const index).obj Uplus ⟶ D)) }
  let commonMap (i j : Fin (n + 3)) (hij : i < j) :
      (faceObj j).right ⟶
        (op ⟨SimplexCategory.mk n, by simp⟩) :=
    (SimplexCategory.Truncated.δ (n + 1) ⟨i.val, by omega⟩
      (by simp) (by simp)).op
  let commonObj (i j : Fin (n + 3)) (hij : i < j) : index :=
    StructuredArrow.mk ((faceObj j).hom ≫
      (truncInclusion (n + 1)).map (commonMap i j hij))
  let faceToCommonJ (i j : Fin (n + 3)) (hij : i < j) :
      faceObj j ⟶ commonObj i j hij :=
    StructuredArrow.homMk' (faceObj j) (commonMap i j hij)
  let faceToCommonI (i j : Fin (n + 3)) (hij : i < j) :
      faceObj i ⟶ commonObj i j hij :=
    StructuredArrow.homMk (f := faceObj i) (f' := commonObj i j hij)
      (SimplexCategory.Truncated.δ (n + 1) (j.pred hij.ne_zero)
        (by simp) (by simp)).op (by
        apply Opposite.unop_injective
        dsimp [faceObj, faceArrow, commonObj, commonMap]
        change SimplexCategory.δ (j.pred hij.ne_zero) ≫ SimplexCategory.δ i =
          SimplexCategory.δ ⟨i.val, by omega⟩ ≫ SimplexCategory.δ j
        exact (SimplexCategory.δ_comp_δ' (i := ⟨i.val, by omega⟩)
          (j := j) (by simpa using hij)).symm)
  let qL : CompatibleBoundary n U (limit D) :=
    ⟨fun i => limit.π D (faceObj i), by
      intro i j hij
      have wI := (limit.cone D).w (faceToCommonI i j hij)
      have wJ := (limit.cone D).w (faceToCommonJ i j hij)
      change limit.π D (faceObj i) ≫
          U.map (SimplexCategory.Truncated.δ (n + 1)
            ⟨j.val - 1, by omega⟩ (by simp) (by simp)).op =
        limit.π D (faceObj j) ≫
          U.map (SimplexCategory.Truncated.δ (n + 1)
            ⟨i.val, by omega⟩ (by simp) (by simp)).op
      exact wI.trans wJ.symm⟩
  let qU : (compatibleBoundaryFunctor n U).obj (op Uplus) :=
    hRep.homEquiv (𝟙 Uplus)
  let a : limit D ⟶ Uplus := hRep.homEquiv.symm qL
  let b : Uplus ⟶ limit D := (limit.isLimit D).lift (boundaryCone qU)
  have hqa (i : Fin (n + 3)) :
      a ≫ qU.1 i = qL.1 i := by
    have ha : hRep.homEquiv a = qL := by
      dsimp [a]
      exact hRep.homEquiv.apply_symm_apply qL
    have h := hRep.homEquiv_eq a
    have hi := congrArg (fun q : CompatibleBoundary n U (limit D) => q.1 i) h
    change (hRep.homEquiv a).1 i = a ≫ qU.1 i at hi
    rw [ha] at hi
    exact hi.symm
  have hcomponent_face (i : Fin (n + 3)) :
      component qU (faceObj i) = qU.1 i := by
    have hface : alpha (faceObj i) =
        (𝟙 (SimplexCategory.mk (n + 1))) ≫ SimplexCategory.δ i := by
      simp [alpha, faceObj, faceArrow]
    by_cases heq : facIdx (faceObj i) = i
    · have hmap : facMap (faceObj i) = 𝟙 _ := by
        apply (cancel_mono (SimplexCategory.δ i)).1
        calc
          facMap (faceObj i) ≫ SimplexCategory.δ i = alpha (faceObj i) := by
            simpa [heq] using (facEq (faceObj i)).symm
          _ = (𝟙 _) ≫ SimplexCategory.δ i := hface
      dsimp [component]
      rw [heq, hmap]
      change qU.1 i ≫ U.map
          (𝟙 ((op ⟨SimplexCategory.mk (n + 1), by simp⟩) :
            (SimplexCategory.Truncated (n + 1))ᵒᵖ)) = qU.1 i
      rw [U.map_id]
      simp
    · obtain hlt | hgt := lt_or_gt_of_ne heq
      · have h := compatibleBoundary_factor_eq n U qU
            (faceObj i).right.unop.property (alpha (faceObj i)) hlt
            (facMap (faceObj i)) (𝟙 _) (facEq (faceObj i)) hface
        change qU.1 (facIdx (faceObj i)) ≫
            U.map (SimplexCategory.Truncated.Hom.tr (facMap (faceObj i))
              (faceObj i).right.unop.property (by simp)).op = qU.1 i
        exact h.trans (by
          change qU.1 i ≫ U.map
              (𝟙 ((op ⟨SimplexCategory.mk (n + 1), by simp⟩) :
                (SimplexCategory.Truncated (n + 1))ᵒᵖ)) = qU.1 i
          rw [U.map_id]
          simp)
      · have h := compatibleBoundary_factor_eq n U qU
            (faceObj i).right.unop.property (alpha (faceObj i)) hgt
            (𝟙 _) (facMap (faceObj i)) hface (facEq (faceObj i))
        change qU.1 (facIdx (faceObj i)) ≫
            U.map (SimplexCategory.Truncated.Hom.tr (facMap (faceObj i))
              (faceObj i).right.unop.property (by simp)).op = qU.1 i
        exact h.symm.trans (by
          change qU.1 i ≫ U.map
              (𝟙 ((op ⟨SimplexCategory.mk (n + 1), by simp⟩) :
                (SimplexCategory.Truncated (n + 1))ᵒᵖ)) = qU.1 i
          rw [U.map_id]
          simp)
  have hba : b ≫ a = 𝟙 Uplus := by
    apply hRep.homEquiv.injective
    rw [hRep.homEquiv_comp]
    have ha : hRep.homEquiv a = qL := by
      dsimp [a]
      exact hRep.homEquiv.apply_symm_apply qL
    rw [ha]
    apply Subtype.ext
    funext i
    change b ≫ qL.1 i = qU.1 i
    dsimp [qL]
    have hf : b ≫ limit.π D (faceObj i) = component qU (faceObj i) := by
      dsimp [b]
      exact (limit.isLimit D).fac (boundaryCone qU) (faceObj i)
    exact hf.trans (hcomponent_face i)
  have hab : a ≫ b = 𝟙 (limit D) := by
    apply (limit.isLimit D).hom_ext
    intro j
    rw [Category.assoc, (limit.isLimit D).fac (boundaryCone qU) j]
    simp only [Category.id_comp]
    change a ≫ component qU j = limit.π D j
    have h1 : a ≫ component qU j =
        qL.1 (facIdx j) ≫
          U.map (SimplexCategory.Truncated.Hom.tr (facMap j)
            j.right.unop.property (by simp)).op := by
      dsimp [component]
      calc
        a ≫ (qU.1 (facIdx j) ≫
            U.map (SimplexCategory.Truncated.Hom.tr (facMap j)
              j.right.unop.property (by simp)).op) =
            (a ≫ qU.1 (facIdx j)) ≫
              U.map (SimplexCategory.Truncated.Hom.tr (facMap j)
                j.right.unop.property (by simp)).op :=
          (Category.assoc _ _ _).symm
        _ = qL.1 (facIdx j) ≫
            U.map (SimplexCategory.Truncated.Hom.tr (facMap j)
              j.right.unop.property (by simp)).op :=
          congrArg (fun z => z ≫
            U.map (SimplexCategory.Truncated.Hom.tr (facMap j)
              j.right.unop.property (by simp)).op) (hqa (facIdx j))
    have h2 : qL.1 (facIdx j) ≫
        U.map (SimplexCategory.Truncated.Hom.tr (facMap j)
          j.right.unop.property (by simp)).op = limit.π D j := by
      change limit.π D (faceObj (facIdx j)) ≫
          U.map (SimplexCategory.Truncated.Hom.tr (facMap j)
            j.right.unop.property (by simp)).op = limit.π D j
      exact (limit.cone D).w (faceToJ j)
    exact h1.trans h2
  exact ⟨{ hom := b, inv := a, hom_inv_id := hba, inv_hom_id := hab }⟩

/-- The representability hypothesis produces the next truncated object and
the adjoint mapping property from the source's Lemma `lemma-work-out`. -/
structure NextTruncatedObjectData {C : Type u} [Category.{v} C]
    (n : ℕ) (U : SimplicialObject.Truncated C (n + 1)) (Uplus : C) where
  tildeU : SimplicialObject.Truncated C (n + 2)
  restrict_eq :
    (SimplicialObject.Truncated.trunc C (n + 2) (n + 1)).obj tildeU = U
  top_eq : tildeU.obj (op ⟨SimplexCategory.mk (n + 2), by simp⟩) = Uplus
  homEquiv : ∀ V : SimplicialObject.Truncated C (n + 2),
    (V ⟶ tildeU) ≃
      ((SimplicialObject.Truncated.trunc C (n + 2) (n + 1)).obj V ⟶ U)

private theorem has_limit_one_step_index {C : Type u} [Category.{v} C]
    (n : ℕ) (U : SimplicialObject.Truncated C (n + 1)) (Uplus : C)
    (hRep : (compatibleBoundaryFunctor n U).RepresentableBy Uplus) :
    HasLimit (StructuredArrow.proj
      (op ⟨SimplexCategory.mk (n + 2), by simp⟩)
      (SimplexCategory.Truncated.incl (n + 1) (n + 2)).op ⋙ U) := by
  classical
  let L := (SimplexCategory.Truncated.incl (n + 1) (n + 2)).op
  let I := StructuredArrow (op ⟨SimplexCategory.mk (n + 2), by simp⟩) L
  let D := StructuredArrow.proj
    (op ⟨SimplexCategory.mk (n + 2), by simp⟩) L ⋙ U
  let targetEq :
      (SimplexCategory.mk (n + 2) : SimplexCategory) =
        SimplexCategory.mk ((n + 1) + 1) := by
    congr 1
  let alpha (j : I) :
      j.right.unop.1 ⟶ SimplexCategory.mk ((n + 1) + 1) :=
    j.hom.unop.hom ≫ eqToHom targetEq
  have alpha_not_surjective (j : I) :
      ¬ Function.Surjective (alpha j).toOrderHom := by
    intro hs
    have hEpi : Epi (alpha j) := (SimplexCategory.epi_iff_surjective).2 hs
    let _ : Epi (alpha j) := hEpi
    have hlen := SimplexCategory.len_le_of_epi (alpha j)
    have hk := j.right.unop.property
    dsimp [alpha] at hlen
    omega
  let facIdx (j : I) : Fin (n + 3) :=
    Classical.choose
      (SimplexCategory.eq_comp_δ_of_not_surjective (alpha j)
        (alpha_not_surjective j))
  let facMap (j : I) : j.right.unop.1 ⟶ SimplexCategory.mk (n + 1) :=
    Classical.choose
      (Classical.choose_spec
        (SimplexCategory.eq_comp_δ_of_not_surjective (alpha j)
          (alpha_not_surjective j)))
  have facEq (j : I) :
      alpha j = facMap j ≫ SimplexCategory.δ (facIdx j) :=
    Classical.choose_spec
      (Classical.choose_spec
        (SimplexCategory.eq_comp_δ_of_not_surjective (alpha j)
          (alpha_not_surjective j)))
  let faceArrow (i : Fin (n + 3)) :
      (op ⟨SimplexCategory.mk (n + 2), by simp⟩) ⟶
        L.obj (op ⟨SimplexCategory.mk (n + 1), by simp⟩) :=
      (SimplexCategory.Truncated.Hom.tr (n := n + 2)
        (SimplexCategory.δ i ≫ eqToHom targetEq.symm)
        (by simp) (by simp)).op
  let faceObj (i : Fin (n + 3)) : I := StructuredArrow.mk (faceArrow i)
  let faceToJ (j : I) : faceObj (facIdx j) ⟶ j :=
    StructuredArrow.homMk
      (SimplexCategory.Truncated.Hom.tr (facMap j)
        j.right.unop.property (by simp)).op (by
        apply Opposite.unop_injective
        dsimp [faceObj, faceArrow, L]
        apply SimplexCategory.Truncated.Hom.ext
        convert congrArg (fun z => z.toOrderHom) (facEq j).symm using 1 <;>
          simp [alpha] <;> try { congr 1 })
  have hαf {j k : I} (f : j ⟶ k) :
      alpha k = f.right.unop.hom ≫ alpha j := by
    have hw0 := f.w
    have hw : (L.map f.right).unop.hom ≫ j.hom.unop.hom =
        k.hom.unop.hom := by
      exact congrArg (fun z => z.unop.hom) hw0
    dsimp [L] at hw
    simpa [alpha, Category.assoc] using
      (congrArg (fun z => z ≫ eqToHom targetEq) hw).symm
  have hcomp {j k : I} (f : j ⟶ k) :
      (SimplexCategory.Truncated.Hom.tr (facMap j)
        j.right.unop.property (by simp)).op ≫ f.right =
      (SimplexCategory.Truncated.Hom.tr
        (f.right.unop.hom ≫ facMap j)
        k.right.unop.property (by simp)).op := by
    apply Opposite.unop_injective
    exact (SimplexCategory.Truncated.Hom.tr_comp' (n := n + 1)
      (f := f.right.unop.hom)
      (g := SimplexCategory.Truncated.Hom.tr (facMap j)
        j.right.unop.property (by simp))
      (ha := k.right.unop.property)).symm
  let component (q : CompatibleBoundary n U Uplus) (j : I) :
      Uplus ⟶ D.obj j :=
    q.1 (facIdx j) ≫
      U.map (SimplexCategory.Truncated.Hom.tr (facMap j)
        j.right.unop.property (by simp)).op
  let boundaryCone (q : CompatibleBoundary n U Uplus) : Cone D :=
    { pt := Uplus
      π := NatTrans.mk (fun j => component q j) (by
          intro j k f
          have hfac :
              alpha k =
                (f.right.unop.hom ≫ facMap j) ≫
                  SimplexCategory.δ (facIdx j) := by
            rw [hαf f, facEq j]
            simp [Category.assoc]
          have hfactor :
              q.1 (facIdx j) ≫
                  U.map (SimplexCategory.Truncated.Hom.tr
                    (f.right.unop.hom ≫ facMap j)
                    k.right.unop.property (by simp)).op =
                q.1 (facIdx k) ≫
                  U.map (SimplexCategory.Truncated.Hom.tr (facMap k)
                    k.right.unop.property (by simp)).op := by
            by_cases heq : facIdx j = facIdx k
            · rw [← heq]
              have hmap : f.right.unop.hom ≫ facMap j = facMap k := by
                apply (cancel_mono (SimplexCategory.δ (facIdx j))).1
                calc
                  (f.right.unop.hom ≫ facMap j) ≫
                      SimplexCategory.δ (facIdx j) = alpha k := hfac.symm
                  _ = facMap k ≫ SimplexCategory.δ (facIdx j) := by
                    simpa [heq] using facEq k
              rw [hmap]
            · obtain hlt | hgt := lt_or_gt_of_ne heq
              · exact compatibleBoundary_factor_eq n U q
                    k.right.unop.property (alpha k) hlt
                    (f.right.unop.hom ≫ facMap j) (facMap k) hfac (facEq k)
              · exact (compatibleBoundary_factor_eq n U q
                    k.right.unop.property (alpha k) hgt
                    (facMap k) (f.right.unop.hom ≫ facMap j)
                    (facEq k) hfac).symm
          dsimp [component, D]
          rw [Category.id_comp]
          have hmap_comp :
              U.map (SimplexCategory.Truncated.Hom.tr
                (f.right.unop.hom ≫ facMap j)
                k.right.unop.property (by simp)).op =
                U.map (SimplexCategory.Truncated.Hom.tr (facMap j)
                  j.right.unop.property (by simp)).op ≫ U.map f.right := by
            rw [← hcomp f]
            exact U.map_comp _ _
          calc
            q.1 (facIdx k) ≫
                  U.map (SimplexCategory.Truncated.Hom.tr (facMap k)
                    k.right.unop.property (by simp)).op =
                q.1 (facIdx j) ≫
                  U.map (SimplexCategory.Truncated.Hom.tr
                    (f.right.unop.hom ≫ facMap j)
                    k.right.unop.property (by simp)).op := hfactor.symm
            _ = q.1 (facIdx j) ≫
                  (U.map (SimplexCategory.Truncated.Hom.tr (facMap j)
                    j.right.unop.property (by simp)).op ≫ U.map f.right) := by
              exact congrArg (fun z => q.1 (facIdx j) ≫ z) hmap_comp
            _ = (q.1 (facIdx j) ≫
                  U.map (SimplexCategory.Truncated.Hom.tr (facMap j)
                    j.right.unop.property (by simp)).op) ≫ U.map f.right := by
              simp only [Category.assoc]) }
  let commonMap (i j : Fin (n + 3)) (hij : i < j) :
      (faceObj j).right ⟶
        (op ⟨SimplexCategory.mk n, by simp⟩) :=
    (SimplexCategory.Truncated.δ (n + 1) ⟨i.val, by omega⟩
      (by simp) (by simp)).op
  let commonObj (i j : Fin (n + 3)) (hij : i < j) : I :=
    StructuredArrow.mk ((faceObj j).hom ≫ L.map (commonMap i j hij))
  let faceToCommonJ (i j : Fin (n + 3)) (hij : i < j) :
      faceObj j ⟶ commonObj i j hij :=
    StructuredArrow.homMk' (faceObj j) (commonMap i j hij)
  let faceToCommonI (i j : Fin (n + 3)) (hij : i < j) :
      faceObj i ⟶ commonObj i j hij :=
    StructuredArrow.homMk (f := faceObj i) (f' := commonObj i j hij)
      (SimplexCategory.Truncated.δ (n + 1) (j.pred hij.ne_zero)
        (by simp) (by simp)).op (by
        apply Opposite.unop_injective
        dsimp [faceObj, faceArrow, commonObj, commonMap, L]
        apply SimplexCategory.Truncated.Hom.ext
        simp only
        convert congrArg (fun z => z.toOrderHom)
            (SimplexCategory.δ_comp_δ' (i := ⟨i.val, by omega⟩)
              (j := j) (by simpa using hij)).symm using 1 <;>
          simp <;> try { congr 1 })
  let qU : CompatibleBoundary n U Uplus := hRep.homEquiv (𝟙 Uplus)
  let isLimit : IsLimit (boundaryCone qU) :=
    { lift := fun s =>
        let qL : (compatibleBoundaryFunctor n U).obj (op s.pt) :=
          ⟨fun i => s.π.app (faceObj i), by
            intro i j hij
            have wI := s.π.naturality (faceToCommonI i j hij)
            have wJ := s.π.naturality (faceToCommonJ i j hij)
            dsimp [D] at wI wJ
            simp only [Category.id_comp] at wI wJ
            have hI : s.π.app (faceObj i) ≫
                D.map (faceToCommonI i j hij) =
                s.π.app (commonObj i j hij) := by
              exact wI.symm
            have hJ : s.π.app (faceObj j) ≫
                D.map (faceToCommonJ i j hij) =
                s.π.app (commonObj i j hij) := by
              exact wJ.symm
            have hh := hI.trans hJ.symm
            dsimp [D, StructuredArrow.proj, Comma.snd, Comma.map,
              StructuredArrow.homMk,
              StructuredArrow.homMk', faceToCommonI, faceToCommonJ,
              commonObj, commonMap, faceObj, faceArrow, L] at hh
            convert hh using 1;
              simp [faceObj, faceArrow, truncatedFace];
              try { congr 1 }
            rfl⟩
        hRep.homEquiv.symm qL
      fac := by
        intro s j
        let qL : (compatibleBoundaryFunctor n U).obj (op s.pt) :=
          ⟨fun i => s.π.app (faceObj i), by
            intro i k hik
            have wI := s.π.naturality (faceToCommonI i k hik)
            have wJ := s.π.naturality (faceToCommonJ i k hik)
            dsimp [D] at wI wJ
            simp only [Category.id_comp] at wI wJ
            have hI : s.π.app (faceObj i) ≫
                D.map (faceToCommonI i k hik) =
                s.π.app (commonObj i k hik) := by
              exact wI.symm
            have hJ : s.π.app (faceObj k) ≫
                D.map (faceToCommonJ i k hik) =
                s.π.app (commonObj i k hik) := by
              exact wJ.symm
            have hh := hI.trans hJ.symm
            dsimp [D, StructuredArrow.proj, Comma.snd, Comma.map,
              StructuredArrow.homMk,
              StructuredArrow.homMk', faceToCommonI, faceToCommonJ,
              commonObj, commonMap, faceObj, faceArrow, L] at hh
            convert hh using 1;
              simp [faceObj, faceArrow, truncatedFace];
              try { congr 1 }
            rfl⟩
        let a := hRep.homEquiv.symm qL
        have ha : hRep.homEquiv a = qL :=
          hRep.homEquiv.apply_symm_apply qL
        have h := hRep.homEquiv_eq a
        have hi := congrArg (fun q : CompatibleBoundary n U s.pt =>
          q.1 (facIdx j)) h
        change (hRep.homEquiv a).1 (facIdx j) =
          a ≫ qU.1 (facIdx j) at hi
        rw [ha] at hi
        change hRep.homEquiv.symm qL ≫ qU.1 (facIdx j) ≫
          U.map (SimplexCategory.Truncated.Hom.tr (facMap j)
            j.right.unop.property (by simp)).op = s.π.app j
        dsimp [a] at hi
        let g := U.map (SimplexCategory.Truncated.Hom.tr (facMap j)
          j.right.unop.property (by simp)).op
        change hRep.homEquiv.symm qL ≫ qU.1 (facIdx j) ≫ g = s.π.app j
        have hg := congrArg (fun f => f ≫ g) hi
        have hn : qL.1 (facIdx j) ≫ g = s.π.app j := by
          change s.π.app (faceObj (facIdx j)) ≫ D.map (faceToJ j) = s.π.app j
          calc
            s.π.app (faceObj (facIdx j)) ≫ D.map (faceToJ j) =
                𝟙 s.pt ≫ s.π.app j := by
              simpa only [Functor.const_obj_map] using
                (s.π.naturality (faceToJ j)).symm
            _ = s.π.app j := Category.id_comp _
        simpa only [Category.assoc] using hg.symm.trans hn
      uniq := by
        intro s m hm
        let qL : (compatibleBoundaryFunctor n U).obj (op s.pt) :=
          ⟨fun i => s.π.app (faceObj i), by
            intro i k hik
            have wI := s.π.naturality (faceToCommonI i k hik)
            have wJ := s.π.naturality (faceToCommonJ i k hik)
            dsimp [D] at wI wJ
            simp only [Category.id_comp] at wI wJ
            have hI : s.π.app (faceObj i) ≫
                D.map (faceToCommonI i k hik) =
                s.π.app (commonObj i k hik) := by
              exact wI.symm
            have hJ : s.π.app (faceObj k) ≫
                D.map (faceToCommonJ i k hik) =
                s.π.app (commonObj i k hik) := by
              exact wJ.symm
            have hh := hI.trans hJ.symm
            dsimp [D, StructuredArrow.proj, Comma.snd, Comma.map,
              StructuredArrow.homMk,
              StructuredArrow.homMk', faceToCommonI, faceToCommonJ,
              commonObj, commonMap, faceObj, faceArrow, L] at hh
            convert hh using 1;
              simp [faceObj, faceArrow, truncatedFace];
              try { congr 1 }
            rfl⟩
        let a := hRep.homEquiv.symm qL
        have ha : hRep.homEquiv a = qL :=
          hRep.homEquiv.apply_symm_apply qL
        have hmface (i : Fin (n + 3)) : m ≫ qU.1 i =
            s.π.app (faceObj i) := by
          have hci := hm (faceObj i)
          have hcomponent_face : component qU (faceObj i) = qU.1 i := by
            have hface : alpha (faceObj i) =
                (𝟙 (SimplexCategory.mk (n + 1))) ≫ SimplexCategory.δ i := by
              change (faceArrow i).unop.hom = SimplexCategory.δ i
              dsimp [faceArrow, targetEq]
              rfl
            by_cases heq : facIdx (faceObj i) = i
            · have hmap : facMap (faceObj i) = 𝟙 _ := by
                apply (cancel_mono (SimplexCategory.δ i)).1
                calc
                  facMap (faceObj i) ≫ SimplexCategory.δ i =
                      alpha (faceObj i) := by simpa [heq] using (facEq (faceObj i)).symm
                  _ = (𝟙 _) ≫ SimplexCategory.δ i := hface
              dsimp [component]
              rw [heq, hmap]
              change qU.1 i ≫ U.map
                (𝟙 ((op ⟨SimplexCategory.mk (n + 1), by simp⟩) :
                  (SimplexCategory.Truncated (n + 1))ᵒᵖ)) = qU.1 i
              rw [U.map_id]
              simp
            · obtain hlt | hgt := lt_or_gt_of_ne heq
              · have hh := compatibleBoundary_factor_eq n U qU
                    (faceObj i).right.unop.property (alpha (faceObj i)) hlt
                    (facMap (faceObj i)) (𝟙 _) (facEq (faceObj i)) hface
                change qU.1 (facIdx (faceObj i)) ≫
                    U.map (SimplexCategory.Truncated.Hom.tr
                      (facMap (faceObj i))
                      (faceObj i).right.unop.property (by simp)).op = qU.1 i
                exact hh.trans (by
                  change qU.1 i ≫ U.map
                    (𝟙 ((op ⟨SimplexCategory.mk (n + 1), by simp⟩) :
                      (SimplexCategory.Truncated (n + 1))ᵒᵖ)) = qU.1 i
                  rw [U.map_id]
                  simp)
              · have hh := compatibleBoundary_factor_eq n U qU
                    (faceObj i).right.unop.property (alpha (faceObj i)) hgt
                    (𝟙 _) (facMap (faceObj i)) hface (facEq (faceObj i))
                change qU.1 (facIdx (faceObj i)) ≫
                    U.map (SimplexCategory.Truncated.Hom.tr
                      (facMap (faceObj i))
                      (faceObj i).right.unop.property (by simp)).op = qU.1 i
                exact hh.symm.trans (by
                  change qU.1 i ≫ U.map
                    (𝟙 ((op ⟨SimplexCategory.mk (n + 1), by simp⟩) :
                      (SimplexCategory.Truncated (n + 1))ᵒᵖ)) = qU.1 i
                  rw [U.map_id]
                  simp)
          dsimp [boundaryCone] at hci
          rw [hcomponent_face] at hci
          exact hci
        apply hRep.homEquiv.injective
        apply Subtype.ext
        funext i
        change (hRep.homEquiv m).1 i = (hRep.homEquiv a).1 i
        rw [hRep.homEquiv_eq m, hRep.homEquiv_eq a]
        change m ≫ qU.1 i = a ≫ qU.1 i
        rw [hmface i]
        have h := hRep.homEquiv_eq a
        have hi := congrArg (fun q : CompatibleBoundary n U s.pt => q.1 i) h
        change (hRep.homEquiv a).1 i = a ≫ qU.1 i at hi
        rw [ha] at hi
        simpa [qL] using hi }
  exact HasLimit.mk { cone := boundaryCone qU, isLimit := isLimit }

private def strictifyFunctor {B : Type u₁} [Category.{v₁} B]
    {C : Type u₂} [Category.{v₂} C] (G : B ⥤ C) (obj : B → C)
    (e : ∀ X, obj X ≅ G.obj X) : B ⥤ C where
  obj := obj
  map {X Y} f := (e X).hom ≫ G.map f ≫ (e Y).inv
  map_id := by
    intro X
    simp
  map_comp := by
    intro X Y Z f g
    simp only [Functor.map_comp, Category.assoc, Iso.inv_hom_id_assoc]

theorem work_out_next_truncated_object {C : Type u} [Category.{v} C]
    (n : ℕ) (U : SimplicialObject.Truncated C (n + 1)) (Uplus : C)
    (hRep : (compatibleBoundaryFunctor n U).RepresentableBy Uplus) :
    Nonempty (NextTruncatedObjectData n U Uplus) := by
  classical
  let L := (SimplexCategory.Truncated.incl (n + 1) (n + 2)).op
  let hTop := has_limit_one_step_index n U Uplus hRep
  let hAll : ∀ Y : (SimplexCategory.Truncated (n + 2))ᵒᵖ,
      HasLimit (StructuredArrow.proj Y L ⋙ U) := by
    intro Y
    by_cases hY : Y.unop.1.len ≤ n + 1
    · let X : (SimplexCategory.Truncated (n + 1))ᵒᵖ :=
        op ⟨Y.unop.1, hY⟩
      have e : L.obj X = Y := by
        apply Opposite.unop_injective
        apply ObjectProperty.FullSubcategory.ext
        apply SimplexCategory.ext
        rfl
      rw [← e]
      let hInitial : IsInitial (StructuredArrow.mk (𝟙 (L.obj X))) :=
        StructuredArrow.mkIdInitial
      exact HasLimit.mk
        { cone := coneOfDiagramInitial hInitial
            (StructuredArrow.proj (L.obj X) L ⋙ U)
          isLimit := limitOfDiagramInitial hInitial
            (StructuredArrow.proj (L.obj X) L ⋙ U) }
    · have hlen : Y.unop.1.len = n + 2 := by
        have hy := Y.unop.property
        omega
      have e : Y = op ⟨SimplexCategory.mk (n + 2), by simp⟩ := by
        apply Opposite.unop_injective
        apply ObjectProperty.FullSubcategory.ext
        apply SimplexCategory.ext
        simpa using hlen
      rw [e]
      exact hTop
  let hAllInst : ∀ Y : (SimplexCategory.Truncated (n + 2))ᵒᵖ,
      HasLimit (StructuredArrow.proj Y L ⋙ U) := hAll
  let G := @Functor.pointwiseRightKanExtension _ _ _ _ _ _ L U hAllInst
  let counitG := @Functor.pointwiseRightKanExtensionCounit _ _ _ _ _ _ L U hAllInst
  have hCounitIso : ∀ X : (SimplexCategory.Truncated (n + 1))ᵒᵖ,
      IsIso (counitG.app X) := by
    intro X
    change IsIso (limit.π (StructuredArrow.proj (L.obj X) L ⋙ U)
      (StructuredArrow.mk (𝟙 (L.obj X))))
    exact isIso_π_of_isInitial
      (StructuredArrow.mkIdInitial (T := L) (Y := X)) _
  let obj : (SimplexCategory.Truncated (n + 2))ᵒᵖ → C := fun Y =>
    if hY : Y.unop.1.len ≤ n + 1 then
      U.obj (op ⟨Y.unop.1, hY⟩)
    else
      Uplus
  let eObj : ∀ Y : (SimplexCategory.Truncated (n + 2))ᵒᵖ,
      obj Y ≅ G.obj Y := by
    intro Y
    by_cases hY : Y.unop.1.len ≤ n + 1
    · let X : (SimplexCategory.Truncated (n + 1))ᵒᵖ :=
        op ⟨Y.unop.1, hY⟩
      have eY : L.obj X = Y := by
        apply Opposite.unop_injective
        apply ObjectProperty.FullSubcategory.ext
        apply SimplexCategory.ext
        rfl
      have hobj : obj Y = U.obj X := by
        dsimp [obj]
        simp only [dif_pos hY]
        rfl
      letI : IsIso (counitG.app X) := hCounitIso X
      exact eqToIso hobj ≪≫ (asIso (counitG.app X)).symm ≪≫
        G.mapIso (eqToIso eY)
    · have hlen : Y.unop.1.len = n + 2 := by
        have hy := Y.unop.property
        omega
      have eY : Y = op ⟨SimplexCategory.mk (n + 2), by simp⟩ := by
        apply Opposite.unop_injective
        apply ObjectProperty.FullSubcategory.ext
        apply SimplexCategory.ext
        simpa using hlen
      have hobj : obj Y = Uplus := by
        dsimp [obj]
        simp only [dif_neg hY]
      rw [hobj, eY]
      let J := (SimplexCategory.Truncated.inclusion (n + 2)).op
      let S : (SimplexCategory.Truncated (n + 2))ᵒᵖ :=
        op ⟨SimplexCategory.mk (n + 2), by simp⟩
      let P := StructuredArrow.post S L J
      let D0 := coskeletonIndexDiagram (n + 1) (n + 2) U
      let D1 := StructuredArrow.proj S L ⋙ U
      have hRight (X : StructuredArrow S L) : (P.obj X).right = X.right := by
        rfl
      have hDobj (X : StructuredArrow S L) :
          D0.obj (P.obj X) = D1.obj X := by
        change U.obj ((P.obj X).right) = U.obj X.right
        exact congrArg U.obj (hRight X)
      let w : P ⋙ D0 ≅ D1 := NatIso.ofComponents
          (fun X => eqToIso (hDobj X)) (by
        intro X Y f
        have hX := hRight X
        have hY := hRight Y
        cases hX
        cases hY
        have hdx := hDobj X
        have hdy := hDobj Y
        cases hdx
        cases hdy
        cases X
        cases Y
        dsimp [P]
        simp only [D0, D1, coskeletonIndexDiagram, Functor.comp_map,
          StructuredArrow.proj_map, StructuredArrow.post_map]
        apply (comp_eqToHom_iff _ _ _).2
        rw [Category.assoc]
        apply (conj_eqToHom_iff_heq' _ _ _ _).2
        change U.map ((P.map f).right) ≍ U.map f.right
        dsimp [P, StructuredArrow.post]
        rfl)
      letI : HasLimit (P.asEquivalence.functor ⋙ D0) := by
        change HasLimit (P ⋙ D0)
        exact hasLimit_of_iso w.symm
      letI : HasLimit D0 :=
        hasLimit_of_equivalence_comp P.asEquivalence
      let eTop := Classical.choice (formula_limit_of_representable n U Uplus hRep)
      let eLim : limit D1 ≅ limit D0 :=
        HasLimit.isoOfEquivalence P.asEquivalence w
      have eTop' : Uplus ≅ limit (StructuredArrow.proj S L ⋙ U) :=
        eTop ≪≫ eLim.symm
      simpa [G, Functor.pointwiseRightKanExtension, S, L] using eTop'
  let F := strictifyFunctor
    (B := (SimplexCategory.Truncated (n + 2))ᵒᵖ) (C := C) G obj eObj
  let eNat : F ≅ G := NatIso.ofComponents eObj (by
    intro X Y f
    dsimp [F, strictifyFunctor]
    simp)
  have hrestrict :
      (SimplicialObject.Truncated.trunc C (n + 2) (n + 1)).obj F = U := by
    refine CategoryTheory.Functor.ext (fun X => ?_) (fun X Y f => ?_)
    · dsimp [SimplicialObject.Truncated.trunc, F, strictifyFunctor]
      have hx :
          ((SimplexCategory.Truncated.incl (n + 1) (n + 2)).obj X.unop).obj.len ≤
            n + 1 := X.unop.property
      have hX : op ⟨((SimplexCategory.Truncated.incl (n + 1) (n + 2)).obj X.unop).obj,
          hx⟩ = X := by
        apply Opposite.unop_injective
        apply ObjectProperty.FullSubcategory.ext
        rfl
      simp only [obj, dif_pos hx]
      rw [hX]
    · dsimp [SimplicialObject.Truncated.trunc, F, strictifyFunctor]
      have hx :
          X.unop.obj.len ≤ n + 1 := X.unop.property
      have hy :
          Y.unop.obj.len ≤ n + 1 := Y.unop.property
      have hLx : (L.obj X).unop.obj.len ≤ n + 1 := by
        change X.unop.obj.len ≤ n + 1
        exact hx
      have hLy : (L.obj Y).unop.obj.len ≤ n + 1 := by
        change Y.unop.obj.len ≤ n + 1
        exact hy
      have hX0 : op ⟨(L.obj X).unop.obj, hLx⟩ = X := by
        apply Opposite.unop_injective
        apply ObjectProperty.FullSubcategory.ext
        rfl
      have hY0 : op ⟨(L.obj Y).unop.obj, hLy⟩ = Y := by
        apply Opposite.unop_injective
        apply ObjectProperty.FullSubcategory.ext
        rfl
      change (eObj (L.obj X)).hom ≫ G.map (L.map f) ≫
          (eObj (L.obj Y)).inv = _
      dsimp [eObj, obj]
      simp only [dif_pos hLx, dif_pos hLy]
      simp only [Iso.trans_hom, Iso.trans_inv, Functor.mapIso_hom,
        Functor.mapIso_inv, Iso.symm_hom, Iso.symm_inv, Iso.refl_hom,
        Iso.refl_inv, eqToIso.hom, eqToIso.inv]
      simp only [asIso_hom, asIso_inv, Category.assoc]
      have hmapX :
          G.map (𝟙 (L.obj (op ⟨(L.obj X).unop.obj, hLx⟩))) ≫
              G.map (L.map f) = G.map (L.map f) := by
        rw [← G.map_comp]
        congr 1
        cases hX0
        exact Category.id_comp (L.map f)
      have hmapY :
          G.map (L.map f) ≫
              G.map (𝟙 (L.obj (op ⟨(L.obj Y).unop.obj, hLy⟩))) =
            G.map (L.map f) := by
        rw [← G.map_comp]
        congr 1
        cases hY0
        exact Category.comp_id (L.map f)
      have hcore :
          G.map (𝟙 (L.obj (op ⟨(L.obj X).unop.obj, hLx⟩))) ≫
              G.map (L.map f) ≫
                G.map (𝟙 (L.obj (op ⟨(L.obj Y).unop.obj, hLy⟩))) =
            G.map (L.map f) := by
        calc
          _ = (G.map (𝟙 (L.obj (op ⟨(L.obj X).unop.obj, hLx⟩))) ≫
              G.map (L.map f)) ≫
                G.map (𝟙 (L.obj (op ⟨(L.obj Y).unop.obj, hLy⟩))) := by
            simp only [Category.assoc]
          _ = G.map (L.map f) ≫
              G.map (𝟙 (L.obj (op ⟨(L.obj Y).unop.obj, hLy⟩))) := by
            rw [hmapX]
          _ = G.map (L.map f) := hmapY
      have hnat :
          G.map (L.map f) ≫ counitG.app (op ⟨(L.obj Y).unop.obj, hLy⟩) =
            counitG.app (op ⟨(L.obj X).unop.obj, hLx⟩) ≫ U.map f := by
        have hleft :
            G.map (L.map f) ≫ counitG.app (op ⟨(L.obj Y).unop.obj, hLy⟩) ≍
              G.map (L.map f) ≫ counitG.app Y := by
          cases hY0
          rfl
        have hright :
            counitG.app (op ⟨(L.obj X).unop.obj, hLx⟩) ≫ U.map f ≍
              counitG.app X ≫ U.map f := by
          cases hX0
          rfl
        have hn :
            G.map (L.map f) ≫ counitG.app Y =
              counitG.app X ≫ U.map f := by
          simpa only [Functor.comp_obj, Functor.comp_map, G] using
            counitG.naturality f
        exact eq_of_heq (hleft.trans ((heq_of_eq hn).trans hright.symm))
      have hcore_assoc {Z : C}
          (k : G.obj (L.obj (op ⟨(L.obj Y).unop.obj, hLy⟩)) ⟶ Z) :
          G.map (𝟙 (L.obj (op ⟨(L.obj X).unop.obj, hLx⟩))) ≫
              G.map (L.map f) ≫
                G.map (𝟙 (L.obj (op ⟨(L.obj Y).unop.obj, hLy⟩))) ≫ k =
            G.map (L.map f) ≫ k := by
        calc
          _ = (G.map (𝟙 (L.obj (op ⟨(L.obj X).unop.obj, hLx⟩))) ≫
              G.map (L.map f) ≫
                G.map (𝟙 (L.obj (op ⟨(L.obj Y).unop.obj, hLy⟩)))) ≫ k := by
            simp only [Category.assoc]
          _ = G.map (L.map f) ≫ k := by rw [hcore]
      have hnat_assoc {Z : C}
          (k : U.obj (op ⟨(L.obj Y).unop.obj, hLy⟩) ⟶ Z) :
          G.map (L.map f) ≫ counitG.app (op ⟨(L.obj Y).unop.obj, hLy⟩) ≫ k =
            counitG.app (op ⟨(L.obj X).unop.obj, hLx⟩) ≫ U.map f ≫ k := by
        calc
          _ = (G.map (L.map f) ≫
              counitG.app (op ⟨(L.obj Y).unop.obj, hLy⟩)) ≫ k := by
            simp only [Category.assoc]
          _ = (counitG.app (op ⟨(L.obj X).unop.obj, hLx⟩) ≫ U.map f) ≫ k := by
            rw [hnat]
          _ = _ := by simp only [Category.assoc]
      rw [hcore_assoc]
      rw [hnat_assoc]
      have hIso : IsIso (counitG.app (op ⟨(L.obj X).unop.obj, hLx⟩)) :=
        hCounitIso _
      simpa only [Category.assoc] using
        congrArg
          (fun k => eqToHom _ ≫ k)
          (@IsIso.inv_hom_id_assoc _ _ _ _
            (counitG.app (op ⟨(L.obj X).unop.obj, hLx⟩)) hIso _
            (U.map f ≫ eqToHom _))
  have htop : F.obj (op ⟨SimplexCategory.mk (n + 2), by simp⟩) = Uplus := by
    dsimp [F, strictifyFunctor, obj]
    simp
  have hG : G.IsRightKanExtension counitG := by
    dsimp [G, counitG]
    infer_instance
  let alpha := Functor.whiskerLeft L eNat.hom ≫ counitG
  have hF : F.IsRightKanExtension alpha := by
    exact @Functor.isRightKanExtension_of_iso _ _ _ _ _ _ G F eNat.symm L U
      counitG alpha (by
      dsimp [alpha]
      rw [← Functor.whiskerLeft_comp_assoc, eNat.inv_hom_id,
        Functor.whiskerLeft_id', Category.id_comp]) hG
  refine ⟨{ tildeU := F, restrict_eq := hrestrict, top_eq := htop, homEquiv := ?_ }⟩
  intro V
  simpa [SimplicialObject.Truncated.trunc] using
    (@Functor.homEquivOfIsRightKanExtension _ _ _ _ _ _ F L U alpha hF V)

/-! ## Explicit maps in the one-step extension -/

def extensionFace {C : Type u} [Category.{v} C] (n : ℕ)
    (U : SimplicialObject.Truncated C (n + 1)) (i : Fin (n + 2)) :
    U.obj (op ⟨SimplexCategory.mk (n + 1), by simp⟩) ⟶
      U.obj (op ⟨SimplexCategory.mk n, by simp⟩) :=
  truncatedFace n U i

def extensionDegeneracy {C : Type u} [Category.{v} C] (n : ℕ)
    (U : SimplicialObject.Truncated C (n + 1)) (j : Fin (n + 1)) :
    U.obj (op ⟨SimplexCategory.mk n, by simp⟩) ⟶
      U.obj (op ⟨SimplexCategory.mk (n + 1), by simp⟩) :=
  U.map (SimplexCategory.Truncated.σ (n + 1) j (by simp) (by simp)).op

/-- The tuple of components in the source's displayed degeneracy formula. -/
def degeneracyTuple {C : Type u} [Category.{v} C] (n : ℕ)
    (U : SimplicialObject.Truncated C (n + 1)) (j : Fin (n + 2)) :
    Fin (n + 3) →
      (U.obj (op ⟨SimplexCategory.mk (n + 1), by simp⟩) ⟶
        U.obj (op ⟨SimplexCategory.mk (n + 1), by simp⟩)) :=
  fun i =>
    if hi : i.val < j.val then
      extensionFace n U ⟨i.val, by omega⟩ ≫
        extensionDegeneracy n U ⟨j.val - 1, by omega⟩
    else if hij : i.val = j.val ∨ i.val = j.val + 1 then
      𝟙 _
    else
      extensionFace n U ⟨i.val - 1, by omega⟩ ≫
        extensionDegeneracy n U ⟨j.val, by omega⟩

private theorem simplex_delta_sigma_self_of_val_eq {n : ℕ}
    {a : Fin (n + 2)} {b : Fin (n + 1)} (h : a.val = b.val) :
    SimplexCategory.δ a ≫ SimplexCategory.σ b = 𝟙 _ := by
  have h' := SimplexCategory.δ_comp_σ_self (n := n) (i := b)
  rw [show a = b.castSucc by
    apply Fin.ext
    simpa using h]
  exact h'

private theorem simplex_delta_sigma_succ_of_val_eq {n : ℕ}
    {a : Fin (n + 2)} {b : Fin (n + 1)} (h : a.val = b.val + 1) :
    SimplexCategory.δ a ≫ SimplexCategory.σ b = 𝟙 _ := by
  have h' := SimplexCategory.δ_comp_σ_succ (n := n) (i := b)
  rw [show a = b.succ by
    apply Fin.ext
    simpa using h]
  exact h'

theorem degeneracyTuple_is_compatible {C : Type u} [Category.{v} C]
    (n : ℕ) (U : SimplicialObject.Truncated C (n + 1)) (j : Fin (n + 2)) :
    ∀ (i k : Fin (n + 3)) (hik : i < k),
      degeneracyTuple n U j i ≫ truncatedFace n U ⟨k.val - 1, by omega⟩ =
        degeneracyTuple n U j k ≫ truncatedFace n U ⟨i.val, by omega⟩ := by
  intro i k hik
  by_cases hi : i.val < j.val
  · by_cases hk : k.val < j.val
    · simp [degeneracyTuple, hi, hk, extensionFace, extensionDegeneracy, truncatedFace]
      repeat' rw [← U.map_comp]
      congr 1
      apply Opposite.unop_injective
      apply ObjectProperty.hom_ext
      change (SimplexCategory.δ _ ≫ SimplexCategory.σ _ ≫ SimplexCategory.δ _) =
        (SimplexCategory.δ _ ≫ SimplexCategory.σ _ ≫ SimplexCategory.δ _)
      cases n with
      | zero => omega
      | succ n =>
        let a : Fin (n + 2) := ⟨k.val - 1, by omega⟩
        let b : Fin (n + 1) := ⟨j.val - 2, by omega⟩
        let c : Fin (n + 2) := ⟨i.val, by omega⟩
        let d : Fin (n + 2) := ⟨k.val, by omega⟩
        have ha : (⟨k.val - 1, by omega⟩ : Fin (n + 3)) = a.castSucc := by
          apply Fin.ext
          rfl
        have hb : (⟨j.val - 1, by omega⟩ : Fin (n + 2)) = b.succ := by
          apply Fin.ext
          change j.val - 1 = (j.val - 2) + 1
          omega
        have hc : (⟨i.val, by omega⟩ : Fin (n + 3)) = c.castSucc := by
          apply Fin.ext
          rfl
        have hd : (⟨k.val, by omega⟩ : Fin (n + 3)) = d.castSucc := by
          apply Fin.ext
          rfl
        rw [ha, hb, hc, hd]
        have hleA : a ≤ b.castSucc := by
          simp only [Fin.le_iff_val_le_val]
          change a.val ≤ b.val
          dsimp [a, b]
          omega
        have hleC : c ≤ b.castSucc := by
          simp only [Fin.le_iff_val_le_val]
          change c.val ≤ b.val
          dsimp [b, c]
          omega
        have hleD : c ≤ a := by
          simp only [Fin.le_iff_val_le_val]
          dsimp [a, c]
          omega
        have hd' : d.castSucc = a.succ := by
          apply Fin.ext
          change k.val = (k.val - 1) + 1
          omega
        have h1 := SimplexCategory.δ_comp_σ_of_le (n := n) (i := a) (j := b) hleA
        have h2 := SimplexCategory.δ_comp_σ_of_le (n := n) (i := c) (j := b) hleC
        have h3 := SimplexCategory.δ_comp_δ (n := n) (i := c) (j := a) hleD
        rw [← Category.assoc]
        rw [← Category.assoc]
        rw [hd', h1, h2]
        simp only [Category.assoc]
        rw [← h3]
    · by_cases hkj0 : k.val = j.val
      · simp [degeneracyTuple, hi, hkj0, extensionFace, extensionDegeneracy, truncatedFace]
        repeat' rw [← U.map_comp]
        congr 1
        apply Opposite.unop_injective
        apply ObjectProperty.hom_ext
        change (SimplexCategory.δ _ ≫ SimplexCategory.σ _ ≫ SimplexCategory.δ _) = SimplexCategory.δ _
        have hunit :
            SimplexCategory.δ (⟨j.val - 1, by omega⟩ : Fin (n + 2)) ≫
                SimplexCategory.σ (⟨j.val - 1, by omega⟩ : Fin (n + 1)) = 𝟙 _ := by
          apply simplex_delta_sigma_self_of_val_eq
          rfl
        simpa only [Category.assoc, Category.id_comp] using
          congrArg (fun f => f ≫ SimplexCategory.δ (⟨i.val, by omega⟩ : Fin (n + 2))) hunit
      · by_cases hkj1 : k.val = j.val + 1
        · simp [degeneracyTuple, hi, hkj1, extensionFace, extensionDegeneracy, truncatedFace]
          repeat' rw [← U.map_comp]
          congr 1
          apply Opposite.unop_injective
          apply ObjectProperty.hom_ext
          change (SimplexCategory.δ _ ≫ SimplexCategory.σ _ ≫ SimplexCategory.δ _) = SimplexCategory.δ _
          have hunit :
              SimplexCategory.δ (⟨j.val, by omega⟩ : Fin (n + 2)) ≫
                  SimplexCategory.σ (⟨j.val - 1, by omega⟩ : Fin (n + 1)) = 𝟙 _ := by
            apply simplex_delta_sigma_succ_of_val_eq
            change j.val = (j.val - 1) + 1
            omega
          simpa only [Category.assoc, Category.id_comp] using
            congrArg (fun f => f ≫ SimplexCategory.δ (⟨i.val, by omega⟩ : Fin (n + 2))) hunit
        · have hkj : j.val + 1 < k.val := by omega
          simp [degeneracyTuple, hi, hk, hkj0, hkj1, extensionFace, extensionDegeneracy, truncatedFace]
          repeat' rw [← U.map_comp]
          congr 1
          apply Opposite.unop_injective
          apply ObjectProperty.hom_ext
          change (SimplexCategory.δ _ ≫ SimplexCategory.σ _ ≫ SimplexCategory.δ _) =
            (SimplexCategory.δ _ ≫ SimplexCategory.σ _ ≫ SimplexCategory.δ _)
          cases n with
          | zero => omega
          | succ n =>
            let a : Fin (n + 2) := ⟨k.val - 2, by omega⟩
            let b : Fin (n + 1) := ⟨j.val - 1, by omega⟩
            let c : Fin (n + 2) := ⟨i.val, by omega⟩
            have ha : (⟨k.val - 1, by omega⟩ : Fin (n + 3)) = a.succ := by
              apply Fin.ext
              change k.val - 1 = (k.val - 2) + 1
              omega
            have hb : (⟨j.val - 1, by omega⟩ : Fin (n + 2)) = b.castSucc := by
              apply Fin.ext
              rfl
            have hc : (⟨i.val, by omega⟩ : Fin (n + 3)) = c.castSucc := by
              apply Fin.ext
              rfl
            have hj : (⟨j.val, by omega⟩ : Fin (n + 2)) = b.succ := by
              apply Fin.ext
              change j.val = (j.val - 1) + 1
              omega
            rw [ha, hb, hc, hj]
            have hgt : b.castSucc < a := by
              simp only [Fin.lt_def]
              change b.val < a.val
              dsimp [a, b]
              omega
            have hle : c ≤ b.castSucc := by
              simp only [Fin.le_iff_val_le_val]
              change c.val ≤ b.val
              dsimp [b, c]
              omega
            have h3le : c ≤ a := by
              simp only [Fin.le_iff_val_le_val]
              dsimp [a, c]
              omega
            have hgt' := SimplexCategory.δ_comp_σ_of_gt (n := n) (i := a) (j := b) hgt
            have hle' := SimplexCategory.δ_comp_σ_of_le (n := n) (i := c) (j := b) hle
            have h3 := SimplexCategory.δ_comp_δ (n := n) (i := c) (j := a) h3le
            rw [← Category.assoc]
            rw [← Category.assoc]
            rw [hgt', hle']
            simp only [Category.assoc]
            rw [← h3]
  · by_cases hij0 : i.val = j.val
    · have hkj0 : k.val ≠ j.val := by omega
      by_cases hkj1 : k.val = j.val + 1
      · simp [degeneracyTuple, hij0, hkj1]
      · have hkj : j.val + 1 < k.val := by omega
        have hk : ¬ k.val < j.val := by omega
        simp [degeneracyTuple, hij0, hk, hkj0, hkj1, extensionFace, extensionDegeneracy,
          truncatedFace]
        repeat' rw [← U.map_comp]
        congr 1
        have hunit :
            SimplexCategory.Truncated.δ (n + 1) j (by simp) (by simp) ≫
                SimplexCategory.Truncated.σ (n + 1)
                  (⟨j.val, by omega⟩ : Fin (n + 1)) (by simp) (by simp) = 𝟙 _ := by
          apply ObjectProperty.hom_ext
          exact simplex_delta_sigma_self_of_val_eq (h := rfl)
        rw [← CategoryTheory.op_comp, hunit]
        simp
    · by_cases hij1 : i.val = j.val + 1
      · have hkj0 : k.val ≠ j.val := by omega
        have hkj1 : k.val ≠ j.val + 1 := by omega
        have hk : ¬ k.val < j.val := by omega
        have hki : i.val < k.val := hik
        have hklt : k.val < n + 3 := k.isLt
        have hjlt : j.val < n + 2 := j.isLt
        simp [degeneracyTuple, hij1, hkj0, hkj1, hk, extensionFace, extensionDegeneracy,
          truncatedFace]
        repeat' rw [← U.map_comp]
        congr 1
        have hunit :
            SimplexCategory.Truncated.δ (n + 1)
                (⟨j.val + 1, by omega⟩ : Fin (n + 2)) (by simp) (by simp) ≫
                SimplexCategory.Truncated.σ (n + 1)
                  (⟨j.val, by omega⟩ : Fin (n + 1)) (by simp) (by simp) = 𝟙 _ := by
          apply ObjectProperty.hom_ext
          exact simplex_delta_sigma_succ_of_val_eq (h := by rfl)
        rw [← CategoryTheory.op_comp, hunit]
        simp
      · have hij : j.val + 1 < i.val := by omega
        have hkj0 : k.val ≠ j.val := by omega
        have hkj1 : k.val ≠ j.val + 1 := by omega
        have hki : i.val < k.val := hik
        have hk : ¬ k.val < j.val := by omega
        simp [degeneracyTuple, hi, hij0, hij1, hkj0, hkj1, hk, extensionFace,
          extensionDegeneracy, truncatedFace]
        repeat' rw [← U.map_comp]
        congr 1
        apply Opposite.unop_injective
        apply ObjectProperty.hom_ext
        change (SimplexCategory.δ _ ≫ SimplexCategory.σ _ ≫ SimplexCategory.δ _) =
          (SimplexCategory.δ _ ≫ SimplexCategory.σ _ ≫ SimplexCategory.δ _)
        cases n with
        | zero => omega
        | succ n =>
          let a : Fin (n + 2) := ⟨k.val - 2, by omega⟩
          let b : Fin (n + 1) := ⟨j.val, by omega⟩
          let c : Fin (n + 2) := ⟨i.val - 1, by omega⟩
          have ha : (⟨k.val - 1, by omega⟩ : Fin (n + 3)) = a.succ := by
            apply Fin.ext
            change k.val - 1 = (k.val - 2) + 1
            omega
          have hb : (⟨j.val, by omega⟩ : Fin (n + 2)) = b.castSucc := by
            apply Fin.ext
            rfl
          have hc : (⟨i.val - 1, by omega⟩ : Fin (n + 3)) = c.castSucc := by
            apply Fin.ext
            rfl
          have hi' : (⟨i.val, by omega⟩ : Fin (n + 3)) = c.succ := by
            apply Fin.ext
            change i.val = (i.val - 1) + 1
            omega
          rw [ha, hb, hc, hi']
          have hgtA : b.castSucc < a := by
            simp only [Fin.lt_def]
            change b.val < a.val
            dsimp [a, b]
            omega
          have hgtC : b.castSucc < c := by
            simp only [Fin.lt_def]
            change b.val < c.val
            dsimp [b, c]
            omega
          have h3le : c ≤ a := by
            simp only [Fin.le_iff_val_le_val]
            dsimp [a, c]
            omega
          have h1 := SimplexCategory.δ_comp_σ_of_gt (n := n) (i := a) (j := b) hgtA
          have h2 := SimplexCategory.δ_comp_σ_of_gt (n := n) (i := c) (j := b) hgtC
          have h3 := SimplexCategory.δ_comp_δ (n := n) (i := c) (j := a) h3le
          rw [← Category.assoc]
          rw [← Category.assoc]
          rw [h1, h2]
          simp only [Category.assoc]
          rw [← h3]

noncomputable def representedDegeneracy {C : Type u} [Category.{v} C]
    (n : ℕ) (U : SimplicialObject.Truncated C (n + 1)) (Uplus : C)
    (hRep : (compatibleBoundaryFunctor n U).RepresentableBy Uplus)
    (j : Fin (n + 2)) :
    U.obj (op ⟨SimplexCategory.mk (n + 1), by simp⟩) ⟶ Uplus :=
  hRep.homEquiv.symm
    ⟨degeneracyTuple n U j, degeneracyTuple_is_compatible n U j⟩

/-- The universal compatible boundary supplied by a representing object. -/
noncomputable def representedBoundary {C : Type u} [Category.{v} C]
    (n : ℕ) (U : SimplicialObject.Truncated C (n + 1)) (Uplus : C)
    (hRep : (compatibleBoundaryFunctor n U).RepresentableBy Uplus) :
    CompatibleBoundary n U Uplus :=
  hRep.homEquiv (𝟙 Uplus)

/-- The new face maps are the coordinates of the universal boundary.

The indexing is shifted by one relative to the source: `Uplus` is the new
top degree of the extension of `U`. -/
noncomputable def representedFace {C : Type u} [Category.{v} C]
    (n : ℕ) (U : SimplicialObject.Truncated C (n + 1)) (Uplus : C)
    (hRep : (compatibleBoundaryFunctor n U).RepresentableBy Uplus)
    (i : Fin (n + 3)) :
    Uplus ⟶ U.obj (op ⟨SimplexCategory.mk (n + 1), by simp⟩) :=
  (representedBoundary n U Uplus hRep).1 i

theorem extension_face_is_coordinate_projection {C : Type u} [Category.{v} C]
    (n : ℕ) (U : SimplicialObject.Truncated C (n + 1)) (Uplus : C)
    (hRep : (compatibleBoundaryFunctor n U).RepresentableBy Uplus)
    {T : C} (f : T ⟶ Uplus) (i : Fin (n + 3)) :
    (hRep.homEquiv f).1 i =
      ((compatibleBoundaryFunctor n U).map f.op
        (representedBoundary n U Uplus hRep)).1 i := by
  exact congrArg (fun q : CompatibleBoundary n U T => q.1 i)
    (hRep.homEquiv_eq f)

/-! The source lists the first cases of `degeneracyTuple`; the following
declarations record the actual component formulas. -/
def zeroDegeneracyTuple {C : Type u} [Category.{v} C]
    (U : SimplicialObject.Truncated C 0) {T : C}
    (f : T ⟶ U.obj (op ⟨SimplexCategory.mk 0, by simp⟩)) :
    Fin 2 → (T ⟶ U.obj (op ⟨SimplexCategory.mk 0, by simp⟩)) :=
  fun _ => f

theorem zero_degeneracy_tuple_formula {C : Type u} [Category.{v} C]
    (U : SimplicialObject.Truncated C 0) {T : C}
    (f : T ⟶ U.obj (op ⟨SimplexCategory.mk 0, by simp⟩)) :
    zeroDegeneracyTuple U f = fun _ => f := by
  rfl

theorem degeneracy_tuple_degree_one_first {C : Type u} [Category.{v} C]
    (U : SimplicialObject.Truncated C 1) :
    degeneracyTuple 0 U (0 : Fin 2) 0 = 𝟙 _ ∧
      degeneracyTuple 0 U (0 : Fin 2) 1 = 𝟙 _ ∧
      degeneracyTuple 0 U (0 : Fin 2) 2 =
        extensionFace 0 U (1 : Fin 2) ≫ extensionDegeneracy 0 U (0 : Fin 1) := by
  simp [degeneracyTuple, extensionFace, extensionDegeneracy, truncatedFace]

theorem degeneracy_tuple_degree_one_second {C : Type u} [Category.{v} C]
    (U : SimplicialObject.Truncated C 1) :
    degeneracyTuple 0 U (1 : Fin 2) 0 =
        extensionFace 0 U (0 : Fin 2) ≫ extensionDegeneracy 0 U (0 : Fin 1) ∧
      degeneracyTuple 0 U (1 : Fin 2) 1 = 𝟙 _ ∧
      degeneracyTuple 0 U (1 : Fin 2) 2 = 𝟙 _ := by
  simp [degeneracyTuple, extensionFace, extensionDegeneracy, truncatedFace]

theorem degeneracy_tuple_degree_two_first {C : Type u} [Category.{v} C]
    (U : SimplicialObject.Truncated C 2) :
    degeneracyTuple 1 U (0 : Fin 3) 0 = 𝟙 _ ∧
      degeneracyTuple 1 U (0 : Fin 3) 1 = 𝟙 _ ∧
      degeneracyTuple 1 U (0 : Fin 3) 2 =
        extensionFace 1 U (1 : Fin 3) ≫ extensionDegeneracy 1 U (0 : Fin 2) ∧
      degeneracyTuple 1 U (0 : Fin 3) 3 =
        extensionFace 1 U (2 : Fin 3) ≫ extensionDegeneracy 1 U (0 : Fin 2) := by
  simp [degeneracyTuple, extensionFace, extensionDegeneracy, truncatedFace]

theorem degeneracy_tuple_degree_two_second {C : Type u} [Category.{v} C]
    (U : SimplicialObject.Truncated C 2) :
    degeneracyTuple 1 U (1 : Fin 3) 0 =
        extensionFace 1 U (0 : Fin 3) ≫ extensionDegeneracy 1 U (0 : Fin 2) ∧
      degeneracyTuple 1 U (1 : Fin 3) 1 = 𝟙 _ ∧
      degeneracyTuple 1 U (1 : Fin 3) 2 = 𝟙 _ ∧
      degeneracyTuple 1 U (1 : Fin 3) 3 =
        extensionFace 1 U (2 : Fin 3) ≫ extensionDegeneracy 1 U (1 : Fin 2) := by
  simp [degeneracyTuple, extensionFace, extensionDegeneracy, truncatedFace]

theorem degeneracy_tuple_degree_two_third {C : Type u} [Category.{v} C]
    (U : SimplicialObject.Truncated C 2) :
    degeneracyTuple 1 U (2 : Fin 3) 0 =
        extensionFace 1 U (0 : Fin 3) ≫ extensionDegeneracy 1 U (1 : Fin 2) ∧
      degeneracyTuple 1 U (2 : Fin 3) 1 =
        extensionFace 1 U (1 : Fin 3) ≫ extensionDegeneracy 1 U (1 : Fin 2) ∧
      degeneracyTuple 1 U (2 : Fin 3) 2 = 𝟙 _ ∧
      degeneracyTuple 1 U (2 : Fin 3) 3 = 𝟙 _ := by
  simp [degeneracyTuple, extensionFace, extensionDegeneracy, truncatedFace]

/-! ## Inductive construction -/

structure InductiveCoskeletonTower {C : Type u} [Category.{v} C]
    (m : ℕ) (U : SimplicialObject.Truncated C m) where
  level : ∀ k : ℕ, SimplicialObject.Truncated C (m + k)
  base : level 0 = U
  next_restrict : ∀ k : ℕ,
    (SimplicialObject.Truncated.trunc C (m + k + 1) (m + k)).obj
        (level (k + 1)) = level k
  mapping_property : ∀ k : ℕ, ∀ V : SimplicialObject.Truncated C (m + k),
    (V ⟶ level k) ≃
      ((SimplicialObject.Truncated.trunc C (m + k) m).obj V ⟶ U)

noncomputable def inductiveCoskeletonLevel {C : Type u} [Category.{v} C]
    {m : ℕ} {U : SimplicialObject.Truncated C m}
    (T : InductiveCoskeletonTower m U) (k : ℕ) : C :=
  (T.level k).obj (op ⟨SimplexCategory.mk (m + k), by simp⟩)

noncomputable def inductiveCoskeletonComponent {C : Type u} [Category.{v} C]
    {m : ℕ} {U : SimplicialObject.Truncated C m}
    (T : InductiveCoskeletonTower m U) (r k : ℕ) (h : r ≤ k) : C :=
    (T.level k).obj
    (op ⟨SimplexCategory.mk (m + r), by exact Nat.add_le_add_left h m⟩)

private structure FiniteOneStepData {C : Type u} [Category.{v} C]
    (n : ℕ) (U : SimplicialObject.Truncated C n) where
  next : SimplicialObject.Truncated C (n + 1)
  restrict_eq :
    (SimplicialObject.Truncated.trunc C (n + 1) n).obj next = U
  homEquiv : ∀ V : SimplicialObject.Truncated C (n + 1),
    (V ⟶ next) ≃
      ((SimplicialObject.Truncated.trunc C (n + 1) n).obj V ⟶ U)

private theorem finite_one_step_index_limit {C : Type u} [Category.{v} C]
    [HasFiniteLimits C] (n : ℕ) (U : SimplicialObject.Truncated C n) :
    HasLimit (StructuredArrow.proj
      (op ⟨SimplexCategory.mk (n + 1), by simp⟩)
      (SimplexCategory.Truncated.incl n (n + 1)).op ⋙ U) := by
  classical
  let S : (SimplexCategory.Truncated (n + 1))ᵒᵖ :=
    op ⟨SimplexCategory.mk (n + 1), by simp⟩
  let L := (SimplexCategory.Truncated.incl n (n + 1)).op
  let D := StructuredArrow.proj S L ⋙ U
  let : Finite (SimplexCategory.Truncated n) :=
    Finite.of_injective
      (fun x => ⟨x.1.len, Nat.lt_succ_of_le x.2⟩ :
        SimplexCategory.Truncated n → Fin (n + 1))
      (by
        intro x y h
        cases x with
        | mk x hx =>
          cases y with
          | mk y hy =>
            congr
            exact SimplexCategory.ext (Fin.ext_iff.mp h))
  let : Fintype (SimplexCategory.Truncated n) := Fintype.ofFinite _
  let : Fintype ((SimplexCategory.Truncated n)ᵒᵖ) :=
    Fintype.ofEquiv _ equivToOpposite
  let : ∀ T : (SimplexCategory.Truncated n)ᵒᵖ,
      Finite (S ⟶ L.obj T) := fun T =>
    Finite.of_injective (fun f => f.unop.hom.toOrderHom.toFun)
      (by
        intro f g h
        apply Opposite.unop_injective
        apply InducedCategory.hom_ext
        apply SimplexCategory.Hom.ext
        exact DFunLike.ext _ _ (fun i => congrFun h i))
  let : ∀ T : (SimplexCategory.Truncated n)ᵒᵖ,
      Fintype (S ⟶ L.obj T) := fun T => Fintype.ofFinite _
  let : Fintype (StructuredArrow S L) :=
    Fintype.ofInjective
      (fun j : StructuredArrow S L =>
        (⟨j.right, j.hom⟩ : Σ T, S ⟶ L.obj T))
      (by
        rintro ⟨⟨⟩, jr, jh⟩ ⟨⟨⟩, kr, kh⟩ h
        cases h
        rfl)
  let : ∀ j k : StructuredArrow S L, Finite (j ⟶ k) :=
    fun j k =>
      Finite.of_injective (fun f => f.right.unop.hom.toOrderHom.toFun)
        (by
          intro f g h
          apply Comma.hom_ext f g
          · exact Subsingleton.elim _ _
          · apply Opposite.unop_injective
            apply SimplexCategory.Truncated.Hom.ext
            exact DFunLike.ext _ _ (fun i => congrFun h i))
  let : FinCategory (StructuredArrow S L) :=
    { fintypeObj := inferInstance
      fintypeHom := fun j k => Fintype.ofFinite _ }
  change HasLimit D
  infer_instance

private theorem exists_finite_one_step {C : Type u} [Category.{v} C]
    [HasFiniteLimits C] (n : ℕ) (U : SimplicialObject.Truncated C n) :
    Nonempty (FiniteOneStepData n U) := by
  classical
  let S : (SimplexCategory.Truncated (n + 1))ᵒᵖ :=
    op ⟨SimplexCategory.mk (n + 1), by simp⟩
  let L := (SimplexCategory.Truncated.incl n (n + 1)).op
  let D := StructuredArrow.proj S L ⋙ U
  let hTop : HasLimit D := by
    dsimp [D, S, L]
    exact finite_one_step_index_limit n U
  let hAll : ∀ Y : (SimplexCategory.Truncated (n + 1))ᵒᵖ,
      HasLimit (StructuredArrow.proj Y L ⋙ U) := by
    intro Y
    by_cases hY : Y.unop.1.len ≤ n
    · let X : (SimplexCategory.Truncated n)ᵒᵖ :=
        op ⟨Y.unop.1, hY⟩
      have e : L.obj X = Y := by
        apply Opposite.unop_injective
        apply ObjectProperty.FullSubcategory.ext
        apply SimplexCategory.ext
        rfl
      rw [← e]
      let hInitial : IsInitial (StructuredArrow.mk (𝟙 (L.obj X))) :=
        StructuredArrow.mkIdInitial
      exact HasLimit.mk
        { cone := coneOfDiagramInitial hInitial
            (StructuredArrow.proj (L.obj X) L ⋙ U)
          isLimit := limitOfDiagramInitial hInitial
            (StructuredArrow.proj (L.obj X) L ⋙ U) }
    · have hlen : Y.unop.1.len = n + 1 := by
        have hy := Y.unop.property
        omega
      have e : Y = S := by
        apply Opposite.unop_injective
        apply ObjectProperty.FullSubcategory.ext
        apply SimplexCategory.ext
        simpa [S] using hlen
      rw [e]
      exact hTop
  let hAllInst : ∀ Y : (SimplexCategory.Truncated (n + 1))ᵒᵖ,
      HasLimit (StructuredArrow.proj Y L ⋙ U) := hAll
  let G := @Functor.pointwiseRightKanExtension _ _ _ _ _ _ L U hAllInst
  let counitG := @Functor.pointwiseRightKanExtensionCounit _ _ _ _ _ _ L U hAllInst
  have hCounitIso : ∀ X : (SimplexCategory.Truncated n)ᵒᵖ,
      IsIso (counitG.app X) := by
    intro X
    change IsIso (limit.π (StructuredArrow.proj (L.obj X) L ⋙ U)
      (StructuredArrow.mk (𝟙 (L.obj X))))
    exact isIso_π_of_isInitial
      (StructuredArrow.mkIdInitial (T := L) (Y := X)) _
  let obj : (SimplexCategory.Truncated (n + 1))ᵒᵖ → C := fun Y =>
    if hY : Y.unop.1.len ≤ n then
      U.obj (op ⟨Y.unop.1, hY⟩)
    else
      limit D
  let eObj : ∀ Y : (SimplexCategory.Truncated (n + 1))ᵒᵖ,
      obj Y ≅ G.obj Y := by
    intro Y
    by_cases hY : Y.unop.1.len ≤ n
    · let X : (SimplexCategory.Truncated n)ᵒᵖ :=
        op ⟨Y.unop.1, hY⟩
      have eY : L.obj X = Y := by
        apply Opposite.unop_injective
        apply ObjectProperty.FullSubcategory.ext
        apply SimplexCategory.ext
        rfl
      have hobj : obj Y = U.obj X := by
        dsimp [obj]
        simp only [dif_pos hY]
        rfl
      letI : IsIso (counitG.app X) := hCounitIso X
      exact eqToIso hobj ≪≫ (asIso (counitG.app X)).symm ≪≫
        G.mapIso (eqToIso eY)
    · have hlen : Y.unop.1.len = n + 1 := by
        have hy := Y.unop.property
        omega
      have eY : Y = S := by
        apply Opposite.unop_injective
        apply ObjectProperty.FullSubcategory.ext
        apply SimplexCategory.ext
        simpa [S] using hlen
      have hobj : obj Y = limit D := by
        dsimp [obj]
        simp only [dif_neg hY]
      rw [hobj, eY]
      exact Iso.refl _
  let F := strictifyFunctor
    (B := (SimplexCategory.Truncated (n + 1))ᵒᵖ) (C := C) G obj eObj
  let eNat : F ≅ G := NatIso.ofComponents eObj (by
    intro X Y f
    dsimp [F, strictifyFunctor]
    simp)
  have hrestrict :
      (SimplicialObject.Truncated.trunc C (n + 1) n).obj F = U := by
    refine CategoryTheory.Functor.ext (fun X => ?_) (fun X Y f => ?_)
    · dsimp [SimplicialObject.Truncated.trunc, F, strictifyFunctor]
      have hx :
          ((SimplexCategory.Truncated.incl n (n + 1)).obj X.unop).obj.len ≤ n :=
        X.unop.property
      have hX : op ⟨((SimplexCategory.Truncated.incl n (n + 1)).obj X.unop).obj,
          hx⟩ = X := by
        apply Opposite.unop_injective
        apply ObjectProperty.FullSubcategory.ext
        rfl
      simp only [obj, dif_pos hx]
      rw [hX]
    · dsimp [SimplicialObject.Truncated.trunc, F, strictifyFunctor]
      have hx : X.unop.obj.len ≤ n := X.unop.property
      have hy : Y.unop.obj.len ≤ n := Y.unop.property
      have hLx : (L.obj X).unop.obj.len ≤ n := by
        change X.unop.obj.len ≤ n
        exact hx
      have hLy : (L.obj Y).unop.obj.len ≤ n := by
        change Y.unop.obj.len ≤ n
        exact hy
      have hX0 : op ⟨(L.obj X).unop.obj, hLx⟩ = X := by
        apply Opposite.unop_injective
        apply ObjectProperty.FullSubcategory.ext
        rfl
      have hY0 : op ⟨(L.obj Y).unop.obj, hLy⟩ = Y := by
        apply Opposite.unop_injective
        apply ObjectProperty.FullSubcategory.ext
        rfl
      change (eObj (L.obj X)).hom ≫ G.map (L.map f) ≫
          (eObj (L.obj Y)).inv = _
      dsimp [eObj, obj]
      simp only [dif_pos hLx, dif_pos hLy]
      simp only [Iso.trans_hom, Iso.trans_inv, Functor.mapIso_hom,
        Functor.mapIso_inv, Iso.symm_hom, Iso.symm_inv, Iso.refl_hom,
        Iso.refl_inv, eqToIso.hom, eqToIso.inv]
      simp only [asIso_hom, asIso_inv, Category.assoc]
      have hmapX :
          G.map (𝟙 (L.obj (op ⟨(L.obj X).unop.obj, hLx⟩))) ≫
              G.map (L.map f) = G.map (L.map f) := by
        rw [← G.map_comp]
        congr 1
        cases hX0
        exact Category.id_comp (L.map f)
      have hmapY :
          G.map (L.map f) ≫
              G.map (𝟙 (L.obj (op ⟨(L.obj Y).unop.obj, hLy⟩))) =
            G.map (L.map f) := by
        rw [← G.map_comp]
        congr 1
        cases hY0
        exact Category.comp_id (L.map f)
      have hcore :
          G.map (𝟙 (L.obj (op ⟨(L.obj X).unop.obj, hLx⟩))) ≫
              G.map (L.map f) ≫
                G.map (𝟙 (L.obj (op ⟨(L.obj Y).unop.obj, hLy⟩))) =
            G.map (L.map f) := by
        calc
          _ = (G.map (𝟙 (L.obj (op ⟨(L.obj X).unop.obj, hLx⟩))) ≫
              G.map (L.map f)) ≫
                G.map (𝟙 (L.obj (op ⟨(L.obj Y).unop.obj, hLy⟩))) := by
            simp only [Category.assoc]
          _ = G.map (L.map f) ≫
              G.map (𝟙 (L.obj (op ⟨(L.obj Y).unop.obj, hLy⟩))) := by
            rw [hmapX]
          _ = G.map (L.map f) := hmapY
      have hnat :
          G.map (L.map f) ≫ counitG.app (op ⟨(L.obj Y).unop.obj, hLy⟩) =
            counitG.app (op ⟨(L.obj X).unop.obj, hLx⟩) ≫ U.map f := by
        have hleft :
            G.map (L.map f) ≫ counitG.app (op ⟨(L.obj Y).unop.obj, hLy⟩) ≍
              G.map (L.map f) ≫ counitG.app Y := by
          cases hY0
          rfl
        have hright :
            counitG.app (op ⟨(L.obj X).unop.obj, hLx⟩) ≫ U.map f ≍
              counitG.app X ≫ U.map f := by
          cases hX0
          rfl
        have hn :
            G.map (L.map f) ≫ counitG.app Y =
              counitG.app X ≫ U.map f := by
          simpa only [Functor.comp_obj, Functor.comp_map, G] using
            counitG.naturality f
        exact eq_of_heq (hleft.trans ((heq_of_eq hn).trans hright.symm))
      have hcore_assoc {Z : C}
          (k : G.obj (L.obj (op ⟨(L.obj Y).unop.obj, hLy⟩)) ⟶ Z) :
          G.map (𝟙 (L.obj (op ⟨(L.obj X).unop.obj, hLx⟩))) ≫
              G.map (L.map f) ≫
                G.map (𝟙 (L.obj (op ⟨(L.obj Y).unop.obj, hLy⟩))) ≫ k =
            G.map (L.map f) ≫ k := by
        calc
          _ = (G.map (𝟙 (L.obj (op ⟨(L.obj X).unop.obj, hLx⟩))) ≫
              G.map (L.map f) ≫
                G.map (𝟙 (L.obj (op ⟨(L.obj Y).unop.obj, hLy⟩)))) ≫ k := by
            simp only [Category.assoc]
          _ = G.map (L.map f) ≫ k := by rw [hcore]
      have hnat_assoc {Z : C}
          (k : U.obj (op ⟨(L.obj Y).unop.obj, hLy⟩) ⟶ Z) :
          G.map (L.map f) ≫ counitG.app (op ⟨(L.obj Y).unop.obj, hLy⟩) ≫ k =
            counitG.app (op ⟨(L.obj X).unop.obj, hLx⟩) ≫ U.map f ≫ k := by
        calc
          _ = (G.map (L.map f) ≫
              counitG.app (op ⟨(L.obj Y).unop.obj, hLy⟩)) ≫ k := by
            simp only [Category.assoc]
          _ = (counitG.app (op ⟨(L.obj X).unop.obj, hLx⟩) ≫ U.map f) ≫ k := by
            rw [hnat]
          _ = _ := by simp only [Category.assoc]
      rw [hcore_assoc]
      rw [hnat_assoc]
      have hIso : IsIso (counitG.app (op ⟨(L.obj X).unop.obj, hLx⟩)) :=
        hCounitIso _
      simpa only [Category.assoc] using
        congrArg
          (fun k => eqToHom _ ≫ k)
          (@IsIso.inv_hom_id_assoc _ _ _ _
            (counitG.app (op ⟨(L.obj X).unop.obj, hLx⟩)) hIso _
            (U.map f ≫ eqToHom _))
  have hG : G.IsRightKanExtension counitG := by
    dsimp [G, counitG]
    infer_instance
  let alpha := Functor.whiskerLeft L eNat.hom ≫ counitG
  have hF : F.IsRightKanExtension alpha := by
    exact @Functor.isRightKanExtension_of_iso _ _ _ _ _ _ G F eNat.symm L U
      counitG alpha (by
      dsimp [alpha]
      rw [← Functor.whiskerLeft_comp_assoc, eNat.inv_hom_id,
        Functor.whiskerLeft_id', Category.id_comp]) hG
  refine ⟨{ next := F, restrict_eq := hrestrict, homEquiv := ?_ }⟩
  intro V
  simpa [SimplicialObject.Truncated.trunc] using
    (@Functor.homEquivOfIsRightKanExtension _ _ _ _ _ _ F L U alpha hF V)

theorem exists_inductive_coskeleton_tower {C : Type u} [Category.{v} C]
    [HasFiniteLimits C] (m : ℕ) (U : SimplicialObject.Truncated C m) :
    Nonempty (InductiveCoskeletonTower m U) := by
  let stepData : ∀ k : ℕ, (V : SimplicialObject.Truncated C (m + k)) →
      FiniteOneStepData (m + k) V :=
    fun k V => Classical.choice (exists_finite_one_step (m + k) V)
  let level : ∀ k : ℕ, SimplicialObject.Truncated C (m + k) :=
    Nat.rec U (fun k V => (stepData k V).next)
  have hnext (k : ℕ) :
      (SimplicialObject.Truncated.trunc C (m + k + 1) (m + k)).obj
          (level (k + 1)) = level k := by
    change (SimplicialObject.Truncated.trunc C (m + k + 1) (m + k)).obj
        (stepData k (level k)).next = level k
    exact (stepData k (level k)).restrict_eq
  have hmap (k : ℕ) (V : SimplicialObject.Truncated C (m + k)) :
      (V ⟶ level k) ≃
        ((SimplicialObject.Truncated.trunc C (m + k) m).obj V ⟶ U) := by
    induction k with
    | zero =>
        have hV : (SimplicialObject.Truncated.trunc C m m).obj V = V := by
          refine CategoryTheory.Functor.ext (fun X => ?_) (fun X Y f => ?_)
          · apply congrArg V.obj
            apply Opposite.unop_injective
            apply ObjectProperty.FullSubcategory.ext
            rfl
          · dsimp [SimplicialObject.Truncated.trunc]
            simp
            rfl
        simpa [level, hV] using (Equiv.refl (V ⟶ U))
    | succ k ih =>
        exact (stepData k (level k)).homEquiv V |>.trans
          (ih ((SimplicialObject.Truncated.trunc C (m + k + 1) (m + k)).obj V))
  exact ⟨{
    level := level
    base := by simpa using (show level 0 = U from rfl)
    next_restrict := hnext
    mapping_property := hmap
  }⟩

theorem inductive_tower_mapping_property {C : Type u} [Category.{v} C]
    {m : ℕ} {U : SimplicialObject.Truncated C m}
    (T : InductiveCoskeletonTower m U) (k : ℕ)
    (V : SimplicialObject.Truncated C (m + k)) :
    Nonempty ((V ⟶ T.level k) ≃
      ((SimplicialObject.Truncated.trunc C (m + k) m).obj V ⟶ U)) := by
  exact ⟨T.mapping_property k V⟩

theorem inductive_tower_component_stabilizes {C : Type u} [Category.{v} C]
    {m : ℕ} {U : SimplicialObject.Truncated C m}
    (T : InductiveCoskeletonTower m U) (r k : ℕ)
    (h : r ≤ k) (h' : r ≤ k + 1) :
    inductiveCoskeletonComponent T r k h =
      inductiveCoskeletonComponent T r (k + 1) h' := by
  have e := congrArg (fun V : SimplicialObject.Truncated C (m + k) =>
    V.obj (op ⟨SimplexCategory.mk (m + r), Nat.add_le_add_left h m⟩)) (T.next_restrict k)
  have hobj : (op ((SimplexCategory.Truncated.incl (m + k) (m + k + 1)).obj
      ⟨SimplexCategory.mk (m + r), Nat.add_le_add_left h m⟩)) =
      (op ⟨SimplexCategory.mk (m + r), Nat.add_le_add_left h' m⟩) := by
    apply congrArg op
    apply ObjectProperty.FullSubcategory.ext
    rfl
  change (T.level k).obj _ = (T.level (k + 1)).obj _
  rw [← hobj]
  exact e.symm

/-! ## Consequences usually packaged as the cosk-up lemma -/

noncomputable def coskeletonAdjunction {C : Type u} [Category.{v} C] (n : ℕ)
    [∀ U : SimplicialObject.Truncated C n, HasCoskeleton n U] :
    SimplicialObject.truncation (C := C) n ⊣
      SimplicialObject.Truncated.cosk (C := C) n :=
  Functor.ranAdjunction (H := C) (truncInclusion n)

noncomputable def coskeletonUnit {C : Type u} [Category.{v} C] (n : ℕ)
    [∀ U : SimplicialObject.Truncated C n, HasCoskeleton n U] :
    𝟭 (SimplicialObject C) ⟶
      SimplicialObject.truncation (C := C) n ⋙
        SimplicialObject.Truncated.cosk (C := C) n :=
  (coskeletonAdjunction n).unit

noncomputable def cosk_up_right_adjoint {C : Type u} [Category.{v} C] (n : ℕ)
    [∀ U : SimplicialObject.Truncated C n, HasCoskeleton n U] :
    SimplicialObject.truncation (C := C) n ⊣
      SimplicialObject.Truncated.cosk (C := C) n :=
  coskeletonAdjunction n

noncomputable def restrictedCoskeleton {C : Type u} [Category.{v} C]
    (n n' : ℕ) (_h : n ≤ n')
    [∀ U : SimplicialObject.Truncated C n, HasCoskeleton n U] :
    SimplicialObject.Truncated C n ⥤ SimplicialObject.Truncated C n' :=
  SimplicialObject.Truncated.cosk (C := C) n ⋙
    SimplicialObject.truncation (C := C) n'

theorem restricted_coskeleton_right_adjoint {C : Type u} [Category.{v} C]
    (n n' : ℕ) (h : n ≤ n')
    [∀ U : SimplicialObject.Truncated C n, HasCoskeleton n U] :
    Nonempty (SimplicialObject.Truncated.trunc C n' n h ⊣
      restrictedCoskeleton n n' h) := by
  sorry

theorem cosk_up_coskeleton_iso {C : Type u} [Category.{v} C]
    (n m : ℕ) (h : n ≤ m)
    [∀ U : SimplicialObject.Truncated C n, HasCoskeleton n U]
    [∀ U : SimplicialObject.Truncated C m, HasCoskeleton m U]
    (U : SimplicialObject.Truncated C n) :
    Nonempty ((SimplicialObject.Truncated.cosk m).obj
        ((SimplicialObject.truncation m).obj
          ((SimplicialObject.Truncated.cosk n).obj U)) ≅
      (SimplicialObject.Truncated.cosk n).obj U) := by
  let adjR : SimplicialObject.Truncated.trunc C m n h ⊣
      restrictedCoskeleton n m h :=
    Classical.choice (restricted_coskeleton_right_adjoint n m h)
  let adjComp := (cosk_up_right_adjoint m).comp adjR
  let adjComp' := Adjunction.ofNatIsoLeft adjComp
    (SimplicialObject.truncationCompTrunc h)
  let e := Adjunction.rightAdjointUniq (cosk_up_right_adjoint n) adjComp'
  exact ⟨e.symm.app U⟩

theorem cosk_up_preserves_coskeletal {C : Type u} [Category.{v} C]
    (n m : ℕ) (h : n ≤ m)
    [∀ U : SimplicialObject.Truncated C n, HasCoskeleton n U]
    [∀ U : SimplicialObject.Truncated C m, HasCoskeleton m U]
    (U : SimplicialObject C)
    [IsIso ((coskeletonUnit n).app U)] :
    IsIso ((coskeletonUnit m).app U) := by
  sorry

/-! ## Weaker existence hypotheses and connected indexing categories -/

abbrev HasFiniteConnectedLimits (C : Type u) [Category.{v} C] : Prop :=
  ∀ (J : Type) [SmallCategory J] [FinCategory J] [IsConnected J],
    HasLimitsOfShape J C

theorem has_coskeleton_of_has_finite_connected_limits
    {C : Type u} [Category.{v} C] (k : ℕ) (hk : 1 ≤ k)
    (hC : HasFiniteConnectedLimits C)
    (U : SimplicialObject.Truncated C k) :
    HasCoskeleton k U := by
  let : NeZero k := ⟨Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hk)⟩
  let : (truncInclusion k).HasPointwiseRightKanExtension U := by
    intro X
    have : Finite (SimplexCategory.Truncated k) :=
      Finite.of_injective
        (fun x => ⟨x.1.len, Nat.lt_succ_of_le x.2⟩ :
          SimplexCategory.Truncated k → Fin (k + 1))
        (by
          intro x y h
          cases x with
          | mk x hx =>
            cases y with
            | mk y hy =>
              congr
              exact SimplexCategory.ext (Fin.ext_iff.mp h))
    let : Fintype (SimplexCategory.Truncated k) := Fintype.ofFinite _
    let : Fintype ((SimplexCategory.Truncated k)ᵒᵖ) :=
      Fintype.ofEquiv _ equivToOpposite
    let : ∀ T : (SimplexCategory.Truncated k)ᵒᵖ,
        Finite (X ⟶ (truncInclusion k).obj T) := fun T =>
      Finite.of_injective (fun f => f.unop.toOrderHom.toFun)
        (by
          intro f g h
          apply Opposite.unop_injective
          apply SimplexCategory.Hom.ext
          exact DFunLike.ext _ _ (fun i => congrFun h i))
    let : ∀ T : (SimplexCategory.Truncated k)ᵒᵖ,
        Fintype (X ⟶ (truncInclusion k).obj T) := fun T => Fintype.ofFinite _
    let : Fintype (StructuredArrow X (truncInclusion k)) :=
      Fintype.ofInjective
        (fun j : StructuredArrow X (truncInclusion k) =>
          (⟨j.right, j.hom⟩ : Σ T, X ⟶ (truncInclusion k).obj T))
        (by
          rintro ⟨⟨⟩, jr, jh⟩ ⟨⟨⟩, kr, kh⟩ h
          cases h
          rfl)
    let : ∀ j k : StructuredArrow X (truncInclusion k), Finite (j ⟶ k) :=
      fun j k =>
        Finite.of_injective (fun f => f.right.unop.hom.toOrderHom.toFun)
          (by
            intro f g h
            apply Comma.hom_ext f g
            · exact Subsingleton.elim _ _
            · apply Opposite.unop_injective
              apply SimplexCategory.Truncated.Hom.ext
              exact DFunLike.ext _ _ (fun i => congrFun h i))
    let : FinCategory (StructuredArrow X (truncInclusion k)) :=
      { fintypeObj := inferInstance
        fintypeHom := fun j k => Fintype.ofFinite _ }
    by_cases hX : X.unop.len ≤ k
    · let Y : (SimplexCategory.Truncated k)ᵒᵖ :=
        op ⟨SimplexCategory.mk X.unop.len, hX⟩
      have e : (truncInclusion k).obj Y = X := by
        apply Opposite.unop_injective
        exact SimplexCategory.ext rfl
      rw [← e]
      let hInitial : IsInitial (StructuredArrow.mk (𝟙 (truncInclusion k).obj Y)) :=
        StructuredArrow.mkIdInitial
      exact HasLimit.mk
        { cone := coneOfDiagramInitial hInitial
            (StructuredArrow.proj ((truncInclusion k).obj Y) (truncInclusion k) ⋙ U)
          isLimit := limitOfDiagramInitial hInitial
            (StructuredArrow.proj ((truncInclusion k).obj Y) (truncInclusion k) ⋙ U) }
    · let e : X = op (SimplexCategory.mk X.unop.len) := by
        apply Opposite.unop_injective
        exact SimplexCategory.ext rfl
      rw [e]
      let : IsConnected (coskeletonIndex k X.unop.len) := by infer_instance
      let : HasLimitsOfShape (coskeletonIndex k X.unop.len) C :=
        hC (coskeletonIndex k X.unop.len)
      change HasLimit (coskeletonIndexDiagram k X.unop.len U)
      exact (inferInstance :
        HasLimitsOfShape (coskeletonIndex k X.unop.len) C).has_limit _
  exact
    (Functor.pointwiseRightKanExtensionIsPointwiseRightKanExtension
      (truncInclusion k) U).hasRightKanExtension

theorem has_coskeleton_functor_of_has_finite_connected_limits
    {C : Type u} [Category.{v} C] (k : ℕ) (hk : 1 ≤ k)
    (hC : HasFiniteConnectedLimits C) :
    HasCoskeletonFunctor (C := C) k := by
  intro U
  exact has_coskeleton_of_has_finite_connected_limits k hk hC U

theorem coskeleton_index_is_connected (k n : ℕ) (hk : 1 ≤ k)
    (hkn : k + 1 ≤ n) :
    IsConnected (coskeletonIndex k n) := by
  sorry

/-! ## Products and fibre products -/

theorem coskeleton_product_iso {C : Type u} [Category.{v} C] (n : ℕ)
    [∀ U : SimplicialObject.Truncated C n, HasCoskeleton n U]
    {U V : SimplicialObject.Truncated C n} [HasBinaryProduct U V]
    [HasBinaryProduct
      ((SimplicialObject.Truncated.cosk n).obj U)
      ((SimplicialObject.Truncated.cosk n).obj V)] :
    Nonempty ((SimplicialObject.Truncated.cosk n).obj (U ⨯ V) ≅
      (SimplicialObject.Truncated.cosk n).obj U ⨯
        (SimplicialObject.Truncated.cosk n).obj V) := by
  sorry

theorem coskeleton_fibre_product_iso {C : Type u} [Category.{v} C] (n : ℕ)
    [∀ U : SimplicialObject.Truncated C n, HasCoskeleton n U]
    {U V W : SimplicialObject.Truncated C n} (a : U ⟶ V) (b : W ⟶ V)
    [HasPullback a b]
    [HasPullback
      ((SimplicialObject.Truncated.cosk n).map a)
      ((SimplicialObject.Truncated.cosk n).map b)] :
    Nonempty ((SimplicialObject.Truncated.cosk n).obj (pullback a b) ≅
      pullback ((SimplicialObject.Truncated.cosk n).map a)
        ((SimplicialObject.Truncated.cosk n).map b)) := by
  sorry

/-! ## Coskeletons over an object -/

theorem coskeleton_over_forget_commutes {C : Type u} [Category.{v} C]
    [HasFiniteLimits C] (X : C) (k : ℕ) (hk : 1 ≤ k)
    [∀ U : SimplicialObject.Truncated (Over X) k,
      (SimplexCategory.Truncated.inclusion k).op.HasRightKanExtension U]
    [∀ U : SimplicialObject.Truncated C k,
      (SimplexCategory.Truncated.inclusion k).op.HasRightKanExtension U]
    (U : SimplicialObject.Truncated (Over X) k) :
    Nonempty (((SimplicialObject.whiskering (Over X) C).obj (Over.forget X)).obj
        ((SimplicialObject.Truncated.cosk (C := Over X) k).obj U) ≅
      (SimplicialObject.Truncated.cosk (C := C) k).obj
        (((SimplicialObject.Truncated.whiskering (Over X) C).obj
          (Over.forget X)).obj U)) := by
  sorry

/-! ## The standard simplex -/

theorem standard_simplex_hom_equiv_from_one_skeleton (n : ℕ) (U : SSet) :
    Nonempty ((U ⟶ (Δ[n] : SSet)) ≃
      ((SSet.truncation 1).obj U ⟶
        (SSet.truncation 1).obj (Δ[n] : SSet))) := by
  sorry

theorem standard_simplex_is_one_coskeletal (n : ℕ) :
    IsIso ((SSet.coskAdj 1).unit.app (Δ[n] : SSet)) := by
  sorry

end Formalization.Books.Simplicial.Unit19
