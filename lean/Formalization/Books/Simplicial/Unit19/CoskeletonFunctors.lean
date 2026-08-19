import Formalization.Books.Simplicial.Unit12.TruncatedSimplicialObjects
import Mathlib.AlgebraicTopology.SimplicialObject.Coskeletal
import Mathlib.AlgebraicTopology.SimplicialSet.FiniteProd
import Mathlib.CategoryTheory.Functor.KanExtension.Pointwise
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

universe v u

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
  letI : HasInitial (coskeletonIndex m n) :=
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
  sorry

theorem recover_coskeleton {C : Type u} [Category.{v} C] (n : ℕ)
    (U : SimplicialObject.Truncated C n) [HasCoskeleton n U] :
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
  sorry

theorem has_coskeleton_zero_of_has_binary_products {C : Type u}
    [Category.{v} C] [HasBinaryProducts C] (X : C) :
    HasCoskeleton 0 (zeroTruncatedObject X) := by
  sorry

theorem has_coskeleton_functor_zero_of_has_binary_products {C : Type u}
    [Category.{v} C] [HasBinaryProducts C] :
    HasCoskeletonFunctor (C := C) 0 := by
  sorry

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

theorem formula_limit_of_representable {C : Type u} [Category.{v} C]
    (n : ℕ) (U : SimplicialObject.Truncated C (n + 1)) (Uplus : C)
    (hRep : (compatibleBoundaryFunctor n U).RepresentableBy Uplus)
    [HasLimit (coskeletonIndexDiagram (n + 1) (n + 2) U)] :
    Nonempty (Uplus ≅ limit (coskeletonIndexDiagram (n + 1) (n + 2) U)) := by
  sorry

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

theorem work_out_next_truncated_object {C : Type u} [Category.{v} C]
    (n : ℕ) (U : SimplicialObject.Truncated C (n + 1)) (Uplus : C)
    (hRep : (compatibleBoundaryFunctor n U).RepresentableBy Uplus) :
    Nonempty (NextTruncatedObjectData n U Uplus) := by
  sorry

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

theorem degeneracyTuple_is_compatible {C : Type u} [Category.{v} C]
    (n : ℕ) (U : SimplicialObject.Truncated C (n + 1)) (j : Fin (n + 2)) :
    ∀ (i k : Fin (n + 3)) (hik : i < k),
      degeneracyTuple n U j i ≫ truncatedFace n U ⟨k.val - 1, by omega⟩ =
        degeneracyTuple n U j k ≫ truncatedFace n U ⟨i.val, by omega⟩ := by
  sorry

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
  sorry

theorem degeneracy_tuple_degree_one_second {C : Type u} [Category.{v} C]
    (U : SimplicialObject.Truncated C 1) :
    degeneracyTuple 0 U (1 : Fin 2) 0 =
        extensionFace 0 U (0 : Fin 2) ≫ extensionDegeneracy 0 U (0 : Fin 1) ∧
      degeneracyTuple 0 U (1 : Fin 2) 1 = 𝟙 _ ∧
      degeneracyTuple 0 U (1 : Fin 2) 2 = 𝟙 _ := by
  sorry

theorem degeneracy_tuple_degree_two_first {C : Type u} [Category.{v} C]
    (U : SimplicialObject.Truncated C 2) :
    degeneracyTuple 1 U (0 : Fin 3) 0 = 𝟙 _ ∧
      degeneracyTuple 1 U (0 : Fin 3) 1 = 𝟙 _ ∧
      degeneracyTuple 1 U (0 : Fin 3) 2 =
        extensionFace 1 U (1 : Fin 3) ≫ extensionDegeneracy 1 U (0 : Fin 2) ∧
      degeneracyTuple 1 U (0 : Fin 3) 3 =
        extensionFace 1 U (2 : Fin 3) ≫ extensionDegeneracy 1 U (0 : Fin 2) := by
  sorry

theorem degeneracy_tuple_degree_two_second {C : Type u} [Category.{v} C]
    (U : SimplicialObject.Truncated C 2) :
    degeneracyTuple 1 U (1 : Fin 3) 0 =
        extensionFace 1 U (0 : Fin 3) ≫ extensionDegeneracy 1 U (0 : Fin 2) ∧
      degeneracyTuple 1 U (1 : Fin 3) 1 = 𝟙 _ ∧
      degeneracyTuple 1 U (1 : Fin 3) 2 = 𝟙 _ ∧
      degeneracyTuple 1 U (1 : Fin 3) 3 =
        extensionFace 1 U (2 : Fin 3) ≫ extensionDegeneracy 1 U (1 : Fin 2) := by
  sorry

theorem degeneracy_tuple_degree_two_third {C : Type u} [Category.{v} C]
    (U : SimplicialObject.Truncated C 2) :
    degeneracyTuple 1 U (2 : Fin 3) 0 =
        extensionFace 1 U (0 : Fin 3) ≫ extensionDegeneracy 1 U (1 : Fin 2) ∧
      degeneracyTuple 1 U (2 : Fin 3) 1 =
        extensionFace 1 U (1 : Fin 3) ≫ extensionDegeneracy 1 U (1 : Fin 2) ∧
      degeneracyTuple 1 U (2 : Fin 3) 2 = 𝟙 _ ∧
      degeneracyTuple 1 U (2 : Fin 3) 3 = 𝟙 _ := by
  sorry

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

theorem exists_inductive_coskeleton_tower {C : Type u} [Category.{v} C]
    [HasFiniteLimits C] (m : ℕ) (U : SimplicialObject.Truncated C m) :
    Nonempty (InductiveCoskeletonTower m U) := by
  sorry

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
  sorry

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
  sorry

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
  sorry

theorem has_coskeleton_functor_of_has_finite_connected_limits
    {C : Type u} [Category.{v} C] (k : ℕ) (hk : 1 ≤ k)
    (hC : HasFiniteConnectedLimits C) :
    HasCoskeletonFunctor (C := C) k := by
  sorry

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
