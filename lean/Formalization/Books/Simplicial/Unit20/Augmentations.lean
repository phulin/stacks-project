import Formalization.Books.Simplicial.Unit19.CoskeletonFunctors
import Formalization.Books.Simplicial.Unit03.SimplicialObjects
import Mathlib.AlgebraicTopology.CechNerve

/-!
# Simplicial Methods, Chapter 20: Augmentations

The source's augmentation is a morphism from a simplicial object to a
constant simplicial object.  The Čech nerve used in the chapter is Mathlib's
`Arrow.cechNerve`; the explicit `HasCechNerve` witness below supplies the
wide pullbacks required by that canonical construction.
-/

namespace Formalization.Books.Simplicial.Unit20

open CategoryTheory
open CategoryTheory.Limits
open Opposite
open scoped _root_.Simplicial

universe v u

/-! ## Augmentations -/

/-- An augmentation of `U` towards `X`, as in the source definition. -/
abbrev Augmentation {C : Type u} [Category.{v} C]
    (U : SimplicialObject C) (X : C) : Type _ :=
  U ⟶ (SimplicialObject.const C).obj X

/-- The degree-zero data appearing in the source's augmentation criterion. -/
abbrev AugmentationZeroData {C : Type u} [Category.{v} C]
    (U : SimplicialObject C) (X : C) : Type _ :=
  { ε₀ : U.obj (op (SimplexCategory.mk 0)) ⟶ X //
    U.δ (0 : Fin 2) ≫ ε₀ = U.δ (1 : Fin 2) ≫ ε₀ }

/-- The source's characterization of augmentations by their degree-zero map. -/
theorem augmentation_hom_equiv {C : Type u} [Category.{v} C]
    (U : SimplicialObject C) (X : C) :
    Nonempty (Augmentation U X ≃ AugmentationZeroData U X) := by
  refine ⟨{
    toFun := fun ε => ⟨ε.app (op (SimplexCategory.mk 0)), by
      have h0 := ε.naturality (SimplexCategory.δ (0 : Fin 2)).op
      have h1 := ε.naturality (SimplexCategory.δ (1 : Fin 2)).op
      have h0' : U.map (SimplexCategory.δ (0 : Fin 2)).op ≫
          ε.app (op (SimplexCategory.mk 0)) =
          ε.app (op (SimplexCategory.mk 1)) ≫ 𝟙 X := by
        exact h0
      have h1' : U.map (SimplexCategory.δ (1 : Fin 2)).op ≫
          ε.app (op (SimplexCategory.mk 0)) =
          ε.app (op (SimplexCategory.mk 1)) ≫ 𝟙 X := by
        exact h1
      exact (by
        simpa only [SimplicialObject.δ, Category.comp_id] using h0'.trans h1'.symm)⟩
    invFun := fun d =>
      (SimplicialObject.augment U X d.1 (by
        intro n g₁ g₂
        rw [SimplexCategory.eq_const_of_zero g₁,
          SimplexCategory.eq_const_of_zero g₂]
        rcases le_total (g₁.toOrderHom 0) (g₂.toOrderHom 0) with h | h
        · let e := SimplexCategory.mkOfLe (g₁.toOrderHom 0) (g₂.toOrderHom 0) h
          have he0 : SimplexCategory.δ (0 : Fin 2) ≫ e =
              SimplexCategory.const _ _ (g₂.toOrderHom 0) := by
            apply SimplexCategory.Hom.ext_zero_left
            rfl
          have he1 : SimplexCategory.δ (1 : Fin 2) ≫ e =
              SimplexCategory.const _ _ (g₁.toOrderHom 0) := by
            apply SimplexCategory.Hom.ext_zero_left
            rfl
          rw [← he1, ← he0]
          have hd := d.2
          change U.map (SimplexCategory.δ (0 : Fin 2)).op ≫ d.1 =
            U.map (SimplexCategory.δ (1 : Fin 2)).op ≫ d.1 at hd
          simpa only [op_comp, U.map_comp, Category.assoc] using
            (congrArg (fun k => U.map e.op ≫ k) hd.symm)
        · let e := SimplexCategory.mkOfLe (g₂.toOrderHom 0) (g₁.toOrderHom 0) h
          have he0 : SimplexCategory.δ (0 : Fin 2) ≫ e =
              SimplexCategory.const _ _ (g₁.toOrderHom 0) := by
            apply SimplexCategory.Hom.ext_zero_left
            rfl
          have he1 : SimplexCategory.δ (1 : Fin 2) ≫ e =
              SimplexCategory.const _ _ (g₂.toOrderHom 0) := by
            apply SimplexCategory.Hom.ext_zero_left
            rfl
          rw [← he0, ← he1]
          have hd := d.2
          change U.map (SimplexCategory.δ (0 : Fin 2)).op ≫ d.1 =
            U.map (SimplexCategory.δ (1 : Fin 2)).op ≫ d.1 at hd
          simpa only [op_comp, U.map_comp, Category.assoc] using
            congrArg (fun k => U.map e.op ≫ k) hd)).hom
    left_inv := by
      intro ε
      apply SimplicialObject.hom_ext
      intro n
      change U.map (SimplexCategory.const ⦋0⦌ n.unop 0).op ≫
          ε.app (op (SimplexCategory.mk 0)) = ε.app n
      have h := ε.naturality (SimplexCategory.const ⦋0⦌ n.unop 0).op
      change U.map (SimplexCategory.const ⦋0⦌ n.unop 0).op ≫
          ε.app (op (SimplexCategory.mk 0)) = ε.app n ≫ 𝟙 X at h
      rw [← Category.comp_id (ε.app n)]
      exact h
    right_inv := by
      intro d
      apply Subtype.ext
      dsimp
      exact SimplicialObject.augment_hom_zero U X d.1 _
  }⟩

/-- The degree-zero component of an augmentation. -/
def augmentationAtZero {C : Type u} [Category.{v} C]
    {U : SimplicialObject C} {X : C} (ε : Augmentation U X) :
    U.obj (op (SimplexCategory.mk 0)) ⟶ X :=
  ε.app (op (SimplexCategory.mk 0))

/-- Package a source augmentation as Mathlib's augmented simplicial object. -/
def augmentationAsAugmented {C : Type u} [Category.{v} C]
    {U : SimplicialObject C} {X : C} (ε : Augmentation U X) :
    SimplicialObject.Augmented C where
  left := U
  right := X
  hom := ε

/-! ## The fibre-product simplicial object -/

/-- Existence of all finite wide pullbacks needed for the Čech nerve of `f`. -/
abbrev HasCechNerve {C : Type u} [Category.{v} C]
    {Y X : C} (f : Y ⟶ X) : Prop :=
  ∀ n : ℕ,
    HasWidePullback X
      (fun _ : Fin (n + 1) => Y) (fun _ => f)

/-- The source's simplicial object of iterated fibre products, using Mathlib's
Čech nerve construction. -/
noncomputable def cechNerve {C : Type u} [Category.{v} C]
    {Y X : C} (f : Y ⟶ X) (h : HasCechNerve f) : SimplicialObject C :=
  letI : ∀ n : ℕ,
      HasWidePullback (Arrow.mk f).right
        (fun _ : Fin (n + 1) => (Arrow.mk f).left)
        (fun _ => (Arrow.mk f).hom) := by
    intro n
    change HasWidePullback X (fun _ : Fin (n + 1) => Y) (fun _ => f)
    exact h n
  (Arrow.mk f).cechNerve

/-- The degree formula for the fibre-product simplicial object. -/
theorem cechNerve_obj_formula {C : Type u} [Category.{v} C]
    {Y X : C} (f : Y ⟶ X) (h : HasCechNerve f) (n : ℕ) :
    (cechNerve f h).obj (op (SimplexCategory.mk n)) =
      widePullback X (fun _ : Fin (n + 1) => Y) (fun _ => f) := by
  let _ : ∀ m : ℕ,
      HasWidePullback (Arrow.mk f).right
        (fun _ : Fin (m + 1) => (Arrow.mk f).left)
        (fun _ => (Arrow.mk f).hom) := by
    intro m
    change HasWidePullback X (fun _ : Fin (m + 1) => Y) (fun _ => f)
    exact h m
  rfl

/-- The coordinate map used in the source's construction of a morphism into
the fibre-product simplicial object. -/
def cechNerveCoordinate {C : Type u} [Category.{v} C]
    (V : SimplicialObject C)
    {Y : C} (g₀ : V.obj (op (SimplexCategory.mk 0)) ⟶ Y)
    (n : ℕ) (i : Fin (n + 1)) :
    V.obj (op (SimplexCategory.mk n)) ⟶ Y :=
  V.map (SimplexCategory.const (SimplexCategory.mk 0)
      (SimplexCategory.mk n) i).op ≫ g₀

/-- The two degree-one coordinates are the two face composites in the
source's displayed compatibility diagram.  The index is reversed because
`SimplexCategory.δ i` omits vertex `i`. -/
theorem cechNerveCoordinate_one_faces {C : Type u} [Category.{v} C]
    (V : SimplicialObject C)
    {Y : C} (g₀ : V.obj (op (SimplexCategory.mk 0)) ⟶ Y) (i : Fin 2) :
    cechNerveCoordinate V g₀ 1 i = V.δ (1 - i) ≫ g₀ := by
  fin_cases i <;>
    simp [cechNerveCoordinate, SimplicialObject.δ,
      SimplexCategory.δ_zero_eq_const, SimplexCategory.δ_one_eq_const]

/-- The degree-one compatibility diagram forces the two coordinate maps to
have the same composite with `f`. -/
theorem cechNerve_one_simplex_compatibility {C : Type u} [Category.{v} C]
    {Y X : C} (f : Y ⟶ X) (V : SimplicialObject C)
    (g₀ : V.obj (op (SimplexCategory.mk 0)) ⟶ Y)
    (hg : V.δ (0 : Fin 2) ≫ g₀ ≫ f = V.δ (1 : Fin 2) ≫ g₀ ≫ f) :
    cechNerveCoordinate V g₀ 1 (0 : Fin 2) ≫ f =
      cechNerveCoordinate V g₀ 1 (1 : Fin 2) ≫ f := by
  simpa [cechNerveCoordinate, SimplexCategory.δ_one_eq_const,
    SimplexCategory.δ_zero_eq_const, SimplicialObject.δ, Category.assoc] using hg.symm

/-- The general adjacent-coordinate equality used in the source's
construction of a map into the iterated fibre product. -/
theorem cechNerveCoordinate_adjacent {C : Type u} [Category.{v} C]
    {Y X : C} (f : Y ⟶ X) (V : SimplicialObject C)
    (g₀ : V.obj (op (SimplexCategory.mk 0)) ⟶ Y)
    (hg : V.δ (0 : Fin 2) ≫ g₀ ≫ f = V.δ (1 : Fin 2) ≫ g₀ ≫ f)
    {n : ℕ} (i : Fin n) :
    cechNerveCoordinate V g₀ n (Fin.castSucc i) ≫ f =
      cechNerveCoordinate V g₀ n i.succ ≫ f := by
  simp only [cechNerveCoordinate]
  have h := congrArg (fun k => V.map (SimplexCategory.mkOfSucc i).op ≫ k) hg
  simpa only [SimplicialObject.δ, ← V.map_comp_assoc, ← op_comp,
    SimplexCategory.δ_zero_mkOfSucc, SimplexCategory.δ_one_mkOfSucc,
    Category.assoc] using h.symm

/-- The degree-zero maps satisfying the relation in the source's displayed
hom-set formula. -/
abbrev CechNerveZeroMapData {C : Type u} [Category.{v} C]
    {Y X : C} (f : Y ⟶ X) (V : SimplicialObject C) : Type _ :=
  { g₀ : V.obj (op (SimplexCategory.mk 0)) ⟶ Y //
    V.δ (0 : Fin 2) ≫ g₀ ≫ f = V.δ (1 : Fin 2) ≫ g₀ ≫ f }

private noncomputable def augmentationOfZero {C : Type u} [Category.{v} C]
    (V : SimplicialObject C) {X : C}
    (g₀ : V.obj (op (SimplexCategory.mk 0)) ⟶ X)
    (hg : V.δ (0 : Fin 2) ≫ g₀ = V.δ (1 : Fin 2) ≫ g₀) :
    Augmentation V X :=
  (SimplicialObject.augment V X g₀ (by
    intro n g₁ g₂
    rw [SimplexCategory.eq_const_of_zero g₁,
      SimplexCategory.eq_const_of_zero g₂]
    rcases le_total (g₁.toOrderHom 0) (g₂.toOrderHom 0) with h | h
    · let e := SimplexCategory.mkOfLe (g₁.toOrderHom 0) (g₂.toOrderHom 0) h
      have he0 : SimplexCategory.δ (0 : Fin 2) ≫ e =
          SimplexCategory.const _ _ (g₂.toOrderHom 0) := by
        apply SimplexCategory.Hom.ext_zero_left
        rfl
      have he1 : SimplexCategory.δ (1 : Fin 2) ≫ e =
          SimplexCategory.const _ _ (g₁.toOrderHom 0) := by
        apply SimplexCategory.Hom.ext_zero_left
        rfl
      rw [← he1, ← he0]
      have hh := hg
      change V.map (SimplexCategory.δ (0 : Fin 2)).op ≫ g₀ =
        V.map (SimplexCategory.δ (1 : Fin 2)).op ≫ g₀ at hh
      simpa only [op_comp, V.map_comp, Category.assoc] using
        (congrArg (fun k => V.map e.op ≫ k) hh.symm)
    · let e := SimplexCategory.mkOfLe (g₂.toOrderHom 0) (g₁.toOrderHom 0) h
      have he0 : SimplexCategory.δ (0 : Fin 2) ≫ e =
          SimplexCategory.const _ _ (g₁.toOrderHom 0) := by
        apply SimplexCategory.Hom.ext_zero_left
        rfl
      have he1 : SimplexCategory.δ (1 : Fin 2) ≫ e =
          SimplexCategory.const _ _ (g₂.toOrderHom 0) := by
        apply SimplexCategory.Hom.ext_zero_left
        rfl
      rw [← he0, ← he1]
      have hh := hg
      change V.map (SimplexCategory.δ (0 : Fin 2)).op ≫ g₀ =
        V.map (SimplexCategory.δ (1 : Fin 2)).op ≫ g₀ at hh
      simpa only [op_comp, V.map_comp, Category.assoc] using
        congrArg (fun k => V.map e.op ≫ k) hh)).hom

private noncomputable def cechNerveMapOfZero {C : Type u} [Category.{v} C]
    {Y X : C} (f : Y ⟶ X) (h : HasCechNerve f)
    (V : SimplicialObject C) (d : CechNerveZeroMapData f V) :
    V ⟶ cechNerve f h := by
  let ε : Augmentation V X :=
    augmentationOfZero V (d.1 ≫ f) (by
      simpa only [Category.assoc] using d.2)
  have hε0 : ε.app (op (SimplexCategory.mk 0)) = d.1 ≫ f := by
    simp [ε, augmentationOfZero]
  let F : Arrow C := Arrow.mk f
  letI : ∀ n : ℕ,
      HasWidePullback F.right
        (fun _ : Fin (n + 1) => F.left) (fun _ => F.hom) := by
    intro n
    change HasWidePullback X (fun _ : Fin (n + 1) => Y) (fun _ => f)
    exact h n
  let η' : V ⟶ F.cechNerve :=
    { app := fun x =>
        WidePullback.lift (ε.app x)
          (fun i => V.map (SimplexCategory.const _ x.unop i).op ≫ d.1)
          (by
            intro i
            let q : SimplexCategory.mk 0 ⟶ x.unop :=
              SimplexCategory.const (SimplexCategory.mk 0) x.unop i
            change (V.map (SimplexCategory.const
              (SimplexCategory.mk 0) x.unop i).op ≫ d.1) ≫ f = ε.app x
            rw [Category.assoc, hε0.symm]
            simp)
      naturality := by
        intro x y q
        dsimp [F, Arrow.cechNerve]
        refine WidePullback.hom_ext _ _ _ (fun j => ?_) ?_
        · simp only [Category.assoc, WidePullback.lift_π]
          rw [← V.map_comp_assoc, ← Quiver.Hom.op_unop q, ← op_comp,
            SimplexCategory.const_comp]
          simp only [Quiver.Hom.unop_op]
        · simp only [Category.assoc, WidePullback.lift_base]
          simp }
  change V ⟶ F.cechNerve
  exact η'

private noncomputable def cechNerveZeroOfMap {C : Type u} [Category.{v} C]
    {Y X : C} (f : Y ⟶ X) (h : HasCechNerve f)
    (V : SimplicialObject C) (g : V ⟶ cechNerve f h) :
    CechNerveZeroMapData f V := by
  let F : Arrow C := Arrow.mk f
  letI : ∀ n : ℕ,
      HasWidePullback F.right
        (fun _ : Fin (n + 1) => F.left) (fun _ => F.hom) := by
    intro n
    change HasWidePullback X (fun _ : Fin (n + 1) => Y) (fun _ => f)
    exact h n
  let A : SimplicialObject.Augmented C := F.augmentedCechNerve
  let ε : Augmentation V X := g ≫ A.hom
  let p₀ : (cechNerve f h).obj (op (SimplexCategory.mk 0)) ⟶ Y := by
    rw [cechNerve_obj_formula f h 0]
    exact WidePullback.π (fun _ : Fin (0 + 1) => f) 0
  let r₀ : (cechNerve f h).obj (op (SimplexCategory.mk 1)) ⟶ Y :=
    (cechNerve f h).map (SimplexCategory.δ (1 : Fin 2)).op ≫ p₀
  let r₁ : (cechNerve f h).obj (op (SimplexCategory.mk 1)) ⟶ Y :=
    (cechNerve f h).map (SimplexCategory.δ (0 : Fin 2)).op ≫ p₀
  refine ⟨g.app (op (SimplexCategory.mk 0)) ≫
      p₀, ?_⟩
  have hp₀ : p₀ ≫ f = A.hom.app (op (SimplexCategory.mk 0)) := by
    change (WidePullback.π (fun _ : Fin (0 + 1) => f) 0) ≫ f =
      WidePullback.base (fun _ : Fin (0 + 1) => f)
    simp only [WidePullback.π_arrow]
  have hπ : r₁ ≫ f = r₀ ≫ f := by
    have h₀A := A.hom.naturality (SimplexCategory.δ (0 : Fin 2)).op
    have h₁A := A.hom.naturality (SimplexCategory.δ (1 : Fin 2)).op
    have h₀A' :
        (cechNerve f h).map (SimplexCategory.δ (0 : Fin 2)).op ≫
            A.hom.app (op (SimplexCategory.mk 0)) =
          A.hom.app (op (SimplexCategory.mk 1)) := by
      change A.left.map (SimplexCategory.δ (0 : Fin 2)).op ≫
          A.hom.app (op (SimplexCategory.mk 0)) =
        A.hom.app (op (SimplexCategory.mk 1))
      simp
    have h₁A' :
        (cechNerve f h).map (SimplexCategory.δ (1 : Fin 2)).op ≫
            A.hom.app (op (SimplexCategory.mk 0)) =
          A.hom.app (op (SimplexCategory.mk 1)) := by
      change A.left.map (SimplexCategory.δ (1 : Fin 2)).op ≫
          A.hom.app (op (SimplexCategory.mk 0)) =
        A.hom.app (op (SimplexCategory.mk 1))
      simp
    dsimp [r₁, r₀]
    rw [Category.assoc, hp₀, Category.assoc, hp₀]
    exact h₀A'.trans h₁A'.symm
  have hπ' := congrArg
    (fun k => g.app (op (SimplexCategory.mk 1)) ≫ k) hπ
  have h0 := g.naturality (SimplexCategory.δ (0 : Fin 2)).op
  have h1 := g.naturality (SimplexCategory.δ (1 : Fin 2)).op
  have h0' := congrArg
    (fun k : V.obj (op (SimplexCategory.mk 1)) ⟶
        (cechNerve f h).obj (op (SimplexCategory.mk 0)) =>
      k ≫ p₀ ≫ f) h0
  have h1' := congrArg
    (fun k : V.obj (op (SimplexCategory.mk 1)) ⟶
        (cechNerve f h).obj (op (SimplexCategory.mk 0)) =>
      k ≫ p₀ ≫ f) h1
  have h0'' :
      (V.map (SimplexCategory.δ (0 : Fin 2)).op ≫
        g.app (op (SimplexCategory.mk 0))) ≫ p₀ ≫ f =
      g.app (op (SimplexCategory.mk 1)) ≫ r₁ ≫ f := by
    simp [r₁, Category.assoc]
  have h1'' :
      (V.map (SimplexCategory.δ (1 : Fin 2)).op ≫
        g.app (op (SimplexCategory.mk 0))) ≫ p₀ ≫ f =
      g.app (op (SimplexCategory.mk 1)) ≫ r₀ ≫ f := by
    simp [r₀, Category.assoc]
  simpa only [SimplicialObject.δ, Category.assoc] using
    h0''.trans (hπ'.trans h1''.symm)

/-! ## The hom-set and coskeleton statements -/

private noncomputable def cechNerveZeroOfTruncatedMap {C : Type u} [Category.{v} C]
    {Y X : C} (f : Y ⟶ X) (h : HasCechNerve f)
    (V : SimplicialObject C)
    (p : SimplexCategory.len (SimplexCategory.mk 0) ≤ 1)
    (g : (SimplicialObject.truncation (C := C) 1).obj V ⟶
      (SimplicialObject.truncation (C := C) 1).obj (cechNerve f h)) :
    CechNerveZeroMapData f V := by
  let p₀ : (cechNerve f h).obj (op (SimplexCategory.mk 0)) ⟶ Y := by
    rw [cechNerve_obj_formula f h 0]
    exact WidePullback.π (fun _ : Fin (0 + 1) => f) 0
  refine ⟨g.app (op ⟨SimplexCategory.mk 0, p⟩) ≫ p₀, ?_⟩
  have h0 := g.naturality
    (SimplexCategory.Truncated.Hom.tr (SimplexCategory.δ (0 : Fin 2))).op
  have h1 := g.naturality
    (SimplexCategory.Truncated.Hom.tr (SimplexCategory.δ (1 : Fin 2))).op
  have hp₀ : p₀ ≫ f =
      WidePullback.base (fun _ : Fin (0 + 1) => f) := by
    change (WidePullback.π (fun _ : Fin (0 + 1) => f) 0) ≫ f = _
    simp only [WidePullback.π_arrow]
  have hface :
      (cechNerve f h).map (SimplexCategory.δ (0 : Fin 2)).op ≫ p₀ ≫ f =
        (cechNerve f h).map (SimplexCategory.δ (1 : Fin 2)).op ≫ p₀ ≫ f := by
    let F : Arrow C := Arrow.mk f
    let : ∀ n : ℕ,
        HasWidePullback F.right
          (fun _ : Fin (n + 1) => F.left) (fun _ => F.hom) := by
      intro n
      change HasWidePullback X (fun _ : Fin (n + 1) => Y) (fun _ => f)
      exact h n
    let A : SimplicialObject.Augmented C := F.augmentedCechNerve
    have h0A' :
        (cechNerve f h).map (SimplexCategory.δ (0 : Fin 2)).op ≫
            A.hom.app (op (SimplexCategory.mk 0)) =
          A.hom.app (op (SimplexCategory.mk 1)) := by
      change A.left.map (SimplexCategory.δ (0 : Fin 2)).op ≫
          A.hom.app (op (SimplexCategory.mk 0)) =
        A.hom.app (op (SimplexCategory.mk 1))
      simp
    have h1A' :
        (cechNerve f h).map (SimplexCategory.δ (1 : Fin 2)).op ≫
            A.hom.app (op (SimplexCategory.mk 0)) =
          A.hom.app (op (SimplexCategory.mk 1)) := by
      change A.left.map (SimplexCategory.δ (1 : Fin 2)).op ≫
          A.hom.app (op (SimplexCategory.mk 0)) =
        A.hom.app (op (SimplexCategory.mk 1))
      simp
    have hfaceA := h0A'.trans h1A'.symm
    change
      (cechNerve f h).map (SimplexCategory.δ (0 : Fin 2)).op ≫
          (WidePullback.base (fun _ : Fin (0 + 1) => f) : _ ⟶ X) =
        (cechNerve f h).map (SimplexCategory.δ (1 : Fin 2)).op ≫
          (WidePullback.base (fun _ : Fin (0 + 1) => f) : _ ⟶ X) at hfaceA
    have hfaceB :
        (cechNerve f h).map (SimplexCategory.δ (0 : Fin 2)).op ≫
            (WidePullback.base (fun _ : Fin (0 + 1) => f) : _ ⟶ F.right) =
          (cechNerve f h).map (SimplexCategory.δ (1 : Fin 2)).op ≫
            (WidePullback.base (fun _ : Fin (0 + 1) => f) : _ ⟶ F.right) := by
      simpa [A, F, Arrow.mk] using hfaceA
    simpa [F, ← hp₀] using hfaceB
  have h0' := congrArg (fun k => k ≫ p₀ ≫ f) h0
  have h1' := congrArg (fun k => k ≫ p₀ ≫ f) h1
  have h0'' :
      V.map (SimplexCategory.δ (0 : Fin 2)).op ≫
          (g.app (op ⟨SimplexCategory.mk 0, p⟩) ≫ p₀) ≫ f =
        g.app (op ⟨SimplexCategory.mk 1, by simp⟩) ≫
          (cechNerve f h).map (SimplexCategory.δ (0 : Fin 2)).op ≫ p₀ ≫ f := by
    simpa [SimplicialObject.truncation, SimplicialObject.δ,
      Nat.zero_add, Category.assoc] using h0'
  have h1'' :
      V.map (SimplexCategory.δ (1 : Fin 2)).op ≫
          (g.app (op ⟨SimplexCategory.mk 0, p⟩) ≫ p₀) ≫ f =
        g.app (op ⟨SimplexCategory.mk 1, by simp⟩) ≫
          (cechNerve f h).map (SimplexCategory.δ (1 : Fin 2)).op ≫ p₀ ≫ f := by
    simpa [SimplicialObject.truncation, SimplicialObject.δ,
      Nat.zero_add, Category.assoc] using h1'
  have hface' := congrArg
    (fun k => g.app (op ⟨SimplexCategory.mk 1, by simp⟩) ≫ k) hface
  simpa [SimplicialObject.δ, Nat.zero_add, Category.assoc] using
    h0''.trans (hface'.trans h1''.symm)

private lemma truncated_app_proof_irrel {C : Type u} [Category.{v} C]
    {V W : SimplicialObject.Truncated C 1}
    (g : V ⟶ W) (n : ℕ)
    (p q : SimplexCategory.len (SimplexCategory.mk n) ≤ 1) :
    g.app (op ⟨SimplexCategory.mk n, p⟩) =
      g.app (op ⟨SimplexCategory.mk n, q⟩) := by
  have hobj : (⟨SimplexCategory.mk n, p⟩ : SimplexCategory.Truncated 1) =
      ⟨SimplexCategory.mk n, q⟩ := by
    apply ObjectProperty.FullSubcategory.ext
    rfl
  cases hobj
  rfl

private lemma cechNerveZeroOfTruncatedMap_fst {C : Type u} [Category.{v} C]
    {Y X : C} (f : Y ⟶ X) (h : HasCechNerve f)
    (V : SimplicialObject C)
    (g : (SimplicialObject.truncation (C := C) 1).obj V ⟶
      (SimplicialObject.truncation (C := C) 1).obj (cechNerve f h))
    (p : SimplexCategory.len (SimplexCategory.mk 0) ≤ 1) :
    (cechNerveZeroOfTruncatedMap f h V p g).1 =
      g.app (op ⟨SimplexCategory.mk 0, p⟩) ≫
        WidePullback.π (fun _ : Fin (0 + 1) => f) 0 := by
  dsimp [cechNerveZeroOfTruncatedMap]
  cases cechNerve_obj_formula f h 0
  rfl

/-- The second equality in the source's displayed formula, expressed as an
equivalence from the truncated hom-set to the degree-zero data. -/
theorem cechNerve_truncated_hom_equiv_zero {C : Type u} [Category.{v} C]
    {Y X : C} (f : Y ⟶ X) (h : HasCechNerve f)
    (V : SimplicialObject C) :
    Nonempty (((SimplicialObject.truncation (C := C) 1).obj V ⟶
        (SimplicialObject.truncation (C := C) 1).obj (cechNerve f h)) ≃
      CechNerveZeroMapData f V) := by
  let p₀ : SimplexCategory.len (SimplexCategory.mk 0) ≤ 1 := by simp
  refine ⟨Equiv.mk (cechNerveZeroOfTruncatedMap f h V p₀)
    (fun d => (SimplicialObject.truncation (C := C) 1).map
      (cechNerveMapOfZero f h V d)) ?_ ?_⟩
  · intro g
    let d := cechNerveZeroOfTruncatedMap f h V p₀ g
    let F : Arrow C := Arrow.mk f
    let : ∀ n : ℕ,
        HasWidePullback F.right
          (fun _ : Fin (n + 1) => F.left) (fun _ => F.hom) := by
      intro n
      change HasWidePullback X (fun _ : Fin (n + 1) => Y) (fun _ => f)
      exact h n
    change (SimplicialObject.truncation (C := C) 1).obj V ⟶
      (SimplicialObject.truncation (C := C) 1).obj F.cechNerve at g
    have hd : d.1 =
        g.app (op ⟨SimplexCategory.mk 0, p₀⟩) ≫
          WidePullback.π (fun _ : Fin (0 + 1) => f) 0 := by
      dsimp [d, cechNerveZeroOfTruncatedMap]
      cases Formalization.Books.Simplicial.Unit03.cech_nerve_degree F 0
      rfl
    let pF :
        ((SimplicialObject.truncation (C := C) 1).obj F.cechNerve).obj
            (op ⟨SimplexCategory.mk 0, p₀⟩) ⟶ Y := by
      change F.cechNerve.obj (op (SimplexCategory.mk 0)) ⟶ Y
      rw [Formalization.Books.Simplicial.Unit03.cech_nerve_degree F 0]
      exact WidePullback.π (fun _ : Fin (0 + 1) => f) 0
    let pFAt : ∀ q : SimplexCategory.len (SimplexCategory.mk 0) ≤ 1,
        ((SimplicialObject.truncation (C := C) 1).obj F.cechNerve).obj
            (op ⟨SimplexCategory.mk 0, q⟩) ⟶ Y := fun q => by
      change F.cechNerve.obj (op (SimplexCategory.mk 0)) ⟶ Y
      rw [Formalization.Books.Simplicial.Unit03.cech_nerve_degree F 0]
      exact WidePullback.π (fun _ : Fin (0 + 1) => f) 0
    have hdF : d.1 =
        g.app (op ⟨SimplexCategory.mk 0, p₀⟩) ≫ pF := by
      dsimp [d, cechNerveZeroOfTruncatedMap, pF]
      cases cechNerve_obj_formula f h 0
      cases Formalization.Books.Simplicial.Unit03.cech_nerve_degree F 0
      rfl
    change (SimplicialObject.truncation (C := C) 1).map
        (cechNerveMapOfZero f h V d) = g
    ext j
    rcases j with ⟨⟨⟨n⟩, hn⟩⟩
    have hn' : n ≤ 1 := by simpa only [SimplexCategory.len_mk] using hn
    rcases Nat.eq_zero_or_pos n with rfl | hnpos
    · change (cechNerveMapOfZero f h V d).app
          ((SimplexCategory.Truncated.inclusion 1).op.obj
            (op ⟨SimplexCategory.mk 0, hn⟩)) =
        g.app (op ⟨SimplexCategory.mk 0, hn⟩)
      cases cechNerve_obj_formula f h 0
      apply WidePullback.hom_ext _ _ _ ?_ ?_
      · intro i
        rcases i with ⟨i, hi⟩
        change i < 1 at hi
        have hi' : i < 1 := hi
        have : i = 0 := by omega
        subst i
        dsimp [cechNerveMapOfZero]
        change WidePullback.lift _ _ _ ≫ _ = _
        simp only [WidePullback.lift_π]
        rw [hd]
        have hghn : g.app (op ⟨SimplexCategory.mk 0, p₀⟩) =
            g.app (op ⟨SimplexCategory.mk 0, hn⟩) :=
          truncated_app_proof_irrel
            (W := (SimplicialObject.truncation (C := C) 1).obj F.cechNerve)
            g 0 p₀ hn
        have hconst : SimplexCategory.const (SimplexCategory.mk 0)
            (SimplexCategory.mk 0) 0 = 𝟙 (SimplexCategory.mk 0) := by
          apply SimplexCategory.Hom.ext_zero_left
          rfl
        rw [hconst]
        simp only [CategoryTheory.op_id, V.map_id]
        rw [hghn]
        exact Category.id_comp _
      · dsimp [cechNerveMapOfZero]
        change WidePullback.lift _ _ _ ≫ _ = _
        simp only [WidePullback.lift_base]
        have hε0 :
            (augmentationOfZero V (d.1 ≫ f)
              (by simpa only [Category.assoc] using d.2)).app
                (op (SimplexCategory.mk 0)) = d.1 ≫ f := by
          simp [augmentationOfZero]
        have hghn : g.app (op ⟨SimplexCategory.mk 0, p₀⟩) =
            g.app (op ⟨SimplexCategory.mk 0, hn⟩) :=
          truncated_app_proof_irrel
            (W := (SimplicialObject.truncation (C := C) 1).obj F.cechNerve)
            g 0 p₀ hn
        have hpF : pF ≫ f =
            WidePullback.base (fun _ : Fin (0 + 1) => f) := by
          dsimp [pF]
          change WidePullback.π (fun _ : Fin (0 + 1) => f) 0 ≫ f = _
          rw [WidePullback.π_arrow]
        rw [hε0, hdF, hghn]
        change (g.app (op ⟨SimplexCategory.mk 0, hn⟩) ≫ pF) ≫ f = _
        rw [Category.assoc, hpF]
        rfl
    · have : n = 1 := by omega
      subst n
      change (cechNerveMapOfZero f h V d).app
          ((SimplexCategory.Truncated.inclusion 1).op.obj
            (op ⟨SimplexCategory.mk 1, hn⟩)) =
        g.app (op ⟨SimplexCategory.mk 1, hn⟩)
      cases Formalization.Books.Simplicial.Unit03.cech_nerve_degree F 1
      apply WidePullback.hom_ext _ _ _ ?_ ?_
      · intro i
        rcases i with ⟨i, hi⟩
        change i < 2 at hi
        have hi' : i < 2 := hi
        have hicases : i = 0 ∨ i = 1 := by omega
        rcases hicases with rfl | rfl
        · have hi := g.naturality
            (SimplexCategory.Truncated.Hom.tr
              (SimplexCategory.δ (1 : Fin 2))).op
          have hi' := congrArg
            (fun k => k ≫ pFAt _)
            hi
          dsimp [cechNerveMapOfZero]
          change WidePullback.lift _ _ _ ≫ _ = _
          simp only [WidePullback.lift_π]
          rw [hdF]
          simpa [SimplicialObject.truncation, SimplicialObject.δ,
            SimplexCategory.δ_one_eq_const, SimplexCategory.δ_zero_eq_const,
            F, Arrow.cechNerve, Category.assoc, pF, pFAt,
            WidePullback.lift_π] using hi'
        · have hi := g.naturality
            (SimplexCategory.Truncated.Hom.tr
              (SimplexCategory.δ (0 : Fin 2))).op
          have hi' := congrArg
            (fun k => k ≫ pFAt _)
            hi
          dsimp [cechNerveMapOfZero]
          change WidePullback.lift _ _ _ ≫ _ = _
          simp only [WidePullback.lift_π]
          rw [hdF]
          simpa [SimplicialObject.truncation, SimplicialObject.δ,
            SimplexCategory.δ_one_eq_const, SimplexCategory.δ_zero_eq_const,
            F, Arrow.cechNerve, Category.assoc, pF, pFAt,
            WidePullback.lift_π] using hi'
      · dsimp [cechNerveMapOfZero]
        change WidePullback.lift _ _ _ ≫ _ = _
        simp only [WidePullback.lift_base]
        have hε1 :
            (augmentationOfZero V (d.1 ≫ f)
              (by simpa only [Category.assoc] using d.2)).app
                (op (SimplexCategory.mk 1)) =
              V.map (SimplexCategory.const (SimplexCategory.mk 0)
                (SimplexCategory.mk 1) 0).op ≫ d.1 ≫ f := by
          simp [augmentationOfZero]
        have hi := g.naturality
          (SimplexCategory.Truncated.Hom.tr
            (SimplexCategory.δ (1 : Fin 2))).op
        have hi' := congrArg
          (fun k => k ≫ pFAt _) hi
        have hi'' := congrArg (fun k => k ≫ f) hi'
        rw [hε1, hdF]
        simpa [SimplicialObject.truncation, SimplicialObject.δ,
          SimplexCategory.δ_one_eq_const, SimplexCategory.δ_zero_eq_const,
          F, Arrow.cechNerve, Category.assoc, pF, pFAt,
          WidePullback.lift_π] using hi''
  · intro d
    let F : Arrow C := Arrow.mk f
    let : ∀ n : ℕ,
        HasWidePullback F.right
          (fun _ : Fin (n + 1) => F.left) (fun _ => F.hom) := by
      intro n
      change HasWidePullback X (fun _ : Fin (n + 1) => Y) (fun _ => f)
      exact h n
    apply Subtype.ext
    change (cechNerveZeroOfTruncatedMap f h V p₀
        ((SimplicialObject.truncation (C := C) 1).map
          (show V ⟶ F.cechNerve from cechNerveMapOfZero f h V d))).1 = d.1
    rw [cechNerveZeroOfTruncatedMap_fst f h V
      ((SimplicialObject.truncation (C := C) 1).map
        (show V ⟶ F.cechNerve from cechNerveMapOfZero f h V d)) p₀]
    change (cechNerveMapOfZero f h V d).app
        (op (SimplexCategory.mk 0)) ≫
      WidePullback.π (fun _ : Fin (0 + 1) => f) 0 = d.1
    dsimp [cechNerveMapOfZero]
    cases cechNerve_obj_formula f h 0
    change WidePullback.lift _ _ _ ≫ _ = _
    simp only [WidePullback.lift_π]
    have hconst : SimplexCategory.const (SimplexCategory.mk 0)
        (SimplexCategory.mk 0) 0 = 𝟙 (SimplexCategory.mk 0) := by
      apply SimplexCategory.Hom.ext_zero_left
      rfl
    rw [hconst]
    simp only [CategoryTheory.op_id, V.map_id, Category.id_comp]

private lemma cechNerve_truncated_map_of_zero {C : Type u} [Category.{v} C]
    {Y X : C} (f : Y ⟶ X) (h : HasCechNerve f)
    (V : SimplicialObject C)
    (p : SimplexCategory.len (SimplexCategory.mk 0) ≤ 1)
    (g : (SimplicialObject.truncation (C := C) 1).obj V ⟶
      (SimplicialObject.truncation (C := C) 1).obj (cechNerve f h)) :
    (SimplicialObject.truncation (C := C) 1).map
        (cechNerveMapOfZero f h V
          (cechNerveZeroOfTruncatedMap f h V p g)) = g := by
  let d := cechNerveZeroOfTruncatedMap f h V p g
  let F : Arrow C := Arrow.mk f
  let : ∀ n : ℕ,
      HasWidePullback F.right
        (fun _ : Fin (n + 1) => F.left) (fun _ => F.hom) := by
    intro n
    change HasWidePullback X (fun _ : Fin (n + 1) => Y) (fun _ => f)
    exact h n
  change (SimplicialObject.truncation (C := C) 1).obj V ⟶
    (SimplicialObject.truncation (C := C) 1).obj F.cechNerve at g
  have hd : d.1 =
      g.app (op ⟨SimplexCategory.mk 0, p⟩) ≫
        WidePullback.π (fun _ : Fin (0 + 1) => f) 0 := by
    dsimp [d, cechNerveZeroOfTruncatedMap]
    cases Formalization.Books.Simplicial.Unit03.cech_nerve_degree F 0
    rfl
  let pF :
      ((SimplicialObject.truncation (C := C) 1).obj F.cechNerve).obj
          (op ⟨SimplexCategory.mk 0, p⟩) ⟶ Y := by
    change F.cechNerve.obj (op (SimplexCategory.mk 0)) ⟶ Y
    rw [Formalization.Books.Simplicial.Unit03.cech_nerve_degree F 0]
    exact WidePullback.π (fun _ : Fin (0 + 1) => f) 0
  let pFAt : ∀ q : SimplexCategory.len (SimplexCategory.mk 0) ≤ 1,
      ((SimplicialObject.truncation (C := C) 1).obj F.cechNerve).obj
          (op ⟨SimplexCategory.mk 0, q⟩) ⟶ Y := fun q => by
    change F.cechNerve.obj (op (SimplexCategory.mk 0)) ⟶ Y
    rw [Formalization.Books.Simplicial.Unit03.cech_nerve_degree F 0]
    exact WidePullback.π (fun _ : Fin (0 + 1) => f) 0
  have hdF : d.1 =
      g.app (op ⟨SimplexCategory.mk 0, p⟩) ≫ pF := by
    dsimp [d, cechNerveZeroOfTruncatedMap, pF]
    cases cechNerve_obj_formula f h 0
    cases Formalization.Books.Simplicial.Unit03.cech_nerve_degree F 0
    rfl
  ext j
  rcases j with ⟨⟨⟨n⟩, hn⟩⟩
  have hn' : n ≤ 1 := by simpa only [SimplexCategory.len_mk] using hn
  rcases Nat.eq_zero_or_pos n with rfl | hnpos
  · change (cechNerveMapOfZero f h V d).app
        ((SimplexCategory.Truncated.inclusion 1).op.obj
          (op ⟨SimplexCategory.mk 0, hn⟩)) =
      g.app (op ⟨SimplexCategory.mk 0, hn⟩)
    cases cechNerve_obj_formula f h 0
    apply WidePullback.hom_ext _ _ _ ?_ ?_
    · intro i
      rcases i with ⟨i, hi⟩
      change i < 1 at hi
      have : i = 0 := by omega
      subst i
      dsimp [cechNerveMapOfZero]
      change WidePullback.lift _ _ _ ≫ _ = _
      simp only [WidePullback.lift_π]
      rw [hd]
      have hghn : g.app (op ⟨SimplexCategory.mk 0, p⟩) =
          g.app (op ⟨SimplexCategory.mk 0, hn⟩) :=
        truncated_app_proof_irrel
          (W := (SimplicialObject.truncation (C := C) 1).obj F.cechNerve)
          g 0 p hn
      have hconst : SimplexCategory.const (SimplexCategory.mk 0)
          (SimplexCategory.mk 0) 0 = 𝟙 (SimplexCategory.mk 0) := by
        apply SimplexCategory.Hom.ext_zero_left
        rfl
      rw [hconst]
      simp only [CategoryTheory.op_id, V.map_id]
      rw [hghn]
      exact Category.id_comp _
    · dsimp [cechNerveMapOfZero]
      change WidePullback.lift _ _ _ ≫ _ = _
      simp only [WidePullback.lift_base]
      have hε0 :
          (augmentationOfZero V (d.1 ≫ f)
            (by simpa only [Category.assoc] using d.2)).app
              (op (SimplexCategory.mk 0)) = d.1 ≫ f := by
        simp [augmentationOfZero]
      have hghn : g.app (op ⟨SimplexCategory.mk 0, p⟩) =
          g.app (op ⟨SimplexCategory.mk 0, hn⟩) :=
        truncated_app_proof_irrel
          (W := (SimplicialObject.truncation (C := C) 1).obj F.cechNerve)
          g 0 p hn
      have hpF : pF ≫ f =
          WidePullback.base (fun _ : Fin (0 + 1) => f) := by
        dsimp [pF]
        change WidePullback.π (fun _ : Fin (0 + 1) => f) 0 ≫ f = _
        rw [WidePullback.π_arrow]
      rw [hε0, hdF, hghn]
      change (g.app (op ⟨SimplexCategory.mk 0, hn⟩) ≫ pF) ≫ f = _
      rw [Category.assoc, hpF]
      rfl
  · have : n = 1 := by omega
    subst n
    change (cechNerveMapOfZero f h V d).app
        ((SimplexCategory.Truncated.inclusion 1).op.obj
          (op ⟨SimplexCategory.mk 1, hn⟩)) =
      g.app (op ⟨SimplexCategory.mk 1, hn⟩)
    cases Formalization.Books.Simplicial.Unit03.cech_nerve_degree F 1
    apply WidePullback.hom_ext _ _ _ ?_ ?_
    · intro i
      rcases i with ⟨i, hi⟩
      change i < 2 at hi
      have hicases : i = 0 ∨ i = 1 := by omega
      rcases hicases with rfl | rfl
      · have hi := g.naturality
          (SimplexCategory.Truncated.Hom.tr
            (SimplexCategory.δ (1 : Fin 2))).op
        have hi' := congrArg (fun k => k ≫ pFAt _) hi
        dsimp [cechNerveMapOfZero]
        change WidePullback.lift _ _ _ ≫ _ = _
        simp only [WidePullback.lift_π]
        rw [hdF]
        simpa [SimplicialObject.truncation, SimplicialObject.δ,
          SimplexCategory.δ_one_eq_const, SimplexCategory.δ_zero_eq_const,
          F, Arrow.cechNerve, Category.assoc, pF, pFAt,
          WidePullback.lift_π] using hi'
      · have hi := g.naturality
          (SimplexCategory.Truncated.Hom.tr
            (SimplexCategory.δ (0 : Fin 2))).op
        have hi' := congrArg (fun k => k ≫ pFAt _) hi
        dsimp [cechNerveMapOfZero]
        change WidePullback.lift _ _ _ ≫ _ = _
        simp only [WidePullback.lift_π]
        rw [hdF]
        simpa [SimplicialObject.truncation, SimplicialObject.δ,
          SimplexCategory.δ_one_eq_const, SimplexCategory.δ_zero_eq_const,
          F, Arrow.cechNerve, Category.assoc, pF, pFAt,
          WidePullback.lift_π] using hi'
    · dsimp [cechNerveMapOfZero]
      change WidePullback.lift _ _ _ ≫ _ = _
      simp only [WidePullback.lift_base]
      have hε1 :
          (augmentationOfZero V (d.1 ≫ f)
            (by simpa only [Category.assoc] using d.2)).app
              (op (SimplexCategory.mk 1)) =
            V.map (SimplexCategory.const (SimplexCategory.mk 0)
              (SimplexCategory.mk 1) 0).op ≫ d.1 ≫ f := by
        simp [augmentationOfZero]
      have hi := g.naturality
        (SimplexCategory.Truncated.Hom.tr
          (SimplexCategory.δ (1 : Fin 2))).op
      have hi' := congrArg (fun k => k ≫ pFAt _) hi
      have hi'' := congrArg (fun k => k ≫ f) hi'
      rw [hε1, hdF]
      simpa [SimplicialObject.truncation, SimplicialObject.δ,
        SimplexCategory.δ_one_eq_const, SimplexCategory.δ_zero_eq_const,
        F, Arrow.cechNerve, Category.assoc, pF, pFAt,
        WidePullback.lift_π] using hi''

/-- The combined source-facing hom-set description. -/
theorem cechNerve_hom_equiv_zero {C : Type u} [Category.{v} C]
    {Y X : C} (f : Y ⟶ X) (h : HasCechNerve f)
    (V : SimplicialObject C) :
    Nonempty ((V ⟶ cechNerve f h) ≃ CechNerveZeroMapData f V) := by
  refine ⟨Equiv.mk (cechNerveZeroOfMap f h V)
      (cechNerveMapOfZero f h V) ?_ ?_⟩
  · intro g
    let d := cechNerveZeroOfMap f h V g
    let F : Arrow C := Arrow.mk f
    let : ∀ n : ℕ,
        HasWidePullback F.right
          (fun _ : Fin (n + 1) => F.left) (fun _ => F.hom) := by
      intro n
      change HasWidePullback X (fun _ : Fin (n + 1) => Y) (fun _ => f)
      exact h n
    change cechNerveMapOfZero f h V d = g
    let A : Augmentation (cechNerve f h) X := F.augmentedCechNerve.hom
    let p₀ : (cechNerve f h).obj (op (SimplexCategory.mk 0)) ⟶ Y := by
      rw [cechNerve_obj_formula f h 0]
      exact WidePullback.π (fun _ : Fin (0 + 1) => f) 0
    have hp₀ : p₀ ≫ f =
        WidePullback.base (fun _ : Fin (0 + 1) => f) := by
      change (WidePullback.π (fun _ : Fin (0 + 1) => f) 0) ≫ f =
        WidePullback.base (fun _ : Fin (0 + 1) => f)
      simp only [WidePullback.π_arrow]
    have hd : d.1 = g.app (op (SimplexCategory.mk 0)) ≫ p₀ := by
      dsimp [d, cechNerveZeroOfMap, p₀]
    have hzero : d.1 ≫ f = (g ≫ A).app
        (op (SimplexCategory.mk 0)) := by
      rw [hd, Category.assoc, hp₀]
      change g.app (op (SimplexCategory.mk 0)) ≫
          WidePullback.base (fun _ : Fin (0 + 1) => f) =
        g.app (op (SimplexCategory.mk 0)) ≫
          WidePullback.base (fun _ : Fin (0 + 1) => f)
      rfl
    have haug : augmentationOfZero V (d.1 ≫ f)
        (by simpa only [Category.assoc] using d.2) = g ≫ A := by
      apply SimplicialObject.hom_ext
      intro n
      let q : SimplexCategory.mk 0 ⟶ n.unop :=
        SimplexCategory.const (SimplexCategory.mk 0) n.unop 0
      have hεn := (augmentationOfZero V (d.1 ≫ f)
        (by simpa only [Category.assoc] using d.2)).naturality q.op
      have hgn := (g ≫ A).naturality q.op
      have hε0 : (augmentationOfZero V (d.1 ≫ f)
          (by simpa only [Category.assoc] using d.2)).app
            (op (SimplexCategory.mk 0)) = d.1 ≫ f := by
        simp [augmentationOfZero]
      have hg0 : (g ≫ A).app
          (op (SimplexCategory.mk 0)) = d.1 ≫ f := hzero.symm
      rw [hε0] at hεn
      rw [hg0] at hgn
      simpa [q] using hεn.symm.trans hgn
    change V ⟶ F.cechNerve at g
    change (show V ⟶ F.cechNerve from cechNerveMapOfZero f h V d) = g
    let pF0 : F.cechNerve.obj (op (SimplexCategory.mk 0)) ⟶ Y := by
      rw [Formalization.Books.Simplicial.Unit03.cech_nerve_degree F 0]
      exact WidePullback.π (fun _ : Fin (0 + 1) => f) 0
    have hdF : d.1 = g.app (op (SimplexCategory.mk 0)) ≫ pF0 := by
      dsimp [d, cechNerveZeroOfMap, pF0]
      cases cechNerve_obj_formula f h 0
      cases Formalization.Books.Simplicial.Unit03.cech_nerve_degree F 0
      rfl
    apply SimplicialObject.hom_ext
    intro n
    rcases n with ⟨⟨n⟩⟩
    cases Formalization.Books.Simplicial.Unit03.cech_nerve_degree F n
    cases cechNerve_obj_formula f h n
    apply WidePullback.hom_ext _ _ _ (fun i => ?_) ?_
    · dsimp [cechNerveMapOfZero]
      dsimp [F]
      change WidePullback.lift _ _ _ ≫ _ = _
      simp only [WidePullback.lift_base]
      have hn := congrArg
        (fun k => k.app (op (SimplexCategory.mk n))) haug
      have hbase : A.app (op (SimplexCategory.mk n)) =
          WidePullback.base (fun _ : Fin (n + 1) => f) := by
        change (F.augmentedCechNerve.hom).app
            (op (SimplexCategory.mk n)) = _
        dsimp [F, Arrow.augmentedCechNerve]
      have hcomp : (g ≫ A).app (op (SimplexCategory.mk n)) =
          g.app (op (SimplexCategory.mk n)) ≫
            A.app (op (SimplexCategory.mk n)) := by rfl
      exact hn.trans (hcomp.trans (by rw [hbase]))
    · dsimp [cechNerveMapOfZero]
      dsimp [F]
      change WidePullback.lift _ _ _ ≫ _ = _
      simp only [WidePullback.lift_π]
      have hi := g.naturality
        (SimplexCategory.const (SimplexCategory.mk 0)
          (SimplexCategory.mk n) i).op
      have hi' := congrArg (fun k => k ≫ pF0) hi
      rw [hdF]
      simp [F, Arrow.cechNerve, pF0, WidePullback.lift_π]
  · intro d
    apply Subtype.ext
    simp only [cechNerveZeroOfMap]
    change (cechNerveMapOfZero f h V d).app
        (op (SimplexCategory.mk 0)) ≫
      WidePullback.π (fun _ : Fin (0 + 1) => f) 0 = d.1
    dsimp [cechNerveMapOfZero]
    cases cechNerve_obj_formula f h 0
    change WidePullback.lift _ _ _ ≫ _ = _
    simp only [WidePullback.lift_π]
    have hconst : SimplexCategory.const (SimplexCategory.mk 0)
        (SimplexCategory.mk 0) 0 = 𝟙 (SimplexCategory.mk 0) := by
      apply SimplexCategory.Hom.ext_zero_left
      rfl
    rw [hconst]
    simp only [CategoryTheory.op_id, V.map_id, Category.id_comp]

/-- The first equality in the source's displayed formula, expressed as an
equivalence with the degree-one truncation hom-set. -/
theorem cechNerve_hom_equiv_truncated {C : Type u} [Category.{v} C]
    {Y X : C} (f : Y ⟶ X) (h : HasCechNerve f)
    (V : SimplicialObject C) :
    Nonempty ((V ⟶ cechNerve f h) ≃
      ((SimplicialObject.truncation (C := C) 1).obj V ⟶
        (SimplicialObject.truncation (C := C) 1).obj (cechNerve f h))) := by
  let e₃ := (cechNerve_hom_equiv_zero f h V).some
  let e₂ := (cechNerve_truncated_hom_equiv_zero f h V).some
  exact ⟨e₃.trans e₂.symm⟩

/-- The Čech nerve is one-coskeletal.  This right-extension formulation does
not require a globally chosen `cosk₁` functor. -/
theorem cechNerve_is_one_coskeletal {C : Type u} [Category.{v} C]
    {Y X : C} (f : Y ⟶ X) (h : HasCechNerve f) :
    SimplicialObject.IsCoskeletal (cechNerve f h) 1 := by
  let p₀ : SimplexCategory.len (SimplexCategory.mk 0) ≤ 1 := by simp
  constructor
  refine Functor.IsRightKanExtension.mk ⟨?_⟩
  refine IsTerminal.ofUniqueHom (fun e => ?_) (fun e m => ?_)
  · let g : (SimplicialObject.truncation (C := C) 1).obj e.left ⟶
        (SimplicialObject.truncation (C := C) 1).obj (cechNerve f h) := by
      change ((SimplexCategory.Truncated.inclusion 1).op ⋙ e.left) ⟶
        ((SimplexCategory.Truncated.inclusion 1).op ⋙ cechNerve f h)
      exact e.hom
    let η : e.left ⟶ cechNerve f h :=
      cechNerveMapOfZero f h e.left
        (cechNerveZeroOfTruncatedMap f h e.left p₀ g)
    refine CostructuredArrow.homMk η ?_
    change (SimplicialObject.truncation (C := C) 1).map η ≫ 𝟙 _ = e.hom
    rw [Category.comp_id]
    change (SimplicialObject.truncation (C := C) 1).map η = g
    exact cechNerve_truncated_map_of_zero f h e.left p₀ g
  · dsimp
    apply CostructuredArrow.hom_ext
    let g : (SimplicialObject.truncation (C := C) 1).obj e.left ⟶
        (SimplicialObject.truncation (C := C) 1).obj (cechNerve f h) := by
      change ((SimplexCategory.Truncated.inclusion 1).op ⋙ e.left) ⟶
        ((SimplexCategory.Truncated.inclusion 1).op ⋙ cechNerve f h)
      exact e.hom
    let η : e.left ⟶ cechNerve f h :=
      cechNerveMapOfZero f h e.left
        (cechNerveZeroOfTruncatedMap f h e.left p₀ g)
    let μ : e.left ⟶ cechNerve f h := by
      exact m.left
    change m.left = cechNerveMapOfZero f h e.left
      (cechNerveZeroOfTruncatedMap f h e.left p₀ (id e.hom))
    change μ = η
    have hm' := CostructuredArrow.w m
    dsimp [Functor.RightExtension.mk] at hm'
    rw [Category.comp_id] at hm'
    have hμ :
        (SimplexCategory.Truncated.inclusion 1).op.whiskerLeft μ = e.hom := by
      dsimp [μ, Functor.RightExtension.mk]
      exact hm'
    have hη :
        (SimplexCategory.Truncated.inclusion 1).op.whiskerLeft η = e.hom := by
      change (SimplicialObject.truncation (C := C) 1).map η = g
      exact cechNerve_truncated_map_of_zero f h e.left p₀ g
    have hzero : μ.app (op (SimplexCategory.mk 0)) =
        η.app (op (SimplexCategory.mk 0)) := by
      have hzero' := congrArg
        (fun k => k.app (op ⟨SimplexCategory.mk 0, p₀⟩))
        (hμ.trans hη.symm)
      change μ.app (op (SimplexCategory.mk 0)) =
        η.app (op (SimplexCategory.mk 0)) at hzero'
      exact hzero'
    apply SimplicialObject.hom_ext
    intro n
    rcases n with ⟨⟨n⟩⟩
    let F : Arrow C := Arrow.mk f
    let : ∀ n : ℕ,
        HasWidePullback F.right
          (fun _ : Fin (n + 1) => F.left) (fun _ => F.hom) := by
      intro n
      change HasWidePullback X (fun _ : Fin (n + 1) => Y) (fun _ => f)
      exact h n
    change e.left ⟶ F.cechNerve at μ
    change e.left ⟶ F.cechNerve at η
    cases Formalization.Books.Simplicial.Unit03.cech_nerve_degree F n
    change μ.app (op (SimplexCategory.mk n)) =
      η.app (op (SimplexCategory.mk n))
    have hproj : ∀ i : Fin (n + 1),
        μ.app (op (SimplexCategory.mk n)) ≫
            WidePullback.π (fun _ : Fin (n + 1) => f) i =
          η.app (op (SimplexCategory.mk n)) ≫
            WidePullback.π (fun _ : Fin (n + 1) => f) i := by
      intro i
      let q : SimplexCategory.mk 0 ⟶ SimplexCategory.mk n :=
          SimplexCategory.const (SimplexCategory.mk 0)
            (SimplexCategory.mk n) i
      have hmq := μ.naturality q.op
      change e.left.map q.op ≫ μ.app (op (SimplexCategory.mk 0)) =
          μ.app (op (SimplexCategory.mk n)) ≫
            F.cechNerve.map q.op at hmq
      have hηq := η.naturality q.op
      let pF0 : F.cechNerve.obj (op (SimplexCategory.mk 0)) ⟶ Y := by
        rw [Formalization.Books.Simplicial.Unit03.cech_nerve_degree F 0]
        exact WidePullback.π (fun _ : Fin (0 + 1) => f) 0
      have hmq' := congrArg
        (fun k => k ≫ pF0) hmq
      have hηq' := congrArg
        (fun k => k ≫ pF0) hηq
      have hpi : F.cechNerve.map q.op ≫ pF0 =
          WidePullback.π (fun _ : Fin (n + 1) => f) i := by
        dsimp [F, Arrow.cechNerve, pF0]
        change WidePullback.lift _ _ _ ≫ _ = _
        rw [WidePullback.lift_π]
        congr 1
      have hmq'' :
          μ.app (op (SimplexCategory.mk n)) ≫
              WidePullback.π (fun _ : Fin (n + 1) => f) i =
            e.left.map q.op ≫ μ.app (op (SimplexCategory.mk 0)) ≫
              pF0 := by
        rw [← hpi]
        simpa only [Category.assoc] using hmq'.symm
      have hηq'' :
          η.app (op (SimplexCategory.mk n)) ≫
              WidePullback.π (fun _ : Fin (n + 1) => f) i =
            e.left.map q.op ≫ η.app (op (SimplexCategory.mk 0)) ≫
              pF0 := by
        rw [← hpi]
        simpa only [Category.assoc] using hηq'.symm
      rw [hmq'', hzero, hηq'']
    apply WidePullback.hom_ext _ _ _ ?_ ?_
    · intro i
      exact hproj i
    · have hb := congrArg
        (fun k => k ≫ f) (hproj (0 : Fin (n + 1)))
      have hbase : WidePullback.π (fun _ : Fin (n + 1) => f) 0 ≫ f =
          WidePullback.base (fun _ : Fin (n + 1) => f) := by
        rw [WidePullback.π_arrow]
      calc
        μ.app (op (SimplexCategory.mk n)) ≫
              WidePullback.base (fun _ : Fin (n + 1) => f) =
            (μ.app (op (SimplexCategory.mk n)) ≫
              WidePullback.π (fun _ : Fin (n + 1) => f) 0) ≫ f := by
                rw [Category.assoc, hbase]
        _ = (η.app (op (SimplexCategory.mk n)) ≫
              WidePullback.π (fun _ : Fin (n + 1) => f) 0) ≫ f := hb
        _ = η.app (op (SimplexCategory.mk n)) ≫
              WidePullback.base (fun _ : Fin (n + 1) => f) := by
                rw [Category.assoc, hbase]

/-- When the chosen degree-one coskeleton exists, this is the canonical
isomorphism corresponding to the source's `U = cosk₁ sk₁ U`. -/
noncomputable def cechNerveCoskeletonIso {C : Type u} [Category.{v} C]
    {Y X : C} (f : Y ⟶ X) (h : HasCechNerve f)
    [∀ W : SimplicialObject.Truncated C 1,
      Formalization.Books.Simplicial.Unit19.HasCoskeleton 1 W] :
    cechNerve f h ≅
      (SimplicialObject.Truncated.cosk (C := C) 1).obj
        ((SimplicialObject.truncation (C := C) 1).obj (cechNerve f h)) := by
  letI : (cechNerve f h).IsCoskeletal 1 :=
    cechNerve_is_one_coskeletal f h
  exact SimplicialObject.isoCoskOfIsCoskeletal
    (X := cechNerve f h) (n := 1)

/-! ## The canonical map associated to an augmentation -/

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The canonical map from an augmented simplicial object to the Čech nerve
of its degree-zero augmentation. -/
noncomputable def augmentationToCechNerve {C : Type u} [Category.{v} C]
    {V : SimplicialObject C} {X : C} (ε : Augmentation V X)
    (h : HasCechNerve (augmentationAtZero ε)) :
    V ⟶ cechNerve (augmentationAtZero ε) h := by
  let A : SimplicialObject.Augmented C := augmentationAsAugmented ε
  let F : Arrow C := Arrow.mk (augmentationAtZero ε)
  letI : ∀ n : ℕ,
      HasWidePullback F.right
        (fun _ : Fin (n + 1) => F.left) (fun _ => F.hom) := by
    intro n
    change HasWidePullback X
      (fun _ : Fin (n + 1) => V.obj (op (SimplexCategory.mk 0)))
      (fun _ => augmentationAtZero ε)
    exact h n
  let G : SimplicialObject.Augmented.toArrow.obj A ⟶ F := eqToHom (by rfl)
  let η : A ⟶ F.augmentedCechNerve :=
    { left :=
        { app := fun x =>
            WidePullback.lift (A.hom.app _ ≫ G.right)
              (fun i =>
                A.left.map (SimplexCategory.const _ x.unop i).op ≫ G.left)
              (by
                intro i
                simp)
          naturality := by
            intro x y g
            dsimp
            refine WidePullback.hom_ext _ _ _ (fun j => ?_) ?_
            · simp only [WidePullback.lift_π, Category.assoc,
                ← A.left.map_comp_assoc]
              rfl
            · simp }
      right := G.right }
  simpa [cechNerve, A, F, G, augmentationAsAugmented, augmentationAtZero] using η.left

end Formalization.Books.Simplicial.Unit20
