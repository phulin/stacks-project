import Formalization.Books.Simplicial.Unit19.CoskeletonFunctors
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
source's displayed compatibility diagram. -/
theorem cechNerveCoordinate_one_faces {C : Type u} [Category.{v} C]
    (V : SimplicialObject C)
    {Y : C} (g₀ : V.obj (op (SimplexCategory.mk 0)) ⟶ Y) (i : Fin 2) :
    cechNerveCoordinate V g₀ 1 i = V.δ i ≫ g₀ := by
  sorry

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
  let A : SimplicialObject.Augmented C := augmentationAsAugmented ε
  let F : Arrow C := Arrow.mk f
  letI : ∀ n : ℕ,
      HasWidePullback F.right
        (fun _ : Fin (n + 1) => F.left) (fun _ => F.hom) := by
    intro n
    change HasWidePullback X (fun _ : Fin (n + 1) => Y) (fun _ => f)
    exact h n
  let G₀ : Arrow.mk (ε.app (op (SimplexCategory.mk 0))) ⟶ F :=
    { left := d.1
      right := 𝟙 X
      w := by
        simp [F, hε0] }
  let G : SimplicialObject.Augmented.toArrow.obj A ⟶ F :=
    { left := d.1
      right := G₀.right
      w := by
        simpa [SimplicialObject.Augmented.toArrow, A,
          augmentationAsAugmented, F, G₀, Category.assoc] using G₀.w }
  let η : A ⟶ F.augmentedCechNerve :=
    { left :=
        { app := fun x =>
            WidePullback.lift (A.hom.app _ ≫ G.right)
            (fun i =>
                A.left.map (SimplexCategory.const _ x.unop i).op ≫
                  G.left)
              (by
                intro i
                let q : SimplexCategory.mk 0 ⟶ x.unop :=
                  SimplexCategory.const (SimplexCategory.mk 0) x.unop i
                simpa only [G, G₀, F, SimplicialObject.Augmented.toArrow,
                  A, augmentationAsAugmented, Category.assoc,
                  Category.comp_id] using A.hom.naturality q.op)
          naturality := by
            intro x y q
            dsimp
            refine WidePullback.hom_ext _ _ _ (fun j => ?_) ?_
            · simp only [WidePullback.lift_π, Category.assoc,
                ← A.left.map_comp_assoc]
              rfl
            · simp }
      right := G.right }
  change V ⟶ F.cechNerve
  exact eqToHom (by rfl) ≫ η.left

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
  let d := (augmentation_hom_equiv V X).some.toFun ε
  refine ⟨g.app (op (SimplexCategory.mk 0)) ≫
      WidePullback.π (fun _ : Fin (0 + 1) => f) 0, ?_⟩
  have hd := d.2
  simpa [cechNerve, A, F, ε, Category.assoc] using hd

/-! ## The hom-set and coskeleton statements -/

/-- The first equality in the source's displayed formula, expressed as an
equivalence with the degree-one truncation hom-set. -/
theorem cechNerve_hom_equiv_truncated {C : Type u} [Category.{v} C]
    {Y X : C} (f : Y ⟶ X) (h : HasCechNerve f)
    (V : SimplicialObject C) :
    Nonempty ((V ⟶ cechNerve f h) ≃
      ((SimplicialObject.truncation (C := C) 1).obj V ⟶
        (SimplicialObject.truncation (C := C) 1).obj (cechNerve f h))) := by
  sorry

/-- The second equality in the source's displayed formula, expressed as an
equivalence from the truncated hom-set to the degree-zero data. -/
theorem cechNerve_truncated_hom_equiv_zero {C : Type u} [Category.{v} C]
    {Y X : C} (f : Y ⟶ X) (h : HasCechNerve f)
    (V : SimplicialObject C) :
    Nonempty (((SimplicialObject.truncation (C := C) 1).obj V ⟶
        (SimplicialObject.truncation (C := C) 1).obj (cechNerve f h)) ≃
      CechNerveZeroMapData f V) := by
  sorry

/-- The combined source-facing hom-set description. -/
theorem cechNerve_hom_equiv_zero {C : Type u} [Category.{v} C]
    {Y X : C} (f : Y ⟶ X) (h : HasCechNerve f)
    (V : SimplicialObject C) :
    Nonempty ((V ⟶ cechNerve f h) ≃ CechNerveZeroMapData f V) := by
  refine ⟨{ toFun := cechNerveZeroOfMap f h V,
    invFun := cechNerveMapOfZero f h V,
    left_inv := by
      intro g
      let d := cechNerveZeroOfMap f h V g
      change cechNerveMapOfZero f h V d = g
      apply SimplicialObject.hom_ext
      intro n
      apply WidePullback.hom_ext _ _ _ (fun i => ?_) ?_
      · intro i
        simp [cechNerveMapOfZero, cechNerve, Category.assoc]
      · simp [cechNerveMapOfZero, cechNerve, Category.assoc]
    right_inv := by
      intro d
      apply Subtype.ext
      simp only [cechNerveZeroOfMap]
      dsimp
      simp [cechNerve, Category.assoc] }⟩

/-- The Čech nerve is one-coskeletal.  This right-extension formulation does
not require a globally chosen `cosk₁` functor. -/
theorem cechNerve_is_one_coskeletal {C : Type u} [Category.{v} C]
    {Y X : C} (f : Y ⟶ X) (h : HasCechNerve f) :
    SimplicialObject.IsCoskeletal (cechNerve f h) 1 := by
  sorry

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
