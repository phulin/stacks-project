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
  sorry

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
  sorry

/-- The general adjacent-coordinate equality used in the source's
construction of a map into the iterated fibre product. -/
theorem cechNerveCoordinate_adjacent {C : Type u} [Category.{v} C]
    {Y X : C} (f : Y ⟶ X) (V : SimplicialObject C)
    (g₀ : V.obj (op (SimplexCategory.mk 0)) ⟶ Y)
    (hg : V.δ (0 : Fin 2) ≫ g₀ ≫ f = V.δ (1 : Fin 2) ≫ g₀ ≫ f)
    {n : ℕ} (i : Fin n) :
    cechNerveCoordinate V g₀ n (Fin.castSucc i) ≫ f =
      cechNerveCoordinate V g₀ n i.succ ≫ f := by
  sorry

/-- The degree-zero maps satisfying the relation in the source's displayed
hom-set formula. -/
abbrev CechNerveZeroMapData {C : Type u} [Category.{v} C]
    {Y X : C} (f : Y ⟶ X) (V : SimplicialObject C) : Type _ :=
  { g₀ : V.obj (op (SimplexCategory.mk 0)) ⟶ Y //
    V.δ (0 : Fin 2) ≫ g₀ ≫ f = V.δ (1 : Fin 2) ≫ g₀ ≫ f }

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
  sorry

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
