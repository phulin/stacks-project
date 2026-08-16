import Formalization.Books.Stacks.Unit01.InheritedTopology
import Mathlib.Algebra.Category.Grp.Basic

/-!
# Stacks, Chapter 1, Section 11: gerbes
-/

namespace Formalization.Books.Stacks.Unit01

open CategoryTheory
open Opposite

open scoped CategoryTheory.Pseudofunctor.StrongTrans

universe t w v u

def LocallyNonempty {C : Type u} [Category.{v} C]
    (F : FiberedCategory.{w, v, u} C) (J : GrothendieckTopology C) : Prop :=
  ∀ U : C, ∃ (ι : Type t) (X : ι → C) (f : ∀ i, X i ⟶ U),
    CoveringFamily J f ∧ ∀ i, Nonempty (Fiber F (X i))

def LocallyIsomorphic {C : Type u} [Category.{v} C]
    (F : FiberedCategory.{w, v, u} C) (J : GrothendieckTopology C) : Prop :=
  ∀ (U : C) (x y : Fiber F U),
    ∃ (ι : Type t) (X : ι → C) (f : ∀ i, X i ⟶ U),
      CoveringFamily J f ∧
        ∀ i, Nonempty
          ((F.map (f i).op.toLoc).toFunctor.obj x ≅
            (F.map (f i).op.toLoc).toFunctor.obj y)

def IsGerbe {C : Type u} [Category.{v} C]
    (F : FiberedCategory.{w, v, u} C) (J : GrothendieckTopology C) : Prop :=
  StackInGroupoids F J ∧
    LocallyNonempty.{t, w, v, u} F J ∧
      LocallyIsomorphic.{t, w, v, u} F J

def FiberedInGroupoidsOver {C : Type u} [Category.{v} C]
    {F G : FiberedCategory.{w, v, u} C} (η : FiberedMorphism F G) : Prop :=
  ∀ (U : C) (y : Fiber G U) (x x' : Fiber F U)
    (a : (η.app (.mk (op U))).toFunctor.obj x ⟶ y)
    (a' : (η.app (.mk (op U))).toFunctor.obj x' ⟶ y)
    (f : x ⟶ x'),
    (η.app (.mk (op U))).toFunctor.map f ≫ a' = a →
      ∃ g : x' ⟶ x,
        (η.app (.mk (op U))).toFunctor.map g ≫ a = a' ∧
          f ≫ g = 𝟙 _ ∧ g ≫ f = 𝟙 _

def LocallyLiftsMorphisms {C : Type u} [Category.{v} C]
    {F G : FiberedCategory.{w, v, u} C} (η : FiberedMorphism F G)
    (J : GrothendieckTopology C) : Prop :=
  ∀ (U : C) (x x' : Fiber F U)
    (b : (η.app (.mk (op U))).toFunctor.obj x ⟶
      (η.app (.mk (op U))).toFunctor.obj x'),
    ∃ (ι : Type t) (X : ι → C) (f : ∀ i, X i ⟶ U),
      CoveringFamily J f ∧
        ∀ i, ∃ a : (F.map (f i).op.toLoc).toFunctor.obj x ⟶
            (F.map (f i).op.toLoc).toFunctor.obj x',
          (η.app (.mk (op (X i)))).toFunctor.map a =
            ((η.naturality (f i).op.toLoc).hom.toNatTrans.app x) ≫
              (G.map (f i).op.toLoc).toFunctor.map b ≫
              ((η.naturality (f i).op.toLoc).inv.toNatTrans.app x')

def GerbeOver {C : Type u} [Category.{v} C]
    {F G : FiberedCategory.{w, v, u} C} (η : FiberedMorphism F G)
    (J : GrothendieckTopology C) : Prop :=
  StackInGroupoids F J ∧ StackInGroupoids G J ∧
    LocallyEssentiallyInImage.{t, v, u, w} η J ∧
      LocallyLiftsMorphisms.{t, w, v, u} η J

structure GerbeFactorizationData {C : Type u} [Category.{v} C]
    {F G : FiberedCategory.{w, v, u} C} (η : FiberedMorphism F G)
    (J : GrothendieckTopology C) where
  value : FiberedCategory.{w, v, u} C
  fromOriginal : FiberedMorphism F value
  toBase : FiberedMorphism value G
  factorization : Nonempty (fromOriginal ≫ toBase ≅ η)
  isGerbe : IsGerbe.{t, w, v, u} value J
  equivalentToOriginal : FiberwiseEquivalence fromOriginal
  fibredInGroupoidsOverBase : FiberedInGroupoidsOver toBase
  locallyEssentiallyInImage : LocallyEssentiallyInImage.{t, v, u, w} toBase J
  locallyLiftsMorphisms : LocallyLiftsMorphisms.{t, w, v, u} toBase J

def AutomorphismGroupsAbelian {C : Type u} [Category.{v} C]
    (F : FiberedCategory.{w, v, u} C) : Prop :=
  ∀ (U : C) (x : Fiber F U) (a b : Aut x), a * b = b * a

def automorphismSheafPresheaf {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C) (A : Sheaf J AddCommGrpCat.{w}) (U : C) :
    (Over C U)ᵒᵖ ⥤ Type w :=
  (A.over U).obj ⋙ (forget AddCommGrpCat)

noncomputable def conjugateAutomorphism {C : Type u} [Category.{v} C]
    {F : FiberedCategory.{w, v, u} C} (hF : FiberwiseGroupoid F) {U : C}
    {x y : Fiber F U} (φ : x ⟶ y) (a : Aut x) : Aut y := by
  letI := hF U
  exact (asIso φ).symm.trans (a.trans (asIso φ))

theorem conjugation_presheaf_map_exists {C : Type u} [Category.{v} C]
    {F : FiberedCategory.{w, v, u} C} (hF : FiberwiseGroupoid F) {U : C}
    {x y : Fiber F U} (φ : x ⟶ y) :
    Nonempty (IsomPresheaf F x x ⟶ IsomPresheaf F y y) := by
  sorry

noncomputable def conjugationPresheafMap {C : Type u} [Category.{v} C]
    {F : FiberedCategory.{w, v, u} C} (hF : FiberwiseGroupoid F) {U : C}
    {x y : Fiber F U} (φ : x ⟶ y) :
    IsomPresheaf F x x ⟶ IsomPresheaf F y y :=
  Classical.choice (conjugation_presheaf_map_exists hF φ)

structure GerbeAutomorphismSheafData {C : Type u} [Category.{v} C]
    (F : FiberedCategory.{w, v, u} C) (J : GrothendieckTopology C)
    (hF : FiberwiseGroupoid F) where
  sheaf : Sheaf J AddCommGrpCat.{w}
  localIdentifications : ∀ (U : C) (x : Fiber F U),
    automorphismSheafPresheaf J sheaf U ≅ IsomPresheaf F x x
  conjugationCompatible : ∀ (U : C) (x y : Fiber F U) (φ : x ⟶ y),
    (localIdentifications U x).hom ≫ conjugationPresheafMap hF φ =
      (localIdentifications U y).hom

theorem equivalent_gerbes_preserve
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    {F G : FiberedCategory.{w, v, u} C} (η : FiberedMorphism F G)
    (hη : FiberwiseEquivalence η) :
    IsGerbe F J ↔ IsGerbe G J := by
  sorry

theorem gerbe_characterization_by_factorization
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    {F G : FiberedCategory.{w, v, u} C} (η : FiberedMorphism F G) :
    GerbeOver η J ↔ Nonempty (GerbeFactorizationData η J) := by
  sorry

theorem base_change_of_gerbe
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    {A B C' D : FiberedCategory.{w, v, u} C}
    (sq : TwoCartesianSquare A B C' D)
    (hgerbe : GerbeOver sq.top J) :
    GerbeOver sq.right J := by
  sorry

theorem composition_of_gerbes
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    {F G H : FiberedCategory.{w, v, u} C} (η : FiberedMorphism F G)
    (θ : FiberedMorphism G H) (hη : GerbeOver η J)
    (hθ : GerbeOver θ J) :
    GerbeOver (η ≫ θ) J := by
  sorry

theorem gerbe_descent
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    {A B C' D : FiberedCategory.{w, v, u} C} (sq : TwoCartesianSquare A B C' D)
    (hlocal : LocallyEssentiallyInImage sq.bottom J)
    (hgerbe : GerbeOver sq.bottom J) :
    GerbeOver sq.left J := by
  sorry

theorem gerbe_abelian_automorphisms
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    {F : FiberedCategory.{w, v, u} C} (hF : IsGerbe F J)
    (hAb : AutomorphismGroupsAbelian F) :
    Nonempty (GerbeAutomorphismSheafData F J hF.1.1) := by
  sorry

end Formalization.Books.Stacks.Unit01
