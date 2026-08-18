import Formalization.Books.Sheaves.Unit15.AlgebraicStructures
import Formalization.Books.Sheaves.Unit16.ExactnessAndPoints
import Formalization.Books.Sheaves.Unit25.Infrastructure
import Mathlib.Algebra.Category.ModuleCat.Stalk
import Mathlib.CategoryTheory.Monoidal.Ring
import Mathlib.CategoryTheory.Monoidal.Cartesian.Mod
import Mathlib.CategoryTheory.Sites.CartesianMonoidal

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open MonoidalCategory CartesianMonoidalCategory
open Formalization.Books.Sheaves.Unit05
open Formalization.Books.Sheaves.Unit10
open Formalization.Books.Sheaves.Unit13
open Formalization.Books.Sheaves.Unit15
open Formalization.Books.Sheaves.Unit16
open Formalization.Books.Sheaves.Unit22
open scoped CategoryTheory.AddMonObj CategoryTheory.ModObj CategoryTheory.MonObj
  CategoryTheory.RingObj

namespace Formalization.Books.Modules.Unit15

universe v

noncomputable section

noncomputable def sheafProductSectionsEquiv {X : TopCat.{v}}
    (F G : TopCat.Sheaf (Type v) X) (U : Opens X) :
    (((TopCat.Sheaf.forget (Type v) X).obj (limit (pair F G))).obj
      (op U) : Type v) ≃
      (F.presheaf.obj (op U) : Type v) ×
        (G.presheaf.obj (op U) : Type v) := by
  let e₁ := (preservesLimitIso (TopCat.Sheaf.forget (Type v) X)
    (pair F G)).app (op U)
  let e₁' := HasLimit.isoOfNatIso (Discrete.compNatIsoDiscrete
    (fun j : WalkingPair => (pair F G).obj (Discrete.mk j))
    (TopCat.Sheaf.forget (Type v) X))
  let e₂ := preservesLimitIso
    ((evaluation ((Opens X)ᵒᵖ) (Type v)).obj (op U))
    (Discrete.functor ((TopCat.Sheaf.forget (Type v) X).obj ∘ fun j : WalkingPair =>
      (pair F G).obj (Discrete.mk j)))
  let e₃ := HasLimit.isoOfNatIso (Discrete.compNatIsoDiscrete
    (fun j : WalkingPair =>
      (TopCat.Sheaf.forget (Type v) X).obj
        ((pair F G).obj (Discrete.mk j)))
    ((evaluation ((Opens X)ᵒᵖ) (Type v)).obj (op U)))
  let e₄ := (Types.productIso (fun j : WalkingPair =>
    ((evaluation ((Opens X)ᵒᵖ) (Type v)).obj (op U)).obj
      ((TopCat.Sheaf.forget (Type v) X).obj
        ((pair F G).obj (Discrete.mk j))))).toEquiv
  let e₅ : (∀ j : WalkingPair,
      ((evaluation ((Opens X)ᵒᵖ) (Type v)).obj (op U)).obj
        ((TopCat.Sheaf.forget (Type v) X).obj
          ((pair F G).obj (Discrete.mk j)))) ≃
      (F.presheaf.obj (op U) : Type v) ×
        (G.presheaf.obj (op U) : Type v) := {
    toFun := fun s => (s WalkingPair.left, s WalkingPair.right)
    invFun := fun p j => match j with
      | WalkingPair.left => p.1
      | WalkingPair.right => p.2
    left_inv := by
      intro s
      funext j
      cases j <;> rfl
    right_inv := by
      intro p
      rcases p with ⟨p, q⟩
      rfl }
  exact e₁.toEquiv.trans ((e₁'.app (op U)).toEquiv.trans
    (e₂.toEquiv.trans (e₃.toEquiv.trans (e₄.trans e₅))))

/-! ## Sectionwise bilinear maps -/

/-
The sheaf of rings API available for ringed spaces uses `RingCat`, so the
sectionwise interface is written with the existing `LinearMap` API over a
ring.  The curried type is the usual definition of a map linear in each
variable and does not impose an unmentioned commutativity hypothesis.
-/
structure SectionBilinearMap (R M N P : Type v) [Ring R]
    [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
    [Module R M] [Module R N] [Module R P] where
  toFun : M → N → P
  map_add_left' : ∀ (x y : M) (z : N),
    toFun (x + y) z = toFun x z + toFun y z
  map_smul_left' : ∀ (r : R) (x : M) (z : N),
    toFun (r • x) z = r • toFun x z
  map_add_right' : ∀ (x : M) (y z : N),
    toFun x (y + z) = toFun x y + toFun x z
  map_smul_right' : ∀ (r : R) (x : M) (y : N),
    toFun x (r • y) = r • toFun x y

instance {R M N P : Type v} [Ring R]
    [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
    [Module R M] [Module R N] [Module R P] :
    CoeFun (SectionBilinearMap R M N P) (fun _ => M → N → P) :=
  ⟨SectionBilinearMap.toFun⟩

/-! The underlying sheaf of sets of a sheaf of modules. -/
noncomputable def moduleSetSheaf {X : TopCat.{v}}
    {O : RingSheaf.{v, v} X} (F : Mod O) :
    TopCat.Sheaf (Type v) X := by
  letI : AlgebraicStructureType AddCommGrpCat (forget AddCommGrpCat) :=
    (standardAlgebraicStructureTypes.{v, v, v}).2.1
  exact underlyingSheaf (forget AddCommGrpCat)
    ((SheafOfModules.toSheaf O).obj F)

/-! The underlying sheaf of sets of the structure sheaf. -/
noncomputable def ringSetSheaf {X : TopCat.{v}}
    (O : RingSheaf.{v, v} X) : TopCat.Sheaf (Type v) X := by
  letI : AlgebraicStructureType RingCat (forget RingCat) :=
    (standardAlgebraicStructureTypes.{v, v, v}).2.2.2.2.1
  exact underlyingSheaf (forget RingCat) O

/-! The product of two underlying sheaves of sets. -/
noncomputable abbrev moduleSetProduct {X : TopCat.{v}}
    {O : RingSheaf.{v, v} X} (F G : Mod O) :
    TopCat.Sheaf (Type v) X :=
  limit (pair (moduleSetSheaf F) (moduleSetSheaf G))

/-! The set-valued sheaf map underlying a prospective bilinear map. -/
abbrev ModuleSetMap {X : TopCat.{v}}
    {O : RingSheaf.{v, v} X} (F G H : Mod O) :=
  moduleSetProduct F G ⟶ moduleSetSheaf H

/-! The product of two morphisms from a sheaf of sets. -/
noncomputable def sheafHomProduct {X : TopCat.{v}}
    {O : RingSheaf.{v, v} X} {F G : Mod O}
    (S : TopCat.Sheaf (Type v) X)
    (a : S ⟶ moduleSetSheaf F) (b : S ⟶ moduleSetSheaf G) :
    S ⟶ moduleSetProduct F G :=
  limit.lift (pair (moduleSetSheaf F) (moduleSetSheaf G))
    (BinaryFan.mk a b)

/-! The Hom-set rule `(a, b) ↦ f ∘ (a × b)`. -/
noncomputable def sheafHomBilinearRule {X : TopCat.{v}}
    {O : RingSheaf.{v, v} X} {F G H : Mod O}
    (f : ModuleSetMap F G H) (S : TopCat.Sheaf (Type v) X)
    (a : S ⟶ moduleSetSheaf F) (b : S ⟶ moduleSetSheaf G) :
    S ⟶ moduleSetSheaf H :=
  sheafHomProduct S a b ≫ f

/-! A Hom-set formulation of bilinearity.  The bracketed structures are the
algebraic structures on the Hom sets; `IsHomCharacterization` records the
pointwise compatibility needed for this interface. -/
def IsHomRuleBilinear {X : TopCat.{v}}
    {O : RingSheaf.{v, v} X} {F G H : Mod O}
    (f : ModuleSetMap F G H) (S : TopCat.Sheaf (Type v) X)
    [Ring (S ⟶ ringSetSheaf O)]
    [AddCommGroup (S ⟶ moduleSetSheaf F)]
    [AddCommGroup (S ⟶ moduleSetSheaf G)]
    [AddCommGroup (S ⟶ moduleSetSheaf H)]
    [Module (S ⟶ ringSetSheaf O) (S ⟶ moduleSetSheaf F)]
    [Module (S ⟶ ringSetSheaf O) (S ⟶ moduleSetSheaf G)]
    [Module (S ⟶ ringSetSheaf O) (S ⟶ moduleSetSheaf H)] : Prop :=
  ∃ g : SectionBilinearMap
      (S ⟶ ringSetSheaf O)
      (S ⟶ moduleSetSheaf F)
      (S ⟶ moduleSetSheaf G)
      (S ⟶ moduleSetSheaf H),
    ∀ a b, g a b = sheafHomBilinearRule f S a b

/-! The additive and scalar operations used by the Hom-set formulation are
pointwise when evaluated on sections.  We record these compatibility
conditions explicitly because the algebraic structures on Hom types are
otherwise arbitrary Lean instances. -/
def IsPointwiseAddModuleHom {X : TopCat.{v}}
    {O : RingSheaf.{v, v} X} (F : Mod O)
    (S : TopCat.Sheaf (Type v) X)
    [Add (S ⟶ moduleSetSheaf F)] : Prop :=
  ∀ (a b : S ⟶ moduleSetSheaf F) (U : Opens X)
    (s : S.presheaf.obj (op U)),
    (a + b).hom.app (op U) s =
      (show (F.val.obj (op U) : Type v) from a.hom.app (op U) s) +
        (show (F.val.obj (op U) : Type v) from b.hom.app (op U) s)

def IsPointwiseSmulHom {X : TopCat.{v}}
    {O : RingSheaf.{v, v} X} {F : Mod O}
    (S : TopCat.Sheaf (Type v) X)
    [SMul (S ⟶ ringSetSheaf O) (S ⟶ moduleSetSheaf F)] : Prop :=
  ∀ (r : S ⟶ ringSetSheaf O) (a : S ⟶ moduleSetSheaf F)
    (U : Opens X) (s : S.presheaf.obj (op U)),
    (r • a).hom.app (op U) s =
      (show (O.obj.obj (op U) : Type v) from r.hom.app (op U) s) •
        (show (F.val.obj (op U) : Type v) from a.hom.app (op U) s)

def IsPointwiseBilinearOperations {X : TopCat.{v}}
    {O : RingSheaf.{v, v} X} {F G H : Mod O}
    (S : TopCat.Sheaf (Type v) X)
    [Add (S ⟶ moduleSetSheaf F)]
    [Add (S ⟶ moduleSetSheaf G)]
    [Add (S ⟶ moduleSetSheaf H)]
    [SMul (S ⟶ ringSetSheaf O) (S ⟶ moduleSetSheaf F)]
    [SMul (S ⟶ ringSetSheaf O) (S ⟶ moduleSetSheaf G)]
    [SMul (S ⟶ ringSetSheaf O) (S ⟶ moduleSetSheaf H)] : Prop :=
  IsPointwiseAddModuleHom F S ∧
    IsPointwiseAddModuleHom G S ∧
    IsPointwiseAddModuleHom H S ∧
    IsPointwiseSmulHom (O := O) S (F := F) ∧
    IsPointwiseSmulHom (O := O) S (F := G) ∧
    IsPointwiseSmulHom (O := O) S (F := H)

/-! The source's Hom-set characterization, quantified over all sheaves of
sets and all Hom-set algebraic structures whose additive and scalar
operations are identified with the pointwise section operations. -/
def IsHomCharacterization {X : TopCat.{v}}
    {O : RingSheaf.{v, v} X} {F G H : Mod O}
    (f : ModuleSetMap F G H) : Prop :=
  ∀ (S : TopCat.Sheaf (Type v) X),
    ∀ [Ring (S ⟶ ringSetSheaf O)]
      [AddCommGroup (S ⟶ moduleSetSheaf F)]
      [AddCommGroup (S ⟶ moduleSetSheaf G)]
      [AddCommGroup (S ⟶ moduleSetSheaf H)]
      [Module (S ⟶ ringSetSheaf O) (S ⟶ moduleSetSheaf F)]
      [Module (S ⟶ ringSetSheaf O) (S ⟶ moduleSetSheaf G)]
      [Module (S ⟶ ringSetSheaf O) (S ⟶ moduleSetSheaf H)],
      IsPointwiseBilinearOperations (O := O) (F := F) (G := G) (H := H) S →
      IsHomRuleBilinear f S

/-! The map on sections induced by a map of sheaves of sets. -/
noncomputable def sectionMap {X : TopCat.{v}}
    {O : RingSheaf.{v, v} X} {F G H : Mod O}
    (f : ModuleSetMap F G H) (U : Opens X)
    (x : (F.val.obj (op U) : Type v))
    (y : (G.val.obj (op U) : Type v)) :
    (H.val.obj (op U) : Type v) :=
  f.hom.app (op U)
    ((sheafProductSectionsEquiv (moduleSetSheaf F) (moduleSetSheaf G) U).symm
      (x, y))

/-! Sectionwise bilinearity of an underlying map of sheaves of sets. -/
def IsSectionwiseBilinear {X : TopCat.{v}}
    {O : RingSheaf.{v, v} X} {F G H : Mod O}
    (f : ModuleSetMap F G H) : Prop :=
  ∀ U : Opens X, ∃ g : SectionBilinearMap
      (O.obj.obj (op U) : Type v)
      (F.val.obj (op U) : Type v)
      (G.val.obj (op U) : Type v)
      (H.val.obj (op U) : Type v),
    ∀ x y, g x y = sectionMap f U x y

private theorem pretest_product_sections_first {X : TopCat.{v}}
    {O : RingSheaf.{v, v} X} (F G : Mod O) (U : Opens X)
    (s : (F.val.obj (op U) : Type v))
    (t : (G.val.obj (op U) : Type v)) :
    (limit.π (pair (moduleSetSheaf F) (moduleSetSheaf G)) (Discrete.mk (WalkingPair.left))).hom.app
        (op U)
        ((sheafProductSectionsEquiv (moduleSetSheaf F) (moduleSetSheaf G) U).symm (s, t)) = s := by
  let e₁ := (preservesLimitIso (TopCat.Sheaf.forget (Type v) X)
    (pair (moduleSetSheaf F) (moduleSetSheaf G))).app (op U)
  let e₁' := HasLimit.isoOfNatIso
    ((Functor.isoWhiskerRight
        (Discrete.natIsoFunctor
          (F := pair (moduleSetSheaf F) (moduleSetSheaf G)))
        (TopCat.Sheaf.forget (Type v) X)).trans
      (Discrete.compNatIsoDiscrete
        (fun j : WalkingPair =>
          (pair (moduleSetSheaf F) (moduleSetSheaf G)).obj (Discrete.mk j))
        (TopCat.Sheaf.forget (Type v) X)))
  let e₂ := preservesLimitIso
    ((evaluation ((Opens X)ᵒᵖ) (Type v)).obj (op U))
    (Discrete.functor ((TopCat.Sheaf.forget (Type v) X).obj ∘ fun j : WalkingPair =>
      (pair (moduleSetSheaf F) (moduleSetSheaf G)).obj (Discrete.mk j)))
  let e₃ := HasLimit.isoOfNatIso (Discrete.compNatIsoDiscrete
    (fun j : WalkingPair =>
      (TopCat.Sheaf.forget (Type v) X).obj
        ((pair (moduleSetSheaf F) (moduleSetSheaf G)).obj (Discrete.mk j)))
    ((evaluation ((Opens X)ᵒᵖ) (Type v)).obj (op U)))
  let e₄ := (Types.productIso (fun j : WalkingPair =>
    ((evaluation ((Opens X)ᵒᵖ) (Type v)).obj (op U)).obj
      ((TopCat.Sheaf.forget (Type v) X).obj
        ((pair (moduleSetSheaf F) (moduleSetSheaf G)).obj (Discrete.mk j))))).toEquiv
  let e₅ : (∀ j : WalkingPair,
      ((evaluation ((Opens X)ᵒᵖ) (Type v)).obj (op U)).obj
        ((TopCat.Sheaf.forget (Type v) X).obj
          ((pair (moduleSetSheaf F) (moduleSetSheaf G)).obj (Discrete.mk j)))) ≃
      (F.val.obj (op U) : Type v) × (G.val.obj (op U) : Type v) := {
    toFun := fun s => (s WalkingPair.left, s WalkingPair.right)
    invFun := fun p j => match j with
      | WalkingPair.left => p.1
      | WalkingPair.right => p.2
    left_inv := by
      intro s
      funext j
      cases j <;> rfl
    right_inv := by
      intro p
      rcases p with ⟨p, q⟩
      rfl }
  let e := e₁.toEquiv.trans ((e₁'.app (op U)).toEquiv.trans
    (e₂.toEquiv.trans (e₃.toEquiv.trans (e₄.trans e₅))))
  have hcoord (q : (((TopCat.Sheaf.forget (Type v) X).obj
      (limit (pair (moduleSetSheaf F) (moduleSetSheaf G)))).obj (op U) : Type v)) :
      (e q).1 =
        (limit.π (pair (moduleSetSheaf F) (moduleSetSheaf G))
          (Discrete.mk WalkingPair.left)).hom.app (op U) q := by
    change ((Types.productIso _).hom ≫ (↾fun s => s WalkingPair.left)) (_ ) = _
    rw [Types.productIso_hom_comp_eval]
    change
      ((e₃.hom ≫ limit.π
        (Discrete.functor (fun j : WalkingPair =>
          ((evaluation ((Opens X)ᵒᵖ) (Type v)).obj (op U)).obj
            ((TopCat.Sheaf.forget (Type v) X).obj
              ((pair (moduleSetSheaf F) (moduleSetSheaf G)).obj
                (Discrete.mk j)))))
        (Discrete.mk WalkingPair.left))
        (e₂.hom ((e₁'.app (op U)).hom (e₁.hom q)))) = _
    have h₃ := HasLimit.isoOfNatIso_hom_π
      (Discrete.compNatIsoDiscrete
        (fun j : WalkingPair =>
          (TopCat.Sheaf.forget (Type v) X).obj
            ((pair (moduleSetSheaf F) (moduleSetSheaf G)).obj (Discrete.mk j)))
        ((evaluation ((Opens X)ᵒᵖ) (Type v)).obj (op U)))
      (Discrete.mk WalkingPair.left)
    have h₃' :
        e₃.hom ≫ limit.π
            (Discrete.functor (fun j : WalkingPair =>
              ((evaluation ((Opens X)ᵒᵖ) (Type v)).obj (op U)).obj
                ((TopCat.Sheaf.forget (Type v) X).obj
                  ((pair (moduleSetSheaf F) (moduleSetSheaf G)).obj
                    (Discrete.mk j)))))
            (Discrete.mk WalkingPair.left) =
          limit.π
              (Discrete.functor (fun j : WalkingPair =>
                (TopCat.Sheaf.forget (Type v) X).obj
                  ((pair (moduleSetSheaf F) (moduleSetSheaf G)).obj
                    (Discrete.mk j))) ⋙
                ((evaluation ((Opens X)ᵒᵖ) (Type v)).obj (op U)))
              (Discrete.mk WalkingPair.left) ≫
            (Discrete.compNatIsoDiscrete
                (fun j : WalkingPair =>
                  (TopCat.Sheaf.forget (Type v) X).obj
                    ((pair (moduleSetSheaf F) (moduleSetSheaf G)).obj
                      (Discrete.mk j)))
                ((evaluation ((Opens X)ᵒᵖ) (Type v)).obj (op U))).hom.app
              (Discrete.mk WalkingPair.left) := by
      simpa [e₃, Function.comp_def] using h₃
    rw [h₃']
    have h₂ := preservesLimitIso_hom_π
      ((evaluation ((Opens X)ᵒᵖ) (Type v)).obj (op U))
      (Discrete.functor (fun j : WalkingPair =>
        (TopCat.Sheaf.forget (Type v) X).obj
          ((pair (moduleSetSheaf F) (moduleSetSheaf G)).obj (Discrete.mk j))))
      (Discrete.mk WalkingPair.left)
    have h₂' :
        e₂.hom ≫
            limit.π
              (Discrete.functor (fun j : WalkingPair =>
                (TopCat.Sheaf.forget (Type v) X).obj
                  ((pair (moduleSetSheaf F) (moduleSetSheaf G)).obj
                    (Discrete.mk j))) ⋙
                ((evaluation ((Opens X)ᵒᵖ) (Type v)).obj (op U)))
              (Discrete.mk WalkingPair.left) =
          ((evaluation ((Opens X)ᵒᵖ) (Type v)).obj (op U)).map
            (limit.π
              (Discrete.functor (fun j : WalkingPair =>
                (TopCat.Sheaf.forget (Type v) X).obj
                  ((pair (moduleSetSheaf F) (moduleSetSheaf G)).obj
                    (Discrete.mk j))))
              (Discrete.mk WalkingPair.left)) := by
      simpa [e₂, Function.comp_def] using h₂
    have h₁ := HasLimit.isoOfNatIso_hom_π
      ((Functor.isoWhiskerRight
          (Discrete.natIsoFunctor
            (F := pair (moduleSetSheaf F) (moduleSetSheaf G)))
          (TopCat.Sheaf.forget (Type v) X)).trans
        (Discrete.compNatIsoDiscrete
          (fun j : WalkingPair =>
            (pair (moduleSetSheaf F) (moduleSetSheaf G)).obj (Discrete.mk j))
      (TopCat.Sheaf.forget (Type v) X)))
      (Discrete.mk WalkingPair.left)
    let c₁ :=
      (Functor.isoWhiskerRight
          (Discrete.natIsoFunctor
            (F := pair (moduleSetSheaf F) (moduleSetSheaf G)))
          (TopCat.Sheaf.forget (Type v) X)).trans
        (Discrete.compNatIsoDiscrete
          (fun j : WalkingPair =>
            (pair (moduleSetSheaf F) (moduleSetSheaf G)).obj (Discrete.mk j))
          (TopCat.Sheaf.forget (Type v) X))
    have h₁' :
        (e₁'.app (op U)).hom ≫
            (limit.π
              (Discrete.functor (fun j : WalkingPair =>
                (TopCat.Sheaf.forget (Type v) X).obj
                  ((pair (moduleSetSheaf F) (moduleSetSheaf G)).obj
                    (Discrete.mk j))))
              (Discrete.mk WalkingPair.left)).app (op U) =
          (limit.π
              (pair (moduleSetSheaf F) (moduleSetSheaf G) ⋙
                TopCat.Sheaf.forget (Type v) X)
              (Discrete.mk WalkingPair.left)).app (op U) ≫
            (c₁.hom.app (Discrete.mk WalkingPair.left)).app (op U) := by
      have h₁eval := congrArg (fun k => k.app (op U)) h₁
      convert h₁eval using 1 <;>
        simp [e₁', Function.comp_def, Discrete.compNatIsoDiscrete,
          Discrete.natIso, NatIso.ofComponents, NatTrans.comp_app,
          Functor.comp_obj] <;>
        try rfl
    have h₀ := preservesLimitIso_hom_π
      (TopCat.Sheaf.forget (Type v) X)
      (pair (moduleSetSheaf F) (moduleSetSheaf G))
      (Discrete.mk WalkingPair.left)
    have h₀' :
        e₁.hom ≫
            (limit.π
              (pair (moduleSetSheaf F) (moduleSetSheaf G) ⋙
                TopCat.Sheaf.forget (Type v) X)
              (Discrete.mk WalkingPair.left)).app (op U) =
          ((TopCat.Sheaf.forget (Type v) X).map
            (limit.π (pair (moduleSetSheaf F) (moduleSetSheaf G))
              (Discrete.mk WalkingPair.left))).app (op U) := by
      have h₀eval := congrArg (fun k => k.app (op U)) h₀
      rw [NatTrans.comp_app] at h₀eval
      simpa [e₁] using h₀eval
    have h_arrow :
        e₁.hom ≫ (e₁'.app (op U)).hom ≫ e₂.hom ≫ e₃.hom ≫
            limit.π
                (Discrete.functor (fun j : WalkingPair =>
                  ((evaluation ((Opens X)ᵒᵖ) (Type v)).obj (op U)).obj
                    ((TopCat.Sheaf.forget (Type v) X).obj
                      ((pair (moduleSetSheaf F) (moduleSetSheaf G)).obj
                        (Discrete.mk j)))))
                (Discrete.mk WalkingPair.left) =
          (limit.π (pair (moduleSetSheaf F) (moduleSetSheaf G))
            (Discrete.mk WalkingPair.left)).hom.app (op U) := by
      change
        (((e₁.hom ≫ (e₁'.app (op U)).hom) ≫ e₂.hom) ≫
          (e₃.hom ≫
            limit.π
              (Discrete.functor (fun j : WalkingPair =>
                ((evaluation ((Opens X)ᵒᵖ) (Type v)).obj (op U)).obj
                  ((TopCat.Sheaf.forget (Type v) X).obj
                    ((pair (moduleSetSheaf F) (moduleSetSheaf G)).obj
                      (Discrete.mk j)))))
              (Discrete.mk WalkingPair.left))) =
          (limit.π (pair (moduleSetSheaf F) (moduleSetSheaf G))
            (Discrete.mk WalkingPair.left)).hom.app (op U)
      simp only [Category.assoc]
      rw [h₃']
      rw [← Category.assoc e₂.hom]
      rw [h₂']
      have h_eval :
          ((evaluation ((Opens X)ᵒᵖ) (Type v)).obj (op U)).map
              (limit.π
                (Discrete.functor (fun j : WalkingPair =>
                  (TopCat.Sheaf.forget (Type v) X).obj
                    ((pair (moduleSetSheaf F) (moduleSetSheaf G)).obj
                      (Discrete.mk j))))
                (Discrete.mk WalkingPair.left)) =
            (limit.π
                (Discrete.functor (fun j : WalkingPair =>
                  (TopCat.Sheaf.forget (Type v) X).obj
                    ((pair (moduleSetSheaf F) (moduleSetSheaf G)).obj
                      (Discrete.mk j))))
                (Discrete.mk WalkingPair.left)).app (op U) := by
        rfl
      rw [h_eval]
      rw [← Category.assoc (e₁'.app (op U)).hom]
      rw [h₁']
      simp only [Category.assoc]
      rw [← Category.assoc e₁.hom]
      rw [h₀']
      have hforget :
          (TopCat.Sheaf.forget (Type v) X).map
              (limit.π (pair (moduleSetSheaf F) (moduleSetSheaf G))
                (Discrete.mk WalkingPair.left)) =
            (limit.π (pair (moduleSetSheaf F) (moduleSetSheaf G))
              (Discrete.mk WalkingPair.left)).hom := by
        rfl
      rw [hforget]
      simp only [c₁, Discrete.compNatIsoDiscrete, Discrete.natIso,
        NatIso.ofComponents]
      rfl
    have h_arrow' := h_arrow
    rw [h₃'] at h_arrow'
    have hq := congrArg (fun k => k q) h_arrow'
    change
      (limit.π
          (Discrete.functor (fun j : WalkingPair =>
            (TopCat.Sheaf.forget (Type v) X).obj
              ((pair (moduleSetSheaf F) (moduleSetSheaf G)).obj
                (Discrete.mk j))) ⋙
            ((evaluation ((Opens X)ᵒᵖ) (Type v)).obj (op U)))
          (Discrete.mk WalkingPair.left) ≫
        (Discrete.compNatIsoDiscrete
          (fun j : WalkingPair =>
            (TopCat.Sheaf.forget (Type v) X).obj
              ((pair (moduleSetSheaf F) (moduleSetSheaf G)).obj
                (Discrete.mk j)))
          ((evaluation ((Opens X)ᵒᵖ) (Type v)).obj (op U))).hom.app
          (Discrete.mk WalkingPair.left))
        (e₂.hom ((e₁'.app (op U)).hom (e₁.hom q))) =
      (limit.π (pair (moduleSetSheaf F) (moduleSetSheaf G))
        (Discrete.mk WalkingPair.left)).hom.app (op U) q at hq
    exact hq
  have hp := congrArg Prod.fst (e.apply_symm_apply (s, t))
  exact hcoord _ |>.symm.trans hp


private theorem pretest_product_sections_second {X : TopCat.{v}}
    {O : RingSheaf.{v, v} X} (F G : Mod O) (U : Opens X)
    (s : (F.val.obj (op U) : Type v))
    (t : (G.val.obj (op U) : Type v)) :
    (limit.π (pair (moduleSetSheaf F) (moduleSetSheaf G))
      (Discrete.mk WalkingPair.right)).hom.app (op U)
      ((sheafProductSectionsEquiv (moduleSetSheaf F) (moduleSetSheaf G) U).symm
        (s, t)) = t := by
  let e₁ := (preservesLimitIso (TopCat.Sheaf.forget (Type v) X)
    (pair (moduleSetSheaf F) (moduleSetSheaf G))).app (op U)
  let e₁' := HasLimit.isoOfNatIso
    ((Functor.isoWhiskerRight
        (Discrete.natIsoFunctor
          (F := pair (moduleSetSheaf F) (moduleSetSheaf G)))
        (TopCat.Sheaf.forget (Type v) X)).trans
      (Discrete.compNatIsoDiscrete
        (fun j : WalkingPair =>
          (pair (moduleSetSheaf F) (moduleSetSheaf G)).obj (Discrete.mk j))
        (TopCat.Sheaf.forget (Type v) X)))
  let e₂ := preservesLimitIso
    ((evaluation ((Opens X)ᵒᵖ) (Type v)).obj (op U))
    (Discrete.functor ((TopCat.Sheaf.forget (Type v) X).obj ∘ fun j : WalkingPair =>
      (pair (moduleSetSheaf F) (moduleSetSheaf G)).obj (Discrete.mk j)))
  let e₃ := HasLimit.isoOfNatIso (Discrete.compNatIsoDiscrete
    (fun j : WalkingPair =>
      (TopCat.Sheaf.forget (Type v) X).obj
        ((pair (moduleSetSheaf F) (moduleSetSheaf G)).obj (Discrete.mk j)))
    ((evaluation ((Opens X)ᵒᵖ) (Type v)).obj (op U)))
  let e₄ := (Types.productIso (fun j : WalkingPair =>
    ((evaluation ((Opens X)ᵒᵖ) (Type v)).obj (op U)).obj
      ((TopCat.Sheaf.forget (Type v) X).obj
        ((pair (moduleSetSheaf F) (moduleSetSheaf G)).obj (Discrete.mk j))))).toEquiv
  let e₅ : (∀ j : WalkingPair,
      ((evaluation ((Opens X)ᵒᵖ) (Type v)).obj (op U)).obj
        ((TopCat.Sheaf.forget (Type v) X).obj
          ((pair (moduleSetSheaf F) (moduleSetSheaf G)).obj (Discrete.mk j)))) ≃
      (F.val.obj (op U) : Type v) × (G.val.obj (op U) : Type v) := {
    toFun := fun s => (s WalkingPair.left, s WalkingPair.right)
    invFun := fun p j => match j with
      | WalkingPair.left => p.1
      | WalkingPair.right => p.2
    left_inv := by
      intro s
      funext j
      cases j <;> rfl
    right_inv := by
      intro p
      rcases p with ⟨p, q⟩
      rfl }
  let e := e₁.toEquiv.trans ((e₁'.app (op U)).toEquiv.trans
    (e₂.toEquiv.trans (e₃.toEquiv.trans (e₄.trans e₅))))
  have hcoord (q : (((TopCat.Sheaf.forget (Type v) X).obj
      (limit (pair (moduleSetSheaf F) (moduleSetSheaf G)))).obj (op U) : Type v)) :
      (e q).2 =
        (limit.π (pair (moduleSetSheaf F) (moduleSetSheaf G))
          (Discrete.mk WalkingPair.right)).hom.app (op U) q := by
    change ((Types.productIso _).hom ≫ (↾fun s => s WalkingPair.right)) (_ ) = _
    rw [Types.productIso_hom_comp_eval]
    change
      ((e₃.hom ≫ limit.π
        (Discrete.functor (fun j : WalkingPair =>
          ((evaluation ((Opens X)ᵒᵖ) (Type v)).obj (op U)).obj
            ((TopCat.Sheaf.forget (Type v) X).obj
              ((pair (moduleSetSheaf F) (moduleSetSheaf G)).obj
                (Discrete.mk j)))))
        (Discrete.mk WalkingPair.right))
        (e₂.hom ((e₁'.app (op U)).hom (e₁.hom q)))) = _
    have h₃ := HasLimit.isoOfNatIso_hom_π
      (Discrete.compNatIsoDiscrete
        (fun j : WalkingPair =>
          (TopCat.Sheaf.forget (Type v) X).obj
            ((pair (moduleSetSheaf F) (moduleSetSheaf G)).obj (Discrete.mk j)))
        ((evaluation ((Opens X)ᵒᵖ) (Type v)).obj (op U)))
      (Discrete.mk WalkingPair.right)
    have h₃' :
        e₃.hom ≫ limit.π
            (Discrete.functor (fun j : WalkingPair =>
              ((evaluation ((Opens X)ᵒᵖ) (Type v)).obj (op U)).obj
                ((TopCat.Sheaf.forget (Type v) X).obj
                  ((pair (moduleSetSheaf F) (moduleSetSheaf G)).obj
                    (Discrete.mk j)))))
            (Discrete.mk WalkingPair.right) =
          limit.π
              (Discrete.functor (fun j : WalkingPair =>
                (TopCat.Sheaf.forget (Type v) X).obj
                  ((pair (moduleSetSheaf F) (moduleSetSheaf G)).obj
                    (Discrete.mk j))) ⋙
                ((evaluation ((Opens X)ᵒᵖ) (Type v)).obj (op U)))
              (Discrete.mk WalkingPair.right) ≫
            (Discrete.compNatIsoDiscrete
                (fun j : WalkingPair =>
                  (TopCat.Sheaf.forget (Type v) X).obj
                    ((pair (moduleSetSheaf F) (moduleSetSheaf G)).obj
                      (Discrete.mk j)))
                ((evaluation ((Opens X)ᵒᵖ) (Type v)).obj (op U))).hom.app
              (Discrete.mk WalkingPair.right) := by
      simpa [e₃, Function.comp_def] using h₃
    rw [h₃']
    have h₂ := preservesLimitIso_hom_π
      ((evaluation ((Opens X)ᵒᵖ) (Type v)).obj (op U))
      (Discrete.functor (fun j : WalkingPair =>
        (TopCat.Sheaf.forget (Type v) X).obj
          ((pair (moduleSetSheaf F) (moduleSetSheaf G)).obj (Discrete.mk j))))
      (Discrete.mk WalkingPair.right)
    have h₂' :
        e₂.hom ≫
            limit.π
              (Discrete.functor (fun j : WalkingPair =>
                (TopCat.Sheaf.forget (Type v) X).obj
                  ((pair (moduleSetSheaf F) (moduleSetSheaf G)).obj
                    (Discrete.mk j))) ⋙
                ((evaluation ((Opens X)ᵒᵖ) (Type v)).obj (op U)))
              (Discrete.mk WalkingPair.right) =
          ((evaluation ((Opens X)ᵒᵖ) (Type v)).obj (op U)).map
            (limit.π
              (Discrete.functor (fun j : WalkingPair =>
                (TopCat.Sheaf.forget (Type v) X).obj
                  ((pair (moduleSetSheaf F) (moduleSetSheaf G)).obj
                    (Discrete.mk j))))
              (Discrete.mk WalkingPair.right)) := by
      simpa [e₂, Function.comp_def] using h₂
    have h₁ := HasLimit.isoOfNatIso_hom_π
      ((Functor.isoWhiskerRight
          (Discrete.natIsoFunctor
            (F := pair (moduleSetSheaf F) (moduleSetSheaf G)))
          (TopCat.Sheaf.forget (Type v) X)).trans
        (Discrete.compNatIsoDiscrete
          (fun j : WalkingPair =>
            (pair (moduleSetSheaf F) (moduleSetSheaf G)).obj (Discrete.mk j))
          (TopCat.Sheaf.forget (Type v) X)))
      (Discrete.mk WalkingPair.right)
    let c₁ :=
      (Functor.isoWhiskerRight
          (Discrete.natIsoFunctor
            (F := pair (moduleSetSheaf F) (moduleSetSheaf G)))
          (TopCat.Sheaf.forget (Type v) X)).trans
        (Discrete.compNatIsoDiscrete
          (fun j : WalkingPair =>
            (pair (moduleSetSheaf F) (moduleSetSheaf G)).obj (Discrete.mk j))
          (TopCat.Sheaf.forget (Type v) X))
    have h₁' :
        (e₁'.app (op U)).hom ≫
            (limit.π
              (Discrete.functor (fun j : WalkingPair =>
                (TopCat.Sheaf.forget (Type v) X).obj
                  ((pair (moduleSetSheaf F) (moduleSetSheaf G)).obj
                    (Discrete.mk j))))
              (Discrete.mk WalkingPair.right)).app (op U) =
          (limit.π
              (pair (moduleSetSheaf F) (moduleSetSheaf G) ⋙
                TopCat.Sheaf.forget (Type v) X)
              (Discrete.mk WalkingPair.right)).app (op U) ≫
            (c₁.hom.app (Discrete.mk WalkingPair.right)).app (op U) := by
      have h₁eval := congrArg (fun k => k.app (op U)) h₁
      convert h₁eval using 1 <;>
        simp [e₁', Function.comp_def, Discrete.compNatIsoDiscrete,
          Discrete.natIso, NatIso.ofComponents, NatTrans.comp_app,
          Functor.comp_obj] <;>
        try rfl
    have h₀ := preservesLimitIso_hom_π
      (TopCat.Sheaf.forget (Type v) X)
      (pair (moduleSetSheaf F) (moduleSetSheaf G))
      (Discrete.mk WalkingPair.right)
    have h₀' :
        e₁.hom ≫
            (limit.π
              (pair (moduleSetSheaf F) (moduleSetSheaf G) ⋙
                TopCat.Sheaf.forget (Type v) X)
              (Discrete.mk WalkingPair.right)).app (op U) =
          ((TopCat.Sheaf.forget (Type v) X).map
            (limit.π (pair (moduleSetSheaf F) (moduleSetSheaf G))
              (Discrete.mk WalkingPair.right))).app (op U) := by
      have h₀eval := congrArg (fun k => k.app (op U)) h₀
      rw [NatTrans.comp_app] at h₀eval
      simpa [e₁] using h₀eval
    have h_arrow :
        e₁.hom ≫ (e₁'.app (op U)).hom ≫ e₂.hom ≫ e₃.hom ≫
            limit.π
                (Discrete.functor (fun j : WalkingPair =>
                  ((evaluation ((Opens X)ᵒᵖ) (Type v)).obj (op U)).obj
                    ((TopCat.Sheaf.forget (Type v) X).obj
                      ((pair (moduleSetSheaf F) (moduleSetSheaf G)).obj
                        (Discrete.mk j)))))
                (Discrete.mk WalkingPair.right) =
          (limit.π (pair (moduleSetSheaf F) (moduleSetSheaf G))
            (Discrete.mk WalkingPair.right)).hom.app (op U) := by
      change
        (((e₁.hom ≫ (e₁'.app (op U)).hom) ≫ e₂.hom) ≫
          (e₃.hom ≫
            limit.π
              (Discrete.functor (fun j : WalkingPair =>
                ((evaluation ((Opens X)ᵒᵖ) (Type v)).obj (op U)).obj
                  ((TopCat.Sheaf.forget (Type v) X).obj
                    ((pair (moduleSetSheaf F) (moduleSetSheaf G)).obj
                      (Discrete.mk j)))))
              (Discrete.mk WalkingPair.right))) =
          (limit.π (pair (moduleSetSheaf F) (moduleSetSheaf G))
            (Discrete.mk WalkingPair.right)).hom.app (op U)
      simp only [Category.assoc]
      rw [h₃']
      rw [← Category.assoc e₂.hom]
      rw [h₂']
      have h_eval :
          ((evaluation ((Opens X)ᵒᵖ) (Type v)).obj (op U)).map
              (limit.π
                (Discrete.functor (fun j : WalkingPair =>
                  (TopCat.Sheaf.forget (Type v) X).obj
                    ((pair (moduleSetSheaf F) (moduleSetSheaf G)).obj
                      (Discrete.mk j))))
                (Discrete.mk WalkingPair.right)) =
            (limit.π
                (Discrete.functor (fun j : WalkingPair =>
                  (TopCat.Sheaf.forget (Type v) X).obj
                    ((pair (moduleSetSheaf F) (moduleSetSheaf G)).obj
                      (Discrete.mk j))))
                (Discrete.mk WalkingPair.right)).app (op U) := by
        rfl
      rw [h_eval]
      rw [← Category.assoc (e₁'.app (op U)).hom]
      rw [h₁']
      simp only [Category.assoc]
      rw [← Category.assoc e₁.hom]
      rw [h₀']
      have hforget :
          (TopCat.Sheaf.forget (Type v) X).map
              (limit.π (pair (moduleSetSheaf F) (moduleSetSheaf G))
                (Discrete.mk WalkingPair.right)) =
            (limit.π (pair (moduleSetSheaf F) (moduleSetSheaf G))
              (Discrete.mk WalkingPair.right)).hom := by
        rfl
      rw [hforget]
      simp only [c₁, Discrete.compNatIsoDiscrete, Discrete.natIso,
        NatIso.ofComponents]
      rfl
    have h_arrow' := h_arrow
    rw [h₃'] at h_arrow'
    have hq := congrArg (fun k => k q) h_arrow'
    change
      (limit.π
          (Discrete.functor (fun j : WalkingPair =>
            (TopCat.Sheaf.forget (Type v) X).obj
              ((pair (moduleSetSheaf F) (moduleSetSheaf G)).obj
                (Discrete.mk j))) ⋙
            ((evaluation ((Opens X)ᵒᵖ) (Type v)).obj (op U)))
          (Discrete.mk WalkingPair.right) ≫
        (Discrete.compNatIsoDiscrete
          (fun j : WalkingPair =>
            (TopCat.Sheaf.forget (Type v) X).obj
              ((pair (moduleSetSheaf F) (moduleSetSheaf G)).obj
                (Discrete.mk j)))
          ((evaluation ((Opens X)ᵒᵖ) (Type v)).obj (op U))).hom.app
          (Discrete.mk WalkingPair.right))
        (e₂.hom ((e₁'.app (op U)).hom (e₁.hom q))) =
      (limit.π (pair (moduleSetSheaf F) (moduleSetSheaf G))
        (Discrete.mk WalkingPair.right)).hom.app (op U) q at hq
    exact hq
  have hp := congrArg Prod.snd (e.apply_symm_apply (s, t))
  exact hcoord _ |>.symm.trans hp

private theorem sheafHomProduct_app_eq {X : TopCat.{v}}
    {O : RingSheaf.{v, v} X} {F G : Mod O}
    (S : TopCat.Sheaf (Type v) X)
    (a : S ⟶ moduleSetSheaf F) (b : S ⟶ moduleSetSheaf G)
    (U : (Opens X)ᵒᵖ) (s : S.obj.obj U) :
    (sheafHomProduct S a b).hom.app U s =
      (sheafProductSectionsEquiv (moduleSetSheaf F) (moduleSetSheaf G)
        U.unop).symm (a.hom.app U s, b.hom.app U s) := by
  let e := sheafProductSectionsEquiv (moduleSetSheaf F)
    (moduleSetSheaf G) U.unop
  apply e.injective
  change e ((sheafHomProduct S a b).hom.app U s) =
    e (e.symm (a.hom.app U s, b.hom.app U s))
  rw [e.apply_symm_apply]
  apply Prod.ext
  ·
    have hcoord :
        (limit.π (pair (moduleSetSheaf F) (moduleSetSheaf G))
          (Discrete.mk WalkingPair.left)).hom.app U
            ((sheafHomProduct S a b).hom.app U s) =
          (e ((sheafHomProduct S a b).hom.app U s)).1 := by
      rw [← e.symm_apply_apply ((sheafHomProduct S a b).hom.app U s)]
      simpa [e] using pretest_product_sections_first F G U.unop
        (e ((sheafHomProduct S a b).hom.app U s)).1
        (e ((sheafHomProduct S a b).hom.app U s)).2
    rw [← hcoord]
    have hh := congrArg (fun k => (k.hom.app U) s)
      (limit.lift_π (BinaryFan.mk a b)
        (Discrete.mk WalkingPair.left))
    change (ConcreteCategory.hom
        ((limit.π (pair (moduleSetSheaf F) (moduleSetSheaf G))
          (Discrete.mk WalkingPair.left)).hom.app U))
        ((ConcreteCategory.hom
          ((limit.lift (pair (moduleSetSheaf F) (moduleSetSheaf G))
            (BinaryFan.mk a b)).hom.app U)) s) =
      (ConcreteCategory.hom (a.hom.app U)) s at hh
    exact hh
  ·
    have hcoord :
        (limit.π (pair (moduleSetSheaf F) (moduleSetSheaf G))
          (Discrete.mk WalkingPair.right)).hom.app U
            ((sheafHomProduct S a b).hom.app U s) =
          (e ((sheafHomProduct S a b).hom.app U s)).2 := by
      rw [← e.symm_apply_apply ((sheafHomProduct S a b).hom.app U s)]
      simpa [e] using pretest_product_sections_second F G U.unop
        (e ((sheafHomProduct S a b).hom.app U s)).1
        (e ((sheafHomProduct S a b).hom.app U s)).2
    rw [← hcoord]
    have hh := congrArg (fun k => (k.hom.app U) s)
      (limit.lift_π (BinaryFan.mk a b)
        (Discrete.mk WalkingPair.right))
    change (ConcreteCategory.hom
        ((limit.π (pair (moduleSetSheaf F) (moduleSetSheaf G))
          (Discrete.mk WalkingPair.right)).hom.app U))
        ((ConcreteCategory.hom
          ((limit.lift (pair (moduleSetSheaf F) (moduleSetSheaf G))
            (BinaryFan.mk a b)).hom.app U)) s) =
      (ConcreteCategory.hom (b.hom.app U)) s at hh
    exact hh

private theorem sheafHomBilinearRule_app_eq {X : TopCat.{v}}
    {O : RingSheaf.{v, v} X} {F G H : Mod O}
    (f : ModuleSetMap F G H) (S : TopCat.Sheaf (Type v) X)
    (a : S ⟶ moduleSetSheaf F) (b : S ⟶ moduleSetSheaf G)
    (U : (Opens X)ᵒᵖ) (s : S.obj.obj U) :
    (sheafHomBilinearRule f S a b).hom.app (op U.unop) s =
      sectionMap f U.unop (a.hom.app U s) (b.hom.app U s) := by
  change f.hom.app U ((sheafHomProduct S a b).hom.app U s) =
    f.hom.app U
      ((sheafProductSectionsEquiv (moduleSetSheaf F)
        (moduleSetSheaf G) U.unop).symm
        (a.hom.app U s, b.hom.app U s))
  exact congrArg (fun q => f.hom.app U q)
    (sheafHomProduct_app_eq S a b U s)

private noncomputable def sheafHomAdd {X : TopCat.{v}}
    {O : RingSheaf.{v, v} X} {F : Mod O}
    (S : TopCat.Sheaf (Type v) X)
    (a b : S ⟶ moduleSetSheaf F) : S ⟶ moduleSetSheaf F :=
  ObjectProperty.homMk {
    app := fun U => TypeCat.ofHom (fun s =>
      (show (F.val.obj U : Type v) from a.hom.app U s) +
        (show (F.val.obj U : Type v) from b.hom.app U s))
    naturality := by
      intro U V i
      apply ConcreteCategory.hom_ext
      intro s
      change (show (F.val.obj V : Type v) from a.hom.app V (S.obj.map i s)) +
          (show (F.val.obj V : Type v) from b.hom.app V (S.obj.map i s)) =
        (F.val.map i).hom
          ((show (F.val.obj U : Type v) from a.hom.app U s) +
            (show (F.val.obj U : Type v) from b.hom.app U s))
      calc
        (show (F.val.obj V : Type v) from a.hom.app V (S.obj.map i s)) +
            (show (F.val.obj V : Type v) from b.hom.app V (S.obj.map i s)) =
            (show (F.val.obj V : Type v) from
              (F.val.map i).hom (a.hom.app U s)) +
              (show (F.val.obj V : Type v) from
                (F.val.map i).hom (b.hom.app U s)) := by
          exact congrArg₂ (fun p q => p + q)
            (congrArg (fun k => (ConcreteCategory.hom k) s)
              (a.hom.naturality i))
            (congrArg (fun k => (ConcreteCategory.hom k) s)
              (b.hom.naturality i))
        _ = (show (F.val.obj V : Type v) from
          (F.val.map i).hom
            ((show (F.val.obj U : Type v) from a.hom.app U s) +
              (show (F.val.obj U : Type v) from b.hom.app U s))) := by
          rw [map_add]
          rfl }

private noncomputable def sheafHomZero {X : TopCat.{v}}
    {O : RingSheaf.{v, v} X} {F : Mod O}
    (S : TopCat.Sheaf (Type v) X) : S ⟶ moduleSetSheaf F :=
  ObjectProperty.homMk {
    app := fun U => TypeCat.ofHom (fun _ => (0 : (F.val.obj U : Type v)))
    naturality := by
      intro U V i
      apply ConcreteCategory.hom_ext
      intro s
      change (0 : (F.val.obj V : Type v)) = (F.val.map i).hom 0
      rw [map_zero]
      rfl }

private noncomputable def sheafHomNeg {X : TopCat.{v}}
    {O : RingSheaf.{v, v} X} {F : Mod O}
    (S : TopCat.Sheaf (Type v) X) (a : S ⟶ moduleSetSheaf F) :
    S ⟶ moduleSetSheaf F :=
  ObjectProperty.homMk {
    app := fun U => TypeCat.ofHom (fun s =>
      -(show (F.val.obj U : Type v) from a.hom.app U s))
    naturality := by
      intro U V i
      apply ConcreteCategory.hom_ext
      intro s
      change -(show (F.val.obj V : Type v) from a.hom.app V (S.obj.map i s)) =
        (F.val.map i).hom
          (-(show (F.val.obj U : Type v) from a.hom.app U s))
      rw [map_neg]
      exact congrArg Neg.neg
        (congrArg (fun k => (ConcreteCategory.hom k) s)
          (a.hom.naturality i)) }

private noncomputable def sheafHomSmul {X : TopCat.{v}}
    {O : RingSheaf.{v, v} X} {F : Mod O}
    (S : TopCat.Sheaf (Type v) X)
    (r : S ⟶ ringSetSheaf O) (a : S ⟶ moduleSetSheaf F) :
    S ⟶ moduleSetSheaf F :=
  ObjectProperty.homMk {
    app := fun U => TypeCat.ofHom (fun s =>
      (show (O.obj.obj U : Type v) from r.hom.app U s) •
        (show (F.val.obj U : Type v) from a.hom.app U s))
    naturality := by
      intro U V i
      apply ConcreteCategory.hom_ext
      intro s
      change
        (show (O.obj.obj V : Type v) from r.hom.app V (S.obj.map i s)) •
            (show (F.val.obj V : Type v) from a.hom.app V (S.obj.map i s)) =
          ((SheafOfModules.toSheaf O).obj F).obj.map i
            ((show (O.obj.obj U : Type v) from r.hom.app U s) •
              (show (F.val.obj U : Type v) from a.hom.app U s))
      calc
        (show (O.obj.obj V : Type v) from r.hom.app V (S.obj.map i s)) •
              (show (F.val.obj V : Type v) from a.hom.app V (S.obj.map i s)) =
            (show (O.obj.obj V : Type v) from (O.obj.map i).hom (r.hom.app U s)) •
              (show (F.val.obj V : Type v) from (F.val.map i).hom (a.hom.app U s)) := by
          exact congrArg₂ (fun p q => p • q)
            (congrArg (fun k => (ConcreteCategory.hom k) s)
              (r.hom.naturality i))
            (congrArg (fun k => (ConcreteCategory.hom k) s)
              (a.hom.naturality i))
        _ = (show (F.val.obj V : Type v) from
          (F.val.map i).hom
            ((show (O.obj.obj U : Type v) from r.hom.app U s) •
              (show (F.val.obj U : Type v) from a.hom.app U s))) := by
          exact (PresheafOfModules.map_smul F.val i
            (r.hom.app U s) (a.hom.app U s)).symm }

private noncomputable def sheafRingHomAdd {X : TopCat.{v}}
    {O : RingSheaf.{v, v} X} (S : TopCat.Sheaf (Type v) X)
    (a b : S ⟶ ringSetSheaf O) : S ⟶ ringSetSheaf O :=
  ObjectProperty.homMk {
    app := fun U => TypeCat.ofHom (fun s =>
      (show (O.obj.obj U : Type v) from a.hom.app U s) +
        (show (O.obj.obj U : Type v) from b.hom.app U s))
    naturality := by
      intro U V i
      apply ConcreteCategory.hom_ext
      intro s
      change (show (O.obj.obj V : Type v) from a.hom.app V (S.obj.map i s)) +
          (show (O.obj.obj V : Type v) from b.hom.app V (S.obj.map i s)) =
        (O.obj.map i).hom
          ((show (O.obj.obj U : Type v) from a.hom.app U s) +
            (show (O.obj.obj U : Type v) from b.hom.app U s))
      calc
        (show (O.obj.obj V : Type v) from a.hom.app V (S.obj.map i s)) +
              (show (O.obj.obj V : Type v) from b.hom.app V (S.obj.map i s)) =
            (O.obj.map i).hom (a.hom.app U s) +
              (O.obj.map i).hom (b.hom.app U s) := by
          exact congrArg₂ (fun p q => p + q)
            (congrArg (fun k => (ConcreteCategory.hom k) s)
              (a.hom.naturality i))
            (congrArg (fun k => (ConcreteCategory.hom k) s)
              (b.hom.naturality i))
        _ = (O.obj.map i).hom
            ((show (O.obj.obj U : Type v) from a.hom.app U s) +
              (show (O.obj.obj U : Type v) from b.hom.app U s)) := by
          rw [map_add] }

private noncomputable def sheafRingHomZero {X : TopCat.{v}}
    {O : RingSheaf.{v, v} X} (S : TopCat.Sheaf (Type v) X) :
    S ⟶ ringSetSheaf O :=
  ObjectProperty.homMk {
    app := fun U => TypeCat.ofHom (fun _ => (0 : (O.obj.obj U : Type v)))
    naturality := by
      intro U V i
      apply ConcreteCategory.hom_ext
      intro s
      change (0 : (O.obj.obj V : Type v)) = (O.obj.map i).hom 0
      rw [map_zero] }

private noncomputable def sheafRingHomNeg {X : TopCat.{v}}
    {O : RingSheaf.{v, v} X} (S : TopCat.Sheaf (Type v) X)
    (a : S ⟶ ringSetSheaf O) : S ⟶ ringSetSheaf O :=
  ObjectProperty.homMk {
    app := fun U => TypeCat.ofHom (fun s =>
      -(show (O.obj.obj U : Type v) from a.hom.app U s))
    naturality := by
      intro U V i
      apply ConcreteCategory.hom_ext
      intro s
      change -(show (O.obj.obj V : Type v) from a.hom.app V (S.obj.map i s)) =
        (O.obj.map i).hom
          (-(show (O.obj.obj U : Type v) from a.hom.app U s))
      rw [map_neg]
      exact congrArg Neg.neg
        (congrArg (fun k => (ConcreteCategory.hom k) s)
          (a.hom.naturality i)) }

private noncomputable def sheafRingHomOne {X : TopCat.{v}}
    {O : RingSheaf.{v, v} X} (S : TopCat.Sheaf (Type v) X) :
    S ⟶ ringSetSheaf O :=
  ObjectProperty.homMk {
    app := fun U => TypeCat.ofHom (fun _ => (1 : (O.obj.obj U : Type v)))
    naturality := by
      intro U V i
      apply ConcreteCategory.hom_ext
      intro s
      change (1 : (O.obj.obj V : Type v)) = (O.obj.map i).hom 1
      rw [map_one] }

private noncomputable def sheafRingHomMul {X : TopCat.{v}}
    {O : RingSheaf.{v, v} X} (S : TopCat.Sheaf (Type v) X)
    (a b : S ⟶ ringSetSheaf O) : S ⟶ ringSetSheaf O :=
  ObjectProperty.homMk {
    app := fun U => TypeCat.ofHom (fun s =>
      (show (O.obj.obj U : Type v) from a.hom.app U s) *
        (show (O.obj.obj U : Type v) from b.hom.app U s))
    naturality := by
      intro U V i
      apply ConcreteCategory.hom_ext
      intro s
      change (show (O.obj.obj V : Type v) from a.hom.app V (S.obj.map i s)) *
          (show (O.obj.obj V : Type v) from b.hom.app V (S.obj.map i s)) =
        (O.obj.map i).hom
          ((show (O.obj.obj U : Type v) from a.hom.app U s) *
            (show (O.obj.obj U : Type v) from b.hom.app U s))
      calc
        (show (O.obj.obj V : Type v) from a.hom.app V (S.obj.map i s)) *
              (show (O.obj.obj V : Type v) from b.hom.app V (S.obj.map i s)) =
            (O.obj.map i).hom (a.hom.app U s) *
              (O.obj.map i).hom (b.hom.app U s) := by
          exact congrArg₂ (fun p q => p * q)
            (congrArg (fun k => (ConcreteCategory.hom k) s)
              (a.hom.naturality i))
            (congrArg (fun k => (ConcreteCategory.hom k) s)
              (b.hom.naturality i))
        _ = (O.obj.map i).hom
            ((show (O.obj.obj U : Type v) from a.hom.app U s) *
              (show (O.obj.obj U : Type v) from b.hom.app U s)) := by
          rw [map_mul] }

private noncomputable def sheafHomAddCommGroup {X : TopCat.{v}}
    {O : RingSheaf.{v, v} X} {F : Mod O} (S : TopCat.Sheaf (Type v) X) :
    AddCommGroup (S ⟶ moduleSetSheaf F) := by
  letI : Add (S ⟶ moduleSetSheaf F) := ⟨sheafHomAdd S⟩
  letI : Zero (S ⟶ moduleSetSheaf F) := ⟨sheafHomZero S⟩
  letI : Neg (S ⟶ moduleSetSheaf F) := ⟨sheafHomNeg S⟩
  exact {
  add := sheafHomAdd S
  add_assoc := by
    intro a b c
    apply CategoryTheory.Sheaf.hom_ext
    apply NatTrans.ext
    funext U
    apply ConcreteCategory.hom_ext
    intro s
    change
      ((show (F.val.obj U : Type v) from
          (sheafHomAdd S a b).hom.app U s) +
        (show (F.val.obj U : Type v) from c.hom.app U s)) =
      ((show (F.val.obj U : Type v) from a.hom.app U s) +
        (show (F.val.obj U : Type v) from
          (sheafHomAdd S b c).hom.app U s))
    exact add_assoc _ _ _
  zero := sheafHomZero S
  zero_add := by
    intro a
    apply CategoryTheory.Sheaf.hom_ext
    apply NatTrans.ext
    funext U
    apply ConcreteCategory.hom_ext
    intro s
    change (show (F.val.obj U : Type v) from
        (sheafHomAdd S (sheafHomZero S) a).hom.app U s) =
      (show (F.val.obj U : Type v) from a.hom.app U s)
    change 0 + (show (F.val.obj U : Type v) from a.hom.app U s) = _
    exact zero_add _
  add_zero := by
    intro a
    apply CategoryTheory.Sheaf.hom_ext
    apply NatTrans.ext
    funext U
    apply ConcreteCategory.hom_ext
    intro s
    change (show (F.val.obj U : Type v) from
        (sheafHomAdd S a (sheafHomZero S)).hom.app U s) =
      (show (F.val.obj U : Type v) from a.hom.app U s)
    change (show (F.val.obj U : Type v) from a.hom.app U s) + 0 = _
    exact add_zero _
  neg := sheafHomNeg S
  nsmul := nsmulRec
  zsmul := zsmulRec
  neg_add_cancel := by
    intro a
    apply CategoryTheory.Sheaf.hom_ext
    apply NatTrans.ext
    funext U
    apply ConcreteCategory.hom_ext
    intro s
    change (show (F.val.obj U : Type v) from
        (sheafHomAdd S (sheafHomNeg S a) a).hom.app U s) = 0
    change -(show (F.val.obj U : Type v) from a.hom.app U s) +
        (show (F.val.obj U : Type v) from a.hom.app U s) = 0
    exact neg_add_cancel _
  add_comm := by
    intro a b
    apply CategoryTheory.Sheaf.hom_ext
    apply NatTrans.ext
    funext U
    apply ConcreteCategory.hom_ext
    intro s
    change (show (F.val.obj U : Type v) from a.hom.app U s) +
          (show (F.val.obj U : Type v) from b.hom.app U s) =
        (show (F.val.obj U : Type v) from b.hom.app U s) +
          (show (F.val.obj U : Type v) from a.hom.app U s)
    exact add_comm _ _ }

private noncomputable def sheafRingHomAddCommGroup {X : TopCat.{v}}
    {O : RingSheaf.{v, v} X} (S : TopCat.Sheaf (Type v) X) :
    AddCommGroup (S ⟶ ringSetSheaf O) := by
  letI : Add (S ⟶ ringSetSheaf O) := ⟨sheafRingHomAdd S⟩
  letI : Zero (S ⟶ ringSetSheaf O) := ⟨sheafRingHomZero S⟩
  letI : Neg (S ⟶ ringSetSheaf O) := ⟨sheafRingHomNeg S⟩
  exact {
    add := sheafRingHomAdd S
    add_assoc := by
      intro a b c
      apply CategoryTheory.Sheaf.hom_ext
      apply NatTrans.ext
      funext U
      apply ConcreteCategory.hom_ext
      intro s
      change
        ((show (O.obj.obj U : Type v) from
            (sheafRingHomAdd S a b).hom.app U s) +
          (show (O.obj.obj U : Type v) from c.hom.app U s)) =
        ((show (O.obj.obj U : Type v) from a.hom.app U s) +
          (show (O.obj.obj U : Type v) from
            (sheafRingHomAdd S b c).hom.app U s))
      exact add_assoc _ _ _
    zero := sheafRingHomZero S
    zero_add := by
      intro a
      apply CategoryTheory.Sheaf.hom_ext
      apply NatTrans.ext
      funext U
      apply ConcreteCategory.hom_ext
      intro s
      change (show (O.obj.obj U : Type v) from
          (sheafRingHomAdd S (sheafRingHomZero S) a).hom.app U s) =
        (show (O.obj.obj U : Type v) from a.hom.app U s)
      change 0 + (show (O.obj.obj U : Type v) from a.hom.app U s) = _
      exact zero_add _
    add_zero := by
      intro a
      apply CategoryTheory.Sheaf.hom_ext
      apply NatTrans.ext
      funext U
      apply ConcreteCategory.hom_ext
      intro s
      change (show (O.obj.obj U : Type v) from
          (sheafRingHomAdd S a (sheafRingHomZero S)).hom.app U s) =
        (show (O.obj.obj U : Type v) from a.hom.app U s)
      change (show (O.obj.obj U : Type v) from a.hom.app U s) + 0 = _
      exact add_zero _
    neg := sheafRingHomNeg S
    nsmul := nsmulRec
    zsmul := zsmulRec
    neg_add_cancel := by
      intro a
      apply CategoryTheory.Sheaf.hom_ext
      apply NatTrans.ext
      funext U
      apply ConcreteCategory.hom_ext
      intro s
      change (show (O.obj.obj U : Type v) from
          (sheafRingHomAdd S (sheafRingHomNeg S a) a).hom.app U s) = 0
      change -(show (O.obj.obj U : Type v) from a.hom.app U s) +
          (show (O.obj.obj U : Type v) from a.hom.app U s) = 0
      exact neg_add_cancel _
    add_comm := by
      intro a b
      apply CategoryTheory.Sheaf.hom_ext
      apply NatTrans.ext
      funext U
      apply ConcreteCategory.hom_ext
      intro s
      change (show (O.obj.obj U : Type v) from a.hom.app U s) +
            (show (O.obj.obj U : Type v) from b.hom.app U s) =
          (show (O.obj.obj U : Type v) from b.hom.app U s) +
            (show (O.obj.obj U : Type v) from a.hom.app U s)
      exact add_comm _ _ }

private noncomputable def sheafRingHomRing {X : TopCat.{v}}
    {O : RingSheaf.{v, v} X} (S : TopCat.Sheaf (Type v) X) :
    Ring (S ⟶ ringSetSheaf O) := by
  letI : AddCommGroup (S ⟶ ringSetSheaf O) := sheafRingHomAddCommGroup S
  letI : Mul (S ⟶ ringSetSheaf O) := ⟨sheafRingHomMul S⟩
  letI : One (S ⟶ ringSetSheaf O) := ⟨sheafRingHomOne S⟩
  exact {
    add := sheafRingHomAdd S
    add_assoc := add_assoc
    zero := sheafRingHomZero S
    zero_add := zero_add
    add_zero := add_zero
    neg := sheafRingHomNeg S
    nsmul := nsmulRec
    zsmul := zsmulRec
    neg_add_cancel := neg_add_cancel
    add_comm := add_comm
    mul := sheafRingHomMul S
    mul_assoc := by
      intro a b c
      apply CategoryTheory.Sheaf.hom_ext
      apply NatTrans.ext
      funext U
      apply ConcreteCategory.hom_ext
      intro s
      change
        ((show (O.obj.obj U : Type v) from
            (sheafRingHomMul S a b).hom.app U s) *
          (show (O.obj.obj U : Type v) from c.hom.app U s)) =
        ((show (O.obj.obj U : Type v) from a.hom.app U s) *
          (show (O.obj.obj U : Type v) from
            (sheafRingHomMul S b c).hom.app U s))
      exact mul_assoc _ _ _
    one := sheafRingHomOne S
    one_mul := by
      intro a
      apply CategoryTheory.Sheaf.hom_ext
      apply NatTrans.ext
      funext U
      apply ConcreteCategory.hom_ext
      intro s
      change (show (O.obj.obj U : Type v) from
          (sheafRingHomMul S (sheafRingHomOne S) a).hom.app U s) =
        (show (O.obj.obj U : Type v) from a.hom.app U s)
      change 1 * (show (O.obj.obj U : Type v) from a.hom.app U s) = _
      exact one_mul _
    mul_one := by
      intro a
      apply CategoryTheory.Sheaf.hom_ext
      apply NatTrans.ext
      funext U
      apply ConcreteCategory.hom_ext
      intro s
      change (show (O.obj.obj U : Type v) from
          (sheafRingHomMul S a (sheafRingHomOne S)).hom.app U s) =
        (show (O.obj.obj U : Type v) from a.hom.app U s)
      change (show (O.obj.obj U : Type v) from a.hom.app U s) * 1 = _
      exact mul_one _
    zero_mul := by
      intro a
      apply CategoryTheory.Sheaf.hom_ext
      apply NatTrans.ext
      funext U
      apply ConcreteCategory.hom_ext
      intro s
      change (show (O.obj.obj U : Type v) from
          (sheafRingHomMul S (sheafRingHomZero S) a).hom.app U s) = 0
      change 0 * (show (O.obj.obj U : Type v) from a.hom.app U s) = 0
      exact zero_mul _
    mul_zero := by
      intro a
      apply CategoryTheory.Sheaf.hom_ext
      apply NatTrans.ext
      funext U
      apply ConcreteCategory.hom_ext
      intro s
      change (show (O.obj.obj U : Type v) from
          (sheafRingHomMul S a (sheafRingHomZero S)).hom.app U s) = 0
      change (show (O.obj.obj U : Type v) from a.hom.app U s) * 0 = 0
      exact mul_zero _
    left_distrib := by
      intro a b c
      apply CategoryTheory.Sheaf.hom_ext
      apply NatTrans.ext
      funext U
      apply ConcreteCategory.hom_ext
      intro s
      change (show (O.obj.obj U : Type v) from
          (sheafRingHomMul S a (sheafRingHomAdd S b c)).hom.app U s) =
        (show (O.obj.obj U : Type v) from
          (sheafRingHomAdd S (sheafRingHomMul S a b)
            (sheafRingHomMul S a c)).hom.app U s)
      change (show (O.obj.obj U : Type v) from a.hom.app U s) *
          ((show (O.obj.obj U : Type v) from b.hom.app U s) +
            (show (O.obj.obj U : Type v) from c.hom.app U s)) =
        (show (O.obj.obj U : Type v) from a.hom.app U s) *
            (show (O.obj.obj U : Type v) from b.hom.app U s) +
          (show (O.obj.obj U : Type v) from a.hom.app U s) *
            (show (O.obj.obj U : Type v) from c.hom.app U s)
      exact left_distrib _ _ _
    right_distrib := by
      intro a b c
      apply CategoryTheory.Sheaf.hom_ext
      apply NatTrans.ext
      funext U
      apply ConcreteCategory.hom_ext
      intro s
      change (show (O.obj.obj U : Type v) from
          (sheafRingHomMul S (sheafRingHomAdd S a b) c).hom.app U s) =
        (show (O.obj.obj U : Type v) from
          (sheafRingHomAdd S (sheafRingHomMul S a c)
            (sheafRingHomMul S b c)).hom.app U s)
      change ((show (O.obj.obj U : Type v) from a.hom.app U s) +
          (show (O.obj.obj U : Type v) from b.hom.app U s)) *
            (show (O.obj.obj U : Type v) from c.hom.app U s) =
        (show (O.obj.obj U : Type v) from a.hom.app U s) *
            (show (O.obj.obj U : Type v) from c.hom.app U s) +
          (show (O.obj.obj U : Type v) from b.hom.app U s) *
            (show (O.obj.obj U : Type v) from c.hom.app U s)
      exact right_distrib _ _ _ }

private noncomputable def sheafHomModule {X : TopCat.{v}}
    {O : RingSheaf.{v, v} X} {F : Mod O} (S : TopCat.Sheaf (Type v) X) :
    (letI : Ring (S ⟶ ringSetSheaf O) := sheafRingHomRing S;
      letI : AddCommGroup (S ⟶ moduleSetSheaf F) := sheafHomAddCommGroup S;
      Module (S ⟶ ringSetSheaf O) (S ⟶ moduleSetSheaf F)) := by
  letI : Ring (S ⟶ ringSetSheaf O) := sheafRingHomRing S
  letI : AddCommGroup (S ⟶ moduleSetSheaf F) := sheafHomAddCommGroup S
  letI : SMul (S ⟶ ringSetSheaf O) (S ⟶ moduleSetSheaf F) :=
    ⟨sheafHomSmul S⟩
  exact {
    smul := sheafHomSmul S
    one_smul := by
      intro a
      apply CategoryTheory.Sheaf.hom_ext
      apply NatTrans.ext
      funext U
      apply ConcreteCategory.hom_ext
      intro s
      change (show (F.val.obj U : Type v) from
          (sheafHomSmul S (sheafRingHomOne S) a).hom.app U s) =
        (show (F.val.obj U : Type v) from a.hom.app U s)
      change (1 : (O.obj.obj U : Type v)) •
          (show (F.val.obj U : Type v) from a.hom.app U s) = _
      exact one_smul _ _
    mul_smul := by
      intro r s a
      apply CategoryTheory.Sheaf.hom_ext
      apply NatTrans.ext
      funext U
      apply ConcreteCategory.hom_ext
      intro t
      change (show (F.val.obj U : Type v) from
          (sheafHomSmul S (sheafRingHomMul S r s) a).hom.app U t) =
        (show (F.val.obj U : Type v) from
          (sheafHomSmul S r (sheafHomSmul S s a)).hom.app U t)
      change ((show (O.obj.obj U : Type v) from r.hom.app U t) *
          (show (O.obj.obj U : Type v) from s.hom.app U t)) •
            (show (F.val.obj U : Type v) from a.hom.app U t) =
        (show (O.obj.obj U : Type v) from r.hom.app U t) •
          ((show (O.obj.obj U : Type v) from s.hom.app U t) •
            (show (F.val.obj U : Type v) from a.hom.app U t))
      exact mul_smul _ _ _
    smul_add := by
      intro r a b
      apply CategoryTheory.Sheaf.hom_ext
      apply NatTrans.ext
      funext U
      apply ConcreteCategory.hom_ext
      intro t
      change (show (F.val.obj U : Type v) from
          (sheafHomSmul S r (sheafHomAdd S a b)).hom.app U t) =
        (show (F.val.obj U : Type v) from
          (sheafHomAdd S (sheafHomSmul S r a)
            (sheafHomSmul S r b)).hom.app U t)
      change (show (O.obj.obj U : Type v) from r.hom.app U t) •
          ((show (F.val.obj U : Type v) from a.hom.app U t) +
            (show (F.val.obj U : Type v) from b.hom.app U t)) =
        (show (O.obj.obj U : Type v) from r.hom.app U t) •
            (show (F.val.obj U : Type v) from a.hom.app U t) +
          (show (O.obj.obj U : Type v) from r.hom.app U t) •
            (show (F.val.obj U : Type v) from b.hom.app U t)
      exact smul_add _ _ _
    smul_zero := by
      intro r
      apply CategoryTheory.Sheaf.hom_ext
      apply NatTrans.ext
      funext U
      apply ConcreteCategory.hom_ext
      intro t
      change (show (F.val.obj U : Type v) from
          (sheafHomSmul S r (sheafHomZero S)).hom.app U t) = 0
      change (show (O.obj.obj U : Type v) from r.hom.app U t) •
          (0 : (F.val.obj U : Type v)) = 0
      exact smul_zero _
    add_smul := by
      intro r s a
      apply CategoryTheory.Sheaf.hom_ext
      apply NatTrans.ext
      funext U
      apply ConcreteCategory.hom_ext
      intro t
      change (show (F.val.obj U : Type v) from
          (sheafHomSmul S (sheafRingHomAdd S r s) a).hom.app U t) =
        (show (F.val.obj U : Type v) from
          (sheafHomAdd S (sheafHomSmul S r a)
            (sheafHomSmul S s a)).hom.app U t)
      change ((show (O.obj.obj U : Type v) from r.hom.app U t) +
          (show (O.obj.obj U : Type v) from s.hom.app U t)) •
            (show (F.val.obj U : Type v) from a.hom.app U t) =
        (show (O.obj.obj U : Type v) from r.hom.app U t) •
            (show (F.val.obj U : Type v) from a.hom.app U t) +
          (show (O.obj.obj U : Type v) from s.hom.app U t) •
            (show (F.val.obj U : Type v) from a.hom.app U t)
      exact add_smul _ _ _
    zero_smul := by
      intro a
      apply CategoryTheory.Sheaf.hom_ext
      apply NatTrans.ext
      funext U
      apply ConcreteCategory.hom_ext
      intro t
      change (show (F.val.obj U : Type v) from
          (sheafHomSmul S (sheafRingHomZero S) a).hom.app U t) = 0
      change (0 : (O.obj.obj U : Type v)) •
          (show (F.val.obj U : Type v) from a.hom.app U t) = 0
      exact zero_smul _ _ }

theorem isSectionwiseBilinear_iff_isHomCharacterization
    {X : TopCat.{v}} {O : RingSheaf.{v, v} X} {F G H : Mod O}
    (f : ModuleSetMap F G H) :
  IsSectionwiseBilinear f ↔ IsHomCharacterization f := by
  constructor
  · intro h S instR instF instG instH modF modG modH hp
    unfold IsHomRuleBilinear
    refine ⟨{
      toFun := sheafHomBilinearRule f S
      map_add_left' := ?_
      map_smul_left' := ?_
      map_add_right' := ?_
      map_smul_right' := ?_ }, ?_⟩
    · intro x y z
      apply CategoryTheory.Sheaf.hom_ext
      apply NatTrans.ext
      funext U
      apply ConcreteCategory.hom_ext
      intro s
      change f.hom.app U
          ((sheafHomProduct S (x + y) z).hom.app U s) =
        ((sheafHomBilinearRule f S x z +
          sheafHomBilinearRule f S y z).hom.app U) s
      rw [hp.2.2.1 _ _ U.unop s]
      rw [sheafHomBilinearRule_app_eq f S x z U s,
        sheafHomBilinearRule_app_eq f S y z U s]
      rw [sheafHomProduct_app_eq S (x + y) z U s]
      change sectionMap f U.unop ((x + y).hom.app U s) (z.hom.app U s) =
        sectionMap f U.unop (x.hom.app U s) (z.hom.app U s) +
        sectionMap f U.unop (y.hom.app U s) (z.hom.app U s)
      obtain ⟨g, hg⟩ := h U.unop
      have hxy :
          (x + y).hom.app U s =
            (show (F.val.obj (op U.unop) : Type v) from x.hom.app U s) +
              (show (F.val.obj (op U.unop) : Type v) from y.hom.app U s) := by
        simpa only [op_unop] using hp.1 x y U.unop s
      calc
        sectionMap f U.unop ((x + y).hom.app U s) (z.hom.app U s) =
            g ((x + y).hom.app U s) (z.hom.app U s) :=
          (hg _ _).symm
        _ = g
            ((show (F.val.obj (op U.unop) : Type v) from x.hom.app U s) +
              (show (F.val.obj (op U.unop) : Type v) from y.hom.app U s))
            (z.hom.app U s) := by
          rw [hxy]
        _ = g (x.hom.app U s) (z.hom.app U s) +
            g (y.hom.app U s) (z.hom.app U s) :=
          g.map_add_left' _ _ _
        _ = sectionMap f U.unop (x.hom.app U s) (z.hom.app U s) +
            sectionMap f U.unop (y.hom.app U s) (z.hom.app U s) := by
          exact congrArg₂ (fun p q => p + q) (hg _ _) (hg _ _)
    · intro r x z
      apply CategoryTheory.Sheaf.hom_ext
      apply NatTrans.ext
      funext U
      apply ConcreteCategory.hom_ext
      intro s
      change f.hom.app U
          ((sheafHomProduct S (r • x) z).hom.app U s) =
        ((r • sheafHomBilinearRule f S x z).hom.app U) s
      rw [hp.2.2.2.2.2 r (sheafHomBilinearRule f S x z) U.unop s]
      rw [sheafHomBilinearRule_app_eq f S x z U s]
      rw [sheafHomProduct_app_eq S (r • x) z U s]
      change sectionMap f U.unop ((r • x).hom.app U s) (z.hom.app U s) =
        (show (O.obj.obj (op U.unop) : Type v) from r.hom.app U s) •
          sectionMap f U.unop (x.hom.app U s) (z.hom.app U s)
      obtain ⟨g, hg⟩ := h U.unop
      have hxr :
          (r • x).hom.app U s =
            (show (O.obj.obj (op U.unop) : Type v) from r.hom.app U s) •
              (show (F.val.obj (op U.unop) : Type v) from x.hom.app U s) := by
        simpa only [op_unop] using hp.2.2.2.1 r x U.unop s
      calc
        sectionMap f U.unop ((r • x).hom.app U s) (z.hom.app U s) =
            g ((r • x).hom.app U s) (z.hom.app U s) :=
          (hg _ _).symm
        _ = g
            ((show (O.obj.obj (op U.unop) : Type v) from r.hom.app U s) •
              (show (F.val.obj (op U.unop) : Type v) from x.hom.app U s))
            (z.hom.app U s) := by
          rw [hxr]
        _ = (show (O.obj.obj (op U.unop) : Type v) from r.hom.app U s) •
            g (x.hom.app U s) (z.hom.app U s) :=
          g.map_smul_left' _ _ _
        _ = (show (O.obj.obj (op U.unop) : Type v) from r.hom.app U s) •
            sectionMap f U.unop (x.hom.app U s) (z.hom.app U s) := by
          exact congrArg (fun q =>
            (show (O.obj.obj (op U.unop) : Type v) from r.hom.app U s) • q)
            (hg _ _)
    · intro x y z
      apply CategoryTheory.Sheaf.hom_ext
      apply NatTrans.ext
      funext U
      apply ConcreteCategory.hom_ext
      intro s
      change f.hom.app U
          ((sheafHomProduct S x (y + z)).hom.app U s) =
        ((sheafHomBilinearRule f S x y +
          sheafHomBilinearRule f S x z).hom.app U) s
      rw [hp.2.2.1 _ _ U.unop s]
      rw [sheafHomBilinearRule_app_eq f S x y U s,
        sheafHomBilinearRule_app_eq f S x z U s]
      rw [sheafHomProduct_app_eq S x (y + z) U s]
      change sectionMap f U.unop (x.hom.app U s) ((y + z).hom.app U s) =
        sectionMap f U.unop (x.hom.app U s) (y.hom.app U s) +
        sectionMap f U.unop (x.hom.app U s) (z.hom.app U s)
      obtain ⟨g, hg⟩ := h U.unop
      have hyz :
          (y + z).hom.app U s =
            (show (G.val.obj (op U.unop) : Type v) from y.hom.app U s) +
              (show (G.val.obj (op U.unop) : Type v) from z.hom.app U s) := by
        simpa only [op_unop] using hp.2.1 y z U.unop s
      calc
        sectionMap f U.unop (x.hom.app U s) ((y + z).hom.app U s) =
            g (x.hom.app U s) ((y + z).hom.app U s) :=
          (hg _ _).symm
        _ = g (x.hom.app U s)
            ((show (G.val.obj (op U.unop) : Type v) from y.hom.app U s) +
              (show (G.val.obj (op U.unop) : Type v) from z.hom.app U s)) := by
          rw [hyz]
        _ = g (x.hom.app U s) (y.hom.app U s) +
            g (x.hom.app U s) (z.hom.app U s) :=
          g.map_add_right' _ _ _
        _ = sectionMap f U.unop (x.hom.app U s) (y.hom.app U s) +
            sectionMap f U.unop (x.hom.app U s) (z.hom.app U s) := by
          exact congrArg₂ (fun p q => p + q) (hg _ _) (hg _ _)
    · intro r x y
      apply CategoryTheory.Sheaf.hom_ext
      apply NatTrans.ext
      funext U
      apply ConcreteCategory.hom_ext
      intro s
      change f.hom.app U
          ((sheafHomProduct S x (r • y)).hom.app U s) =
        ((r • sheafHomBilinearRule f S x y).hom.app U) s
      rw [hp.2.2.2.2.2 r (sheafHomBilinearRule f S x y) U.unop s]
      rw [sheafHomBilinearRule_app_eq f S x y U s]
      rw [sheafHomProduct_app_eq S x (r • y) U s]
      change sectionMap f U.unop (x.hom.app U s) ((r • y).hom.app U s) =
        (show (O.obj.obj (op U.unop) : Type v) from r.hom.app U s) •
          sectionMap f U.unop (x.hom.app U s) (y.hom.app U s)
      obtain ⟨g, hg⟩ := h U.unop
      have hyr :
          (r • y).hom.app U s =
            (show (O.obj.obj (op U.unop) : Type v) from r.hom.app U s) •
              (show (G.val.obj (op U.unop) : Type v) from y.hom.app U s) := by
        simpa only [op_unop] using hp.2.2.2.2.1 r y U.unop s
      calc
        sectionMap f U.unop (x.hom.app U s) ((r • y).hom.app U s) =
            g (x.hom.app U s) ((r • y).hom.app U s) :=
          (hg _ _).symm
        _ = g (x.hom.app U s)
            ((show (O.obj.obj (op U.unop) : Type v) from r.hom.app U s) •
              (show (G.val.obj (op U.unop) : Type v) from y.hom.app U s)) := by
          rw [hyr]
        _ = (show (O.obj.obj (op U.unop) : Type v) from r.hom.app U s) •
            g (x.hom.app U s) (y.hom.app U s) :=
          g.map_smul_right' _ _ _
        _ = (show (O.obj.obj (op U.unop) : Type v) from r.hom.app U s) •
            sectionMap f U.unop (x.hom.app U s) (y.hom.app U s) := by
          exact congrArg (fun q =>
            (show (O.obj.obj (op U.unop) : Type v) from r.hom.app U s) • q)
            (hg _ _)
    · intro a b
      rfl
  · intro h U
    let S : TopCat.Sheaf (Type v) X :=
      ⟨(Opens.grothendieckTopology X).sheafify (CategoryTheory.yoneda.obj U),
        (Opens.grothendieckTopology X).sheafify_isSheaf
          (CategoryTheory.yoneda.obj U)⟩
    letI : Ring (S ⟶ ringSetSheaf O) := sheafRingHomRing S
    letI : AddCommGroup (S ⟶ moduleSetSheaf F) := sheafHomAddCommGroup S
    letI : AddCommGroup (S ⟶ moduleSetSheaf G) := sheafHomAddCommGroup S
    letI : AddCommGroup (S ⟶ moduleSetSheaf H) := sheafHomAddCommGroup S
    letI : Module (S ⟶ ringSetSheaf O) (S ⟶ moduleSetSheaf F) :=
      sheafHomModule S
    letI : Module (S ⟶ ringSetSheaf O) (S ⟶ moduleSetSheaf G) :=
      sheafHomModule S
    letI : Module (S ⟶ ringSetSheaf O) (S ⟶ moduleSetSheaf H) :=
      sheafHomModule S
    have hp : IsPointwiseBilinearOperations (O := O) (F := F) (G := G)
        (H := H) S := by
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
        intro a b U' s <;> rfl
    let xHom : (F.val.obj (op U) : Type v) → (S ⟶ moduleSetSheaf F) :=
      fun x => ObjectProperty.homMk
        ((Opens.grothendieckTopology X).sheafifyLift
          (yonedaEquiv.symm x) (moduleSetSheaf F).property)
    let yHom : (G.val.obj (op U) : Type v) → (S ⟶ moduleSetSheaf G) :=
      fun y => ObjectProperty.homMk
        ((Opens.grothendieckTopology X).sheafifyLift
          (yonedaEquiv.symm y) (moduleSetSheaf G).property)
    let rHom : (O.obj.obj (op U) : Type v) → (S ⟶ ringSetSheaf O) :=
      fun r => ObjectProperty.homMk
        ((Opens.grothendieckTopology X).sheafifyLift
          (yonedaEquiv.symm r) (ringSetSheaf O).property)
    have xHom_add (x₁ x₂ : (F.val.obj (op U) : Type v)) :
        xHom (x₁ + x₂) = xHom x₁ + xHom x₂ := by
      apply CategoryTheory.Sheaf.hom_ext
      apply (Opens.grothendieckTopology X).sheafify_hom_ext
        _ _ (moduleSetSheaf F).property
      dsimp [xHom]
      change
        (Opens.grothendieckTopology X).toSheafify (CategoryTheory.yoneda.obj U) ≫
            (Opens.grothendieckTopology X).sheafifyLift
              (yonedaEquiv.symm (x₁ + x₂)) (moduleSetSheaf F).property = _
      rw [CategoryTheory.GrothendieckTopology.toSheafify_sheafifyLift]
      apply NatTrans.ext
      funext V
      apply ConcreteCategory.hom_ext
      intro q
      dsimp [CategoryTheory.yonedaEquiv]
      change
        (moduleSetSheaf F).obj.map q.op (x₁ + x₂) =
          (xHom x₁ + xHom x₂).hom.app (op V.unop)
            (show S.obj.obj (op V.unop) from
              ((Opens.grothendieckTopology X).toSheafify
                (CategoryTheory.yoneda.obj U)).app (op V.unop) q)
      have hpoint := hp.1 (xHom x₁) (xHom x₂) V.unop
        (show S.obj.obj (op V.unop) from
          ((Opens.grothendieckTopology X).toSheafify
            (CategoryTheory.yoneda.obj U)).app (op V.unop) q)
      have hpoint' :
          (xHom x₁ + xHom x₂).hom.app V
              (show S.obj.obj V from
                ((Opens.grothendieckTopology X).toSheafify
                  (CategoryTheory.yoneda.obj U)).app V q) =
            (show (F.val.obj (op V.unop) : Type v) from
              (xHom x₁).hom.app V
                (show S.obj.obj V from
                  ((Opens.grothendieckTopology X).toSheafify
                    (CategoryTheory.yoneda.obj U)).app V q)) +
              (show (F.val.obj (op V.unop) : Type v) from
                (xHom x₂).hom.app V
                  (show S.obj.obj V from
                    ((Opens.grothendieckTopology X).toSheafify
                      (CategoryTheory.yoneda.obj U)).app V q)) := by
        simpa only [op_unop] using hpoint
      rw [hpoint']
      have h1 :=
        CategoryTheory.GrothendieckTopology.toSheafify_sheafifyLift
          (J := Opens.grothendieckTopology X)
          (P := CategoryTheory.yoneda.obj U) (Q := (moduleSetSheaf F).obj)
          (yonedaEquiv.symm x₁) (moduleSetSheaf F).property
      have h1V := congrArg (fun k => (ConcreteCategory.hom (k.app V)) q) h1
      have hx1 :
          (show (F.val.obj (op V.unop) : Type v) from
            (xHom x₁).hom.app V
              (show S.obj.obj V from
                ((Opens.grothendieckTopology X).toSheafify
                  (CategoryTheory.yoneda.obj U)).app V q)) =
            (F.val.map q.op).hom x₁ := by
        change
          (ConcreteCategory.hom
            (((Opens.grothendieckTopology X).toSheafify
                (CategoryTheory.yoneda.obj U) ≫
              (Opens.grothendieckTopology X).sheafifyLift
                (yonedaEquiv.symm x₁) (moduleSetSheaf F).property).app V)) q =
            (ConcreteCategory.hom ((yonedaEquiv.symm x₁).app V)) q
        exact h1V
      rw [hx1]
      have h2 :=
        CategoryTheory.GrothendieckTopology.toSheafify_sheafifyLift
          (J := Opens.grothendieckTopology X)
          (P := CategoryTheory.yoneda.obj U) (Q := (moduleSetSheaf F).obj)
          (yonedaEquiv.symm x₂) (moduleSetSheaf F).property
      have h2V := congrArg (fun k => (ConcreteCategory.hom (k.app V)) q) h2
      have hx2 :
          (show (F.val.obj (op V.unop) : Type v) from
            (xHom x₂).hom.app V
              (show S.obj.obj V from
                ((Opens.grothendieckTopology X).toSheafify
                  (CategoryTheory.yoneda.obj U)).app V q)) =
            (F.val.map q.op).hom x₂ := by
        change
          (ConcreteCategory.hom
            (((Opens.grothendieckTopology X).toSheafify
                (CategoryTheory.yoneda.obj U) ≫
              (Opens.grothendieckTopology X).sheafifyLift
                (yonedaEquiv.symm x₂) (moduleSetSheaf F).property).app V)) q =
            (ConcreteCategory.hom ((yonedaEquiv.symm x₂).app V)) q
        exact h2V
      rw [hx2]
      have hmap (x : (F.val.obj (op U) : Type v)) :
          (moduleSetSheaf F).obj.map q.op x =
            (((SheafOfModules.toSheaf O).obj F).obj.map q.op).hom x := by
        rfl
      rw [hmap]
      exact (((SheafOfModules.toSheaf O).obj F).obj.map q.op).hom.map_add _ _
    have yHom_add (y₁ y₂ : (G.val.obj (op U) : Type v)) :
        yHom (y₁ + y₂) = yHom y₁ + yHom y₂ := by
      apply CategoryTheory.Sheaf.hom_ext
      apply (Opens.grothendieckTopology X).sheafify_hom_ext
        _ _ (moduleSetSheaf G).property
      dsimp [yHom]
      change
        (Opens.grothendieckTopology X).toSheafify (CategoryTheory.yoneda.obj U) ≫
            (Opens.grothendieckTopology X).sheafifyLift
              (yonedaEquiv.symm (y₁ + y₂)) (moduleSetSheaf G).property = _
      rw [CategoryTheory.GrothendieckTopology.toSheafify_sheafifyLift]
      apply NatTrans.ext
      funext V
      apply ConcreteCategory.hom_ext
      intro q
      dsimp [CategoryTheory.yonedaEquiv]
      change
        (moduleSetSheaf G).obj.map q.op (y₁ + y₂) =
          (yHom y₁ + yHom y₂).hom.app (op V.unop)
            (show S.obj.obj (op V.unop) from
              ((Opens.grothendieckTopology X).toSheafify
                (CategoryTheory.yoneda.obj U)).app (op V.unop) q)
      have hpoint := hp.2.1 (yHom y₁) (yHom y₂) V.unop
        (show S.obj.obj (op V.unop) from
          ((Opens.grothendieckTopology X).toSheafify
            (CategoryTheory.yoneda.obj U)).app (op V.unop) q)
      have hpoint' :
          (yHom y₁ + yHom y₂).hom.app V
              (show S.obj.obj V from
                ((Opens.grothendieckTopology X).toSheafify
                  (CategoryTheory.yoneda.obj U)).app V q) =
            (show (G.val.obj (op V.unop) : Type v) from
              (yHom y₁).hom.app V
                (show S.obj.obj V from
                  ((Opens.grothendieckTopology X).toSheafify
                    (CategoryTheory.yoneda.obj U)).app V q)) +
              (show (G.val.obj (op V.unop) : Type v) from
                (yHom y₂).hom.app V
                  (show S.obj.obj V from
                    ((Opens.grothendieckTopology X).toSheafify
                      (CategoryTheory.yoneda.obj U)).app V q)) := by
        simpa only [op_unop] using hpoint
      rw [hpoint']
      have h1 :=
        CategoryTheory.GrothendieckTopology.toSheafify_sheafifyLift
          (J := Opens.grothendieckTopology X)
          (P := CategoryTheory.yoneda.obj U) (Q := (moduleSetSheaf G).obj)
          (yonedaEquiv.symm y₁) (moduleSetSheaf G).property
      have h1V := congrArg (fun k => (ConcreteCategory.hom (k.app V)) q) h1
      have hy1 :
          (show (G.val.obj (op V.unop) : Type v) from
            (yHom y₁).hom.app V
              (show S.obj.obj V from
                ((Opens.grothendieckTopology X).toSheafify
                  (CategoryTheory.yoneda.obj U)).app V q)) =
            (G.val.map q.op).hom y₁ := by
        change
          (ConcreteCategory.hom
            (((Opens.grothendieckTopology X).toSheafify
                (CategoryTheory.yoneda.obj U) ≫
              (Opens.grothendieckTopology X).sheafifyLift
                (yonedaEquiv.symm y₁) (moduleSetSheaf G).property).app V)) q =
            (ConcreteCategory.hom ((yonedaEquiv.symm y₁).app V)) q
        exact h1V
      rw [hy1]
      have h2 :=
        CategoryTheory.GrothendieckTopology.toSheafify_sheafifyLift
          (J := Opens.grothendieckTopology X)
          (P := CategoryTheory.yoneda.obj U) (Q := (moduleSetSheaf G).obj)
          (yonedaEquiv.symm y₂) (moduleSetSheaf G).property
      have h2V := congrArg (fun k => (ConcreteCategory.hom (k.app V)) q) h2
      have hy2 :
          (show (G.val.obj (op V.unop) : Type v) from
            (yHom y₂).hom.app V
              (show S.obj.obj V from
                ((Opens.grothendieckTopology X).toSheafify
                  (CategoryTheory.yoneda.obj U)).app V q)) =
            (G.val.map q.op).hom y₂ := by
        change
          (ConcreteCategory.hom
            (((Opens.grothendieckTopology X).toSheafify
                (CategoryTheory.yoneda.obj U) ≫
              (Opens.grothendieckTopology X).sheafifyLift
                (yonedaEquiv.symm y₂) (moduleSetSheaf G).property).app V)) q =
            (ConcreteCategory.hom ((yonedaEquiv.symm y₂).app V)) q
        exact h2V
      rw [hy2]
      have hmap (y : (G.val.obj (op U) : Type v)) :
          (moduleSetSheaf G).obj.map q.op y =
            (((SheafOfModules.toSheaf O).obj G).obj.map q.op).hom y := by
        rfl
      rw [hmap]
      exact (((SheafOfModules.toSheaf O).obj G).obj.map q.op).hom.map_add _ _
    have xHom_smul (r : (O.obj.obj (op U) : Type v))
        (x : (F.val.obj (op U) : Type v)) :
        xHom (r • x) = rHom r • xHom x := by
      apply CategoryTheory.Sheaf.hom_ext
      apply (Opens.grothendieckTopology X).sheafify_hom_ext
        _ _ (moduleSetSheaf F).property
      dsimp [xHom, rHom]
      change
        (Opens.grothendieckTopology X).toSheafify (CategoryTheory.yoneda.obj U) ≫
            (Opens.grothendieckTopology X).sheafifyLift
              (yonedaEquiv.symm (r • x)) (moduleSetSheaf F).property = _
      rw [CategoryTheory.GrothendieckTopology.toSheafify_sheafifyLift]
      apply NatTrans.ext
      funext V
      apply ConcreteCategory.hom_ext
      intro q
      dsimp [CategoryTheory.yonedaEquiv]
      change
        (moduleSetSheaf F).obj.map q.op (r • x) =
          (rHom r • xHom x).hom.app (op V.unop)
            (show S.obj.obj (op V.unop) from
              ((Opens.grothendieckTopology X).toSheafify
                (CategoryTheory.yoneda.obj U)).app (op V.unop) q)
      have hpoint := hp.2.2.2.1 (rHom r) (xHom x) V.unop
        (show S.obj.obj (op V.unop) from
          ((Opens.grothendieckTopology X).toSheafify
            (CategoryTheory.yoneda.obj U)).app (op V.unop) q)
      have hpoint' :
          (rHom r • xHom x).hom.app V
              (show S.obj.obj V from
                ((Opens.grothendieckTopology X).toSheafify
                  (CategoryTheory.yoneda.obj U)).app V q) =
            (show (O.obj.obj (op V.unop) : Type v) from
              (rHom r).hom.app V
                (show S.obj.obj V from
                  ((Opens.grothendieckTopology X).toSheafify
                    (CategoryTheory.yoneda.obj U)).app V q)) •
              (show (F.val.obj (op V.unop) : Type v) from
                (xHom x).hom.app V
                  (show S.obj.obj V from
                    ((Opens.grothendieckTopology X).toSheafify
                      (CategoryTheory.yoneda.obj U)).app V q)) := by
        simpa only [op_unop] using hpoint
      rw [hpoint']
      have hr :=
        CategoryTheory.GrothendieckTopology.toSheafify_sheafifyLift
          (J := Opens.grothendieckTopology X)
          (P := CategoryTheory.yoneda.obj U) (Q := (ringSetSheaf O).obj)
          (yonedaEquiv.symm r) (ringSetSheaf O).property
      have hrV := congrArg (fun k => (ConcreteCategory.hom (k.app V)) q) hr
      have hrv :
          (show (O.obj.obj (op V.unop) : Type v) from
            (rHom r).hom.app V
              (show S.obj.obj V from
                ((Opens.grothendieckTopology X).toSheafify
                  (CategoryTheory.yoneda.obj U)).app V q)) =
            (O.obj.map q.op).hom r := by
        change
          (ConcreteCategory.hom
            (((Opens.grothendieckTopology X).toSheafify
                (CategoryTheory.yoneda.obj U) ≫
              (Opens.grothendieckTopology X).sheafifyLift
                (yonedaEquiv.symm r) (ringSetSheaf O).property).app V)) q =
            (ConcreteCategory.hom ((yonedaEquiv.symm r).app V)) q
        exact hrV
      rw [hrv]
      have hf :=
        CategoryTheory.GrothendieckTopology.toSheafify_sheafifyLift
          (J := Opens.grothendieckTopology X)
          (P := CategoryTheory.yoneda.obj U) (Q := (moduleSetSheaf F).obj)
          (yonedaEquiv.symm x) (moduleSetSheaf F).property
      have hfV := congrArg (fun k => (ConcreteCategory.hom (k.app V)) q) hf
      have hfx :
          (show (F.val.obj (op V.unop) : Type v) from
            (xHom x).hom.app V
              (show S.obj.obj V from
                ((Opens.grothendieckTopology X).toSheafify
                  (CategoryTheory.yoneda.obj U)).app V q)) =
            (F.val.map q.op).hom x := by
        change
          (ConcreteCategory.hom
            (((Opens.grothendieckTopology X).toSheafify
                (CategoryTheory.yoneda.obj U) ≫
              (Opens.grothendieckTopology X).sheafifyLift
                (yonedaEquiv.symm x) (moduleSetSheaf F).property).app V)) q =
            (ConcreteCategory.hom ((yonedaEquiv.symm x).app V)) q
        exact hfV
      rw [hfx]
      have hmap (z : (F.val.obj (op U) : Type v)) :
          (moduleSetSheaf F).obj.map q.op z =
            (((SheafOfModules.toSheaf O).obj F).obj.map q.op).hom z := by
        rfl
      rw [hmap]
      exact PresheafOfModules.map_smul F.val q.op r x
    have yHom_smul (r : (O.obj.obj (op U) : Type v))
        (y : (G.val.obj (op U) : Type v)) :
        yHom (r • y) = rHom r • yHom y := by
      apply CategoryTheory.Sheaf.hom_ext
      apply (Opens.grothendieckTopology X).sheafify_hom_ext
        _ _ (moduleSetSheaf G).property
      dsimp [yHom, rHom]
      change
        (Opens.grothendieckTopology X).toSheafify (CategoryTheory.yoneda.obj U) ≫
            (Opens.grothendieckTopology X).sheafifyLift
              (yonedaEquiv.symm (r • y)) (moduleSetSheaf G).property = _
      rw [CategoryTheory.GrothendieckTopology.toSheafify_sheafifyLift]
      apply NatTrans.ext
      funext V
      apply ConcreteCategory.hom_ext
      intro q
      dsimp [CategoryTheory.yonedaEquiv]
      change
        (moduleSetSheaf G).obj.map q.op (r • y) =
          (rHom r • yHom y).hom.app (op V.unop)
            (show S.obj.obj (op V.unop) from
              ((Opens.grothendieckTopology X).toSheafify
                (CategoryTheory.yoneda.obj U)).app (op V.unop) q)
      have hpoint := hp.2.2.2.2.1 (rHom r) (yHom y) V.unop
        (show S.obj.obj (op V.unop) from
          ((Opens.grothendieckTopology X).toSheafify
            (CategoryTheory.yoneda.obj U)).app (op V.unop) q)
      have hpoint' :
          (rHom r • yHom y).hom.app V
              (show S.obj.obj V from
                ((Opens.grothendieckTopology X).toSheafify
                  (CategoryTheory.yoneda.obj U)).app V q) =
            (show (O.obj.obj (op V.unop) : Type v) from
              (rHom r).hom.app V
                (show S.obj.obj V from
                  ((Opens.grothendieckTopology X).toSheafify
                    (CategoryTheory.yoneda.obj U)).app V q)) •
              (show (G.val.obj (op V.unop) : Type v) from
                (yHom y).hom.app V
                  (show S.obj.obj V from
                    ((Opens.grothendieckTopology X).toSheafify
                      (CategoryTheory.yoneda.obj U)).app V q)) := by
        simpa only [op_unop] using hpoint
      rw [hpoint']
      have hr :=
        CategoryTheory.GrothendieckTopology.toSheafify_sheafifyLift
          (J := Opens.grothendieckTopology X)
          (P := CategoryTheory.yoneda.obj U) (Q := (ringSetSheaf O).obj)
          (yonedaEquiv.symm r) (ringSetSheaf O).property
      have hrV := congrArg (fun k => (ConcreteCategory.hom (k.app V)) q) hr
      have hrv :
          (show (O.obj.obj (op V.unop) : Type v) from
            (rHom r).hom.app V
              (show S.obj.obj V from
                ((Opens.grothendieckTopology X).toSheafify
                  (CategoryTheory.yoneda.obj U)).app V q)) =
            (O.obj.map q.op).hom r := by
        change
          (ConcreteCategory.hom
            (((Opens.grothendieckTopology X).toSheafify
                (CategoryTheory.yoneda.obj U) ≫
              (Opens.grothendieckTopology X).sheafifyLift
                (yonedaEquiv.symm r) (ringSetSheaf O).property).app V)) q =
            (ConcreteCategory.hom ((yonedaEquiv.symm r).app V)) q
        exact hrV
      rw [hrv]
      have hg :=
        CategoryTheory.GrothendieckTopology.toSheafify_sheafifyLift
          (J := Opens.grothendieckTopology X)
          (P := CategoryTheory.yoneda.obj U) (Q := (moduleSetSheaf G).obj)
          (yonedaEquiv.symm y) (moduleSetSheaf G).property
      have hgV := congrArg (fun k => (ConcreteCategory.hom (k.app V)) q) hg
      have hgy :
          (show (G.val.obj (op V.unop) : Type v) from
            (yHom y).hom.app V
              (show S.obj.obj V from
                ((Opens.grothendieckTopology X).toSheafify
                  (CategoryTheory.yoneda.obj U)).app V q)) =
            (G.val.map q.op).hom y := by
        change
          (ConcreteCategory.hom
            (((Opens.grothendieckTopology X).toSheafify
                (CategoryTheory.yoneda.obj U) ≫
              (Opens.grothendieckTopology X).sheafifyLift
                (yonedaEquiv.symm y) (moduleSetSheaf G).property).app V)) q =
            (ConcreteCategory.hom ((yonedaEquiv.symm y).app V)) q
        exact hgV
      rw [hgy]
      have hmap (z : (G.val.obj (op U) : Type v)) :
          (moduleSetSheaf G).obj.map q.op z =
            (((SheafOfModules.toSheaf O).obj G).obj.map q.op).hom z := by
        rfl
      rw [hmap]
      exact PresheafOfModules.map_smul G.val q.op r y
    let s0 : S.obj.obj (op U) :=
      ((Opens.grothendieckTopology X).toSheafify
        (CategoryTheory.yoneda.obj U)).app (op U) (𝟙 U)
    let evH : (S ⟶ moduleSetSheaf H) → (H.val.obj (op U) : Type v) :=
      fun a => a.hom.app (op U) s0
    have x0 (x : (F.val.obj (op U) : Type v)) :
        (xHom x).hom.app (op U) s0 = x := by
      have hx :=
        CategoryTheory.GrothendieckTopology.toSheafify_sheafifyLift
          (J := Opens.grothendieckTopology X)
          (P := CategoryTheory.yoneda.obj U) (Q := (moduleSetSheaf F).obj)
          (yonedaEquiv.symm x) (moduleSetSheaf F).property
      have hx0 := congrArg
        (fun k => (ConcreteCategory.hom (k.app (op U))) (𝟙 U)) hx
      change
        (ConcreteCategory.hom
          (((Opens.grothendieckTopology X).toSheafify
              (CategoryTheory.yoneda.obj U) ≫
            (Opens.grothendieckTopology X).sheafifyLift
              (yonedaEquiv.symm x) (moduleSetSheaf F).property).app (op U)))
            (𝟙 U) = x
      exact hx0.trans (by
        change CategoryTheory.yonedaEquiv
            (F := (moduleSetSheaf F).obj) (yonedaEquiv.symm x) = x
        exact Equiv.apply_symm_apply _ _)
    have y0 (y : (G.val.obj (op U) : Type v)) :
        (yHom y).hom.app (op U) s0 = y := by
      have hy :=
        CategoryTheory.GrothendieckTopology.toSheafify_sheafifyLift
          (J := Opens.grothendieckTopology X)
          (P := CategoryTheory.yoneda.obj U) (Q := (moduleSetSheaf G).obj)
          (yonedaEquiv.symm y) (moduleSetSheaf G).property
      have hy0 := congrArg
        (fun k => (ConcreteCategory.hom (k.app (op U))) (𝟙 U)) hy
      change
        (ConcreteCategory.hom
          (((Opens.grothendieckTopology X).toSheafify
              (CategoryTheory.yoneda.obj U) ≫
            (Opens.grothendieckTopology X).sheafifyLift
              (yonedaEquiv.symm y) (moduleSetSheaf G).property).app (op U)))
            (𝟙 U) = y
      exact hy0.trans (by
        change CategoryTheory.yonedaEquiv
            (F := (moduleSetSheaf G).obj) (yonedaEquiv.symm y) = y
        exact Equiv.apply_symm_apply _ _)
    have r0 (r : (O.obj.obj (op U) : Type v)) :
        (rHom r).hom.app (op U) s0 = r := by
      have hr :=
        CategoryTheory.GrothendieckTopology.toSheafify_sheafifyLift
          (J := Opens.grothendieckTopology X)
          (P := CategoryTheory.yoneda.obj U) (Q := (ringSetSheaf O).obj)
          (yonedaEquiv.symm r) (ringSetSheaf O).property
      have hr0 := congrArg
        (fun k => (ConcreteCategory.hom (k.app (op U))) (𝟙 U)) hr
      change
        (ConcreteCategory.hom
          (((Opens.grothendieckTopology X).toSheafify
              (CategoryTheory.yoneda.obj U) ≫
            (Opens.grothendieckTopology X).sheafifyLift
              (yonedaEquiv.symm r) (ringSetSheaf O).property).app (op U)))
            (𝟙 U) = r
      exact hr0.trans (by
        change CategoryTheory.yonedaEquiv
            (F := (ringSetSheaf O).obj) (yonedaEquiv.symm r) = r
        exact Equiv.apply_symm_apply _ _)
    have hh := h S hp
    rcases hh with ⟨g, hg⟩
    have eval_rule (a : S ⟶ moduleSetSheaf F)
        (b : S ⟶ moduleSetSheaf G) :
        evH (g a b) =
          sectionMap f U (a.hom.app (op U) s0) (b.hom.app (op U) s0) := by
      calc
        evH (g a b) = evH (sheafHomBilinearRule f S a b) :=
          congrArg evH (hg a b)
        _ = sectionMap f U (a.hom.app (op U) s0)
              (b.hom.app (op U) s0) := by
          change
            (show (H.val.obj (op U) : Type v) from
              (sheafHomBilinearRule f S a b).hom.app (op U) s0) = _
          exact sheafHomBilinearRule_app_eq f S a b (op U) s0
    refine ⟨{
      toFun := fun x y => evH (g (xHom x) (yHom y))
      map_add_left' := by
        intro x₁ x₂ y
        calc
          evH (g (xHom (x₁ + x₂)) (yHom y)) =
              evH (g (xHom x₁ + xHom x₂) (yHom y)) := by
            rw [xHom_add]
          _ = evH (g (xHom x₁) (yHom y)) +
              evH (g (xHom x₂) (yHom y)) := by
            calc
              evH (g (xHom x₁ + xHom x₂) (yHom y)) =
                  evH (g (xHom x₁) (yHom y) +
                    g (xHom x₂) (yHom y)) :=
                congrArg evH (g.map_add_left' _ _ _)
              _ = evH (g (xHom x₁) (yHom y)) +
                  evH (g (xHom x₂) (yHom y)) := by
                change
                  (show (H.val.obj (op U) : Type v) from
                    (g (xHom x₁) (yHom y) +
                      g (xHom x₂) (yHom y)).hom.app (op U) s0) =
                    (show (H.val.obj (op U) : Type v) from
                      (g (xHom x₁) (yHom y)).hom.app (op U) s0) +
                    (show (H.val.obj (op U) : Type v) from
                      (g (xHom x₂) (yHom y)).hom.app (op U) s0)
                exact hp.2.2.1 (g (xHom x₁) (yHom y))
                  (g (xHom x₂) (yHom y)) U s0
      map_smul_left' := by
        intro r x y
        calc
          evH (g (xHom (r • x)) (yHom y)) =
              evH (g (rHom r • xHom x) (yHom y)) := by
            rw [xHom_smul]
          _ = evH (rHom r • g (xHom x) (yHom y)) :=
            congrArg evH (g.map_smul_left' _ _ _)
          _ = (show (O.obj.obj (op U) : Type v) from
                (rHom r).hom.app (op U) s0) •
              evH (g (xHom x) (yHom y)) := by
            change
              (show (H.val.obj (op U) : Type v) from
                (rHom r • g (xHom x) (yHom y)).hom.app (op U) s0) =
                (show (O.obj.obj (op U) : Type v) from
                  (rHom r).hom.app (op U) s0) •
                  (show (H.val.obj (op U) : Type v) from
                    (g (xHom x) (yHom y)).hom.app (op U) s0)
            exact hp.2.2.2.2.2 (rHom r) (g (xHom x) (yHom y)) U s0
          _ = r • evH (g (xHom x) (yHom y)) := by
            rw [r0]
      map_add_right' := by
        intro x y₁ y₂
        calc
          evH (g (xHom x) (yHom (y₁ + y₂))) =
              evH (g (xHom x) (yHom y₁ + yHom y₂)) := by
            rw [yHom_add]
          _ = evH (g (xHom x) (yHom y₁)) +
              evH (g (xHom x) (yHom y₂)) := by
            calc
              evH (g (xHom x) (yHom y₁ + yHom y₂)) =
                  evH (g (xHom x) (yHom y₁) +
                    g (xHom x) (yHom y₂)) :=
                congrArg evH (g.map_add_right' _ _ _)
              _ = evH (g (xHom x) (yHom y₁)) +
                  evH (g (xHom x) (yHom y₂)) := by
                change
                  (show (H.val.obj (op U) : Type v) from
                    (g (xHom x) (yHom y₁) +
                      g (xHom x) (yHom y₂)).hom.app (op U) s0) =
                    (show (H.val.obj (op U) : Type v) from
                      (g (xHom x) (yHom y₁)).hom.app (op U) s0) +
                    (show (H.val.obj (op U) : Type v) from
                      (g (xHom x) (yHom y₂)).hom.app (op U) s0)
                exact hp.2.2.1 (g (xHom x) (yHom y₁))
                  (g (xHom x) (yHom y₂)) U s0
      map_smul_right' := by
        intro r x y
        calc
          evH (g (xHom x) (yHom (r • y))) =
              evH (g (xHom x) (rHom r • yHom y)) := by
            rw [yHom_smul]
          _ = evH (rHom r • g (xHom x) (yHom y)) :=
            congrArg evH (g.map_smul_right' _ _ _)
          _ = (show (O.obj.obj (op U) : Type v) from
                (rHom r).hom.app (op U) s0) •
              evH (g (xHom x) (yHom y)) := by
            change
              (show (H.val.obj (op U) : Type v) from
                (rHom r • g (xHom x) (yHom y)).hom.app (op U) s0) =
                (show (O.obj.obj (op U) : Type v) from
                  (rHom r).hom.app (op U) s0) •
                  (show (H.val.obj (op U) : Type v) from
                    (g (xHom x) (yHom y)).hom.app (op U) s0)
            exact hp.2.2.2.2.2 (rHom r) (g (xHom x) (yHom y)) U s0
          _ = r • evH (g (xHom x) (yHom y)) := by
            rw [r0]
      }, ?_⟩
    intro x y
    have he := eval_rule (xHom x) (yHom y)
    simpa only [x0 x, y0 y] using he

/-! The canonical module structure on a module stalk. -/
noncomputable abbrev moduleStalk {X : TopCat.{v}}
    {O : RingSheaf.{v, v} X} (F : Mod O) (x : X) :
    ModuleCat (TopCat.Presheaf.stalk (C := RingCat) O.obj x) :=
  ModuleCat.of (TopCat.Presheaf.stalk (C := RingCat) O.obj x)
    (↑(TopCat.Presheaf.stalk (C := AddCommGrpCat) F.val.presheaf x))

/-! The stalk map of a sheaf-valued map and its two product projections. -/
noncomputable def stalkMap {X : TopCat.{v}}
    {O : RingSheaf.{v, v} X} {F G H : Mod O}
    (f : ModuleSetMap F G H) (x : X) :
    (TopCat.Presheaf.stalkFunctor (Type v) x).obj
        (moduleSetProduct F G).presheaf →
      (TopCat.Presheaf.stalkFunctor (Type v) x).obj
        (moduleSetSheaf H).presheaf :=
  (TopCat.Presheaf.stalkFunctor (Type v) x).map f.hom

noncomputable def stalkProductFirst {X : TopCat.{v}}
    {O : RingSheaf.{v, v} X} (F G : Mod O) (x : X) :
    (TopCat.Presheaf.stalkFunctor (Type v) x).obj
        (moduleSetProduct F G).presheaf →
      (TopCat.Presheaf.stalkFunctor (Type v) x).obj
        (moduleSetSheaf F).presheaf :=
  (TopCat.Presheaf.stalkFunctor (Type v) x).map
    (limit.π (pair (moduleSetSheaf F) (moduleSetSheaf G))
      (Discrete.mk WalkingPair.left)).hom

noncomputable def stalkProductSecond {X : TopCat.{v}}
    {O : RingSheaf.{v, v} X} (F G : Mod O) (x : X) :
    (TopCat.Presheaf.stalkFunctor (Type v) x).obj
        (moduleSetProduct F G).presheaf →
      (TopCat.Presheaf.stalkFunctor (Type v) x).obj
        (moduleSetSheaf G).presheaf :=
  (TopCat.Presheaf.stalkFunctor (Type v) x).map
    (limit.π (pair (moduleSetSheaf F) (moduleSetSheaf G))
      (Discrete.mk WalkingPair.right)).hom

/-! The canonical comparison between a module stalk and the stalk of its
underlying sheaf of sets. -/
noncomputable def moduleStalkUnderlyingEquiv {X : TopCat.{v}}
    {O : RingSheaf.{v, v} X} (F : Mod O) (x : X) :
    ↑(moduleStalk F x) ≃
      (TopCat.Presheaf.stalkFunctor (Type v) x).obj
        (moduleSetSheaf F).presheaf :=
  algebraicStalkUnderlyingEquiv (forget AddCommGrpCat)
    ((SheafOfModules.toSheaf O).obj F).obj x

/-! A pairing of stalks into the stalk of the sheaf product. -/
structure StalkPairing {X : TopCat.{v}}
    {O : RingSheaf.{v, v} X} (F G : Mod O) (x : X) where
  toFun :
    ↑(moduleStalk F x) → ↑(moduleStalk G x) →
      (TopCat.Presheaf.stalkFunctor (Type v) x).obj
        (moduleSetProduct F G).presheaf
  fst_toFun : ∀ a b,
    (moduleStalkUnderlyingEquiv F x).symm
      (stalkProductFirst F G x (toFun a b)) = a
  snd_toFun : ∀ a b,
    (moduleStalkUnderlyingEquiv G x).symm
      (stalkProductSecond F G x (toFun a b)) = b

instance {X : TopCat.{v}} {O : RingSheaf.{v, v} X}
    {F G : Mod O} {x : X} : CoeFun (StalkPairing F G x)
      (fun _ => ↑(moduleStalk F x) →
        ↑(moduleStalk G x) →
          (TopCat.Presheaf.stalkFunctor (Type v) x).obj
            (moduleSetProduct F G).presheaf) :=
  ⟨StalkPairing.toFun⟩

/-! Stalkwise bilinearity, expressed through a product pairing. -/
def IsStalkwiseBilinear {X : TopCat.{v}}
    {O : RingSheaf.{v, v} X} {F G H : Mod O}
    (f : ModuleSetMap F G H) : Prop :=
  ∀ x : X, ∃ p : StalkPairing F G x,
    ∃ g : SectionBilinearMap
      (TopCat.Presheaf.stalk (C := RingCat) O.obj x : Type v)
      ↑(moduleStalk F x)
      ↑(moduleStalk G x)
      ↑(moduleStalk H x),
      ∀ a b,
        g a b = (moduleStalkUnderlyingEquiv H x).symm
          (stalkMap f x (p a b))

/-! The finite-product stalk pairing exists; this is the canonical comparison
behind the existential presentation of `IsStalkwiseBilinear`. -/
theorem exists_stalkPairing {X : TopCat.{v}}
    {O : RingSheaf.{v, v} X} (F G : Mod O) (x : X) :
    Nonempty (StalkPairing F G x) := by
  let : PreservesFiniteLimits
      (colim : ((OpenNhds x)ᵒᵖ ⥤ Type v) ⥤ Type v) := by infer_instance
  let : PreservesFiniteLimits
      ((Functor.whiskeringLeft (OpenNhds x)ᵒᵖ (Opens X)ᵒᵖ (Type v)).obj
        (OpenNhds.inclusion x).op) := by infer_instance
  let : PreservesFiniteLimits (TopCat.Presheaf.stalkFunctor (Type v) x) := by
    exact comp_preservesFiniteLimits _ _
  let e₁ := preservesLimitIso (TopCat.Sheaf.forget (Type v) X)
    (pair (moduleSetSheaf F) (moduleSetSheaf G))
  let e₁' := HasLimit.isoOfNatIso
    ((Functor.isoWhiskerRight
        (Discrete.natIsoFunctor
          (F := pair (moduleSetSheaf F) (moduleSetSheaf G)))
        (TopCat.Sheaf.forget (Type v) X)).trans
      (Discrete.compNatIsoDiscrete
        (fun j : WalkingPair =>
          (pair (moduleSetSheaf F) (moduleSetSheaf G)).obj (Discrete.mk j))
        (TopCat.Sheaf.forget (Type v) X)))
  let e₂ := preservesLimitIso (TopCat.Presheaf.stalkFunctor (Type v) x)
    (Discrete.functor (fun j : WalkingPair =>
      (TopCat.Sheaf.forget (Type v) X).obj
        ((pair (moduleSetSheaf F) (moduleSetSheaf G)).obj (Discrete.mk j))))
  let e₃ := HasLimit.isoOfNatIso (Discrete.compNatIsoDiscrete
    (fun j : WalkingPair =>
      (TopCat.Sheaf.forget (Type v) X).obj
        ((pair (moduleSetSheaf F) (moduleSetSheaf G)).obj (Discrete.mk j)))
    (TopCat.Presheaf.stalkFunctor (Type v) x))
  let e₄ := (Types.productIso (fun j : WalkingPair =>
    ((TopCat.Presheaf.stalkFunctor (Type v) x).obj
      ((TopCat.Sheaf.forget (Type v) X).obj
        ((pair (moduleSetSheaf F) (moduleSetSheaf G)).obj (Discrete.mk j)))))).toEquiv
  let e₅ : (∀ j : WalkingPair,
      (TopCat.Presheaf.stalkFunctor (Type v) x).obj
        ((TopCat.Sheaf.forget (Type v) X).obj
          ((pair (moduleSetSheaf F) (moduleSetSheaf G)).obj (Discrete.mk j)))) ≃
      (moduleSetSheaf F).presheaf.stalk x × (moduleSetSheaf G).presheaf.stalk x := {
    toFun := fun s => (s WalkingPair.left, s WalkingPair.right)
    invFun := fun p j => match j with
      | WalkingPair.left => p.1
      | WalkingPair.right => p.2
    left_inv := by
      intro s
      funext j
      cases j <;> rfl
    right_inv := by
      intro p
      rcases p with ⟨p, q⟩
      rfl }
  let e := (Functor.mapIso (TopCat.Presheaf.stalkFunctor (Type v) x)
      (e₁.trans e₁')).trans e₂
  let e'' := (e.toEquiv.trans e₃.toEquiv).trans e₄
  let e' := (e.toEquiv.trans e₃.toEquiv).trans (e₄.trans e₅)
  have hcoord (j : WalkingPair)
      (q : (TopCat.Presheaf.stalkFunctor (Type v) x).obj
        (moduleSetProduct F G).presheaf) :
      (e'' q) j =
        (TopCat.Presheaf.stalkFunctor (Type v) x).map
          (limit.π (pair (moduleSetSheaf F) (moduleSetSheaf G))
            (Discrete.mk j)).hom q := by
    change (e₄ (e₃.hom (e.hom q))) j = (TopCat.Presheaf.stalkFunctor (Type v) x).map
          (limit.π (pair (moduleSetSheaf F) (moduleSetSheaf G))
            (Discrete.mk j)).hom q
    let K : WalkingPair → Type v := fun j =>
      (TopCat.Presheaf.stalkFunctor (Type v) x).obj
        ((TopCat.Sheaf.forget (Type v) X).obj
          ((pair (moduleSetSheaf F) (moduleSetSheaf G)).obj
            (Discrete.mk j)))
    change
      ((Types.productIso K).hom ≫ (↾fun s => s j))
        (e₃.hom (e.hom q)) = (TopCat.Presheaf.stalkFunctor (Type v) x).map
          (limit.π (pair (moduleSetSheaf F) (moduleSetSheaf G))
            (Discrete.mk j)).hom q
    rw [Types.productIso_hom_comp_eval]
    change
      ((e₃.hom ≫ limit.π
        (Discrete.functor (fun j : WalkingPair =>
          (TopCat.Presheaf.stalkFunctor (Type v) x).obj
            ((TopCat.Sheaf.forget (Type v) X).obj
              ((pair (moduleSetSheaf F) (moduleSetSheaf G)).obj
                (Discrete.mk j)))))
        (Discrete.mk j)) (e.hom q)) =
          (TopCat.Presheaf.stalkFunctor (Type v) x).map
          (limit.π (pair (moduleSetSheaf F) (moduleSetSheaf G))
            (Discrete.mk j)).hom q
    have h₃ := HasLimit.isoOfNatIso_hom_π
      (Discrete.compNatIsoDiscrete
        (fun j : WalkingPair =>
          (TopCat.Sheaf.forget (Type v) X).obj
            ((pair (moduleSetSheaf F) (moduleSetSheaf G)).obj (Discrete.mk j)))
        (TopCat.Presheaf.stalkFunctor (Type v) x))
        (Discrete.mk j)
    have h₃' :
        e₃.hom ≫ limit.π
            (Discrete.functor (fun j : WalkingPair =>
              (TopCat.Presheaf.stalkFunctor (Type v) x).obj
                ((TopCat.Sheaf.forget (Type v) X).obj
                  ((pair (moduleSetSheaf F) (moduleSetSheaf G)).obj
                    (Discrete.mk j)))))
            (Discrete.mk j) =
          limit.π
              (Discrete.functor (fun j : WalkingPair =>
                (TopCat.Sheaf.forget (Type v) X).obj
                  ((pair (moduleSetSheaf F) (moduleSetSheaf G)).obj
                    (Discrete.mk j))) ⋙
                TopCat.Presheaf.stalkFunctor (Type v) x)
              (Discrete.mk j) ≫
            (Discrete.compNatIsoDiscrete
                (fun j : WalkingPair =>
                  (TopCat.Sheaf.forget (Type v) X).obj
                    ((pair (moduleSetSheaf F) (moduleSetSheaf G)).obj
                      (Discrete.mk j)))
                (TopCat.Presheaf.stalkFunctor (Type v) x)).hom.app
              (Discrete.mk j) := by
      simpa [e₃, Function.comp_def] using h₃
    rw [h₃']
    have h_arrow :
        e.hom ≫
            (limit.π
                ((Discrete.functor (fun j : WalkingPair =>
                  (TopCat.Sheaf.forget (Type v) X).obj
                    ((pair (moduleSetSheaf F) (moduleSetSheaf G)).obj
                      (Discrete.mk j))) ⋙
                  TopCat.Presheaf.stalkFunctor (Type v) x))
                (Discrete.mk j) ≫
              (Discrete.compNatIsoDiscrete
                (fun j : WalkingPair =>
                  (TopCat.Sheaf.forget (Type v) X).obj
                    ((pair (moduleSetSheaf F) (moduleSetSheaf G)).obj
                      (Discrete.mk j)))
                (TopCat.Presheaf.stalkFunctor (Type v) x)).hom.app
                (Discrete.mk j)) =
          (TopCat.Presheaf.stalkFunctor (Type v) x).map
            (limit.π (pair (moduleSetSheaf F) (moduleSetSheaf G))
              (Discrete.mk j)).hom := by
      dsimp [e]
      change
        (((TopCat.Presheaf.stalkFunctor (Type v) x).mapIso
            (e₁.trans e₁')).hom ≫ e₂.hom) ≫
            limit.π
                ((Discrete.functor (fun j : WalkingPair =>
                  (TopCat.Sheaf.forget (Type v) X).obj
                    ((pair (moduleSetSheaf F) (moduleSetSheaf G)).obj
                      (Discrete.mk j))) ⋙
                  TopCat.Presheaf.stalkFunctor (Type v) x))
                (Discrete.mk j) ≫
              (Discrete.compNatIsoDiscrete
                (fun j : WalkingPair =>
                  (TopCat.Sheaf.forget (Type v) X).obj
                    ((pair (moduleSetSheaf F) (moduleSetSheaf G)).obj
                      (Discrete.mk j)))
                (TopCat.Presheaf.stalkFunctor (Type v) x)).hom.app
                (Discrete.mk j) =
          (TopCat.Presheaf.stalkFunctor (Type v) x).map
            (limit.π (pair (moduleSetSheaf F) (moduleSetSheaf G))
              (Discrete.mk j)).hom
      have h₂ :
          e₂.hom ≫
              limit.π
                ((Discrete.functor (fun j : WalkingPair =>
                  (TopCat.Sheaf.forget (Type v) X).obj
                    ((pair (moduleSetSheaf F) (moduleSetSheaf G)).obj
                      (Discrete.mk j))) ⋙
                  TopCat.Presheaf.stalkFunctor (Type v) x))
                (Discrete.mk j) =
            (TopCat.Presheaf.stalkFunctor (Type v) x).map
              (limit.π
                (Discrete.functor (fun j : WalkingPair =>
                  (TopCat.Sheaf.forget (Type v) X).obj
                    ((pair (moduleSetSheaf F) (moduleSetSheaf G)).obj
                      (Discrete.mk j))))
                (Discrete.mk j)) := by
        simpa [e₂] using
          (preservesLimitIso_hom_π
            (TopCat.Presheaf.stalkFunctor (Type v) x)
            (Discrete.functor (fun j : WalkingPair =>
              (TopCat.Sheaf.forget (Type v) X).obj
                ((pair (moduleSetSheaf F) (moduleSetSheaf G)).obj
                  (Discrete.mk j))))
            (Discrete.mk j))
      have h₂' :
          (((TopCat.Presheaf.stalkFunctor (Type v) x).mapIso
              (e₁.trans e₁')).hom ≫ e₂.hom) ≫
              limit.π
                ((Discrete.functor (fun j : WalkingPair =>
                  (TopCat.Sheaf.forget (Type v) X).obj
                    ((pair (moduleSetSheaf F) (moduleSetSheaf G)).obj
                      (Discrete.mk j))) ⋙
                  TopCat.Presheaf.stalkFunctor (Type v) x))
                (Discrete.mk j) ≫
            (Discrete.compNatIsoDiscrete
                (fun j : WalkingPair =>
                  (TopCat.Sheaf.forget (Type v) X).obj
                    ((pair (moduleSetSheaf F) (moduleSetSheaf G)).obj
                      (Discrete.mk j)))
                (TopCat.Presheaf.stalkFunctor (Type v) x)).hom.app
                (Discrete.mk j) =
          ((TopCat.Presheaf.stalkFunctor (Type v) x).mapIso
              (e₁.trans e₁')).hom ≫
            (TopCat.Presheaf.stalkFunctor (Type v) x).map
              (limit.π
                (Discrete.functor (fun j : WalkingPair =>
                  (TopCat.Sheaf.forget (Type v) X).obj
                    ((pair (moduleSetSheaf F) (moduleSetSheaf G)).obj
                      (Discrete.mk j))))
                (Discrete.mk j)) ≫
            (Discrete.compNatIsoDiscrete
                (fun j : WalkingPair =>
                  (TopCat.Sheaf.forget (Type v) X).obj
                    ((pair (moduleSetSheaf F) (moduleSetSheaf G)).obj
                      (Discrete.mk j)))
                (TopCat.Presheaf.stalkFunctor (Type v) x)).hom.app
                (Discrete.mk j) := by
        simpa only [Category.assoc] using congrArg
          (fun k =>
            ((TopCat.Presheaf.stalkFunctor (Type v) x).mapIso
                (e₁.trans e₁')).hom ≫ k ≫
              (Discrete.compNatIsoDiscrete
                (fun j : WalkingPair =>
                  (TopCat.Sheaf.forget (Type v) X).obj
                    ((pair (moduleSetSheaf F) (moduleSetSheaf G)).obj
                      (Discrete.mk j)))
                (TopCat.Presheaf.stalkFunctor (Type v) x)).hom.app
                (Discrete.mk j)) h₂
      rw [h₂']
      simp only [Functor.mapIso_hom, Iso.trans_hom, Functor.map_comp]
      have h₁ := HasLimit.isoOfNatIso_hom_π
        ((Functor.isoWhiskerRight
            (Discrete.natIsoFunctor
              (F := pair (moduleSetSheaf F) (moduleSetSheaf G)))
            (TopCat.Sheaf.forget (Type v) X)).trans
          (Discrete.compNatIsoDiscrete
            (fun j : WalkingPair =>
              (pair (moduleSetSheaf F) (moduleSetSheaf G)).obj (Discrete.mk j))
            (TopCat.Sheaf.forget (Type v) X)))
        (Discrete.mk j)
      have h₁' :
          e₁'.hom ≫
              limit.π
                (Discrete.functor (fun j : WalkingPair =>
                  (TopCat.Sheaf.forget (Type v) X).obj
                    ((pair (moduleSetSheaf F) (moduleSetSheaf G)).obj
                      (Discrete.mk j))))
                (Discrete.mk j) =
            limit.π
                (pair (moduleSetSheaf F) (moduleSetSheaf G) ⋙
                  TopCat.Sheaf.forget (Type v) X)
                (Discrete.mk j) ≫
              (Discrete.compNatIsoDiscrete
                (fun j : WalkingPair =>
                  (pair (moduleSetSheaf F) (moduleSetSheaf G)).obj
                    (Discrete.mk j))
                (TopCat.Sheaf.forget (Type v) X)).hom.app
                (Discrete.mk j) := by
        simp [e₁', Function.comp_def]
      have h₀ := preservesLimitIso_hom_π
        (TopCat.Sheaf.forget (Type v) X)
        (pair (moduleSetSheaf F) (moduleSetSheaf G))
        (Discrete.mk j)
      have h₀' :
          e₁.hom ≫
              limit.π
                (pair (moduleSetSheaf F) (moduleSetSheaf G) ⋙
                  TopCat.Sheaf.forget (Type v) X)
                (Discrete.mk j) =
            (TopCat.Sheaf.forget (Type v) X).map
              (limit.π (pair (moduleSetSheaf F) (moduleSetSheaf G))
                (Discrete.mk j)) := by
        simp [e₁]
      have h₁map :
          (TopCat.Presheaf.stalkFunctor (Type v) x).map e₁'.hom ≫
              (TopCat.Presheaf.stalkFunctor (Type v) x).map
                (limit.π
                  (Discrete.functor (fun j : WalkingPair =>
                    (TopCat.Sheaf.forget (Type v) X).obj
                      ((pair (moduleSetSheaf F) (moduleSetSheaf G)).obj
                        (Discrete.mk j))))
                  (Discrete.mk j)) =
            (TopCat.Presheaf.stalkFunctor (Type v) x).map
              (limit.π
                (pair (moduleSetSheaf F) (moduleSetSheaf G) ⋙
                  TopCat.Sheaf.forget (Type v) X)
                (Discrete.mk j) ≫
                (Discrete.compNatIsoDiscrete
                  (fun j : WalkingPair =>
                    (pair (moduleSetSheaf F) (moduleSetSheaf G)).obj
                      (Discrete.mk j))
                  (TopCat.Sheaf.forget (Type v) X)).hom.app
                  (Discrete.mk j)) := by
        rw [← Functor.map_comp, h₁']
      have h₁map' := congrArg
        (fun k =>
          ((TopCat.Presheaf.stalkFunctor (Type v) x).map e₁.hom ≫ k) ≫
            (Discrete.compNatIsoDiscrete
              (fun j : WalkingPair =>
                (TopCat.Sheaf.forget (Type v) X).obj
                  ((pair (moduleSetSheaf F) (moduleSetSheaf G)).obj
                    (Discrete.mk j)))
              (TopCat.Presheaf.stalkFunctor (Type v) x)).hom.app
              (Discrete.mk j)) h₁map
      have h₁map'' :
          (((TopCat.Presheaf.stalkFunctor (Type v) x).map e₁.hom ≫
              (TopCat.Presheaf.stalkFunctor (Type v) x).map e₁'.hom) ≫
              (TopCat.Presheaf.stalkFunctor (Type v) x).map
                (limit.π
                  (Discrete.functor (fun j : WalkingPair =>
                    (TopCat.Sheaf.forget (Type v) X).obj
                      ((pair (moduleSetSheaf F) (moduleSetSheaf G)).obj
                        (Discrete.mk j))))
                  (Discrete.mk j))) ≫
            (Discrete.compNatIsoDiscrete
              (fun j : WalkingPair =>
                (TopCat.Sheaf.forget (Type v) X).obj
                  ((pair (moduleSetSheaf F) (moduleSetSheaf G)).obj
                    (Discrete.mk j)))
              (TopCat.Presheaf.stalkFunctor (Type v) x)).hom.app
              (Discrete.mk j) =
          ((TopCat.Presheaf.stalkFunctor (Type v) x).map e₁.hom ≫
              (TopCat.Presheaf.stalkFunctor (Type v) x).map
                (limit.π
                  (pair (moduleSetSheaf F) (moduleSetSheaf G) ⋙
                    TopCat.Sheaf.forget (Type v) X)
                  (Discrete.mk j) ≫
                  (Discrete.compNatIsoDiscrete
                    (fun j : WalkingPair =>
                      (pair (moduleSetSheaf F) (moduleSetSheaf G)).obj
                        (Discrete.mk j))
                    (TopCat.Sheaf.forget (Type v) X)).hom.app
                    (Discrete.mk j))) ≫
            (Discrete.compNatIsoDiscrete
              (fun j : WalkingPair =>
                (TopCat.Sheaf.forget (Type v) X).obj
                  ((pair (moduleSetSheaf F) (moduleSetSheaf G)).obj
                    (Discrete.mk j)))
              (TopCat.Presheaf.stalkFunctor (Type v) x)).hom.app
              (Discrete.mk j) := by
        simpa only [Category.assoc] using h₁map'
      refine h₁map''.trans ?_
      have h₀map := congrArg
        (fun k =>
          (TopCat.Presheaf.stalkFunctor (Type v) x).map k ≫
            (Discrete.compNatIsoDiscrete
              (fun j : WalkingPair =>
                (TopCat.Sheaf.forget (Type v) X).obj
                  ((pair (moduleSetSheaf F) (moduleSetSheaf G)).obj
                    (Discrete.mk j)))
              (TopCat.Presheaf.stalkFunctor (Type v) x)).hom.app
              (Discrete.mk j)) h₀'
      have hforget :
          (TopCat.Sheaf.forget (Type v) X).map
              (limit.π (pair (moduleSetSheaf F) (moduleSetSheaf G))
                (Discrete.mk j)) =
            (limit.π (pair (moduleSetSheaf F) (moduleSetSheaf G))
              (Discrete.mk j)).hom := by
        rfl
      convert h₀map using 1
      all_goals
        simp [Functor.map_comp, Discrete.compNatIsoDiscrete,
        Discrete.natIso, NatIso.ofComponents, hforget]; try rfl
    have hq := congrArg (fun k => k q) h_arrow
    change
      (limit.π
          ((Discrete.functor (fun j : WalkingPair =>
            (TopCat.Sheaf.forget (Type v) X).obj
              ((pair (moduleSetSheaf F) (moduleSetSheaf G)).obj
                (Discrete.mk j))) ⋙
            TopCat.Presheaf.stalkFunctor (Type v) x))
          (Discrete.mk j) ≫
        (Discrete.compNatIsoDiscrete
          (fun j : WalkingPair =>
            (TopCat.Sheaf.forget (Type v) X).obj
              ((pair (moduleSetSheaf F) (moduleSetSheaf G)).obj
                (Discrete.mk j)))
          (TopCat.Presheaf.stalkFunctor (Type v) x)).hom.app
          (Discrete.mk j)) (e.hom q) =
        (TopCat.Presheaf.stalkFunctor (Type v) x).map
          (limit.π (pair (moduleSetSheaf F) (moduleSetSheaf G))
            (Discrete.mk j)).hom q at hq
    exact hq

  let p : StalkPairing F G x := {
    toFun := fun a b => e'.symm
      (moduleStalkUnderlyingEquiv F x a, moduleStalkUnderlyingEquiv G x b)
    fst_toFun := by
      intro a b
      apply (moduleStalkUnderlyingEquiv F x).injective
      have hp := congrArg Prod.fst
        (e'.apply_symm_apply
          (moduleStalkUnderlyingEquiv F x a, moduleStalkUnderlyingEquiv G x b))
      have hc := hcoord WalkingPair.left
        (e'.symm
          (moduleStalkUnderlyingEquiv F x a, moduleStalkUnderlyingEquiv G x b))
      have heq :
          e''
              (e'.symm
                (moduleStalkUnderlyingEquiv F x a,
                  moduleStalkUnderlyingEquiv G x b)) WalkingPair.left =
            (e'
              (e'.symm
                (moduleStalkUnderlyingEquiv F x a,
                  moduleStalkUnderlyingEquiv G x b))).1 := by
        rfl
      have hp' :
          stalkProductFirst F G x
              (e'.symm
                (moduleStalkUnderlyingEquiv F x a,
                  moduleStalkUnderlyingEquiv G x b)) =
            moduleStalkUnderlyingEquiv F x a := by
        change
          (TopCat.Presheaf.stalkFunctor (Type v) x).map
              (limit.π (pair (moduleSetSheaf F) (moduleSetSheaf G))
                (Discrete.mk WalkingPair.left)).hom
              (e'.symm
                (moduleStalkUnderlyingEquiv F x a,
                  moduleStalkUnderlyingEquiv G x b)) =
            moduleStalkUnderlyingEquiv F x a
        exact hc.symm.trans (heq.trans hp)
      rw [hp']
      simpa only using
        (moduleStalkUnderlyingEquiv F x).apply_symm_apply
          ((moduleStalkUnderlyingEquiv F x) a)
    snd_toFun := by
      intro a b
      apply (moduleStalkUnderlyingEquiv G x).injective
      have hp := congrArg Prod.snd
        (e'.apply_symm_apply
          (moduleStalkUnderlyingEquiv F x a, moduleStalkUnderlyingEquiv G x b))
      have hc := hcoord WalkingPair.right
        (e'.symm
          (moduleStalkUnderlyingEquiv F x a, moduleStalkUnderlyingEquiv G x b))
      have heq :
          e''
              (e'.symm
                (moduleStalkUnderlyingEquiv F x a,
                  moduleStalkUnderlyingEquiv G x b)) WalkingPair.right =
            (e'
              (e'.symm
                (moduleStalkUnderlyingEquiv F x a,
                  moduleStalkUnderlyingEquiv G x b))).2 := by
        rfl
      have hp' :
          stalkProductSecond F G x
              (e'.symm
                (moduleStalkUnderlyingEquiv F x a,
                  moduleStalkUnderlyingEquiv G x b)) =
            moduleStalkUnderlyingEquiv G x b := by
        change
          (TopCat.Presheaf.stalkFunctor (Type v) x).map
              (limit.π (pair (moduleSetSheaf F) (moduleSetSheaf G))
                (Discrete.mk WalkingPair.right)).hom
              (e'.symm
                (moduleStalkUnderlyingEquiv F x a,
                  moduleStalkUnderlyingEquiv G x b)) =
            moduleStalkUnderlyingEquiv G x b
        exact hc.symm.trans (heq.trans hp)
      rw [hp']
      simpa only using
        (moduleStalkUnderlyingEquiv G x).apply_symm_apply
          ((moduleStalkUnderlyingEquiv G x) b) }
  exact ⟨p⟩

/-! Equality of sections can be checked on all stalks. -/
theorem sections_eq_of_equal_stalks {X : TopCat.{v}}
    (F : TopCat.Sheaf (Type v) X) (U : Opens X)
    (s t : F.presheaf.obj (op U))
    (h : ∀ x : U,
      TopCat.Presheaf.germ F.presheaf U x.1 x.2 s =
        TopCat.Presheaf.germ F.presheaf U x.1 x.2 t) :
    s = t := by
  apply TopCat.Presheaf.section_ext F U s t
  intro x hx
  exact h ⟨x, hx⟩

private theorem test_product_sections_first {X : TopCat.{v}}
    {O : RingSheaf.{v, v} X} (F G : Mod O) (U : Opens X)
    (s : (F.val.obj (op U) : Type v))
    (t : (G.val.obj (op U) : Type v)) :
    (limit.π (pair (moduleSetSheaf F) (moduleSetSheaf G)) (Discrete.mk (WalkingPair.left))).hom.app
        (op U)
        ((sheafProductSectionsEquiv (moduleSetSheaf F) (moduleSetSheaf G) U).symm (s, t)) = s := by
  let e₁ := (preservesLimitIso (TopCat.Sheaf.forget (Type v) X)
    (pair (moduleSetSheaf F) (moduleSetSheaf G))).app (op U)
  let e₁' := HasLimit.isoOfNatIso
    ((Functor.isoWhiskerRight
        (Discrete.natIsoFunctor
          (F := pair (moduleSetSheaf F) (moduleSetSheaf G)))
        (TopCat.Sheaf.forget (Type v) X)).trans
      (Discrete.compNatIsoDiscrete
        (fun j : WalkingPair =>
          (pair (moduleSetSheaf F) (moduleSetSheaf G)).obj (Discrete.mk j))
        (TopCat.Sheaf.forget (Type v) X)))
  let e₂ := preservesLimitIso
    ((evaluation ((Opens X)ᵒᵖ) (Type v)).obj (op U))
    (Discrete.functor ((TopCat.Sheaf.forget (Type v) X).obj ∘ fun j : WalkingPair =>
      (pair (moduleSetSheaf F) (moduleSetSheaf G)).obj (Discrete.mk j)))
  let e₃ := HasLimit.isoOfNatIso (Discrete.compNatIsoDiscrete
    (fun j : WalkingPair =>
      (TopCat.Sheaf.forget (Type v) X).obj
        ((pair (moduleSetSheaf F) (moduleSetSheaf G)).obj (Discrete.mk j)))
    ((evaluation ((Opens X)ᵒᵖ) (Type v)).obj (op U)))
  let e₄ := (Types.productIso (fun j : WalkingPair =>
    ((evaluation ((Opens X)ᵒᵖ) (Type v)).obj (op U)).obj
      ((TopCat.Sheaf.forget (Type v) X).obj
        ((pair (moduleSetSheaf F) (moduleSetSheaf G)).obj (Discrete.mk j))))).toEquiv
  let e₅ : (∀ j : WalkingPair,
      ((evaluation ((Opens X)ᵒᵖ) (Type v)).obj (op U)).obj
        ((TopCat.Sheaf.forget (Type v) X).obj
          ((pair (moduleSetSheaf F) (moduleSetSheaf G)).obj (Discrete.mk j)))) ≃
      (F.val.obj (op U) : Type v) × (G.val.obj (op U) : Type v) := {
    toFun := fun s => (s WalkingPair.left, s WalkingPair.right)
    invFun := fun p j => match j with
      | WalkingPair.left => p.1
      | WalkingPair.right => p.2
    left_inv := by
      intro s
      funext j
      cases j <;> rfl
    right_inv := by
      intro p
      rcases p with ⟨p, q⟩
      rfl }
  let e := e₁.toEquiv.trans ((e₁'.app (op U)).toEquiv.trans
    (e₂.toEquiv.trans (e₃.toEquiv.trans (e₄.trans e₅))))
  have hcoord (q : (((TopCat.Sheaf.forget (Type v) X).obj
      (limit (pair (moduleSetSheaf F) (moduleSetSheaf G)))).obj (op U) : Type v)) :
      (e q).1 =
        (limit.π (pair (moduleSetSheaf F) (moduleSetSheaf G))
          (Discrete.mk WalkingPair.left)).hom.app (op U) q := by
    change ((Types.productIso _).hom ≫ (↾fun s => s WalkingPair.left)) (_ ) = _
    rw [Types.productIso_hom_comp_eval]
    change
      ((e₃.hom ≫ limit.π
        (Discrete.functor (fun j : WalkingPair =>
          ((evaluation ((Opens X)ᵒᵖ) (Type v)).obj (op U)).obj
            ((TopCat.Sheaf.forget (Type v) X).obj
              ((pair (moduleSetSheaf F) (moduleSetSheaf G)).obj
                (Discrete.mk j)))))
        (Discrete.mk WalkingPair.left))
        (e₂.hom ((e₁'.app (op U)).hom (e₁.hom q)))) = _
    have h₃ := HasLimit.isoOfNatIso_hom_π
      (Discrete.compNatIsoDiscrete
        (fun j : WalkingPair =>
          (TopCat.Sheaf.forget (Type v) X).obj
            ((pair (moduleSetSheaf F) (moduleSetSheaf G)).obj (Discrete.mk j)))
        ((evaluation ((Opens X)ᵒᵖ) (Type v)).obj (op U)))
      (Discrete.mk WalkingPair.left)
    have h₃' :
        e₃.hom ≫ limit.π
            (Discrete.functor (fun j : WalkingPair =>
              ((evaluation ((Opens X)ᵒᵖ) (Type v)).obj (op U)).obj
                ((TopCat.Sheaf.forget (Type v) X).obj
                  ((pair (moduleSetSheaf F) (moduleSetSheaf G)).obj
                    (Discrete.mk j)))))
            (Discrete.mk WalkingPair.left) =
          limit.π
              (Discrete.functor (fun j : WalkingPair =>
                (TopCat.Sheaf.forget (Type v) X).obj
                  ((pair (moduleSetSheaf F) (moduleSetSheaf G)).obj
                    (Discrete.mk j))) ⋙
                ((evaluation ((Opens X)ᵒᵖ) (Type v)).obj (op U)))
              (Discrete.mk WalkingPair.left) ≫
            (Discrete.compNatIsoDiscrete
                (fun j : WalkingPair =>
                  (TopCat.Sheaf.forget (Type v) X).obj
                    ((pair (moduleSetSheaf F) (moduleSetSheaf G)).obj
                      (Discrete.mk j)))
                ((evaluation ((Opens X)ᵒᵖ) (Type v)).obj (op U))).hom.app
              (Discrete.mk WalkingPair.left) := by
      simpa [e₃, Function.comp_def] using h₃
    rw [h₃']
    have h₂ := preservesLimitIso_hom_π
      ((evaluation ((Opens X)ᵒᵖ) (Type v)).obj (op U))
      (Discrete.functor (fun j : WalkingPair =>
        (TopCat.Sheaf.forget (Type v) X).obj
          ((pair (moduleSetSheaf F) (moduleSetSheaf G)).obj (Discrete.mk j))))
      (Discrete.mk WalkingPair.left)
    have h₂' :
        e₂.hom ≫
            limit.π
              (Discrete.functor (fun j : WalkingPair =>
                (TopCat.Sheaf.forget (Type v) X).obj
                  ((pair (moduleSetSheaf F) (moduleSetSheaf G)).obj
                    (Discrete.mk j))) ⋙
                ((evaluation ((Opens X)ᵒᵖ) (Type v)).obj (op U)))
              (Discrete.mk WalkingPair.left) =
          ((evaluation ((Opens X)ᵒᵖ) (Type v)).obj (op U)).map
            (limit.π
              (Discrete.functor (fun j : WalkingPair =>
                (TopCat.Sheaf.forget (Type v) X).obj
                  ((pair (moduleSetSheaf F) (moduleSetSheaf G)).obj
                    (Discrete.mk j))))
              (Discrete.mk WalkingPair.left)) := by
      simpa [e₂, Function.comp_def] using h₂
    have h₁ := HasLimit.isoOfNatIso_hom_π
      ((Functor.isoWhiskerRight
          (Discrete.natIsoFunctor
            (F := pair (moduleSetSheaf F) (moduleSetSheaf G)))
          (TopCat.Sheaf.forget (Type v) X)).trans
        (Discrete.compNatIsoDiscrete
          (fun j : WalkingPair =>
            (pair (moduleSetSheaf F) (moduleSetSheaf G)).obj (Discrete.mk j))
      (TopCat.Sheaf.forget (Type v) X)))
      (Discrete.mk WalkingPair.left)
    let c₁ :=
      (Functor.isoWhiskerRight
          (Discrete.natIsoFunctor
            (F := pair (moduleSetSheaf F) (moduleSetSheaf G)))
          (TopCat.Sheaf.forget (Type v) X)).trans
        (Discrete.compNatIsoDiscrete
          (fun j : WalkingPair =>
            (pair (moduleSetSheaf F) (moduleSetSheaf G)).obj (Discrete.mk j))
          (TopCat.Sheaf.forget (Type v) X))
    have h₁' :
        (e₁'.app (op U)).hom ≫
            (limit.π
              (Discrete.functor (fun j : WalkingPair =>
                (TopCat.Sheaf.forget (Type v) X).obj
                  ((pair (moduleSetSheaf F) (moduleSetSheaf G)).obj
                    (Discrete.mk j))))
              (Discrete.mk WalkingPair.left)).app (op U) =
          (limit.π
              (pair (moduleSetSheaf F) (moduleSetSheaf G) ⋙
                TopCat.Sheaf.forget (Type v) X)
              (Discrete.mk WalkingPair.left)).app (op U) ≫
            (c₁.hom.app (Discrete.mk WalkingPair.left)).app (op U) := by
      have h₁eval := congrArg (fun k => k.app (op U)) h₁
      convert h₁eval using 1 <;>
        simp [e₁', Function.comp_def, Discrete.compNatIsoDiscrete,
          Discrete.natIso, NatIso.ofComponents, NatTrans.comp_app,
          Functor.comp_obj] <;>
        try rfl
    have h₀ := preservesLimitIso_hom_π
      (TopCat.Sheaf.forget (Type v) X)
      (pair (moduleSetSheaf F) (moduleSetSheaf G))
      (Discrete.mk WalkingPair.left)
    have h₀' :
        e₁.hom ≫
            (limit.π
              (pair (moduleSetSheaf F) (moduleSetSheaf G) ⋙
                TopCat.Sheaf.forget (Type v) X)
              (Discrete.mk WalkingPair.left)).app (op U) =
          ((TopCat.Sheaf.forget (Type v) X).map
            (limit.π (pair (moduleSetSheaf F) (moduleSetSheaf G))
              (Discrete.mk WalkingPair.left))).app (op U) := by
      have h₀eval := congrArg (fun k => k.app (op U)) h₀
      rw [NatTrans.comp_app] at h₀eval
      simpa [e₁] using h₀eval
    have h_arrow :
        e₁.hom ≫ (e₁'.app (op U)).hom ≫ e₂.hom ≫ e₃.hom ≫
            limit.π
                (Discrete.functor (fun j : WalkingPair =>
                  ((evaluation ((Opens X)ᵒᵖ) (Type v)).obj (op U)).obj
                    ((TopCat.Sheaf.forget (Type v) X).obj
                      ((pair (moduleSetSheaf F) (moduleSetSheaf G)).obj
                        (Discrete.mk j)))))
                (Discrete.mk WalkingPair.left) =
          (limit.π (pair (moduleSetSheaf F) (moduleSetSheaf G))
            (Discrete.mk WalkingPair.left)).hom.app (op U) := by
      change
        (((e₁.hom ≫ (e₁'.app (op U)).hom) ≫ e₂.hom) ≫
          (e₃.hom ≫
            limit.π
              (Discrete.functor (fun j : WalkingPair =>
                ((evaluation ((Opens X)ᵒᵖ) (Type v)).obj (op U)).obj
                  ((TopCat.Sheaf.forget (Type v) X).obj
                    ((pair (moduleSetSheaf F) (moduleSetSheaf G)).obj
                      (Discrete.mk j)))))
              (Discrete.mk WalkingPair.left))) =
          (limit.π (pair (moduleSetSheaf F) (moduleSetSheaf G))
            (Discrete.mk WalkingPair.left)).hom.app (op U)
      simp only [Category.assoc]
      rw [h₃']
      rw [← Category.assoc e₂.hom]
      rw [h₂']
      have h_eval :
          ((evaluation ((Opens X)ᵒᵖ) (Type v)).obj (op U)).map
              (limit.π
                (Discrete.functor (fun j : WalkingPair =>
                  (TopCat.Sheaf.forget (Type v) X).obj
                    ((pair (moduleSetSheaf F) (moduleSetSheaf G)).obj
                      (Discrete.mk j))))
                (Discrete.mk WalkingPair.left)) =
            (limit.π
                (Discrete.functor (fun j : WalkingPair =>
                  (TopCat.Sheaf.forget (Type v) X).obj
                    ((pair (moduleSetSheaf F) (moduleSetSheaf G)).obj
                      (Discrete.mk j))))
                (Discrete.mk WalkingPair.left)).app (op U) := by
        rfl
      rw [h_eval]
      rw [← Category.assoc (e₁'.app (op U)).hom]
      rw [h₁']
      simp only [Category.assoc]
      rw [← Category.assoc e₁.hom]
      rw [h₀']
      have hforget :
          (TopCat.Sheaf.forget (Type v) X).map
              (limit.π (pair (moduleSetSheaf F) (moduleSetSheaf G))
                (Discrete.mk WalkingPair.left)) =
            (limit.π (pair (moduleSetSheaf F) (moduleSetSheaf G))
              (Discrete.mk WalkingPair.left)).hom := by
        rfl
      rw [hforget]
      simp only [c₁, Discrete.compNatIsoDiscrete, Discrete.natIso,
        NatIso.ofComponents]
      rfl
    have h_arrow' := h_arrow
    rw [h₃'] at h_arrow'
    have hq := congrArg (fun k => k q) h_arrow'
    change
      (limit.π
          (Discrete.functor (fun j : WalkingPair =>
            (TopCat.Sheaf.forget (Type v) X).obj
              ((pair (moduleSetSheaf F) (moduleSetSheaf G)).obj
                (Discrete.mk j))) ⋙
            ((evaluation ((Opens X)ᵒᵖ) (Type v)).obj (op U)))
          (Discrete.mk WalkingPair.left) ≫
        (Discrete.compNatIsoDiscrete
          (fun j : WalkingPair =>
            (TopCat.Sheaf.forget (Type v) X).obj
              ((pair (moduleSetSheaf F) (moduleSetSheaf G)).obj
                (Discrete.mk j)))
          ((evaluation ((Opens X)ᵒᵖ) (Type v)).obj (op U))).hom.app
          (Discrete.mk WalkingPair.left))
        (e₂.hom ((e₁'.app (op U)).hom (e₁.hom q))) =
      (limit.π (pair (moduleSetSheaf F) (moduleSetSheaf G))
        (Discrete.mk WalkingPair.left)).hom.app (op U) q at hq
    exact hq
  have hp := congrArg Prod.fst (e.apply_symm_apply (s, t))
  exact hcoord _ |>.symm.trans hp

private theorem test_product_sections_second {X : TopCat.{v}}
    {O : RingSheaf.{v, v} X} (F G : Mod O) (U : Opens X)
    (s : (F.val.obj (op U) : Type v))
    (t : (G.val.obj (op U) : Type v)) :
    (limit.π (pair (moduleSetSheaf F) (moduleSetSheaf G))
      (Discrete.mk WalkingPair.right)).hom.app (op U)
      ((sheafProductSectionsEquiv (moduleSetSheaf F) (moduleSetSheaf G) U).symm
        (s, t)) = t := by
  let e₁ := (preservesLimitIso (TopCat.Sheaf.forget (Type v) X)
    (pair (moduleSetSheaf F) (moduleSetSheaf G))).app (op U)
  let e₁' := HasLimit.isoOfNatIso
    ((Functor.isoWhiskerRight
        (Discrete.natIsoFunctor
          (F := pair (moduleSetSheaf F) (moduleSetSheaf G)))
        (TopCat.Sheaf.forget (Type v) X)).trans
      (Discrete.compNatIsoDiscrete
        (fun j : WalkingPair =>
          (pair (moduleSetSheaf F) (moduleSetSheaf G)).obj (Discrete.mk j))
        (TopCat.Sheaf.forget (Type v) X)))
  let e₂ := preservesLimitIso
    ((evaluation ((Opens X)ᵒᵖ) (Type v)).obj (op U))
    (Discrete.functor ((TopCat.Sheaf.forget (Type v) X).obj ∘ fun j : WalkingPair =>
      (pair (moduleSetSheaf F) (moduleSetSheaf G)).obj (Discrete.mk j)))
  let e₃ := HasLimit.isoOfNatIso (Discrete.compNatIsoDiscrete
    (fun j : WalkingPair =>
      (TopCat.Sheaf.forget (Type v) X).obj
        ((pair (moduleSetSheaf F) (moduleSetSheaf G)).obj (Discrete.mk j)))
    ((evaluation ((Opens X)ᵒᵖ) (Type v)).obj (op U)))
  let e₄ := (Types.productIso (fun j : WalkingPair =>
    ((evaluation ((Opens X)ᵒᵖ) (Type v)).obj (op U)).obj
      ((TopCat.Sheaf.forget (Type v) X).obj
        ((pair (moduleSetSheaf F) (moduleSetSheaf G)).obj (Discrete.mk j))))).toEquiv
  let e₅ : (∀ j : WalkingPair,
      ((evaluation ((Opens X)ᵒᵖ) (Type v)).obj (op U)).obj
        ((TopCat.Sheaf.forget (Type v) X).obj
          ((pair (moduleSetSheaf F) (moduleSetSheaf G)).obj (Discrete.mk j)))) ≃
      (F.val.obj (op U) : Type v) × (G.val.obj (op U) : Type v) := {
    toFun := fun s => (s WalkingPair.left, s WalkingPair.right)
    invFun := fun p j => match j with
      | WalkingPair.left => p.1
      | WalkingPair.right => p.2
    left_inv := by
      intro s
      funext j
      cases j <;> rfl
    right_inv := by
      intro p
      rcases p with ⟨p, q⟩
      rfl }
  let e := e₁.toEquiv.trans ((e₁'.app (op U)).toEquiv.trans
    (e₂.toEquiv.trans (e₃.toEquiv.trans (e₄.trans e₅))))
  have hcoord (q : (((TopCat.Sheaf.forget (Type v) X).obj
      (limit (pair (moduleSetSheaf F) (moduleSetSheaf G)))).obj (op U) : Type v)) :
      (e q).2 =
        (limit.π (pair (moduleSetSheaf F) (moduleSetSheaf G))
          (Discrete.mk WalkingPair.right)).hom.app (op U) q := by
    change ((Types.productIso _).hom ≫ (↾fun s => s WalkingPair.right)) (_ ) = _
    rw [Types.productIso_hom_comp_eval]
    change
      ((e₃.hom ≫ limit.π
        (Discrete.functor (fun j : WalkingPair =>
          ((evaluation ((Opens X)ᵒᵖ) (Type v)).obj (op U)).obj
            ((TopCat.Sheaf.forget (Type v) X).obj
              ((pair (moduleSetSheaf F) (moduleSetSheaf G)).obj
                (Discrete.mk j)))))
        (Discrete.mk WalkingPair.right))
        (e₂.hom ((e₁'.app (op U)).hom (e₁.hom q)))) = _
    have h₃ := HasLimit.isoOfNatIso_hom_π
      (Discrete.compNatIsoDiscrete
        (fun j : WalkingPair =>
          (TopCat.Sheaf.forget (Type v) X).obj
            ((pair (moduleSetSheaf F) (moduleSetSheaf G)).obj (Discrete.mk j)))
        ((evaluation ((Opens X)ᵒᵖ) (Type v)).obj (op U)))
      (Discrete.mk WalkingPair.right)
    have h₃' :
        e₃.hom ≫ limit.π
            (Discrete.functor (fun j : WalkingPair =>
              ((evaluation ((Opens X)ᵒᵖ) (Type v)).obj (op U)).obj
                ((TopCat.Sheaf.forget (Type v) X).obj
                  ((pair (moduleSetSheaf F) (moduleSetSheaf G)).obj
                    (Discrete.mk j)))))
            (Discrete.mk WalkingPair.right) =
          limit.π
              (Discrete.functor (fun j : WalkingPair =>
                (TopCat.Sheaf.forget (Type v) X).obj
                  ((pair (moduleSetSheaf F) (moduleSetSheaf G)).obj
                    (Discrete.mk j))) ⋙
                ((evaluation ((Opens X)ᵒᵖ) (Type v)).obj (op U)))
              (Discrete.mk WalkingPair.right) ≫
            (Discrete.compNatIsoDiscrete
                (fun j : WalkingPair =>
                  (TopCat.Sheaf.forget (Type v) X).obj
                    ((pair (moduleSetSheaf F) (moduleSetSheaf G)).obj
                      (Discrete.mk j)))
                ((evaluation ((Opens X)ᵒᵖ) (Type v)).obj (op U))).hom.app
              (Discrete.mk WalkingPair.right) := by
      simpa [e₃, Function.comp_def] using h₃
    rw [h₃']
    have h₂ := preservesLimitIso_hom_π
      ((evaluation ((Opens X)ᵒᵖ) (Type v)).obj (op U))
      (Discrete.functor (fun j : WalkingPair =>
        (TopCat.Sheaf.forget (Type v) X).obj
          ((pair (moduleSetSheaf F) (moduleSetSheaf G)).obj (Discrete.mk j))))
      (Discrete.mk WalkingPair.right)
    have h₂' :
        e₂.hom ≫
            limit.π
              (Discrete.functor (fun j : WalkingPair =>
                (TopCat.Sheaf.forget (Type v) X).obj
                  ((pair (moduleSetSheaf F) (moduleSetSheaf G)).obj
                    (Discrete.mk j))) ⋙
                ((evaluation ((Opens X)ᵒᵖ) (Type v)).obj (op U)))
              (Discrete.mk WalkingPair.right) =
          ((evaluation ((Opens X)ᵒᵖ) (Type v)).obj (op U)).map
            (limit.π
              (Discrete.functor (fun j : WalkingPair =>
                (TopCat.Sheaf.forget (Type v) X).obj
                  ((pair (moduleSetSheaf F) (moduleSetSheaf G)).obj
                    (Discrete.mk j))))
              (Discrete.mk WalkingPair.right)) := by
      simpa [e₂, Function.comp_def] using h₂
    have h₁ := HasLimit.isoOfNatIso_hom_π
      ((Functor.isoWhiskerRight
          (Discrete.natIsoFunctor
            (F := pair (moduleSetSheaf F) (moduleSetSheaf G)))
          (TopCat.Sheaf.forget (Type v) X)).trans
        (Discrete.compNatIsoDiscrete
          (fun j : WalkingPair =>
            (pair (moduleSetSheaf F) (moduleSetSheaf G)).obj (Discrete.mk j))
          (TopCat.Sheaf.forget (Type v) X)))
      (Discrete.mk WalkingPair.right)
    let c₁ :=
      (Functor.isoWhiskerRight
          (Discrete.natIsoFunctor
            (F := pair (moduleSetSheaf F) (moduleSetSheaf G)))
          (TopCat.Sheaf.forget (Type v) X)).trans
        (Discrete.compNatIsoDiscrete
          (fun j : WalkingPair =>
            (pair (moduleSetSheaf F) (moduleSetSheaf G)).obj (Discrete.mk j))
          (TopCat.Sheaf.forget (Type v) X))
    have h₁' :
        (e₁'.app (op U)).hom ≫
            (limit.π
              (Discrete.functor (fun j : WalkingPair =>
                (TopCat.Sheaf.forget (Type v) X).obj
                  ((pair (moduleSetSheaf F) (moduleSetSheaf G)).obj
                    (Discrete.mk j))))
              (Discrete.mk WalkingPair.right)).app (op U) =
          (limit.π
              (pair (moduleSetSheaf F) (moduleSetSheaf G) ⋙
                TopCat.Sheaf.forget (Type v) X)
              (Discrete.mk WalkingPair.right)).app (op U) ≫
            (c₁.hom.app (Discrete.mk WalkingPair.right)).app (op U) := by
      have h₁eval := congrArg (fun k => k.app (op U)) h₁
      convert h₁eval using 1 <;>
        simp [e₁', Function.comp_def, Discrete.compNatIsoDiscrete,
          Discrete.natIso, NatIso.ofComponents, NatTrans.comp_app,
          Functor.comp_obj] <;>
        try rfl
    have h₀ := preservesLimitIso_hom_π
      (TopCat.Sheaf.forget (Type v) X)
      (pair (moduleSetSheaf F) (moduleSetSheaf G))
      (Discrete.mk WalkingPair.right)
    have h₀' :
        e₁.hom ≫
            (limit.π
              (pair (moduleSetSheaf F) (moduleSetSheaf G) ⋙
                TopCat.Sheaf.forget (Type v) X)
              (Discrete.mk WalkingPair.right)).app (op U) =
          ((TopCat.Sheaf.forget (Type v) X).map
            (limit.π (pair (moduleSetSheaf F) (moduleSetSheaf G))
              (Discrete.mk WalkingPair.right))).app (op U) := by
      have h₀eval := congrArg (fun k => k.app (op U)) h₀
      rw [NatTrans.comp_app] at h₀eval
      simpa [e₁] using h₀eval
    have h_arrow :
        e₁.hom ≫ (e₁'.app (op U)).hom ≫ e₂.hom ≫ e₃.hom ≫
            limit.π
                (Discrete.functor (fun j : WalkingPair =>
                  ((evaluation ((Opens X)ᵒᵖ) (Type v)).obj (op U)).obj
                    ((TopCat.Sheaf.forget (Type v) X).obj
                      ((pair (moduleSetSheaf F) (moduleSetSheaf G)).obj
                        (Discrete.mk j)))))
                (Discrete.mk WalkingPair.right) =
          (limit.π (pair (moduleSetSheaf F) (moduleSetSheaf G))
            (Discrete.mk WalkingPair.right)).hom.app (op U) := by
      change
        (((e₁.hom ≫ (e₁'.app (op U)).hom) ≫ e₂.hom) ≫
          (e₃.hom ≫
            limit.π
              (Discrete.functor (fun j : WalkingPair =>
                ((evaluation ((Opens X)ᵒᵖ) (Type v)).obj (op U)).obj
                  ((TopCat.Sheaf.forget (Type v) X).obj
                    ((pair (moduleSetSheaf F) (moduleSetSheaf G)).obj
                      (Discrete.mk j)))))
              (Discrete.mk WalkingPair.right))) =
          (limit.π (pair (moduleSetSheaf F) (moduleSetSheaf G))
            (Discrete.mk WalkingPair.right)).hom.app (op U)
      simp only [Category.assoc]
      rw [h₃']
      rw [← Category.assoc e₂.hom]
      rw [h₂']
      have h_eval :
          ((evaluation ((Opens X)ᵒᵖ) (Type v)).obj (op U)).map
              (limit.π
                (Discrete.functor (fun j : WalkingPair =>
                  (TopCat.Sheaf.forget (Type v) X).obj
                    ((pair (moduleSetSheaf F) (moduleSetSheaf G)).obj
                      (Discrete.mk j))))
                (Discrete.mk WalkingPair.right)) =
            (limit.π
                (Discrete.functor (fun j : WalkingPair =>
                  (TopCat.Sheaf.forget (Type v) X).obj
                    ((pair (moduleSetSheaf F) (moduleSetSheaf G)).obj
                      (Discrete.mk j))))
                (Discrete.mk WalkingPair.right)).app (op U) := by
        rfl
      rw [h_eval]
      rw [← Category.assoc (e₁'.app (op U)).hom]
      rw [h₁']
      simp only [Category.assoc]
      rw [← Category.assoc e₁.hom]
      rw [h₀']
      have hforget :
          (TopCat.Sheaf.forget (Type v) X).map
              (limit.π (pair (moduleSetSheaf F) (moduleSetSheaf G))
                (Discrete.mk WalkingPair.right)) =
            (limit.π (pair (moduleSetSheaf F) (moduleSetSheaf G))
              (Discrete.mk WalkingPair.right)).hom := by
        rfl
      rw [hforget]
      simp only [c₁, Discrete.compNatIsoDiscrete, Discrete.natIso,
        NatIso.ofComponents]
      rfl
    have h_arrow' := h_arrow
    rw [h₃'] at h_arrow'
    have hq := congrArg (fun k => k q) h_arrow'
    change
      (limit.π
          (Discrete.functor (fun j : WalkingPair =>
            (TopCat.Sheaf.forget (Type v) X).obj
              ((pair (moduleSetSheaf F) (moduleSetSheaf G)).obj
                (Discrete.mk j))) ⋙
            ((evaluation ((Opens X)ᵒᵖ) (Type v)).obj (op U)))
          (Discrete.mk WalkingPair.right) ≫
        (Discrete.compNatIsoDiscrete
          (fun j : WalkingPair =>
            (TopCat.Sheaf.forget (Type v) X).obj
              ((pair (moduleSetSheaf F) (moduleSetSheaf G)).obj
                (Discrete.mk j)))
          ((evaluation ((Opens X)ᵒᵖ) (Type v)).obj (op U))).hom.app
          (Discrete.mk WalkingPair.right))
        (e₂.hom ((e₁'.app (op U)).hom (e₁.hom q))) =
      (limit.π (pair (moduleSetSheaf F) (moduleSetSheaf G))
        (Discrete.mk WalkingPair.right)).hom.app (op U) q at hq
    exact hq
  have hp := congrArg Prod.snd (e.apply_symm_apply (s, t))
  exact hcoord _ |>.symm.trans hp

private theorem product_germ_first {X : TopCat.{v}}
    {O : RingSheaf.{v, v} X} (F G : Mod O) (U : Opens X)
    (s : (F.val.obj (op U) : Type v))
    (t : (G.val.obj (op U) : Type v)) (x : U) :
    stalkProductFirst F G x.1
        (TopCat.Presheaf.germ (moduleSetProduct F G).presheaf U x.1 x.2
          ((sheafProductSectionsEquiv (moduleSetSheaf F) (moduleSetSheaf G) U).symm
            (s, t))) =
        moduleStalkUnderlyingEquiv F x.1
        (TopCat.Presheaf.germ F.val.presheaf U x.1 x.2 s) := by
  unfold moduleSetSheaf
  change (TopCat.Presheaf.stalkFunctor (Type v) x.1).map
      (limit.π (pair (moduleSetSheaf F) (moduleSetSheaf G))
        (Discrete.mk WalkingPair.left)).hom
      (TopCat.Presheaf.germ (moduleSetProduct F G).presheaf U x.1 x.2
        ((sheafProductSectionsEquiv (moduleSetSheaf F) (moduleSetSheaf G) U).symm
          (s, t))) = _
  have hh := TopCat.Presheaf.stalkFunctor_map_germ_apply
    (F := (moduleSetProduct F G).presheaf)
    (G := (moduleSetSheaf F).presheaf)
    U x.1 x.2
    (limit.π (pair (moduleSetSheaf F) (moduleSetSheaf G))
      (Discrete.mk WalkingPair.left)).hom
    ((sheafProductSectionsEquiv (moduleSetSheaf F) (moduleSetSheaf G) U).symm
      (s, t))
  calc
    _ = (TopCat.Presheaf.germ (moduleSetSheaf F).presheaf U x.1 x.2)
        ((limit.π (pair (moduleSetSheaf F) (moduleSetSheaf G))
          (Discrete.mk WalkingPair.left)).hom.app (op U)
          ((sheafProductSectionsEquiv (moduleSetSheaf F) (moduleSetSheaf G) U).symm
            (s, t))) := hh
    _ = _ := by
      rw [test_product_sections_first F G U s t]
      have hsectionType :
          ((moduleSetSheaf F).presheaf.obj (op U) : Type v) =
            (F.val.obj (op U) : Type v) := by
        rfl
      cases hsectionType
      have hobj :
          ((SheafOfModules.toSheaf O).obj F).obj = F.val.presheaf := by
        rfl
      let s' : (forget AddCommGrpCat).obj
          (((SheafOfModules.toSheaf O).obj F).obj.obj (op U)) := s
      have hgerm :
          (ConcreteCategory.hom
            ((forget AddCommGrpCat).map
              (algebraicStalkGerm ((SheafOfModules.toSheaf O).obj F).obj
                U x.1 x.2))) s' =
          (ConcreteCategory.hom
            (TopCat.Presheaf.germ F.val.presheaf U x.1 x.2)) s' := by
        rfl
      have hF := algebraicStalkGerm_underlying (forget AddCommGrpCat)
        ((SheafOfModules.toSheaf O).obj F).obj U x.1 x.2
      have hF' := congrArg (fun k => (ConcreteCategory.hom k) s') hF
      simp only [ConcreteCategory.comp_apply] at hF'
      change
        (algebraicStalkUnderlyingEquiv (forget AddCommGrpCat)
          ((SheafOfModules.toSheaf O).obj F).obj x.1)
          ((ConcreteCategory.hom
            ((forget AddCommGrpCat).map
              (algebraicStalkGerm ((SheafOfModules.toSheaf O).obj F).obj
                U x.1 x.2))) s') = _ at hF'
      rw [hgerm] at hF'
      exact hF'.symm

private theorem product_germ_second {X : TopCat.{v}}
    {O : RingSheaf.{v, v} X} (F G : Mod O) (U : Opens X)
    (s : (F.val.obj (op U) : Type v))
    (t : (G.val.obj (op U) : Type v)) (x : U) :
    stalkProductSecond F G x.1
        (TopCat.Presheaf.germ (moduleSetProduct F G).presheaf U x.1 x.2
          ((sheafProductSectionsEquiv (moduleSetSheaf F) (moduleSetSheaf G) U).symm
            (s, t))) =
      moduleStalkUnderlyingEquiv G x.1
        (TopCat.Presheaf.germ G.val.presheaf U x.1 x.2 t) := by
  change (TopCat.Presheaf.stalkFunctor (Type v) x.1).map
      (limit.π (pair (moduleSetSheaf F) (moduleSetSheaf G))
        (Discrete.mk WalkingPair.right)).hom
      (TopCat.Presheaf.germ (moduleSetProduct F G).presheaf U x.1 x.2
        ((sheafProductSectionsEquiv (moduleSetSheaf F) (moduleSetSheaf G) U).symm
          (s, t))) = _
  have hh := TopCat.Presheaf.stalkFunctor_map_germ_apply
    (F := (moduleSetProduct F G).presheaf)
    (G := (moduleSetSheaf G).presheaf)
    U x.1 x.2
    (limit.π (pair (moduleSetSheaf F) (moduleSetSheaf G))
      (Discrete.mk WalkingPair.right)).hom
    ((sheafProductSectionsEquiv (moduleSetSheaf F) (moduleSetSheaf G) U).symm
      (s, t))
  calc
    _ = (TopCat.Presheaf.germ (moduleSetSheaf G).presheaf U x.1 x.2)
        ((limit.π (pair (moduleSetSheaf F) (moduleSetSheaf G))
          (Discrete.mk WalkingPair.right)).hom.app (op U)
          ((sheafProductSectionsEquiv (moduleSetSheaf F) (moduleSetSheaf G) U).symm
            (s, t))) := hh
    _ = _ := by
      rw [test_product_sections_second F G U s t]
      have hsectionType :
          ((moduleSetSheaf G).presheaf.obj (op U) : Type v) =
            (G.val.obj (op U) : Type v) := by
        rfl
      cases hsectionType
      have hobj :
          ((SheafOfModules.toSheaf O).obj G).obj = G.val.presheaf := by
        rfl
      let s' : (forget AddCommGrpCat).obj
          (((SheafOfModules.toSheaf O).obj G).obj.obj (op U)) := t
      have hgerm :
          (ConcreteCategory.hom
            ((forget AddCommGrpCat).map
              (algebraicStalkGerm ((SheafOfModules.toSheaf O).obj G).obj
                U x.1 x.2))) s' =
          (ConcreteCategory.hom
            (TopCat.Presheaf.germ G.val.presheaf U x.1 x.2)) s' := by
        rfl
      have hF := algebraicStalkGerm_underlying (forget AddCommGrpCat)
        ((SheafOfModules.toSheaf O).obj G).obj U x.1 x.2
      have hF' := congrArg (fun k => (ConcreteCategory.hom k) s') hF
      simp only [ConcreteCategory.comp_apply] at hF'
      change
        (algebraicStalkUnderlyingEquiv (forget AddCommGrpCat)
          ((SheafOfModules.toSheaf O).obj G).obj x.1)
          ((ConcreteCategory.hom
            ((forget AddCommGrpCat).map
              (algebraicStalkGerm ((SheafOfModules.toSheaf O).obj G).obj
                U x.1 x.2))) s') = _ at hF'
      rw [hgerm] at hF'
      exact hF'.symm

private theorem stalk_product_ext {X : TopCat.{v}}
    {O : RingSheaf.{v, v} X} (F G : Mod O) (x : X)
    (q r : (TopCat.Presheaf.stalkFunctor (Type v) x).obj
      (moduleSetProduct F G).presheaf)
    (h₁ : stalkProductFirst F G x q = stalkProductFirst F G x r)
    (h₂ : stalkProductSecond F G x q = stalkProductSecond F G x r) :
    q = r := by
  rcases (moduleSetProduct F G).presheaf.exists_germ_eq q with
    ⟨U₁, hx₁, s₁, rfl⟩
  rcases (moduleSetProduct F G).presheaf.exists_germ_eq r with
    ⟨U₂, hx₂, s₂, rfl⟩
  have h₁' := h₁
  have h₂' := h₂
  change (TopCat.Presheaf.stalkFunctor (Type v) x).map
      (limit.π (pair (moduleSetSheaf F) (moduleSetSheaf G))
        (Discrete.mk WalkingPair.left)).hom
      (TopCat.Presheaf.germ (moduleSetProduct F G).presheaf U₁ x hx₁ s₁) =
    (TopCat.Presheaf.stalkFunctor (Type v) x).map
      (limit.π (pair (moduleSetSheaf F) (moduleSetSheaf G))
        (Discrete.mk WalkingPair.left)).hom
      (TopCat.Presheaf.germ (moduleSetProduct F G).presheaf U₂ x hx₂ s₂) at h₁'
  change (TopCat.Presheaf.stalkFunctor (Type v) x).map
      (limit.π (pair (moduleSetSheaf F) (moduleSetSheaf G))
        (Discrete.mk WalkingPair.right)).hom
      (TopCat.Presheaf.germ (moduleSetProduct F G).presheaf U₁ x hx₁ s₁) =
    (TopCat.Presheaf.stalkFunctor (Type v) x).map
      (limit.π (pair (moduleSetSheaf F) (moduleSetSheaf G))
        (Discrete.mk WalkingPair.right)).hom
      (TopCat.Presheaf.germ (moduleSetProduct F G).presheaf U₂ x hx₂ s₂) at h₂'
  simp only [TopCat.Presheaf.stalkFunctor_map_germ_apply] at h₁' h₂'
  change (moduleSetSheaf F).presheaf.germ U₁ x hx₁
      ((limit.π (pair (moduleSetSheaf F) (moduleSetSheaf G))
        (Discrete.mk WalkingPair.left)).hom.app (op U₁) s₁) =
    (moduleSetSheaf F).presheaf.germ U₂ x hx₂
      ((limit.π (pair (moduleSetSheaf F) (moduleSetSheaf G))
        (Discrete.mk WalkingPair.left)).hom.app (op U₂) s₂) at h₁'
  change (moduleSetSheaf G).presheaf.germ U₁ x hx₁
      ((limit.π (pair (moduleSetSheaf F) (moduleSetSheaf G))
        (Discrete.mk WalkingPair.right)).hom.app (op U₁) s₁) =
    (moduleSetSheaf G).presheaf.germ U₂ x hx₂
      ((limit.π (pair (moduleSetSheaf F) (moduleSetSheaf G))
        (Discrete.mk WalkingPair.right)).hom.app (op U₂) s₂) at h₂'
  have hcoordF₁ :
      (limit.π (pair (moduleSetSheaf F) (moduleSetSheaf G))
        (Discrete.mk WalkingPair.left)).hom.app (op U₁) s₁ =
        (sheafProductSectionsEquiv (moduleSetSheaf F) (moduleSetSheaf G) U₁ s₁).1 := by
    let e := sheafProductSectionsEquiv (moduleSetSheaf F) (moduleSetSheaf G) U₁
    rw [← e.symm_apply_apply s₁]
    simpa [e] using test_product_sections_first F G U₁ (e s₁).1 (e s₁).2
  have hcoordF₂ :
      (limit.π (pair (moduleSetSheaf F) (moduleSetSheaf G))
        (Discrete.mk WalkingPair.left)).hom.app (op U₂) s₂ =
        (sheafProductSectionsEquiv (moduleSetSheaf F) (moduleSetSheaf G) U₂ s₂).1 := by
    let e := sheafProductSectionsEquiv (moduleSetSheaf F) (moduleSetSheaf G) U₂
    rw [← e.symm_apply_apply s₂]
    simpa [e] using test_product_sections_first F G U₂ (e s₂).1 (e s₂).2
  have hcoordG₁ :
      (limit.π (pair (moduleSetSheaf F) (moduleSetSheaf G))
        (Discrete.mk WalkingPair.right)).hom.app (op U₁) s₁ =
        (sheafProductSectionsEquiv (moduleSetSheaf F) (moduleSetSheaf G) U₁ s₁).2 := by
    let e := sheafProductSectionsEquiv (moduleSetSheaf F) (moduleSetSheaf G) U₁
    rw [← e.symm_apply_apply s₁]
    simpa [e] using test_product_sections_second F G U₁ (e s₁).1 (e s₁).2
  have hcoordG₂ :
      (limit.π (pair (moduleSetSheaf F) (moduleSetSheaf G))
        (Discrete.mk WalkingPair.right)).hom.app (op U₂) s₂ =
        (sheafProductSectionsEquiv (moduleSetSheaf F) (moduleSetSheaf G) U₂ s₂).2 := by
    let e := sheafProductSectionsEquiv (moduleSetSheaf F) (moduleSetSheaf G) U₂
    rw [← e.symm_apply_apply s₂]
    simpa [e] using test_product_sections_second F G U₂ (e s₂).1 (e s₂).2
  rw [hcoordF₁, hcoordF₂] at h₁'
  rw [hcoordG₁, hcoordG₂] at h₂'
  have h₁'' := h₁'
  have h₂'' := h₂'
  rcases (moduleSetSheaf F).presheaf.germ_eq x hx₁ hx₂
    ((sheafProductSectionsEquiv (moduleSetSheaf F) (moduleSetSheaf G) U₁ s₁).1)
    ((sheafProductSectionsEquiv (moduleSetSheaf F) (moduleSetSheaf G) U₂ s₂).1) h₁' with
    ⟨W₁, hxW₁, iW₁U₁, iW₁U₂, hW₁⟩
  rcases (moduleSetSheaf G).presheaf.germ_eq x hx₁ hx₂
    ((sheafProductSectionsEquiv (moduleSetSheaf F) (moduleSetSheaf G) U₁ s₁).2)
    ((sheafProductSectionsEquiv (moduleSetSheaf F) (moduleSetSheaf G) U₂ s₂).2) h₂' with
    ⟨W₂, hxW₂, iW₂U₁, iW₂U₂, hW₂⟩
  let W := W₁ ⊓ W₂
  let j₁ : W ⟶ W₁ := homOfLE inf_le_left
  let j₂ : W ⟶ W₂ := homOfLE inf_le_right
  let k₁ : W ⟶ U₁ := j₁ ≫ iW₁U₁
  let k₂ : W ⟶ U₂ := j₁ ≫ iW₁U₂
  have hW₁' := congrArg (fun z =>
      (moduleSetSheaf F).presheaf.map j₁.op z) hW₁
  have hW₂' := congrArg (fun z =>
      (moduleSetSheaf G).presheaf.map j₂.op z) hW₂
  have hFcoord :
      (moduleSetSheaf F).presheaf.map k₁.op
          ((limit.π (pair (moduleSetSheaf F) (moduleSetSheaf G))
            (Discrete.mk WalkingPair.left)).hom.app (op U₁) s₁) =
        (moduleSetSheaf F).presheaf.map k₂.op
          ((limit.π (pair (moduleSetSheaf F) (moduleSetSheaf G))
            (Discrete.mk WalkingPair.left)).hom.app (op U₂) s₂) := by
    rw [hcoordF₁, hcoordF₂]
    change (moduleSetSheaf F).presheaf.map (iW₁U₁.op ≫ j₁.op)
          ((sheafProductSectionsEquiv (moduleSetSheaf F) (moduleSetSheaf G) U₁ s₁).1) =
        (moduleSetSheaf F).presheaf.map (iW₁U₂.op ≫ j₁.op)
          ((sheafProductSectionsEquiv (moduleSetSheaf F) (moduleSetSheaf G) U₂ s₂).1)
    simpa only [(moduleSetSheaf F).presheaf.map_comp, ConcreteCategory.comp_apply] using hW₁'
  have hGcoord :
      (moduleSetSheaf G).presheaf.map k₁.op
          ((limit.π (pair (moduleSetSheaf F) (moduleSetSheaf G))
            (Discrete.mk WalkingPair.right)).hom.app (op U₁) s₁) =
        (moduleSetSheaf G).presheaf.map k₂.op
          ((limit.π (pair (moduleSetSheaf F) (moduleSetSheaf G))
            (Discrete.mk WalkingPair.right)).hom.app (op U₂) s₂) := by
    let l₁ : W ⟶ U₁ := j₂ ≫ iW₂U₁
    let l₂ : W ⟶ U₂ := j₂ ≫ iW₂U₂
    have hk₁ : k₁ = l₁ := Subsingleton.elim _ _
    have hk₂ : k₂ = l₂ := Subsingleton.elim _ _
    rw [hcoordG₁, hcoordG₂, hk₁, hk₂]
    change (moduleSetSheaf G).presheaf.map (iW₂U₁.op ≫ j₂.op)
          ((sheafProductSectionsEquiv (moduleSetSheaf F) (moduleSetSheaf G) U₁ s₁).2) =
        (moduleSetSheaf G).presheaf.map (iW₂U₂.op ≫ j₂.op)
          ((sheafProductSectionsEquiv (moduleSetSheaf F) (moduleSetSheaf G) U₂ s₂).2)
    simpa only [(moduleSetSheaf G).presheaf.map_comp, ConcreteCategory.comp_apply] using hW₂'
  have hleft (V : Opens X)
      (z : (moduleSetProduct F G).presheaf.obj (op V)) :
      (limit.π (pair (moduleSetSheaf F) (moduleSetSheaf G))
        (Discrete.mk WalkingPair.left)).hom.app (op V) z =
        (sheafProductSectionsEquiv (moduleSetSheaf F) (moduleSetSheaf G) V z).1 := by
    let e := sheafProductSectionsEquiv (moduleSetSheaf F) (moduleSetSheaf G) V
    rw [← e.symm_apply_apply z]
    simpa [e] using test_product_sections_first F G V (e z).1 (e z).2
  have hright (V : Opens X)
      (z : (moduleSetProduct F G).presheaf.obj (op V)) :
      (limit.π (pair (moduleSetSheaf F) (moduleSetSheaf G))
        (Discrete.mk WalkingPair.right)).hom.app (op V) z =
        (sheafProductSectionsEquiv (moduleSetSheaf F) (moduleSetSheaf G) V z).2 := by
    let e := sheafProductSectionsEquiv (moduleSetSheaf F) (moduleSetSheaf G) V
    rw [← e.symm_apply_apply z]
    simpa [e] using test_product_sections_second F G V (e z).1 (e z).2
  have hproduct :
      (moduleSetProduct F G).presheaf.map k₁.op s₁ =
        (moduleSetProduct F G).presheaf.map k₂.op s₂ := by
    apply (sheafProductSectionsEquiv (moduleSetSheaf F) (moduleSetSheaf G) W).injective
    have hnF₁ :
        (limit.π (pair (moduleSetSheaf F) (moduleSetSheaf G))
          (Discrete.mk WalkingPair.left)).hom.app (op W)
            ((moduleSetProduct F G).presheaf.map k₁.op s₁) =
          (moduleSetSheaf F).presheaf.map k₁.op
            ((limit.π (pair (moduleSetSheaf F) (moduleSetSheaf G))
              (Discrete.mk WalkingPair.left)).hom.app (op U₁) s₁) := by
      have hn := congrArg (fun z => z s₁)
        ((limit.π (pair (moduleSetSheaf F) (moduleSetSheaf G))
          (Discrete.mk WalkingPair.left)).hom.naturality k₁.op)
      change (limit.π (pair (moduleSetSheaf F) (moduleSetSheaf G))
          (Discrete.mk WalkingPair.left)).hom.app (op W)
            ((moduleSetProduct F G).presheaf.map k₁.op s₁) = _ at hn
      convert hn using 1
      all_goals rfl
    have hnF₂ :
        (limit.π (pair (moduleSetSheaf F) (moduleSetSheaf G))
          (Discrete.mk WalkingPair.left)).hom.app (op W)
            ((moduleSetProduct F G).presheaf.map k₂.op s₂) =
          (moduleSetSheaf F).presheaf.map k₂.op
            ((limit.π (pair (moduleSetSheaf F) (moduleSetSheaf G))
              (Discrete.mk WalkingPair.left)).hom.app (op U₂) s₂) := by
      have hn := congrArg (fun z => z s₂)
        ((limit.π (pair (moduleSetSheaf F) (moduleSetSheaf G))
          (Discrete.mk WalkingPair.left)).hom.naturality k₂.op)
      change (limit.π (pair (moduleSetSheaf F) (moduleSetSheaf G))
          (Discrete.mk WalkingPair.left)).hom.app (op W)
            ((moduleSetProduct F G).presheaf.map k₂.op s₂) = _ at hn
      convert hn using 1
      all_goals rfl
    have hnGleft :
        (limit.π (pair (moduleSetSheaf F) (moduleSetSheaf G))
          (Discrete.mk WalkingPair.right)).hom.app (op W)
            ((moduleSetProduct F G).presheaf.map k₁.op s₁) =
          (moduleSetSheaf G).presheaf.map k₁.op
            ((limit.π (pair (moduleSetSheaf F) (moduleSetSheaf G))
              (Discrete.mk WalkingPair.right)).hom.app (op U₁) s₁) := by
      have hn := congrArg (fun z => z s₁)
        ((limit.π (pair (moduleSetSheaf F) (moduleSetSheaf G))
          (Discrete.mk WalkingPair.right)).hom.naturality k₁.op)
      change (limit.π (pair (moduleSetSheaf F) (moduleSetSheaf G))
          (Discrete.mk WalkingPair.right)).hom.app (op W)
            ((moduleSetProduct F G).presheaf.map k₁.op s₁) = _ at hn
      convert hn using 1
      all_goals rfl
    have hnGright :
        (limit.π (pair (moduleSetSheaf F) (moduleSetSheaf G))
          (Discrete.mk WalkingPair.right)).hom.app (op W)
            ((moduleSetProduct F G).presheaf.map k₂.op s₂) =
          (moduleSetSheaf G).presheaf.map k₂.op
            ((limit.π (pair (moduleSetSheaf F) (moduleSetSheaf G))
              (Discrete.mk WalkingPair.right)).hom.app (op U₂) s₂) := by
      have hn := congrArg (fun z => z s₂)
        ((limit.π (pair (moduleSetSheaf F) (moduleSetSheaf G))
          (Discrete.mk WalkingPair.right)).hom.naturality k₂.op)
      change (limit.π (pair (moduleSetSheaf F) (moduleSetSheaf G))
          (Discrete.mk WalkingPair.right)).hom.app (op W)
            ((moduleSetProduct F G).presheaf.map k₂.op s₂) = _ at hn
      convert hn using 1
      all_goals rfl
    have hleft₁ :
        (sheafProductSectionsEquiv (moduleSetSheaf F) (moduleSetSheaf G) W
          ((moduleSetProduct F G).presheaf.map k₁.op s₁)).1 =
        (moduleSetSheaf F).presheaf.map k₁.op
          ((limit.π (pair (moduleSetSheaf F) (moduleSetSheaf G))
            (Discrete.mk WalkingPair.left)).hom.app (op U₁) s₁) := by
      rw [← hleft W]
      simpa [moduleSetSheaf] using hnF₁
    have hleft₂ :
        (sheafProductSectionsEquiv (moduleSetSheaf F) (moduleSetSheaf G) W
          ((moduleSetProduct F G).presheaf.map k₂.op s₂)).1 =
        (moduleSetSheaf F).presheaf.map k₂.op
          ((limit.π (pair (moduleSetSheaf F) (moduleSetSheaf G))
            (Discrete.mk WalkingPair.left)).hom.app (op U₂) s₂) := by
      rw [← hleft W]
      simpa [moduleSetSheaf] using hnF₂
    have hright₁ :
        (sheafProductSectionsEquiv (moduleSetSheaf F) (moduleSetSheaf G) W
          ((moduleSetProduct F G).presheaf.map k₁.op s₁)).2 =
        (moduleSetSheaf G).presheaf.map k₁.op
          ((limit.π (pair (moduleSetSheaf F) (moduleSetSheaf G))
            (Discrete.mk WalkingPair.right)).hom.app (op U₁) s₁) := by
      rw [← hright W]
      simpa [moduleSetSheaf] using hnGleft
    have hright₂ :
        (sheafProductSectionsEquiv (moduleSetSheaf F) (moduleSetSheaf G) W
          ((moduleSetProduct F G).presheaf.map k₂.op s₂)).2 =
        (moduleSetSheaf G).presheaf.map k₂.op
          ((limit.π (pair (moduleSetSheaf F) (moduleSetSheaf G))
            (Discrete.mk WalkingPair.right)).hom.app (op U₂) s₂) := by
      rw [← hright W]
      simpa [moduleSetSheaf] using hnGright
    apply Prod.ext
    · exact hleft₁.trans (hFcoord.trans hleft₂.symm)
    · exact hright₁.trans (hGcoord.trans hright₂.symm)
  exact TopCat.Presheaf.germ_ext (moduleSetProduct F G).presheaf W
    (by exact ⟨hxW₁, hxW₂⟩) k₁ k₂ hproduct

/-! The stalkwise characterization from the source. -/
theorem isSectionwiseBilinear_of_isStalkwiseBilinear {X : TopCat.{v}}
    {O : RingSheaf.{v, v} X} {F G H : Mod O}
    (f : ModuleSetMap F G H) (h : IsStalkwiseBilinear f) :
    IsSectionwiseBilinear f := by
  intro U
  have hsectionMap_germ
      (s : (F.val.obj (op U) : Type v))
      (t : (G.val.obj (op U) : Type v)) (x : U) :
      stalkMap f x.1
          (TopCat.Presheaf.germ (moduleSetProduct F G).presheaf U x.1 x.2
            ((sheafProductSectionsEquiv (moduleSetSheaf F) (moduleSetSheaf G) U).symm
              (s, t))) =
        TopCat.Presheaf.germ (moduleSetSheaf H).presheaf U x.1 x.2
          (sectionMap f U s t) := by
    change
      (TopCat.Presheaf.stalkFunctor (Type v) x.1).map f.hom
          (TopCat.Presheaf.germ (moduleSetProduct F G).presheaf U x.1 x.2
            ((sheafProductSectionsEquiv (moduleSetSheaf F) (moduleSetSheaf G) U).symm
              (s, t))) = _
    simpa [sectionMap] using
      (TopCat.Presheaf.stalkFunctor_map_germ_apply U x.1 x.2 f.hom
        ((sheafProductSectionsEquiv (moduleSetSheaf F) (moduleSetSheaf G) U).symm
          (s, t)))
  have hsection_value
      (x : U)
      (p : StalkPairing F G x.1)
      (g : SectionBilinearMap
        (TopCat.Presheaf.stalk (C := RingCat) O.obj x.1 : Type v)
        ↑(moduleStalk F x.1) ↑(moduleStalk G x.1) ↑(moduleStalk H x.1))
      (hg : ∀ a b, g a b = (moduleStalkUnderlyingEquiv H x.1).symm
        (stalkMap f x.1 (p a b)))
      (s : (F.val.obj (op U) : Type v))
      (t : (G.val.obj (op U) : Type v)) :
      (moduleStalkUnderlyingEquiv H x.1).symm
          (TopCat.Presheaf.germ (moduleSetSheaf H).presheaf U x.1 x.2
            (sectionMap f U s t)) =
        g (TopCat.Presheaf.germ F.val.presheaf U x.1 x.2 s)
          (TopCat.Presheaf.germ G.val.presheaf U x.1 x.2 t) := by
    let a := TopCat.Presheaf.germ F.val.presheaf U x.1 x.2 s
    let b := TopCat.Presheaf.germ G.val.presheaf U x.1 x.2 t
    have hpfirst :
        stalkProductFirst F G x.1 (p a b) =
          moduleStalkUnderlyingEquiv F x.1 a := by
      have hp := congrArg (moduleStalkUnderlyingEquiv F x.1)
        (p.fst_toFun a b)
      simpa only [a, Equiv.apply_symm_apply] using hp
    have hpsecond :
        stalkProductSecond F G x.1 (p a b) =
          moduleStalkUnderlyingEquiv G x.1 b := by
      have hp := congrArg (moduleStalkUnderlyingEquiv G x.1)
        (p.snd_toFun a b)
      simpa only [b, Equiv.apply_symm_apply] using hp
    have hproduct := product_germ_first F G U s t x
    have hproduct' := product_germ_second F G U s t x
    have hpEq :
        p a b =
          TopCat.Presheaf.germ (moduleSetProduct F G).presheaf U x.1 x.2
            ((sheafProductSectionsEquiv (moduleSetSheaf F) (moduleSetSheaf G) U).symm
              (s, t)) := by
      apply stalk_product_ext F G x.1
      · exact hpfirst.trans hproduct.symm
      · exact hpsecond.trans hproduct'.symm
    rw [hg a b, hpEq, hsectionMap_germ]
  have hmodule_germ
      (K : Mod O) (u : (K.val.obj (op U) : Type v)) (x : U) :
      (moduleStalkUnderlyingEquiv K x.1).symm
          (TopCat.Presheaf.germ (moduleSetSheaf K).presheaf U x.1 x.2 u) =
        TopCat.Presheaf.germ K.val.presheaf U x.1 x.2 u := by
    unfold moduleStalkUnderlyingEquiv
    have hsectionType :
        ((moduleSetSheaf K).presheaf.obj (op U) : Type v) =
          (K.val.obj (op U) : Type v) := by
      rfl
    cases hsectionType
    let u' : (forget AddCommGrpCat).obj
        (((SheafOfModules.toSheaf O).obj K).obj.obj (op U)) := u
    have hgerm :
        (ConcreteCategory.hom
          ((forget AddCommGrpCat).map
            (algebraicStalkGerm ((SheafOfModules.toSheaf O).obj K).obj
              U x.1 x.2))) u' =
        (ConcreteCategory.hom
          (TopCat.Presheaf.germ K.val.presheaf U x.1 x.2)) u' := by
      rfl
    have hK := algebraicStalkGerm_underlying (forget AddCommGrpCat)
      ((SheafOfModules.toSheaf O).obj K).obj U x.1 x.2
    have hK' := congrArg (fun k => (ConcreteCategory.hom k) u') hK
    simp only [ConcreteCategory.comp_apply] at hK'
    change
      (algebraicStalkUnderlyingEquiv (forget AddCommGrpCat)
        ((SheafOfModules.toSheaf O).obj K).obj x.1)
        ((ConcreteCategory.hom
          ((forget AddCommGrpCat).map
            (algebraicStalkGerm ((SheafOfModules.toSheaf O).obj K).obj
              U x.1 x.2))) u') = _ at hK'
    rw [hgerm] at hK'
    have hset :
        (ConcreteCategory.hom
          ((moduleSetSheaf K).presheaf.germ U x.1 x.2)) u =
        (algebraicStalkUnderlyingEquiv (forget AddCommGrpCat)
          ((SheafOfModules.toSheaf O).obj K).obj x.1)
          ((ConcreteCategory.hom (TopCat.Presheaf.germ K.val.presheaf U x.1 x.2)) u) := by
      change
        (ConcreteCategory.hom
          ((underlyingPresheaf (forget AddCommGrpCat)
            ((SheafOfModules.toSheaf O).obj K).obj).germ U x.1 x.2)) u' =
          (algebraicStalkUnderlyingEquiv (forget AddCommGrpCat)
            ((SheafOfModules.toSheaf O).obj K).obj x.1)
            ((ConcreteCategory.hom (TopCat.Presheaf.germ K.val.presheaf U x.1 x.2)) u')
      exact hK'.symm
    rw [hset]
    exact (algebraicStalkUnderlyingEquiv (forget AddCommGrpCat)
      ((SheafOfModules.toSheaf O).obj K).obj x.1).symm_apply_apply _
  have hmodule_germ_add
      (K : Mod O) (u v : (K.val.obj (op U) : Type v)) (x : U) :
      (moduleStalkUnderlyingEquiv K x.1).symm
          (TopCat.Presheaf.germ (moduleSetSheaf K).presheaf U x.1 x.2 (u + v)) =
        (moduleStalkUnderlyingEquiv K x.1).symm
            (TopCat.Presheaf.germ (moduleSetSheaf K).presheaf U x.1 x.2 u) +
          (moduleStalkUnderlyingEquiv K x.1).symm
            (TopCat.Presheaf.germ (moduleSetSheaf K).presheaf U x.1 x.2 v) := by
    rw [hmodule_germ K u x, hmodule_germ K v x, hmodule_germ K (u + v) x]
    exact (algebraicStalkGerm ((SheafOfModules.toSheaf O).obj K).obj
      U x.1 x.2).hom.map_add u v
  have hmodule_germ_smul
      (K : Mod O) (r : (O.obj.obj (op U) : Type v))
      (u : (K.val.obj (op U) : Type v)) (x : U) :
      (moduleStalkUnderlyingEquiv K x.1).symm
          (TopCat.Presheaf.germ (moduleSetSheaf K).presheaf U x.1 x.2 (r • u)) =
        (TopCat.Presheaf.germ O.obj U x.1 x.2 r) •
          (moduleStalkUnderlyingEquiv K x.1).symm
            (TopCat.Presheaf.germ (moduleSetSheaf K).presheaf U x.1 x.2 u) := by
    rw [hmodule_germ K (r • u) x, hmodule_germ K u x]
    exact PresheafOfModules.germ_ringCat_smul K.val x U x.2 r u
  refine ⟨{
    toFun := sectionMap f U
    map_add_left' := ?_
    map_smul_left' := ?_
    map_add_right' := ?_
    map_smul_right' := ?_ }, ?_⟩
  · intro s₁ s₂ t
    let s₁₂ : (F.val.obj (op U) : Type v) := s₁ + s₂
    change sectionMap f U s₁₂ t =
      sectionMap f U s₁ t + sectionMap f U s₂ t
    apply sections_eq_of_equal_stalks (moduleSetSheaf H) U
    intro x
    rcases h x.1 with ⟨p, g, hg⟩
    have hFadd := hmodule_germ_add F s₁ s₂ x
    rw [hmodule_germ F (s₁ + s₂) x, hmodule_germ F s₁ x,
      hmodule_germ F s₂ x] at hFadd
    apply (moduleStalkUnderlyingEquiv H x.1).symm.injective
    rw [hsection_value x p g hg s₁₂ t]
    rw [hmodule_germ_add H (sectionMap f U s₁ t) (sectionMap f U s₂ t) x]
    rw [hsection_value x p g hg s₁ t, hsection_value x p g hg s₂ t]
    rw [hFadd]
    exact g.map_add_left' _ _ _
  · intro r s t
    let rs : (F.val.obj (op U) : Type v) := r • s
    change sectionMap f U rs t = r • sectionMap f U s t
    apply sections_eq_of_equal_stalks (moduleSetSheaf H) U
    intro x
    rcases h x.1 with ⟨p, g, hg⟩
    have hFsmul := hmodule_germ_smul F r s x
    rw [hmodule_germ F (r • s) x, hmodule_germ F s x] at hFsmul
    apply (moduleStalkUnderlyingEquiv H x.1).symm.injective
    rw [hsection_value x p g hg rs t]
    rw [hmodule_germ_smul H r (sectionMap f U s t) x]
    rw [hsection_value x p g hg s t]
    rw [hFsmul]
    exact g.map_smul_left' _ _ _
  · intro s t₁ t₂
    let t₁₂ : (G.val.obj (op U) : Type v) := t₁ + t₂
    change sectionMap f U s t₁₂ =
      sectionMap f U s t₁ + sectionMap f U s t₂
    apply sections_eq_of_equal_stalks (moduleSetSheaf H) U
    intro x
    rcases h x.1 with ⟨p, g, hg⟩
    have hGadd := hmodule_germ_add G t₁ t₂ x
    rw [hmodule_germ G (t₁ + t₂) x, hmodule_germ G t₁ x,
      hmodule_germ G t₂ x] at hGadd
    apply (moduleStalkUnderlyingEquiv H x.1).symm.injective
    rw [hsection_value x p g hg s t₁₂]
    rw [hmodule_germ_add H (sectionMap f U s t₁) (sectionMap f U s t₂) x]
    rw [hsection_value x p g hg s t₁, hsection_value x p g hg s t₂]
    rw [hGadd]
    exact g.map_add_right' _ _ _
  · intro r s t
    let rt : (G.val.obj (op U) : Type v) := r • t
    change sectionMap f U s rt = r • sectionMap f U s t
    apply sections_eq_of_equal_stalks (moduleSetSheaf H) U
    intro x
    rcases h x.1 with ⟨p, g, hg⟩
    have hGsmul := hmodule_germ_smul G r t x
    rw [hmodule_germ G (r • t) x, hmodule_germ G t x] at hGsmul
    apply (moduleStalkUnderlyingEquiv H x.1).symm.injective
    rw [hsection_value x p g hg s rt]
    rw [hmodule_germ_smul H r (sectionMap f U s t) x]
    rw [hsection_value x p g hg s t]
    rw [hGsmul]
    exact g.map_smul_right' _ _ _
  · intro s t
    rfl

/-! ## Ring and module objects -/

/-! Evaluation of an internal map on generalized elements. -/
def internalBilinearValue {C : Type v} [Category.{v} C]
    [CartesianMonoidalCategory C] [BraidedCategory C] {A B D : C}
    (f : A ⊗ B ⟶ D) {Z : C} (a : Z ⟶ A) (b : Z ⟶ B) : Z ⟶ D :=
  CartesianMonoidalCategory.lift a b ≫ f

/-! Bilinearity in an arbitrary Cartesian monoidal category. -/
structure InternalBilinearMap {C : Type v} [Category.{v} C]
    [CartesianMonoidalCategory C] [BraidedCategory C]
    (R : C) [RingObj R]
    (F G H : C) [AddGrpObj F] [AddModObj R F] [ModObj R F]
    [AddGrpObj G] [AddModObj R G] [ModObj R G]
    [AddGrpObj H] [AddModObj R H] [ModObj R H] where
  toHom : F ⊗ G ⟶ H
  map_add_left : ∀ {Z : C} (a₁ a₂ : Z ⟶ F) (b : Z ⟶ G),
    internalBilinearValue toHom (a₁ + a₂) b =
      internalBilinearValue toHom a₁ b + internalBilinearValue toHom a₂ b
  map_smul_left : ∀ {Z : C} (r : Z ⟶ R) (a : Z ⟶ F) (b : Z ⟶ G),
    internalBilinearValue toHom (r • a) b =
      r • internalBilinearValue toHom a b
  map_add_right : ∀ {Z : C} (a : Z ⟶ F) (b₁ b₂ : Z ⟶ G),
    internalBilinearValue toHom a (b₁ + b₂) =
      internalBilinearValue toHom a b₁ + internalBilinearValue toHom a b₂
  map_smul_right : ∀ {Z : C} (r : Z ⟶ R) (a : Z ⟶ F) (b : Z ⟶ G),
    internalBilinearValue toHom a (r • b) =
      r • internalBilinearValue toHom a b

/-! The categorical version of the Hom-set characterization. -/
def IsInternalHomRuleBilinear {C : Type v} [Category.{v} C]
    [CartesianMonoidalCategory C] [BraidedCategory C]
    (R : C) [RingObj R]
    (F G H : C) [AddGrpObj F] [AddModObj R F] [ModObj R F]
    [AddGrpObj G] [AddModObj R G] [ModObj R G]
    [AddGrpObj H] [AddModObj R H] [ModObj R H]
    (f : F ⊗ G ⟶ H) : Prop :=
  ∀ (S : C),
    (∀ (a₁ a₂ : S ⟶ F) (b : S ⟶ G),
      internalBilinearValue f (a₁ + a₂) b =
        internalBilinearValue f a₁ b + internalBilinearValue f a₂ b) ∧
    (∀ (r : S ⟶ R) (a : S ⟶ F) (b : S ⟶ G),
      internalBilinearValue f (r • a) b =
        r • internalBilinearValue f a b) ∧
    (∀ (a : S ⟶ F) (b₁ b₂ : S ⟶ G),
      internalBilinearValue f a (b₁ + b₂) =
        internalBilinearValue f a b₁ + internalBilinearValue f a b₂) ∧
    (∀ (r : S ⟶ R) (a : S ⟶ F) (b : S ⟶ G),
      internalBilinearValue f a (r • b) =
        r • internalBilinearValue f a b)

theorem internalBilinearMap_isInternalHomRuleBilinear {C : Type v}
    [Category.{v} C] [CartesianMonoidalCategory C] [BraidedCategory C]
    (R : C) [RingObj R]
    (F G H : C) [AddGrpObj F] [AddModObj R F] [ModObj R F]
    [AddGrpObj G] [AddModObj R G] [ModObj R G]
    [AddGrpObj H] [AddModObj R H] [ModObj R H]
    (f : InternalBilinearMap R F G H) :
    IsInternalHomRuleBilinear R F G H f.toHom := by
  intro S
  exact ⟨f.map_add_left, f.map_smul_left, f.map_add_right, f.map_smul_right⟩

/-! A bilinear map of sheaves of modules. -/
structure SheafBilinearMap {X : TopCat.{v}}
    {O : RingSheaf.{v, v} X} (F G H : Mod O) where
  toSetMap : ModuleSetMap F G H
  isSectionwiseBilinear : IsSectionwiseBilinear toSetMap

/-! Source-facing aliases over the canonical ringed-space structure. -/
abbrev RingedSpaceBilinearMap {X : RingedSpace.{v}}
    (F G H : Mod X.structureSheaf) :=
  SheafBilinearMap F G H

abbrev BilinearMap {X : RingedSpace.{v}}
    (F G H : Mod X.structureSheaf) :=
  RingedSpaceBilinearMap F G H

namespace SheafBilinearMap

instance {X : TopCat.{v}} {O : RingSheaf.{v, v} X}
    {F G H : Mod O} : Coe (SheafBilinearMap F G H) (ModuleSetMap F G H) :=
  ⟨SheafBilinearMap.toSetMap⟩

/-! The displayed addition axiom in the first variable. -/
theorem map_add_left {X : TopCat.{v}} {O : RingSheaf.{v, v} X}
    {F G H : Mod O} (f : SheafBilinearMap F G H) (U : Opens X)
    (x y : (F.val.obj (op U) : Type v))
    (z : (G.val.obj (op U) : Type v)) :
    sectionMap f.toSetMap U (x + y) z =
      sectionMap f.toSetMap U x z + sectionMap f.toSetMap U y z := by
  rcases f.isSectionwiseBilinear U with ⟨g, hg⟩
  rw [← hg, ← hg, ← hg, g.map_add_left']

end SheafBilinearMap

end

end Formalization.Books.Modules.Unit15
