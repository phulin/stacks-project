import Formalization.Books.Sheaves.Unit22.RingedSpaces
import Formalization.Books.Sheaves.Unit15.AlgebraicStructures
import Formalization.Books.Sheaves.Unit16.ExactnessAndPoints
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

/-! A pointwise Hom-set formulation of bilinearity.  The bracketed
structures are the pointwise ring and module structures on the Hom sets. -/
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

/-! The source's Hom-set characterization, quantified over all sheaves of
sets and all explicit pointwise ring/module structures on the Hom types. -/
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

theorem isSectionwiseBilinear_iff_isHomCharacterization
    {X : TopCat.{v}} {O : RingSheaf.{v, v} X} {F G H : Mod O}
    (f : ModuleSetMap F G H) :
    IsSectionwiseBilinear f ↔ IsHomCharacterization f := by
  sorry

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
  letI : PreservesFiniteLimits
      (colim : ((OpenNhds x)ᵒᵖ ⥤ Type v) ⥤ Type v) := by infer_instance
  letI : PreservesFiniteLimits
      ((Functor.whiskeringLeft (OpenNhds x)ᵒᵖ (Opens X)ᵒᵖ (Type v)).obj
        (OpenNhds.inclusion x).op) := by infer_instance
  letI : PreservesFiniteLimits (TopCat.Presheaf.stalkFunctor (Type v) x) := by
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
    change (e₄ (e₃.hom (e.hom q))) j =
      (TopCat.Presheaf.stalkFunctor (Type v) x).map
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
        simpa [e₁', Function.comp_def] using h₁
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
        simpa [e₁] using h₀
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
      convert h₀map using 1 <;>
        simp [Functor.map_comp, Discrete.compNatIsoDiscrete,
          Discrete.natIso, NatIso.ofComponents, Category.assoc, hforget] <;>
        try rfl
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
  change (TopCat.Presheaf.stalkFunctor (Type v) x.1).map
      (limit.π (pair (moduleSetSheaf F) (moduleSetSheaf G))
        (Discrete.mk WalkingPair.left)).hom
      (TopCat.Presheaf.germ (moduleSetProduct F G).presheaf U x.1 x.2
        ((sheafProductSectionsEquiv (moduleSetSheaf F) (moduleSetSheaf G) U).symm
          (s, t))) = _
  rw [TopCat.Presheaf.stalkFunctor_map_germ_apply]
  rw [test_product_sections_first F G U s t]

/-! The stalkwise characterization from the source. -/
theorem isSectionwiseBilinear_of_isStalkwiseBilinear {X : TopCat.{v}}
    {O : RingSheaf.{v, v} X} {F G H : Mod O}
    (f : ModuleSetMap F G H) (h : IsStalkwiseBilinear f) :
    IsSectionwiseBilinear f := by
  sorry

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
