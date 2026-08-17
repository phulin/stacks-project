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
  sorry

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
  sorry

end SheafBilinearMap

end

end Formalization.Books.Modules.Unit15
