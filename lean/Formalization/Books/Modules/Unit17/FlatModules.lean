import Formalization.Books.Modules.Unit16.TensorProduct
import Formalization.Books.Categories.Unit23.ExactFunctors
import Formalization.Books.Sheaves.Unit31.Infrastructure
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.RingTheory.Flat.Basic

/-!
# Sheaves of Modules, Chapter 17: Flat modules

The source section is `books/modules.tex:2527--2804`. Chapter 16 supplies
the sheaf tensor product used here. As in that chapter, the formal sheaf of
rings is a `CommRingSheaf`, the canonical Mathlib model in which the tensor
product of two sheaves of modules is defined.
-/

namespace Formalization.Books.Modules.Unit17

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Formalization.Books.Categories.Unit23
open Formalization.Books.Modules.Unit03
open Formalization.Books.Modules.Unit16
open Formalization.Books.Sheaves.Unit10
open Formalization.Books.Sheaves.Unit17
open Formalization.Books.Sheaves.Unit24
open Formalization.Books.Sheaves.Unit22
open scoped ZeroObject

universe v

noncomputable section

/-! ## Definition `definition-flat` -/

/- The source writes `G ↦ G ⊗ F`. The existing Chapter 16 functor is the
   left-tensor convention, so this chapter exposes the right-tensor convention
   explicitly and uses it in the definition below. -/

/-- Tensoring on the right by a fixed sheaf of modules. -/
noncomputable def tensorRightFunctor {X : TopCat.{v}}
    (O : CommRingSheaf X) (F : CommRingSheafModule O) :
    CommRingSheafModule O ⥤ CommRingSheafModule O where
  obj G := tensorProductSheaf O G F
  map f := tensorProductMap f (𝟙 F)
  map_id G := by
    exact tensorProductMap_id
  map_comp f g := by
    exact tensorProductMap_comp f g (𝟙 F) (𝟙 F)

/-- A sheaf of modules is flat when tensoring on the right by it is exact. -/
def IsFlat {X : TopCat.{v}} (O : CommRingSheaf X)
    (F : CommRingSheafModule O) : Prop :=
  IsExact (tensorRightFunctor O F)

/-! ## Lemma `lemma-flat-stalks-flat` and definition `definition-flat-at-point` -/

/-- The stalk module used in the pointwise flatness statements. -/
noncomputable abbrev moduleStalk {X : TopCat.{v}} {O : CommRingSheaf X}
    (F : CommRingSheafModule O) (x : X) :
    ModuleCat (TopCat.Presheaf.stalk (C := CommRingCat) O.obj x) :=
  commRingSheafModuleStalk F x

/-- Flatness of a sheaf at a point, expressed by flatness of its stalk. -/
def IsFlatAt {X : TopCat.{v}} (O : CommRingSheaf X)
    (F : CommRingSheafModule O) (x : X) : Prop :=
  Module.Flat (TopCat.Presheaf.stalk (C := CommRingCat) O.obj x)
    (moduleStalk F x : Type v)

/-- Sheaf flatness is equivalent to flatness of every stalk. -/
theorem isFlat_iff_isFlatAt {X : TopCat.{v}} {O : CommRingSheaf X}
    (F : CommRingSheafModule O) :
    IsFlat O F ↔ ∀ x : X, IsFlatAt O F x := by
  sorry

/-! ## Lemma `lemma-base-change-flat` -/

/-- Pullback of a flat module along a morphism of commutative ringed spaces is
flat. The scalar map and the right-adjoint hypothesis are the canonical
Chapter 16 pullback data. -/
theorem pullback_isFlat
    {X Y : TopCat.{v}} {OX : CommRingSheaf X} {OY : CommRingSheaf Y}
    (f : X ⟶ Y)
    (α : commRingSheafToRingSheaf OY ⟶
      (sheafRingPushforward f).obj (commRingSheafToRingSheaf OX))
    [((SheafOfModules.pushforward (F := Opens.map f) α).IsRightAdjoint)]
    {G : CommRingSheafModule OY} (hG : IsFlat OY G) :
    IsFlat OX ((pullbackModule f α).obj G) := by
  sorry

/-! ## Lemma `lemma-colimits-flat` -/

/-- Filtered colimits of flat sheaves of modules are flat. -/
theorem filteredColimit_isFlat
    {X : TopCat.{v}} {O : CommRingSheaf X}
    {J : Type v} [Category.{v} J] [IsFiltered J]
    (D : J ⥤ CommRingSheafModule O)
    (hD : ∀ j, IsFlat O (D.obj j)) :
    IsFlat O (colimit D) := by
  sorry

/-- Direct sums of flat sheaves of modules are flat. -/
theorem directSum_isFlat
    {X : TopCat.{v}} {O : CommRingSheaf X} {I : Type v}
    (F : I → CommRingSheafModule O)
    (hF : ∀ i, IsFlat O (F i)) :
    IsFlat O (directSum F) := by
  sorry

/-! ## Lemma `lemma-j-shriek-flat` -/

/- The open-extension construction in the earlier sheaf chapters is stated
   for the project's `RingedSpace`/`Mod` model. We retain that canonical
   construction here and state its stalkwise flatness consequence explicitly;
   `isFlat_iff_isFlatAt` is the commutative-ring sheaf version of the same
   source characterization. -/

/-- Stalkwise flatness for the project's ringed-space module model. -/
def openExtensionUnit {X : TopCat.{v}} (O : CommRingSheaf X)
    (U : Opens X) : CommRingSheafModule O :=
  (openModuleExtensionFunctor (underlyingRingedSpace O) U).obj
    (SheafOfModules.unit (ringedOpenSubspace (underlyingRingedSpace O) U).structureSheaf)

/-- The extension by zero of the unit sheaf on an open subspace is flat. -/
theorem openExtensionUnit_isFlat
    {X : TopCat.{v}} (O : CommRingSheaf X) (U : Opens X) :
    IsFlat O (openExtensionUnit O U) := by
  sorry

/-! ## Lemma `lemma-module-quotient-flat` -/

/-- Every sheaf of modules is an epimorphic quotient of a direct sum of
extension-by-zero copies of the structure sheaf. -/
theorem exists_epi_from_openExtensionUnits
    {X : TopCat.{v}} (O : CommRingSheaf X) (F : CommRingSheafModule O) :
    ∃ (I : Type v) (U : I → Opens X)
      (q : sheafModuleCoproduct (commRingSheafToRingSheaf O)
        (fun i => openExtensionUnit O (U i)) ⟶ F), Epi q := by
  sorry

/-- Every sheaf of modules is an epimorphic quotient of a stalkwise-flat
module. -/
theorem exists_epi_from_isFlat
    {X : TopCat.{v}} (O : CommRingSheaf X) (F : CommRingSheafModule O) :
    ∃ P : CommRingSheafModule O, ∃ q : P ⟶ F, Epi q ∧ IsFlat O P := by
  sorry

/-! ## Lemma `lemma-flat-tor-zero` -/

noncomputable instance tensorRightFunctor_preservesZeroMorphisms
    {X : TopCat.{v}} {O : CommRingSheaf X}
    (F : CommRingSheafModule O) :
    (tensorRightFunctor O F).PreservesZeroMorphisms := by
  sorry

/-- Tensoring a short exact sequence by a flat sheaf remains short exact. -/
theorem shortExact_tensor_isShortExact
    {X : TopCat.{v}} {O : CommRingSheaf X}
    {S : ShortComplex (CommRingSheafModule O)} (hS : S.ShortExact)
    {G : CommRingSheafModule O} (hG : IsFlat O G) :
    (S.map (tensorRightFunctor O G)).ShortExact := by
  sorry

/-! ## Lemma `lemma-flat-ses` -/

/-- In a short exact sequence, flatness of the ends implies flatness of the
middle term. -/
theorem isFlat_middle_of_isFlat_left_of_isFlat_right
    {X : TopCat.{v}} {O : CommRingSheaf X}
    {S : ShortComplex (CommRingSheafModule O)} (hS : S.ShortExact)
    (h₁ : IsFlat O S.X₁) (h₃ : IsFlat O S.X₃) :
    IsFlat O S.X₂ := by
  sorry

/-- In a short exact sequence, flatness of the middle and right terms implies
flatness of the left term. -/
theorem isFlat_left_of_isFlat_middle_of_isFlat_right
    {X : TopCat.{v}} {O : CommRingSheaf X}
    {S : ShortComplex (CommRingSheafModule O)} (hS : S.ShortExact)
    (h₂ : IsFlat O S.X₂) (h₃ : IsFlat O S.X₃) :
    IsFlat O S.X₁ := by
  sorry

/-! ## Lemma `lemma-flat-resolution-of-flat` -/

/-- An exact augmented complex written in the source's one-sided resolution
form. The fields record exactness at the augmentation and at every positive
term. -/
structure FlatResolution {X : TopCat.{v}} (O : CommRingSheaf X)
    (Q : CommRingSheafModule O) where
  term : ℕ → CommRingSheafModule O
  differential : ∀ i, term (i + 1) ⟶ term i
  augmentation : term 0 ⟶ Q
  differential_comp : ∀ i,
    differential (i + 1) ≫ differential i = 0
  differential_augmentation : differential 0 ≫ augmentation = 0
  exact_at_zero :
    (ShortComplex.mk (differential 0) augmentation differential_augmentation).Exact
  exact_at_succ : ∀ i,
    (ShortComplex.mk (differential (i + 1)) (differential i)
      (differential_comp i)).Exact

abbrev FlatResolution.zeroComplex {X : TopCat.{v}} {O : CommRingSheaf X}
    {Q : CommRingSheafModule O} (R : FlatResolution O Q) :
    ShortComplex (CommRingSheafModule O) :=
  ShortComplex.mk (R.differential 0) R.augmentation R.differential_augmentation

abbrev FlatResolution.succComplex {X : TopCat.{v}} {O : CommRingSheaf X}
    {Q : CommRingSheafModule O} (R : FlatResolution O Q) (i : ℕ) :
    ShortComplex (CommRingSheafModule O) :=
  ShortComplex.mk (R.differential (i + 1)) (R.differential i)
    (R.differential_comp i)

/-- Exactness of the resolution after tensoring by an arbitrary sheaf. -/
def TensoredResolutionExact {X : TopCat.{v}} {O : CommRingSheaf X}
    {Q : CommRingSheafModule O} (R : FlatResolution O Q)
    (G : CommRingSheafModule O) : Prop :=
  (R.zeroComplex.map (tensorRightFunctor O G)).Exact ∧
    ∀ i, (R.succComplex i).map (tensorRightFunctor O G) |>.Exact

/-- A flat resolution of a flat module remains exact after tensoring with any
module. -/
theorem flatResolution_tensor_exact
    {X : TopCat.{v}} {O : CommRingSheaf X}
    {Q : CommRingSheafModule O} (R : FlatResolution O Q)
    (hQ : IsFlat O Q) (hF : ∀ i, IsFlat O (R.term i))
    (G : CommRingSheafModule O) :
    TensoredResolutionExact R G := by
  sorry

/-! ## Lemma `lemma-flat-eq` -/

/-- The ringed space carried by a commutative sheaf of rings, restricted to an
open. -/
noncomputable abbrev openRingedSpace {X : TopCat.{v}} (O : CommRingSheaf X)
    (U : Opens X) : RingedSpace :=
  ringedOpenSubspace (underlyingRingedSpace O) U

/-- The restriction of a module to an open. -/
noncomputable abbrev restrictedModule {X : TopCat.{v}} (O : CommRingSheaf X)
    (F : CommRingSheafModule O) (U : Opens X) :
    Mod (openRingedSpace O U).structureSheaf :=
  (openModuleRestrictionFunctor (underlyingRingedSpace O) U).obj F

/-- The finite direct sum of copies of the unit sheaf. -/
noncomputable def finiteFreeModule (Y : RingedSpace.{v}) (n : ℕ) :
    Mod Y.structureSheaf := by
  let F : ULift.{v} (Fin n) → Mod Y.structureSheaf :=
    fun _ => SheafOfModules.unit Y.structureSheaf
  exact sheafModuleCoproduct Y.structureSheaf F

/-- The local data in the equational criterion: a complex from the unit sheaf
to a finite free module and then to the restricted module. -/
structure LocalEquationalCriterionData {X : TopCat.{v}}
    (O : CommRingSheaf X) (F : CommRingSheafModule O) (U : Opens X) where
  n : ℕ
  sourceMap :
    (SheafOfModules.unit (openRingedSpace O U).structureSheaf :
      Mod (openRingedSpace O U).structureSheaf) ⟶
      finiteFreeModule (openRingedSpace O U) n
  targetMap : finiteFreeModule (openRingedSpace O U) n ⟶
    restrictedModule O F U
  complex : sourceMap ≫ targetMap = 0

/-- The explicit local factorization property for the preceding complex. -/
def LocalEquationalFactorization {X : TopCat.{v}}
    {O : CommRingSheaf X} {F : CommRingSheafModule O} {U : Opens X}
    (data : LocalEquationalCriterionData O F U) : Prop :=
  ∀ x : openRingedSpace O U, ∃ V : Opens (openRingedSpace O U).carrier,
    x ∈ V ∧ ∃ m : ℕ,
      ∃ A : (openModuleRestrictionFunctor (openRingedSpace O U) V).obj
          (finiteFreeModule (openRingedSpace O U) data.n) ⟶
        finiteFreeModule
          (ringedOpenSubspace (openRingedSpace O U) V) m,
      ∃ t : finiteFreeModule
          (ringedOpenSubspace (openRingedSpace O U) V) m ⟶
        (openModuleRestrictionFunctor (openRingedSpace O U) V).obj
          (restrictedModule O F U),
        (openModuleRestrictionFunctor (openRingedSpace O U) V).map data.sourceMap ≫ A = 0 ∧
          (openModuleRestrictionFunctor (openRingedSpace O U) V).map data.targetMap = A ≫ t

/-- A flat module satisfies the local equational factorization criterion. -/
theorem flat_local_equational_criterion
    {X : TopCat.{v}} (O : CommRingSheaf X) (F : CommRingSheafModule O)
    (hF : IsFlat O F) (U : Opens X)
    (data : LocalEquationalCriterionData O F U) :
    LocalEquationalFactorization data := by
  sorry

end

end Formalization.Books.Modules.Unit17
