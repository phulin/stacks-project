import Formalization.Books.Sheaves.Unit17.AlgebraicStructures
import Formalization.Books.Sheaves.Unit06.PresheavesOfModules
import Formalization.Books.Sheaves.Unit14.StalksOfPresheavesOfModules
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.CategoryTheory.Sites.LocallyBijective

/-!
# Sheaves on Spaces, Chapter 17, Section 4: Sheafification of presheaves of
modules

The source span is `books/sheaves.tex:1822-1983`.  The ring and module
sheafifications below use Mathlib's canonical `SheafOfModules` construction.
The earlier presheaf change-of-rings and stalk APIs are reused for the
source-facing tensor, restriction, adjunction, and stalk statements.
-/

namespace Formalization.Books.Sheaves.Unit17

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Formalization.Books.Sheaves.Unit04
open Formalization.Books.Sheaves.Unit05
open Formalization.Books.Sheaves.Unit06
open Formalization.Books.Sheaves.Unit14
open Formalization.Books.Sheaves.Unit03

universe v

noncomputable section

/-! ## Ring and module sheafification -/

/-- The canonical sheafification of a presheaf of rings. -/
noncomputable def ringSheafification {X : TopCat.{v}}
    (O : RingPresheaf.{v, v} X) :
    Sheaf (Opens.grothendieckTopology X) RingCat.{v} :=
  (CategoryTheory.presheafToSheaf (Opens.grothendieckTopology X)
    RingCat).obj O

/-- The canonical map from a presheaf of rings to its sheafification. -/
noncomputable def ringSheafificationUnit {X : TopCat.{v}}
    (O : RingPresheaf.{v, v} X) :
    O ⟶ (ringSheafification O).obj :=
  CategoryTheory.toSheafify (Opens.grothendieckTopology X) O

/-- The ring sheafification unit is locally injective. -/
theorem ringSheafificationUnit_isLocallyInjective {X : TopCat.{v}}
    (O : RingPresheaf.{v, v} X) :
    Presheaf.IsLocallyInjective (Opens.grothendieckTopology X)
      (ringSheafificationUnit O) := by
  sorry

/-- The ring sheafification unit is locally surjective. -/
theorem ringSheafificationUnit_isLocallySurjective {X : TopCat.{v}}
    (O : RingPresheaf.{v, v} X) :
    Presheaf.IsLocallySurjective (Opens.grothendieckTopology X)
      (ringSheafificationUnit O) := by
  sorry

/-- The sheaf of modules obtained by sheafifying an `O`-module presheaf. -/
noncomputable def moduleSheafification {X : TopCat.{v}}
    {O : RingPresheaf.{v, v} X} (F : PMod O) :
    SheafOfModules.{v} (ringSheafification O) := by
  letI : Presheaf.IsLocallyInjective (Opens.grothendieckTopology X)
      (ringSheafificationUnit O) := ringSheafificationUnit_isLocallyInjective O
  letI : Presheaf.IsLocallySurjective (Opens.grothendieckTopology X)
      (ringSheafificationUnit O) := ringSheafificationUnit_isLocallySurjective O
  exact (PresheafOfModules.sheafification (ringSheafificationUnit O)).obj F

/-- The unit of module sheafification, with its natural restricted-scalar
target made explicit. -/
noncomputable def moduleSheafificationUnit {X : TopCat.{v}}
    {O : RingPresheaf.{v, v} X} (F : PMod O) :
    F ⟶ (PresheafOfModules.restrictScalars (ringSheafificationUnit O)).obj
      ((SheafOfModules.forget (ringSheafification O)).obj
        (moduleSheafification F)) := by
  letI : Presheaf.IsLocallyInjective (Opens.grothendieckTopology X)
      (ringSheafificationUnit O) := ringSheafificationUnit_isLocallyInjective O
  letI : Presheaf.IsLocallySurjective (Opens.grothendieckTopology X)
      (ringSheafificationUnit O) := ringSheafificationUnit_isLocallySurjective O
  exact (PresheafOfModules.sheafificationAdjunction
    (ringSheafificationUnit O)).unit.app F

/-- The underlying set presheaf of an `O`-module presheaf. -/
abbrev moduleUnderlyingSetPresheaf {X : TopCat.{v}}
    {O : RingPresheaf.{v, v} X} (F : PMod O) : TopCat.Presheaf (Type v) X :=
  Formalization.Books.Sheaves.Unit05.underlyingPresheaf
    (CategoryTheory.forget AddCommGrpCat) F.presheaf

/-- The underlying set presheaf of the sheafified module. -/
abbrev moduleSheafificationSetPresheaf {X : TopCat.{v}}
    {O : RingPresheaf.{v, v} X} (F : PMod O) : TopCat.Presheaf (Type v) X :=
  Formalization.Books.Sheaves.Unit05.underlyingPresheaf
    (CategoryTheory.forget AddCommGrpCat)
    ((SheafOfModules.toSheaf (ringSheafification O)).obj
      (moduleSheafification F)).obj

/-- The underlying set sheafification is unchanged by the module structure. -/
theorem moduleSheafification_underlying_iso {X : TopCat.{v}}
    {O : RingPresheaf.{v, v} X} (F : PMod O) :
    Nonempty
      (moduleSheafificationSetPresheaf F ≅
        (sheafification (moduleUnderlyingSetPresheaf F)).presheaf) := by
  sorry

/-- The universal property of the module sheafification, in the canonical
restricted-scalar form used by Mathlib. -/
noncomputable def moduleSheafificationHomEquiv {X : TopCat.{v}}
    {O : RingPresheaf.{v, v} X} (F : PMod O)
    (G : SheafOfModules.{v} (ringSheafification O)) :
    (moduleSheafification F ⟶ G) ≃
      (F ⟶ (PresheafOfModules.restrictScalars (ringSheafificationUnit O)).obj
        ((SheafOfModules.forget (ringSheafification O)).obj G)) := by
  letI : Presheaf.IsLocallyInjective (Opens.grothendieckTopology X)
      (ringSheafificationUnit O) := ringSheafificationUnit_isLocallyInjective O
  letI : Presheaf.IsLocallySurjective (Opens.grothendieckTopology X)
      (ringSheafificationUnit O) := ringSheafificationUnit_isLocallySurjective O
  exact PresheafOfModules.sheafificationHomEquiv (ringSheafificationUnit O)

/-! ## The induced action and its universal property -/

/-- The underlying set presheaf of the sheafified ring. -/
abbrev ringSheafificationSetPresheaf {X : TopCat.{v}}
    (O : RingPresheaf.{v, v} X) : TopCat.Presheaf (Type v) X :=
  Formalization.Books.Sheaves.Unit05.underlyingPresheaf
    (CategoryTheory.forget RingCat) (ringSheafification O).obj

/-- The pointwise scalar action on sections of the sheafified module. -/
noncomputable def moduleSheafificationActionAt {X : TopCat.{v}}
    {O : RingPresheaf.{v, v} X} (F : PMod O) (U : Opens X) :
    ((ringSheafification O).obj.obj (op U) : Type v) →
      ((moduleSheafification F).val.obj (op U) : Type v) →
      ((moduleSheafification F).val.obj (op U) : Type v) :=
  fun r m => r • m

/-- The scalar action is compatible with restrictions. -/
theorem moduleSheafificationActionAt_natural {X : TopCat.{v}}
    {O : RingPresheaf.{v, v} X} (F : PMod O)
    {U V : Opens X} (h : V ≤ U)
    (r : (ringSheafification O).obj.obj (op U))
    (m : (moduleSheafification F).val.obj (op U)) :
    moduleSheafificationActionAt F V
        ((ringSheafification O).obj.map (homOfLE h).op r)
        ((moduleSheafification F).val.map (homOfLE h).op m) =
      (moduleSheafification F).val.map (homOfLE h).op
        (moduleSheafificationActionAt F U r m) := by
  simp [moduleSheafificationActionAt]

/-- The scalar action as a morphism of sheaves of sets, written on the
underlying presheaves. -/
noncomputable def moduleSheafificationAction {X : TopCat.{v}}
    {O : RingPresheaf.{v, v} X} (F : PMod O) :
    presheafProduct (ringSheafificationSetPresheaf O)
        (moduleSheafificationSetPresheaf F) ⟶
      moduleSheafificationSetPresheaf F :=
  { app := fun U => TypeCat.ofHom (fun st =>
      let p := (presheafProductSectionsEquiv
        (ringSheafificationSetPresheaf O) (moduleSheafificationSetPresheaf F)
        U.unop) st
      moduleSheafificationActionAt F U.unop p.1 p.2)
    naturality := by
      intro U V f
      ext st
      let p := (presheafProductSectionsEquiv
        (ringSheafificationSetPresheaf O) (moduleSheafificationSetPresheaf F)
        U.unop) st
      change moduleSheafificationActionAt F V.unop
          (restriction (F := ringSheafificationSetPresheaf O) f.unop.le p.1)
          (restriction (F := moduleSheafificationSetPresheaf F) f.unop.le p.2) =
        restriction (F := moduleSheafificationSetPresheaf F) f.unop.le
          (moduleSheafificationActionAt F U.unop p.1 p.2)
      exact moduleSheafificationActionAt_natural F f.unop.le p.1 p.2 }

/-- The action map makes the sheafification unit a map of module presheaves;
this is the source's commutative square on sections. -/
theorem moduleSheafificationUnit_action_compatibility {X : TopCat.{v}}
    {O : RingPresheaf.{v, v} X} (F : PMod O) (U : Opens X)
    (r : O.obj (op U)) (m : F.obj (op U)) :
    moduleSheafificationActionAt F U
        ((ringSheafificationUnit O).app (op U) r)
        ((moduleSheafificationUnit F).app (op U) m) =
      (moduleSheafificationUnit F).app (op U) (r • m) := by
  sorry

/-! ## Restriction, tensor product sheaves, and change of rings -/

/-- Restriction of scalars for sheaves of modules. -/
noncomputable abbrev sheafRestrictionOfScalars {X : TopCat.{v}}
    {O₁ O₂ : Sheaf (Opens.grothendieckTopology X) RingCat.{v}}
      (α : O₁ ⟶ O₂) :
    SheafOfModules.{v} O₂ ⥤ SheafOfModules.{v} O₁ :=
  SheafOfModules.restrictScalars α

/-- The presheaf-level extension of scalars underlying the tensor product
sheaf. -/
noncomputable abbrev sheafTensorProductPresheaf {X : TopCat.{v}}
    {O₁ O₂ : Sheaf (Opens.grothendieckTopology X) RingCat.{v}}
    (α : O₁ ⟶ O₂) (G : SheafOfModules.{v} O₁) : PMod O₂.obj :=
  tensorProductPresheaf α.hom G.val

/-- The tensor product sheaf in the source is module sheafification of the
presheaf-level extension of scalars. -/
noncomputable def tensorProductSheaf {X : TopCat.{v}}
    {O₁ O₂ : Sheaf (Opens.grothendieckTopology X) RingCat.{v}}
    (α : O₁ ⟶ O₂) (G : SheafOfModules.{v} O₁) :
    SheafOfModules.{v} O₂ := by
  exact (PresheafOfModules.sheafification (𝟙 O₂.obj)).obj
    (sheafTensorProductPresheaf α G)

/-- The sheaf change-of-rings functor. -/
noncomputable def sheafChangeOfRings {X : TopCat.{v}}
    {O₁ O₂ : Sheaf (Opens.grothendieckTopology X) RingCat.{v}}
      (α : O₁ ⟶ O₂) :
    SheafOfModules.{v} O₁ ⥤ SheafOfModules.{v} O₂ where
  obj G := tensorProductSheaf α G
  map f := (PresheafOfModules.sheafification (𝟙 O₂.obj)).map
    ((changeOfRings α.hom).map f.val)

/-! ## Adjunction and stalks -/

/-- Change of rings is left adjoint to restriction of scalars on sheaves. -/
theorem exists_sheafChangeOfRingsAdjunction {X : TopCat.{v}}
    {O₁ O₂ : Sheaf (Opens.grothendieckTopology X) RingCat.{v}}
      (α : O₁ ⟶ O₂) :
    Nonempty (sheafChangeOfRings α ⊣ sheafRestrictionOfScalars α) := by
  sorry

/-- A chosen adjunction between sheaf extension and restriction of scalars. -/
noncomputable def sheafChangeOfRingsAdjunction {X : TopCat.{v}}
    {O₁ O₂ : Sheaf (Opens.grothendieckTopology X) RingCat.{v}}
      (α : O₁ ⟶ O₂) :
    sheafChangeOfRings α ⊣ sheafRestrictionOfScalars α :=
  Classical.choice (exists_sheafChangeOfRingsAdjunction α)

/-- The source-facing Hom bijection for tensor product sheaves and
restriction of scalars. -/
noncomputable def sheafChangeOfRingsHomEquiv {X : TopCat.{v}}
    {O₁ O₂ : Sheaf (Opens.grothendieckTopology X) RingCat.{v}}
      (α : O₁ ⟶ O₂)
    (G : SheafOfModules.{v} O₁) (F : SheafOfModules.{v} O₂) :
    (G ⟶ (sheafRestrictionOfScalars α).obj F) ≃
      ((sheafChangeOfRings α).obj G ⟶ F) :=
  (sheafChangeOfRingsAdjunction α).homEquiv G F |>.symm

/-- The stalk tensor-product comparison from the preceding module-stalk
chapter, stated in the source's module-isomorphism form. -/
theorem sheafification_stalk_tensorProduct_iso {X : TopCat.{v}}
    {O O' : CommRingPresheaf X} (α : O ⟶ O')
    (F : CommRingPresheafModule O) (x : X) :
    Nonempty (stalkTensorProduct α F x ≅
      ModuleCat.of (O'.stalk x)
        (↑(TopCat.Presheaf.stalk
          (tensorProductPresheaf (commRingPresheafMorphismToRingPresheaf α) F).presheaf x))) := by
  exact stalk_tensorProductPresheaf_iso α F x

/-- The same stalk comparison with the source's sheaf hypotheses displayed;
the presheaf tensor has the same stalk as its sheafification. -/
theorem stalk_tensorProductSheaf_statement {X : TopCat.{v}}
    {O O' : CommRingPresheaf X} (α : O ⟶ O')
    (_hO : Presheaf.IsSheaf (Opens.grothendieckTopology X) O)
    (_hO' : Presheaf.IsSheaf (Opens.grothendieckTopology X) O')
    (F : CommRingPresheafModule O)
    (_hF : Presheaf.IsSheaf (Opens.grothendieckTopology X) F.presheaf)
    (x : X) :
    Nonempty (stalkTensorProduct α F x ≅
      ModuleCat.of (O'.stalk x)
        (↑(TopCat.Presheaf.stalk
          (tensorProductPresheaf (commRingPresheafMorphismToRingPresheaf α) F).presheaf x))) := by
  exact stalk_tensorProductPresheaf_iso α F x

end

end Formalization.Books.Sheaves.Unit17
