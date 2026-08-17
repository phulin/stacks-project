import Formalization.Books.Sheaves.Unit17.Modules

/-!
# Sheaves on Spaces, Chapter 20: Sheafification of presheaves of modules

The source span is `books/sheaves.tex:1822-1983`.  The canonical
sheafification, action, restriction, change-of-rings, and presheaf-stalk
interfaces were established in the earlier module-sheafification API.  This
file gives those declarations their source-section names and adds the
source-facing factorization and sheaf-stalk statements.
-/

namespace Formalization.Books.Sheaves.Unit20

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Formalization.Books.Sheaves.Unit04
open Formalization.Books.Sheaves.Unit06
open Formalization.Books.Sheaves.Unit14

universe v

noncomputable section

/-! ## Sheafification of a presheaf of modules -/

/-- The sheafification of a presheaf of rings. -/
noncomputable abbrev ringSheafification {X : TopCat.{v}}
    (O : RingPresheaf.{v, v} X) :
    Sheaf (Opens.grothendieckTopology X) RingCat.{v} :=
  Formalization.Books.Sheaves.Unit17.ringSheafification O

/-- The canonical map from a presheaf of rings to its sheafification. -/
noncomputable abbrev ringSheafificationUnit {X : TopCat.{v}}
    (O : RingPresheaf.{v, v} X) :
    O ⟶ (ringSheafification O).obj :=
  Formalization.Books.Sheaves.Unit17.ringSheafificationUnit O

/-- The sheafification of a presheaf of modules over `O`. -/
noncomputable abbrev moduleSheafification {X : TopCat.{v}}
    {O : RingPresheaf.{v, v} X} (F : PMod O) :
    SheafOfModules.{v} (ringSheafification O) :=
  Formalization.Books.Sheaves.Unit17.moduleSheafification F

/-- The module-sheafification unit, viewed by restriction of scalars as a map
of presheaves of `O`-modules. -/
noncomputable abbrev moduleSheafificationUnit {X : TopCat.{v}}
    {O : RingPresheaf.{v, v} X} (F : PMod O) :
    F ⟶ (PresheafOfModules.restrictScalars (ringSheafificationUnit O)).obj
      ((SheafOfModules.forget (ringSheafification O)).obj
        (moduleSheafification F)) :=
  Formalization.Books.Sheaves.Unit17.moduleSheafificationUnit F

/-- The underlying set presheaf of a presheaf of modules. -/
noncomputable abbrev moduleUnderlyingSetPresheaf {X : TopCat.{v}}
    {O : RingPresheaf.{v, v} X} (F : PMod O) :
    TopCat.Presheaf (Type v) X :=
  Formalization.Books.Sheaves.Unit17.moduleUnderlyingSetPresheaf F

/-- The underlying set presheaf of the sheafified module. -/
noncomputable abbrev moduleSheafificationSetPresheaf {X : TopCat.{v}}
    {O : RingPresheaf.{v, v} X} (F : PMod O) :
    TopCat.Presheaf (Type v) X :=
  Formalization.Books.Sheaves.Unit17.moduleSheafificationSetPresheaf F

/-- The underlying set presheaf of the module sheafification is isomorphic to
the ordinary set-valued sheafification. -/
theorem moduleSheafification_underlying_iso {X : TopCat.{v}}
    {O : RingPresheaf.{v, v} X} (F : PMod O) :
    Nonempty
      (moduleSheafificationSetPresheaf F ≅
        (Formalization.Books.Sheaves.Unit17.sheafification
          (moduleUnderlyingSetPresheaf F)).presheaf) := by
  exact Formalization.Books.Sheaves.Unit17.moduleSheafification_underlying_iso F

/-- The universal-property bijection for module sheafification. -/
noncomputable abbrev moduleSheafificationHomEquiv {X : TopCat.{v}}
    {O : RingPresheaf.{v, v} X} (F : PMod O)
    (G : SheafOfModules.{v} (ringSheafification O)) :
    (moduleSheafification F ⟶ G) ≃
      (F ⟶ (PresheafOfModules.restrictScalars (ringSheafificationUnit O)).obj
        ((SheafOfModules.forget (ringSheafification O)).obj G)) :=
  Formalization.Books.Sheaves.Unit17.moduleSheafificationHomEquiv F G

/-- The sheafification functor on presheaves of `O`-modules. -/
noncomputable def moduleSheafificationFunctor {X : TopCat.{v}}
    (O : RingPresheaf.{v, v} X) :
    PMod O ⥤ SheafOfModules.{v} (ringSheafification O) := by
  letI : Presheaf.IsLocallyInjective (Opens.grothendieckTopology X)
      (ringSheafificationUnit O) :=
    Formalization.Books.Sheaves.Unit17.ringSheafificationUnit_isLocallyInjective O
  letI : Presheaf.IsLocallySurjective (Opens.grothendieckTopology X)
      (ringSheafificationUnit O) :=
    Formalization.Books.Sheaves.Unit17.ringSheafificationUnit_isLocallySurjective O
  exact PresheafOfModules.sheafification (ringSheafificationUnit O)

/-- The object part of the sheafification functor is the source's `F#`. -/
theorem moduleSheafificationFunctor_obj {X : TopCat.{v}}
    (O : RingPresheaf.{v, v} X) (F : PMod O) :
    (moduleSheafificationFunctor O).obj F = moduleSheafification F := by
  rfl

/-- The functor `i` in the source, combining the forgetful functor with
restriction of scalars along the ring sheafification map. -/
noncomputable def sheafModuleRestriction {X : TopCat.{v}}
    (O : RingPresheaf.{v, v} X) :
    SheafOfModules.{v} (ringSheafification O) ⥤ PMod O :=
  (SheafOfModules.forget (ringSheafification O)) ⋙
    PresheafOfModules.restrictScalars (ringSheafificationUnit O)

/-- The sheafification and restriction functors form the source's
adjunction. -/
noncomputable def moduleSheafificationAdjunction {X : TopCat.{v}}
    (O : RingPresheaf.{v, v} X) :
    moduleSheafificationFunctor O ⊣ sheafModuleRestriction O := by
  letI : Presheaf.IsLocallyInjective (Opens.grothendieckTopology X)
      (ringSheafificationUnit O) :=
    Formalization.Books.Sheaves.Unit17.ringSheafificationUnit_isLocallyInjective O
  letI : Presheaf.IsLocallySurjective (Opens.grothendieckTopology X)
      (ringSheafificationUnit O) :=
    Formalization.Books.Sheaves.Unit17.ringSheafificationUnit_isLocallySurjective O
  exact PresheafOfModules.sheafificationAdjunction (ringSheafificationUnit O)

/-- The source's Hom-set bijection expressing the adjunction between module
sheafification and `sheafModuleRestriction`. -/
noncomputable def moduleSheafificationAdjunctionHomEquiv
    {X : TopCat.{v}} (O : RingPresheaf.{v, v} X) (F : PMod O)
    (G : SheafOfModules.{v} (ringSheafification O)) :
    (F ⟶ (sheafModuleRestriction O).obj G) ≃
      (moduleSheafification F ⟶ G) :=
  (moduleSheafificationHomEquiv F G).symm

/-- A chosen factorization of a presheaf-module morphism through the module
sheafification. -/
noncomputable def moduleSheafificationLift {X : TopCat.{v}}
    {O : RingPresheaf.{v, v} X} {F : PMod O}
    (G : SheafOfModules.{v} (ringSheafification O))
    (φ : F ⟶ (sheafModuleRestriction O).obj G) :
    moduleSheafification F ⟶ G :=
  (moduleSheafificationHomEquiv F G).symm φ

/-- The chosen lift has the required universal-property image. -/
theorem moduleSheafificationLift_spec {X : TopCat.{v}}
    {O : RingPresheaf.{v, v} X} {F : PMod O}
    (G : SheafOfModules.{v} (ringSheafification O))
    (φ : F ⟶ (sheafModuleRestriction O).obj G) :
    moduleSheafificationHomEquiv F G (moduleSheafificationLift G φ) = φ := by
  exact (moduleSheafificationHomEquiv F G).apply_symm_apply φ

/-! The next statement writes the same universal property as the source's
explicit unique factorization through the unit. -/

/-- Every presheaf-module map into a sheaf of `O#`-modules factors uniquely
through the module sheafification by an `O#`-linear map. -/
theorem existsUnique_moduleSheafificationFactorization {X : TopCat.{v}}
    {O : RingPresheaf.{v, v} X} {F : PMod O}
    (G : SheafOfModules.{v} (ringSheafification O))
    (φ : F ⟶ (sheafModuleRestriction O).obj G) :
    ∃! ψ : moduleSheafification F ⟶ G,
      moduleSheafificationUnit F ≫
          (PresheafOfModules.restrictScalars (ringSheafificationUnit O)).map ψ.val =
        φ := by
  sorry

/-! ## The induced action -/

/-- The underlying set presheaf of the sheafified ring. -/
noncomputable abbrev ringSheafificationSetPresheaf {X : TopCat.{v}}
    (O : RingPresheaf.{v, v} X) : TopCat.Presheaf (Type v) X :=
  Formalization.Books.Sheaves.Unit17.ringSheafificationSetPresheaf O

/-- The scalar action on sections of the sheafified module. -/
noncomputable abbrev moduleSheafificationActionAt {X : TopCat.{v}}
    {O : RingPresheaf.{v, v} X} (F : PMod O) (U : Opens X) :=
  Formalization.Books.Sheaves.Unit17.moduleSheafificationActionAt F U

/-- The scalar action is compatible with restriction maps. -/
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
  exact Formalization.Books.Sheaves.Unit17.moduleSheafificationActionAt_natural
    F h r m

/-- The action as a morphism of presheaves of sets on the underlying sheaves. -/
noncomputable abbrev moduleSheafificationAction {X : TopCat.{v}}
    {O : RingPresheaf.{v, v} X} (F : PMod O) :
    presheafProduct (ringSheafificationSetPresheaf O)
        (moduleSheafificationSetPresheaf F) ⟶
      moduleSheafificationSetPresheaf F :=
  Formalization.Books.Sheaves.Unit17.moduleSheafificationAction F

/-- The underlying set sheaf of the sheafified module. -/
noncomputable abbrev moduleSheafificationSetSheaf {X : TopCat.{v}}
    {O : RingPresheaf.{v, v} X} (F : PMod O) :
    TopCat.Sheaf (Type v) X :=
  Formalization.Books.Sheaves.Unit17.moduleSheafificationSetSheaf F

/-- The presheaf product carrying the scalar action is a sheaf. -/
theorem moduleSheafificationActionDomain_isSheaf {X : TopCat.{v}}
    {O : RingPresheaf.{v, v} X} (F : PMod O) :
    TopCat.Presheaf.IsSheaf (presheafProduct
      (ringSheafificationSetPresheaf O)
      (moduleSheafificationSetPresheaf F)) := by
  exact Formalization.Books.Sheaves.Unit17.moduleSheafificationActionDomain_isSheaf F

/-- The scalar action as an actual morphism of sheaves of sets.  The displayed
domain is the sheaf carried by the product of the two underlying presheaves. -/
noncomputable abbrev moduleSheafificationActionSheaf {X : TopCat.{v}}
    {O : RingPresheaf.{v, v} X} (F : PMod O) :
    (⟨presheafProduct (ringSheafificationSetPresheaf O)
        (moduleSheafificationSetPresheaf F),
      moduleSheafificationActionDomain_isSheaf F⟩ : TopCat.Sheaf (Type v) X) ⟶
      moduleSheafificationSetSheaf F :=
  Formalization.Books.Sheaves.Unit17.moduleSheafificationActionSheaf F

/-- The sheafification unit commutes with the induced scalar action. -/
theorem moduleSheafificationUnit_action_compatibility {X : TopCat.{v}}
    {O : RingPresheaf.{v, v} X} (F : PMod O) (U : Opens X)
    (r : O.obj (op U)) (m : F.obj (op U)) :
    moduleSheafificationActionAt F U
        ((ringSheafificationUnit O).app (op U) r)
        ((moduleSheafificationUnit F).app (op U) m) =
      (moduleSheafificationUnit F).app (op U) (r • m) := by
  exact Formalization.Books.Sheaves.Unit17.moduleSheafificationUnit_action_compatibility
    F U r m

/-! ## Restriction, tensor product sheaves, and change of rings -/

/-- Restriction of scalars for sheaves of modules. -/
noncomputable abbrev sheafRestrictionOfScalars {X : TopCat.{v}}
    {O₁ O₂ : Sheaf (Opens.grothendieckTopology X) RingCat.{v}}
      (α : O₁ ⟶ O₂) :
    SheafOfModules.{v} O₂ ⥤ SheafOfModules.{v} O₁ :=
  Formalization.Books.Sheaves.Unit17.sheafRestrictionOfScalars α

/-- The presheaf tensor product underlying the source's tensor product sheaf. -/
noncomputable abbrev sheafTensorProductPresheaf {X : TopCat.{v}}
    {O₁ O₂ : Sheaf (Opens.grothendieckTopology X) RingCat.{v}}
    (α : O₁ ⟶ O₂) (G : SheafOfModules.{v} O₁) : PMod O₂.obj :=
  Formalization.Books.Sheaves.Unit17.sheafTensorProductPresheaf α G

/-- The source's warning that the presheaf tensor product need not itself be a
sheaf. -/
theorem tensorProductPresheaf_not_always_isSheaf :
    ¬ ∀ {X : TopCat.{v}}
      {O₁ O₂ : Sheaf (Opens.grothendieckTopology X) RingCat.{v}}
      (α : O₁ ⟶ O₂) (G : SheafOfModules.{v} O₁),
      Presheaf.IsSheaf (Opens.grothendieckTopology X)
        (sheafTensorProductPresheaf α G).presheaf := by
  sorry

/-- The tensor product sheaf, defined by sheafifying the presheaf tensor. -/
noncomputable abbrev tensorProductSheaf {X : TopCat.{v}}
    {O₁ O₂ : Sheaf (Opens.grothendieckTopology X) RingCat.{v}}
    (α : O₁ ⟶ O₂) (G : SheafOfModules.{v} O₁) :
    SheafOfModules.{v} O₂ :=
  Formalization.Books.Sheaves.Unit17.tensorProductSheaf α G

/-- The sheaf-level change-of-rings functor. -/
noncomputable abbrev sheafChangeOfRings {X : TopCat.{v}}
    {O₁ O₂ : Sheaf (Opens.grothendieckTopology X) RingCat.{v}}
      (α : O₁ ⟶ O₂) :
    SheafOfModules.{v} O₁ ⥤ SheafOfModules.{v} O₂ :=
  Formalization.Books.Sheaves.Unit17.sheafChangeOfRings α

/-- Change of rings is left adjoint to restriction of scalars on sheaves. -/
theorem exists_sheafChangeOfRingsAdjunction {X : TopCat.{v}}
    {O₁ O₂ : Sheaf (Opens.grothendieckTopology X) RingCat.{v}}
      (α : O₁ ⟶ O₂) :
    Nonempty (sheafChangeOfRings α ⊣ sheafRestrictionOfScalars α) := by
  exact Formalization.Books.Sheaves.Unit17.exists_sheafChangeOfRingsAdjunction α

/-- A chosen change-of-rings adjunction. -/
noncomputable abbrev sheafChangeOfRingsAdjunction {X : TopCat.{v}}
    {O₁ O₂ : Sheaf (Opens.grothendieckTopology X) RingCat.{v}}
      (α : O₁ ⟶ O₂) :
    sheafChangeOfRings α ⊣ sheafRestrictionOfScalars α :=
  Formalization.Books.Sheaves.Unit17.sheafChangeOfRingsAdjunction α

/-- The canonical Hom bijection for tensor product sheaves and restriction of
scalars. -/
noncomputable abbrev sheafChangeOfRingsHomEquiv {X : TopCat.{v}}
    {O₁ O₂ : Sheaf (Opens.grothendieckTopology X) RingCat.{v}}
      (α : O₁ ⟶ O₂)
    (G : SheafOfModules.{v} O₁) (F : SheafOfModules.{v} O₂) :
    (G ⟶ (sheafRestrictionOfScalars α).obj F) ≃
      ((sheafChangeOfRings α).obj G ⟶ F) :=
  Formalization.Books.Sheaves.Unit17.sheafChangeOfRingsHomEquiv α G F

/-! The presheaf stalk comparison used in the final sheaf-stalk statement. -/

/-- The stalk of the presheaf change of rings is the stalk-level extension of
scalars. -/
theorem sheafification_stalk_tensorProduct_iso
    {X : TopCat.{v}} {O O' : CommRingPresheaf X} (α : O ⟶ O')
    (F : CommRingPresheafModule O) (x : X) :
    Nonempty (stalkTensorProduct α F x ≅
      ModuleCat.of (O'.stalk x)
        (↑(TopCat.Presheaf.stalk
          (tensorProductPresheaf (commRingPresheafMorphismToRingPresheaf α) F).presheaf x))) := by
  exact Formalization.Books.Sheaves.Unit17.sheafification_stalk_tensorProduct_iso α F x

/-! ## Stalks -/

/-- A sheaf of commutative rings, matching the source's tensor notation. -/
abbrev CommRingSheaf (X : TopCat.{v}) :=
  Sheaf (Opens.grothendieckTopology X) CommRingCat.{v}

/-- Forgetting commutativity on a sheaf of rings. -/
noncomputable abbrev commRingSheafToRingSheaf {X : TopCat.{v}}
    (O : CommRingSheaf X) :
    Sheaf (Opens.grothendieckTopology X) RingCat.{v} :=
  (sheafCompose (Opens.grothendieckTopology X)
    (forget₂ CommRingCat RingCat)).obj O

/-- The underlying sheaf of modules over a commutative-ring sheaf. -/
abbrev CommRingSheafModule {X : TopCat.{v}} (O : CommRingSheaf X) :=
  SheafOfModules.{v} (commRingSheafToRingSheaf O)

/-- The underlying RingCat morphism of a commutative sheaf-ring morphism. -/
noncomputable abbrev commRingSheafMorphismToRingSheaf {X : TopCat.{v}}
    {O₁ O₂ : CommRingSheaf X} (α : O₁ ⟶ O₂) :
    commRingSheafToRingSheaf O₁ ⟶ commRingSheafToRingSheaf O₂ :=
  (sheafCompose (Opens.grothendieckTopology X)
    (forget₂ CommRingCat RingCat)).map α

/-- The tensor product sheaf for commutative sheaves of rings. -/
noncomputable abbrev commRingTensorProductSheaf {X : TopCat.{v}}
    {O₁ O₂ : CommRingSheaf X} (α : O₁ ⟶ O₂)
    (G : CommRingSheafModule O₁) : CommRingSheafModule O₂ :=
  tensorProductSheaf (commRingSheafMorphismToRingSheaf α) G

/-- The stalk-level extension of scalars for the source's sheaf hypotheses.
`ModuleCat.extendScalars` fixes the canonical tensor-ordering convention used
by Mathlib. -/
noncomputable def commRingSheafModuleStalk {X : TopCat.{v}}
    {O : CommRingSheaf X} (G : CommRingSheafModule O) (x : X) :
    ModuleCat (↑(TopCat.Presheaf.stalk O.obj x)) := by
  letI : Module (↑(TopCat.Presheaf.stalk O.obj x))
      (↑(TopCat.Presheaf.stalk G.val.presheaf x)) :=
    Formalization.Books.Sheaves.Unit14.stalkModule O.obj G.val x
  exact ModuleCat.of (↑(TopCat.Presheaf.stalk O.obj x))
    (↑(TopCat.Presheaf.stalk G.val.presheaf x))

/-- The stalk-level extension of scalars for the source's sheaf hypotheses.
`ModuleCat.extendScalars` fixes the canonical tensor-ordering convention used
by Mathlib. -/
noncomputable def sheafStalkTensorProduct {X : TopCat.{v}}
    {O₁ O₂ : CommRingSheaf X} (α : O₁ ⟶ O₂)
    (G : CommRingSheafModule O₁) (x : X) :
    ModuleCat (↑(TopCat.Presheaf.stalk O₂.obj x)) := by
  exact (ModuleCat.extendScalars
      ((TopCat.Presheaf.stalkFunctor (CommRingCat.{v}) x).map α.hom).hom).obj
    (commRingSheafModuleStalk G x)

/-- The stalk of the tensor product sheaf is canonically the stalk-level
extension of scalars. -/
theorem stalk_tensorProductSheaf_iso {X : TopCat.{v}}
    {O₁ O₂ : CommRingSheaf X} (α : O₁ ⟶ O₂)
    (G : CommRingSheafModule O₁) (x : X) :
    Nonempty (sheafStalkTensorProduct α G x ≅
      commRingSheafModuleStalk (commRingTensorProductSheaf α G) x) := by
  sorry

end

end Formalization.Books.Sheaves.Unit20
