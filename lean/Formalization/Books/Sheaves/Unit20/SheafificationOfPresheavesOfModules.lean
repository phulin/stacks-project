import Formalization.Books.Sheaves.Unit17.Modules
import Mathlib.Algebra.Category.Grp.Zero
import Mathlib.Algebra.Module.MinimalAxioms
import Mathlib.Topology.Sheaves.Alexandrov
import Mathlib.Topology.Sheaves.Skyscraper
import Mathlib.Topology.Sheaves.Limits

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
open scoped ZeroObject ChangeOfRings
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
  exact Formalization.Books.Sheaves.Unit17.existsUnique_moduleSheafificationFactorization G φ

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

/- The source's warning that the presheaf tensor product need not itself be a
sheaf.

The theorem lives here, rather than in Unit 17, because the assertion occurs
in the source's discussion of sheafifying presheaves of modules. -/
/-- On commutative ring sheaves, the sections of the presheaf tensor product
are the expected sectionwise extensions of scalars.  This is the precise
bridge from the presheaf computation in Unit 06 to the counterexample below. -/
theorem commRingSheafTensorProductPresheaf_obj_iso
    {X : TopCat.{v}}
    {O₁ O₂ : Formalization.Books.Sheaves.Unit17.CommRingSheaf X}
    (α : O₁ ⟶ O₂)
    (G : CommRingPresheafModule O₁.obj)
    (U : (Opens X)ᵒᵖ) :
    Nonempty
      ((ModuleCat.extendScalars (α.hom.app U).hom).obj
          (ModuleCat.of (O₁.obj.obj U) (G.obj U)) ≅
        ModuleCat.of (O₂.obj.obj U)
          ((tensorProductPresheaf
            (commRingPresheafMorphismToRingPresheaf α.hom) G).obj U)) := by
  exact tensorProductPresheaf_obj_iso α.hom G U

/- The only non-formal part of the warning is the construction of one
   counterexample.  A proof can be organized as follows.

   1. Use the finite space with opens `∅`, `U`, `V`, `U ∩ V`, and `U ∪ V`.
      Define a sheaf of `ℤ`-modules whose gluing map over the cover `{U, V}`
      realizes the inclusion `2ℤ → ℤ` as an equalizer.  Verify the sheaf
      condition by enumerating the covers of this finite lattice.
   2. Take the constant commutative ring sheaves associated to `ℤ` and
      `ZMod 2`, with their quotient morphism, and equip the module sheaf from
      step 1 with its evident `ℤ`-action.
   3. For each of the five opens, rewrite the tensor-product presheaf using
      `commRingSheafTensorProductPresheaf_obj_iso`.  Naturality of that
      comparison identifies the gluing fork for `{U, V}` with the result of
      tensoring the fork from step 1 by `ZMod 2`.
   4. The image of `2ℤ → ℤ` after this scalar extension is zero, so the
      resulting fork is not limiting.  Apply the equalizer-products
      characterization of the sheaf condition to the cover `{U, V}`.

   Keeping this construction in a separate lemma makes the final logical
   assembly below independent of the chosen finite-space presentation. -/
private inductive unit20VPoint
  | left
  | top
  | right
  deriving DecidableEq

private instance : LE unit20VPoint where
  le x y := match x, y with
    | .left, .left => True
    | .left, .top => True
    | .top, .top => True
    | .right, .right => True
    | .right, .top => True
    | _, _ => False

private instance : Preorder unit20VPoint where
  le_refl x := by cases x <;> simp [LE.le]
  le_trans x y z := by cases x <;> cases y <;> cases z <;> simp [LE.le]

private abbrev unit20Point := Topology.WithUpperSet (ULift.{v} unit20VPoint)

private abbrev unit20X := TopCat.of unit20Point

private noncomputable def unit20Mod2Cast :
    CommRingCat.of (ULift.{v} ℤ) ⟶ CommRingCat.of (ULift.{v} (ZMod 2)) :=
  CommRingCat.ofHom
    { toFun := fun z => ⟨(z.down : ZMod 2)⟩
      map_one' := by rfl
      map_mul' := by intro x y; cases x; cases y; congr 1; simp
      map_zero' := by rfl
      map_add' := by intro x y; cases x; cases y; congr 1; simp }

private noncomputable def unit20Top : unit20Point := ULift.up .top

private noncomputable def unit20Left : unit20Point := ULift.up .left

private noncomputable def unit20Right : unit20Point := ULift.up .right

private theorem unit20_mem_top {U : Opens unit20X} {x : unit20Point}
    (hx : x ∈ U) : unit20Top ∈ U := by
  have hU := U.isOpen
  rw [Topology.IsUpperSet.isOpen_iff_isUpperSet] at hU
  apply hU (a := x) (b := unit20Top)
  · rcases x with ⟨x⟩
    cases x <;> simp [unit20Top, LE.le]
  · exact hx

private noncomputable instance unit20PointDecidable (x : unit20Point) :
    ∀ U : Opens unit20X, Decidable (x ∈ U) := fun _ => Classical.propDecidable _

private theorem unit20_commRing_eqToHom_apply {A B : CommRingCat.{v}}
    (h : A = B) (x : A) :
    (ConcreteCategory.hom (eqToHom h)) x =
      cast (congrArg (fun R : CommRingCat.{v} => (R : Type v)) h) x := by
  cases h
  rfl

private noncomputable abbrev unit20O1Presheaf :
    CommRingPresheaf.{v} unit20X :=
  skyscraperPresheaf (X := unit20X) unit20Top
    (CommRingCat.of (ULift.{v} ℤ))

private noncomputable def unit20O1 :
    Formalization.Books.Sheaves.Unit17.CommRingSheaf unit20X := by
  classical
  exact ⟨unit20O1Presheaf,
    skyscraperPresheaf_isSheaf (X := unit20X) (C := CommRingCat.{v}) unit20Top
      (CommRingCat.of (ULift.{v} ℤ))⟩

private noncomputable abbrev unit20O2LeftPresheaf :
    CommRingPresheaf.{v} unit20X :=
  skyscraperPresheaf (X := unit20X) unit20Left
    (CommRingCat.of (ULift.{v} (ZMod 2)))

private noncomputable def unit20O2Left :
    Formalization.Books.Sheaves.Unit17.CommRingSheaf unit20X := by
  classical
  exact ⟨unit20O2LeftPresheaf,
    skyscraperPresheaf_isSheaf (X := unit20X) (C := CommRingCat.{v}) unit20Left
      (CommRingCat.of (ULift.{v} (ZMod 2)))⟩

private noncomputable abbrev unit20O2RightPresheaf :
    CommRingPresheaf.{v} unit20X :=
  skyscraperPresheaf (X := unit20X) unit20Right
    (CommRingCat.of (ULift.{v} ℤ))

private noncomputable def unit20O2Right :
    Formalization.Books.Sheaves.Unit17.CommRingSheaf unit20X := by
  classical
  exact ⟨unit20O2RightPresheaf,
    skyscraperPresheaf_isSheaf (X := unit20X) (C := CommRingCat.{v}) unit20Right
      (CommRingCat.of (ULift.{v} ℤ))⟩

private noncomputable def unit20O2 :
    Formalization.Books.Sheaves.Unit17.CommRingSheaf unit20X :=
  unit20O2Left ⨯ unit20O2Right

private noncomputable def unit20AlphaLeftApp (U : (Opens unit20X)ᵒᵖ) :
    unit20O1.obj.obj U ⟶ unit20O2Left.obj.obj U := by
    classical
    by_cases h : unit20Left ∈ U.unop
    · have ht : unit20Top ∈ U.unop := unit20_mem_top h
      change (skyscraperPresheaf (X := unit20X) unit20Top
          (CommRingCat.of (ULift.{v} ℤ))).obj U ⟶
        (skyscraperPresheaf (X := unit20X) unit20Left
          (CommRingCat.of (ULift.{v} (ZMod 2)))).obj U
      have hT :
          (skyscraperPresheaf (X := unit20X) unit20Top
            (CommRingCat.of (ULift.{v} ℤ))).obj U =
            CommRingCat.of (ULift.{v} ℤ) := by
        simp [skyscraperPresheaf, ht]
      have hL :
          (skyscraperPresheaf (X := unit20X) unit20Left
            (CommRingCat.of (ULift.{v} (ZMod 2)))).obj U =
            CommRingCat.of (ULift.{v} (ZMod 2)) := by
        simp [skyscraperPresheaf, h]
      exact eqToHom hT ≫ unit20Mod2Cast ≫ eqToHom hL.symm
    · change (skyscraperPresheaf (X := unit20X) unit20Top
          (CommRingCat.of (ULift.{v} ℤ))).obj U ⟶
        (skyscraperPresheaf (X := unit20X) unit20Left
          (CommRingCat.of (ULift.{v} (ZMod 2)))).obj U
      simpa [skyscraperPresheaf, h] using
        (terminalIsTerminal.from
          ((skyscraperPresheaf (X := unit20X) unit20Top
            (CommRingCat.of (ULift.{v} ℤ))).obj U))

private noncomputable def unit20AlphaLeft : unit20O1.obj ⟶ unit20O2Left.obj where
  app U := unit20AlphaLeftApp U
  naturality {X Y} f := by
    classical
    by_cases hY : unit20Left ∈ Y.unop
    · have hX : unit20Left ∈ X.unop := leOfHom f.unop hY
      have htX : unit20Top ∈ X.unop := unit20_mem_top hX
      have htY : unit20Top ∈ Y.unop := unit20_mem_top hY
      have hTX : unit20O1.obj.obj X = CommRingCat.of (ULift.{v} ℤ) := by
        simp [unit20O1, skyscraperPresheaf, htX]
      have hTY : unit20O1.obj.obj Y = CommRingCat.of (ULift.{v} ℤ) := by
        simp [unit20O1, skyscraperPresheaf, htY]
      have hLX : unit20O2Left.obj.obj X =
          CommRingCat.of (ULift.{v} (ZMod 2)) := by
        simp [unit20O2Left, skyscraperPresheaf, hX]
      have hLY : unit20O2Left.obj.obj Y =
          CommRingCat.of (ULift.{v} (ZMod 2)) := by
        simp [unit20O2Left, skyscraperPresheaf, hY]
      have hmapT : unit20O1.obj.map f ≫ eqToHom hTY = eqToHom hTX := by
        have hTX' :
            (if h : unit20Top ∈ X.unop then CommRingCat.of (ULift.{v} ℤ)
              else ⊤_ CommRingCat) = CommRingCat.of (ULift.{v} ℤ) := by
          simp [htX]
        have hTY' :
            (if h : unit20Top ∈ Y.unop then CommRingCat.of (ULift.{v} ℤ)
              else ⊤_ CommRingCat) = CommRingCat.of (ULift.{v} ℤ) := by
          simp [htY]
        have hmap :
            (skyscraperPresheaf (X := unit20X) unit20Top
                (CommRingCat.of (ULift.{v} ℤ))).map f ≫ eqToHom hTY' =
              eqToHom hTX' := by
          dsimp [skyscraperPresheaf]
          rw [dif_pos htY]
          simp only [eqToHom_trans]
        have hTXeq : hTX' = hTX := Subsingleton.elim _ _
        have hTYeq : hTY' = hTY := Subsingleton.elim _ _
        change (skyscraperPresheaf (X := unit20X) unit20Top
            (CommRingCat.of (ULift.{v} ℤ))).map f ≫ eqToHom hTY =
          eqToHom hTX
        rw [← hTYeq, ← hTXeq]
        exact hmap
      have hmapL : unit20O2Left.obj.map f ≫ eqToHom hLY = eqToHom hLX := by
        have hLX' :
            (if h : unit20Left ∈ X.unop then
              CommRingCat.of (ULift.{v} (ZMod 2)) else ⊤_ CommRingCat) =
              CommRingCat.of (ULift.{v} (ZMod 2)) := by
          simp [hX]
        have hLY' :
            (if h : unit20Left ∈ Y.unop then
              CommRingCat.of (ULift.{v} (ZMod 2)) else ⊤_ CommRingCat) =
              CommRingCat.of (ULift.{v} (ZMod 2)) := by
          simp [hY]
        have hmap :
            (skyscraperPresheaf (X := unit20X) unit20Left
                (CommRingCat.of (ULift.{v} (ZMod 2)))).map f ≫ eqToHom hLY' =
              eqToHom hLX' := by
          dsimp [skyscraperPresheaf]
          rw [dif_pos hY]
          simp only [eqToHom_trans]
        have hLXeq : hLX' = hLX := Subsingleton.elim _ _
        have hLYeq : hLY' = hLY := Subsingleton.elim _ _
        change (skyscraperPresheaf (X := unit20X) unit20Left
            (CommRingCat.of (ULift.{v} (ZMod 2)))).map f ≫ eqToHom hLY =
          eqToHom hLX
        rw [← hLYeq, ← hLXeq]
        exact hmap
      have happX : unit20AlphaLeftApp X =
          eqToHom hTX ≫ unit20Mod2Cast ≫ eqToHom hLX.symm := by
        simp [unit20AlphaLeftApp, hX]
        congr 1
      have happY : unit20AlphaLeftApp Y =
          eqToHom hTY ≫ unit20Mod2Cast ≫ eqToHom hLY.symm := by
        simp [unit20AlphaLeftApp, hY]
        congr 1
      change unit20O1.obj.map f ≫ unit20AlphaLeftApp Y =
        unit20AlphaLeftApp X ≫ unit20O2Left.obj.map f
      rw [happY, happX]
      have hcompL : eqToHom hLX.symm ≫ unit20O2Left.obj.map f =
          eqToHom hLY.symm := by
        apply (cancel_mono (eqToHom hLY)).1
        rw [Category.assoc, hmapL]
        simp
      calc
        unit20O1.obj.map f ≫
              (eqToHom hTY ≫ unit20Mod2Cast ≫ eqToHom hLY.symm) =
            (unit20O1.obj.map f ≫ eqToHom hTY) ≫ unit20Mod2Cast ≫
              eqToHom hLY.symm := by rw [Category.assoc]
        _ = (eqToHom hTX ≫ unit20Mod2Cast) ≫ eqToHom hLY.symm := by
          rw [hmapT]
          rw [Category.assoc]
        _ = (eqToHom hTX ≫ unit20Mod2Cast ≫ eqToHom hLX.symm) ≫
              unit20O2Left.obj.map f := by
          rw [← hcompL]
          simp only [Category.assoc]
    · have hYobj : unit20O2Left.obj.obj Y = ⊤_ CommRingCat := by
        simp [unit20O2Left, skyscraperPresheaf, hY]
      apply (cancel_mono (eqToHom hYobj)).1
      apply terminalIsTerminal.hom_ext

private noncomputable def unit20AlphaRightApp (U : (Opens unit20X)ᵒᵖ) :
    unit20O1.obj.obj U ⟶ unit20O2Right.obj.obj U := by
  classical
  by_cases h : unit20Right ∈ U.unop
  · have ht : unit20Top ∈ U.unop := unit20_mem_top h
    change (skyscraperPresheaf (X := unit20X) unit20Top
        (CommRingCat.of (ULift.{v} ℤ))).obj U ⟶
      (skyscraperPresheaf (X := unit20X) unit20Right
        (CommRingCat.of (ULift.{v} ℤ))).obj U
    have hT :
        (skyscraperPresheaf (X := unit20X) unit20Top
          (CommRingCat.of (ULift.{v} ℤ))).obj U =
          CommRingCat.of (ULift.{v} ℤ) := by
      simp [skyscraperPresheaf, ht]
    have hR :
        (skyscraperPresheaf (X := unit20X) unit20Right
          (CommRingCat.of (ULift.{v} ℤ))).obj U =
          CommRingCat.of (ULift.{v} ℤ) := by
      simp [skyscraperPresheaf, h]
    exact eqToHom hT ≫ 𝟙 _ ≫ eqToHom hR.symm
  · simpa [unit20O1, unit20O2Right, skyscraperPresheaf, h] using
      (terminalIsTerminal.from
        ((skyscraperPresheaf (X := unit20X) unit20Top
          (CommRingCat.of (ULift.{v} ℤ))).obj U))

private noncomputable def unit20AlphaRight : unit20O1.obj ⟶ unit20O2Right.obj where
  app U := unit20AlphaRightApp U
  naturality {X Y} f := by
    classical
    by_cases hY : unit20Right ∈ Y.unop
    · have hX : unit20Right ∈ X.unop := leOfHom f.unop hY
      have htX : unit20Top ∈ X.unop := unit20_mem_top hX
      have htY : unit20Top ∈ Y.unop := unit20_mem_top hY
      have hTX :
          unit20O1.obj.obj X =
          CommRingCat.of (ULift.{v} ℤ) := by
        simp [unit20O1, skyscraperPresheaf, htX]
      have hTY :
          unit20O1.obj.obj Y =
          CommRingCat.of (ULift.{v} ℤ) := by
        simp [unit20O1, skyscraperPresheaf, htY]
      have hRX :
          unit20O2Right.obj.obj X =
          CommRingCat.of (ULift.{v} ℤ) := by
        simp [unit20O2Right, skyscraperPresheaf, hX]
      have hRY :
          unit20O2Right.obj.obj Y =
          CommRingCat.of (ULift.{v} ℤ) := by
        simp [unit20O2Right, skyscraperPresheaf, hY]
      have hmapT :
          unit20O1.obj.map f ≫ eqToHom hTY =
            eqToHom hTX := by
        have hTX' :
            (if h : unit20Top ∈ X.unop then CommRingCat.of (ULift.{v} ℤ)
              else ⊤_ CommRingCat) = CommRingCat.of (ULift.{v} ℤ) := by
          simp [htX]
        have hTY' :
            (if h : unit20Top ∈ Y.unop then CommRingCat.of (ULift.{v} ℤ)
              else ⊤_ CommRingCat) = CommRingCat.of (ULift.{v} ℤ) := by
          simp [htY]
        have hmap :
            (skyscraperPresheaf (X := unit20X) unit20Top
                (CommRingCat.of (ULift.{v} ℤ))).map f ≫ eqToHom hTY' =
              eqToHom hTX' := by
          dsimp [skyscraperPresheaf]
          rw [dif_pos htY]
          simp only [eqToHom_trans]
        have hTXeq : hTX' = hTX := Subsingleton.elim _ _
        have hTYeq : hTY' = hTY := Subsingleton.elim _ _
        change (skyscraperPresheaf (X := unit20X) unit20Top
            (CommRingCat.of (ULift.{v} ℤ))).map f ≫ eqToHom hTY =
          eqToHom hTX
        rw [← hTYeq, ← hTXeq]
        exact hmap
      have hmapR :
          unit20O2Right.obj.map f ≫ eqToHom hRY =
            eqToHom hRX := by
        have hRX' :
            (if h : unit20Right ∈ X.unop then CommRingCat.of (ULift.{v} ℤ)
              else ⊤_ CommRingCat) = CommRingCat.of (ULift.{v} ℤ) := by
          simp [hX]
        have hRY' :
            (if h : unit20Right ∈ Y.unop then CommRingCat.of (ULift.{v} ℤ)
              else ⊤_ CommRingCat) = CommRingCat.of (ULift.{v} ℤ) := by
          simp [hY]
        have hmap :
            (skyscraperPresheaf (X := unit20X) unit20Right
                (CommRingCat.of (ULift.{v} ℤ))).map f ≫ eqToHom hRY' =
              eqToHom hRX' := by
          dsimp [skyscraperPresheaf]
          rw [dif_pos hY]
          simp only [eqToHom_trans]
        have hRXeq : hRX' = hRX := Subsingleton.elim _ _
        have hRYeq : hRY' = hRY := Subsingleton.elim _ _
        change (skyscraperPresheaf (X := unit20X) unit20Right
            (CommRingCat.of (ULift.{v} ℤ))).map f ≫ eqToHom hRY =
          eqToHom hRX
        rw [← hRYeq, ← hRXeq]
        exact hmap
      have happX : unit20AlphaRightApp X = eqToHom hTX ≫ 𝟙 _ ≫ eqToHom hRX.symm := by
        simp [unit20AlphaRightApp, hX, hRX]
        congr 1
      have happY : unit20AlphaRightApp Y = eqToHom hTY ≫ 𝟙 _ ≫ eqToHom hRY.symm := by
        simp [unit20AlphaRightApp, hY, hRY]
        congr 1
      change unit20O1.obj.map f ≫ unit20AlphaRightApp Y =
        unit20AlphaRightApp X ≫ unit20O2Right.obj.map f
      rw [happY, happX]
      have hcompR : eqToHom hRX.symm ≫ unit20O2Right.obj.map f =
          eqToHom hRY.symm := by
        apply (cancel_mono (eqToHom hRY)).1
        rw [Category.assoc, hmapR]
        simp
      calc
        unit20O1.obj.map f ≫
              (eqToHom hTY ≫ 𝟙 _ ≫ eqToHom hRY.symm) =
            (unit20O1.obj.map f ≫ eqToHom hTY) ≫ 𝟙 _ ≫
              eqToHom hRY.symm := by rw [Category.assoc]
        _ = (eqToHom hTX ≫ 𝟙 _) ≫ eqToHom hRY.symm := by
          rw [hmapT]
          rw [Category.assoc]
        _ = (eqToHom hTX ≫ 𝟙 _ ≫ eqToHom hRX.symm) ≫
              unit20O2Right.obj.map f := by
          rw [← hcompR]
          simp only [Category.assoc]
    · have hYobj : unit20O2Right.obj.obj Y = ⊤_ CommRingCat := by
        simp [unit20O2Right, skyscraperPresheaf, hY]
      apply (cancel_mono (eqToHom hYobj)).1
      apply terminalIsTerminal.hom_ext

private noncomputable def unit20Alpha : unit20O1 ⟶ unit20O2 :=
  prod.lift (ObjectProperty.homMk unit20AlphaLeft)
    (ObjectProperty.homMk unit20AlphaRight)

private noncomputable abbrev unit20GPresheaf :
    TopCat.Presheaf AddCommGrpCat.{v} unit20X := by
  classical
  exact skyscraperPresheaf (X := unit20X) (C := AddCommGrpCat.{v}) unit20Left
    (AddCommGrpCat.of (ULift.{v} ℤ))

private theorem unit20_uliftInt_module_ext
    (P Q : Module (ULift.{v} ℤ) (ULift.{v} ℤ)) : P = Q := by
  apply Module.ext' P Q
  intro r m
  rcases r with ⟨r⟩
  have hP : @SMul.smul (ULift.{v} ℤ) (ULift.{v} ℤ)
      P.toSMul (r : ULift.{v} ℤ) m = r • m := by
    let : Module (ULift.{v} ℤ) (ULift.{v} ℤ) := P
    exact Int.cast_smul_eq_zsmul (ULift.{v} ℤ) r m
  have hQ : @SMul.smul (ULift.{v} ℤ) (ULift.{v} ℤ)
      Q.toSMul (r : ULift.{v} ℤ) m = r • m := by
    let : Module (ULift.{v} ℤ) (ULift.{v} ℤ) := Q
    exact Int.cast_smul_eq_zsmul (ULift.{v} ℤ) r m
  change @SMul.smul (ULift.{v} ℤ) (ULift.{v} ℤ)
      P.toSMul (r : ULift.{v} ℤ) m =
    @SMul.smul (ULift.{v} ℤ) (ULift.{v} ℤ)
      Q.toSMul (r : ULift.{v} ℤ) m
  exact hP.trans hQ.symm

@[instance_reducible] private noncomputable def unit20_moduleTransport
    {R R' : RingCat.{v}} {M M' : AddCommGrpCat.{v}}
    (hR : R = R') (hM : M = M') (inst : Module (↑R) (↑M)) :
    Module (↑R') (↑M') := by
  cases hR
  cases hM
  exact inst

private theorem unit20_eqToHom_module_smul
    {R R' : RingCat.{v}} {M M' : AddCommGrpCat.{v}}
    (hR : R = R') (hM : M = M') (inst : Module (↑R) (↑M))
    (transport : Module (↑R') (↑M'))
    (hinst : transport = unit20_moduleTransport hR hM inst)
    (r : R) (m : M) :
    (letI := inst
     letI := transport
     (ConcreteCategory.hom (eqToHom hM)) (r • m) =
       (ConcreteCategory.hom (eqToHom hR)) r •
         (ConcreteCategory.hom (eqToHom hM)) m) := by
  cases hR
  cases hM
  rw [hinst]
  rfl

private noncomputable def unit20GVal :
    PresheafOfModules (unit20O1.obj ⋙ (forget₂ CommRingCat RingCat)) := by
  classical
  let hDec : ∀ U : Opens unit20X, Decidable (unit20Left ∈ U) :=
    fun U => Classical.propDecidable _
  letI : ∀ U : Opens unit20X, Decidable (unit20Left ∈ U) := hDec
  let moduleInst : ∀ U : (Opens unit20X)ᵒᵖ, Module
      (↑((unit20O1.obj ⋙ (forget₂ CommRingCat RingCat)).obj U))
      ((unit20GPresheaf).obj U) := fun U => by
    by_cases h : unit20Left ∈ U.unop
    · change Module
        (↑((unit20O1.obj ⋙ (forget₂ CommRingCat RingCat)).obj U))
        (↑(if h : unit20Left ∈ U.unop then
          AddCommGrpCat.of (ULift.{v} ℤ) else ⊤_ AddCommGrpCat))
      rw [dif_pos h]
      have ht : unit20Top ∈ U.unop := unit20_mem_top h
      have hO1 : (unit20O1.obj ⋙ (forget₂ CommRingCat RingCat)).obj U =
          RingCat.of (ULift.{v} ℤ) := by
        simp [unit20O1, skyscraperPresheaf, ht]
        rfl
      exact Module.compHom (ULift.{v} ℤ) (eqToHom hO1).hom
    · change Module
        (↑((unit20O1.obj ⋙ (forget₂ CommRingCat RingCat)).obj U))
        (↑(if h : unit20Left ∈ U.unop then
          AddCommGrpCat.of (ULift.{v} ℤ) else ⊤_ AddCommGrpCat))
      rw [dif_neg h]
      let : Subsingleton (↑(⊤_ AddCommGrpCat)) :=
        AddCommGrpCat.subsingleton_of_isZero
          ((isZero_zero AddCommGrpCat).of_iso
            (HasZeroObject.zeroIsoTerminal :
              (0 : AddCommGrpCat) ≅ ⊤_ AddCommGrpCat).symm)
      letI : SMul
          (↑((unit20O1.obj ⋙ (forget₂ CommRingCat RingCat)).obj U))
          (↑(⊤_ AddCommGrpCat)) := ⟨fun _ _ => 0⟩
      exact Module.ofMinimalAxioms (M := ↑(⊤_ AddCommGrpCat))
        (fun _ _ _ => Subsingleton.elim _ _)
        (fun _ _ _ => Subsingleton.elim _ _)
        (fun _ _ _ => Subsingleton.elim _ _)
        (fun _ => Subsingleton.elim _ _)
  letI : ∀ U : (Opens unit20X)ᵒᵖ, Module
      (↑((unit20O1.obj ⋙ (forget₂ CommRingCat RingCat)).obj U))
      ((unit20GPresheaf).obj U) := moduleInst
  exact PresheafOfModules.ofPresheaf unit20GPresheaf (by
    intro U V f r m
    by_cases h : unit20Left ∈ V.unop
    · have h' : unit20Left ∈ U.unop := leOfHom f.unop h
      have ht : unit20Top ∈ V.unop := unit20_mem_top h
      have ht' : unit20Top ∈ U.unop := unit20_mem_top h'
      have hRU : (unit20O1.obj ⋙ (forget₂ CommRingCat RingCat)).obj U =
          RingCat.of (ULift.{v} ℤ) := by
        simp [unit20O1, skyscraperPresheaf, ht']
        rfl
      have hRV : (unit20O1.obj ⋙ (forget₂ CommRingCat RingCat)).obj V =
          RingCat.of (ULift.{v} ℤ) := by
        simp [unit20O1, skyscraperPresheaf, ht]
        rfl
      have hGU : unit20GPresheaf.obj U = AddCommGrpCat.of (ULift.{v} ℤ) := by
        simp [unit20GPresheaf, skyscraperPresheaf, h']
      have hGV : unit20GPresheaf.obj V = AddCommGrpCat.of (ULift.{v} ℤ) := by
        simp [unit20GPresheaf, skyscraperPresheaf, h]
      let instU₀ : Module
          (↑((unit20O1.obj ⋙ (forget₂ CommRingCat RingCat)).obj U))
          (↑(unit20GPresheaf.obj U)) := inferInstance
      have hRUv :
          (unit20O1.obj ⋙ (forget₂ CommRingCat RingCat)).obj U =
            (unit20O1.obj ⋙ (forget₂ CommRingCat RingCat)).obj V :=
        hRU.trans hRV.symm
      have hGUv : unit20GPresheaf.obj U = unit20GPresheaf.obj V :=
        hGU.trans hGV.symm
      have hGU' :
          (if h : unit20Left ∈ U.unop then AddCommGrpCat.of (ULift.{v} ℤ)
            else ⊤_ AddCommGrpCat) = AddCommGrpCat.of (ULift.{v} ℤ) := by
        simp [h']
      have hGV' :
          (if h : unit20Left ∈ V.unop then AddCommGrpCat.of (ULift.{v} ℤ)
            else ⊤_ AddCommGrpCat) = AddCommGrpCat.of (ULift.{v} ℤ) := by
        simp [h]
      have hGUv' :
          (if h : unit20Left ∈ U.unop then AddCommGrpCat.of (ULift.{v} ℤ)
            else ⊤_ AddCommGrpCat) =
            (if h : unit20Left ∈ V.unop then AddCommGrpCat.of (ULift.{v} ℤ)
              else ⊤_ AddCommGrpCat) := hGU'.trans hGV'.symm
      have hGmap' :
          (skyscraperPresheaf (X := unit20X) unit20Left
            (AddCommGrpCat.of (ULift.{v} ℤ))).map f = eqToHom hGUv' := by
        have hmap :
            (skyscraperPresheaf (X := unit20X) unit20Left
              (AddCommGrpCat.of (ULift.{v} ℤ))).map f ≫ eqToHom hGV' =
              eqToHom hGU' := by
          dsimp [skyscraperPresheaf]
          rw [dif_pos h]
          simp only [eqToHom_trans]
        have hcomp : eqToHom hGU' = eqToHom hGUv' ≫ eqToHom hGV' := by
          rw [eqToHom_trans]
        have hpost :
            (skyscraperPresheaf (X := unit20X) unit20Left
                (AddCommGrpCat.of (ULift.{v} ℤ))).map f ≫ eqToHom hGV' =
              eqToHom hGUv' ≫ eqToHom hGV' := hmap.trans hcomp
        apply (cancel_mono (eqToHom hGV')).1
        exact hpost
      have hGmap : unit20GPresheaf.map f = eqToHom hGUv := by
        simp [unit20GPresheaf, skyscraperPresheaf, h, h']
      have hRmap :
          ((unit20O1.obj ⋙ (forget₂ CommRingCat RingCat)).map f) =
            eqToHom hRUv := by
        have hRU' :
            (if h : unit20Top ∈ U.unop then CommRingCat.of (ULift.{v} ℤ)
              else ⊤_ CommRingCat) = CommRingCat.of (ULift.{v} ℤ) := by
          simp [ht']
        have hRV' :
            (if h : unit20Top ∈ V.unop then CommRingCat.of (ULift.{v} ℤ)
              else ⊤_ CommRingCat) = CommRingCat.of (ULift.{v} ℤ) := by
          simp [ht]
        have hRUv' :
            (if h : unit20Top ∈ U.unop then CommRingCat.of (ULift.{v} ℤ)
              else ⊤_ CommRingCat) =
              (if h : unit20Top ∈ V.unop then CommRingCat.of (ULift.{v} ℤ)
                else ⊤_ CommRingCat) := hRU'.trans hRV'.symm
        have hRmap' :
            (skyscraperPresheaf (X := unit20X) unit20Top
              (CommRingCat.of (ULift.{v} ℤ))).map f = eqToHom hRUv' := by
          have hmap :
              (skyscraperPresheaf (X := unit20X) unit20Top
                (CommRingCat.of (ULift.{v} ℤ))).map f ≫ eqToHom hRV' =
                eqToHom hRU' := by
            dsimp [skyscraperPresheaf]
            rw [dif_pos ht]
            simp only [eqToHom_trans]
          have hcomp : eqToHom hRU' = eqToHom hRUv' ≫ eqToHom hRV' := by
            rw [eqToHom_trans]
          have hpost :
              (skyscraperPresheaf (X := unit20X) unit20Top
                  (CommRingCat.of (ULift.{v} ℤ))).map f ≫ eqToHom hRV' =
                eqToHom hRUv' ≫ eqToHom hRV' := hmap.trans hcomp
          apply (cancel_mono (eqToHom hRV')).1
          exact hpost
        have hRmap'' := congrArg
          (fun g => (forget₂ CommRingCat RingCat).map g) hRmap'
        simpa [unit20O1, unit20O1Presheaf, skyscraperPresheaf, eqToHom_map]
          using hRmap''
      let transportedV : Module
          (↑((unit20O1.obj ⋙ (forget₂ CommRingCat RingCat)).obj V))
          (↑(unit20GPresheaf.obj V)) := by
        rw [hGV]
        exact Module.compHom (ULift.{v} ℤ) (eqToHom hRV).hom
      have hinstV : moduleInst V = transportedV := by
        let : Subsingleton (Module
            (↑((unit20O1.obj ⋙ (forget₂ CommRingCat RingCat)).obj V))
            (↑(unit20GPresheaf.obj V))) := by
          rw [hRV, hGV]
          exact ⟨fun P Q => unit20_uliftInt_module_ext P Q⟩
        exact Subsingleton.elim _ _
      have htransport : transportedV = unit20_moduleTransport hRUv hGUv instU₀ := by
        let : Subsingleton (Module
            (↑((unit20O1.obj ⋙ (forget₂ CommRingCat RingCat)).obj V))
            (↑(unit20GPresheaf.obj V))) := by
          rw [hRV, hGV]
          exact ⟨fun P Q => unit20_uliftInt_module_ext P Q⟩
        exact Subsingleton.elim _ _
      change (ConcreteCategory.hom (unit20GPresheaf.map f))
          (@SMul.smul _ _ instU₀.toSMul r m) =
        @SMul.smul _ _ (moduleInst V).toSMul
          ((ConcreteCategory.hom
            ((unit20O1.obj ⋙ (forget₂ CommRingCat RingCat)).map f)) r)
          ((ConcreteCategory.hom (unit20GPresheaf.map f)) m)
      rw [hGmap, hRmap]
      have hsmul := unit20_eqToHom_module_smul hRUv hGUv instU₀ transportedV
        htransport r m
      rw [hinstV]
      exact hsmul
    · have hGV : unit20GPresheaf.obj V = ⊤_ AddCommGrpCat := by
        simp [unit20GPresheaf, skyscraperPresheaf, h]
      let : Subsingleton (↑(unit20GPresheaf.obj V)) := by
        rw [hGV]
        exact AddCommGrpCat.subsingleton_of_isZero
          ((isZero_zero AddCommGrpCat).of_iso
            (HasZeroObject.zeroIsoTerminal :
              (0 : AddCommGrpCat) ≅ ⊤_ AddCommGrpCat).symm)
      exact Subsingleton.elim _ _)

private noncomputable def unit20G :
    Formalization.Books.Sheaves.Unit17.CommRingSheafModule unit20O1 :=
  ⟨unit20GVal, by
    classical
    change Presheaf.IsSheaf (Opens.grothendieckTopology unit20X) unit20GPresheaf
    exact skyscraperPresheaf_isSheaf (X := unit20X) unit20Left
      (AddCommGrpCat.of (ULift.{v} ℤ))⟩

private noncomputable def unit20Cover : ULift.{v} (Fin 2) → Opens unit20X :=
  by
    classical
    exact fun i => Fin.cases (Alexandrov.principalOpen unit20Left)
      (fun _ => Alexandrov.principalOpen (ULift.up .right)) i.down

private theorem unit20Cover_iSup : iSup unit20Cover = ⊤ := by
  apply le_antisymm le_top
  intro x hx
  rw [TopologicalSpace.Opens.mem_iSup]
  rcases x with ⟨x⟩
  cases x with
  | left =>
      refine ⟨⟨⟨0, by decide⟩⟩, ?_⟩
      change unit20VPoint.left ≤ unit20VPoint.left
      simp [LE.le]
  | top =>
      refine ⟨⟨⟨0, by decide⟩⟩, ?_⟩
      change unit20VPoint.left ≤ unit20VPoint.top
      simp [LE.le]
  | right =>
      refine ⟨⟨⟨1, by decide⟩⟩, ?_⟩
      change unit20VPoint.right ≤ unit20VPoint.right
      simp [LE.le]

private noncomputable abbrev unit20T :=
  sheafTensorProductPresheaf
    (Formalization.Books.Sheaves.Unit17.commRingSheafMorphismToRingSheaf unit20Alpha)
    unit20G

private noncomputable abbrev unit20E :=
  sectionwiseExtensionOfScalars unit20Alpha.hom unit20G.val

private noncomputable abbrev unit20O1Top := unit20O1.obj.obj (op (⊤ : Opens unit20X))

private noncomputable abbrev unit20O2Top := unit20O2.obj.obj (op (⊤ : Opens unit20X))

private noncomputable abbrev unit20AlphaTop :=
  unit20Alpha.hom.app (op (⊤ : Opens unit20X))

private noncomputable abbrev unit20GTop := unit20G.val.obj (op (⊤ : Opens unit20X))

private theorem unit20GTop_eq_ulift :
    unit20GPresheaf.obj (op (⊤ : Opens unit20X)) =
      AddCommGrpCat.of (ULift.{v} ℤ) := by
  simp [unit20GPresheaf, skyscraperPresheaf]

private theorem unit20O1Top_eq_ulift :
    unit20O1Top = CommRingCat.of (ULift.{v} ℤ) := by
  change (if h : unit20Top ∈ (⊤ : Opens unit20X) then
      CommRingCat.of (ULift.{v} ℤ) else ⊤_ CommRingCat) =
    CommRingCat.of (ULift.{v} ℤ)
  simp

private theorem unit20O1TopRing_eq_ulift :
    (unit20O1.obj ⋙ (forget₂ CommRingCat RingCat)).obj
        (op (⊤ : Opens unit20X)) = RingCat.of (ULift.{v} ℤ) := by
  change (forget₂ CommRingCat RingCat).obj unit20O1Top =
    (forget₂ CommRingCat RingCat).obj (CommRingCat.of (ULift.{v} ℤ))
  exact congrArg (fun R : CommRingCat.{v} =>
    (forget₂ CommRingCat RingCat).obj R) unit20O1Top_eq_ulift

private theorem unit20GTop_carrier_eq_ulift :
    (unit20GTop : Type v) = ULift.{v} ℤ := by
  change (unit20GPresheaf.obj (op (⊤ : Opens unit20X)) : Type v) = ULift.{v} ℤ
  simp [unit20GPresheaf, skyscraperPresheaf]

private theorem unit20O1Top_carrier_eq_ulift :
    (unit20O1Top : Type v) = ULift.{v} ℤ := by
  exact congrArg (fun R : CommRingCat.{v} => (R : Type v)) unit20O1Top_eq_ulift

private noncomputable abbrev unit20GTopAdd : AddCommGrpCat.{v} :=
  AddCommGrpCat.of (unit20GTop : Type v)

private noncomputable abbrev unit20O1TopAdd : AddCommGrpCat.{v} :=
  AddCommGrpCat.of (unit20O1Top : Type v)

private theorem unit20GTopAdd_eq_ulift :
    unit20GTopAdd = AddCommGrpCat.of (ULift.{v} ℤ) := by
  have h : unit20Left ∈ (⊤ : Opens unit20X) := by simp
  change (if h' : unit20Left ∈ (⊤ : Opens unit20X) then
      AddCommGrpCat.of (ULift.{v} ℤ) else ⊤_ AddCommGrpCat) =
    AddCommGrpCat.of (ULift.{v} ℤ)
  rw [dif_pos h]

private theorem unit20O1TopAdd_eq_ulift :
    unit20O1TopAdd = AddCommGrpCat.of (ULift.{v} ℤ) := by
  have h := congrArg (fun R : RingCat.{v} =>
    (forget₂ RingCat AddCommGrpCat).obj R) unit20O1TopRing_eq_ulift
  exact h

private noncomputable def unit20TopRingCast :
    (ULift.{v} ℤ) →+* (unit20O1Top : Type v) :=
  (eqToHom unit20O1TopRing_eq_ulift.symm).hom

private noncomputable def unit20GTopOne : unit20GTop := by
  exact ConcreteCategory.hom (eqToHom unit20GTopAdd_eq_ulift.symm)
    (⟨(1 : ℤ)⟩ : ULift.{v} ℤ)

private noncomputable def unit20GTopToO1
    (m : (unit20GTop : Type v)) : (unit20O1Top : Type v) := by
  exact unit20TopRingCast
    (ConcreteCategory.hom (eqToHom unit20GTopAdd_eq_ulift) m)

private noncomputable instance unit20TopModule : Module (↑unit20O1Top) (↑unit20GTop) := by
  change Module
    (↑((Formalization.Books.Sheaves.Unit17.commRingSheafToRingSheaf unit20O1).obj.obj
      (op (⊤ : Opens unit20X)))) (↑unit20GTop)
  exact unit20GTop.isModule

private noncomputable def unit20TopTensor : unit20E.obj (op (⊤ : Opens unit20X)) :=
  by
    letI : Module (↑unit20O1Top) (↑unit20GTop) := by
      change Module
        (↑((Formalization.Books.Sheaves.Unit17.commRingSheafToRingSheaf unit20O1).obj.obj
          (op (⊤ : Opens unit20X)))) (↑unit20GTop)
      exact unit20GTop.isModule
    exact (1 : unit20O2.obj.obj (op (⊤ : Opens unit20X))) ⊗ₜ[
      unit20O1.obj.obj (op (⊤ : Opens unit20X)),
      (unit20Alpha.hom.app (op (⊤ : Opens unit20X))).hom] unit20GTopOne

private noncomputable def unit20TopTensorInT : unit20T.obj (op (⊤ : Opens unit20X)) :=
  (tensorProductPresheaf_sectionwiseIso unit20Alpha.hom unit20G.val).hom.app
    (op (⊤ : Opens unit20X)) unit20TopTensor

private noncomputable def unit20TopAdjointMap :
    ModuleCat.of (unit20O1.obj.obj (op (⊤ : Opens unit20X)))
        (unit20G.val.obj (op (⊤ : Opens unit20X))) ⟶
      (ModuleCat.restrictScalars
        (unit20Alpha.hom.app (op (⊤ : Opens unit20X))).hom).obj
        (ModuleCat.of (unit20O2.obj.obj (op (⊤ : Opens unit20X)))
          (unit20O2.obj.obj (op (⊤ : Opens unit20X)))) := by
  letI : Module (↑unit20O1Top) (↑unit20GTop) := by
    change Module
      (↑((Formalization.Books.Sheaves.Unit17.commRingSheafToRingSheaf unit20O1).obj.obj
        (op (⊤ : Opens unit20X)))) (↑unit20GTop)
    exact unit20GTop.isModule
  let target :=
    (ModuleCat.restrictScalars
      (unit20Alpha.hom.app (op (⊤ : Opens unit20X))).hom).obj
      (ModuleCat.of (unit20O2.obj.obj (op (⊤ : Opens unit20X)))
        (unit20O2.obj.obj (op (⊤ : Opens unit20X))))
  letI : Module (↑unit20O1Top) (↑unit20O2Top) := unit20AlphaTop.hom.toModule
  change ModuleCat.of (unit20O1.obj.obj (op (⊤ : Opens unit20X)))
      (unit20G.val.obj (op (⊤ : Opens unit20X))) ⟶ target
  refine ModuleCat.ofHom
    { toFun := fun m =>
      (unit20Alpha.hom.app (op (⊤ : Opens unit20X))).hom (unit20GTopToO1 m)
      map_add' := by
        intro x y
        simp only [unit20GTopToO1]
        simp
      map_smul' := by
        intro r m
        simp only [unit20GTopToO1]
        let transport : Module (ULift.{v} ℤ) (ULift.{v} ℤ) :=
          Module.compHom (ULift.{v} ℤ) (RingHom.id _)
        have htransport : transport =
            unit20_moduleTransport unit20O1TopRing_eq_ulift
              unit20GTopAdd_eq_ulift unit20TopModule := by
          apply unit20_uliftInt_module_ext
        have hsmul := unit20_eqToHom_module_smul
          unit20O1TopRing_eq_ulift unit20GTopAdd_eq_ulift unit20TopModule
          transport htransport r m
        have hsmul' := congrArg (fun z : ULift.{v} ℤ =>
          unit20TopRingCast z) hsmul
        have hO1smul : unit20GTopToO1 (r • m) =
            r • unit20GTopToO1 m := by
          convert hsmul' using 1 <;>
            simp_all [unit20GTopToO1, transport]
          all_goals
            have hcast : unit20TopRingCast
                (ConcreteCategory.hom (eqToHom unit20O1TopRing_eq_ulift) r) = r := by
              change (eqToHom unit20O1TopRing_eq_ulift.symm).hom
                  ((eqToHom unit20O1TopRing_eq_ulift).hom r) = r
              have hc : eqToHom unit20O1TopRing_eq_ulift ≫
                  eqToHom unit20O1TopRing_eq_ulift.symm = 𝟙 _ := by simp
              have hc' := congrArg (fun f => f r) hc
              exact hc'
            rw [hcast]
        rw [hsmul']
        rw [show (ConcreteCategory.hom (eqToHom unit20O1TopRing_eq_ulift) r) •
            (ConcreteCategory.hom (eqToHom unit20GTopAdd_eq_ulift) m) =
            (ConcreteCategory.hom (eqToHom unit20O1TopRing_eq_ulift) r) *
              (ConcreteCategory.hom (eqToHom unit20GTopAdd_eq_ulift) m) by rfl]
        rw [unit20TopRingCast.map_mul]
        rw [(unit20Alpha.hom.app (op (⊤ : Opens unit20X))).hom.map_mul]
        have hcast : unit20TopRingCast
            (ConcreteCategory.hom (eqToHom unit20O1TopRing_eq_ulift) r) = r := by
          change (eqToHom unit20O1TopRing_eq_ulift.symm).hom
              ((eqToHom unit20O1TopRing_eq_ulift).hom r) = r
          have hc : eqToHom unit20O1TopRing_eq_ulift ≫
              eqToHom unit20O1TopRing_eq_ulift.symm = 𝟙 _ := by simp
          have hc' := congrArg (fun f => f r) hc
          change (eqToHom unit20O1TopRing_eq_ulift.symm).hom
              ((eqToHom unit20O1TopRing_eq_ulift).hom r) = r at hc'
          exact hc'
        rw [hcast]
        rfl }

private noncomputable def unit20TopTensorToRing :
    unit20E.{v}.obj (op (⊤ : Opens unit20X)) ⟶
      ModuleCat.of.{v, v} (unit20O2.obj.obj (op (⊤ : Opens unit20X)))
        (unit20O2.obj.obj (op (⊤ : Opens unit20X))) :=
  ((ModuleCat.extendRestrictScalarsAdj
      (unit20Alpha.hom.app (op (⊤ : Opens unit20X))).hom).homEquiv
    (ModuleCat.of.{v, v} (unit20O1.obj.obj (op (⊤ : Opens unit20X)))
      (unit20G.val.obj (op (⊤ : Opens unit20X))))
    (ModuleCat.of.{v, v} (unit20O2.obj.obj (op (⊤ : Opens unit20X)))
      (unit20O2.obj.obj (op (⊤ : Opens unit20X))))).symm unit20TopAdjointMap

private theorem unit20GTopOne_to_ulift :
    ConcreteCategory.hom (eqToHom unit20GTopAdd_eq_ulift) unit20GTopOne =
      (⟨(1 : ℤ)⟩ : ULift.{v} ℤ) := by
  change (eqToHom unit20GTopAdd_eq_ulift).hom
      ((eqToHom unit20GTopAdd_eq_ulift.symm).hom (⟨(1 : ℤ)⟩ : ULift.{v} ℤ)) = _
  have hc : eqToHom unit20GTopAdd_eq_ulift.symm ≫
      eqToHom unit20GTopAdd_eq_ulift = 𝟙 _ := by simp
  have hc' := congrArg (fun f => f (⟨(1 : ℤ)⟩ : ULift.{v} ℤ)) hc
  change (eqToHom unit20GTopAdd_eq_ulift).hom
      ((eqToHom unit20GTopAdd_eq_ulift.symm).hom (⟨(1 : ℤ)⟩ : ULift.{v} ℤ)) = _ at hc'
  exact hc'

private theorem unit20GTopToO1_one :
    unit20GTopToO1 unit20GTopOne = (1 : unit20O1Top) := by
  unfold unit20GTopToO1
  rw [unit20GTopOne_to_ulift]
  exact unit20TopRingCast.map_one

private theorem unit20TopAdjointMap_apply :
    ConcreteCategory.hom unit20TopAdjointMap unit20GTopOne =
      (1 : unit20O2.obj.obj (op (⊤ : Opens unit20X))) := by
  change (unit20Alpha.hom.app (op (⊤ : Opens unit20X))).hom
      (unit20GTopToO1 unit20GTopOne) = 1
  rw [unit20GTopToO1_one]
  exact (unit20Alpha.hom.app (op (⊤ : Opens unit20X))).hom.map_one

private theorem unit20_extendRestrictScalars_apply_tmul
    {R S : Type v} [CommRing R] [CommRing S]
    {M : ModuleCat.{v} R} {N : ModuleCat.{v} S}
    (f : R →+* S) (g : M ⟶ (ModuleCat.restrictScalars f).obj N)
    (s : S) (m : M) :
    ConcreteCategory.hom
        (((ModuleCat.extendRestrictScalarsAdj f).homEquiv M N).symm g)
        (s ⊗ₜ[R, f] m) = s • (ConcreteCategory.hom g m : (N : Type v)) := by
  change ConcreteCategory.hom
      (ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars f g)
      (s ⊗ₜ[R, f] m) = s • ConcreteCategory.hom g m
  erw [ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars_hom_apply]
  rfl

private theorem unit20TopTensorToRing_apply :
    ConcreteCategory.hom unit20TopTensorToRing unit20TopTensor =
      (1 : unit20O2.obj.obj (op (⊤ : Opens unit20X))) := by
  have htm := unit20_extendRestrictScalars_apply_tmul
    (unit20Alpha.hom.app (op (⊤ : Opens unit20X))).hom unit20TopAdjointMap
    (1 : unit20O2.obj.obj (op (⊤ : Opens unit20X))) unit20GTopOne
  rw [unit20TopAdjointMap_apply] at htm
  change _ = (1 : unit20O2.obj.obj (op (⊤ : Opens unit20X))) •
      (1 : unit20O2.obj.obj (op (⊤ : Opens unit20X))) at htm
  have hone : (1 : unit20O2.obj.obj (op (⊤ : Opens unit20X))) •
      (1 : unit20O2.obj.obj (op (⊤ : Opens unit20X))) = 1 := by
    exact one_smul _ _
  rw [hone] at htm
  convert htm using 1 ;
    simp [unit20TopTensorToRing, unit20TopTensor]
  all_goals congr 1

private theorem unit20O2TopTwo_ne_zero :
    (2 : unit20O2.{v}.obj.obj (op (⊤ : Opens unit20X))) ≠ 0 := by
  intro h
  let ε : unit20O2.{v}.obj.obj (op (⊤ : Opens unit20X)) ⟶
      unit20O2Right.{v}.obj.obj (op (⊤ : Opens unit20X)) :=
    (prod.snd (X := unit20O2Left.{v}) (Y := unit20O2Right.{v})).hom.app
      (op (⊤ : Opens unit20X))
  have h' : ε.hom (2 : unit20O2.{v}.obj.obj (op (⊤ : Opens unit20X))) =
      ε.hom 0 := congrArg (fun z => ε.hom z) h
  have hne : ε.hom (2 : unit20O2.{v}.obj.obj (op (⊤ : Opens unit20X))) ≠
      ε.hom 0 := by
    have hR : unit20O2Right.{v}.obj.obj (op (⊤ : Opens unit20X)) =
        CommRingCat.of (ULift.{v} ℤ) := by
      have ht : unit20Right ∈ (⊤ : Opens unit20X) := by simp
      change (if h : unit20Right ∈ (⊤ : Opens unit20X) then
          CommRingCat.of (ULift.{v} ℤ) else ⊤_ CommRingCat) =
        CommRingCat.of (ULift.{v} ℤ)
      rw [dif_pos ht]
    have hne' : (2 : ULift.{v} ℤ) ≠ 0 := by
      intro hz
      have hz' := congrArg ULift.down hz
      norm_num at hz'
    intro hz
    have hz' := congrArg (fun z => ConcreteCategory.hom (eqToHom hR) z) hz
    have hε2 : ConcreteCategory.hom (eqToHom hR)
        (ε.hom (2 : unit20O2.{v}.obj.obj (op (⊤ : Opens unit20X)))) =
        (2 : ULift.{v} ℤ) := by
      change ((eqToHom hR).hom.comp ε.hom)
        (2 : unit20O2.{v}.obj.obj (op (⊤ : Opens unit20X))) =
        (2 : ULift.{v} ℤ)
      exact map_natCast _ 2
    have hε0 : ConcreteCategory.hom (eqToHom hR) (ε.hom 0) =
        (0 : ULift.{v} ℤ) := by
      change ((eqToHom hR).hom.comp ε.hom) 0 = (0 : ULift.{v} ℤ)
      exact map_zero _
    rw [hε2, hε0] at hz'
    exact hne' hz'
  exact hne h'

private theorem unit20TopTensorInT_ne_zero :
    unit20TopTensorInT.{v} ≠ (0 : unit20T.obj (op (⊤ : Opens unit20X))) := by
  let e := tensorProductPresheaf_sectionwiseIso unit20Alpha.hom unit20G.val
  intro h
  change ConcreteCategory.hom (e.hom.app (op (⊤ : Opens unit20X)))
      unit20TopTensor.{v} = 0 at h
  have hi : ConcreteCategory.hom (e.inv.app (op (⊤ : Opens unit20X)))
      (ConcreteCategory.hom (e.hom.app (op (⊤ : Opens unit20X))) unit20TopTensor.{v}) =
      unit20TopTensor.{v} := by
    have hi' := congrArg (fun f => f.app (op (⊤ : Opens unit20X))) e.hom_inv_id
    have hi'' := congrArg (fun f => f unit20TopTensor.{v}) hi'
    simpa only [PresheafOfModules.comp_app, PresheafOfModules.id_app,
      ModuleCat.id_apply, ConcreteCategory.comp_apply] using hi''
  have hx : unit20TopTensor.{v} = 0 := by
    calc
      unit20TopTensor.{v} = ConcreteCategory.hom (e.inv.app (op (⊤ : Opens unit20X)))
          (ConcreteCategory.hom (e.hom.app (op (⊤ : Opens unit20X))) unit20TopTensor.{v}) :=
        hi.symm
      _ = ConcreteCategory.hom (e.inv.app (op (⊤ : Opens unit20X))) 0 := by rw [h]
      _ = 0 := (e.inv.app (op (⊤ : Opens unit20X))).hom.map_zero
  have hx' := congrArg
    (fun z => ConcreteCategory.hom unit20TopTensorToRing.{v} z) hx
  rw [unit20TopTensorToRing_apply.{v}] at hx'
  apply unit20O2TopTwo_ne_zero
  calc
    (2 : unit20O2.{v}.obj.obj (op (⊤ : Opens unit20X))) = 1 + 1 := by norm_num
    _ = 0 := by rw [hx']; simp

private noncomputable def unit20ZeroMap :
    AddCommGrpCat.of (ULift.{v} ℤ) ⟶ unit20T.presheaf.obj
      (op (⊤ : Opens unit20X)) :=
  AddCommGrpCat.ofHom
    { toFun := fun _ => 0
      map_zero' := by simp
      map_add' := by simp }

private noncomputable def unit20DoubleMap :
    AddCommGrpCat.of (ULift.{v} ℤ) ⟶ unit20T.presheaf.obj
      (op (⊤ : Opens unit20X)) :=
  AddCommGrpCat.ofHom
    { toFun := fun z => z.down • ((2 : ℤ) • unit20TopTensorInT)
      map_zero' := by simp
      map_add' := by
        intro x y
        simp [add_smul] }

private theorem unit20TopTensorInT_double_ne_zero :
    (2 : ℤ) • (unit20TopTensorInT.{v} :
      unit20T.presheaf.obj (op (⊤ : Opens unit20X))) ≠
      (0 : unit20T.presheaf.obj (op (⊤ : Opens unit20X))) := by
  intro h
  have h_obj : (2 : ℤ) • unit20TopTensorInT.{v} =
      (0 : unit20T.obj (op (⊤ : Opens unit20X))) := by
    exact h
  let e := tensorProductPresheaf_sectionwiseIso unit20Alpha.hom unit20G.val
  change (2 : ℤ) • ConcreteCategory.hom (e.hom.app (op (⊤ : Opens unit20X)))
      unit20TopTensor.{v} = 0 at h_obj
  have hi : ConcreteCategory.hom (e.inv.app (op (⊤ : Opens unit20X)))
      (ConcreteCategory.hom (e.hom.app (op (⊤ : Opens unit20X))) unit20TopTensor.{v}) =
      unit20TopTensor.{v} := by
    have hi' := congrArg (fun f => f.app (op (⊤ : Opens unit20X))) e.hom_inv_id
    have hi'' := congrArg (fun f => f unit20TopTensor.{v}) hi'
    simpa only [PresheafOfModules.comp_app, PresheafOfModules.id_app,
      ModuleCat.id_apply, ConcreteCategory.comp_apply] using hi''
  have h' := congrArg
    (fun z : unit20T.obj (op (⊤ : Opens unit20X)) =>
      ConcreteCategory.hom (e.inv.app (op (⊤ : Opens unit20X))) z) h_obj
  rw [map_zsmul, map_zero, hi] at h'
  have h'' := congrArg
    (fun z => ConcreteCategory.hom unit20TopTensorToRing.{v} z) h'
  apply unit20O2TopTwo_ne_zero
  rw [map_zsmul, map_zero, unit20TopTensorToRing_apply.{v}] at h''
  simpa using h''

private theorem unit20ZeroMap_ne_unit20DoubleMap :
    unit20ZeroMap.{v} ≠ unit20DoubleMap.{v} := by
  intro h
  have hv : ConcreteCategory.hom unit20ZeroMap.{v}
      (⟨(1 : ℤ)⟩ : ULift.{v} ℤ) =
      ConcreteCategory.hom unit20DoubleMap.{v}
        (⟨(1 : ℤ)⟩ : ULift.{v} ℤ) := congrArg
    (fun f => f (⟨(1 : ℤ)⟩ : ULift.{v} ℤ)) h
  apply unit20TopTensorInT_double_ne_zero
  have hv' := hv.symm
  have hdouble : ConcreteCategory.hom unit20DoubleMap.{v}
      (⟨(1 : ℤ)⟩ : ULift.{v} ℤ) =
      (⟨(1 : ℤ)⟩ : ULift.{v} ℤ).down •
        ((2 : ℤ) • (unit20TopTensorInT.{v} :
          unit20T.presheaf.obj (op (⊤ : Opens unit20X)))) := by
    rfl
  have hzero : ConcreteCategory.hom unit20ZeroMap.{v}
      (⟨(1 : ℤ)⟩ : ULift.{v} ℤ) =
      (0 : unit20T.presheaf.obj (op (⊤ : Opens unit20X))) := by
    rfl
  have hv'' := hdouble.symm.trans (hv'.trans hzero)
  simpa using hv''

private theorem unit20ProdLeft_two_eq_zero :
    (2 : unit20O2.{v}.obj.obj
      (op (Alexandrov.principalOpen unit20Left))) = 0 := by
  let F : Formalization.Books.Sheaves.Unit17.CommRingSheaf unit20X ⥤
      CommRingCat.{v} :=
    TopCat.Sheaf.forget (CommRingCat.{v}) unit20X ⋙
      (evaluation (Opens unit20X)ᵒᵖ (CommRingCat.{v})).obj
        (op (Alexandrov.principalOpen unit20Left))
  let : PreservesLimits
      (TopCat.Sheaf.forget (CommRingCat.{v}) unit20X) := by
    infer_instance
  let : PreservesLimit
      ((pair unit20O2Left unit20O2Right) ⋙
        TopCat.Sheaf.forget (CommRingCat.{v}) unit20X)
      ((evaluation (Opens unit20X)ᵒᵖ (CommRingCat.{v})).obj
        (op (Alexandrov.principalOpen unit20Left))) := by
    exact evaluation_preservesLimit _ _
  let : PreservesLimit (pair unit20O2Left unit20O2Right) F := by
    dsimp [F]
    let : PreservesLimit (pair unit20O2Left unit20O2Right)
        (TopCat.Sheaf.forget (CommRingCat.{v}) unit20X) := by
      let : PreservesLimitsOfSize.{0, 0}
          (TopCat.Sheaf.forget (CommRingCat.{v}) unit20X) :=
        preservesLimitsOfSize_shrink
          (TopCat.Sheaf.forget (CommRingCat.{v}) unit20X)
      let hShape : PreservesLimitsOfShape.{0, 0} (Discrete WalkingPair)
          (TopCat.Sheaf.forget (CommRingCat.{v}) unit20X) :=
        PreservesLimitsOfSize.preservesLimitsOfShape
      exact hShape.preservesLimit
    exact comp_preservesLimit
      (K := pair unit20O2Left unit20O2Right)
      (F := TopCat.Sheaf.forget (CommRingCat.{v}) unit20X)
      (G := (evaluation (Opens unit20X)ᵒᵖ (CommRingCat.{v})).obj
        (op (Alexandrov.principalOpen unit20Left)))
  let e := PreservesLimitPair.iso F unit20O2Left unit20O2Right
  change (2 : F.obj (unit20O2Left ⨯ unit20O2Right)) = 0
  apply (ConcreteCategory.bijective_of_isIso e.hom).1
  change e.hom (2 : F.obj (unit20O2Left ⨯ unit20O2Right)) = e.hom 0
  have hm2 :
      ConcreteCategory.hom e.hom
          (2 : F.obj (unit20O2Left ⨯ unit20O2Right)) =
        ConcreteCategory.hom e.hom (1 : F.obj (unit20O2Left ⨯ unit20O2Right)) +
          ConcreteCategory.hom e.hom (1 : F.obj (unit20O2Left ⨯ unit20O2Right)) := by
    simpa only [one_add_one_eq_two] using
      (map_add (ConcreteCategory.hom e.hom)
        (1 : F.obj (unit20O2Left ⨯ unit20O2Right)) 1)
  have hm0 :
      ConcreteCategory.hom e.hom
          (0 : F.obj (unit20O2Left ⨯ unit20O2Right)) = 0 :=
    (ConcreteCategory.hom e.hom).map_zero
  rw [hm2, hm0]
  apply (CategoryTheory.Limits.Concrete.prodEquiv
    (F.obj unit20O2Left) (F.obj unit20O2Right)).injective
  have hL :
      F.obj unit20O2Left = CommRingCat.of (ULift.{v} (ZMod 2)) := by
    dsimp [F, unit20O2Left]
    change
      (if unit20Left ∈
          (Alexandrov.principalOpen unit20Left : Opens unit20X) then
        CommRingCat.of (ULift.{v} (ZMod 2)) else ⊤_ CommRingCat) =
      CommRingCat.of (ULift.{v} (ZMod 2))
    have hmem : unit20Left ∈
        (Alexandrov.principalOpen unit20Left : Opens unit20X) := by
      change unit20Left ≤ unit20Left
      exact @le_rfl (Topology.WithUpperSet (ULift.{v} unit20VPoint)) _ unit20Left
    rw [if_pos hmem]
  have hR : F.obj unit20O2Right = ⊤_ CommRingCat := by
    dsimp [F, unit20O2Right]
    change
      (if unit20Right ∈
          (Alexandrov.principalOpen unit20Left : Opens unit20X) then
        CommRingCat.of (ULift.{v} ℤ) else ⊤_ CommRingCat) =
      ⊤_ CommRingCat
    have hmem : unit20Right ∉
        (Alexandrov.principalOpen unit20Left : Opens unit20X) := by
      change ¬unit20Left ≤ unit20Right
      simp [unit20Left, unit20Right, LE.le]
    rw [if_neg hmem]
  rw [map_one]
  apply Prod.ext
  · calc
      (Concrete.prodEquiv (F.obj unit20O2Left) (F.obj unit20O2Right)
          (1 + 1)).1 =
          ConcreteCategory.hom
            (prod.fst (X := F.obj unit20O2Left) (Y := F.obj unit20O2Right))
            (1 + 1) :=
        CategoryTheory.Limits.Concrete.prodEquiv_apply_fst _ _ _
      _ = ConcreteCategory.hom
            (prod.fst (X := F.obj unit20O2Left) (Y := F.obj unit20O2Right)) 1 +
          ConcreteCategory.hom
            (prod.fst (X := F.obj unit20O2Left) (Y := F.obj unit20O2Right)) 1 :=
        map_add _ _ _
      _ = 0 := by
        rw [map_one, hL]
        congr 1
      _ = (Concrete.prodEquiv (F.obj unit20O2Left) (F.obj unit20O2Right) 0).1 := by
        rw [CategoryTheory.Limits.Concrete.prodEquiv_apply_fst]
        exact (map_zero _).symm
  · calc
      (Concrete.prodEquiv (F.obj unit20O2Left) (F.obj unit20O2Right)
          (1 + 1)).2 =
          ConcreteCategory.hom
            (prod.snd (X := F.obj unit20O2Left) (Y := F.obj unit20O2Right))
            (1 + 1) :=
        CategoryTheory.Limits.Concrete.prodEquiv_apply_snd _ _ _
      _ = ConcreteCategory.hom
            (prod.snd (X := F.obj unit20O2Left) (Y := F.obj unit20O2Right)) 1 +
          ConcreteCategory.hom
            (prod.snd (X := F.obj unit20O2Left) (Y := F.obj unit20O2Right)) 1 :=
        map_add _ _ _
      _ = 0 := by
        rw [map_one, hR]
        let : Subsingleton (⊤_ CommRingCat : Type v) :=
          CommRingCat.subsingleton_of_isTerminal
            (terminalIsTerminal : IsTerminal (⊤_ CommRingCat))
        exact Subsingleton.elim _ _
      _ = (Concrete.prodEquiv (F.obj unit20O2Left) (F.obj unit20O2Right) 0).2 := by
        rw [CategoryTheory.Limits.Concrete.prodEquiv_apply_snd]
        exact (map_zero _).symm

private noncomputable abbrev unit20A : Opens unit20X :=
  Alexandrov.principalOpen unit20Left

private noncomputable abbrev unit20B : Opens unit20X :=
  Alexandrov.principalOpen unit20Right

private noncomputable abbrev unit20O1A := unit20O1.obj.obj (op unit20A)

private noncomputable abbrev unit20O2A := unit20O2.obj.obj (op unit20A)

private noncomputable abbrev unit20AlphaA := unit20Alpha.hom.app (op unit20A)

private noncomputable abbrev unit20GA := unit20G.val.obj (op unit20A)

private theorem unit20T_restrict_double_left :
    unit20T.map (homOfLE (show unit20A ≤ ⊤ from le_top)).op
      ((2 : ℤ) • unit20TopTensorInT) = 0 := by
  let : Module
      (unit20O2.obj.obj (op (⊤ : Opens unit20X)))
      (unit20T.obj (op (⊤ : Opens unit20X))) := by
    change Module
      (↑((Formalization.Books.Sheaves.Unit17.commRingSheafToRingSheaf unit20O2).obj.obj
        (op (⊤ : Opens unit20X)))) (↑(unit20T.obj (op (⊤ : Opens unit20X))))
    infer_instance
  change unit20T.map (homOfLE (show unit20A ≤ ⊤ from le_top)).op
      ((2 : ℤ) • unit20TopTensorInT) = 0
  rw [← Int.cast_smul_eq_zsmul
    (unit20O2.obj.obj (op (⊤ : Opens unit20X)))]
  have hcast : ((2 : ℤ) : unit20O2.obj.obj
      (op (⊤ : Opens unit20X))) = 2 := by norm_num
  rw [hcast]
  have hs := PresheafOfModules.map_smul (M := unit20T)
    (homOfLE (show unit20A ≤ ⊤ from le_top)).op
    (2 : unit20O2.obj.obj (op (⊤ : Opens unit20X))) unit20TopTensorInT
  have hring :
      ConcreteCategory.hom
          (((Formalization.Books.Sheaves.Unit17.commRingSheafToRingSheaf unit20O2).obj.map
            (homOfLE (show unit20A ≤ ⊤ from le_top)).op)) 2 = 0 := by
    let f := ((Formalization.Books.Sheaves.Unit17.commRingSheafToRingSheaf unit20O2).obj.map
      (homOfLE (show unit20A ≤ ⊤ from le_top)).op)
    have h2 := map_add (ConcreteCategory.hom f)
      (1 : unit20O2.obj.obj (op (⊤ : Opens unit20X))) 1
    have h1 := map_one (ConcreteCategory.hom f)
    calc
      ConcreteCategory.hom f 2 = ConcreteCategory.hom f (1 + 1) :=
        congrArg (ConcreteCategory.hom f) one_add_one_eq_two.symm
      _ = ConcreteCategory.hom f 1 + ConcreteCategory.hom f 1 := h2
      _ = (1 : unit20O2.obj.obj (op unit20A)) + 1 := by rw [h1]; rfl
      _ = 2 := one_add_one_eq_two
      _ = 0 := unit20ProdLeft_two_eq_zero
  calc
    ConcreteCategory.hom
        (unit20T.map (homOfLE (show unit20A ≤ ⊤ from le_top)).op)
        (2 • unit20TopTensorInT) =
      ConcreteCategory.hom
          (((Formalization.Books.Sheaves.Unit17.commRingSheafToRingSheaf unit20O2).obj.map
            (homOfLE (show unit20A ≤ ⊤ from le_top)).op)) 2 •
        ConcreteCategory.hom
          (unit20T.map (homOfLE (show unit20A ≤ ⊤ from le_top)).op)
          unit20TopTensorInT := hs
    _ = 0 := by rw [hring, zero_smul]

private theorem unit20T_restrict_topTensor_right :
    unit20T.{v}.map (homOfLE (show unit20B ≤ ⊤ from le_top)).op
        unit20TopTensorInT.{v} = 0 := by
  have hsub : Subsingleton (unit20T.obj (op unit20B)) := by
    let e := tensorProductPresheaf_sectionwiseIso unit20Alpha.hom unit20G.val
    let : Subsingleton (unit20E.obj (op unit20B)) := by
      let : Subsingleton (unit20G.val.obj (op unit20B)) := by
        change Subsingleton (unit20GPresheaf.obj (op unit20B) : Type v)
        have hnot : unit20Left ∉ Alexandrov.principalOpen unit20Right := by
          change ¬unit20Right ≤ unit20Left
          simp [unit20Right, unit20Left, LE.le]
        dsimp [unit20GPresheaf, unit20B, skyscraperPresheaf]
        rw [if_neg hnot]
        exact AddCommGrpCat.subsingleton_of_isZero
          ((isZero_zero AddCommGrpCat).of_iso
            (HasZeroObject.zeroIsoTerminal :
              (0 : AddCommGrpCat) ≅ ⊤_ AddCommGrpCat).symm)
      change Subsingleton (unit20E.obj (op unit20B) : Type v)
      change Subsingleton
        ((ModuleCat.extendScalars
          (unit20Alpha.hom.app (op unit20B)).hom).obj
          (unit20G.val.obj (op unit20B)) : Type v)
      let : Module
          (unit20O1.obj.obj (op unit20B) : Type v)
          (unit20G.val.obj (op unit20B) : Type v) := by
        exact (unit20G.val.obj (op unit20B)).isModule
      refine ⟨fun x y => ?_⟩
      have hx : x = 0 := by
        induction x using TensorProduct.induction_on with
        | zero => rfl
        | tmul s m =>
          have hm : m = 0 := Subsingleton.elim _ _
          subst m
          exact TensorProduct.tmul_zero _ s
        | add x y ihx ihy =>
          calc
            x + y = 0 + 0 := congrArg₂ (· + ·) ihx ihy
            _ = 0 := add_zero 0
      have hy : y = 0 := by
        induction y using TensorProduct.induction_on with
        | zero => rfl
        | tmul s m =>
          have hm : m = 0 := Subsingleton.elim _ _
          subst m
          exact TensorProduct.tmul_zero _ s
        | add x y ihx ihy =>
          calc
            x + y = 0 + 0 := congrArg₂ (· + ·) ihx ihy
            _ = 0 := add_zero 0
      exact hx.trans hy.symm
    exact ⟨fun x y => by
      let eB := presheafOfModulesIsoApp e (op unit20B)
      have hxy : ConcreteCategory.hom eB.inv x =
          ConcreteCategory.hom eB.inv y :=
        Subsingleton.elim _ _
      have hcomp := congrArg
        (fun z => ConcreteCategory.hom eB.hom z) hxy
      have hx := congrArg
        (fun f : unit20T.obj (op unit20B) ⟶ unit20T.obj (op unit20B) =>
          ConcreteCategory.hom f x) eB.inv_hom_id
      have hy := congrArg
        (fun f : unit20T.obj (op unit20B) ⟶ unit20T.obj (op unit20B) =>
          ConcreteCategory.hom f y) eB.inv_hom_id
      have hx' : ConcreteCategory.hom eB.hom
          (ConcreteCategory.hom eB.inv x) = x := by
        change ConcreteCategory.hom eB.hom
            (ConcreteCategory.hom eB.inv x) = x at hx
        exact hx
      have hy' : ConcreteCategory.hom eB.hom
          (ConcreteCategory.hom eB.inv y) = y := by
        change ConcreteCategory.hom eB.hom
            (ConcreteCategory.hom eB.inv y) = y at hy
        exact hy
      exact hx'.symm.trans (hcomp.trans hy')⟩
  change (unit20T.map (homOfLE (show unit20B ≤ ⊤ from le_top)).op
      unit20TopTensorInT : unit20T.obj (op unit20B)) = 0
  exact hsub.elim _ _

 theorem exists_commRingSheaf_tensorProductPresheaf_failed_gluing :
    ∃ (X : TopCat.{v})
      (O₁ O₂ : Formalization.Books.Sheaves.Unit17.CommRingSheaf X)
      (α : O₁ ⟶ O₂)
      (G : Formalization.Books.Sheaves.Unit17.CommRingSheafModule O₁)
      (U : ULift.{v} (Fin 2) → Opens X),
      ¬ Nonempty (IsLimit
        (TopCat.Presheaf.SheafConditionEqualizerProducts.fork
          (sheafTensorProductPresheaf
            (Formalization.Books.Sheaves.Unit17.commRingSheafMorphismToRingSheaf
              α) G).presheaf U)) := by
  refine ⟨unit20X, unit20O1, unit20O2, unit20Alpha, unit20G, unit20Cover, ?_⟩
  rintro ⟨hlim⟩
  simp only [TopCat.Presheaf.SheafConditionEqualizerProducts.fork] at hlim
  let q : unit20T.presheaf.obj (op (⊤ : Opens unit20X)) ⟶
      unit20T.presheaf.obj (op (iSup unit20Cover)) :=
    eqToHom (congrArg (fun U : Opens unit20X =>
      unit20T.presheaf.obj (op U)) unit20Cover_iSup.symm)
  have hq : q = unit20T.presheaf.map (eqToHom unit20Cover_iSup).op := by
    dsimp [q]
    rw [CategoryTheory.eqToHom_op, CategoryTheory.eqToHom_map]
  have hz : unit20ZeroMap ≫ q = unit20DoubleMap ≫ q := by
    apply hlim.hom_ext
    intro j
    rcases j with (_ | _)
    all_goals
      simp only [Fork.ofι_π_app]
      set_option backward.isDefEq.respectTransparency false in
      have hres :
          (unit20ZeroMap ≫ q) ≫
              TopCat.Presheaf.SheafConditionEqualizerProducts.res
                (sheafTensorProductPresheaf
                  (Formalization.Books.Sheaves.Unit17.commRingSheafMorphismToRingSheaf
                    unit20Alpha) unit20G).presheaf unit20Cover =
            (unit20DoubleMap ≫ q) ≫
              TopCat.Presheaf.SheafConditionEqualizerProducts.res
                (sheafTensorProductPresheaf
                  (Formalization.Books.Sheaves.Unit17.commRingSheafMorphismToRingSheaf
                    unit20Alpha) unit20G).presheaf unit20Cover := by
        apply TopCat.Presheaf.SheafConditionEqualizerProducts.piOpens.hom_ext
          (sheafTensorProductPresheaf
            (Formalization.Books.Sheaves.Unit17.commRingSheafMorphismToRingSheaf
              unit20Alpha) unit20G).presheaf unit20Cover
        intro i
        rcases i with ⟨i⟩
        simp only [Category.assoc,
          TopCat.Presheaf.SheafConditionEqualizerProducts.res_π]
        fin_cases i
        · ext z
          have hrel :
              (eqToHom unit20Cover_iSup).op ≫
                  (Opens.leSupr unit20Cover (Equiv.ulift.symm 0)).op =
                (homOfLE (show unit20A ≤ ⊤ from le_top)).op := by
            change _ = (homOfLE (show unit20A ≤ ⊤ from le_top)).op
            apply Subsingleton.elim
          have hmap :
              unit20T.presheaf.map (eqToHom unit20Cover_iSup).op ≫
                  (sheafTensorProductPresheaf
                    (Formalization.Books.Sheaves.Unit17.commRingSheafMorphismToRingSheaf
                      unit20Alpha) unit20G).presheaf.map
                    (Opens.leSupr unit20Cover (Equiv.ulift.symm 0)).op =
                unit20T.presheaf.map
                  (homOfLE (show unit20A ≤ ⊤ from le_top)).op := by
            rw [← unit20T.presheaf.map_comp, hrel]
          have hzero_comp :
              unit20ZeroMap ≫
                  (unit20T.presheaf.map (eqToHom unit20Cover_iSup).op ≫
                    (sheafTensorProductPresheaf
                      (Formalization.Books.Sheaves.Unit17.commRingSheafMorphismToRingSheaf
                        unit20Alpha) unit20G).presheaf.map
                      (Opens.leSupr unit20Cover (Equiv.ulift.symm 0)).op) =
                unit20ZeroMap ≫ unit20T.presheaf.map
                  (homOfLE (show unit20A ≤ ⊤ from le_top)).op := by
            rw [hmap]
          have hdouble_comp :
              unit20DoubleMap ≫
                  (unit20T.presheaf.map (eqToHom unit20Cover_iSup).op ≫
                    (sheafTensorProductPresheaf
                      (Formalization.Books.Sheaves.Unit17.commRingSheafMorphismToRingSheaf
                        unit20Alpha) unit20G).presheaf.map
                      (Opens.leSupr unit20Cover (Equiv.ulift.symm 0)).op) =
                unit20DoubleMap ≫ unit20T.presheaf.map
                  (homOfLE (show unit20A ≤ ⊤ from le_top)).op := by
            rw [hmap]
          have hzero_app := congrArg
            (fun f : AddCommGrpCat.of (ULift.{v} ℤ) ⟶
                unit20T.presheaf.obj (op unit20A) =>
              ConcreteCategory.hom f z) hzero_comp
          have hdouble_app := congrArg
            (fun f : AddCommGrpCat.of (ULift.{v} ℤ) ⟶
                unit20T.presheaf.obj (op unit20A) =>
              ConcreteCategory.hom f z) hdouble_comp
          rw [hq]
          calc
            _ = ConcreteCategory.hom
                (unit20ZeroMap ≫ unit20T.presheaf.map
                  (homOfLE (show unit20A ≤ ⊤ from le_top)).op) z := by
              convert hzero_app using 1
              congr 2
            _ = ConcreteCategory.hom
                (unit20DoubleMap ≫ unit20T.presheaf.map
                  (homOfLE (show unit20A ≤ ⊤ from le_top)).op) z := by
              have hmap_underlying :
                  ∀ x : unit20T.obj (op (⊤ : Opens unit20X)),
                    AddCommGrpCat.Hom.hom
                        (unit20T.presheaf.map
                          (homOfLE (show unit20A ≤ ⊤ from le_top)).op) x =
                      ConcreteCategory.hom
                        (unit20T.map
                          (homOfLE (show unit20A ≤ ⊤ from le_top)).op) x := by
                intro x
                rfl
              have hpresheaf :
                  z.down • (2 : ℤ) • AddCommGrpCat.Hom.hom
                      (unit20T.presheaf.map
                        (homOfLE (show unit20A ≤ ⊤ from le_top)).op)
                      unit20TopTensorInT = 0 := by
                calc
                  _ = z.down • AddCommGrpCat.Hom.hom
                      (unit20T.presheaf.map
                        (homOfLE (show unit20A ≤ ⊤ from le_top)).op)
                      ((2 : ℤ) • unit20TopTensorInT) := by
                    rw [map_zsmul]
                  _ = z.down • ConcreteCategory.hom
                      (unit20T.map
                        (homOfLE (show unit20A ≤ ⊤ from le_top)).op)
                      ((2 : ℤ) • unit20TopTensorInT) := by
                    exact congrArg (fun w => z.down • w)
                      (hmap_underlying ((2 : ℤ) • unit20TopTensorInT))
                  _ = 0 := by
                    rw [unit20T_restrict_double_left, smul_zero]
              simp [unit20ZeroMap, unit20DoubleMap]
              exact hpresheaf.symm
            _ = _ := by
              convert hdouble_app.symm using 1
              congr 2
        · ext z
          have hrel :
              (eqToHom unit20Cover_iSup).op ≫
                  (Opens.leSupr unit20Cover (Equiv.ulift.symm 1)).op =
                (homOfLE (show unit20B ≤ ⊤ from le_top)).op := by
            change _ = (homOfLE (show unit20B ≤ ⊤ from le_top)).op
            apply Subsingleton.elim
          have hmap :
              unit20T.presheaf.map (eqToHom unit20Cover_iSup).op ≫
                  (sheafTensorProductPresheaf
                    (Formalization.Books.Sheaves.Unit17.commRingSheafMorphismToRingSheaf
                      unit20Alpha) unit20G).presheaf.map
                    (Opens.leSupr unit20Cover (Equiv.ulift.symm 1)).op =
                unit20T.presheaf.map
                  (homOfLE (show unit20B ≤ ⊤ from le_top)).op := by
            rw [← unit20T.presheaf.map_comp, hrel]
          have hzero_comp :
              unit20ZeroMap ≫
                  (unit20T.presheaf.map (eqToHom unit20Cover_iSup).op ≫
                    (sheafTensorProductPresheaf
                      (Formalization.Books.Sheaves.Unit17.commRingSheafMorphismToRingSheaf
                        unit20Alpha) unit20G).presheaf.map
                      (Opens.leSupr unit20Cover (Equiv.ulift.symm 1)).op) =
                unit20ZeroMap ≫ unit20T.presheaf.map
                  (homOfLE (show unit20B ≤ ⊤ from le_top)).op := by
            rw [hmap]
          have hdouble_comp :
              unit20DoubleMap ≫
                  (unit20T.presheaf.map (eqToHom unit20Cover_iSup).op ≫
                    (sheafTensorProductPresheaf
                      (Formalization.Books.Sheaves.Unit17.commRingSheafMorphismToRingSheaf
                        unit20Alpha) unit20G).presheaf.map
                      (Opens.leSupr unit20Cover (Equiv.ulift.symm 1)).op) =
                unit20DoubleMap ≫ unit20T.presheaf.map
                  (homOfLE (show unit20B ≤ ⊤ from le_top)).op := by
            rw [hmap]
          have hzero_app := congrArg
            (fun f : AddCommGrpCat.of (ULift.{v} ℤ) ⟶
                unit20T.presheaf.obj (op unit20B) =>
              ConcreteCategory.hom f z) hzero_comp
          have hdouble_app := congrArg
            (fun f : AddCommGrpCat.of (ULift.{v} ℤ) ⟶
                unit20T.presheaf.obj (op unit20B) =>
              ConcreteCategory.hom f z) hdouble_comp
          rw [hq]
          calc
            _ = ConcreteCategory.hom
                (unit20ZeroMap ≫ unit20T.presheaf.map
                  (homOfLE (show unit20B ≤ ⊤ from le_top)).op) z := by
              convert hzero_app using 1
              congr 2
            _ = ConcreteCategory.hom
                (unit20DoubleMap ≫ unit20T.presheaf.map
                  (homOfLE (show unit20B ≤ ⊤ from le_top)).op) z := by
              have hmap_underlying :
                  ∀ x : unit20T.obj (op (⊤ : Opens unit20X)),
                    AddCommGrpCat.Hom.hom
                        (unit20T.presheaf.map
                          (homOfLE (show unit20B ≤ ⊤ from le_top)).op) x =
                      ConcreteCategory.hom
                        (unit20T.map
                          (homOfLE (show unit20B ≤ ⊤ from le_top)).op) x := by
                intro x
                rfl
              have hpresheaf :
                  z.down • (2 : ℤ) • AddCommGrpCat.Hom.hom
                      (unit20T.presheaf.map
                        (homOfLE (show unit20B ≤ ⊤ from le_top)).op)
                      unit20TopTensorInT = 0 := by
                calc
                  _ = z.down • AddCommGrpCat.Hom.hom
                      (unit20T.presheaf.map
                        (homOfLE (show unit20B ≤ ⊤ from le_top)).op)
                      ((2 : ℤ) • unit20TopTensorInT) := by
                    rw [map_zsmul]
                  _ = z.down • ConcreteCategory.hom
                      (unit20T.map
                        (homOfLE (show unit20B ≤ ⊤ from le_top)).op)
                      ((2 : ℤ) • unit20TopTensorInT) := by
                    exact congrArg (fun w => z.down • w)
                      (hmap_underlying ((2 : ℤ) • unit20TopTensorInT))
                  _ = 0 := by
                    rw [map_zsmul, unit20T_restrict_topTensor_right]
                    simp only [smul_zero]
              simp [unit20ZeroMap, unit20DoubleMap]
              exact hpresheaf.symm
            _ = _ := by
              convert hdouble_app.symm using 1
              congr 2
      first
      | simpa only [Category.assoc] using hres
      | simpa only [Category.assoc] using congrArg
          (fun k => k ≫
            TopCat.Presheaf.SheafConditionEqualizerProducts.leftRes
              (sheafTensorProductPresheaf
                (Formalization.Books.Sheaves.Unit17.commRingSheafMorphismToRingSheaf
                  unit20Alpha) unit20G).presheaf unit20Cover) hres
  apply unit20ZeroMap_ne_unit20DoubleMap
  exact (cancel_mono q).1 hz

/-- A failed equalizer-products diagram gives the commutative-ring
counterexample in the form needed by the final theorem. -/
theorem exists_commRingSheaf_tensorProductPresheaf_not_isSheaf :
    ∃ (X : TopCat.{v})
      (O₁ O₂ : Formalization.Books.Sheaves.Unit17.CommRingSheaf X)
      (α : O₁ ⟶ O₂)
      (G : Formalization.Books.Sheaves.Unit17.CommRingSheafModule O₁),
      ¬ Presheaf.IsSheaf (Opens.grothendieckTopology X)
        (sheafTensorProductPresheaf
          (Formalization.Books.Sheaves.Unit17.commRingSheafMorphismToRingSheaf
            α) G).presheaf := by
  obtain ⟨X, O₁, O₂, α, G, U, hU⟩ :=
    exists_commRingSheaf_tensorProductPresheaf_failed_gluing
  refine ⟨X, O₁, O₂, α, G, ?_⟩
  intro hG
  apply hU
  exact (TopCat.Presheaf.isSheaf_iff_isSheafEqualizerProducts _).mp hG U

/-- Extension of scalars on sheaves of modules cannot in general be computed
without sheafifying its underlying tensor-product presheaf. -/
theorem tensorProductPresheaf_not_always_isSheaf :
    ¬ ∀ {X : TopCat.{v}}
      {O₁ O₂ : Sheaf (Opens.grothendieckTopology X) RingCat.{v}}
      (α : O₁ ⟶ O₂) (G : SheafOfModules.{v} O₁),
      Presheaf.IsSheaf (Opens.grothendieckTopology X)
        (sheafTensorProductPresheaf α G).presheaf := by
  intro h
  obtain ⟨X, O₁, O₂, α, G, hnot⟩ :=
    exists_commRingSheaf_tensorProductPresheaf_not_isSheaf
  exact hnot (h
    (Formalization.Books.Sheaves.Unit17.commRingSheafMorphismToRingSheaf α) G)

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

/-- The stalk module of a sheaf of modules over a commutative sheaf of rings. -/
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
  exact Formalization.Books.Sheaves.Unit17.stalk_tensorProductSheaf_statement α G x

end

end Formalization.Books.Sheaves.Unit20
