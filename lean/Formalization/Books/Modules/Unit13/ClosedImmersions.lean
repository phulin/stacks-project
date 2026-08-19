import Formalization.Books.Modules.Unit06.ClosedImmersions
import Formalization.Books.Modules.Unit09.FiniteType
import Formalization.Books.Modules.Unit10.QuasiCoherent
import Formalization.Books.Categories.Unit23.ExactFunctors
import Formalization.Books.Sheaves.Unit32.Infrastructure
import Formalization.Books.Sheaves.Unit26.Infrastructure
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
import Mathlib.CategoryTheory.Subobject.Limits

/-!
# Sheaves of Modules, Chapter 13: Closed immersions of ringed spaces

The canonical sheaf-module pushforward and the canonical closed-subspace
sheaf restriction are used throughout. The source's ideal is represented by
the kernel of the map from the unit module to the pushed-forward unit module.
The supported-sections construction is packaged by the largest supported
subobject and the corresponding right-adjoint interface.
-/

namespace Formalization.Books.Modules.Unit13

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace Topology
open Formalization.Books.Modules.Unit04
open Formalization.Books.Modules.Unit05
open Formalization.Books.Modules.Unit08
open Formalization.Books.Modules.Unit09
open Formalization.Books.Modules.Unit10
open Formalization.Books.Categories.Unit23
open Formalization.Books.Sheaves.Unit10
open Formalization.Books.Sheaves.Unit22

universe v

noncomputable section

/-! ## Closed immersions of ringed spaces -/

/- The kernel is taken in the category of modules over the target structure
   sheaf. `unitToPushforwardObjUnit` is Mathlib's canonical conversion of a
   morphism of sheaves of rings to the corresponding module morphism. -/

/-- The ideal sheaf cutting out a morphism of ringed spaces. -/
noncomputable def closedImmersionIdeal {X Y : RingedSpace.{v}}
    (f : RingedSpaceHom X Y) : Mod Y.structureSheaf :=
  kernel (SheafOfModules.unitToPushforwardObjUnit f.sharp)

/-- The inclusion of the ideal sheaf into the target structure sheaf. -/
noncomputable def closedImmersionIdealInclusion {X Y : RingedSpace.{v}}
    (f : RingedSpaceHom X Y) :
    closedImmersionIdeal f ⟶ SheafOfModules.unit Y.structureSheaf :=
  kernel.ι (SheafOfModules.unitToPushforwardObjUnit f.sharp)

/- A categorical epimorphism in `RingCat` need not be surjective (a
   localization is the standard counterexample).  Consequently `Epi f.sharp`
   is too weak for the quotient-by-the-kernel arguments below.  The source's
   word "surjective" is the stalkwise/local notion for a map of sheaves. -/

/-- The structure-sheaf map of a ringed-space morphism is surjective as a
sheaf map, expressed by surjectivity on every stalk. -/
def StructureSheafMapSurjective {X Y : RingedSpace.{v}}
    (f : RingedSpaceHom X Y) : Prop :=
  ∀ y : Y, Function.Surjective
    ((TopCat.Presheaf.stalkFunctor RingCat.{v} y).map f.sharp.hom)

/- The three conditions in the source definition are kept as fields so that
   later statements can use the topological, sheaf-theoretic, and local
   generation hypotheses independently. -/

/-- A closed immersion of ringed spaces in the sense of the source. -/
structure IsClosedImmersion {X Y : RingedSpace.{v}}
    (f : RingedSpaceHom X Y) : Prop where
  isClosedEmbedding : IsClosedEmbedding f.continuous
  structureSheaf_surjective : StructureSheafMapSurjective f
  ideal_locallyGenerated : locallyGenerated (closedImmersionIdeal f)

/-! ## Pushforward of quasi-coherent modules -/

/-- A module is locally a cokernel of quasi-coherent modules. -/
def IsLocallyCokernelOfQuasiCoherentModules {X : RingedSpace.{v}}
    (F : Mod X.structureSheaf) : Prop :=
  ∀ x : X, ∃ U : Opens X.carrier, x ∈ U ∧
    ∃ A B : Mod (ringedOpenSubspace X U).structureSheaf,
      IsQuasiCoherent A ∧ IsQuasiCoherent B ∧
        ∃ φ : A ⟶ B,
        Nonempty (cokernel φ ≅
            (openModuleRestrictionFunctor X U).obj F)

/-- Pushforward along a closed immersion is locally a cokernel of
quasi-coherent modules when the source module is quasi-coherent. -/
/- Proof roadmap for the `prove` stage:
   1. Use `hf.structureSheaf_surjective`, not a categorical `Epi`, throughout.
      On stalks the module map
      `SheafOfModules.unitToPushforwardObjUnit f.sharp` is a quotient map with
      kernel `closedImmersionIdeal f`.
   2. From `hf.ideal_locallyGenerated` and
      `locallyGenerated_iff_exists_free_surjection` in
      `Formalization/Books/Modules/Unit08/LocallyGenerated.lean`, obtain on a
      neighbourhood of each `y : Y` a free module surjecting onto the ideal.
      Compose with `closedImmersionIdealInclusion f`; its cokernel is the
      restricted pushforward of the unit module.  Package this presentation
      with `SheafOfModules.presentationOfIsCokernelFree` and
      `SheafOfModules.Presentation.isQuasicoherent` from
      `Mathlib/Algebra/Category/ModuleCat/Sheaf/Quasicoherent.lean`.
   3. For `y` outside the closed range, use the open complement supplied by
      `hf.isClosedEmbedding.isClosed_range`; the restricted pushforward is
      zero, hence has the zero free presentation.  For `y = f x`, apply
      `isQuasiCoherent_iff_locallyPresented` and
      `locallyPresented_has_generators_and_relations` from
      `Formalization/Books/Modules/Unit10/QuasiCoherent.lean` to `hF` at `x`.
      Shrink an ambient open `U` so that its inverse image lies in that
      presentation neighbourhood.
   4. Push the two free objects in that presentation to `U`.  Establish the
      needed local base-change isomorphism for `openModuleRestrictionFunctor`
      by comparing stalks.  Establish
      `PreservesColimitsOfSize.{v, v}` for this closed pushforward by the stalk
      computation generalized from `closedImmersion_pushforward_isExact`
      below: at image stalks it is restriction of scalars, and off the image
      it is zero.  In particular it commutes with the presentation's cokernel
      and its two possibly infinite coproducts.
   5. The pushed free objects are coproducts of the quasi-coherent pushed unit
      from step 2.  Take them as `A` and `B`, push the presentation morphism as
      `φ`, and compose the cokernel comparison with the restriction/base-change
      isomorphism to obtain the `Nonempty` isomorphism required by the goal.
   Do not try to turn `Epi f.sharp` into an underlying surjection: that is
   false for `RingCat` and was the dead end behind the old interface. -/
theorem closedImmersion_pushforward_isLocallyCokernelOfQuasiCoherentModules
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y)
    (hf : IsClosedImmersion f) (F : Mod X.structureSheaf)
    (hF : IsQuasiCoherent F) :
    IsLocallyCokernelOfQuasiCoherentModules
      ((ringedSpaceModulePushforward f).obj F) := by
  sorry

/-! ## Finite type -/

/-- Pushforward along a closed embedding of spaces with a surjective
structure-sheaf map reflects finite type. -/
/- Proof roadmap for the `prove` stage:
   Work directly with `SheafOfModules.IsFiniteType` local-generator data from
   `Mathlib/Algebra/Category/ModuleCat/Sheaf/Generators.lean`.
   For the right-to-left implication, a point outside
   `Set.range f.continuous` has a neighbourhood on which the pushforward is
   zero.  At `f x`, transport a finite generating family for `F` to an
   ambient open and use `hsurj (f x)` to lift the scalar action from the
   target stalk; this is precisely where mere categorical epimorphy is
   insufficient.  For the left-to-right implication, restrict finite
   generators of the pushforward to the inverse-image open; the
   closed-embedding stalk comparison identifies the resulting stalks with
   those of `F`.  In both directions assemble a
   `SheafOfModules.LocalGeneratorsData`, retaining the same finite index type,
   and discharge epimorphy of the free map stalkwise.  The useful downstream
   checks are `finiteType_surjective_on_stalk` and `finiteType_stalk_zero` in
   `Formalization/Books/Modules/Unit09/FiniteType.lean`; they may shorten the
   neighbourhood-shrinking steps, but neither supplies the missing scalar
   surjectivity. -/
theorem closedImmersion_pushforward_finiteType_iff
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y)
    (hclosed : IsClosedEmbedding f.continuous)
    (hsurj : StructureSheafMapSurjective f)
    (F : Mod X.structureSheaf) :
    finiteType ((ringedSpaceModulePushforward f).obj F) ↔ finiteType F := by
  sorry

/-! ## The module-category equivalence -/

/- The sectionwise formulation is a usable module-theoretic spelling of
   `I G = 0`: every local section of the ideal acts by zero on every local
   section of `G`. -/

/-- A sheaf of modules is annihilated by a submodule of the structure sheaf. -/
def sheafModuleAnnihilatedBy {X : RingedSpace.{v}}
    {I G : Mod X.structureSheaf}
    (ι : I ⟶ SheafOfModules.unit X.structureSheaf) : Prop :=
  ∀ U : Opens X.carrier,
    ∀ i : (I.val.obj (op U)), ∀ g : (G.val.obj (op U)),
      (let a : X.structureSheaf.obj.obj (op U) :=
        (ι.val.app (op U)).hom i
       a • g) = 0

/-- The essential-image predicate for a closed-immersion pushforward. -/
def IsInClosedImmersionPushforwardEssentialImage
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y)
    (G : Mod Y.structureSheaf) : Prop :=
  sheafModuleAnnihilatedBy (G := G)
    (closedImmersionIdealInclusion f)

/-- The module pushforward along a closed immersion is exact. -/
/- Proof roadmap for the `prove` stage:
   `sheafModuleRingedSpacePushforward_isLeftExact` in
   `Formalization/Books/Modules/Unit03/AbelianCategory.lean` gives the finite
   limit half for every ringed-space morphism.  For finite colimits, compare
   the canonical colimit map on every target stalk.  If the point is outside
   the closed range, choose a disjoint neighbourhood and identify all
   pushforward stalks with zero.  At a point in the range, use the inducing
   homeomorphism to identify the pushforward stalk with the source stalk,
   with scalars restricted along the stalk ring map.  Then invoke
   `ModuleCat.preservesColimit_restrictScalars` from
   `Mathlib/Algebra/Category/ModuleCat/ChangeOfRings.lean`.  Stalk functors
   preserve the relevant finite colimits and jointly detect isomorphisms, so
   the comparison is an isomorphism.  Package this as
   `PreservesFiniteColimits (ringedSpaceModulePushforward f)` and pair it with
   the existing left-exact result.  No hypothesis on `f.sharp` is used or
   needed; exactness only depends on the closed topological embedding. -/
theorem closedImmersion_pushforward_isExact
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y)
    (hclosed : IsClosedEmbedding f.continuous) :
    IsExact (ringedSpaceModulePushforward f) := by
  sorry

/-- The module pushforward along a closed immersion is fully faithful. -/
/- Proof roadmap for the `prove` stage:
   Let `adj := ringedSpaceModuleAdjunction f` from
   `Formalization/Books/Sheaves/Unit26/Infrastructure.lean`.  Prove
   `IsIso adj.counit` by `NatTrans.isIso_iff_isIso_app`, and prove each app is
   an isomorphism stalkwise.  At `x : X`, combine the inducing-map comparison
   `TopCat.Presheaf.stalkPushforward...stalkPushforward_iso_of_isInducing`
   (`Mathlib/Topology/Sheaves/Stalks.lean`) with
   `ringedSpaceModulePullback_stalk_formula` from Unit26.  The scalar map on
   this stalk is surjective by `hsurj (f x)`, so if `B` is the target stalk
   ring and `M` a `B`-module, the counit `B ⊗_A M → M` has inverse
   `m ↦ 1 ⊗ m`; prove well-definedness by choosing a preimage in `A` for
   each `b : B`.  Use `TopCat.Presheaf.isIso_of_stalkFunctor_map_iso` to return
   from stalks to sheaves of modules.  Finally return
   `⟨adj.fullyFaithfulROfIsIsoCounit⟩`.  A proof using only
   `Epi f.sharp` would establish a different ring-epimorphism statement and
   must not be reused for the quotient calculation needed next. -/
theorem closedImmersion_pushforward_fullyFaithful
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y)
    (hclosed : IsClosedEmbedding f.continuous)
    (hsurj : StructureSheafMapSurjective f) :
    Nonempty (ringedSpaceModulePushforward f).FullyFaithful := by
  sorry

/-- The essential image of a closed-immersion pushforward consists precisely
of modules annihilated by the ideal sheaf. -/
/- Proof roadmap for the `prove` stage:
   First obtain `ff` from `closedImmersion_pushforward_fullyFaithful f hclosed
   hsurj` and install its `Full` and `Faithful` instances.
   * If `G ≅ f_* F`, the composite from `closedImmersionIdeal f` to the
     pushed unit is zero by `kernel.condition`; naturality of the module action
     then shows sectionwise that the ideal kills `f_* F`, and transport this
     property across the displayed isomorphism.
   * Conversely set `L := ringedSpaceModulePullback f` and use
     `(ringedSpaceModuleAdjunction f).unit.app G`.  Prove this unit is an
     isomorphism on each stalk.  Stalk functors preserve the kernel defining
     `closedImmersionIdeal`; hence `hsurj y` identifies the pushed structure
     stalk with the quotient of the ambient stalk by that kernel.  The
     sectionwise annihilation hypothesis passes to germs, so the standard map
     `G_y → G_y ⊗_{O_{Y,y}} O_{X,x}` is an isomorphism at points of the
     range.  Off the range the pushed structure stalk is the zero ring; its
     surjective structure map has unit in the kernel, so the same annihilation
     hypothesis forces `G_y` to be zero.  Use the closed-pushforward stalk
     comparison and `TopCat.Presheaf.isIso_of_stalkFunctor_map_iso` to finish.
   Apply `Adjunction.isIso_unit_app_iff_mem_essImage` from
   `Mathlib/CategoryTheory/Adjunction/FullyFaithful.lean`, or simply take
   `F := L.obj G` and the inverse of the unit, for the final existential.
   The quotient step explains why the repaired stalk-surjectivity hypothesis
   is essential: kernel annihilation does not characterize modules over a
   general categorical ring epimorphism such as a localization. -/
theorem closedImmersion_pushforward_essentialImage
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y)
    (hclosed : IsClosedEmbedding f.continuous)
    (hsurj : StructureSheafMapSurjective f)
    (G : Mod Y.structureSheaf) :
    (∃ F, Nonempty ((ringedSpaceModulePushforward f).obj F ≅ G)) ↔
      IsInClosedImmersionPushforwardEssentialImage f G := by
  sorry

/-! ## Sections with support in a closed subset -/

/-- The ringed space on a closed subspace with the restricted structure sheaf. -/
noncomputable def ringedClosedSubspace (X : RingedSpace.{v}) (Z : Set X) :
    RingedSpace.{v} where
  carrier := Formalization.Books.Sheaves.Unit22.closedSubspace Z
  structureSheaf :=
    (TopCat.Sheaf.pullback RingCat
      (Formalization.Books.Sheaves.Unit22.closedInclusion Z)).obj X.structureSheaf

/-- The canonical morphism from the ringed closed subspace to the ambient
ringed space. -/
noncomputable def ringedClosedInclusion (X : RingedSpace.{v}) (Z : Set X) :
    RingedSpaceHom (ringedClosedSubspace X Z) X where
  continuous := Formalization.Books.Sheaves.Unit22.closedInclusion Z
  sharp :=
    (TopCat.Sheaf.pullbackPushforwardAdjunction RingCat
      (Formalization.Books.Sheaves.Unit22.closedInclusion Z)).unit.app X.structureSheaf

/-- The restricted structure sheaf gives the closed embedding and surjective
structure map needed to view supported modules on the closed subspace.

It is deliberately not asserted to be an `IsClosedImmersion`: for an
arbitrary ringed space and closed set, the kernel ideal need not be locally
generated. -/
/- Proof roadmap for the `prove` stage:
   For the first component, unfold `ringedClosedInclusion` and use
   `hZ.isClosedEmbedding_subtypeVal`.  For stalkwise surjectivity, unfold
   `StructureSheafMapSurjective` and split on `y ∈ Z`.  If `y ∈ Z`, use the
   unit-stalk computation underlying
   `closedSubsetPushforward_inverseImage_counit_isIso` and
   `closedSubsetStructure_inverseImagePushforwardIso` in
   `Formalization/Books/Sheaves/Unit32/ClosedImmersions.lean`: the unit map at
   `y` followed by `closedSubsetPushforward_stalkIso` is the pullback-stalk
   isomorphism.  If `y ∉ Z`, use
   `closedAlgebraicSheafDirectImage_stalk_outside` from
   `Formalization/Books/Sheaves/Unit32/Infrastructure.lean` with
   `C := RingCat.{v}`; the target is the terminal (zero) ring, so the unique
   map to it is surjective.  The sharp map is definitionally the same unit
   after unfolding `ringedClosedInclusion` and `ringedClosedSubspace`.
   Do not attempt to fill a local-generation field: the source applies the
   two-hypothesis equivalence theorem here, not its stronger special
   definition of closed immersion. -/
theorem ringedClosedInclusion_isClosedEmbedding_and_surjective
    (X : RingedSpace.{v}) (Z : Set X) (hZ : IsClosed Z) :
    IsClosedEmbedding (ringedClosedInclusion X Z).continuous ∧
      StructureSheafMapSurjective (ringedClosedInclusion X Z) := by
  sorry

/-- A module section is supported in a closed subset. -/
def moduleSectionSupportedInClosed {X : RingedSpace.{v}} (Z : Set X)
    {F : Mod X.structureSheaf} (U : Opens X.carrier)
    (s : F.val.obj (op U)) : Prop :=
  sectionSupport U s ⊆
    Formalization.Books.Modules.Unit06.closedSubsetInOpen Z U

/-- The sections of a module supported in a closed subset. -/
def moduleSectionsWithSupportInClosed {X : RingedSpace.{v}} (Z : Set X)
    {F : Mod X.structureSheaf} (U : Opens X.carrier) :
    Set (F.val.obj (op U)) :=
  {s | moduleSectionSupportedInClosed Z U s}

/- The source observes that these sections are closed under the module
   operations.  The closure proof is deferred with the other proposition
   proofs, while the sectionwise submodule interface is made explicit. -/

/-- The sections supported in `Z` form a submodule on every open. -/
/- Proof roadmap for the `prove` stage:
   Refine a `Submodule` whose carrier is
   `moduleSectionsWithSupportInClosed Z U`.  The zero clause follows because
   `sectionSupport U 0` is empty (unfold `sectionSupport`/`sectionGerm` and
   use `map_zero`).  For addition, apply `add_sectionSupport_subset` from
   `Formalization/Books/Modules/Unit05/Supports.lean`; each summand support is
   contained in `closedSubsetInOpen Z U`, so the union is.  For scalar
   multiplication apply `smul_sectionSupport_subset` from the same file and
   compose its inclusion into the second factor with the hypothesis for the
   section.  Close with `rfl` for the carrier equality.  No closedness
   hypothesis on `Z` is required for these three algebraic closure checks. -/
theorem moduleSectionsWithSupportInClosed_isSubmodule
    {X : RingedSpace.{v}} (Z : Set X)
    {F : Mod X.structureSheaf} (U : Opens X.carrier) :
    ∃ S : Submodule (X.structureSheaf.obj.obj (op U))
        (F.val.obj (op U)),
      S.carrier = moduleSectionsWithSupportInClosed Z U := by
  sorry

/- The sectionwise module in the source is represented by the canonical
   submodule selected from the preceding closure statement. -/

/-- The submodule of sections supported in `Z` on an open subset. -/
noncomputable def moduleSectionsWithSupportInClosedSubmodule
    {X : RingedSpace.{v}} (Z : Set X)
    {F : Mod X.structureSheaf} (U : Opens X.carrier) :
    Submodule (X.structureSheaf.obj.obj (op U)) (F.val.obj (op U)) :=
  Classical.choose
    (moduleSectionsWithSupportInClosed_isSubmodule (F := F) Z U)

/-- The selected supported-section submodule has the source's carrier. -/
theorem moduleSectionsWithSupportInClosedSubmodule_carrier
    {X : RingedSpace.{v}} (Z : Set X)
    {F : Mod X.structureSheaf} (U : Opens X.carrier) :
    (moduleSectionsWithSupportInClosedSubmodule (F := F) Z U).carrier =
      moduleSectionsWithSupportInClosed (F := F) Z U :=
  Classical.choose_spec
    (moduleSectionsWithSupportInClosed_isSubmodule (F := F) Z U)

/-- A module subobject contains a section when that section lifts to it. -/
def moduleSubsheafContainsSection {X : RingedSpace.{v}}
    {F : Mod X.structureSheaf} (P : Subobject F) (U : Opens X.carrier)
    (s : F.val.obj (op U)) : Prop :=
  ∃ t : ((P : Mod X.structureSheaf).val.obj (op U)),
    P.arrow.val.app (op U) t = s

/-- Support containment for a sheaf of modules. -/
def moduleSupportContainedIn {X : RingedSpace.{v}} (Z : Set X)
    (F : Mod X.structureSheaf) : Prop :=
  moduleSupport F ⊆ Z

/-- There is a largest module subsheaf whose support is contained in `Z`. -/
/- Proof roadmap for the `prove` stage:
   Port the kernel-on-the-open-complement construction in
   `exists_closedSupportSubsheaf` from
   `Formalization/Books/Modules/Unit06/ClosedImmersions.lean`, keeping the
   module structure instead of forgetting to abelian sheaves.
   1. Put `Uc : Opens X := ⟨Zᶜ, hZ.isOpen_compl⟩`, let
      `j := ringedOpenInclusion X Uc`, and form the unit
      `η : F ⟶ (ringedSpaceModulePushforward j).obj
        ((openModuleRestrictionFunctor X Uc).obj F)` from
      `ringedSpaceModuleAdjunction j` in
      `Formalization/Books/Sheaves/Unit26/Infrastructure.lean`.  If inference
      needs the open-specific right-adjoint instance, reuse the construction
      inside `openModuleRestrictionFunctor` in
      `Formalization/Books/Sheaves/Unit31/Infrastructure.lean`.
   2. Set `P := kernelSubobject η`.  For `x ∉ Z`, the open-pullback unit is
      an isomorphism on the `x`-stalk.  Combine the pullback stalk formula from
      Unit26 with `TopCat.Presheaf.stalk_mono_of_mono` and
      `kernelSubobject_arrow_comp` to show the stalk of `P` is zero.  This
      gives `moduleSupportContainedIn Z (P : Mod _)`.
   3. Given `Q` supported in `Z`, its restriction to `Uc` has all stalks zero,
      hence is a zero module sheaf.  Therefore `Q.arrow ≫ η = 0`; apply
      `le_kernelSubobject η Q` to get `Q ≤ P`.
   4. Return `⟨P, support, maximality⟩`.
   The direct port should use `moduleStalkFunctor` from Unit26 at module-valued
   steps; use `SheafOfModules.forget` only to invoke the established
   AddCommGrp-valued stalk-isomorphism detector. -/
theorem exists_closedSupportModuleSubsheaf {X : RingedSpace.{v}} (Z : Set X)
    (hZ : IsClosed Z) (F : Mod X.structureSheaf) :
    ∃ P : Subobject F,
      moduleSupportContainedIn Z (P : Mod X.structureSheaf) ∧
        ∀ Q : Subobject F,
          moduleSupportContainedIn Z (Q : Mod X.structureSheaf) → Q ≤ P := by
  sorry

/-- The canonical largest module subsheaf supported in `Z`. -/
noncomputable def closedSupportModuleSubsheaf {X : RingedSpace.{v}}
    (Z : Set X) (hZ : IsClosed Z) (F : Mod X.structureSheaf) : Subobject F :=
  Classical.choose (exists_closedSupportModuleSubsheaf Z hZ F)

/-- The canonical supported module subsheaf has support in `Z`. -/
theorem closedSupportModuleSubsheaf_supportContainedIn
    {X : RingedSpace.{v}} (Z : Set X) (hZ : IsClosed Z)
    (F : Mod X.structureSheaf) :
    moduleSupportContainedIn Z
      (closedSupportModuleSubsheaf Z hZ F : Mod X.structureSheaf) := by
  exact (Classical.choose_spec (exists_closedSupportModuleSubsheaf Z hZ F)).1

/-- The canonical supported module subsheaf is largest among supported
subsheaves. -/
theorem closedSupportModuleSubsheaf_isLargest
    {X : RingedSpace.{v}} (Z : Set X) (hZ : IsClosed Z)
    (F : Mod X.structureSheaf) (Q : Subobject F)
    (hQ : moduleSupportContainedIn Z (Q : Mod X.structureSheaf)) :
    Q ≤ closedSupportModuleSubsheaf Z hZ F := by
  exact (Classical.choose_spec (exists_closedSupportModuleSubsheaf Z hZ F)).2 Q hQ

/-- A section belongs to the canonical supported submodule exactly when it is
supported in `Z`. -/
/- Proof roadmap for the `prove` stage:
   Follow `closedSupportSubsheaf_section_iff` in
   `Formalization/Books/Modules/Unit06/ClosedImmersions.lean`.
   * For a lift `t` through the subobject arrow, take `x` outside `Z`.
     `closedSupportModuleSubsheaf_supportContainedIn` says the source stalk is
     subsingleton.  Naturality of germs, via
     `TopCat.Presheaf.stalkFunctor_map_germ_apply`, sends the zero germ of `t`
     to the germ of `s`, contradicting membership in `sectionSupport U s`.
   * Conversely assume the support containment.  Recreate the complement
     unit `η` and its kernel `K` from the proof of
     `exists_closedSupportModuleSubsheaf`.  Sheaf section extensionality plus
     `TopCat.Presheaf.pullbackPushforwardAdjunction_unit_app_app_germToPullbackStalk`
     shows `η.val.app (op U) s = 0`.  Evaluate the kernel diagram at `op U`;
     `SheafOfModules.forget` preserves limits, and the evaluation functor
     preserves them, so `PreservesKernel.iso` identifies `K(U)` with the
     ordinary kernel.  Use `kernel.lift` on the cyclic map generated by `s`
     (the Unit06 proof uses `AddCommGrpCat.of (ULift.{v} ℤ)`) to obtain a
     section `tK` mapping to `s`.
   * The support proof for `K` and
     `closedSupportModuleSubsheaf_isLargest` give `K ≤` the chosen largest
     subobject.  Map `tK` along `Subobject.ofLE` and use
     `Subobject.ofLE_arrow` to produce the required lift.
   Keep the `ULift.{v}` generator in the evaluation argument; using plain
   `ℤ` causes the universe mismatch recorded in the abelian template. -/
theorem closedSupportModuleSubsheaf_section_iff
    {X : RingedSpace.{v}} (Z : Set X) (hZ : IsClosed Z)
    (F : Mod X.structureSheaf) (U : Opens X.carrier)
    (s : F.val.obj (op U)) :
    moduleSubsheafContainsSection
      (closedSupportModuleSubsheaf Z hZ F) U s ↔
      s ∈ moduleSectionsWithSupportInClosed Z U := by
  sorry

/-! ## The supported-sections right adjoint -/

/-- The module-valued supported-sections functor exists as the right adjoint
to closed direct image. -/
/- Proof roadmap for the `prove` stage:
   This is the module analogue of the construction in the private theorem
   `closedSupport_canonical_exists` in
   `Formalization/Books/Modules/Unit06/ClosedImmersions.lean`.
   1. Let `i := ringedClosedInclusion X Z`, `R :=
      ringedSpaceModulePushforward i`, and use
      `ringedClosedInclusion_isClosedEmbedding_and_surjective X Z hZ` with
      `closedImmersion_pushforward_fullyFaithful` to obtain `R.FullyFaithful`.
      The latter theorem needs exactly the two components of the repaired
      interface; it does not require local generation of the closed-set ideal.
   2. Define the object assignment
      `vObj F := (ringedSpaceModulePullback i).obj
        (closedSupportModuleSubsheaf Z hZ F : Mod _)`.  Show that the unit
      `u F : P(F) ⟶ R.obj (vObj F)` is an isomorphism.  At points of `Z`, use
      the quotient-tensor calculation from
      `closedImmersion_pushforward_fullyFaithful`; off `Z`, both stalks vanish
      by `closedSupportModuleSubsheaf_supportContainedIn` and the closed
      pushforward outside-stalk calculation.  Detect the isomorphism stalkwise.
   3. For `α : R.obj G ⟶ F`, every local section in its source has support
      in `Z` (use the closed-pushforward stalk comparison from
      `Formalization/Books/Sheaves/Unit32/ClosedImmersions.lean`).  By
      `closedSupportModuleSubsheaf_section_iff`, `α` factors uniquely through
      the mono `(closedSupportModuleSubsheaf Z hZ F).arrow`; call the factor
      `factor α`.  It can equivalently be built through the complement kernel
      using `factorThruKernelSubobject`, `Subobject.ofLE`, and
      `Subobject.ofLE_arrow` from Mathlib's subobject limits API.
   4. Define the Hom equivalence
      `(R.obj G ⟶ F) ≃ (G ⟶ vObj F)`: forward is the fully-faithful
      preimage of `factor α ≫ u F`; backward sends `β` to
      `R.map β ≫ inv (u F) ≫ P(F).arrow`.  Prove the inverse laws by
      cancelling the subobject mono and using `FullyFaithful.map_preimage`.
      Prove naturality in `G` exactly as in the Unit06 template.
   5. Apply `Adjunction.rightAdjointOfEquiv` and
      `Adjunction.adjunctionOfEquivRight` from
      `Mathlib/CategoryTheory/Adjunction/Basic.lean`.  The isomorphism in the
      second conjunct is `(asIso (u F)).symm`.  Use explicit universe `v` for
      both module categories so the Hom equivalence does not lift to `v+1`. -/
theorem exists_moduleSectionsWithSupportFunctor
    (X : RingedSpace.{v}) (Z : Set X) (hZ : IsClosed Z) :
    ∃ H : Mod X.structureSheaf ⥤
        Mod (ringedClosedSubspace X Z).structureSheaf,
      Nonempty (ringedSpaceModulePushforward (ringedClosedInclusion X Z) ⊣ H) ∧
        ∀ F : Mod X.structureSheaf,
          Nonempty ((ringedSpaceModulePushforward
            (ringedClosedInclusion X Z)).obj (H.obj F) ≅
            (closedSupportModuleSubsheaf Z hZ F : Mod X.structureSheaf)) := by
  sorry

/-- The sheaf of modules of sections supported in `Z`, viewed on the closed
subspace. -/
noncomputable def moduleSectionsWithSupportFunctor
    (X : RingedSpace.{v}) (Z : Set X) (hZ : IsClosed Z) :
    Mod X.structureSheaf ⥤ Mod (ringedClosedSubspace X Z).structureSheaf :=
  Classical.choose (exists_moduleSectionsWithSupportFunctor X Z hZ)

/-- The chosen supported-sections functor is right adjoint to closed direct
image. -/
noncomputable def moduleSectionsWithSupportFunctor_adjunction
    (X : RingedSpace.{v}) (Z : Set X) (hZ : IsClosed Z) :
    ringedSpaceModulePushforward (ringedClosedInclusion X Z) ⊣
      moduleSectionsWithSupportFunctor X Z hZ :=
  Classical.choice
    (Classical.choose_spec (exists_moduleSectionsWithSupportFunctor X Z hZ)).1

/- The source displays the adjunction as the corresponding Hom equivalence;
   expose that usable interface alongside the chosen adjunction. -/

/-- The Hom correspondence for sections supported in `Z`. -/
noncomputable abbrev moduleSectionsWithSupportFunctor_homEquiv
    (X : RingedSpace.{v}) (Z : Set X) (hZ : IsClosed Z)
    (G : Mod (ringedClosedSubspace X Z).structureSheaf)
    (F : Mod X.structureSheaf) :
    ((ringedSpaceModulePushforward (ringedClosedInclusion X Z)).obj G ⟶ F) ≃
      (G ⟶ (moduleSectionsWithSupportFunctor X Z hZ).obj F) :=
  (moduleSectionsWithSupportFunctor_adjunction X Z hZ).homEquiv G F

/-- The chosen right adjoint realizes the largest supported submodule. -/
theorem moduleSectionsWithSupportFunctor_obj_iso
    (X : RingedSpace.{v}) (Z : Set X) (hZ : IsClosed Z)
    (F : Mod X.structureSheaf) :
    Nonempty ((ringedSpaceModulePushforward
      (ringedClosedInclusion X Z)).obj
        ((moduleSectionsWithSupportFunctor X Z hZ).obj F) ≅
      (closedSupportModuleSubsheaf Z hZ F : Mod X.structureSheaf)) := by
  exact (Classical.choose_spec
    (exists_moduleSectionsWithSupportFunctor X Z hZ)).2 F

/-- The supported-sections functor is left exact. -/
/- Proof roadmap for the `prove` stage:
   Unfold `IsLeftExact` to `PreservesFiniteLimits`.  The adjunction
   `moduleSectionsWithSupportFunctor_adjunction X Z hZ` makes this functor a
   right adjoint, so
   `Adjunction.rightAdjoint_preservesLimits` from
   `Mathlib/CategoryTheory/Adjunction/Limits.lean` supplies
   `PreservesLimitsOfSize.{v, v}`.  Restrict that instance to each finite
   indexing category (or construct the `PreservesFiniteLimits` record using
   `.preservesLimitsOfShape`).  No exactness or full-faithfulness theorem is
   required at this point. -/
theorem moduleSectionsWithSupportFunctor_isLeftExact
    (X : RingedSpace.{v}) (Z : Set X) (hZ : IsClosed Z) :
    IsLeftExact (moduleSectionsWithSupportFunctor X Z hZ) := by
  sorry

/-- The source's warning that supported sections are not exact in general. -/
def AllModuleSupportedSectionsFunctorsExact : Prop :=
  ∀ (X : RingedSpace.{v}) (Z : Set X) (hZ : IsClosed Z),
    IsExact (moduleSectionsWithSupportFunctor X Z hZ)

theorem not_allModuleSupportedSectionsFunctorsExact :
    ¬ AllModuleSupportedSectionsFunctorsExact := by
  /- Proof roadmap for the `prove` stage:
     Give an explicit Sierpiński-space counterexample; an abstract appeal to
     "not exact in general" has no usable witness.
     1. Use the two-point Sierpiński topology (Mathlib's topology on `Prop`,
        lifted to `ULift.{v} Prop` if needed), with open generic point `True`
        and closed point `Z := {False}`.  Let the structure ring sheaf be the
        constant sheaf `ℤ`, constructed by `CategoryTheory.constantSheaf`
        (`Mathlib/CategoryTheory/Sites/ConstantSheaf.lean`), and form the
        corresponding `RingedSpace.{v}`.  On this space a constant section is
        determined by its germ at `True`.
     2. Let `A` be the unit module on `X`.  On the one-point closed subspace,
        let `K` be the cokernel of multiplication by `2` on the unit module;
        its unique stalk is `ZMod 2` and is nonzero.  Put
        `B := (ringedSpaceModulePushforward (ringedClosedInclusion X Z)).obj K`.
        The quotient map on the closed point, transposed/pushed forward, gives
        `p : A ⟶ B`.  Check `Epi p` stalkwise: it is `ℤ → ZMod 2` at the
        closed point and the map to the zero stalk at the generic point.
     3. Use `closedSupportModuleSubsheaf_section_iff` to show the largest
        `Z`-supported subobject of `A` is zero: a nonzero constant section has
        nonzero germ at `True`.  The same theorem and the closed-pushforward
        stalk description show the largest supported subobject of `B` is all
        of `B`, which is nonzero.
     4. Transport these identifications through
        `moduleSectionsWithSupportFunctor_obj_iso`.  If the chosen supported
        functor were exact, its `PreservesFiniteColimits` component would
        preserve the cokernel/epimorphism `p` (use
        `preservesEpimorphisms_of_preservesColimitsOfShape` from
        `Mathlib/CategoryTheory/Limits/Constructions/EpiMono.lean`).  Its image
        instead has zero source and nonzero target, hence is not epi.
        Contradiction.
     Finally specialize the assumed `AllModuleSupportedSectionsFunctorsExact`
     to this `X`, `Z`, and its proof of closedness.  Keep `ULift.{v}` on the
     two points and on any finite diagram indices to avoid a universe-level
     mismatch. -/
  sorry

end

end Formalization.Books.Modules.Unit13
