import Formalization.Books.Modules.Unit08.LocallyGenerated
import Formalization.Books.Sheaves.Unit25.Infrastructure
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import Mathlib.CategoryTheory.Sites.GlobalSections

/-!
# Sheaves of Modules, Chapter 10: Quasi-coherent modules

This file follows the source section `Quasi-coherent modules`.  The ambient
categories, open restrictions, free sheaves, cokernels, pullbacks, and
sheafification are the canonical constructions from the preceding modules
chapters and Mathlib.
-/

namespace Formalization.Books.Modules.Unit10

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Formalization.Books.Modules.Unit03
open Formalization.Books.Modules.Unit04
open Formalization.Books.Modules.Unit08
open Formalization.Books.Sheaves.Unit10
open Formalization.Books.Sheaves.Unit22
open scoped BigOperators

universe v

noncomputable section

local notation "Mod" => Formalization.Books.Sheaves.Unit10.Mod

/-! ## The definition and its exact presentation -/

/-- A free-cokernel presentation after transporting a module to the ringed
open subspace.  This is the source-facing form used by the explicit cokernel
statements below; `HasLocalPresentation` uses Mathlib's native `F.over U`
instead. -/
def hasPresentationOn {X : RingedSpace.{v}} (F : Mod X.structureSheaf)
    (U : Opens X.carrier) : Prop :=
  Nonempty (((openModuleRestrictionFunctor X U).obj F).Presentation)

/-- The source definition of quasi-coherence, using Mathlib's canonical
presentation data for sheaves of modules. -/
abbrev IsQuasiCoherent {X : RingedSpace.{v}} (F : Mod X.structureSheaf) : Prop :=
  SheafOfModules.IsQuasicoherent F

/-- The pointwise local-presentation formulation used in the source's
explanation of quasi-coherence. The underlying presentation is Mathlib's
canonical `SheafOfModules.Presentation`, whose generators present the module
and whose relations generate the kernel of the associated epimorphism. -/
def HasLocalPresentation {X : RingedSpace.{v}} (F : Mod X.structureSheaf) : Prop :=
  ∀ x : X, ∃ U : Opens X.carrier, x ∈ U ∧ Nonempty ((F.over U).Presentation)

/- The source calls this condition “locally presented” immediately after the
definition of quasi-coherence. -/
abbrev LocallyPresented {X : RingedSpace.{v}} (F : Mod X.structureSheaf) : Prop :=
  HasLocalPresentation F

/-- The full subcategory denoted by `QCoh(O_X)`. -/
abbrev QCoh (X : RingedSpace.{v}) :=
  ObjectProperty.FullSubcategory
    (fun F : Mod X.structureSheaf => IsQuasiCoherent F)

/-- The opening warning that quasi-coherent sheaves need not form an abelian
category in the generality of ringed spaces. -/
def AllQuasiCoherentCategoriesAbelian : Prop :=
  ∀ X : RingedSpace.{v}, Nonempty (Abelian (QCoh X))

theorem not_all_quasiCoherentCategoriesAbelian :
    ¬ AllQuasiCoherentCategoriesAbelian := by
  /-
  Roadmap/blocker for the prove stage:
  * The statement is the source's warning and is mathematically sound, but a
    proof must start from an actual categorical counterexample
      `∃ X : RingedSpace.{v}, IsEmpty (Abelian (QCoh X))`.
    No such declaration is presently available in Mathlib or in the earlier
    project modules.  In particular, merely showing that an ambient kernel is
    not quasi-coherent does not by itself refute an `Abelian (QCoh X)`
    instance: one must also rule out a kernel object having the universal
    property internal to the full subcategory.
  * The intended counterexample is `exists_wedgeOfLinesExample` below.  Its
    two free sheaves are quasi-coherent by giving each the tautological
    presentation and applying `SheafOfModules.Presentation.isQuasicoherent`.
    The key intermediate lemma to prove is that no
    `K : QCoh E.X` and `k : K.obj ⟶ SheafOfModules.free CountableIndex`
    can satisfy the kernel universal property for `E.map`: localize a
    presentation of `K`, apply that universal property to the free
    generators, and use `E.no_local_matrix` to contradict the resulting
    finite column support.  This proves nonexistence of a kernel internal to
    `QCoh E.X`, not just non-quasi-coherence of the ambient kernel.
  * Given that lemma, an assumed `Abelian (QCoh E.X)` supplies the internal
    kernel via `kernel.ι` and `limit.isLimit`; specialize the lemma to those
    data for the contradiction.
  * Once a counterexample `⟨X, hX⟩` is formalized, finish by introducing
    `h : AllQuasiCoherentCategoriesAbelian` and applying
    `hX.false (h X).some`.  Keep `X` in universe `v`; a small counterexample
    may need an explicit universe lift before it can discharge this
    universe-polymorphic theorem.  At present there is also no earlier API
    lifting a `RingedSpace.{0}`, its module category, and the internal-kernel
    obstruction coherently to `RingedSpace.{v}`; either generalize the wedge
    construction to `v` or add that focused lift before the final step.
  Do not retry typeclass search for a nonexistent negative `Abelian` instance;
  the missing input is the counterexample itself.
  -/
  sorry

theorem isQuasiCoherent_iff_locallyPresented
    {X : RingedSpace.{v}} (F : Mod X.structureSheaf) :
    IsQuasiCoherent F ↔ LocallyPresented F := by
  /-
  Proof roadmap (all cited site/module universes specialize to `v`):
  * Forward: unpack
    `SheafOfModules.IsQuasicoherent.nonempty_quasicoherentData` to
    `q : SheafOfModules.QuasicoherentData.{v} F`.  Its fields are
    `q.X : q.I → Opens X.carrier`,
    `q.coversTop : (Opens.grothendieckTopology X.carrier).CoversTop q.X`,
    and `q.presentation i : (F.over (q.X i)).Presentation`.
  * Apply `Opens.coversTop_iff q.X` from
    `Mathlib/CategoryTheory/Sites/Spaces.lean` to `q.coversTop`.  The resulting
    `hcover : TopologicalSpace.IsOpenCover q.X` is the equality
    `iSup q.X = ⊤`; rewrite by it and use `Opens.mem_iSup.mp` to obtain, for
    each `x : X`, an `i : q.I` with `x ∈ q.X i`.  Return `U := q.X i` and
    `⟨q.presentation i⟩`.
  * Reverse: use classical choice on the pointwise hypothesis to obtain
    `U : X → Opens X.carrier`, membership `hx : ∀ x, x ∈ U x`, and
    `hP : ∀ x, Nonempty ((F.over (U x)).Presentation)`; put
    `P x := (hP x).some`.  Build
    `q : SheafOfModules.QuasicoherentData.{v} F` with index type `X`, open
    family `U`, presentations `P`, and prove `q.coversTop` via the reverse
    implication of `Opens.coversTop_iff U`.  For its
    `iSup U = ⊤` goal use `eq_top_iff` and `Opens.mem_iSup.mpr ⟨x, hx x⟩`
    pointwise.
  * Finish with `SheafOfModules.QuasicoherentData.isQuasicoherent q` from
    `Mathlib/Algebra/Category/ModuleCat/Sheaf/Quasicoherent.lean`.
  This native `F.over U` formulation deliberately avoids the unrelated
  open-subspace restriction comparison that blocked the previous proof.
  -/
  sorry

/-
Roadmap/blocker for transporting the native local presentation to the older
ringed-open-subspace interface:
* Given `P : (F.over U).Presentation`, first use
  `SheafOfModules.Presentation.map` from
  `Mathlib/Algebra/Category/ModuleCat/Sheaf/Quasicoherent.lean` with the
  equivalence functor `(U.sheafOfModulesEquivOver X.structureSheaf).functor`
  and `U.sheafOfModulesEquivOverUnit X.structureSheaf`; these are in
  `Mathlib/Topology/Sheaves/Module.lean`.  This produces a presentation of
  the equivalence image of `F.over U`.
* Transport that presentation with `SheafOfModules.Presentation.ofIsIso`
  along `openModuleRestrictionObjIso U X.structureSheaf F` from
  `Formalization/Books/Sheaves/Unit24/Infrastructure.lean`.
* The remaining interface obligation is not a presentation argument: the
  comparison lemma requires
  `[(openModuleRestrictionDirectImage U X.structureSheaf).IsRightAdjoint]`
  and lands in that functor's chosen `leftAdjoint.obj F`, while the target is
  `(openModuleRestrictionFunctor X U).obj F`.  The current Unit31 restriction
  definition hides its local right-adjoint witness and exports no iso making
  these two chosen left adjoints equal.  Supply that focused functor/object
  iso upstream, or expose the witness, before completing this declaration;
  do not try to close the mismatch by unfolding the large pullback
  constructions.
-/
/-- Native `F.over U` presentations give presentations on the corresponding
ringed open subspace. -/
theorem locallyPresented_has_presentation
    {X : RingedSpace.{v}} {F : Mod X.structureSheaf}
    (hF : LocallyPresented F) :
    ∀ x : X, ∃ U : Opens X.carrier, x ∈ U ∧ hasPresentationOn F U := by
  sorry

/-! The first part of the source's generators-and-relations explanation. -/
theorem locallyPresented_isLocallyGenerated
    {X : RingedSpace.{v}} {F : Mod X.structureSheaf}
    (hF : LocallyPresented F) :
    locallyGenerated F := by
  intro x
  rcases locallyPresented_has_presentation hF x with ⟨U, hxU, ⟨P⟩⟩
  exact ⟨U, hxU, ⟨P.generators⟩⟩

/-- The generators-and-relations form of the local definition. -/
theorem locallyPresented_has_generators_and_relations
    {X : RingedSpace.{v}} {F : Mod X.structureSheaf}
    (hF : LocallyPresented F) :
    ∀ x : X, ∃ U : Opens X.carrier, x ∈ U ∧
      ∃ (I J : Type v)
        (φ : (SheafOfModules.free J : Mod (ringedOpenSubspace X U).structureSheaf) ⟶
          (SheafOfModules.free I : Mod (ringedOpenSubspace X U).structureSheaf)),
        Nonempty (((openModuleRestrictionFunctor X U).obj F) ≅ cokernel φ) := by
  intro x
  rcases locallyPresented_has_presentation hF x with ⟨U, hxU, ⟨P⟩⟩
  let φ : (SheafOfModules.free P.relations.I :
      Mod (ringedOpenSubspace X U).structureSheaf) ⟶
      (SheafOfModules.free P.generators.I :
        Mod (ringedOpenSubspace X U).structureSheaf) :=
    (SheafOfModules.freeHomEquiv _).symm P.relations.s ≫
      kernel.ι P.generators.π
  refine ⟨U, hxU, P.generators.I, P.relations.I, φ, ?_⟩
  exact ⟨P.isColimit.coconePointUniqueUpToIso (colimit.isColimit _)⟩

/-- The cokernel projection is the last arrow in every displayed local
presentation. -/
theorem locallyPresented_has_cokernel_sequence
    {X : RingedSpace.{v}} {F : Mod X.structureSheaf}
    (hF : LocallyPresented F) :
    ∀ x : X, ∃ U : Opens X.carrier, x ∈ U ∧
      ∃ (I J : Type v)
        (φ : (SheafOfModules.free J : Mod (ringedOpenSubspace X U).structureSheaf) ⟶
          (SheafOfModules.free I : Mod (ringedOpenSubspace X U).structureSheaf)),
        Nonempty (((openModuleRestrictionFunctor X U).obj F) ≅ cokernel φ) ∧
    Nonempty (IsColimit
            (CokernelCofork.ofπ (cokernel.π φ) (cokernel.condition φ))) := by
  /-
  Proof roadmap:
  * Reuse `locallyPresented_has_presentation hF x`, not merely the preceding
    existential theorem, so that the chosen
    `P : ((openModuleRestrictionFunctor X U).obj F).Presentation` remains
    available.  Define `φ` exactly as in
    `locallyPresented_has_generators_and_relations`, with
    `I := P.generators.I` and `J := P.relations.I` (all in `Type v`).
  * The restricted object is the point of `P.isColimit`; compare that cofork
    with the chosen cokernel cofork by
    `P.isColimit.coconePointUniqueUpToIso (colimit.isColimit _)`.  This gives
    the required object iso in the orientation used above.
  * The second conjunct is independent of `P`: package
    `colimit.isColimit (parallelPair φ 0)` as the requested
    `IsColimit (CokernelCofork.ofπ (cokernel.π φ)
      (cokernel.condition φ))` (the cokernel is this chosen colimit).
  The presentation API is in
  `Mathlib/Algebra/Category/ModuleCat/Sheaf/Quasicoherent.lean`; the chosen
  cokernel API is in `Mathlib/CategoryTheory/Limits/Shapes/Kernels.lean`.
  -/
  sorry

/-- The displayed presentation is exact after identifying its cokernel with
the restricted sheaf. -/
theorem locallyPresented_has_exact_presentation
    {X : RingedSpace.{v}} {F : Mod X.structureSheaf}
    (hF : LocallyPresented F) :
    ∀ x : X, ∃ U : Opens X.carrier, x ∈ U ∧
      ∃ (I J : Type v)
        (φ : (SheafOfModules.free J : Mod (ringedOpenSubspace X U).structureSheaf) ⟶
          (SheafOfModules.free I : Mod (ringedOpenSubspace X U).structureSheaf))
        (e : ((openModuleRestrictionFunctor X U).obj F) ≅ cokernel φ),
        (ShortComplex.mk φ (cokernel.π φ ≫ e.inv) (by simp)).Exact := by
  /-
  Proof roadmap:
  * Obtain `U, I, J, φ, e` from
    `locallyPresented_has_generators_and_relations hF x` (or retain the same
    `P` as in the previous roadmap).  Choose `e : restricted F ≅ cokernel φ`
    in the statement's orientation.
  * Start with `ShortComplex.exact_cokernel φ` from
    `Mathlib/CategoryTheory/Abelian/Exact.lean` for
    `free J ⟶ free I ⟶ cokernel φ`.
  * Form `ShortComplex.isoMk (Iso.refl _) (Iso.refl _) e.symm`; its third
    component has hom `e.inv`, so its right square is exactly
    `cokernel.π φ ≫ e.inv`.  Transfer exactness with
    `ShortComplex.exact_of_iso`.  Use `simp only [Category.comp_id,
    Category.id_comp, Iso.inv_hom_id_assoc]` for the two square obligations.
  -/
  sorry

/-! ## Direct sums and pullback -/

/-- The warning used in the proof of the local-presentation lemma: global
sections need not commute with an infinite coproduct. -/
def GlobalSectionsOfCoproductAlwaysCommute : Prop :=
  ∀ (X : RingedSpace.{v}) (I : Type v) (F : I → Mod X.structureSheaf),
    IsIso (sheafModuleSectionsDirectSumMap X.structureSheaf F ⊤)

theorem not_globalSectionsOfCoproductAlwaysCommute :
    ¬ GlobalSectionsOfCoproductAlwaysCommute := by
  /-
  Proof roadmap (for the repaired canonical-comparison statement):
  * Choose `E := Classical.choice exists_wedgeOfLinesExample`, put
    `I := ULift.{0} (ℕ × ℕ)`, and take the constant family
    `F i := SheafOfModules.unit E.X.structureSheaf`.  By definition its
    sheaf coproduct is `SheafOfModules.free I`; the morphism under test is
    `sheafModuleSectionsDirectSumMap` from
    `lean/Formalization/Books/Modules/Unit03/AbelianCategory.lean`.
  * Use `E.coefficientSections 5` as an element of the target.  If it were in
    the comparison map's range, represent its preimage in the `ModuleCat`
    coproduct by a finite set of indices.  The colimit equations
    `colimit.ι_desc` and `SheafOfModules.freeHomEquiv_apply` show that its
    restriction to every open has `HasFiniteFreeSupport` with that same
    finite set.
  * Restrict to `E.neighbourhood 2` and contradict
    `E.no_local_matrix 1 5` (since `2 * (1 + 1) < 5`), after rewriting the
    image of the generator with `E.map_on_generators 5` and
    `SheafOfModules.sectionsMap_freeHomEquiv_symm_freeSection` from
    `Mathlib/Algebra/Category/ModuleCat/Sheaf/Free.lean`.
  * Thus the comparison is not surjective.  Finish from an assumed `IsIso`
    with `ConcreteCategory.bijective_of_isIso`; the underlying category is
    `ModuleCat (globalSectionsRing E.X)`.
  This route is why the definition now names the canonical map rather than
  asking for the absence of an unrelated abstract object isomorphism.
  -/
  sorry

/-- The direct sum of two quasi-coherent modules is quasi-coherent. -/
theorem directSum_isQuasiCoherent
    {X : RingedSpace.{v}} {F G : Mod X.structureSheaf}
    (hF : IsQuasiCoherent F) (hG : IsQuasiCoherent G) :
    IsQuasiCoherent (sheafModuleDirectSum X.structureSheaf F G) := by
  /-
  Proof roadmap:
  * Extract `qF` and `qG` with
    `SheafOfModules.IsQuasicoherent.nonempty_quasicoherentData.some`.
    Use the cover indexed by `qF.I × qG.I` whose open is
    `qF.X i ⊓ qG.X j`.  Prove it covers top through
    `Opens.coversTop_iff` and pointwise choices from the two original covers.
  * On each intersection, transport `qF.presentation i` and
    `qG.presentation j` through the iterated-over equivalence used by
    `SheafOfModules.QuasicoherentData.bind` in
    `Mathlib/Algebra/Category/ModuleCat/Sheaf/Quasicoherent.lean`.  Use
    `Presentation.map`, the restriction functor's colimit preservation, and
    `pushforwardPushforwardEquivalence` to obtain presentations of `F` and
    `G` over the common open.
  * Combine those presentations.  The relations and generators are the sum
    types, the free-object comparisons are
    `SheafOfModules.freeSumIso`, and the cokernel cofork is the binary
    coproduct of the two `Presentation.isColimit` coforks.  Binary coproduct
    preserves that colimit in the abelian sheaf-module category.
  * Package these presentations as
    `SheafOfModules.QuasicoherentData` and finish with
    `QuasicoherentData.isQuasicoherent`.  Finally identify the binary
    coproduct with `sheafModuleDirectSum` by its definition in Unit03.
  -/
  sorry

/-- The source's infinite-direct-sum warning, expressed using the canonical
coproduct of sheaves of modules. -/
def InfiniteDirectSumsPreserveQuasiCoherent : Prop :=
  ∀ (X : RingedSpace.{v}) (I : Type v) (_ : Infinite I)
    (F : I → Mod X.structureSheaf),
    (∀ i, IsQuasiCoherent (F i)) →
      IsQuasiCoherent (sheafModuleCoproduct X.structureSheaf F)

theorem not_infiniteDirectSumsPreserveQuasiCoherent :
    ¬ InfiniteDirectSumsPreserveQuasiCoherent := by
  /-
  Roadmap/blocker for the prove stage:
  * A proof requires an explicit family with no common presentation
    neighbourhood.  The exact reusable input should have type
      `∃ (X : RingedSpace.{v}) (I : Type v) (_ : Infinite I)
        (F : I → Mod X.structureSheaf),
        (∀ i, IsQuasiCoherent (F i)) ∧
        ¬ IsQuasiCoherent (sheafModuleCoproduct X.structureSheaf F)`.
    No declaration with this content exists in earlier Modules chapters or
    Mathlib.  `exists_wedgeOfLinesExample` concerns non-finite global
    sections of one free sheaf and does not by itself provide such a family.
  * Once that witness is available, introduce the universal hypothesis,
    specialize it to `X, I, F`, and apply the witness's last conjunct.
  Do not try to use a coproduct of copies of the structure sheaf: it is the
  free sheaf and has a global `Presentation`, hence is quasi-coherent by
  `SheafOfModules.Presentation.isQuasicoherent` in
  `Mathlib/Algebra/Category/ModuleCat/Sheaf/Quasicoherent.lean`.
  -/
  sorry

/-- An existential form of the infinite-direct-sum warning. -/
def HasInfiniteDirectSumFailure (X : RingedSpace.{v}) : Prop :=
  ∃ (I : Type v) (_ : Infinite I) (F : I → Mod X.structureSheaf),
    (∀ i, IsQuasiCoherent (F i)) ∧
      ¬ IsQuasiCoherent (sheafModuleCoproduct X.structureSheaf F)

theorem exists_infinite_directSum_failure :
    ∃ X : RingedSpace.{v}, HasInfiniteDirectSumFailure X := by
  /-
  Proof roadmap:
  * This is pure classical logic from
    `not_infiniteDirectSumsPreserveQuasiCoherent`; no geometric construction
    should be duplicated here.
  * By contradiction, push `¬ ∃ X, HasInfiniteDirectSumFailure X` through
    `not_exists` twice.  For arbitrary `X, I, instInfinite, F` and `hF`, the
    resulting negation of
    `(∀ i, IsQuasiCoherent (F i)) ∧ ¬ IsQuasiCoherent (coproduct F)`
    forces quasi-coherence of the coproduct.  This constructs
    `InfiniteDirectSumsPreserveQuasiCoherent`, contradicting the preceding
    theorem.
  * Keep the instance binder explicit as
    `letI : Infinite I := instInfinite` before specializing the negated
    existential; otherwise Lean may create two non-definitionally-equal
    instance metavariables.
  -/
  sorry

/-- Pullback preserves quasi-coherence. -/
theorem pullback_isQuasiCoherent
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y)
    (G : Mod Y.structureSheaf) (hG : IsQuasiCoherent G)
    [((SheafOfModules.pushforward (F := Opens.map f.continuous)
      f.sharp).IsRightAdjoint)] :
    IsQuasiCoherent ((sheafModuleRingedSpacePullback f).obj G) := by
  /-
  Proof roadmap:
  * Extract `q : G.QuasicoherentData`.  Pull its open cover back along
    `Opens.map f.continuous`; `Opens.coversTop_iff` plus `Opens.map_iSup` and
    `Opens.map_top` prove that the inverse-image opens cover `X`.
  * For each cover member, map `q.presentation i` by the appropriate module
    pullback.  Install colimit preservation with
    `sheafModuleRingedSpacePullback_preserves_all_colimits f` from
    `lean/Formalization/Books/Modules/Unit03/AbelianCategory.lean`, and use
    `SheafOfModules.Presentation.map` with unit comparison
    `(asIso (SheafOfModules.pullbackObjUnitToUnit _)).symm` from
    `Mathlib/Algebra/Category/ModuleCat/Sheaf/PullbackFree.lean`.
  * Identify restriction-after-pullback with pullback-after-restriction via
    `ringedSpaceModulePullback_restrict_square_iso` in
    `lean/Formalization/Books/Sheaves/Unit26/RingedSpaceModules.lean`, then
    transport the mapped presentation with `Presentation.ofIsIso`.
  * Assemble `QuasicoherentData` and apply `.isQuasicoherent`.
  The remaining prerequisite is the same open inverse-image square exported
  in the roadmap for `Unit08.locallyGenerated_pullback`: the current earlier
  open-immersion API does not yet provide the bundled `RingedSpaceHom` square
  or its right-adjoint witness.  Do not replace it by equality of continuous
  maps, which is too weak for the restriction-square iso.
  -/
  sorry

/-! ## The three associated-sheaf constructions -/

/-- The ring of global sections. -/
abbrev globalSectionsRing (X : RingedSpace.{v}) : Type v :=
  X.structureSheaf.obj.obj (op (⊤ : Opens X.carrier))

/-- The constant presheaf of rings with value `R`. -/
abbrev constantRingPresheaf (X : RingedSpace.{v}) (R : Type v) [Ring R] :
    TopCat.Presheaf RingCat X.carrier :=
  (Functor.const (Opens X.carrier)ᵒᵖ).obj (RingCat.of R)

/-- The constant presheaf of `R`-modules with value `M`. -/
noncomputable def constantModulePresheaf
    {X : RingedSpace.{v}} {R : Type v} [Ring R] (M : ModuleCat R) :
    PresheafOfModules (constantRingPresheaf X R) where
  obj _ := M
  map f :=
    (ModuleCat.restrictScalarsId'
      ((constantRingPresheaf X R).map (𝟙 _)).hom
      (congrArg RingCat.Hom.hom ((constantRingPresheaf X R).map_id _))).inv.app M
  map_id := by simp
  map_comp := by
    intro X₁ Y Z f g
    apply ModuleCat.hom_ext
    ext m
    rfl

/-- The map from a constant ring presheaf to the structure sheaf, induced by
a map into global sections. -/
noncomputable def globalSectionsPresheafMap
    {X : RingedSpace.{v}} {R : Type v} [Ring R]
    (α : R →+* globalSectionsRing X) :
    constantRingPresheaf X R ⟶ X.structureSheaf.obj := by
  classical
  refine { app := fun U => RingCat.ofHom ?_, naturality := ?_ }
  · exact
      ((X.structureSheaf.obj.map
          (homOfLE (show (U.unop : Opens X.carrier) ≤ ⊤ from le_top)).op).hom.comp α)
  · intro U V f
    apply RingCat.hom_ext
    ext r
    have htop :
        (X.structureSheaf.obj.map
            (homOfLE (show (V.unop : Opens X.carrier) ≤ ⊤ from le_top)).op).hom =
          (X.structureSheaf.obj.map f).hom.comp
            (X.structureSheaf.obj.map
              (homOfLE (show (U.unop : Opens X.carrier) ≤ ⊤ from le_top)).op).hom := by
      rw [← RingCat.hom_comp, ← X.structureSheaf.obj.map_comp]
      congr 1
    change
      (X.structureSheaf.obj.map
          (homOfLE (show (V.unop : Opens X.carrier) ≤ ⊤ from le_top)).op).hom
          (α r) =
        (X.structureSheaf.obj.map f).hom
          ((X.structureSheaf.obj.map
            (homOfLE (show (U.unop : Opens X.carrier) ≤ ⊤ from le_top)).op).hom
            (α r))
    exact congrArg (fun h : globalSectionsRing X →+* _ => h (α r)) htop

/-- The presheaf `U ↦ O_X(U) ⊗_R M`. -/
noncomputable abbrev associatedSheafPresheaf
    {X : RingedSpace.{v}} {R : Type v} [Ring R]
    (α : R →+* globalSectionsRing X) (M : ModuleCat R) :
    PresheafOfModules X.structureSheaf.obj :=
  (Formalization.Books.Sheaves.Unit06.changeOfRingsCore
      (globalSectionsPresheafMap α)).obj (constantModulePresheaf M)

/-- The sheafification of the presheaf description. -/
noncomputable def associatedSheafFromPresheaf
    {X : RingedSpace.{v}} {R : Type v} [Ring R]
    (α : R →+* globalSectionsRing X) (M : ModuleCat R) :
    Mod X.structureSheaf :=
  (PresheafOfModules.sheafification (𝟙 X.structureSheaf.obj)).obj
    (associatedSheafPresheaf α M)

/-- The associated sheaf attached to a bundled module. -/
noncomputable abbrev associatedSheafModule
    {X : RingedSpace.{v}} {R : Type v} [Ring R]
    (α : R →+* globalSectionsRing X) (M : ModuleCat R) :
  Mod X.structureSheaf :=
  associatedSheafFromPresheaf α M

/- The presheaf construction is the source's third description.  Keeping
the comparison as an explicit theorem makes the fact that the bundled and
carrier-type interfaces are the same construction available to clients. -/
theorem associatedSheafFromPresheaf_eq_associatedSheafModule
    {X : RingedSpace.{v}} {R : Type v} [Ring R]
    (α : R →+* globalSectionsRing X) (M : ModuleCat R) :
    associatedSheafFromPresheaf α M = associatedSheafModule α M := rfl

/-- The source notation `F_M` when `M` is presented by its carrier type. -/
noncomputable abbrev associatedSheaf
    {X : RingedSpace.{v}} {R : Type v} [Ring R] (α : R →+* globalSectionsRing X)
    (M : Type v) [AddCommGroup M] [Module R M] : Mod X.structureSheaf :=
  associatedSheafModule α (ModuleCat.of R M)

noncomputable abbrev associatedSheafOfModule
    {X : RingedSpace.{v}} {R : Type v} [Ring R]
    (α : R →+* globalSectionsRing X) (M : ModuleCat R) : Mod X.structureSheaf :=
  associatedSheafModule α M

noncomputable abbrev associatedSheafOfGlobalSections
    {X : RingedSpace.{v}} (M : ModuleCat (globalSectionsRing X)) :
    Mod X.structureSheaf :=
  associatedSheafModule (RingHom.id _) M

/-! The free sheaves used in the counterexample are instances of the
associated-sheaf construction. -/
noncomputable abbrev associatedSheafFreeModule
    (X : RingedSpace.{v}) (I : Type v) : Mod X.structureSheaf :=
  associatedSheafModule (RingHom.id _)
    ((ModuleCat.free (globalSectionsRing X)).obj I)

theorem freeSheaf_associatedSheaf_iso
    {X : RingedSpace.{v}} (I : Type v) :
    Nonempty ((SheafOfModules.free I : Mod X.structureSheaf) ≅
      associatedSheafFreeModule X I) := by
  /-
  Proof roadmap:
  * Regard `(ModuleCat.free (globalSectionsRing X)).obj I` as the coproduct
    of `I` copies of the rank-one module.  Construct the corresponding
    colimit cocone using `ModuleCat.free`/`ModuleCat.freeMk` and the standard
    `ModuleCat` coproduct instances.
  * Map it successively through `constantModulePresheaf`,
    `Formalization.Books.Sheaves.Unit06.changeOfRingsCore
      (globalSectionsPresheafMap (RingHom.id _))`, and
    `PresheafOfModules.sheafification (𝟙 X.structureSheaf.obj)`.
    The latter two are left adjoints by
    `PresheafOfModules.pullbackPushforwardAdjunction` and
    `PresheafOfModules.sheafificationAdjunction`, so their mapped cocones are
    colimits.
  * For one summand, simplify extension along the identity and use the
    sheafification counit to identify the image with
    `SheafOfModules.unit X.structureSheaf`.  Compare the resulting coproduct
    cocone with `SheafOfModules.freeCofan I` using
    `SheafOfModules.isColimitFreeCofan` and
    `IsColimit.coconePointUniqueUpToIso` from
    `Mathlib/Algebra/Category/ModuleCat/Sheaf/Free.lean`.
  * Orient the final iso from `free I` to `associatedSheafFreeModule X I` and
    wrap it in `Nonempty`.  Keep all module and index universes at `v`.
  -/
  sorry

theorem associatedSheaf_isQuasiCoherent
    {X : RingedSpace.{v}} {R : Type v} [Ring R]
    (α : R →+* globalSectionsRing X) (M : Type v)
    [AddCommGroup M] [Module R M] :
    IsQuasiCoherent (associatedSheaf α M) := by
  /-
  Proof roadmap:
  * First factor a chronological helper before this theorem which builds a
    two-free-module presentation of `ModuleCat.of R M`.  Take generators
    `M`, use `Finsupp.linearCombination R id` and
    `Finsupp.linearCombination_id_surjective` from
    `Mathlib/LinearAlgebra/Finsupp/LinearCombination.lean`, then take the
    carrier of its kernel as relations.  A second use of the same lemma gives
    a free epimorphism onto the kernel; `Abelian.epiIsCokernelOfKernel`
    supplies the required cokernel iso.  This is the data later named
    `ModulePresentation`.
  * Map that presentation through the presheaf extension-of-scalars and
    sheafification construction.  Both preserve cokernels by their
    adjunctions (`PresheafOfModules.pullbackPushforwardAdjunction` and
    `PresheafOfModules.sheafificationAdjunction`).  Use
    `SheafOfModules.mapFreeIso` for the images of the two free modules.
  * The mapped cokernel therefore yields a global
    `SheafOfModules.Presentation (associatedSheaf α M)` via
    `SheafOfModules.presentationOfIsCokernelFree`; finish with
    `Presentation.isQuasicoherent` from
    `Mathlib/Algebra/Category/ModuleCat/Sheaf/Quasicoherent.lean`.
  The later `associatedPresentationMap_cokernel_iso` is the reusable public
  form of the same calculation, but it cannot be referenced here without
  moving its prerequisite definitions earlier.
  -/
  sorry

theorem associatedSheafModule_isQuasiCoherent
    {X : RingedSpace.{v}} {R : Type v} [Ring R]
    (α : R →+* globalSectionsRing X) (M : ModuleCat R) :
    IsQuasiCoherent (associatedSheafModule α M) := by
  /-
  Proof roadmap:
  * Apply `associatedSheaf_isQuasiCoherent α M` with the bundled carrier
    `M : Type v`; the `AddCommGroup M` and `Module R M` instances are
    inherited from `ModuleCat`.
  * Close the remaining goal by `change`/`rfl`, since
    `associatedSheaf α M` abbreviates
    `associatedSheafModule α (ModuleCat.of R M)` and the bundled module is
    definitionally recovered by `ModuleCat.of` here.  If that last equality
    is not definitional in the current Mathlib build, construct the
    identity-on-elements iso with `ModuleCat.ofHom` and `ModuleCat.hom_ext`,
    map it through the associated-sheaf construction, and use closure of
    `SheafOfModules.isQuasicoherent` under isomorphisms.
  -/
  sorry

/-! The presentation and point descriptions in the source. -/

/-- A module presentation by free modules. -/
structure ModulePresentation {R : Type v} [Ring R] (M : ModuleCat R) where
  relations : Type v
  generators : Type v
  map : (ModuleCat.free R).obj relations ⟶ (ModuleCat.free R).obj generators
  presentation : Nonempty (cokernel map ≅ M)

/-- The coefficient of a free-module map at a relation and generator. -/
abbrev ModulePresentation.matrixEntry {R : Type v} [Ring R]
    {M : ModuleCat R} (P : ModulePresentation M)
    (j : P.relations) (i : P.generators) : R :=
  let v : P.generators →₀ R := P.map.hom (ModuleCat.freeMk j)
  v i

/-! The matrix in the second construction is finite in each column because
the corresponding element of a free module is a finitely supported function. -/

noncomputable def ModulePresentation.relationSectionValue
    {X : RingedSpace.{v}} {R : Type v} [Ring R]
    (α : R →+* globalSectionsRing X) {M : ModuleCat R}
    (P : ModulePresentation M) (j : P.relations)
    (U : (Opens X.carrier)ᵒᵖ) :
    (SheafOfModules.free (R := X.structureSheaf) P.generators).val.obj U :=
  Finset.sum (P.map.hom (ModuleCat.freeMk j)).support (fun i =>
    let rU :=
      (X.structureSheaf.obj.map
        (homOfLE (show U.unop ≤ ⊤ from le_top)).op).hom
        (α (P.matrixEntry j i))
    let mU : (SheafOfModules.free (R := X.structureSheaf) P.generators).val.obj U :=
      (SheafOfModules.freeSection (R := X.structureSheaf) i).1 U
    rU • mU)

theorem ModulePresentation.relationSectionValue_compatible
    {X : RingedSpace.{v}} {R : Type v} [Ring R]
    (α : R →+* globalSectionsRing X) {M : ModuleCat R}
    (P : ModulePresentation M) (j : P.relations)
    {_U _V : (Opens X.carrier)ᵒᵖ} (f : _U ⟶ _V) :
    (SheafOfModules.free (R := X.structureSheaf) P.generators).val.map f
        (P.relationSectionValue α j _U) =
      P.relationSectionValue α j _V := by
  /-
  Proof roadmap:
  * Unfold only `ModulePresentation.relationSectionValue`; do not unfold the
    free sheaf.  Move the restriction map through the finite sum with
    `map_sum` and through scalar multiplication with the component linear
    map's `map_smul`.
  * For each `i` in the fixed support, the scalar equality is naturality of
    `globalSectionsPresheafMap α`; use its `naturality` component and
    `X.structureSheaf.obj.map_comp` to identify restriction from top to `_V`
    with restriction via `_U`.
  * The basis-section equality is
    `PresheafOfModules.sections_property
      (SheafOfModules.freeSection i) f`, from
    `Mathlib/Algebra/Category/ModuleCat/Presheaf.lean`.
  * Finish termwise with `Finset.sum_congr`; the `Finsupp.support` itself is
    unchanged because the module-presentation map is fixed.  A focused
    `simp only [map_sum, map_smul, PresheafOfModules.sections_property]` is
    preferable to unfolding `SheafOfModules.free`.
  -/
  sorry

noncomputable def ModulePresentation.relationSection
    {X : RingedSpace.{v}} {R : Type v} [Ring R]
    (α : R →+* globalSectionsRing X) {M : ModuleCat R}
    (P : ModulePresentation M) (j : P.relations) :
    (SheafOfModules.free P.generators : Mod X.structureSheaf).sections :=
  PresheafOfModules.sectionsMk (P.relationSectionValue α j)
    (fun {_U _V} f => P.relationSectionValue_compatible α j f)

noncomputable def associatedPresentationMap
    {X : RingedSpace.{v}} {R : Type v} [Ring R]
    (α : R →+* globalSectionsRing X) {M : ModuleCat R}
    (P : ModulePresentation M) :
    (SheafOfModules.free P.relations : Mod X.structureSheaf) ⟶
      (SheafOfModules.free P.generators : Mod X.structureSheaf) :=
  (SheafOfModules.freeHomEquiv _).symm
    (fun j => P.relationSection α j)

theorem associatedPresentationMap_section
    {X : RingedSpace.{v}} {R : Type v} [Ring R]
    (α : R →+* globalSectionsRing X) {M : ModuleCat R}
    (P : ModulePresentation M) (j : P.relations) :
    (SheafOfModules.freeHomEquiv
        (SheafOfModules.free P.generators : Mod X.structureSheaf)
      (associatedPresentationMap α P)) j = P.relationSection α j := by
  simp [associatedPresentationMap]

/-! For every chosen module presentation, the associated sheaf has the same
cokernel presentation. This is the presentation-independent construction
asserted in the source's second description. -/
theorem associatedPresentationMap_cokernel_iso
    {X : RingedSpace.{v}} {R : Type v} [Ring R]
    (α : R →+* globalSectionsRing X) {M : ModuleCat R}
    (P : ModulePresentation M) :
    Nonempty (cokernel (associatedPresentationMap α P) ≅
      associatedSheafModule α M) := by
  /-
  Proof roadmap:
  * Let `eM : cokernel P.map ≅ M := (P.presentation).some` and build the
    functor in `M` used by the associated-sheaf construction: constant module
    presheaf, `changeOfRingsCore (globalSectionsPresheafMap α)`, then
    module sheafification.  Prove once that it preserves colimits from the
    three component adjunctions; this is the same functor constructed in
    `exists_associatedSheafFunctor` below.
  * Map the canonical cokernel cofork of `P.map`.  Use
    `isColimitOfPreserves` and `SheafOfModules.mapFreeIso` to replace the two
    mapped free modules by the free sheaves on `P.relations` and
    `P.generators`.
  * Prove that the conjugated mapped arrow is
    `associatedPresentationMap α P` by
    `SheafOfModules.freeHomEquiv.injective`; at generator `j`, expand the
    sectionwise extension and use
    `associatedPresentationMap_section` plus
    `ModulePresentation.relationSectionValue_compatible`.
  * Compare this mapped colimit cocone with the chosen cokernel cocone via
    `IsColimit.coconePointUniqueUpToIso`, then compose with the functor's
    `mapIso eM` and the definitional object comparison to
    `associatedSheafModule α M`.
  Relevant APIs are in
  `Mathlib/Algebra/Category/ModuleCat/Sheaf/Free.lean`,
  `.../Sheaf/Quasicoherent.lean`, and
  `.../Presheaf/Sheafification.lean`.
  -/
  sorry

/-- A one-point ringed space with structure ring `R`. -/
noncomputable def onePointRingedSpace (R : Type v) [Ring R] : RingedSpace.{v} :=
  { carrier := TopCat.of (ULift.{v} PUnit)
    structureSheaf :=
      (CategoryTheory.constantSheaf
        (Opens.grothendieckTopology (TopCat.of (ULift.{v} PUnit))) RingCat).obj
        (RingCat.of R) }

/-- The unique continuous map to the one-point space. -/
noncomputable def onePointContinuousMap
    {X : RingedSpace.{v}} {R : Type v} [Ring R] :
    X.carrier ⟶ (onePointRingedSpace R).carrier :=
  TopCat.ofHom
    (ContinuousMap.const X.carrier
      (ULift.up PUnit.unit : (onePointRingedSpace R).carrier))

/-- The one-point morphism whose map on structure sheaves is induced by `α`. -/
noncomputable def onePointRingedSpaceHom
    {X : RingedSpace.{v}} {R : Type v} [Ring R]
    (α : R →+* globalSectionsRing X) :
    RingedSpaceHom X (onePointRingedSpace R) :=
  { continuous := onePointContinuousMap (X := X) (R := R)
    sharp := by
      let F := (TopCat.Sheaf.pushforward RingCat
        (onePointContinuousMap (X := X) (R := R))).obj
        X.structureSheaf
      let hα : R →+* F.presheaf.obj (op (⊤ : Opens (onePointRingedSpace R).carrier)) := by
        let e : F.presheaf.obj (op (⊤ : Opens (onePointRingedSpace R).carrier)) =
            X.structureSheaf.obj.obj (op (⊤ : Opens X.carrier)) := by
          change X.structureSheaf.obj.obj
              (op ((Opens.map (onePointContinuousMap (X := X) (R := R))).obj
                (⊤ : Opens (onePointRingedSpace R).carrier))) =
            X.structureSheaf.obj.obj (op (⊤ : Opens X.carrier))
          rw [Opens.map_top]
        exact (RingCat.Hom.hom (eqToHom e.symm)).comp α
      exact
        ((CategoryTheory.constantSheafAdj
            (Opens.grothendieckTopology (onePointRingedSpace R).carrier) RingCat
            (T := (⊤ : Opens (onePointRingedSpace R).carrier)) isTerminalTop).homEquiv
          (RingCat.of R) F).symm (RingCat.ofHom hα) }

/-- The one-point morphism realizes the prescribed map on global sections. -/
def onePointRingedSpaceHomInduces
    {X : RingedSpace.{v}} {R : Type v} [Ring R]
    (α : R →+* globalSectionsRing X)
    (f : RingedSpaceHom X (onePointRingedSpace R)) : Prop :=
  f.continuous = onePointContinuousMap ∧
    HEq f.sharp (onePointRingedSpaceHom α).sharp

theorem onePointRingedSpaceHom_induces
    {X : RingedSpace.{v}} {R : Type v} [Ring R]
    (α : R →+* globalSectionsRing X) :
    onePointRingedSpaceHomInduces α (onePointRingedSpaceHom α) := by
  exact ⟨rfl, HEq.rfl⟩

/-- The sheaf on the one-point ringed space corresponding to an `R`-module.
This is the point-space instance of the associated-sheaf construction. -/
noncomputable def onePointRingToGlobalSections
    (R : Type v) [Ring R] :
    R →+* globalSectionsRing (onePointRingedSpace R) :=
  RingCat.Hom.hom ((CategoryTheory.constantSheafAdj
      (Opens.grothendieckTopology (onePointRingedSpace R).carrier) RingCat
      (T := (⊤ : Opens (onePointRingedSpace R).carrier)) isTerminalTop).unit.app
    (RingCat.of R))

noncomputable abbrev onePointModule
    {R : Type v} [Ring R] (M : ModuleCat R) :
  Mod (onePointRingedSpace R).structureSheaf :=
  associatedSheafModule (X := onePointRingedSpace R) (RingHom.id _)
    ((ModuleCat.coextendScalars (onePointRingToGlobalSections R)).obj M)

/-! The pullback API exposes the right-adjoint witness explicitly here. -/

noncomputable def pointModulePullback
    {X : RingedSpace.{v}} {R : Type v} [Ring R]
    (α : R →+* globalSectionsRing X)
    (h : (SheafOfModules.pushforward
      (F := Opens.map (onePointRingedSpaceHom α).continuous)
      (onePointRingedSpaceHom α).sharp).IsRightAdjoint)
    (P : Mod (onePointRingedSpace R).structureSheaf) : Mod X.structureSheaf := by
  letI := h
  exact (sheafModuleRingedSpacePullback (onePointRingedSpaceHom α)).obj P

/-- The point/pullback description of the associated sheaf. -/
def PointModuleDescription
    {X : RingedSpace.{v}} {R : Type v} [Ring R]
    (α : R →+* globalSectionsRing X) (M : ModuleCat R) : Prop :=
  ∃ h : (SheafOfModules.pushforward
      (F := Opens.map (onePointRingedSpaceHom α).continuous)
      (onePointRingedSpaceHom α).sharp).IsRightAdjoint,
    Nonempty (pointModulePullback α h (onePointModule M) ≅
      associatedSheafModule α M)

/-! The point-space/pullback construction is canonically the same associated
sheaf as the presheaf construction. -/
theorem associatedSheaf_point_description
    {X : RingedSpace.{v}} {R : Type v} [Ring R]
    (α : R →+* globalSectionsRing X) (M : ModuleCat R) :
    PointModuleDescription α M := by
  /-
  Proof roadmap:
  * Obtain the witness `h` from the generic presheaf pullback construction.
    The instance for
    `PresheafOfModules.pushforward (onePointRingedSpaceHom α).sharp.hom`
    induces the sheaf instance through
    `SheafOfModules.PullbackConstruction.adjunction` in
    `Mathlib/Algebra/Category/ModuleCat/Sheaf/PullbackContinuous.lean`.
    Bind it explicitly as `let h := inferInstance` and use the same term in
    `pointModulePullback α h` so chosen-left-adjoint mismatches cannot occur.
  * Expand both sides through `SheafOfModules.pullbackIso`.  On the one-point
    site, use `CategoryTheory.constantSheafAdj` to identify the constant
    sheaf's global ring with `R`; prove that the induced composite
    `R →+* globalSectionsRing X` is `α` by the defining hom-equivalence of
    `onePointRingedSpaceHom` and the triangle identity for
    `constantSheafAdj`.
  * Show `onePointRingToGlobalSections R` is an isomorphism from the unit of
    `constantSheafAdj`; along this ring iso the `ModuleCat.coextendScalars`
    in `onePointModule` is canonically transport of `M`.  Then use
    `PresheafOfModules.pullbackComp` from
    `Mathlib/Algebra/Category/ModuleCat/Presheaf/Pullback.lean` to compose the
    two presheaf changes of rings.  The result is
    `associatedSheafPresheaf α M`.
  * Apply the sheafification comparison iso and finish with the definitional
    equality `associatedSheafFromPresheaf_eq_associatedSheafModule`.
  -/
  sorry

/-- A source-facing name for the pullback description. -/
abbrev PullbackDescription
    {X : RingedSpace.{v}} {R : Type v} [Ring R]
    (α : R →+* globalSectionsRing X) (M : ModuleCat R) : Prop :=
  ∃ h : (SheafOfModules.pushforward
      (F := Opens.map (onePointRingedSpaceHom α).continuous)
      (onePointRingedSpaceHom α).sharp).IsRightAdjoint,
    Nonempty (pointModulePullback α h (onePointModule M) ≅
      associatedSheafModule α M)

/-- The three constructions in the source have canonical comparison
isomorphisms. -/
structure AssociatedSheafDescriptions
    {X : RingedSpace.{v}} {R : Type v} [Ring R]
    (α : R →+* globalSectionsRing X) (M : ModuleCat R) where
  modulePresentation : ModulePresentation M
  presentationCokernelIso : Nonempty
    (cokernel (associatedPresentationMap α modulePresentation) ≅
      associatedSheafModule α M)
  pullbackWitness :
    ∃ h : (SheafOfModules.pushforward
        (F := Opens.map (onePointRingedSpaceHom α).continuous)
        (onePointRingedSpaceHom α).sharp).IsRightAdjoint,
      Nonempty (pointModulePullback α h (onePointModule M) ≅
        associatedSheafModule α M)
  presheafToAssociated : Nonempty
    (associatedSheafFromPresheaf α M ≅ associatedSheafModule α M)

/-- The bundled associated-sheaf object is quasi-coherent, and its presheaf
description is definitionally the same object. -/
theorem associatedSheafModule_isQuasiCoherent_and_presheaf_eq
    {X : RingedSpace.{v}} {R : Type v} [Ring R]
    (α : R →+* globalSectionsRing X) (M : ModuleCat R) :
    IsQuasiCoherent (associatedSheafModule α M) ∧
      associatedSheafFromPresheaf α M = associatedSheafModule α M := by
  exact ⟨associatedSheafModule_isQuasiCoherent α M,
    associatedSheafFromPresheaf_eq_associatedSheafModule α M⟩

theorem exists_associatedSheafDescriptions
    {X : RingedSpace.{v}} {R : Type v} [Ring R]
    (α : R →+* globalSectionsRing X) (M : ModuleCat R) :
    Nonempty (AssociatedSheafDescriptions α M) := by
  /-
  Proof roadmap:
  * Construct `P : ModulePresentation M` by the two-step free presentation
    described next to `associatedSheaf_isQuasiCoherent`: generators are the
    carrier of `M`, relations are the carrier of the kernel of the canonical
    free epimorphism, and the cokernel iso comes from
    `Abelian.epiIsCokernelOfKernel`.
  * Fill `presentationCokernelIso` with
    `associatedPresentationMap_cokernel_iso α P` and `pullbackWitness` with
    `associatedSheaf_point_description α M`.
  * For `presheafToAssociated`, the two objects are definitionally equal;
    use `associatedSheafFromPresheaf_eq_associatedSheafModule` to rewrite and
    return `Iso.refl _` (or `eqToIso` if rewriting does not reduce).
  * Package the four fields and wrap the structure in `Nonempty`.  Keep `P`
    as an explicitly typed intermediate term to prevent Lean from repeatedly
    elaborating its kernel/cokernel data.
  -/
  sorry

/-! ## Functorial properties, stalks, and Hom -/

/-- Data asserting that a chosen functor has the associated-sheaf objects. -/
def IsAssociatedSheafFunctor
    {X : RingedSpace.{v}} {R : Type v} [Ring R]
    (α : R →+* globalSectionsRing X)
    (F : ModuleCat R ⥤ Mod X.structureSheaf) : Prop :=
  ∀ M, Nonempty (F.obj M ≅ associatedSheafModule α M)

/-- Existence of the functor supplied by the presheaf construction. -/
theorem exists_associatedSheafFunctor
    {X : RingedSpace.{v}} {R : Type v} [Ring R]
    (α : R →+* globalSectionsRing X) :
    ∃ F : ModuleCat R ⥤ Mod X.structureSheaf,
      IsAssociatedSheafFunctor α F ∧
        PreservesColimitsOfSize.{v, v} F := by
  /-
  Proof roadmap:
  * Define a helper functor
    `constantModulePresheafFunctor : ModuleCat R ⥤
      PresheafOfModules (constantRingPresheaf X R)` whose object is
    `constantModulePresheaf` and whose map is the same linear map at every
    open, conjugated by `ModuleCat.restrictScalarsId'`.  Its functor laws are
    proved componentwise with `ModuleCat.hom_ext`.
  * Set `F` to its composite with
    `Formalization.Books.Sheaves.Unit06.changeOfRingsCore
      (globalSectionsPresheafMap α)` and
    `PresheafOfModules.sheafification (𝟙 X.structureSheaf.obj)`.  The object
    comparison with `associatedSheafModule α M` is `Iso.refl _` after
    unfolding these three small definitions.
  * Prove colimit preservation of the constant helper using
    `PresheafOfModules.evaluationJointlyReflectsColimits` and pointwise
    `ModuleCat` colimits.  The change-of-rings and sheafification components
    preserve all `v`-small colimits because they are the left adjoints in
    `PresheafOfModules.pullbackPushforwardAdjunction` and
    `PresheafOfModules.sheafificationAdjunction`.
  * Combine the three preservation instances for functor composition and
    return `⟨F, fun M ↦ ⟨Iso.refl _⟩, inferInstance⟩`.  Name the
    `PreservesColimitsOfSize.{v,v}` instance for each component before asking
    typeclass search for the composite.
  -/
  sorry

/-- The associated-sheaf construction is functorial in `M`. -/
noncomputable def associatedSheafFunctor
    {X : RingedSpace.{v}} {R : Type v} [Ring R]
    (α : R →+* globalSectionsRing X) : ModuleCat R ⥤ Mod X.structureSheaf := by
  exact Classical.choose (exists_associatedSheafFunctor α)

theorem associatedSheafFunctor_obj
    {X : RingedSpace.{v}} {R : Type v} [Ring R]
    (α : R →+* globalSectionsRing X) (M : ModuleCat R) :
    Nonempty ((associatedSheafFunctor α).obj M ≅ associatedSheafModule α M) := by
  exact (Classical.choose_spec (exists_associatedSheafFunctor α)).1 M

/-- The stalk construction attached to the associated-sheaf functor. -/
noncomputable def associatedSheafStalkFunctor
    {X : RingedSpace.{v}} {R : Type v} [Ring R]
    (α : R →+* globalSectionsRing X) (x : X) :
    ModuleCat R ⥤ ModuleCat.{v, v}
      (TopCat.Presheaf.stalk (C := RingCat.{v}) X.structureSheaf.obj x) :=
  associatedSheafFunctor α ⋙ sheafModuleStalkFunctor X.structureSheaf x

theorem associatedSheafStalkFunctor_obj
    {X : RingedSpace.{v}} {R : Type v} [Ring R]
    (α : R →+* globalSectionsRing X) (M : ModuleCat R) (x : X) :
    Nonempty ((associatedSheafStalkFunctor α x).obj M ≅
      (sheafModuleStalkFunctor X.structureSheaf x).obj
        (associatedSheafModule α M)) := by
  /-
  Proof roadmap:
  * Choose `e : (associatedSheafFunctor α).obj M ≅
      associatedSheafModule α M` from
    `associatedSheafFunctor_obj α M`.
  * Apply `(sheafModuleStalkFunctor X.structureSheaf x).mapIso e` and package
    it in `Nonempty`.  After unfolding only
    `associatedSheafStalkFunctor`, its source is definitionally the left side
    of the goal.  No stalk computation or sheafification unfolding is needed.
  -/
  sorry

/-- The associated-sheaf functor with codomain restricted to quasi-coherent
modules. -/
noncomputable def associatedSheafQCohFunctor
    {X : RingedSpace.{v}} {R : Type v} [Ring R]
    (α : R →+* globalSectionsRing X) : ModuleCat R ⥤ QCoh X where
  obj M := ⟨associatedSheafModule α M, associatedSheafModule_isQuasiCoherent α M⟩
  map f := ⟨
    (Classical.choice (associatedSheafFunctor_obj α _)).inv ≫
      (associatedSheafFunctor α).map f ≫
      (Classical.choice (associatedSheafFunctor_obj α _)).hom⟩
  map_id := by
    intro M
    apply ObjectProperty.hom_ext
    simp
  map_comp := by
    intro M N P f g
    apply ObjectProperty.hom_ext
    simp [Category.assoc]

theorem associatedSheafFunctor_preserves_colimits
    {X : RingedSpace.{v}} {R : Type v} [Ring R]
    (α : R →+* globalSectionsRing X) :
    PreservesColimitsOfSize.{v, v} (associatedSheafFunctor α) := by
  exact (Classical.choose_spec (exists_associatedSheafFunctor α)).2

theorem associatedSheafQCohFunctor_preserves_colimits
    {X : RingedSpace.{v}} {R : Type v} [Ring R]
    (α : R →+* globalSectionsRing X) :
    PreservesColimitsOfSize.{v, v} (associatedSheafQCohFunctor α) := by
  /-
  Proof roadmap:
  * Let `ι : QCoh X ⥤ Mod X.structureSheaf` be the full-subcategory
    inclusion.  Build a natural iso
      `associatedSheafQCohFunctor α ⋙ ι ≅ associatedSheafFunctor α`
    whose component is the inverse of the chosen iso in
    `associatedSheafFunctor_obj`.  Naturality is exactly the conjugation used
    in `associatedSheafQCohFunctor.map`; prove it with
    `simp only [Category.assoc, Iso.hom_inv_id_assoc]`.
  * For a diagram `D` and a colimit cocone in `ModuleCat R`, map it by the
    QCoh functor.  After applying `ι`, the natural iso above and
    `associatedSheafFunctor_preserves_colimits α` give an `IsColimit` cocone
    in the ambient sheaf-module category.
  * Lift universal morphisms back to `QCoh X` using fullness of `ι`, and
    apply `IsColimit.ofFaithful ι` from
    `Mathlib/CategoryTheory/Limits/IsLimit.lean`; faithfulness proves
    uniqueness and `ObjectProperty.hom_ext` discharges equality of lifted
    arrows.
  * Package this for arbitrary `J : Type v`.  Do not infer ambient colimits
    in `QCoh X`; the mapped object itself is the chosen colimit.
  -/
  sorry

/-- The map from global sections to a stalk. -/
noncomputable def globalToStalkRing
    {X : RingedSpace.{v}} (x : X) :
    globalSectionsRing X →+*
      TopCat.Presheaf.stalk (C := RingCat.{v}) X.structureSheaf.obj x :=
  (TopCat.Presheaf.Γgerm (C := RingCat.{v}) X.structureSheaf.obj x).hom

/-- The canonical module `O_{X,x} ⊗_R M`. -/
noncomputable abbrev StalkTensorProduct
    {X : RingedSpace.{v}} {R : Type v} [Ring R]
    (α : R →+* globalSectionsRing X) (M : Type v)
    [AddCommGroup M] [Module R M] (x : X)
    (hR : ∀ a b : R, a * b = b * a)
    (hA : ∀ a b : TopCat.Presheaf.stalk (C := RingCat.{v}) X.structureSheaf.obj x,
      a * b = b * a) :
    ModuleCat (TopCat.Presheaf.stalk (C := RingCat.{v}) X.structureSheaf.obj x) :=
  let A := TopCat.Presheaf.stalk (C := RingCat.{v}) X.structureSheaf.obj x
  let ringR : Ring R := inferInstance
  let ringA : Ring A := inferInstance
  letI : CommRing R := { ringR with mul_comm := hR }
  letI : CommRing A := { ringA with mul_comm := hA }
  (ModuleCat.extendScalars ((globalToStalkRing x).comp α)).obj
    (ModuleCat.of R M)

theorem associatedSheaf_stalk_iso
    {X : RingedSpace.{v}} {R : Type v} [Ring R]
    (α : R →+* globalSectionsRing X) (M : Type v)
    [AddCommGroup M] [Module R M] (x : X)
    (hR : ∀ a b : R, a * b = b * a)
    (hA : ∀ a b : TopCat.Presheaf.stalk (C := RingCat.{v}) X.structureSheaf.obj x,
      a * b = b * a) :
    Nonempty ((sheafModuleStalkFunctor X.structureSheaf x).obj
        (associatedSheaf α M) ≅ StalkTensorProduct α M x hR hA) := by
  /-
  Proof roadmap:
  * Install local `CommRing R` and `CommRing A` instances exactly as in
    `StalkTensorProduct`, where
    `A := TopCat.Presheaf.stalk X.structureSheaf.obj x`; name both instances
    before invoking tensor APIs so typeclass search uses the same structures.
  * Remove sheafification on stalks using
    `TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso` from
    `Mathlib/Topology/Sheaves/Sheafify.lean`, applied to the underlying
    additive presheaf of
    `associatedSheafPresheaf α (ModuleCat.of R M)`.
  * Compute the remaining stalk by its universal property.  Use the
    `PresheafOfModules.pullbackPushforwardAdjunction` defining
    `changeOfRingsCore`, commute its left adjoint with the filtered stalk
    colimit, and identify the stalk of `constantModulePresheaf M` with `M`
    (all transition maps are `ModuleCat.restrictScalarsId'`).  After the
    local commutative-ring instances are installed, the resulting Hom
    equivalence is `ModuleCat.extendRestrictScalarsAdj` for
    `(globalToStalkRing x).comp α`.
  * Identify that stalk ring map using
    `TopCat.Presheaf.map_germ_eq_Γgerm` from
    `Mathlib/Topology/Sheaves/Stalks.lean`, then use Yoneda and
    `ModuleCat.hom_ext` to obtain the object iso.  Unfold only
    `associatedSheaf` and `StalkTensorProduct` for the final `simpa`.
  -/
  sorry

/-- The induced `R`-module of global sections. -/
noncomputable abbrev globalSectionsModule
    {X : RingedSpace.{v}} {R : Type v} [Ring R]
    (α : R →+* globalSectionsRing X) (G : Mod X.structureSheaf) : ModuleCat R :=
  (ModuleCat.restrictScalars α).obj
    ((SheafOfModules.evaluation X.structureSheaf (op (⊤ : Opens X.carrier))).obj G)

theorem associatedSheaf_hom_equiv
    {X : RingedSpace.{v}} {R : Type v} [Ring R]
    (α : R →+* globalSectionsRing X) (M : Type v)
    [AddCommGroup M] [Module R M] (G : Mod X.structureSheaf) :
    Nonempty ((associatedSheaf α M ⟶ G) ≃
      (ModuleCat.of R M ⟶ globalSectionsModule α G)) := by
  /-
  Proof roadmap:
  * Use
    `(PresheafOfModules.sheafificationAdjunction
      (𝟙 X.structureSheaf.obj)).homEquiv` to turn a sheaf morphism out of
    `associatedSheaf α M` into a presheaf-module morphism out of
    `associatedSheafPresheaf α (ModuleCat.of R M)`.
  * Apply
    `PresheafOfModules.pullbackPushforwardAdjunction
      (globalSectionsPresheafMap α).hom` to move change of rings to the
    target.  This leaves maps from `constantModulePresheaf M` to the
    restriction of `G.val`.
  * Construct the remaining equivalence explicitly: evaluate a natural
    transformation at `op ⊤`; conversely, restrict the resulting
    `R`-linear map along the unique arrows `U ⟶ ⊤`.  Naturality follows
    from `G.val.map_comp`, and the inverse laws follow by extensionality at
    each open.  Its codomain is definitionally
    `globalSectionsModule α G`.
  * Compose the three `Equiv`s and return it in `Nonempty`.  Use
    `PresheafOfModules.sheafificationAdjunction_homEquiv_apply` to control the
    first reduction instead of unfolding the adjunction.
  -/
  sorry

/-! ## Restriction and local presentation -/

/-- The map on global sections attached to a ringed-space morphism. -/
noncomputable def ringedSpaceGlobalSectionsMap
    {X Y : RingedSpace.{v}} (g : RingedSpaceHom Y X) :
    globalSectionsRing X →+* globalSectionsRing Y := by
  have h := (g.sharp.hom.app (op (⊤ : Opens X.carrier))).hom
  change X.structureSheaf.obj.obj (op (⊤ : Opens X.carrier)) →+*
    Y.structureSheaf.obj.obj
      (op ((Opens.map g.continuous).obj (⊤ : Opens X.carrier))) at h
  rw [Opens.map_top] at h
  exact h

/-- Scalar extension of a module. -/
noncomputable abbrev associatedScalarExtensionModule
    {R S : Type v} [Ring R] [Ring S]
    (hR : ∀ a b : R, a * b = b * a)
    (hS : ∀ a b : S, a * b = b * a)
    (β : R →+* S) (M : ModuleCat R) : ModuleCat S := by
  let ringR : Ring R := inferInstance
  let ringS : Ring S := inferInstance
  letI : CommRing R := { ringR with mul_comm := hR }
  letI : CommRing S := { ringS with mul_comm := hS }
  exact (ModuleCat.extendScalars β).obj M

theorem restrict_associatedSheaf
    {X Y : RingedSpace.{v}} (g : RingedSpaceHom Y X)
    [((SheafOfModules.pushforward (F := Opens.map g.continuous)
      g.sharp).IsRightAdjoint)]
    {R : Type v} [Ring R] (α : R →+* globalSectionsRing X) (M : ModuleCat R)
    (hR : ∀ a b : R, a * b = b * a)
    (hY : ∀ a b : globalSectionsRing Y, a * b = b * a) :
    Nonempty ((sheafModuleRingedSpacePullback g).obj (associatedSheafModule α M) ≅
      associatedSheafModule (RingHom.id _)
        (associatedScalarExtensionModule
          hR hY ((ringedSpaceGlobalSectionsMap g).comp α) M)) := by
  /-
  Proof roadmap:
  * Install the `CommRing R` and `CommRing (globalSectionsRing Y)` instances
    defined by `hR` and `hY`, once, before unfolding the scalar-extension
    object.
  * Rewrite the left side with `SheafOfModules.pullbackIso` from
    `Mathlib/Algebra/Category/ModuleCat/Sheaf/PullbackContinuous.lean` and
    expand `associatedSheafModule` only to its presheaf change-of-rings plus
    sheafification.  Use `SheafOfModules.sheafificationCompPullback` to move
    pullback past sheafification.
  * On presheaves, use `PresheafOfModules.pullbackComp` from
    `Mathlib/Algebra/Category/ModuleCat/Presheaf/Pullback.lean`; this works for
    the possibly noncommutative intermediate section rings.  Prove its
    composite scalar map is induced by
    `((ringedSpaceGlobalSectionsMap g).comp α)` using extensionality and the
    top component of `g.sharp`; `Opens.map_top` is the only open-set
    normalization required.
  * The resulting object is the presheaf defining the right side, with module
    `(ModuleCat.extendScalars ((ringedSpaceGlobalSectionsMap g).comp α)).obj
      M`; here `ModuleCat.extendScalars` is used only between the commutative
    endpoint rings supplied by `hR` and `hY`.  Apply sheafification's
    `mapIso`, fold
    `associatedScalarExtensionModule`, and compose the object isos.
  Avoid unfolding `ringedSpaceModulePullback`: the chosen-left-adjoint
  comparison is precisely what `SheafOfModules.pullbackIso` controls.
  -/
  sorry

/-- A fundamental system of quasi-compact neighbourhoods at a point. -/
def HasQuasiCompactNeighborhoodBasis {X : RingedSpace.{v}} (x : X) : Prop :=
  ∀ U : Opens X.carrier, x ∈ U →
    ∃ V : Opens X.carrier, x ∈ V ∧ V ≤ U ∧ IsCompact (V : Set X.carrier)

theorem exists_local_associatedSheaf
    {X : RingedSpace.{v}} {F : Mod X.structureSheaf} (x : X)
    (hX : HasQuasiCompactNeighborhoodBasis x) (hF : IsQuasiCoherent F) :
    ∃ U : Opens X.carrier, x ∈ U ∧
      ∃ M : ModuleCat (globalSectionsRing (ringedOpenSubspace X U)),
        Nonempty (((openModuleRestrictionFunctor X U).obj F) ≅
          associatedSheafModule (RingHom.id _) M) := by
  /-
  Proof roadmap (using the repaired quasi-compact-open basis):
  * From `isQuasiCoherent_iff_locallyPresented.mp hF` choose a presentation
    neighbourhood `W` of `x`.  Apply `hX W hxW` to choose an actual open
    `U : Opens X.carrier` with `x ∈ U`, `U ≤ W`, and
    `IsCompact (U : Set X.carrier)`.  The previous definition only produced
    a compact set whose interior need not be compact, which was insufficient.
  * Transport the presentation over `W` to the ringed open subspace `U` using
    `SheafOfModules.Presentation.map`, the iterated-over equivalence, and
    `openModuleRestrictionObjIso` from
    `lean/Formalization/Books/Sheaves/Unit24/Infrastructure.lean`.  Write its
    displayed map as `φ : free J ⟶ free I`.
  * Since `U` is compact, apply
    `sheafModuleSectionsDirectSumMap_bijective` from
    `lean/Formalization/Books/Modules/Unit03/AbelianCategory.lean` to both free
    sheaves.  Thus every column of `φ` is represented by a finite-support
    vector over `globalSectionsRing (ringedOpenSubspace X U)`, giving a
    `ModuleCat` morphism `φΓ : ModuleCat.free _ J ⟶ ModuleCat.free _ I`.
  * Let `M := cokernel φΓ`.  Apply
    `associatedPresentationMap_cokernel_iso (RingHom.id _)` to its canonical
    `ModulePresentation`, and identify its associated presentation map with
    `φ` by `SheafOfModules.freeHomEquiv.injective` and the two bijective
    sections comparisons.
  * Compose the resulting cokernel iso with `P.isColimit`'s
    `coconePointUniqueUpToIso` to identify the restricted `F` with
    `associatedSheafModule (RingHom.id _) M`.
  -/
  sorry

/-! ## The countable wedge example -/

abbrev CountableIndex : Type v := ULift.{v} ℕ
abbrev CountablePairIndex : Type v := ULift.{v} (ℕ × ℕ)

/-- A continuous cutoff which is zero near the origin and one outside a
larger compact interval. -/
structure CutoffFunction where
  toFun : ℝ → ℝ
  continuous_toFun : Continuous toFun
  zero_on : ∀ x ∈ Set.Ioo (-1 : ℝ) 1, toFun x = 0
  one_on : ∀ x, x ∈ Set.Iio (-2 : ℝ) ∨ x ∈ Set.Ioi 2 → toFun x = 1

instance : CoeFun CutoffFunction (fun _ => ℝ → ℝ) := ⟨CutoffFunction.toFun⟩

def scaledCutoff (f : CutoffFunction) (n : ℕ) : ℝ → ℝ :=
  fun x => f (n * x)

/-- Local finiteness of the branchwise coefficient sum. -/
def LocallyFiniteBranchCoefficients {X : RingedSpace.{v}}
    (c : ℕ → ℕ → X → ℝ) : Prop :=
  ∀ j x, ∃ U : Set X.carrier, IsOpen U ∧ x ∈ U ∧
    (Set.Finite {i | ∃ y ∈ U, c j i y ≠ 0})

/-- The characteristic coefficient of a branch, with the common origin
assigned value zero. -/
def branchIndicator {X : RingedSpace.{v}} (branch : Set X.carrier) (origin : X)
    (x : X) : ℝ :=
  by classical exact if x = origin then 0 else if x ∈ branch then 1 else 0

/-- A section of a free sheaf has finite free support when it comes from a
finite subcoproduct. -/
def HasFiniteFreeSupport {X : RingedSpace.{v}} (O : RingSheaf X.carrier)
    {I : Type v} (U : Opens X.carrier)
    (s : sheafModuleSections O (SheafOfModules.free I : Mod O) U) : Prop :=
  ∃ K : Finset I, ∃ t : sheafModuleSections O
      (SheafOfModules.free (↥K) : Mod O) U,
    sheafModuleSectionsMap O
      (SheafOfModules.freeMap (fun k : ↥K => k.1)) U t = s

/-- Projection from a free sheaf to the rank-one summand with a prescribed
index.  This is used to state that the analytic coefficients in the wedge
example really are the coordinate supports of its categorical sections. -/
noncomputable def freeCoordinateProjection {X : RingedSpace.{v}}
    (O : RingSheaf X.carrier) {I : Type v} (i : I) :
    (SheafOfModules.free I : Mod O) ⟶ SheafOfModules.unit O := by
  classical
  exact (SheafOfModules.freeHomEquiv (SheafOfModules.unit O)).symm
    (fun k => if k = i then
      (SheafOfModules.unit O).unitHomEquiv (𝟙 _) else
      (SheafOfModules.unit O).unitHomEquiv (0 :
        SheafOfModules.unit O ⟶ SheafOfModules.unit O))

/-- Failure of a finite matrix expression on the prescribed neighbourhoods. -/
def NotLocallyFiniteLinearCombination {X : RingedSpace.{v}}
    (φ : (SheafOfModules.free CountableIndex : Mod X.structureSheaf) ⟶
    (SheafOfModules.free CountablePairIndex : Mod X.structureSheaf))
    (U : ℕ → Opens X.carrier) : Prop :=
  ∀ n j, 2 * (n + 1) < j →
    ¬ HasFiniteFreeSupport X.structureSheaf (U (n + 1))
      (sheafModuleSectionsMap X.structureSheaf φ (U (n + 1))
        ((SheafOfModules.freeSection (R := X.structureSheaf)
          (ULift.up j)).eval (op (U (n + 1)))))

/-- Data of the countable wedge example in the source. -/
structure WedgeOfLinesExample where
  X : RingedSpace.{0}
  /-- The structure sheaf in the example is the sheaf of continuous
  real-valued functions. -/
  structureSheaf_is_continuousReal :
    X.structureSheaf =
      Formalization.Books.Sheaves.Unit22.realContinuousFunctionRingSheaf X.carrier
  origin : X
  neighbourhood : ℕ → Opens X.carrier
  origin_mem_neighbourhood : ∀ n, origin ∈ neighbourhood n
  neighbourhood_basis : ∀ U : Opens X.carrier, origin ∈ U →
    ∃ n, neighbourhood n ≤ U
  /-- The branches are the countably many copies of the real line glued at
  their common origin. -/
  line : ULift.{0} ℕ → ℝ → X
  line_continuous : ∀ i, Continuous (line i)
  line_cover : ∀ x, ∃ i t, line i t = x
  line_eq_iff : ∀ i j s t, line i s = line j t ↔
    (i = j ∧ s = t) ∨ (s = 0 ∧ t = 0)
  branches : ℕ → Set X.carrier
  branch_eq_range : ∀ i, branches i = Set.range (line (ULift.up i))
  branches_cover : ⋃ i, branches i = Set.univ
  branches_meet_only_at_origin : ∀ i j, i ≠ j →
    branches i ∩ branches j ⊆ {origin}
  /-- We index the source's neighbourhoods from `1` to avoid the
  meaningless expression `1 / 0` at index zero. -/
  neighbourhood_inter_branch : ∀ n i,
    (neighbourhood (n + 1) : Set X.carrier) ∩ branches i =
      line (ULift.up i) ''
        Set.Ioo (-(1 : ℝ) / ((n + 1 : ℕ) : ℝ))
          ((1 : ℝ) / ((n + 1 : ℕ) : ℝ))
  cutoff : CutoffFunction
  coordinate : X → ℝ
  coefficients : ℕ → ℕ → X → ℝ
  coefficient_continuous : ∀ j i, Continuous (coefficients j i)
  coefficient_formula : ∀ j i x,
    coefficients j i x =
      scaledCutoff cutoff j (coordinate x) * branchIndicator (branches i) origin x
  locallyFinite : LocallyFiniteBranchCoefficients coefficients
  map : (SheafOfModules.free (ULift.{0} ℕ) : Mod X.structureSheaf) ⟶
    (SheafOfModules.free (ULift.{0} (ℕ × ℕ)) : Mod X.structureSheaf)
  coefficientSections : ℕ →
    (SheafOfModules.free (ULift.{0} (ℕ × ℕ)) : Mod X.structureSheaf).sections
  /-- On every open, the `(i,j)` coordinate of `coefficientSections j`
  vanishes exactly when the prescribed coefficient function does.  This
  connects the analytic coefficient data to the categorical map; the former
  fields were otherwise independent of `coefficientSections`. -/
  coefficient_support : ∀ j i (U : Opens X.carrier),
    (∀ x ∈ U, coefficients j i x = 0) ↔
      ((freeCoordinateProjection X.structureSheaf
          (ULift.up (i, j))).val.app (op U)).hom
        ((coefficientSections j).eval (op U)) = 0
  map_on_generators : ∀ j,
    (SheafOfModules.freeHomEquiv
      (SheafOfModules.free (ULift.{0} (ℕ × ℕ)) : Mod X.structureSheaf) map)
        (ULift.up j) = coefficientSections j
  no_local_matrix : NotLocallyFiniteLinearCombination map neighbourhood

theorem exists_wedgeOfLinesExample : Nonempty WedgeOfLinesExample := by
  /-
  Proof roadmap:
  * Construct the metric hedgehog as the quotient of `ℕ × ℝ` identifying all
    `(i, 0)`.  Give representatives the distance `|s - t|` on one branch and
    `|s| + |t|` on different branches; prove it descends.  Equip the quotient
    with the topology generated by its metric balls and use
    `MetricSpace.ofDistTopology` from
    `Mathlib/Topology/MetricSpace/Defs.lean`, proving its open-set
    characterization together with separation and the triangle inequality.
    The maps `line i t := [(i,t)]` are isometric embeddings away from the
    common zero and satisfy `line_eq_iff`; take `origin := line 0 0`.
  * Put `neighbourhood 0 := ⊤` and, for `n + 1`, use the metric ball of
    radius `1/(n+1)` at the origin.  The metric-ball basis gives
    `neighbourhood_basis`, and direct distance calculation gives
    `neighbourhood_inter_branch`.  This is why
    `NotLocallyFiniteLinearCombination` now tests `U (n+1)` with the bound
    `2*(n+1) < j`; the old `U n` statement used an unspecified zeroth open and
    an off-by-one cutoff estimate.
  * Build `cutoff` from a continuous piecewise-linear function which is zero
    on `[-1,1]` and one outside `[-2,2]`, using `Continuous.if_le` (or the
    lattice operations `max`/`min`) from Mathlib topology.  Define
    `coordinate (line i t) := t`; the cross-branch distance inequality makes
    it Lipschitz.  Set
      `coefficients j i x := scaledCutoff cutoff j (coordinate x) *
        branchIndicator (branches i) origin x`.
    Continuity follows because the cutoff vanishes on a uniform ball at the
    origin; away from the origin only one branch meets a small ball.
  * Prove `locallyFinite`: at the origin use the ball of radius `1/(j+1)` so
    every coefficient is zero; elsewhere use a ball meeting only the unique
    branch.  On each such open form the finite sum of scalar multiples of
    `SheafOfModules.freeSection (ULift.up (i,j))`.  Glue these compatible local
    sections with the sheaf condition of `SheafOfModules.free` to obtain
    `coefficientSections j`.  The coordinate projections
    `freeCoordinateProjection` and sheaf extensionality prove
    `coefficient_support`.
  * Define `map := (SheafOfModules.freeHomEquiv _).symm
      (fun j ↦ coefficientSections j.down)`.  Then
    `map_on_generators` is `Equiv.apply_symm_apply`.
  * For `2*(n+1) < j`, every branch contains a point of
    `neighbourhood (n+1)` where the `(i,j)` coefficient equals one: choose
    `t` with `2/j < |t| < 1/(n+1)` and use `cutoff.one_on`.  A hypothetical
    `HasFiniteFreeSupport` has a finite index set `K`; choose a branch `i`
    whose `(i,j)` index is outside `K`, apply its coordinate projection, and
    contradict `coefficient_support`.  This proves `no_local_matrix`.
  Keep the construction in universe `0`; `CountableIndex` and
  `CountablePairIndex` then reduce to the displayed `ULift.{0}` types.
  -/
  sorry

end

end Formalization.Books.Modules.Unit10
