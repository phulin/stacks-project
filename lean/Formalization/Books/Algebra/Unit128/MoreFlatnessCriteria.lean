import Formalization.Books.Algebra.Unit03.BasicNotions
import Formalization.Books.Algebra.Unit99.CriteriaForFlatness
import Formalization.Books.Algebra.Unit101.FlatnessCriteriaArtinian
import Formalization.Books.Algebra.Unit104.CohenMacaulayRings
import Formalization.Books.Algebra.Unit106.RegularLocalRings
import Formalization.Books.Algebra.Unit127.ColimitsAndFinitePresentation
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.RingTheory.Localization.AtPrime.Basic

/-!
# Commutative Algebra, Chapter 128: More flatness criteria

This file records the source-facing interfaces in the section.  The local,
Cohen--Macaulay, regular-local, regular-sequence, finite-presentation,
restricted-scalar, Tor, and fibre constructions are the canonical interfaces
from earlier chapters and Mathlib.

The displayed Tor kernel identity and the localization diagrams in the source
are proof scaffolding for the surrounding lemmas.  They are therefore
accounted for in the theorem interfaces rather than duplicated as unreferenced
maps.
-/

namespace Formalization.Books.Algebra.Unit128

open Formalization.Books.Algebra.Unit60
open Formalization.Books.Algebra.Unit101
open Formalization.Books.Algebra.Unit104
open Formalization.Books.Algebra.Unit127
open CategoryTheory
open CategoryTheory.Limits

universe u

noncomputable section

/-! ## Shared source-facing notation -/

/-- The extension to `S` of the maximal ideal of the local base ring `R`. -/
def mappedMaximalIdeal
    {R S : Type u} [CommRing R] [CommRing S] [IsLocalRing R]
    (f : R →+* S) : Ideal S :=
  Ideal.map f (IsLocalRing.maximalIdeal R)

/-- Injectivity of the map induced by an `S`-linear map on the residue modules
of a local map.  The two quotients use the extension of the base maximal ideal,
which is the canonical `S`-module presentation of `m M` and `m N`. -/
def residueMapInjective
    {R S M N : Type u} [CommRing R] [CommRing S] [IsLocalRing R]
    [AddCommGroup M] [Module S M] [AddCommGroup N] [Module S N]
    (f : R →+* S) (u : M →ₗ[S] N) : Prop :=
  Function.Injective
    ((mappedMaximalIdeal f • (⊤ : Submodule S M)).mapQ
      (mappedMaximalIdeal f • (⊤ : Submodule S N)) u
      (Submodule.smul_top_le_comap_smul_top
        (mappedMaximalIdeal f) u))

/-! ## Miracle flatness and regular parameters -/

/-- Miracle flatness: the dimension formula forces a local map from a regular
local ring to a Cohen--Macaulay local ring to be flat. -/
theorem miracle_flatness
    {R S : Type u} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S]
    [IsNoetherianRing R] [IsNoetherianRing S]
    (f : R →+* S) [IsLocalHom f]
    (hR : IsRegularLocalRing R)
    (hS : IsCohenMacaulayLocalRing S)
    (hdim : ringKrullDim S =
      ringKrullDim R + ringKrullDim (S ⧸ mappedMaximalIdeal f)) :
    RingHom.Flat f := by
  /-
  Proof roadmap (reduce to the regular-parameter criterion; do not reproduce
  the source's dimension induction with the current API).

  First put a small private helper before this theorem:

      flat_of_regular_parameter_list
        (xs : List R)
        (hgen : Ideal.ofList xs = IsLocalRing.maximalIdeal R)
        (hRxs : RingTheory.Sequence.IsRegular R xs)
        (hSxs : RingTheory.Sequence.IsRegular S (xs.map f)) : RingHom.Flat f.

  For the helper set `d := xs.length` and `x := xs.get`; rewrite with
  `List.ofFn_get xs`.  The theorem
  `Formalization.Books.Algebra.Unit75.tor_one_span_range_isZero_of_isRegular`
  in `Unit75/TorGroups.lean` gives

      Tor₁^R(S, R ⧸ Ideal.span (Set.range x)) = 0.

  The ideal is the maximal ideal by `hgen`.  Hence the quotient module in
  `Formalization.Books.Algebra.Unit99.variant_local_criterion_flatness`
  (`Unit99/CriteriaForFlatness.lean`) is flat over the residue field
  `R ⧸ IsLocalRing.maximalIdeal R`; install its field structure with
  `Ideal.Quotient.field`.  Apply that criterion with `M := S` and the
  `R`-action `Module.compHom S f`, then transport the result across the
  definitional identification with `RingHom.Flat f`.  Keep the two bridge
  equalities explicit: `Ideal.ofList (List.ofFn x) = Ideal.span (Set.range x)`
  (as in the proof of the Unit75 theorem) and the equality between the
  restricted-scalar carrier and `S`.

  To use the helper here, construct a minimal generating list `xs` of the
  maximal ideal.  The needed upstream construction exists only as the private
  theorem `exists_minimalIdealGeneratingList` in
  `Unit106/RegularLocalRings.lean`, so recreate its short public-facing part
  locally from
  `(IsLocalRing.maximalIdeal R).fg_of_isNoetherianRing` and
  `Submodule.FG.exists_span_finset_card_eq_spanFinrank`: take the resulting
  finset's `toList` and prove `Unit106.IsMinimalIdealGeneratingList` by the
  same erase-index/cardinality argument.  After `letI : IsRegularLocalRing R
  := hR`, `Unit106.regular_ring_CM xs hmin` supplies `hRxs` and also identifies
  `xs.length` with `ringKrullDim R` through
  `IsRegularLocalRing.spanFinrank_maximalIdeal`.

  Finally apply
  `Unit104.regularSequence_iff_expected_quotient_dimension S hS (xs.map f)`.
  Its maximal-ideal membership premise follows from
  `IsLocalRing.map_nonunit f`; rewrite the quotient ideal by
  `Ideal.map_ofList` and `hgen`, obtaining exactly `mappedMaximalIdeal f`.
  The required dimension equality is `hdim`, with the preceding length
  equality and commutativity of addition.  This gives `hSxs`, and
  `flat_of_regular_parameter_list` finishes.

  This route uses only exported theorems.  The direct induction from the book
  currently stops at a genuine API boundary: the chosen element of
  `m_R \ (m_R^2 ∪ ⋃ Ass(S))` must be extended to a minimal generating
  list before `Unit106.regular_ring_CM` can prove that `R/(x)` is regular.
  -/
  sorry

/-- A regular system of parameters of a regular local base that becomes a
regular sequence in the target gives a flat local ring map. -/
theorem flat_of_regular_system_of_parameters
    {R S : Type u} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S]
    [IsNoetherianRing R] [IsNoetherianRing S]
    (f : R →+* S) [IsLocalHom f]
    (hR : IsRegularLocalRing R) (d : ℕ) (x : Fin d → R)
    (hx : IsRegularSystemOfParameters R d x)
    (hxs : RingTheory.Sequence.IsRegular S
      (List.ofFn (fun i => f (x i)))) :
    RingHom.Flat f := by
  /-
  Proof roadmap.

  Reuse the private `flat_of_regular_parameter_list` helper described at
  `miracle_flatness`, with `xs := List.ofFn x`.  The generator equality is
  `hx.2` after proving
  `Ideal.ofList (List.ofFn x) = Ideal.span (Set.range x)` by extensionality
  and `simp`; `hxs` is already the target regularity premise.

  It remains to obtain source regularity from
  `Unit106.regular_ring_CM` (`Unit106/RegularLocalRings.lean`).  Prove the
  following small list lemma first:

      regular_not_mem_eraseIdx
        (hs : RingTheory.Sequence.IsRegular S ys) (i : Fin ys.length) :
        ys.get i ∉ Ideal.ofList (ys.eraseIdx i.1).

  All entries of `ys` lie in the maximal ideal (this follows from regularity
  in a local ring).  Move `ys.get i` to the end using the standard
  `List.Perm` for `eraseIdx`; regularity is preserved by
  `IsLocalRing.isRegular_of_perm` from
  `Mathlib/RingTheory/Regular/RegularSequence.lean`.  Repeatedly use
  `RingTheory.Sequence.isRegular_cons_iff` (or its primed form) and
  `RingTheory.Sequence.IsRegular.quot_ofList_smul_nontrivial`; membership in
  the preceding ideal would make the final class zero, contradicting its
  regularity on the nontrivial quotient.

  Apply this lemma to `ys := List.ofFn (fun i => f (x i))`.  If `x i` lay in
  `Ideal.ofList ((List.ofFn x).eraseIdx i.1)`, mapping the membership along
  `f` and rewriting by `Ideal.map_ofList` would contradict the lemma.  Thus
  `List.ofFn x` satisfies the second field of
  `Unit106.IsMinimalIdealGeneratingList`; the first field is the generator
  equality above.  Install `hR` as the `IsRegularLocalRing R` instance and
  take the first projection of
  `Unit106.regular_ring_CM (List.ofFn x) hminimal` to get source regularity.
  The helper then closes the theorem.

  No extra equation `ringKrullDim R = d` should be added: although the local
  predicate `IsRegularSystemOfParameters` only records generation, target
  regularity forces this generating family to be minimal by the argument
  above, and regularity of `R` then forces the expected cardinality.
  -/
  sorry

/-! ## Directed colimits and finite presentation -/

/-- The transition-locality part of the systems used in Chapter 127 and in
the Noetherian square criterion.  `DirectedRingMapColimit.stagesAreLocal`
records locality of the vertical stage maps but not of either transition
map, so this contract has to be carried separately until the Chapter 127
structure exposes it as a field. -/
def HasLocalTransitionMaps
    {R S : Type u} [CommRing R] [CommRing S] {f : R →+* S}
    (D : DirectedRingMapColimit f) : Prop := by
  letI : Preorder D.index := D.indexPreorder
  exact
    (∀ {i j : D.index} (hij : i ≤ j),
      IsLocalHom ((D.sourceDiagram.map (homOfLE hij)).hom)) ∧
    ∀ {i j : D.index} (hij : i ≤ j),
      IsLocalHom (D.targetTransition hij)

/-- In a Chapter 127 local essentially-finite-presentation module colimit, a
flat target module is already flat over one of the source stages. -/
theorem colimit_eventually_flat
    {R S M : Type u} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S] {f : R →+* S} [IsLocalHom f]
    [AddCommGroup M] [Module S M]
    (D : DirectedLocalModuleEssentiallyFinitePresentation (M := M) f)
    (htrans : HasLocalTransitionMaps D.ringApproximation.base.colimit)
    (hflat : Module.Flat R
      ((ModuleCat.restrictScalars f).obj (ModuleCat.of S M))) :
    ∃ i, letI : Preorder D.ringApproximation.base.colimit.index :=
        D.ringApproximation.base.colimit.indexPreorder
      letI : Module
          (D.ringApproximation.base.colimit.sourceDiagram.obj i)
          (D.moduleApproximation.stage i).module :=
        Module.compHom (D.moduleApproximation.stage i).module
          (D.ringApproximation.base.colimit.stageMap i)
      Module.Flat
        (D.ringApproximation.base.colimit.sourceDiagram.obj i)
        (D.moduleApproximation.stage i).module := by
  /-
  Proof roadmap (the missing Tor-kernel action is the main construction).

  Write `C := D.ringApproximation.base.colimit` and, after installing
  `C.indexPreorder` once, abbreviate the stage objects by `R_i`, `S_i`, and
  `M_i`.  Install the local structures and vertical local homomorphism from
  `D.ringApproximation.base.localStages`.  Each stage is Noetherian: turn
  `D.ringApproximation.base.sourceEssFiniteType i` and
  `.targetEssFiniteType i` into `Algebra.EssFiniteType` instances using the
  relevant ring homomorphism's `toAlgebra`, then apply
  `Algebra.EssFiniteType.isNoetherianRing` from
  `Mathlib/RingTheory/Localization/Submodule.lean` first to `ℤ → R_i`
  and then to `R_i → S_i`.  The module `M_i` is finite by
  `(D.moduleApproximation.stage i).finite`.

  Fix `i` and put `m_i := IsLocalRing.maximalIdeal R_i`.  Use
  `Formalization.Books.Algebra.Unit75.tor_one_ideal_quotient_kernel`
  (`Unit75/TorGroups.lean`) to represent

      Tor₁^{R_i}(M_i, R_i/m_i)

  by `Unit75.idealTensorActionKernel m_i` of the restricted-scalar module.
  Add a local helper `stageTorKernel` which equips this kernel with its
  canonical `S_i`-module action (act on the `M_i` tensor factor), proves the
  inclusion/action map is `S_i`-linear, and transports the Unit75 isomorphism
  back to an `R_i`-linear equivalence.  Since `m_i` is finite over the
  Noetherian ring `R_i`, `M_i` is finite over `S_i`, and `S_i` is Noetherian,
  the tensor target and then this kernel are finite as `S_i`-modules.  This
  `S_i`-finite structure is not supplied by Unit75: `idealTensorActionKernel`
  is currently bundled only over `R_i`.

  Choose finitely many `S_i`-generators of `stageTorKernel`.  Flatness of the
  target says their images in the corresponding kernel over `R` vanish.
  Express those comparison maps using the cocone legs of `C.sourceCocone`,
  `C.targetCocone`, and `D.moduleApproximation.cocone`, together with
  `D.moduleApproximation.stageIso` and `targetIso`.  Apply
  `CategoryTheory.Limits.Types.FilteredColimit.isColimit_eq_iff'` from
  `Mathlib/CategoryTheory/Limits/Types/Filtered.lean` to each generator, then
  use `Finset.exists_le` to choose one common `j ≥ i`.  Naturality must be
  stated as a separate helper identifying the resulting map with
  `(Unit99.canonicalTorOneSquareMapData f_i g_ij h_ij f_j m_i M_i).map`, where
  `g_ij` is the source transition and `h_ij := C.targetTransition hij`.
  This proves that canonical Tor map is zero.

  Apply
  `Formalization.Books.Algebra.Unit99.another_variant_local_criterion_flatness`
  (`Unit99/CriteriaForFlatness.lean`) to the transition square.  Obtain its
  commutativity from `C.map.naturality (homOfLE hij)`; obtain
  `IsTensorProductLocalization` from
  `D.ringApproximation.transitionLocalization hij` (an at-prime localization
  is a localization); obtain locality of `g_ij` and `h_ij` from `htrans`, and
  locality of the vertical maps from `localStages`.  The ideal `m_i` is
  proper, and `M_i/m_i M_i` is flat over the field `R_i/m_i`.  The criterion
  therefore makes the base change of `M_i` flat over `R_j`; transport this
  across `D.moduleApproximation.transitionIso hij` using
  `Module.Flat.of_linearEquiv` to get the displayed conclusion at `j`.

  Known dead end: do not try to synthesize the two transition `IsLocalHom`
  instances from `stagesAreLocal`.  That predicate only covers the local
  stage rings and the vertical `R_i → S_i`; `Unit99` requires all four maps
  in the square.  The explicit `HasLocalTransitionMaps` hypothesis above repairs
  that under-specified Chapter 127 interface without adding Noetherian
  assumptions to the ambient rings.
  -/
  sorry

/-! ## Local maps and finitely presented modules -/

/-- The general finite-presentation version of the injectivity criterion: a
residue-injective map has injective source map and flat quotient. -/
theorem mod_injective_general
    {R S M N : Type u} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S]
    (f : R →+* S) [IsLocalHom f]
    [AddCommGroup M] [Module S M] [AddCommGroup N] [Module S N]
    (hS : f.EssFinitePresentation)
    (hM : Module.FinitePresentation S M)
    (hN : Module.FinitePresentation S N)
    (hNflat : Module.Flat R
      ((ModuleCat.restrictScalars f).obj (ModuleCat.of S N)))
    (u : M →ₗ[S] N)
    (hbar : residueMapInjective f u) :
    Function.Injective u ∧
      Module.Flat R
        ((ModuleCat.restrictScalars f).obj
          (ModuleCat.of S (N ⧸ LinearMap.range u))) := by
  /-
  Proof roadmap (ambient Noetherian hypotheses are intentionally absent).

  The source proof cannot call `Unit99.mod_injective` at `(R,S)`: that theorem
  in `Unit99/CriteriaForFlatness.lean` requires `[IsNoetherianRing S]`, while
  essential finite presentation over an arbitrary local `R` does not imply
  that instance.  Instead build a *single compatible approximation of the
  map* `u`.  The current Chapter 127 theorem
  `limitModuleEssentiallyFinitePresentation` only approximates one module at
  a time, so first add a local structure (or, preferably, add it upstream in
  `Unit127/ColimitsAndFinitePresentation.lean`) containing:

  * one `DirectedLocalEssFinitePresentationApproximation f` with
    `HasLocalTransitionMaps`;
  * `DirectedModuleColimitPresentation`s `DM` and `DN` for `M` and `N`;
  * maps `u_i : (DM.stage i).module →ₗ[S_i] (DN.stage i).module`;
  * commutative transition/base-change squares and an identification of the
    induced colimit map with `u`.

  Construct it from finite presentations of `M` and `N` and a finite matrix
  for `u`: choose lifts of the two presentation matrices and the map matrix at
  one common stage, then move to a later stage where the two matrix identities
  hold.  Use `Types.FilteredColimit.isColimit_eq_iff'` for those finitely many
  identities.  Define later stages by cokernels, exactly as the proof plan of
  `Unit127.limitModuleEssentiallyFinitePresentation`; this also supplies the
  required transition isomorphisms and the quotient/cokernel colimit
  identification.  Separate this construction from the theorem proof so Lean
  elaborates the large dependent stage types only once.

  Apply the preceding `colimit_eventually_flat` to `DN` and `hNflat`.  Enlarge
  the chosen index as needed; flatness persists under the prime-localization
  transition by `Module.Flat.baseChange` and
  `Module.Flat.of_linearEquiv`.  Thus obtain a Noetherian stage with `N_i`
  flat over `R_i`.

  Next descend residue injectivity.  Let `k_i := R_i/m_i` and `k := R/m`.
  Form the source comparison

      Ψ_i : (M_i/m_i M_i) ⊗[k_i] k → M/mM.

  The ring `(S_i/m_i S_i) ⊗[k_i] k` is essentially of finite type over the
  field `k`, hence Noetherian by
  `Algebra.EssFiniteType.isNoetherianRing`; consequently `ker Ψ_i` is
  finite.  Kill a finite generating set at one later stage using
  `Types.FilteredColimit.isColimit_eq_iff'` and `Finset.exists_le`.  This makes
  `Ψ_i` injective.  The square comparing the stage residue map of `u_i` with
  `residueMapInjective f u` then shows that

      M_i/m_i M_i → N_i/m_i N_i

  is injective.  State explicitly the bridge
  `m_i • ⊤` (restricted `R_i` scalars) =
  `(m_i.map (C.stageMap i)) • ⊤` (the `S_i`-submodule used by
  `residueMapInjective`); prove it by extensionality and `Algebra.smul_def`.

  Now install the stage algebra/scalar-tower instances and apply
  `Formalization.Books.Algebra.Unit99.mod_injective` with its `M` parameter
  instantiated by `N_i`, its `N` parameter by `M_i`, and
  `u := (u_i.restrictScalars R_i)`.  Stage Noetherianity is obtained exactly
  as in `colimit_eventually_flat`; stage finiteness comes from
  `FiniteModuleOver.finite`.  The result gives injectivity of `u_i` and
  `R_i`-flatness of `N_i/range(u_i)`.

  Finally propagate this pair of conclusions through all later transition
  base changes.  Flatness of the quotient makes tensoring the short exact
  sequence preserve injectivity; identify the later cokernels with the
  cokernel stages recorded by the compatible map approximation.  Injectivity
  of the colimit map follows from `Types.FilteredColimit.isColimit_eq_iff'`.
  Flatness of the target quotient follows from
  `Unit39.directLimit_ring_baseChange_flat` in
  `Unit39/FlatModules.lean`, followed by `Module.Flat.of_linearEquiv` for the
  colimit/cokernel identification.  Rewrite that cokernel as
  `N ⧸ LinearMap.range u` and its `R`-action as
  `(ModuleCat.restrictScalars f).obj` to assemble the required conjunction.

  Thus the missing `[IsNoetherianRing R]`/`[IsNoetherianRing S]` assumptions
  are not a statement defect; Noetherianity is used only at approximation
  stages.  Adding them here would prove only the older Unit99 lemma and would
  lose the content of Chapter 128.
  -/
  sorry

/-- The general Grothendieck criterion for a regular element in the closed
fibre. -/
theorem grothendieck_general
    {R S : Type u} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S]
    (f : R →+* S) [IsLocalHom f]
    (hS : f.EssFinitePresentation)
    (hflat : Module.Flat R
      ((ModuleCat.restrictScalars f).obj (ModuleCat.of S S)))
    (g : S)
    (hg : IsSMulRegular
      (S ⧸ (mappedMaximalIdeal f : Submodule S S)) g) :
    Module.Flat R
        ((ModuleCat.restrictScalars f).obj
          (ModuleCat.of S
            (S ⧸ (Ideal.span ({g} : Set S) : Submodule S S)))) ∧
      IsSMulRegular S g := by
  sorry

/-- The regular-sequence version of the general Grothendieck criterion. -/
theorem grothendieck_regular_sequence_general
    {R S : Type u} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S]
    (f : R →+* S) [IsLocalHom f]
    (hS : f.EssFinitePresentation)
    (hflat : Module.Flat R
      ((ModuleCat.restrictScalars f).obj (ModuleCat.of S S)))
    (xs : List S)
    (hxs : RingTheory.Sequence.IsRegular
      (S ⧸ (mappedMaximalIdeal f : Submodule S S))
      (xs.map (Ideal.Quotient.mk (mappedMaximalIdeal f)))) :
    RingTheory.Sequence.IsRegular S xs ∧
      (∀ i : Fin xs.length,
        Module.Flat R
          ((ModuleCat.restrictScalars f).obj
            (ModuleCat.of S
              (S ⧸ (Ideal.ofList (xs.take (i.1 + 1)) : Submodule S S))))) := by
  sorry

/-- The local finite-presentation Tor criterion for flatness. -/
theorem variant_local_criterion_flatness_general
    {R S M : Type u} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S]
    (f : R →+* S) [IsLocalHom f]
    [AddCommGroup M] [Module S M]
    (hS : f.EssFinitePresentation)
    (hM : Module.FinitePresentation S M)
    (I : Ideal R) (hI : I ≠ ⊤)
    (hTor :
      letI : Module R M := Module.compHom M f
      IsZero
        (Formalization.Books.Algebra.Unit99.tor
          (R := R) M (R ⧸ I) 1))
    (hflat :
      letI : Module R M := Module.compHom M f
      Module.Flat (R ⧸ I)
        (M ⧸ (I • (⊤ : Submodule R M)))) :
    Module.Flat R
      ((ModuleCat.restrictScalars f).obj (ModuleCat.of S M)) := by
  sorry

/-! ## Fibre criteria -/

/-- The fibre criterion for a chain of local ring maps. -/
theorem criterion_flatness_fibre
    {R S S' M : Type u} [CommRing R] [CommRing S] [CommRing S']
    [IsLocalRing R] [IsLocalRing S] [IsLocalRing S']
    (f : R →+* S) (g : S →+* S') (h : R →+* S')
    [IsLocalHom f] [IsLocalHom g] [IsLocalHom h]
    (comm : g.comp f = h)
    [AddCommGroup M] [Module S' M]
    (hS : f.EssFinitePresentation)
    (hS' : h.EssFinitePresentation)
    (hM : Module.FinitePresentation S' M)
    (hMnonzero : Nontrivial M)
    (hflat_fibre :
      letI : Module S M := Module.compHom M g
      Module.Flat (S ⧸ (mappedMaximalIdeal f : Submodule S S))
        (M ⧸ (mappedMaximalIdeal f • (⊤ : Submodule S M))))
    (hflat_base : Module.Flat R
      ((ModuleCat.restrictScalars h).obj (ModuleCat.of S' M))) :
    Module.Flat R
        ((ModuleCat.restrictScalars f).obj (ModuleCat.of S S)) ∧
      Module.Flat S
        ((ModuleCat.restrictScalars g).obj (ModuleCat.of S' M)) := by
  sorry

/-- The fibre criterion when the intermediate map is initially only
essentially of finite type. -/
theorem criterion_flatness_fibre_fp_over_ft
    {R S S' M : Type u} [CommRing R] [CommRing S] [CommRing S']
    [IsLocalRing R] [IsLocalRing S] [IsLocalRing S']
    (f : R →+* S) (g : S →+* S') (h : R →+* S')
    [IsLocalHom f] [IsLocalHom g] [IsLocalHom h]
    (comm : g.comp f = h)
    [AddCommGroup M] [Module S' M]
    (hS' : h.EssFinitePresentation)
    (hS : f.EssFiniteType)
    (hM : Module.FinitePresentation S' M)
    (hMnonzero : Nontrivial M)
    (hflat_fibre :
      letI : Module S M := Module.compHom M g
      Module.Flat (S ⧸ (mappedMaximalIdeal f : Submodule S S))
        (M ⧸ (mappedMaximalIdeal f • (⊤ : Submodule S M))))
    (hflat_base : Module.Flat R
      ((ModuleCat.restrictScalars h).obj (ModuleCat.of S' M))) :
    f.EssFinitePresentation ∧
      Module.Flat R
        ((ModuleCat.restrictScalars f).obj (ModuleCat.of S S)) ∧
      Module.Flat S
        ((ModuleCat.restrictScalars g).obj (ModuleCat.of S' M)) := by
  sorry

/-- The fibre criterion over a locally nilpotent ideal.  The nonzero-fibre
condition is the existing Chapter 101 `nontrivialFibreAt` predicate, and the
stalk conclusion is expressed by the canonical localized ring map. -/
theorem criterion_flatness_fibre_locally_nilpotent
    {R S S' M : Type u} [CommRing R] [CommRing S] [CommRing S']
    (f : R →+* S) (g : S →+* S') (h : R →+* S')
    (comm : g.comp f = h) (I : Ideal R)
    (hI : Formalization.Books.Algebra.Unit03.locallyNilpotentIdeal I)
    [AddCommGroup M] [Module S' M]
    (hfinite : f.FiniteType)
    (hfp : h.FinitePresentation)
    (hM : Module.FinitePresentation S' M)
    (hflat_fibre :
      letI : Module S M := Module.compHom M g
      Module.Flat (S ⧸ (I.map f))
        (M ⧸ ((I.map f) • (⊤ : Submodule S M))))
    (hflat_base : Module.Flat R
      ((ModuleCat.restrictScalars h).obj (ModuleCat.of S' M))) :
    Module.Flat S
        ((ModuleCat.restrictScalars g).obj (ModuleCat.of S' M)) ∧
      ∀ q : PrimeSpectrum S,
        nontrivialFibreAt (M := M) g q →
          RingHom.EssFinitePresentation
              ((algebraMap S (Localization.AtPrime q.asIdeal)).comp f) ∧
            RingHom.Flat
              ((algebraMap S (Localization.AtPrime q.asIdeal)).comp f) := by
  sorry

end

end Formalization.Books.Algebra.Unit128
