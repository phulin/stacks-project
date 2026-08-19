import Formalization.Books.Algebra.Unit75.TorGroups
import Formalization.Books.Algebra.Unit82.UniversallyInjective
import Formalization.Books.Algebra.Unit87
import Formalization.Books.Algebra.Unit96.Completion
import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import Mathlib.Algebra.DirectSum.Module
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.RingTheory.Ideal.Quotient.PowTransition
import Mathlib.RingTheory.Noetherian.Basic

/-!
# More on Algebra, Chapter 28: Completion and flatness

The completion is Mathlib's `AdicCompletion`.  Direct sums and products use
the canonical `DirectSum` and function-space module structures.  Inverse
systems are the canonical functors on opposite preorders, and Tor is the
canonical construction from Algebra, Chapter 75.
-/

namespace Formalization.Books.MoreAlgebra.Unit28

open CategoryTheory
open CategoryTheory.Limits
open Formalization.Books.Algebra.Unit75
open Formalization.Books.Algebra.Unit82
open Formalization.Books.Algebra.Unit96
open Formalization.Books.Categories.Unit21
open scoped DirectSum TensorProduct

universe u v

noncomputable section

/-! ## The completed direct sum and its product map -/

/- The completion of each coordinate is identified with the coordinate ring
   by the existing `AdicCompletion.ofLinearEquiv` under adic completeness. -/
/-- The canonical map from the completion of a direct sum of copies of `R` to
the corresponding product of copies of `R`. -/
noncomputable def completedDirectSumToProduct
    {R : Type u} [CommRing R] (I : Ideal R) (A : Type v)
    [IsAdicComplete I R] :
    AdicCompletion I (⨁ _ : A, R) →ₗ[R] (∀ _ : A, R) :=
  LinearMap.pi (fun a =>
    (AdicCompletion.ofLinearEquiv I R).symm.toLinearMap.comp
      ((AdicCompletion.map I (DirectSum.component R A (fun _ : A => R) a)).restrictScalars R))

/-- Under Noetherianity and completeness, the completed-direct-sum map is
universally injective. -/
theorem completedDirectSumToProduct_universallyInjective
    {R : Type u} [CommRing R] [IsNoetherianRing R] (I : Ideal R) (A : Type v)
    [IsAdicComplete I R] :
    universallyInjective (completedDirectSumToProduct I A) := by
  /-
  Proof roadmap (normal `prove` stage).

  * Keep the completeness hypothesis: it is exactly what turns every completed
    coordinate into an element of `R` through
    `AdicCompletion.ofLinearEquiv I R`.  First prove two coordinate lemmas for
    `completedDirectSumToProduct`: its `a`-coordinate followed by reduction
    modulo `I ^ n` is the `a`-component of `x.val n`, and consequently its image
    is the family `y : A → R` for which, for every `n`, only finitely many
    `y a` are nonzero modulo `I ^ n`.  The forward implication uses the finite
    support of the direct-sum representative of `x.val n`; the converse and
    injectivity use `AdicCompletion.ext`, `DirectSum.ext_component`, and
    `Formalization.Books.Algebra.Unit96.isAdicComplete_separated` from
    `Formalization/Books/Algebra/Unit96/Completion.lean`.

  * Import `Formalization.Books.Algebra.Unit51.MoreNoetherianRings` and
    `Formalization.Books.Algebra.Unit91.ExamplesAndNonExamples`.  The target
    product is flat by
    `Formalization.Books.Algebra.Unit91.modulePower_is_flat_and_mittagLeffler
    R A |>.1` (unfold
    `Formalization.Books.Algebra.Unit89.modulePower`).  Apply
    `Formalization.Books.Algebra.Unit82.universallyInjective_into_flat_iff` to
    reduce the goal to injectivity of
    `Formalization.Books.Algebra.Unit82.quotientMapByIdeal J
    (completedDirectSumToProduct I A)` for every finitely generated ideal
    `J`.

  * Fix such a `J`.  Use `Module.Finite.of_fg` and
    `Module.Finite.exists_fin'` to choose a finite free surjection
    `g : (Fin k → R) →ₗ[R] J`; compose it with `J.subtype`, and use `J.mkQ`
    for the quotient map.  Apply
    `Formalization.Books.Algebra.Unit51.map_artin_rees I` to the exact
    sequence `Fin k → R → R ⧸ J`.  Its second conclusion gives one constant
    `c` such that a coordinate in `J ∩ I ^ N` has a preimage under `g` lying
    in `I ^ (N - c) • ⊤`.

  * If a convergent family `y` lies coordinatewise in `J`, choose those
    Artin--Rees preimages.  Use separatedness to assign to each nonzero
    coordinate a largest useful `I`-adic order (and use zero as the preimage of
    a zero coordinate).  The finite-support condition for `y mod I ^ (n+c)`
    then shows that each of the `k` coefficient families is again convergent.
    Turn them into elements of the completed direct sum using the converse
    coordinate lemma, and sum their scalar multiples.  This proves the key
    equality
    `comap (completedDirectSumToProduct I A) (J • ⊤) = J • ⊤`.
    `Submodule.Quotient.eq` (or directly the definition of
    `quotientMapByIdeal`) now proves the required quotient-map injectivity.

  Do not try to obtain universal injectivity merely from ordinary injectivity:
  the Artin--Rees lifting is the step that supplies purity after arbitrary
  tensoring.
  -/
  sorry

/-! ## Flatness of completed direct sums -/

/-- The completion of an arbitrary direct sum of copies of a Noetherian ring
is flat over that ring. -/
theorem completedDirectSum_flat
    {R : Type u} [CommRing R] [IsNoetherianRing R] (I : Ideal R) (A : Type v) :
    Module.Flat R (AdicCompletion I (⨁ _ : A, R)) := by
  /-
  Proof roadmap (normal `prove` stage).

  * Put `S := Formalization.Books.Algebra.Unit96.ringCompletion I` and
    `K := I.map (algebraMap R S)`.  Import
    `Formalization.Books.Algebra.Unit97.CompletionForNoetherianRings`.
    `Formalization.Books.Algebra.Unit97.completion_is_noetherian_of_fg_quotient I
    I.fg_of_isNoetherianRing` supplies both `IsNoetherianRing S` and
    `IsAdicComplete K S`; `AdicCompletion.flat_of_isNoetherian` supplies
    `Module.Flat R S`.

  * Add a private `S`-linear equivalence implementing the source identity
    `(⨁ A, R)^ = (⨁ A, S)^`:
    `AdicCompletion I (⨁ _ : A, R) ≃ₗ[S]
      AdicCompletion K (⨁ _ : A, S)`.
    Construct it levelwise.  For every `n`,
    `Formalization.Books.Algebra.Unit96.completion_quotient_power_equiv I
    I.fg_of_isNoetherianRing n` identifies
    `S ⧸ Formalization.Books.Algebra.Unit96.completionPowerIdeal I n` with
    `R ⧸ I ^ n`, while
    `Ideal.map_pow` identifies `K ^ n` with that completion power ideal.
    Lift this equivalence coordinatewise to the finite-support direct sums and
    hence to their quotients.  Check compatibility with
    `Submodule.factorPow` using the displayed evaluation equation from
    `completion_quotient_power_equiv` and
    `AdicCompletion.transitionMap_comp_eval`; assemble the compatible level
    maps with `AdicCompletion.ext`.  Build the inverse from the inverse level
    equivalences and prove the two composites by extensionality.

  * Apply `completedDirectSumToProduct_universallyInjective K A` over `S`,
    then transport universal injectivity across the preceding domain
    equivalence.  By
    `Formalization.Books.Algebra.Unit91.modulePower_is_flat_and_mittagLeffler
    S A |>.1`, the product
    `A → S` is `S`-flat.  Let `q` be `Submodule.mkQ` for the range of the
    transported map.  Package
    `⟨injective, LinearMap.exact_map_mkQ_range _, Submodule.mkQ_surjective _,
      universallyInjective⟩` as a
    `Formalization.Books.Algebra.Unit82.universallyExact` sequence (ordinary
    injectivity follows by testing universal injectivity on the regular
    module and conjugating with `TensorProduct.rid`).  Then
    `Formalization.Books.Algebra.Unit82.flat_ends_of_universallyExact` gives
    `S`-flatness of the completed
    direct sum.

  * Finally transport this flatness back across the levelwise equivalence and
    use `Module.Flat.trans R S _` (the wrapper
    `Formalization.Books.Algebra.Unit39.module_flat_trans` is in
    `Formalization/Books/Algebra/Unit39/FlatModules.lean`) to obtain the stated
    `R`-flatness.

  The direct application of the preceding theorem over `R` is unavailable
  here because `R` is not assumed complete; passing to `S` is essential.
  -/
  sorry

/-! ## Strict Tor vanishing -/

/- The source's `A/I^n` is written as the canonical quotient module
   `A ⧸ (I^n • ⊤)`, so the transition map is exactly Mathlib's
   `Submodule.factorPow`. -/
/-- The transition map on the canonical Tor groups induced by a power
quotient transition. -/
noncomputable def torPowerTransition
    {A : Type u} [CommRing A] (I : Ideal A) (M : ModuleCat.{u} A)
    (p : ℕ) {m n : ℕ} (hmn : m ≤ n) :
    Tor M (ModuleCat.of A
      (A ⧸ (I ^ n • (⊤ : Submodule A A)))) p ⟶
      Tor M (ModuleCat.of A
        (A ⧸ (I ^ m • (⊤ : Submodule A A)))) p :=
  torMapSecond M
    (ModuleCat.of A (A ⧸ (I ^ n • (⊤ : Submodule A A))))
    (ModuleCat.of A (A ⧸ (I ^ m • (⊤ : Submodule A A))))
    (ModuleCat.ofHom (Submodule.factorPow I A hmn)) p

/- The source reference notes that the word “strict” was omitted from the
   published statement; the positive exponent below records the intended
   assertion. -/
/-- For a finite module over a Noetherian ring, the transition maps on positive
Tor groups of successive power quotients are eventually zero. -/
theorem torPowerTransition_eventually_zero
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    (M : ModuleCat.{u} A) [Module.Finite A (M : Type u)]
    (p : ℕ) (hp : 0 < p) :
    ∃ c : ℕ, 0 < c ∧
      ∀ n : ℕ, c ≤ n →
        torPowerTransition I M p (m := n - c) (n := n) (Nat.sub_le n c) = 0 := by
  /-
  Proof roadmap (normal `prove` stage).

  * Import `Formalization.Books.Algebra.Unit51.MoreNoetherianRings`.  Replace
    `p` by `k + 1` using `hp`, and choose
    `Ff : FiniteFreeResolution A M` with
    `Formalization.Books.Algebra.Unit71.exists_finite_free_resolution`.  Work
    first with `Formalization.Books.Algebra.Unit75.resolutionTor Ff.resolution`
    rather than the arbitrary resolution hidden in
    `Formalization.Books.Algebra.Unit75.Tor`.

  * Let `d : Ff.resolution.complex.X (k+1) ⟶
    Ff.resolution.complex.X k` be the differential.  Both terms are finite by
    `Ff.finite`.  Apply
    `Formalization.Books.Algebra.Unit51.artin_rees I
      (LinearMap.range d.hom)` in the
    finite module `Ff.resolution.complex.X k`; retain its positive constant
    `c`.  From its equality deduce the concrete lifting claim: for `c ≤ n`,
    if `d x ∈ I ^ n • ⊤`, then there is
    `y ∈ I ^ (n-c) • ⊤` with `d y = d x`.  Expand an element of
    `I ^ (n-c) • (I ^ c • ⊤ ⊓ range d)` and choose preimages of its finitely
    many range terms to construct `y`.

  * Prove that the homology map induced by
    `Submodule.factorPow I A (Nat.sub_le n c)` on
    `Formalization.Books.Algebra.Unit75.tensorComplex
      Ff.resolution.complex` is zero in degree `k+1`.  Via
    `TensorProduct.comm` followed by
    `TensorProduct.quotTensorEquivQuotSMul`, identify each tensor term with
    the corresponding quotient by `I ^ n`; then, via
    `Formalization.Books.Algebra.Unit71.chainHomologyQuotientIso`, represent a
    cycle by `x` in the finite free term.  The cycle condition says
    `d x ∈ I ^ n • ⊤`; choose `y` as above.  Exactness
    `Ff.resolution.resolution.exact_succ k` shows that `x-y` is a boundary,
    while `y` is zero modulo `I ^ (n-c)`.  Hence the image homology class is
    zero.  Use `ModuleCat.hom_ext` and extensionality of the explicit homology
    quotient to conclude that the whole map is `0`.

  * Compare the canonical resolution
    `Classical.choice
      (Formalization.Books.Algebra.Unit71.exists_free_resolution M)` with
    `Ff.resolution`
    by a resolution map lifting `𝟙 M`.  The induced maps are isomorphisms by
    `Formalization.Books.Algebra.Unit75.isIso_resolutionTorMap_of_isIso`.
    Prove the square with the
    second-variable `Submodule.factorPow` map commutes exactly as in the proof
    of `Formalization.Books.Algebra.Unit75.torMap_commute` (use
    `tensorComplexMap`,
    `tensorComplexMapRight`, and `HomologicalComplex.homologyMap_comp`).
    Cancel the comparison isomorphisms around the zero finite-resolution map;
    after unfolding `torPowerTransition`, this is the required equality.

  The available `Formalization.Books.Algebra.Unit75.TorLongExactSequence`
  exposes only the six-term
  degree-one segment, so induction on `p` through that interface is a dead
  end; the finite-resolution/Artin--Rees argument handles every positive
  degree uniformly.
  -/
  sorry

/-! ## Flat inverse limits -/

/- This is the canonical way to tensor every stage of an inverse system by a
   fixed module. -/
/-- The inverse system obtained by tensoring every stage on the left by `Q`. -/
abbrev tensorInverseSystem
    {A : Type u} [CommRing A] (Q : ModuleCat.{u} A)
    {I : Type v} [Preorder I]
    (F : InverseSystem I (ModuleCat.{u} A)) :
    InverseSystem I (ModuleCat.{u} A) :=
  F ⋙ MonoidalCategory.tensorLeft Q

/- The source's phrase “flat over `A/I^n`” includes the induced quotient
   action.  `Module.IsTorsionBySet.module` is the established project API for
   that action. -/
/-- A stage is flat over the indicated power quotient, with its quotient action
induced from the given `A`-module structure. -/
def IsFlatOverPowerQuotient
    {A : Type u} [CommRing A] (I : Ideal A) (n : ℕ)
    (M : ModuleCat.{u} A) : Prop :=
  ∃ h : Module.IsTorsionBySet A (M : Type u) ((I ^ n : Ideal A) : Set A),
    letI : SMul (A ⧸ I ^ n) (M : Type u) := h.hasSMul
    letI : Module (A ⧸ I ^ n) (M : Type u) := h.module
    Module.Flat (A ⧸ I ^ n) (M : Type u)

/-- A surjective inverse system of modules flat over its successive power
quotients has a flat inverse limit, and tensoring a finite module commutes
with that inverse limit. -/
theorem inverseLimit_flat
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    (F : InverseSystem ℕ (ModuleCat.{u} A))
    (hflat : ∀ n : ℕ, IsFlatOverPowerQuotient I n (F.obj (Opposite.op n)))
    (hsurj : ∀ n : ℕ,
      Function.Surjective ((F.map (opHomOfLE (Nat.le_succ n))).hom)) :
    Module.Flat A ((InverseSystemLimit F : ModuleCat.{u} A) : Type u) ∧
      ∀ (Q : ModuleCat.{u} A) [Module.Finite A (Q : Type u)],
        Nonempty ((MonoidalCategory.tensorLeft Q).obj (InverseSystemLimit F) ≅
          (InverseSystemLimit (tensorInverseSystem Q F) : ModuleCat.{u} A)) := by
  /-
  Proof roadmap (normal `prove` stage).

  The hypotheses are sound as written.  At `n = 0`,
  `IsFlatOverPowerQuotient I 0` forces `F.obj (op 0)` to be the zero module
  because `I ^ 0` contains `1`; this is the canonical zeroth quotient and
  does not affect the tail limit.  The displayed `hsurj` is precisely the
  successive-transition hypothesis used by
  `Formalization.Books.Algebra.Unit87.inverseSystem_map_surjective_of_successive`.

  * First establish a private pro-zero lemma.  If `Q` is finite and `p > 0`,
    then the inverse system `Tor_A(Q, F_n)` has a zero transition after one
    uniform shift.  For each `n`, unpack `hflat n` and use the flat
    `A/I^n`-action to identify
    `Tor_A(Q, F_n)` with
    `Tor_A(Q, A/I^n) ⊗_{A/I^n} F_n`.  Construct this identification from a
    finite free resolution of `Q`: quotient its tensor complex by `I^n` and
    use `Module.Flat.rTensor_exact` over `A/I^n` to commute homology with
    tensoring by `F_n`.  Check transition naturality using
    `Formalization.Books.Algebra.Unit75.torMapSecond_comp` and the defining
    naturality of the tensor
    complex.  Now apply `torPowerTransition_eventually_zero I Q p hp`; the
    Tor factor of the shifted transition is zero, so the whole transition is
    zero.  Use `Formalization.Books.Algebra.Unit75.torLeftRightIso_natural`
    whenever the stage module is
    in the first Tor variable.

  * For finite `Q`, install
    `Module.finitePresentation_of_finite A (Q : Type u)`, and obtain
    `n, m, q, d, hq, hdq` from
    `Module.FinitePresentation.exists_fin' A (Q : Type u)`.  Prove
    `(Formalization.Books.Algebra.Unit87.tensorPresentationKernelSystem d F).IsMittagLeffler`.
    Extend `d` one step to a finite free presentation of `ker d` (Noetherianity
    makes it finite).  At every stage, the quotient of
    `ker (d.rTensor F_n)` by the image of this preceding differential is
    `Tor_1^A(Q,F_n)`.  The image subsystem has surjective transitions by
    `hsurj`, while the quotient subsystem is pro-zero by the preceding
    lemma.  Verify stabilization directly with
    `Formalization.Books.Algebra.Unit86.isMittagLeffler_iff_eventualRange`:
    after the pro-zero shift, every
    element in a later kernel differs from an element lifted through the
    surjective image subsystem.  (Surjectivity of `F` alone does not make the
    kernel-system maps surjective.)

  * Feed this Mittag--Leffler result, `hdq`, `hq`, and `hsurj` to
    `Formalization.Books.Algebra.Unit87.tensor_inverseSystemLimit_iso_of_finitePresentation_of_surjective`
    from `Formalization/Books/Algebra/Unit87/InverseSystems.lean`.  Its output
    is definitionally the second conjunct after unfolding
    `tensorInverseSystem`.

  * For flatness, use
    `Formalization.Books.Algebra.Unit39.flat_criteria |>.out 0 3`.  Fix a finitely
    generated ideal `J`; it is finite over the Noetherian ring.  Apply the
    tensor/limit isomorphism just proved to `ModuleCat.of A J` and to
    `ModuleCat.of A A`.  For the short exact sequence
    `0 → J → A → A/J → 0`, choose at each stage the object supplied by
    `Formalization.Books.Algebra.Unit75.exists_tor_long_exact_sequence
      (F.obj (op n))`.  Its `exact₃`
    says the kernel of `J ⊗ F_n → A ⊗ F_n` is the image of
    `Tor_1(F_n,A/J)` after conjugating the displayed tensor maps by
    `TensorProduct.comm`.  A compatible element in the kernel at the limit
    can be lifted at a sufficiently high stage to this Tor group; transport
    it down by naturality.  The pro-zero lemma for `A/J` (and
    `torLeftRightIso_natural`) makes that transported Tor element zero.
    Thus every stage coordinate, hence the limit element, is zero.  Conjugate
    by the two tensor/limit isomorphisms to prove
    `Function.Injective (J.subtype.rTensor (InverseSystemLimit F))`, completing
    the flatness criterion.
  -/
  sorry

/-! ## Flatness after completion -/

/-- Flatness of the reduction together with vanishing first Tor implies that
completion is flat over the Noetherian completed ring. -/
theorem flat_after_completion
    {R : Type u} [CommRing R] (I : Ideal R)
    (M : ModuleCat.{u} R) (hI : I.FG)
    [IsNoetherianRing (R ⧸ I)]
    (hflat : Module.Flat (R ⧸ I)
      ((M : Type u) ⧸ (I • (⊤ : Submodule R (M : Type u)))))
    (htor : IsZero (Tor M (ModuleCat.of R (R ⧸ I)) 1)) :
    IsNoetherianRing (ringCompletion I) ∧
      Module.Flat (ringCompletion I) (completion I (M : Type u)) := by
  /-
  Proof roadmap (normal `prove` stage).

  * Import
    `Formalization.Books.Algebra.Unit97.CompletionForNoetherianRings` and
    `Formalization.Books.Algebra.Unit99.CriteriaForFlatness`.  Put
    `S := ringCompletion I` and `K := I.map (algebraMap R S)`.
    `Formalization.Books.Algebra.Unit97.completion_is_noetherian_of_fg_quotient
      I hI` immediately gives
    the first conjunct and `IsAdicComplete K S`; install its first component
    as the `IsNoetherianRing S` instance for the rest of the proof.

  * Convert `htor` to
    `IsZero (Formalization.Books.Algebra.Unit99.tor
      (R ⧸ I) (M : Type u) 1)` with `IsZero.of_iso` and
    `Formalization.Books.Algebra.Unit75.torLeftRightIso M
    (ModuleCat.of R (R ⧸ I)) 1`.  Apply
    `Formalization.Books.Algebra.Unit99.what_does_it_mean I hflat` to obtain,
    for every positive `n`,
    flatness of `M ⧸ I^n M` over `R ⧸ I^n`.  Handle `n = 0` separately by
    the subsingleton/zero-ring instances.

  * Define an inverse system `G : InverseSystem ℕ (ModuleCat S)` whose stage
    `n` is `M ⧸ (I ^ n • ⊤)`.  Give it the `S`-action obtained by restricting
    the canonical `R/I^n`-action along `AdicCompletion.evalₐ I n`; define its
    transitions with `Submodule.factorPow I (M : Type u)` and prove
    `S`-linearity from `AdicCompletion.transitionMap_comp_eval`.  The
    transitions are surjective by `Submodule.factor_surjective`.

  * Show `IsFlatOverPowerQuotient K n (G.obj (op n))`.  First prove
    `K ^ n = Formalization.Books.Algebra.Unit96.completionPowerIdeal I n`
    using `Ideal.map_pow` and the
    definitions.  Then use
    `Formalization.Books.Algebra.Unit96.completion_quotient_power_equiv I hI n`
    to identify `S/K^n` with
    `R/I^n`; the identity on the stage module is semilinear for this ring
    equivalence.  Transport the flatness obtained from
    `Formalization.Books.Algebra.Unit99.what_does_it_mean` across that
    ring/module equivalence (a small
    helper proved from `Module.Flat.iff_rTensor_injective'` is useful here),
    and exhibit the required `Module.IsTorsionBySet` witness from the fact
    that `K^n` lies in the kernel of `evalₐ`.

  * Apply `inverseLimit_flat K G` and keep its first component.  Finally build
    an `S`-linear equivalence
    `completion I (M : Type u) ≃ₗ[S] InverseSystemLimit G`: an adic-completion
    element is already a family in these stages, and its `property` is exactly
    the section compatibility.  In the reverse direction use
    `Types.isLimitEquivSections` after the forgetful functor; prove both
    composites with `AdicCompletion.ext` and `Concrete.limit_ext`.  Transport
    flatness along this equivalence with `Module.Flat.of_linearEquiv` and pair
    it with the Noetherianity result.

  Applying `inverseLimit_flat` over the original ring `R` yields only
  `R`-flatness and cannot prove the stated `S`-flatness; the rebased system
  `G` and the quotient equivalences are essential.
  -/
  sorry

end

end Formalization.Books.MoreAlgebra.Unit28
