import Formalization.Books.Algebra.Unit14.BaseChange
import Formalization.Books.Algebra.Unit54.EssentiallyFiniteType
import Formalization.Books.Algebra.Unit56.GradedRings
import Formalization.Books.Algebra.Unit66.WeaklyAssociatedPrimes
import Formalization.Books.MoreAlgebra.Unit22.TorsionFree
import Mathlib.Algebra.DirectSum.Algebra
import Mathlib.Algebra.DirectSum.Decomposition
import Mathlib.Algebra.DirectSum.Module
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.RingTheory.FinitePresentation
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Localization.Algebra
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.Spectrum.Prime.Basic
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.Valuation.ValuationRing

namespace Formalization.Books.MoreAlgebra.Unit26

open scoped TensorProduct

universe u v

noncomputable section

/-- The source's finite family of prime localizations detecting elements of a
    ring.  The family is indexed by `Fin n`, so its codomain is the finite
    dependent product of the corresponding localizations. -/
def HasFinitePrimeLocalizationCover (R : Type u) [CommRing R] : Prop :=
  ∃ (n : ℕ) (p : Fin n → PrimeSpectrum R),
    Function.Injective
      (RingHom.pi (fun i => algebraMap R (Localization.AtPrime (p i).asIdeal)))

/-- Finite presentation of the canonical base-change module over the
    base-changed algebra.  This packages the local module notation `M_p`
    using the established `Unit14.baseChangeModule` construction. -/
def BaseChangeModuleFinitePresentation
    {R S R' M : Type*} [CommRing R] [CommRing S] [CommRing R']
    [AddCommGroup M] [Module S M]
    (f : R →+* S) (g : R →+* R') : Prop :=
  letI : Algebra R S := f.toAlgebra
  letI : Algebra R R' := g.toAlgebra
  Module.FinitePresentation (S ⊗[R] R')
    (Formalization.Books.Algebra.Unit14.baseChangeModule (M := M) f g)

/-- The local finite-presentation condition for the base-changed algebra
    `S_p` over `R_p`. -/
def IsPrimeLocallyFinitelyPresented
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (p : PrimeSpectrum R) : Prop :=
  RingHom.FinitePresentation
    (Formalization.Books.Algebra.Unit14.baseChangeRingMap
      (algebraMap R S) (algebraMap R (Localization.AtPrime p.asIdeal)))

/-- The local finite-presentation condition for `M_p` over `S_p`. -/
def IsPrimeLocallyFinitelyPresentedModule
    {R S M : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module S M] (p : PrimeSpectrum R) : Prop :=
  BaseChangeModuleFinitePresentation (M := M) (algebraMap R S)
    (algebraMap R (Localization.AtPrime p.asIdeal))

/-- Flatness, finite generation, the finite localization cover, and prime-local
    finite presentation imply finite presentation for a module over a
    polynomial algebra. -/
/-
Proof roadmap (`07ea6ace8add`, `4b7d04956892`).  The statement has been
audited against More Algebra, Lemma 053A: the local module really is the
`Unit14.baseChangeModule` appearing in `IsPrimeLocallyFinitelyPresentedModule`,
and no hypothesis needs changing.

The implementation should first add the focused imports
`Formalization.Books.Algebra.Unit39.FlatModules`,
`Formalization.Books.Algebra.Unit129.OpennessFlatLocus`, and
`Mathlib.RingTheory.LocalProperties.FinitePresentation`.  Keep the following
three bridges as small private lemmas before this theorem.

* A coefficient-localization bridge.  For `P := MvPolynomial (Fin n) R` and
  `p : PrimeSpectrum R`, identify `P ⊗[R] Localization.AtPrime p.asIdeal`
  with polynomials over `Localization.AtPrime p.asIdeal` using
  `Algebra.TensorProduct.commRight` followed by
  `MvPolynomial.algebraTensorAlgEquiv`.  Give the analogous linear equivalence
  between `Unit14.baseChangeModule (algebraMap R P) (algebraMap R R_p)` and
  localization of a `P`-module at
  `Submonoid.map (algebraMap R P) p.asIdeal.primeCompl`.  Prove naturality for
  `LinearMap.baseChange`.  The raw ingredients are in
  `Formalization/Books/Algebra/Unit14/BaseChange.lean` and
  `Mathlib/LinearAlgebra/TensorProduct/Tower.lean`; this API lemma is not
  currently present in Unit14.
* A finite-cover injectivity lemma: if
  `hcover = ⟨m, p, hp⟩ : HasFinitePrimeLocalizationCover R` and `N` is
  `R`-flat, then
  `N → ∀ i : Fin m, Localization.AtPrime (p i).asIdeal ⊗[R] N`,
  `x ↦ fun i ↦ 1 ⊗ₜ x`, is injective.  Apply
  `Module.Flat.lTensor_preserves_injective_linearMap` to the linear map
  underlying `RingHom.pi ...`, then conjugate by `TensorProduct.lid` and the
  finite-product equivalence `TensorProduct.piLeft` from
  `Mathlib/LinearAlgebra/TensorProduct/Pi.lean`.  This is the precise descent
  fact supplied by the injective product in `hcover`.
* An away-flatness bridge.  For a finitely presented `P`-module `N`, turn a
  point of the open set returned by
  `Formalization.Books.Algebra.Unit129.openness_flatness` into
  `Module.Flat R (LocalizedModule.Away g N)` on a basic neighbourhood `D(g)`.
  Use `PrimeSpectrum.isTopologicalBasis_basic_opens`,
  `PrimeSpectrum.localization_away_comap_range`, and
  `Formalization.Books.Algebra.Unit39.flat_iff_localized_over_primes`; the
  missing step is the equivalence between Unit129's
  `flatAtPrimeOverBaseRingHom` (Unit99's `flatAtPrimeOverBase`) and Unit39's
  `flat_at_prime_over` after the two successive localizations are identified.
  This bridge, rather than a second openness theorem, is the bounded
  Unit129/Unit39 API gap.

With those bridges in place, the proof follows the source literally.

1. Obtain `⟨r, f, hf⟩ := Module.Finite.exists_fin' P M`, with
   `f : (Fin r → P) →ₗ[P] M` surjective, and put `K := LinearMap.ker f`.
2. Fix `q : PrimeSpectrum P` and put
   `p₀ := PrimeSpectrum.comap (MvPolynomial.C : R →+* P) q`.  Destructure
   `hcover` as `⟨m, p, hp⟩`.  For every prime in the finite family
   consisting of `p₀` and the `p i`, use `hlocal`, the coefficient-localization
   bridge, and `Module.FinitePresentation.fg_ker` applied to the base change of
   `f` to see that the corresponding localization of `K` is finitely
   generated.  Lift finitely many generators with
   `IsLocalizedModule.mk'_surjective`, clear their finitely many denominators,
   and let `K' ≤ K` be their `P`-span.  Record explicitly that `K'.FG` and
   that `K'` and `K` have equal localizations at `p₀` and every `p i`.
3. Set `M' := (Fin r → P) ⨸ K'`.  It lives in the same universe as `R`
   and `P`, which is the important instantiation for Unit129's common
   universe `u`.  The quotient map and `K'.FG` give
   `Module.FinitePresentation P M'` via
   `Module.finitePresentation_of_surjective`; the polynomial map
   `R → P` is finitely presented.  At `q`, the equality at `p₀` identifies
   the prime localization of `M'` with that of `M`.  The latter is `R`-flat:
   combine `hflat` with Unit39's `flatness_descends_more_general` for the flat
   localization of `P`.  Hence `q` belongs to Unit129's open flat locus for
   `M'`.  Applying Unit129 here is not circular: `M'`, unlike the target `M`,
   is already finitely presented over `P`.
4. Choose `g ∉ q.asIdeal` with `D(g)` inside that locus, and use the
   away-flatness bridge to get `M'_g` flat over `R`.  The quotient map
   `π_g : M'_g → M_g` is surjective.  At every cover prime `p i` it is an
   isomorphism by the construction of `K'`.  Apply the finite-cover
   injectivity lemma to `M'_g`: if `π_g x = 0`, all localized images of `x`
   vanish, hence `x = 0`.  Thus `π_g` is an equivalence and `M_g` is
   finitely presented over `P_g`.
5. Let `good : Set P` be the set of such `g`.  Step 4 gives a good element
   outside every prime, so the good basic opens cover `Spec P`.
   `PrimeSpectrum.iSup_basicOpen_eq_top_iff'` turns this into
   `Ideal.span good = ⊤`.  Finish with
   `Module.FinitePresentation.of_localizationSpan good`, transporting along
   the `LocalizedModule.Away` equivalences from step 4.

Do not try to apply Unit129 openness directly to `M`: that assumes the finite
presentation being proved.  The finite approximation `M'` is what avoids
that dead end.
-/
theorem flat_finiteType_finitePresentation_local_module
    {R M : Type*} [CommRing R] (n : ℕ)
    [AddCommGroup M] [Module (MvPolynomial (Fin n) R) M]
    [Module.Finite (MvPolynomial (Fin n) R) M]
    (hcover : HasFinitePrimeLocalizationCover R)
    (hflat : letI : Module R M :=
      Module.compHom M (algebraMap R (MvPolynomial (Fin n) R));
      Module.Flat R M)
    (hlocal : ∀ p : PrimeSpectrum R,
      IsPrimeLocallyFinitelyPresentedModule
        (R := R) (S := MvPolynomial (Fin n) R) (M := M) p) :
    Module.FinitePresentation (MvPolynomial (Fin n) R) M := by
  sorry

/-- The ring-map version of the preceding local finite-presentation result. -/
/-
Proof roadmap (`ad4bb8b03114`).  This interface also matches Lemma 053B.  Its
proof is a reduction to
`flat_finiteType_finitePresentation_local_module`, not a second descent proof.

1. Use `Algebra.FiniteType.iff_quotient_mvPolynomial''` from
   `Mathlib/RingTheory/FiniteType.lean` to obtain
   `φ : P := MvPolynomial (Fin n) R →ₐ[R] S` surjective.  Install
   `φ.toRingHom.toAlgebra` and the induced `P`-module on `S`.  The
   surjective map `Algebra.linearMap P S` makes `S` a finite (indeed cyclic)
   `P`-module by `Module.Finite.of_surjective`.  Convert the given
   `Module.Flat R S` across `φ.commutes`; name the resulting instance so
   typeclass search does not compare two large `Module.compHom` terms.
2. For `p : PrimeSpectrum R`, base-change `φ` to a surjection
   `φ_p : P_p →ₐ[R_p] S_p`.  The local assumption supplies finite
   presentation of `S_p` over `R_p`, while Unit14's
   `baseChange_finite_presentation` supplies it for `P_p` over `R_p`.
   Therefore
   `Algebra.FinitePresentation.ker_fG_of_surjective φ_p` makes
   `ker φ_p` finitely generated, and
   `Module.finitePresentation_of_surjective (Algebra.linearMap P_p S_p)`
   makes `S_p` finitely presented as a `P_p`-module.
3. Transport step 2 through the coefficient-localization/base-change
   equivalence described in the preceding roadmap.  This is exactly the
   `IsPrimeLocallyFinitelyPresentedModule (S := P) (M := S) p` expected by
   the module theorem; no definitional equality between
   `(P ⊗[R] R_p) ⊗[P] S` and `S ⊗[R] R_p` should be requested from Lean.
4. Apply `flat_finiteType_finitePresentation_local_module` to obtain
   `Module.FinitePresentation P S`.  Turn this into
   `Algebra.FinitePresentation P S` using the instance
   `Algebra.FinitePresentation.of_finitePresentation` in
   `Mathlib/RingTheory/Finiteness/ModuleFinitePresentation.lean`, then finish
   with `Algebra.FinitePresentation.trans R P S` (the polynomial algebra is
   finitely presented over `R`).
-/
theorem flat_finiteType_finitePresentation_local
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.FiniteType R S] [Module.Flat R S]
    (hcover : HasFinitePrimeLocalizationCover R)
    (hlocal : ∀ p : PrimeSpectrum R,
      IsPrimeLocallyFinitelyPresented (R := R) (S := S) p) :
    Algebra.FinitePresentation R S := by
  sorry

/-- A finite flat graded module over a positively graded polynomial algebra
    over a local ring is finitely presented. -/
/-
Proof roadmap (`df1047963227`, `ef9f9f83a63e`).  The hypotheses are sound:
`GradedAlgebra 𝒜` puts constants in degree zero, `hX` fixes the variable
degrees, and positivity of `w` forces the degree-zero part of the polynomial
ring to be exactly the constants.  The missing object is a finite direct sum
of twists together with its component and base-change API; Unit56 currently
has only binary `directSumGradedModule`.

Add focused imports of `Formalization.Books.Algebra.Unit20.Nakayama` and
`Formalization.Books.Algebra.Unit78.FiniteProjectiveModules`.  Implement the
following construction in small private declarations before the theorem.

1. Package the supplied data as
   `G : Unit56.GradedRingData P` and
   `GM : Unit56.GradedModuleData G M`, where
   `P := MvPolynomial (Fin n) R`; the only non-definitional bridge is from
   `𝒜 d : Submodule R P` to its `toAddSubgroup`.  Prove once that the
   transferred `DirectSum.Decomposition` and `SetLike.GradedSMul` projections
   agree, instead of unfolding these structures downstream.
2. Establish the polynomial component lemma: `𝒜 d` is the `R`-span of
   the monomials `monomial a 1` with
   `∑ i in a.support, a i * w i = d`.  Use `hX`, graded multiplication, and
   `MvPolynomial.induction_on`; uniqueness comes from the existing direct-sum
   decomposition.  From `hw`, an exponent in degree `d` has every coordinate
   at most `d`, so this indexing set is finite.  Record in particular an
   `R`-linear equivalence `𝒜 0 ≃ₗ[R] R` and finite-free instances for
   every polynomial component.  This lemma is also the normalization needed
   after residue-field base change.
3. Obtain homogeneous generators
   `⟨r, deg, m, hm, hspan⟩` from
   `Formalization.Books.Algebra.Unit56.graded_finite_homogeneous_generators G GM`.
   Put `F := Fin r → P` and define its degree-`d` subgroup by
   `v i ∈ (Unit56.ringTwist G (-deg i)).component d`, i.e.
   `v i ∈ P_{d - deg i}`.  Build the decomposition coordinatewise (the
   finiteness of `Fin r` is essential), its graded scalar action, and the map
   `f := Fintype.linearCombination P m : F →ₗ[P] M`.  Prove `f` graded
   and surjective from `hspan`.  Let `K := LinearMap.ker f`; decompose `K` by
   intersecting with the shifted-free components.  Use
   `Unit56.graded_short_exact_iff_componentwise` for
   `K → F → M` to cache the exact sequence in every integral degree.
   Here `F` and `K` live in the universe of `P`, even when `M` is in a larger
   universe; all later residue-field constructions should retain that
   instantiation.
4. For each `d : ℤ`, give `M_d` its induced `R`-module.  Finiteness follows
   from `Unit56.graded_module_component_finite` after the degree-zero
   equivalence of step 2; flatness follows because component inclusion and
   `DirectSum.decompose` are `R`-linear retractions, using
   `Module.Flat.of_retract`.  Then
   `Formalization.Books.Algebra.Unit78.finite_flat_local_is_free` makes `M_d`
   finite free.  The shifted-free component `F_d` is finite free by step 2.
   Split `F_d → M_d` with `Module.projective_lifting_property`; its
   retraction makes `K_d` finite by `Module.Finite.of_surjective` (and flat by
   `Module.Flat.of_retract`).
5. Let `κ := IsLocalRing.ResidueField R` and
   `Pκ := MvPolynomial (Fin n) κ`.  Base-change the shifted presentation,
   conjugating the ring by `MvPolynomial.algebraTensorAlgEquiv R κ` and the
   module by the coefficient/base-change equivalence from the first roadmap.
   Since `κ` is a field and `Pκ` is finite type,
   `Algebra.FiniteType.isNoetherianRing κ Pκ` makes the homogeneous kernel
   `Kκ` finite.  Apply
   `Unit56.graded_finite_homogeneous_generators_submodule` to obtain finitely
   many homogeneous residue classes generating `Kκ`.  Lift them to
   homogeneous `k j : K` of degrees `e j`: use
   `TensorProduct.mk_surjective R κ K` (the residue map is surjective) and
   then take the required homogeneous component; naturality of the
   decomposition shows that its image is the original homogeneous class.
6. Let `g : (Fin t → P) →ₗ[P] K` be the shifted homogeneous map defined
   by the `k j`.  For every `d`, its component map
   `∏ j, P_{d-e j} → K_d` is surjective after reduction modulo the maximal
   ideal because the residue classes generate `Kκ`.  Apply
   `Formalization.Books.Algebra.Unit20.nakayama_part_six` with
   `I := IsLocalRing.maximalIdeal R`; the target `K_d` is finite by step 4 and
   `I ≤ Ring.jacobson R` is the local-ring Jacobson lemma.  Thus every
   component map is surjective.  Recompose elements with
   `DirectSum.sum_support_decompose` to prove `g` itself surjective.
7. `Module.Finite.of_surjective g` says `K` is finite, equivalently `K.FG`.
   Finish with `Module.finitePresentation_of_surjective f hf K.FG`.

Known dead ends: `Unit56.graded_nakayama_surjective` reduces modulo the
irrelevant ideal of `P`, whereas this proof reduces each `R`-finite component
modulo the maximal ideal of the local base.  Also
`Unit78.finite_flat_local_is_free` supplies component freeness only; it does
not construct the shifted presentation or homogeneous kernel generators.
-/
theorem flat_gradedPolynomial_finitePresentation_module
    {R M : Type*} [CommRing R] (n : ℕ)
    [AddCommGroup M] [Module (MvPolynomial (Fin n) R) M]
    (𝒜 : ℕ → Submodule R (MvPolynomial (Fin n) R))
    (𝓜 : ℤ → AddSubgroup M)
    (w : Fin n → ℕ) (hw : ∀ i, 0 < w i)
    (hX : ∀ i, MvPolynomial.X i ∈ 𝒜 (w i))
    [GradedAlgebra 𝒜] [DirectSum.Decomposition 𝓜]
    [SetLike.GradedSMul 𝒜 𝓜]
    [IsLocalRing R] [Module.Finite (MvPolynomial (Fin n) R) M]
    (hflat : letI : Module R M :=
      Module.compHom M (algebraMap R (MvPolynomial (Fin n) R));
      Module.Flat R M) :
    Module.FinitePresentation (MvPolynomial (Fin n) R) M := by
  sorry

/-- The two graded finite-type finite-presentation conclusions from the
    source, for the algebra and for a finite flat graded module. -/
/-
Proof roadmap (`df1047963227`, `ef9f9f83a63e`).  This statement matches More
Algebra, Lemma 053D; in particular `[Module.Finite R (𝒜 0)]` is exactly
the source hypothesis that the degree-zero algebra is finite over `R`.

1. Let `S₀ := 𝒜 0`, with its canonical algebra structure supplied by
   `SetLike.GradeZero.instAlgebra`.  From `Algebra.FiniteType R S` obtain
   `Algebra.FiniteType S₀ S` using
   `Algebra.FiniteType.of_restrictScalars_finiteType`.  Repeat the finite
   homogeneous decomposition used by Unit56's private
   `exists_finite_homogeneous_ring_generators` to get finitely many
   `t i ∈ 𝒜 (w i)` generating `S` over `S₀`; discard degree-zero
   entries, since they already lie in `S₀`, so `0 < w i`.  This helper must
   be local to Unit26 (or later exposed publicly by Unit56); the current
   declaration in `Formalization/Books/Algebra/Unit56/GradedRings.lean` is
   private and cannot be named by the consumer.
2. Set `P := MvPolynomial (Fin n) R` and
   `φ := MvPolynomial.aeval t : P →ₐ[R] S`.  Give `P` its canonical
   `w`-weighted grading from step 2 of the preceding roadmap, and prove `φ`
   is graded.  The finite `R`-module generators of `S₀`, multiplied by
   polynomials in the `t i`, generate `S` as a `P`-module; package this as
   `Module.Finite P S` using `Module.Finite.of_surjective`.  Consequently any
   finite `S`-module is finite over `P` by
   `Module.Finite.of_restrictScalars_finite P S M`.  Cache the scalar-tower
   equalities showing that restriction along `R → P → S` gives the
   original `R`-actions on `S` and `M`.
3. For each `p : PrimeSpectrum R`, put `R_p := Localization.AtPrime p.asIdeal`.
   Base-change the weighted polynomial grading, `φ`, and the graded module
   decomposition.  Conjugate
   `P ⊗[R] R_p` to `MvPolynomial (Fin n) R_p` with
   `Algebra.TensorProduct.commRight` and
   `MvPolynomial.algebraTensorAlgEquiv`.  Unit39's `flat_base_change` gives
   flatness of the base-changed `S` or `M` over the local ring `R_p`, and
   Unit14's `baseChange_finite_module` gives finiteness over the base-changed
   polynomial ring.  Apply
   `flat_gradedPolynomial_finitePresentation_module` over `R_p`, then
   transport its result back to the exact
   `BaseChangeModuleFinitePresentation φ (algebraMap R R_p)` model.  This is
   the required `hlocal` for the first theorem.
4. Module conclusion: under the two implication hypotheses, install the
   `P`-module on `M`, use step 2 for finiteness and step 3 for every local
   presentation, and apply
   `flat_finiteType_finitePresentation_local_module` with `hcover`.  This gives
   `Module.FinitePresentation P M`.  The map `φ` is finite, hence finite type
   (`RingHom.Finite.finiteType`); transfer the result to an `S`-presentation
   with
   `Formalization.Books.Algebra.Unit06.finitePresentation_module_over_finiteType`
   from `Formalization/Books/Algebra/Unit06/FiniteType.lean`.
5. Algebra conclusion: run the same argument with the graded `P`-module `S`
   to obtain `Module.FinitePresentation P S`.  Use
   `Algebra.FinitePresentation.of_finitePresentation P S` and then
   `Algebra.FinitePresentation.trans R P S` to obtain the required
   `Algebra.FinitePresentation R S`.

The only shared construction between steps 3 and the local theorem should be
the shifted/weighted base-change API described above; duplicating it with a
second choice of tensor-product associators is likely to create incompatible
module instances.
-/
theorem flat_graded_finiteType_finitePresentation
    {R S M : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module S M]
    (𝒜 : ℕ → Submodule R S) (𝓜 : ℤ → AddSubgroup M)
    [GradedAlgebra 𝒜] [DirectSum.Decomposition 𝓜]
    [SetLike.GradedSMul 𝒜 𝓜] [Algebra.FiniteType R S]
    [Module.Finite R (𝒜 0)]
    (hcover : HasFinitePrimeLocalizationCover R) :
    (Module.Flat R S → Algebra.FinitePresentation R S) ∧
      (letI : Module R M := Module.compHom M (algebraMap R S)
       Module.Flat R M → Module.Finite S M →
         Module.FinitePresentation S M) := by
  sorry

/- The source's presentation `0 → K → S^r → M → 0`, its localization
   diagram, and its componentwise shifted exact sequences require the bridge
   constructions recorded in the four roadmaps above.  They are deliberately
   left unimplemented here for the normal proof stage. -/

/-- A local ring has a finite prime-localization cover. -/
theorem hasFinitePrimeLocalizationCover_of_local
    {R : Type u} [CommRing R] [IsLocalRing R] :
    HasFinitePrimeLocalizationCover R := by
  sorry

/-- A Noetherian ring has a finite prime-localization cover. -/
theorem hasFinitePrimeLocalizationCover_of_noetherian
    {R : Type u} [CommRing R] [IsNoetherianRing R] :
    HasFinitePrimeLocalizationCover R := by
  sorry

/-- A domain has a finite prime-localization cover. -/
theorem hasFinitePrimeLocalizationCover_of_domain
    {R : Type u} [CommRing R] [IsDomain R] :
    HasFinitePrimeLocalizationCover R := by
  sorry

/-- A reduced ring with finitely many minimal primes has a finite
    prime-localization cover. -/
theorem hasFinitePrimeLocalizationCover_of_reduced
    {R : Type u} [CommRing R] [IsReduced R]
    (hminimal : (minimalPrimes R).Finite) :
    HasFinitePrimeLocalizationCover R := by
  sorry

/-- Finitely many weakly associated primes give a finite
    prime-localization cover. -/
theorem hasFinitePrimeLocalizationCover_of_finite_weaklyAssociatedPrimes
    {R : Type u} [CommRing R]
    (hfinite :
      (Formalization.Books.Algebra.Unit66.weaklyAssociatedPrimes R R).Finite) :
    HasFinitePrimeLocalizationCover R := by
  sorry

/-- Nagata's valuation-ring finite-presentation theorem, with its algebra and
    module conclusions recorded together. -/
theorem valuationRing_flat_finitePresentation
    {A B M : Type*} [CommRing A] [IsDomain A] [ValuationRing A]
    [CommRing B] [Algebra A B]
    [AddCommGroup M] [Module B M] [Module.Finite B M]
    [Algebra.FiniteType A B] :
    (Module.Flat A B → Algebra.FinitePresentation A B) ∧
      (letI : Module A M := Module.compHom M (algebraMap A B)
       Module.Flat A M → Module.FinitePresentation B M) := by
  sorry

/-- The local essentially-finite-type valuation-ring refinement. -/
theorem valuationRing_local_essFiniteType_finitePresentation
    {A B M : Type*} [CommRing A] [IsDomain A] [ValuationRing A]
    [CommRing B] [Algebra A B] [IsLocalRing B]
    [IsLocalHom (algebraMap A B)]
    [AddCommGroup M] [Module B M] [Module.Finite B M]
    (hess : RingHom.EssFiniteType (algebraMap A B)) :
    (Module.Flat A B →
        Formalization.Books.Algebra.Unit54.RingHom.EssFinitePresentation
          (algebraMap A B)) ∧
      (letI : Module A M := Module.compHom M (algebraMap A B)
       Module.Flat A M → Module.FinitePresentation B M) := by
  sorry

end

end Formalization.Books.MoreAlgebra.Unit26
