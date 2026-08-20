import Formalization.Books.Algebra.Unit17.Spectrum
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.Algebra.Module.LocalizedModule.Away
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.RingHom.FinitePresentation
import Mathlib.RingTheory.RingHom.FiniteType
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# Commutative Algebra, Chapter 118: Generic flatness

The source's localizations are represented by the canonical localization of the
target ring at the image of the base element and by `LocalizedModule.Away` for
the module.  The map from the localized base ring to the localized target is
the canonical `Localization.awayLift` map.
-/

namespace Formalization.Books.Algebra.Unit118

open Set

universe u v w

noncomputable section

/-! ## Localized pairs and the good condition -/

/-- The map `R_f → S_f` induced by a ring map `φ : R →+* S`.

The target localization is taken at `φ f`, so that a localized `S`-module is
canonically an `S_f`-module.  This is the source's notation `S_f` with its
canonical Mathlib model.
-/
noncomputable def localizedRingHom
    {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (f : R) :
    Localization.Away f →+* Localization.Away (φ f) := by
  exact Localization.awayLift
    ((algebraMap S (Localization.Away (φ f))).comp φ) f
    (by
      change IsUnit (algebraMap S (Localization.Away (φ f)) (φ f))
      exact IsLocalization.Away.algebraMap_isUnit (S := Localization.Away (φ f)) (φ f))

/-- Freeness of the localized module over the localized base ring. -/
def LocalizedModuleFreeOverBase
    {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (M : Type*) [AddCommGroup M] [Module S M]
    (f : R) : Prop :=
  let ψ := localizedRingHom φ f
  letI : Module (Localization.Away f)
      (LocalizedModule.Away (φ f) M) :=
    Module.compHom (LocalizedModule.Away (φ f) M) ψ
  Module.Free (Localization.Away f) (LocalizedModule.Away (φ f) M)

/-- Freeness of `S_f` as a module over `R_f`. -/
def LocalizedRingFreeOverBase
    {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (f : R) : Prop :=
  let ψ := localizedRingHom φ f
  letI : Algebra (Localization.Away f) (Localization.Away (φ f)) := ψ.toAlgebra
  Module.Free (Localization.Away f) (Localization.Away (φ f))

/-- The condition on `f` in the source's displayed good-locus equation.

The first two conjuncts are finite presentation of `S_f` over `R_f` and of
`M_f` over `S_f`; the last two are freeness of `S_f` and `M_f` over `R_f`.
-/
def GenericFlatnessCondition
    {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (M : Type*) [AddCommGroup M] [Module S M]
    (f : R) : Prop :=
  let ψ := localizedRingHom φ f
  RingHom.FinitePresentation ψ ∧
    Module.FinitePresentation (Localization.Away (φ f))
      (LocalizedModule.Away (φ f) M) ∧
      LocalizedRingFreeOverBase φ f ∧
      LocalizedModuleFreeOverBase φ M f

/-- The source's good locus, as the union of the principal opens satisfying
`GenericFlatnessCondition`. -/
def genericFlatnessLocus
    {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (M : Type*) [AddCommGroup M] [Module S M] :
    Set (PrimeSpectrum R) :=
  ⋃ f : {f : R // GenericFlatnessCondition φ M f},
    (PrimeSpectrum.basicOpen (f : R) : Set (PrimeSpectrum R))

/-- The good locus is open because it is a union of principal opens. -/
theorem isOpen_genericFlatnessLocus
    {R S M : Type*} [CommRing R] [CommRing S]
    [AddCommGroup M] [Module S M] (φ : R →+* S) :
    IsOpen (genericFlatnessLocus φ M) := by
  exact isOpen_iUnion fun _ => PrimeSpectrum.isOpen_basicOpen

/-! ## Generic freeness -/

/-- Generic freeness over a Noetherian domain (the first version in the
source). -/
/-
Proof roadmap (the statement and `LocalizedModuleFreeOverBase` interface are sound).

1. First isolate the polynomial generic-freeness argument as a helper.  A useful
   source-facing form takes a surjection
   `q : MvPolynomial (Fin n) R →+* S` satisfying
   `q.comp MvPolynomial.C = φ`, a finite `S`-module `M`, and returns the conclusion
   below.  Obtain `q` from `hfiniteType` with
   `Algebra.FiniteType.iff_quotient_mvPolynomial''` in
   `Mathlib/RingTheory/FiniteType.lean`.  The finite generating set for `M` remains
   finite after restriction along `q`; the relevant low-level lemma is
   `Submodule.FG.restrictScalars_of_surjective` in
   `Mathlib/RingTheory/Finiteness/Basic.lean`.
2. Prove that helper by the textbook leading-term/degree filtration on the finite
   module over `MvPolynomial (Fin n) R`.  No declaration currently packages this
   step.  The required missing result should keep the localization in the target
   `S`-module model and conclude
   `Module.Free (Localization.Away f)
     (LocalizedModule.Away (φ f) M)`, with its scalar action installed as
   `Module.compHom _ (localizedRingHom φ f)`.  Formulating the helper this way
   avoids a second missing equivalence between localization as a polynomial-ring
   module and localization as an `S`-module.
3. In the filtration proof, use Noetherianity only to make the coefficient/leading
   relation submodules finitely generated; clear the finitely many nonzero leading
   coefficients in `R`, multiply them to obtain `f`, and use `IsDomain R` to prove
   `f ≠ 0`.  After those coefficients are units in `Localization.Away f`, the
   standard monomials give a basis.  Install that basis with
   `Module.Free.of_basis` (`Mathlib/LinearAlgebra/FreeModule/Basic.lean`).
4. Apply the helper to `q` and rewrite its composite coefficient map by
   `q.comp MvPolynomial.C = φ`; its output is definitionally the requested custom
   predicate.

The alternative normalization route starts with
`Formalization.Books.Algebra.Unit115.noether_normalization_over_domain` in
`Formalization/Books/Algebra/Unit115/NoetherNormalization.lean`.  Its present
conclusion exposes only a bare ring equivalence between the two target
localizations.  Basis transport through this file's interface needs that equivalence
strengthened to an equivalence over `Localization.Away f`, commuting with both
`localizedRingHom`s; the existing result is therefore not by itself a usable
replacement for the polynomial helper.

Known dead end: do not apply
`Module.FinitePresentation.exists_free_localizedModule_powers` from
`Mathlib/RingTheory/Localization/Free.lean` to `M` over `R`.  It requires
`Module.FinitePresentation R M`; finite type of `S/R` and finiteness of `M/S` do
not imply even `Module.Finite R M` (take `S = R[X]`).
-/
theorem genericFlatness_noetherian
    {R S M : Type*} [CommRing R] [CommRing S] [IsNoetherianRing R]
    [IsDomain R] [AddCommGroup M] [Module S M]
    (φ : R →+* S) (hfiniteType : RingHom.FiniteType φ)
    (hM : Module.Finite S M) :
    ∃ f : R, f ≠ 0 ∧ LocalizedModuleFreeOverBase φ M f := by
  sorry

/-- Generic freeness for a finite-presentation algebra and module over a
domain (the second version in the source). -/
/-
Proof roadmap (the statement is sound; the missing part is a joint algebra/module
coefficient-spreading construction, not a change to the hypotheses).

1. Represent the algebra presentation by
   `P := Algebra.Presentation.ofFinitePresentation R S`.  The API in
   `Mathlib/RingTheory/Extension/Presentation/Core.lean` supplies the finitely
   generated domain `P.Core ⊆ R`, the finitely presented algebra
   `P.ModelOfHasCoeffs P.Core`, and
   `P.tensorModelOfHasCoeffsEquiv P.Core :
      R ⊗[P.Core] P.ModelOfHasCoeffs P.Core ≃ₐ[R] S`.
   Here `P.finite_coeffs`, `Algebra.FiniteType.adjoin_of_finite`, and
   `Algebra.FiniteType.isNoetherianRing ℤ P.Core` give Noetherianity, while the
   subalgebra inclusion gives `IsDomain P.Core`.
2. Spread the module presentation at the same time.  Start with
   `Module.FinitePresentation.exists_fin' S M` from
   `Mathlib/Algebra/Module/FinitePresentation.lean`.  Lift the finitely many matrix
   coefficients through `P.tensorModelOfHasCoeffsEquiv`; enlarge `P.Core` by the
   finitely many `R`-coefficients occurring in those tensor expressions, rebuild
   `P.ModelOfHasCoeffs R₀`, and define `M₀` as the cokernel of the lifted finite
   matrix.  This should be packaged as a reusable pair-model theorem returning:
   a finite-type subalgebra `R₀ : Subalgebra ℤ R`, an `R₀`-algebra `S₀`, a finitely
   presented `S₀`-module `M₀`, an `R`-algebra equivalence
   `eS : R ⊗[R₀] S₀ ≃ₐ[R] S`, and an `eS`-semilinear equivalence from the
   base-changed `M₀` to `M`.  There is no such joint theorem in the current imports.
   Use `Formalization.Books.Algebra.Unit14.baseChangeModule`,
   `baseChange_finite_presentation_module`, and
   `baseChange_finite_presentation` from
   `Formalization/Books/Algebra/Unit14/BaseChange.lean` for the model and the
   forward finite-presentation facts.
3. Apply `genericFlatness_noetherian` to
   `algebraMap R₀ S₀ : R₀ →+* S₀` and `M₀`.  Supply finite type from finite
   presentation and module finiteness from the `Module.FinitePresentation`
   instance.  If its witness is `f₀ : R₀`, put `f : R := (f₀ : R)`; injectivity of
   the subalgebra inclusion and the witness's nonvanishing prove `f ≠ 0`.
4. Base-change the chosen basis from `Localization.Away f₀` to
   `Localization.Away f`, then transport it across the localized versions of `eS`
   and the semilinear module equivalence.  The target comparison must identify
   the result with `LocalizedModule.Away (φ f) M` and its
   `localizedRingHom φ f` scalar action.  This localized comparison is the second
   missing reusable construction; implement it via `IsLocalizedModule.iso` /
   `IsLocalizedModule.mapEquiv` in
   `Mathlib/RingTheory/Localization/Module.lean` and
   `LocalizedModule.equivTensorProduct` in
   `Mathlib/Algebra/Module/LocalizedModule/Basic.lean`.  Finish with
   `Module.Free.of_equiv`.

Known dead end: `Module.FinitePresentation.trans` requires `S` to be finitely
presented as an `R`-*module*.  `RingHom.FinitePresentation φ` only says that `S`
is finitely presented as an `R`-algebra, so this route is invalid for `R[X]`.
-/
theorem genericFlatness_finitelyPresented
    {R S M : Type*} [CommRing R] [CommRing S] [IsDomain R]
    [AddCommGroup M] [Module S M]
    (φ : R →+* S) (hfinitePresentation : RingHom.FinitePresentation φ)
    (hM : Module.FinitePresentation S M) :
    ∃ f : R, f ≠ 0 ∧ LocalizedModuleFreeOverBase φ M f := by
  sorry

/-- Generic freeness together with finite-presentation after localization.

This is the strongest of the three generic-flatness statements in the
source. -/
/-
Proof roadmap (all four conjuncts in `GenericFlatnessCondition` match the source).

1. Prove a focused generic finite-presentation helper
   `exists_finitePresentation_away` from `hfiniteType` and `hM`, producing
   `f₀ : R`, `f₀ ≠ 0`,
   `RingHom.FinitePresentation (localizedRingHom φ f₀)`, and
   `Module.FinitePresentation (Localization.Away (φ f₀))
      (LocalizedModule.Away (φ f₀) M)`.
   For the injective-base-map branch, base-change to `FractionRing R` using
   `Formalization.Books.Algebra.Unit14.baseChangeRingMap` and
   `baseChangeModule`.  The base-changed algebra is finitely presented by
   `RingHom.FinitePresentation.of_finiteType` because the fraction field is
   Noetherian, and the base-changed module is finitely presented by
   `Module.finitePresentation_of_finite` because that algebra is Noetherian.
   Descend the two finite presentations by clearing the finitely many
   denominators in their polynomial and matrix presentations.  Neither Mathlib
   nor an earlier chapter currently packages this simultaneous descent to one
   principal localization.  If `ker φ` contains `f₀ ≠ 0`, use that witness
   separately: the target localization away from `φ f₀ = 0` is subsingleton.
2. Put `R₀ := Localization.Away f₀`,
   `S₀ := Localization.Away (φ f₀)`,
   `M₀ := LocalizedModule.Away (φ f₀) M`, and
   `ψ := localizedRingHom φ f₀`.  Install `ψ.toAlgebra`; obtain
   `IsDomain R₀` from `IsLocalization.Away.isDomain` and `f₀ ≠ 0`.
3. Apply `genericFlatness_finitelyPresented ψ` twice: once to the regular
   `S₀`-module `S₀`, obtaining freeness of the localized ring over the localized
   base, and once to `M₀`.  Multiply the two witnesses in `R₀` and preserve both
   freeness statements under the further localization.  The ring finite-
   presentation conjunct is preserved by
   `RingHom.finitePresentation_localizationPreserves` in
   `Mathlib/RingTheory/RingHom/FinitePresentation.lean`; module finite
   presentation after base change is the instance in
   `Mathlib/Algebra/Module/FinitePresentation.lean`.
4. Flatten the resulting iterated localizations.  Write the final element of
   `R₀` as a fraction with `IsLocalization.mk'_surjective`; after replacing it by
   its numerator `a : R`, take `f := f₀ * a`.  Use
   `IsLocalization.Away.mul'`, `IsLocalization.Away.commutes`, and
   `IsLocalization.Away.mul_of_associated` from
   `Mathlib/RingTheory/Localization/Away/Basic.lean` for the rings.  A matching
   iterated-`LocalizedModule.Away` equivalence, together with the proof that its
   restricted scalar action is `localizedRingHom φ f`, is not packaged and must
   be added before this theorem.  Transport the two bases and the two finite-
   presentation instances across those equivalences, and assemble the four
   conjuncts in their definition order.

Do not try to invoke the preceding theorem directly from the original
`hfiniteType`/`hM`: over a non-Noetherian domain these hypotheses do not imply
finite presentation before localization.
-/
theorem genericFlatness
    {R S M : Type*} [CommRing R] [CommRing S] [IsDomain R]
    [AddCommGroup M] [Module S M]
    (φ : R →+* S) (hfiniteType : RingHom.FiniteType φ)
    (hM : Module.Finite S M) :
    ∃ f : R, f ≠ 0 ∧ GenericFlatnessCondition φ M f := by
  sorry

/-! ## Properties of the good locus -/

/-- The good locus is stable under extensions, represented by an exact pair of
`S`-linear maps with injective first map and surjective second map. -/
/-
Proof roadmap (the extension statement is sound).  The recorded claim that
localization exactness itself is absent is stale: only the custom product-away
transfer remains missing.

1. Unpack membership in both unions.  Obtain `a b : R` with
   `GenericFlatnessCondition φ M₁ a`,
   `GenericFlatnessCondition φ M₃ b`, and the point in both basic opens.  Set
   `h := a * b`; use `PrimeSpectrum.mem_basicOpen` and primality to put the point
   in `PrimeSpectrum.basicOpen h`.
2. First add a reusable monotonicity lemma
   `GenericFlatnessCondition.mul_right` saying that a condition at `a` remains
   true at `a * b`.  Its ring part uses
   `RingHom.finitePresentation_localizationPreserves`; its module finite-
   presentation part uses localization/base change; its two free parts use base
   change of a basis.  Compare iterated and one-step away localizations with
   `IsLocalization.Away.mul'`, `commutes`, and `mul_of_associated`.  The required
   module equivalence and the compatibility with `localizedRingHom` are the same
   missing construction identified in the roadmap for `genericFlatness`; prove
   it once and reuse it here.  Apply this lemma to the `M₁` condition at `a` and
   the `M₃` condition at `b` (commute the product for the latter).
3. At `h`, abbreviate
   `A := Localization.Away h`,
   `T := Localization.Away (φ h)`, and
   `Nᵢ := LocalizedModule.Away (φ h) Mᵢ`; install
   `(localizedRingHom φ h).toAlgebra`.  Define the `T`-linear maps
   `f_h := LocalizedModule.map (.powers (φ h)) f` and similarly `g_h`.
   After adding the focused import
   `Mathlib.Algebra.Module.LocalizedModule.Exact`, obtain exactness from
   `LocalizedModule.map_exact`, injectivity from
   `LocalizedModule.map_injective`, and surjectivity from
   `LocalizedModule.map_surjective`.
4. For finite presentation over `T`, identify `N₁` with `LinearMap.ker g_h`:
   cod-restrict `f_h` to the kernel, prove bijectivity using localized exactness
   and injectivity, and use `LinearEquiv.ofBijective`.  Transfer the endpoint
   finite-presentation instance with `Module.FinitePresentation.of_equiv`, then
   apply `Module.finitePresentation_of_ker g_h` and surjectivity of `g_h` to get
   finite presentation of `N₂`.  These declarations are in
   `Mathlib/Algebra/Module/FinitePresentation.lean`.
5. Restrict `f_h` and `g_h` from `T` to `A`.  Since `N₃` is free over `A`, it is
   projective (`Module.Projective.of_free`); use
   `Module.projective_lifting_property` and
   `Function.Exact.split_tfae'` to obtain
   `N₂ ≃ₗ[A] N₁ × N₃`.  Apply `Module.Free.prod` and
   `Module.Free.of_equiv` to make `N₂` free over `A`.  These APIs are in,
   respectively, `Mathlib/Algebra/Module/Projective.lean`,
   `Mathlib/Algebra/Exact/Basic.lean`, `Mathlib/LinearAlgebra/Basis/Prod.lean`,
   and `Mathlib/LinearAlgebra/FreeModule/Basic.lean`.
6. The ring finite-presentation and ring-freeness conjuncts do not depend on the
   module, so copy them from either endpoint condition at `h`; combine them with
   Steps 4 and 5, introduce the subtype witness `h`, and prove membership in the
   defining union.
-/
theorem genericFlatnessLocus_extension
    {R S M₁ M₂ M₃ : Type*} [CommRing R] [CommRing S]
    [AddCommGroup M₁] [AddCommGroup M₂] [AddCommGroup M₃]
    [Module S M₁] [Module S M₂] [Module S M₃]
    (φ : R →+* S) (f : M₁ →ₗ[S] M₂) (g : M₂ →ₗ[S] M₃)
    (hinjective : Function.Injective f)
    (hexact : Function.Exact f g)
    (hsurjective : Function.Surjective g) :
    genericFlatnessLocus φ M₁ ∩ genericFlatnessLocus φ M₃ ⊆
      genericFlatnessLocus φ M₂ := by
  sorry

/-- Localization of the good locus, expressed through the canonical
homeomorphism `Spec(R_f) ≃ D(f)`. -/
theorem genericFlatnessLocus_localize
    {R S M : Type*} [CommRing R] [CommRing S]
    [AddCommGroup M] [Module S M]
    (φ : R →+* S) (f : R) :
    genericFlatnessLocus (localizedRingHom φ f)
        (LocalizedModule.Away (φ f) M) =
      (Formalization.Books.Algebra.Unit17.standardOpenSpectrumHomeomorph f) ⁻¹'
        (Subtype.val ⁻¹'
          ((PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R)) ∩
            genericFlatnessLocus φ M)) := by
  sorry

/-- Density of the good locus can be checked on a dense open covered by
principal opens.  The local density hypotheses are read in the canonical
`Spec(R_f) ≃ D(f)` subspaces. -/
theorem genericFlatnessLocus_reduce
    {R S M : Type*} [CommRing R] [CommRing S]
    [AddCommGroup M] [Module S M]
    (φ : R →+* S) (V : Set (PrimeSpectrum R))
    (hVopen : IsOpen V) (hVdense : Dense V)
    {ι : Type u} (f : ι → R)
    (hcover : V = ⋃ i, (PrimeSpectrum.basicOpen (f i) : Set (PrimeSpectrum R)))
    (hlocal : ∀ i,
      Dense
        ((Formalization.Books.Algebra.Unit17.standardOpenSpectrumHomeomorph (f i)) ''
          genericFlatnessLocus (localizedRingHom φ (f i))
            (LocalizedModule.Away (φ (f i)) M))) :
    Dense (genericFlatnessLocus φ M) := by
  sorry

/-! ## The reduced-base theorem -/

/-- Over a reduced base, the good locus contains a dense open, with a basic
good neighborhood at every point of that open. -/
theorem exists_denseOpen_subset_genericFlatnessLocus
    {R S M : Type*} [CommRing R] [CommRing S] [IsReduced R] [AddCommGroup M]
    [Module S M]
    (φ : R →+* S) (hfiniteType : RingHom.FiniteType φ)
    (hM : Module.Finite S M) :
    ∃ V : Set (PrimeSpectrum R),
      IsOpen V ∧ Dense V ∧
        ∀ u ∈ V, ∃ f : R,
          u ∈ (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R)) ∧
            (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R)) ⊆ V ∧
              GenericFlatnessCondition φ M f := by
  sorry

/- The filtrations, polynomial presentations, fraction-field reductions, and
displayed short exact sequences occurring inside the textbook proofs are proof
scaffolding rather than additional chapter-level assertions.  The reusable
short-exact-sequence content is represented by the explicit `Function.Exact`,
injectivity, and surjectivity hypotheses of `genericFlatnessLocus_extension`.
-/

end

end Formalization.Books.Algebra.Unit118
