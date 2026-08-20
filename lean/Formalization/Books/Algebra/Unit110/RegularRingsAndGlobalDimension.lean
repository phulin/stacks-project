import Formalization.Books.Algebra.Unit39.FlatModules
import Formalization.Books.Algebra.Unit60.Dimension
import Formalization.Books.Algebra.Unit78.FiniteProjectiveModules
import Formalization.Books.Algebra.Unit104.CohenMacaulayRings
import Formalization.Books.Algebra.Unit106.RegularLocalRings
import Formalization.Books.Algebra.Unit109.FiniteGlobalDimension
import Mathlib.RingTheory.LocalProperties.ProjectiveDimension

/-!
# Commutative Algebra, Chapter 110: Regular rings and global dimension

The chapter's projective dimensions and global dimensions use the canonical
interfaces from Chapter 109.  Finite free resolutions are represented by the
source-facing finite-free resolution predicate from that chapter, while local
regularity is Mathlib's `IsRegularLocalRing`.
-/

namespace Formalization.Books.Algebra.Unit110

open CategoryTheory
open Formalization.Books.Algebra.Unit109
open Formalization.Books.Algebra.Unit72
open IsLocalRing

universe u v

noncomputable section

/-! ## Regular local rings and finite global dimension -/

/- The displayed resolution
   `0 → F_(d-e) → ... → F₀ → M → 0` is the finite prefix encoded by
   `HasFiniteFreeResolutionWithFiniteTermsLE`. -/

private theorem resolution_hasProjectiveDimensionLE_of_free_prefix
    {R M : Type u} [CommRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M] (n : ℕ)
    (F : Formalization.Books.Algebra.Unit71.Resolution R (ModuleCat.of R M))
    (hfree : ∀ i : Fin n, Module.Free R (F.complex.X i : Type u))
    (hterminal : Module.Free R (F.complex.X n : Type u))
    (hcondition : (n = 0 → Function.Bijective F.augmentation.hom) ∧
      (0 < n → Function.Injective (F.complex.d n (n - 1)).hom)) :
    CategoryTheory.HasProjectiveDimensionLE (ModuleCat.of R M) n := by
  change CategoryTheory.HasProjectiveDimensionLT (ModuleCat.of R M) (n + 1)
  revert M
  induction n with
  | zero =>
      intro M _ _ F hfree hterminal hcondition
      have hbij := hcondition.1 rfl
      let e : F.complex.X 0 ≃ₗ[R] M :=
        LinearEquiv.ofBijective F.augmentation.hom hbij
      have hprojX : CategoryTheory.Projective (F.complex.X 0) := by
        let : Module.Free R (F.complex.X 0 : Type u) := hterminal
        exact ModuleCat.projective_of_free
          (Module.Free.chooseBasis R (F.complex.X 0 : Type u))
      have hprojM : CategoryTheory.Projective (ModuleCat.of R M) :=
        CategoryTheory.Projective.of_iso e.toModuleIso hprojX
      exact CategoryTheory.projective_iff_hasProjectiveDimensionLT_one.mp hprojM
  | succ n ih =>
      intro M _ _ F hfree hterminal hcondition
      let K : ModuleCat.{u} R := CategoryTheory.Limits.kernel F.augmentation
      let p : F.complex.X 1 ⟶ K :=
        CategoryTheory.Limits.kernel.lift F.augmentation (F.complex.d 1 0)
          F.augmentation_condition
      let C : Formalization.Books.Algebra.Unit71.ModuleChainComplex R :=
        { X := fun i => F.complex.X (i + 1)
          d := fun i j => F.complex.d (i + 1) (j + 1)
          shape := by
            intro i j hij
            apply F.complex.shape
            simp only [ComplexShape.down_Rel] at hij ⊢
            omega
          d_comp_d' := by
            intro i j k hij hjk
            apply F.complex.d_comp_d'
            · simp only [ComplexShape.down_Rel] at hij ⊢
              omega
            · simp only [ComplexShape.down_Rel] at hjk ⊢
              omega }
      have hpι : p ≫ CategoryTheory.Limits.kernel.ι F.augmentation =
          F.complex.d 1 0 := by
        exact CategoryTheory.Limits.kernel.lift_ι _ _ _
      have hpzero : F.complex.d 2 1 ≫ p = 0 := by
        apply (CategoryTheory.cancel_mono
          (CategoryTheory.Limits.kernel.ι F.augmentation)).1
        simp [hpι, F.complex.d_comp_d]
      have htail_exact : Function.Exact
          (F.complex.d 2 1).hom p.hom := by
        apply LinearMap.exact_iff.mpr
        apply le_antisymm
        · intro x hx
          have hx0 : p.hom x = 0 := (LinearMap.mem_ker).1 hx
          have hx' : (F.complex.d 1 0).hom x = 0 := by
            have h := congrArg (fun q => q.hom x) hpι
            simpa [hx0] using h.symm
          have hFexact : Function.Exact
              (F.complex.d 2 1).hom (F.complex.d 1 0).hom :=
            (CategoryTheory.ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp
              (F.exact_succ 0)
          have hxrange : x ∈ LinearMap.range (F.complex.d 2 1).hom := by
            rw [← (LinearMap.exact_iff.mp hFexact)]
            exact hx'
          exact hxrange
        · rw [LinearMap.range_le_ker_iff]
          ext y
          simpa using congrArg (fun q => q.hom y) hpzero
      have htail_zero : C.d 1 0 ≫ p = 0 := by
        exact hpzero
      have htail_exact_zero :
          (CategoryTheory.ShortComplex.mk (C.d 1 0) p htail_zero).Exact := by
        exact (CategoryTheory.ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mpr
          htail_exact
      have htail_exact_succ : ∀ k : ℕ,
          (CategoryTheory.ShortComplex.mk (C.d (k + 2) (k + 1))
            (C.d (k + 1) k) (C.d_comp_d (k + 2) (k + 1) k)).Exact := by
        intro k
        simpa [C] using F.exact_succ (k + 1)
      have htail_epi : Epi p := by
        exact (CategoryTheory.ShortComplex.exact_iff_epi_kernel_lift _).mp
          F.exact_zero
      let G : Formalization.Books.Algebra.Unit71.Resolution R K :=
        { complex := C
          augmentation := p
          augmentation_condition := htail_zero
          exact_zero := htail_exact_zero
          exact_succ := htail_exact_succ
          augmentation_epi := htail_epi }
      have hfree_tail : ∀ i : Fin n,
          Module.Free R (G.complex.X i : Type u) := by
        intro i
        change Module.Free R (F.complex.X (i.1 + 1) : Type u)
        exact hfree ⟨i.1 + 1, by omega⟩
      have hterminal_tail : Module.Free R (G.complex.X n : Type u) := by
        change Module.Free R (F.complex.X (n + 1) : Type u)
        exact hterminal
      have hcondition_tail :
          (n = 0 → Function.Bijective G.augmentation.hom) ∧
            (0 < n → Function.Injective (G.complex.d n (n - 1)).hom) := by
        constructor
        · intro hn
          subst n
          have hinj : Function.Injective p.hom := by
            intro x y hxy
            apply hcondition.2 (by omega)
            have hxy' := congrArg
              (fun z => (CategoryTheory.Limits.kernel.ι F.augmentation).hom z) hxy
            change (p ≫ CategoryTheory.Limits.kernel.ι F.augmentation).hom x =
              (p ≫ CategoryTheory.Limits.kernel.ι F.augmentation).hom y at hxy'
            simpa [hpι] using hxy'
          have hsurj : Function.Surjective p.hom :=
            (ModuleCat.epi_iff_surjective p).mp htail_epi
          exact ⟨hinj, hsurj⟩
        · intro hn
          obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
          dsimp [G, C]
          have hinj := hcondition.2 (by omega)
          simpa using hinj
      have hK : CategoryTheory.HasProjectiveDimensionLE K n := by
        apply ih G hfree_tail hterminal_tail hcondition_tail
      let S := CategoryTheory.ShortComplex.mk
        (CategoryTheory.Limits.kernel.ι F.augmentation) F.augmentation
        (CategoryTheory.Limits.kernel.condition F.augmentation)
      have hS : S.ShortExact := by
        dsimp [S]
        refine { exact := ?_, mono_f := inferInstance, epi_g := F.augmentation_epi }
        apply CategoryTheory.ShortComplex.exact_of_f_is_kernel
        exact CategoryTheory.Limits.kernelIsKernel F.augmentation
      have hproj0 : CategoryTheory.Projective S.X₂ := by
        dsimp [S]
        let : Module.Free R (F.complex.X 0 : Type u) := hfree ⟨0, by omega⟩
        exact ModuleCat.projective_of_free
          (Module.Free.chooseBasis R (F.complex.X 0 : Type u))
      have hproj0' : CategoryTheory.HasProjectiveDimensionLT S.X₂ (n + 2) := by
        exact @CategoryTheory.hasProjectiveDimensionLT_of_ge _ _ _ S.X₂ 1
          (n + 2) (by omega)
          (CategoryTheory.projective_iff_hasProjectiveDimensionLT_one.mp hproj0)
      exact hS.hasProjectiveDimensionLT_X₃ (n + 1)
        (by simpa [CategoryTheory.HasProjectiveDimensionLE] using hK) hproj0'

private theorem finite_free_resolution_with_finite_terms_of_mcm_prefix
    {R M : Type u} [CommRing R] [IsRegularLocalRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M] (n : ℕ)
    (hprefix : Formalization.Books.Algebra.Unit104.HasMCMFiniteFreeResolutionPrefix
      R M n) :
    HasFiniteFreeResolutionWithFiniteTermsLE (ModuleCat.of R M) n := by
  rcases hprefix with ⟨F, hterms, hterminal⟩
  rcases hterminal with ⟨hK, hKcm, hzero, hinj⟩
  let : Module.Finite R (F.complex.X n : Type u) := hK
  have hfree : ∀ i : Fin n,
      Module.Free R (F.complex.X i : Type u) := by
    intro i
    exact (hterms i).1
  have hterminal_free : Module.Free R (F.complex.X n : Type u) :=
    Formalization.Books.Algebra.Unit106.regular_mcm_free hKcm
  have hpd : CategoryTheory.HasProjectiveDimensionLE
      (ModuleCat.of R M) n :=
    resolution_hasProjectiveDimensionLE_of_free_prefix n F hfree hterminal_free
      ⟨hzero, hinj⟩
  exact ((projective_dimension_resolution_criteria_noetherian_local
    (ModuleCat.of R M) n).out 0 6).mp hpd

private theorem exists_minimal_maximalIdeal_generating_list
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R] :
    ∃ xs : List R,
      Formalization.Books.Algebra.Unit106.IsMinimalIdealGeneratingList
        (maximalIdeal R) xs ∧
        xs.length = (maximalIdeal R).spanFinrank := by
  classical
  let S : Set R := (maximalIdeal R).generators
  let hfg : (maximalIdeal R).FG := IsNoetherian.noetherian (maximalIdeal R)
  let hS : S.Finite := Submodule.FG.finite_generators hfg
  let F : Finset R := hS.toFinset
  let xs : List R := F.toList
  have hSF : (F : Set R) = S := hS.coe_toFinset
  have hspan : Ideal.ofList xs = maximalIdeal R := by
    simpa [Ideal.ofList, xs, hSF] using (maximalIdeal R).span_generators
  have hgen : (maximalIdeal R).spanFinrank = F.card := by
    rw [← Submodule.FG.generators_ncard hfg]
    simpa [F, S] using Set.ncard_eq_toFinset_card (hs := hS)
  refine ⟨xs, ⟨hspan, ?_⟩, ?_⟩
  · intro i hi
    have hcard : (xs.eraseIdx i.1).length + 1 = xs.length :=
      List.length_eraseIdx_add_one i.isLt
    have hspan_erase : Ideal.ofList (xs.eraseIdx i.1) = maximalIdeal R := by
      apply le_antisymm
      · rw [← hspan]
        apply Ideal.span_le.mpr
        intro y hy
        change y ∈ Ideal.span {r | r ∈ xs}
        exact Ideal.subset_span (List.eraseIdx_subset hy)
      · rw [← hspan]
        apply Ideal.span_le.mpr
        intro y hy
        by_cases hyeq : y = xs.get i
        · simpa [hyeq] using hi
        · have hy' : y ∈ xs.eraseIdx i.1 := by
            change y ∈ xs at hy
            obtain ⟨j, hj, hget⟩ := (List.mem_iff_getElem.mp hy)
            have hji : j ≠ i.1 := by
              intro hji
              apply hyeq
              subst j
              exact hget.symm
            rw [List.mem_eraseIdx_iff_getElem]
            exact ⟨j, hj, hji, hget⟩
          change y ∈ Ideal.span {r | r ∈ xs.eraseIdx i.1}
          exact Ideal.subset_span hy'
    let E : Finset R := (xs.eraseIdx i.1).toFinset
    have hspanE : Ideal.span (↑E : Set R) = maximalIdeal R := by
      simpa [E, Ideal.ofList] using hspan_erase
    have hle := Submodule.spanFinrank_span_le_ncard_of_finite
      (R := R) (M := R) (s := (↑E : Set R)) E.finite_toSet
    have hspanE' : Submodule.span R (↑E : Set R) = maximalIdeal R := hspanE
    rw [hspanE'] at hle
    rw [hgen] at hle
    have hcard' : E.card ≤ (xs.eraseIdx i.1).length := by
      simpa [E] using List.toFinset_card_le (xs.eraseIdx i.1)
    have hle' : F.card ≤ (xs.eraseIdx i.1).length :=
      le_trans (by simpa using hle) hcard'
    have hle'' : xs.length ≤ (xs.eraseIdx i.1).length := by
      simpa [xs] using hle'
    omega
  · simpa [xs] using hgen.symm

/-- A finite module of depth `e` over a regular local ring of dimension `d`
has a finite free resolution of length at most `d - e`. -/
theorem regular_local_finite_free_resolution
    {R M : Type u} [CommRing R] [IsRegularLocalRing R]
    [AddCommGroup M] [Module R M]
    [Module.Finite R M] (d e : ℕ)
    (hdim : ringKrullDim R = d)
    (hdepth : localDepth R M = (e : ℕ∞)) :
    HasFiniteFreeResolutionWithFiniteTermsLE (ModuleCat.of R M) (d - e) := by
  have hcm : Formalization.Books.Algebra.Unit104.IsCohenMacaulayLocalRing R := by
    obtain ⟨xs, hxs, _⟩ :=
      exists_minimal_maximalIdeal_generating_list (R := R)
    change Formalization.Books.Algebra.Unit103.IsCohenMacaulay R R
    exact (Formalization.Books.Algebra.Unit106.regular_ring_CM xs hxs).2.2
  have hdim' : ringKrullDim R = (((d : ℕ∞) : WithBot ℕ∞)) := by
    simpa using hdim
  obtain ⟨n, hne, hprefix⟩ :=
    Formalization.Books.Algebra.Unit104.exists_mcm_finite_free_resolution_prefix
      (R := R) (M := M) hcm d e hdim' hdepth
  have hde : d - e = n := by omega
  rw [hde]
  exact finite_free_resolution_with_finite_terms_of_mcm_prefix n hprefix

/-- A regular local ring of dimension `d` has global dimension at most `d`. -/
theorem regular_local_global_dimension_le
    {R : Type u} [CommRing R] [IsRegularLocalRing R]
    (d : ℕ) (hdim : ringKrullDim R = d) :
    HasGlobalDimensionLE R d := by
  /-
  Proof roadmap:
  1. Use `(Unit109.finite_global_dimension_criterion (R := R) d).out 0 1`;
     it suffices to bound every finite `M : ModuleCat.{u} R`.
  2. If `M` is subsingleton, use
     `CategoryTheory.hasProjectiveDimensionLT_zero` (or the zero-object
     characterization).  Otherwise install `Nontrivial M` and obtain
     `e : ℕ` and `localDepth R M = (e : ℕ∞)` from
     `Unit72.localDepth_eq_min_ext` (`Unit72/Depth.lean`).
  3. Apply `regular_local_finite_free_resolution d e hdim hdepth`, turn the
     result back into `HasProjectiveDimensionLE ... (d - e)` using
     `(Unit109.projective_dimension_resolution_criteria_noetherian_local
       M (d - e)).out 6 0`, and enlarge the bound to `d` with
     `CategoryTheory.hasProjectiveDimensionLT_of_ge` and `Nat.sub_le`.
  -/
  sorry

/-- Over a Noetherian ring, a global-dimension bound can be checked at the
maximal localizations. -/
theorem finite_global_dimension_iff_localizations
    {R : Type u} [CommRing R] [IsNoetherianRing R] (n : ℕ) :
    HasGlobalDimensionLE R n ↔
      ∀ m : MaximalSpectrum R,
        HasGlobalDimensionLE (Localization.AtPrime m.asIdeal) n := by
  constructor
  · intro h m
    exact (localize_projective_dimension
      (R := R) (M := R) m.asIdeal.primeCompl n).2 h
  · intro h
    apply ((finite_global_dimension_criterion (R := R) n).out 0 1).mpr
    intro M hM
    have hM' : Module.Finite R M := hM
    let := hM'
    apply (ModuleCat.hasProjectiveDimensionLE_iff_forall_maximalSpectrum n M).mpr
    intro m
    exact h m (M.localizedModule m.1.primeCompl)

/-! ## The residue field and dimension bounds -/

/-- The projective dimension of the residue field is at least the dimension of
the cotangent space.  The inequality is written in the canonical extended
natural-number-valued projective-dimension type. -/
theorem residue_field_projective_dimension_ge_cotangentSpace_finrank
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R] :
    Module.finrank (ResidueField R) (CotangentSpace R) ≤
      CategoryTheory.projectiveDimension
        (ModuleCat.of R (ResidueField R)) := by
  /-
  Proof roadmap (Koszul comparison; no Koszul complex is currently packaged
  in Mathlib or an earlier chapter):
  1. Put `n := Module.finrank (ResidueField R) (CotangentSpace R)`.  Use the
     finite-dimensional instance from
     `Mathlib/RingTheory/Ideal/Cotangent.lean` and choose a basis indexed by
     `Fin n`.  Lift it to `x : Fin n → maximalIdeal R` through the quotient
     defining `CotangentSpace`; `IsLocalRing.CotangentSpace.span_image_eq_top_iff`
     in that file records that the lifts minimally generate the maximal
     ideal.
  2. Define the finite Koszul chain complex on the underlying elements
     `x i`, with degree `i` equal to the `i`th exterior power of `Fin n → R`.
     Prove `d ≫ d = 0`, augment degree zero by
     `IsLocalRing.residue R`, and package it as Unit71's
     `FreeAugmentedComplex` (`Unit71/ExtGroups.lean`).
  3. If the residue field has no finite projective dimension, rewrite with
     `Unit109.hasFiniteProjectiveDimension_iff_projectiveDimension_ne_top`
     and the inequality is immediate.  In the finite case take a minimal
     finite free resolution.  The required construction is exactly
     `Unit109.exists_minimalFiniteFreeResolution`, but that declaration is
     currently block-commented; it must be restored (with its
     `MinimalFiniteFreeResolution` interface) or reimplemented locally.
  4. Apply `Unit71.free_augmented_complex_map_exists` to compare the Koszul
     complex with the minimal resolution, lifting the identity of the
     residue field.  Induct on degrees after tensoring with `ResidueField R`:
     minimal differentials vanish, while the Koszul differential gives the
     standard injective comultiplication
     `ExteriorPower^i → ExteriorPower^(i-1) ⊗ CotangentSpace`.  Therefore the
     degree-`n` term of the minimal resolution is nonzero, so its exact length
     is at least `n`.
  5. Rewrite that exact length as `CategoryTheory.projectiveDimension` (both
     sides live in `WithBot ℕ∞`) and conclude the displayed inequality.
  -/
  sorry

/-- If the residue field has projective dimension exactly `n`, then the ring
dimension is at least `n`. -/
theorem ringKrullDim_ge_residue_field_projective_dimension
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (n : ℕ)
    (hκ : HasProjectiveDimensionExactly
      (ModuleCat.of R (ResidueField R)) n) :
    ((n : ℕ∞) : WithBot ℕ∞) ≤ ringKrullDim R := by
  /-
  Proof roadmap:
  1. Use the nontriviality of `ResidueField R` and restore/apply
     `Unit109.exists_minimalFiniteFreeResolution n hκ`.  This theorem and the
     structure it returns are presently inside the block comment beginning
     at `Unit109/FiniteGlobalDimension.lean:936`.
  2. Apply the likewise-commented
     `Unit109.MinimalFiniteFreeResolution.length_le_localDepth` to obtain
     `(n : ℕ∞) ≤ localDepth R R`.  Its proof is already written against the
     active `Unit102.proposition_what_exact` and `Unit102.rankIdeal`
     (`Unit102/WhatMakesAComplexExact.lean`), so restoring that API is the
     narrow prerequisite rather than rebuilding the determinantal argument
     here.
  3. Cast the inequality to `WithBot ℕ∞`, then compose
     `Unit72.supportDim_ge_localDepth (R := R) (M := R)` with
     `Module.supportDim_self_eq_ringKrullDim R`.  Normalize the natural casts
     to obtain the goal.
  -/
  sorry

/-- For a Noetherian local ring, finite projective dimension of the residue
field, finite global dimension, and regularity are equivalent.  In this case
the three numerical invariants in the source agree. -/
theorem residue_field_finite_projective_dimension_iff_finite_global_dimension_iff_regular
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R] :
    List.TFAE
      [ HasFiniteProjectiveDimension (ModuleCat.of R (ResidueField R)),
        HasFiniteGlobalDimension R,
        IsRegularLocalRing R ] ∧
      (HasFiniteProjectiveDimension (ModuleCat.of R (ResidueField R)) →
        globalDimension R = ringKrullDim R ∧
          ringKrullDim R = Module.finrank (ResidueField R) (CotangentSpace R)) := by
  /-
  Proof roadmap:
  1. Let `A`, `B`, `C` be the three displayed propositions.  `B → A` is the
     global bound applied to the residue-field module.  `C → B` follows from
     `regular_local_global_dimension_le` after rewriting regularity with
     `Unit60.isRegularLocalRing_iff_cotangentSpace_finrank_eq_dimension`; its
     equality supplies the finite natural dimension.
  2. For `A → C`, use
     `Unit109.hasFiniteProjectiveDimension_iff_exists_projective_dimension_bound`
     and `Nat.find` to choose the least bound `n`; package minimality as
     `HasProjectiveDimensionExactly ... n`.  Chain
     `residue_field_projective_dimension_ge_cotangentSpace_finrank`,
     `ringKrullDim_ge_residue_field_projective_dimension`, and
     `Unit60.ringKrullDim_le_cotangentSpace_finrank`.  Antisymmetry gives
     `ringKrullDim R = finrank ...`, and
     `Unit60.isRegularLocalRing_iff_cotangentSpace_finrank_eq_dimension`
     yields `C`.
  3. Assemble `List.TFAE [A, B, C]` with `List.tfae_of_forall` (indices
     `0,1,2`) or `tfae_have`/`tfae_finish`.
  4. Under `A`, retain the exact `n` from step 2.  The two dimension bounds
     show `projectiveDimension κ = ringKrullDim R = finrank ...`.  The local
     global bound gives `globalDimension R ≤ ringKrullDim R`; the reverse
     inequality is the `κ` summand of the defining supremum
     `Unit109.globalDimension`.  Conclude both requested equalities, keeping
     all numeric terms in `WithBot ℕ∞` until the final coercion of `finrank`.
  -/
  sorry

/-- A Noetherian local ring is regular exactly when it has finite global
dimension; then all of its prime localizations are regular local rings. -/
theorem regular_local_iff_finite_global_dimension
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R] :
    (IsRegularLocalRing R ↔ HasFiniteGlobalDimension R) ∧
      (HasFiniteGlobalDimension R →
        ∀ p : PrimeSpectrum R,
          IsRegularLocalRing (Localization.AtPrime p.asIdeal)) := by
  /-
  Proof roadmap:
  1. Extract the TFAE component of
     `residue_field_finite_projective_dimension_iff_finite_global_dimension_iff_regular`
     and use `.out 2 1` for `IsRegularLocalRing R ↔
     HasFiniteGlobalDimension R`.
  2. Given `⟨n, hn⟩ : HasFiniteGlobalDimension R` and a prime `p`, apply
     `(Unit109.localize_projective_dimension
       (R := R) (M := R) p.asIdeal.primeCompl n).2 hn` to obtain finite global
     dimension for `Localization.AtPrime p.asIdeal`.
  3. Its local and Noetherian instances are canonical.  Instantiate step 1
     at that localization and take the finite-global-dimension-to-regular
     direction.  No uniform statement about the dimension of all prime
     localizations is needed.
  -/
  sorry

/-! ## Regular rings -/

/-- Compatibility name for Mathlib's canonical regular Noetherian ring class. -/
abbrev IsRegularRing (R : Type u) [CommRing R] : Prop :=
  _root_.IsRegularRing R

/-- Regularity can be checked at maximal ideals. -/
theorem isRegularRing_iff_forall_maximal
    {R : Type u} [CommRing R] [IsNoetherianRing R] :
    IsRegularRing R ↔
      ∀ m : MaximalSpectrum R,
        IsRegularLocalRing (Localization.AtPrime m.asIdeal) := by
  /-
  Proof roadmap:
  1. In the forward direction, unpack `_root_.isRegularRing_iff` from
     `Mathlib/RingTheory/RegularLocalRing/Defs.lean` and specialize it to the
     prime ideal `m.asIdeal`.
  2. Conversely, unpack `_root_.isRegularRing_iff` and fix
     `p : PrimeSpectrum R`.  Choose a maximal ideal `m ≥ p.asIdeal` with
     `Ideal.exists_le_maximal`; by hypothesis `R_m` is regular local.
  3. In `R_m`, set
     `q := p.asIdeal.map (algebraMap R (Localization.AtPrime m.asIdeal))`.
     `Ideal.isPrime_map_of_isLocalizationAtPrime m.asIdeal p≤m` supplies the
     prime instance, and `Ideal.under_map_of_isLocalizationAtPrime` identifies
     its comap with `p.asIdeal`.
  4. Apply the localization clause of
     `regular_local_iff_finite_global_dimension` to `R_m` and `q`.  Transport
     regularity from `(R_m)_q` to `R_p` along
     `IsLocalization.localizationLocalizationAtPrimeIsoLocalization q`
     (`Mathlib/RingTheory/Localization/LocalizationLocalization.lean`) using
     `IsRegularLocalRing.of_ringEquiv`.
  -/
  sorry

/- The following warning in the source points forward to the Nagata example:
regular Noetherian rings need not have finite global dimension because their
Krull dimension need not be finite.  It is intentionally not exposed as an
existence theorem in this chapter.  The witness is constructed only in the
later Examples book (`Books/Examples/Unit16/NoetherianInfiniteDimension.lean`),
which an Algebra chapter may not import.  The Examples owner should expose
regularity of `NoetherianInfiniteDimensionLocalization k`; combining that
result with `noetherianInfiniteDimension_example`,
`isRegularRing_iff_forall_maximal`, and the theorem below then gives the
source's warning without a reverse chronological dependency. -/

/-! ## Finite-dimensional regular rings -/

/- The source leaves `n` implicit in this lemma.  It is made an explicit
   parameter here so that the exact global dimension and exact Krull dimension
   in the first two alternatives have a single common value. -/

/-- For a Noetherian ring, having exact global dimension `n` is equivalent to
being regular of exact dimension `n`, and to the corresponding maximal- or
prime-local conditions. -/
theorem finite_global_dimension_iff_regular_finite_dimension
    {R : Type u} [CommRing R] [IsNoetherianRing R] (n : ℕ) :
    List.TFAE
      [ globalDimension R = ((n : ℕ∞) : WithBot ℕ∞),
        IsRegularRing R ∧
          ringKrullDim R = ((n : ℕ∞) : WithBot ℕ∞),
        (∀ m : MaximalSpectrum R,
            IsRegularLocalRing (Localization.AtPrime m.asIdeal) ∧
              ringKrullDim (Localization.AtPrime m.asIdeal) ≤
                ((n : ℕ∞) : WithBot ℕ∞)) ∧
          ∃ m : MaximalSpectrum R,
            ringKrullDim (Localization.AtPrime m.asIdeal) =
              ((n : ℕ∞) : WithBot ℕ∞),
        (∀ p : PrimeSpectrum R,
            IsRegularLocalRing (Localization.AtPrime p.asIdeal) ∧
              ringKrullDim (Localization.AtPrime p.asIdeal) ≤
                ((n : ℕ∞) : WithBot ℕ∞)) ∧
          ∃ p : PrimeSpectrum R,
            ringKrullDim (Localization.AtPrime p.asIdeal) =
              ((n : ℕ∞) : WithBot ℕ∞) ] := by
  /-
  Proof roadmap.  Name the four alternatives `A`, `B`, `C`, `D`.
  1. Prove a local numeric interface: for any Noetherian local `T`, the TFAE
     theorem above and its numerical clause give
     `IsRegularLocalRing T ∧ ringKrullDim T ≤ n` iff
     `HasGlobalDimensionLE T n`; when regular, they also identify
     `globalDimension T` with `ringKrullDim T`.
  2. `A → C`: `Unit109.globalDimension_le_iff` gives the global bound, and
     `finite_global_dimension_iff_localizations` gives every maximal local
     bound.  Step 1 gives regularity and local dimension `≤ n`.  For `n+1`,
     if all local dimensions were `≤ n`, the same localization criterion
     would contradict exactness of `A`; hence one equals `n+1`.  Handle
     `n=0` separately: `A` rules out the zero ring, so
     `Ideal.exists_maximal R` supplies a maximal ideal, whose non-bottom
     local dimension and the bound force equality to zero.
  3. `C → A`: step 1 and
     `finite_global_dimension_iff_localizations` give global dimension `≤ n`.
     The equality witness rules out a bound by any `e<n`: localize such a
     global bound with `Unit109.localize_projective_dimension`, then use the
     local numeric equality.  Translate leastness into
     `globalDimension R = (n : WithBot ℕ∞)` using
     `Unit109.globalDimension_le_iff` and the canonical cast order.
  4. `B ↔ C`: regularity is
     `isRegularRing_iff_forall_maximal`.  Rewrite
     `ringKrullDim R` with `Unit60.ringKrullDim_eq_iSup_maximal_height` and
     each local dimension with
     `IsLocalization.AtPrime.ringKrullDim_eq_height`.  The upper bounds and
     equality witness compute the supremum as `n`.
  5. `C → D`: use canonical regularity for all primes.  Given `p`, choose a
     maximal `m ≥ p`; height monotonicity and the AtPrime height formula give
     `dim R_p ≤ dim R_m ≤ n`.  A maximal equality witness is also a prime
     witness.  Conversely, restrict `D` to maximal primes; for its prime
     equality witness choose a maximal ideal above it, and the same height
     inequalities force equality at that maximal ideal.
  6. Assemble `List.TFAE [A,B,C,D]` with `List.tfae_of_forall A`, using
     indices `0` through `3`.  Keep `n` fixed throughout; the explicit
     parameter is the common value in all four alternatives.
  -/
  sorry

/-! ## Flat local descent -/

/-- Regularity descends along a flat local homomorphism of Noetherian local
rings. -/
theorem isRegularLocalRing_of_flat_localHom_of_regular
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S]
    [IsNoetherianRing R] [IsNoetherianRing S]
    (f : R →+* S) [IsLocalHom f]
    (hflat : RingHom.Flat f) (hS : IsRegularLocalRing S) :
    IsRegularLocalRing R := by
  /-
  Proof roadmap (the separate universes `u` and `v` are intentional):
  1. Algebraize `f` with `letI : Algebra R S := f.toAlgebra`; rewrite
     `algebraMap R S` to `f`.  Turn `hflat` into `Module.Flat R S` with
     `Unit39.ringHom_flat_iff_module_flat`, and record faithful flatness via
     `Unit39.faithfullyFlat_of_localRingHom f hflat`.
  2. From `hS` and
     `Unit60.isRegularLocalRing_iff_cotangentSpace_finrank_eq_dimension`, take
     `d := Module.finrank (ResidueField S) (CotangentSpace S)` and obtain
     `ringKrullDim S = d`.  Then `regular_local_global_dimension_le d`
     supplies `HasGlobalDimensionLE S d`.
  3. Choose Unit71's finite free resolution of
     `ModuleCat.of R (ResidueField R)` and let `K_d` be its degree-`d`
     syzygy (use the augmentation kernel when `d=0`).  Tensor each short
     exact segment with `S`; `Unit39.flat_tensor_short_exact`
     (`Unit39/FlatModules.lean`) preserves injectivity, exactness, and
     surjectivity.
  4. Dimension-shift the tensor resolution over `S`.  Its target is
     `S ⊗[R] ResidueField R` (it need not be `ResidueField S`), and the global
     bound makes `S ⊗[R] K_d` projective.  Finiteness follows from the finite
     free terms and Noetherian kernels, so it is `FiniteProjective S ...`.
  5. Apply `Unit78.finite_projective_descends`
     (`Unit78/FiniteProjectiveModules.lean`) to descend finite projectivity
     of `K_d`.  Over the local ring `R`, use
     `Unit85.projective_free_over_local_ring`; the original residue-field
     resolution is therefore finite.  Convert it with
     `Unit109.projective_dimension_resolution_criteria_noetherian_local` to
     `HasFiniteProjectiveDimension (ModuleCat.of R (ResidueField R))`.
  6. Finish with the `finite projective dimension → regular` direction of
     `residue_field_finite_projective_dimension_iff_finite_global_dimension_iff_regular`.
  -/
  sorry

end

end Formalization.Books.Algebra.Unit110
