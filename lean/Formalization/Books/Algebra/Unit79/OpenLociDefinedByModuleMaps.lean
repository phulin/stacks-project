import Formalization.Books.Algebra.Unit78.FiniteProjectiveModules
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.Algebra.Module.LocalizedModule.Submodule
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# Commutative Algebra, Chapter 79: Open loci defined by module maps

The source's localizations and fibers are represented by Mathlib's canonical
`LocalizedModule`, `Localization`, and tensor-product constructions.  The
finite-projective conclusions reuse Chapter 78's source-facing predicate,
which is the canonical conjunction of `Module.Finite` and `Module.Projective`.
-/

namespace Formalization.Books.Algebra.Unit79

open Set
open scoped TensorProduct
open TensorProduct

universe u v

noncomputable section

/-! ## Canonical maps and loci -/

/- The map on stalks is Mathlib's localization of a linear map. -/

/-- The localization at a prime of a map of modules. -/
noncomputable def localizedMapAtPrime
    {R M N : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (φ : M →ₗ[R] N) (p : PrimeSpectrum R) :
    LocalizedModule p.asIdeal.primeCompl M →ₗ[Localization.AtPrime p.asIdeal]
      LocalizedModule p.asIdeal.primeCompl N :=
  LocalizedModule.map p.asIdeal.primeCompl φ

/- The source writes the fiber as `M ⊗ κ(p)`.  We use Mathlib's canonical
   `Ideal.Fiber`, which fixes the equivalent normalization `κ(p) ⊗ M`; the
   map is the canonical `LinearMap.baseChange` and is linear over the residue
   field. -/

/-- The map on fibers over the residue field at a prime. -/
def fiberMapAtPrime
    {R M N : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (φ : M →ₗ[R] N) (p : PrimeSpectrum R) :
    p.asIdeal.Fiber M →ₗ[p.asIdeal.ResidueField] p.asIdeal.Fiber N :=
  LinearMap.baseChange p.asIdeal.ResidueField φ

/-- The locus where the localization of a module map at a prime is surjective. -/
def localizedSurjectiveLocus
    {R M N : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (φ : M →ₗ[R] N) : Set (PrimeSpectrum R) :=
  {p | Function.Surjective (localizedMapAtPrime φ p)}

/-- The locus where the fiber map of a module map is surjective. -/
def fiberSurjectiveLocus
    {R M N : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (φ : M →ₗ[R] N) : Set (PrimeSpectrum R) :=
  {p | Function.Surjective (fiberMapAtPrime φ p)}

/-- The locus where the localization of a module map is bijective. -/
def localizedIsomorphismLocus
    {R M N : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (φ : M →ₗ[R] N) : Set (PrimeSpectrum R) :=
  {p | Function.Bijective (localizedMapAtPrime φ p)}

/-- The locus where the fiber map of a module map is injective. -/
def fiberInjectiveLocus
    {R M N : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (φ : M →ₗ[R] N) : Set (PrimeSpectrum R) :=
  {p | Function.Injective (fiberMapAtPrime φ p)}

/-- The locus where the fiber map of a module map is bijective. -/
def fiberIsomorphismLocus
    {R M N : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (φ : M →ₗ[R] N) : Set (PrimeSpectrum R) :=
  {p | Function.Bijective (fiberMapAtPrime φ p)}

/- The source's identity `V = U ∩ W` is immediate from
   `Function.Bijective`, so it is accounted for by this definition rather
   than duplicated as a separate theorem. -/

/- The map away from an element is the same canonical localized map with the
   powers submonoid. -/

/-- The localization away from an element of a map of modules. -/
noncomputable def localizedMapAway
    {R M N : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (φ : M →ₗ[R] N) (f : R) :
    LocalizedModule.Away f M →ₗ[Localization.Away f] LocalizedModule.Away f N :=
  LocalizedModule.map (Submonoid.powers f) φ

/-! ## A finite target: surjectivity -/

/--
If the target of a module map is finite, its surjectivity locus can be read
on fibers, is open, and localizes to a surjection on every basic open it
contains.
-/
theorem map_between_finite
    {R M N : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [Module.Finite R N] (φ : M →ₗ[R] N) :
    localizedSurjectiveLocus φ = fiberSurjectiveLocus φ ∧
      IsOpen (localizedSurjectiveLocus φ) ∧
        ∀ f : R,
          (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R)) ⊆
              localizedSurjectiveLocus φ →
            Function.Surjective (localizedMapAway φ f) := by
  let C := N ⧸ LinearMap.range φ
  letI : Module.Finite R C := by
    dsimp [C]
    infer_instance
  let q : N →ₗ[R] C := (LinearMap.range φ).mkQ
  have hq : Function.Surjective q := Submodule.mkQ_surjective _
  have hqexact : Function.Exact φ q := φ.exact_map_mkQ_range
  have hfiber (p : PrimeSpectrum R) :
      Function.Surjective (fiberMapAtPrime φ p) ↔
        Subsingleton (p.asIdeal.Fiber C) := by
    let K := p.asIdeal.ResidueField
    let hq' : Function.Surjective (q.baseChange K) :=
      LinearMap.baseChange_surjective K hq
    have hex' : Function.Exact (φ.baseChange K) (q.baseChange K) := by
      rw [LinearMap.baseChange_eq_ltensor, LinearMap.baseChange_eq_ltensor]
      exact lTensor_exact K hqexact hq
    change Function.Surjective (φ.baseChange K) ↔ _
    constructor
    · intro hφ
      have hzero : q.baseChange K = 0 := by
        apply LinearMap.ext
        intro z
        obtain ⟨y, rfl⟩ := hφ z
        change (q.baseChange K ∘ₗ φ.baseChange K) y = 0
        rw [← LinearMap.baseChange_comp, hqexact.linearMap_comp_eq_zero,
          LinearMap.baseChange_zero, LinearMap.zero_apply]
      constructor
      intro x y
      obtain ⟨x, rfl⟩ := hq' x
      obtain ⟨y, rfl⟩ := hq' y
      simp [hzero]
    · intro hC
      have hzero : q.baseChange K = 0 := by
        ext z
        exact Subsingleton.elim _ _
      have htop : LinearMap.range (φ.baseChange K) = ⊤ := by
        rw [← hex'.linearMap_ker_eq, hzero, LinearMap.ker_zero]
      exact LinearMap.range_eq_top.mp htop
  have hlocalized (p : PrimeSpectrum R) :
      Function.Surjective (localizedMapAtPrime φ p) ↔
        Subsingleton (LocalizedModule p.asIdeal.primeCompl C) := by
    change Function.Surjective (LocalizedModule.map p.asIdeal.primeCompl φ) ↔ _
    exact LinearMap.localizedMap_surjective_iff_subsingleton_localized_coker
      p.asIdeal.primeCompl φ
  have hpoint (p : PrimeSpectrum R) :
      p ∈ localizedSurjectiveLocus φ ↔ p ∉ Module.support R C := by
    change Function.Surjective (localizedMapAtPrime φ p) ↔ _
    rw [hlocalized, Module.notMem_support_iff]
  have hfiber_point (p : PrimeSpectrum R) :
      p ∈ fiberSurjectiveLocus φ ↔ p ∉ Module.support R C := by
    change Function.Surjective (fiberMapAtPrime φ p) ↔ _
    rw [hfiber]
    rw [← not_nontrivial_iff_subsingleton,
      Module.mem_support_iff_nontrivial_residueField_tensorProduct]
  have hloc : localizedSurjectiveLocus φ = (Module.support R C)ᶜ := by
    ext p
    exact hpoint p
  have hfib : fiberSurjectiveLocus φ = (Module.support R C)ᶜ := by
    ext p
    exact hfiber_point p
  have hopen : IsOpen (localizedSurjectiveLocus φ) := by
    rw [hloc, Module.support_eq_zeroLocus]
    exact (PrimeSpectrum.isClosed_zeroLocus _).isOpen_compl
  refine ⟨?_, hopen, ?_⟩
  · exact hloc.trans hfib.symm
  · intro f hsub
    change Function.Surjective (LocalizedModule.map (Submonoid.powers f) φ)
    apply (LinearMap.localizedMap_surjective_iff_subsingleton_localized_coker
      (Submonoid.powers f) φ).2
    apply (LocalizedModule.subsingleton_iff_support_subset).2
    intro p hp
    rw [PrimeSpectrum.mem_zeroLocus]
    by_contra hfp
    have hfp' : f ∉ p.asIdeal := by simpa using hfp
    have hpbasic : p ∈ (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R)) :=
      (PrimeSpectrum.mem_basicOpen f p).2 hfp'
    exact (hpoint p).1 (hsub hpbasic) hp

/-! ## A finite source and finitely presented target: isomorphisms -/

/--
If the source is finite and the target is finitely presented, the locus where
a module map is an isomorphism after localization at a prime is open.
-/
theorem map_between_finitely_presented
    {R M N : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [Module.Finite R M] [Module.FinitePresentation R N]
    (φ : M →ₗ[R] N) :
    IsOpen (localizedIsomorphismLocus φ) := by
  refine isOpen_iff_forall_mem_open.mpr ?_
  intro p hp
  change Function.Bijective (LocalizedModule.map p.asIdeal.primeCompl φ) at hp
  obtain ⟨g, hg, hbij⟩ :=
    Module.FinitePresentation.exists_notMem_bijective φ p.asIdeal
      (LocalizedModule.mkLinearMap p.asIdeal.primeCompl M)
      (LocalizedModule.mkLinearMap p.asIdeal.primeCompl N) hp
  refine ⟨PrimeSpectrum.basicOpen g, ?_, PrimeSpectrum.isOpen_basicOpen, ?_⟩
  · intro q hq
    have hqg : g ∉ q.asIdeal := (PrimeSpectrum.mem_basicOpen g q).mp hq
    let A := Localization.Away g
    let B := Localization.AtPrime q.asIdeal
    let hpow : Submonoid.powers g ≤ q.asIdeal.primeCompl :=
      Submonoid.powers_le.mpr hqg
    letI : Algebra A B :=
      IsLocalization.localizationAlgebraOfSubmonoidLe A B
        (Submonoid.powers g) q.asIdeal.primeCompl hpow
    letI : IsScalarTower R A B :=
      IsLocalization.localization_isScalarTower_of_submonoid_le A B
        (Submonoid.powers g) q.asIdeal.primeCompl hpow
    letI : IsLocalization (q.asIdeal.primeCompl.map (algebraMap R A)) B :=
      IsLocalization.isLocalization_of_submonoid_le
        (S := A) (T := B) (Submonoid.powers g) q.asIdeal.primeCompl hpow
    let eM₀ := LocalizedModule.equivTensorProduct (Submonoid.powers g) M
    let eN₀ := LocalizedModule.equivTensorProduct (Submonoid.powers g) N
    let eM : (B ⊗[A] LocalizedModule.Away g M) ≃ₗ[B] (B ⊗[R] M) :=
      eM₀.baseChange A B _ _ ≪≫ₗ AlgebraTensorModule.cancelBaseChange R A B B M
    let eN : (B ⊗[A] LocalizedModule.Away g N) ≃ₗ[B] (B ⊗[R] N) :=
      eN₀.baseChange A B _ _ ≪≫ₗ AlgebraTensorModule.cancelBaseChange R A B B N
    let ea : LocalizedModule.Away g M ≃ₗ[A] LocalizedModule.Away g N :=
      LinearEquiv.ofBijective _ hbij
    have he :
        eN.toLinearMap ∘ₗ (ea.baseChange A B _ _).toLinearMap =
          (φ.baseChange B) ∘ₗ eM.toLinearMap := by
      apply LinearMap.ext
      intro z
      refine TensorProduct.induction_on z (by simp) (fun b x ↦ ?_) (fun x y hx hy ↦ ?_)
      · obtain ⟨⟨m, s⟩, rfl⟩ :=
          IsLocalizedModule.mk'_surjective (Submonoid.powers g)
            (LocalizedModule.mkLinearMap (Submonoid.powers g) M) x
        simp only [Function.uncurry_apply_pair]
        rw [← IsLocalizedModule.mk_eq_mk']
        have hea : ea (LocalizedModule.mk m s) = LocalizedModule.mk (φ m) s := by
          change (LocalizedModule.map (Submonoid.powers g) φ) (LocalizedModule.mk m s) = _
          exact LocalizedModule.map_mk (Submonoid.powers g) φ m s
        simp [eM, eN, eM₀, eN₀, ea, LocalizedModule.map_mk,
          IsLocalizedModule.map_mk', LocalizedModule.equivTensorProduct_apply_mk,
          LinearMap.baseChange_tmul, AlgebraTensorModule.cancelBaseChange_tmul, hea]
        rw [LocalizedModule.equivTensorProduct_apply_mk,
          LocalizedModule.equivTensorProduct_apply_mk]
        simp [AlgebraTensorModule.cancelBaseChange_tmul]
      · simpa [LinearMap.comp_apply] using congrArg₂ (· + ·) hx hy
    have hbase : Function.Bijective (φ.baseChange B) := by
      have heq :
          φ.baseChange B =
            eN.toLinearMap ∘ₗ (ea.baseChange A B _ _).toLinearMap ∘ₗ eM.symm.toLinearMap := by
        calc
          φ.baseChange B = (φ.baseChange B) ∘ₗ LinearMap.id := by simp
          _ = (φ.baseChange B) ∘ₗ (eM.toLinearMap ∘ₗ eM.symm.toLinearMap) := by simp
          _ = ((φ.baseChange B) ∘ₗ eM.toLinearMap) ∘ₗ eM.symm.toLinearMap := by
            rw [LinearMap.comp_assoc]
          _ = (eN.toLinearMap ∘ₗ (ea.baseChange A B _ _).toLinearMap) ∘ₗ
              eM.symm.toLinearMap := by rw [he]
          _ = eN.toLinearMap ∘ₗ (ea.baseChange A B _ _).toLinearMap ∘ₗ eM.symm.toLinearMap := by
            rw [LinearMap.comp_assoc]
      rw [heq]
      exact eN.bijective.comp ((ea.baseChange A B _ _).bijective.comp eM.symm.bijective)
    let eMq := LocalizedModule.equivTensorProduct q.asIdeal.primeCompl M
    let eNq := LocalizedModule.equivTensorProduct q.asIdeal.primeCompl N
    have heq :
        eNq.toLinearMap ∘ₗ LocalizedModule.map q.asIdeal.primeCompl φ =
          (φ.baseChange B) ∘ₗ eMq.toLinearMap := by
      ext x
      obtain ⟨⟨m, s⟩, rfl⟩ :=
        IsLocalizedModule.mk'_surjective q.asIdeal.primeCompl
          (LocalizedModule.mkLinearMap q.asIdeal.primeCompl M) x
      simp only [Function.uncurry_apply_pair]
      rw [← IsLocalizedModule.mk_eq_mk']
      simp [eMq, eNq, LocalizedModule.map_mk, IsLocalizedModule.map_mk',
        LocalizedModule.equivTensorProduct_apply_mk, LinearMap.baseChange_tmul]
    have hqbij : Function.Bijective (LocalizedModule.map q.asIdeal.primeCompl φ) := by
      have heq' :
          LocalizedModule.map q.asIdeal.primeCompl φ =
            eNq.symm.toLinearMap ∘ₗ (φ.baseChange B) ∘ₗ eMq.toLinearMap := by
        calc
          LocalizedModule.map q.asIdeal.primeCompl φ =
              LinearMap.id ∘ₗ LocalizedModule.map q.asIdeal.primeCompl φ := by simp
          _ = (eNq.symm.toLinearMap ∘ₗ eNq.toLinearMap) ∘ₗ
              LocalizedModule.map q.asIdeal.primeCompl φ := by simp
          _ = eNq.symm.toLinearMap ∘ₗ
              (eNq.toLinearMap ∘ₗ LocalizedModule.map q.asIdeal.primeCompl φ) := by
            rw [LinearMap.comp_assoc]
          _ = eNq.symm.toLinearMap ∘ₗ (φ.baseChange B) ∘ₗ eMq.toLinearMap := by rw [heq]
      rw [heq']
      exact eNq.symm.bijective.comp (hbase.comp eMq.bijective)
    exact hqbij
  · exact (PrimeSpectrum.mem_basicOpen g p).2 hg

/-! ## Finite presentation and local freeness -/

/--
A finitely presented module which is free at a prime is free after localizing
away from an element outside that prime.
-/
theorem finitely_presented_localization_free
    {R M : Type*} [CommRing R]
    [AddCommGroup M] [Module R M]
    [Module.FinitePresentation R M] (p : PrimeSpectrum R)
    (hM : Module.Free (Localization.AtPrime p.asIdeal)
      (LocalizedModule p.asIdeal.primeCompl M)) :
    ∃ f : R, f ∉ p.asIdeal ∧
      Module.Free (Localization.Away f) (LocalizedModule.Away f M) := by
  obtain ⟨f, hf, hfree, _⟩ :=
    Module.FinitePresentation.exists_free_localizedModule_powers
      p.asIdeal.primeCompl (LocalizedModule.mkLinearMap p.asIdeal.primeCompl M)
      (Localization.AtPrime p.asIdeal)
  exact ⟨f, hf, hfree⟩

/-! ## Finite projective maps -/

/- The source-facing finite-projective predicate from Chapter 78 is reused for
   the kernel and cokernel conclusions. -/

/--
For a map between finite projective modules, the injective, surjective, and
bijective fiber loci are open.  On any basic open contained in one of these
loci, the corresponding localized map has the asserted property, and the
associated kernel or cokernel is finite projective.
-/
theorem cokernel_flat
    {R P₁ P₂ : Type*} [CommRing R]
    [AddCommGroup P₁] [Module R P₁] [AddCommGroup P₂] [Module R P₂]
    [Module.Finite R P₁] [Module.Projective R P₁]
    [Module.Finite R P₂] [Module.Projective R P₂]
    (φ : P₁ →ₗ[R] P₂) :
    IsOpen (fiberInjectiveLocus φ) ∧
      (∀ f : R,
        (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R)) ⊆
            fiberInjectiveLocus φ →
          Function.Injective (localizedMapAway φ f) ∧
            Formalization.Books.Algebra.Unit78.FiniteProjective
              (Localization.Away f)
              (LocalizedModule.Away f (P₂ ⧸ LinearMap.range φ))) ∧
      IsOpen (fiberSurjectiveLocus φ) ∧
        (∀ f : R,
          (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R)) ⊆
              fiberSurjectiveLocus φ →
            Function.Surjective (localizedMapAway φ f) ∧
              Formalization.Books.Algebra.Unit78.FiniteProjective
                (Localization.Away f)
                (LocalizedModule.Away f (LinearMap.ker φ))) ∧
        IsOpen (fiberIsomorphismLocus φ) ∧
          ∀ f : R,
            (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R)) ⊆
                fiberIsomorphismLocus φ →
              Function.Bijective (localizedMapAway φ f) := by
  letI : Module.FinitePresentation R P₁ := Module.finitePresentation_of_projective R P₁
  letI : Module.FinitePresentation R P₂ := Module.finitePresentation_of_projective R P₂
  have hsplit (q : PrimeSpectrum R)
      (hq : Function.Injective (fiberMapAtPrime φ q)) :
      ∃ r, r ∘ₗ localizedMapAtPrime φ q = LinearMap.id := by
    let Rp := Localization.AtPrime q.asIdeal
    let K := q.asIdeal.ResidueField
    let l := localizedMapAtPrime φ q
    let e₁ : (K ⊗[Rp] LocalizedModule q.asIdeal.primeCompl P₁) ≃ₗ[K]
        (K ⊗[R] P₁) :=
      (LocalizedModule.equivTensorProduct q.asIdeal.primeCompl P₁).baseChange Rp K _ _ ≪≫ₗ
        AlgebraTensorModule.cancelBaseChange R Rp K K P₁
    let e₂ : (K ⊗[Rp] LocalizedModule q.asIdeal.primeCompl P₂) ≃ₗ[K]
        (K ⊗[R] P₂) :=
      (LocalizedModule.equivTensorProduct q.asIdeal.primeCompl P₂).baseChange Rp K _ _ ≪≫ₗ
        AlgebraTensorModule.cancelBaseChange R Rp K K P₂
    letI : Module.Finite Rp (LocalizedModule q.asIdeal.primeCompl P₁) :=
      Module.Finite.of_isLocalizedModule q.asIdeal.primeCompl
        (Rₚ := Rp) (LocalizedModule.mkLinearMap q.asIdeal.primeCompl P₁)
    letI : Module.Finite Rp (LocalizedModule q.asIdeal.primeCompl P₂) :=
      Module.Finite.of_isLocalizedModule q.asIdeal.primeCompl
        (Rₚ := Rp) (LocalizedModule.mkLinearMap q.asIdeal.primeCompl P₂)
    letI : Module.Projective Rp (LocalizedModule q.asIdeal.primeCompl P₂) :=
      Module.projective_of_isLocalizedModule q.asIdeal.primeCompl
        (LocalizedModule.mkLinearMap q.asIdeal.primeCompl P₂)
    letI : Module.Flat Rp (LocalizedModule q.asIdeal.primeCompl P₂) := inferInstance
    letI : Module.Free Rp (LocalizedModule q.asIdeal.primeCompl P₂) :=
      Module.free_of_flat_of_isLocalRing
    have he :
        e₂.toLinearMap ∘ₗ l.baseChange K =
          (fiberMapAtPrime φ q) ∘ₗ e₁.toLinearMap := by
      apply LinearMap.ext
      intro z
      refine TensorProduct.induction_on z (by simp) (fun k x ↦ ?_) (fun x y hx hy ↦ ?_)
      · obtain ⟨⟨m, s⟩, rfl⟩ :=
          IsLocalizedModule.mk'_surjective q.asIdeal.primeCompl
            (LocalizedModule.mkLinearMap q.asIdeal.primeCompl P₁) x
        simp only [Function.uncurry_apply_pair]
        rw [← IsLocalizedModule.mk_eq_mk']
        simp [e₁, e₂, l, localizedMapAtPrime, fiberMapAtPrime,
          LocalizedModule.map_mk, IsLocalizedModule.map_mk',
          LocalizedModule.equivTensorProduct_apply_mk, LinearMap.baseChange_tmul,
          AlgebraTensorModule.cancelBaseChange_tmul]
        rw [LocalizedModule.equivTensorProduct_apply_mk,
          LocalizedModule.equivTensorProduct_apply_mk]
        simp [AlgebraTensorModule.cancelBaseChange_tmul]
      · simpa [LinearMap.comp_apply] using congrArg₂ (· + ·) hx hy
    have hlt : Function.Injective (l.lTensor K) := by
      intro x y hxy
      change l.baseChange K x = l.baseChange K y at hxy
      apply e₁.injective
      apply hq
      calc
        fiberMapAtPrime φ q (e₁ x) = e₂ (l.baseChange K x) :=
          (DFunLike.congr_fun he x).symm
        _ = e₂ (l.baseChange K y) := congrArg e₂ hxy
        _ = fiberMapAtPrime φ q (e₁ y) := DFunLike.congr_fun he y
    exact (IsLocalRing.split_injective_iff_lTensor_residueField_injective l).mpr hlt
  have hlocal (q : PrimeSpectrum R)
      (hq : Function.Injective (fiberMapAtPrime φ q)) :
      Function.Injective (localizedMapAtPrime φ q) := by
    obtain ⟨r, hr⟩ := hsplit q hq
    exact Function.LeftInverse.injective (DFunLike.congr_fun hr)
  have hker (q : PrimeSpectrum R)
      (hq : q ∈ fiberInjectiveLocus φ) :
      q ∉ Module.support R (LinearMap.ker φ) := by
    change Function.Injective (fiberMapAtPrime φ q) at hq
    rw [Module.notMem_support_iff]
    let j := LocalizedModule.map q.asIdeal.primeCompl (LinearMap.ker φ).subtype
    have hj : Function.Injective j :=
      LocalizedModule.map_injective q.asIdeal.primeCompl _ Subtype.val_injective
    have hz : localizedMapAtPrime φ q ∘ₗ j = 0 := by
      ext x
      obtain ⟨⟨m, s⟩, rfl⟩ :=
        IsLocalizedModule.mk'_surjective q.asIdeal.primeCompl
          (LocalizedModule.mkLinearMap q.asIdeal.primeCompl (LinearMap.ker φ)) x
      simp only [Function.uncurry_apply_pair]
      rw [← IsLocalizedModule.mk_eq_mk']
      rw [LocalizedModule.map_mk, LocalizedModule.map_mk]
      have hm : φ m = 0 := LinearMap.mem_ker.mp m.property
      simp [j, localizedMapAtPrime, IsLocalizedModule.map_mk', hm]
    have hi := hlocal q hq
    refine ⟨fun x y => ?_⟩
    apply hj
    apply hi
    have hx := LinearMap.congr_fun hz x
    have hy := LinearMap.congr_fun hz y
    simpa [LinearMap.comp_apply] using hx.trans hy.symm
  have hopen_injective : IsOpen (fiberInjectiveLocus φ) := by
    refine isOpen_iff_forall_mem_open.mpr ?_
    intro q hq
    obtain ⟨r, hr⟩ := hsplit q hq
    let f₁ := LocalizedModule.mkLinearMap q.asIdeal.primeCompl P₁
    let f₂ := LocalizedModule.mkLinearMap q.asIdeal.primeCompl P₂
    let rR := r.restrictScalars R
    obtain ⟨l, s, hls⟩ :=
      Module.FinitePresentation.exists_lift_of_isLocalizedModule
        q.asIdeal.primeCompl f₁ (rR ∘ₗ f₂)
    have hmap (x : P₁) :
        localizedMapAtPrime φ q (f₁ x) = f₂ (φ x) := by
      simp [localizedMapAtPrime, f₁, f₂]
    have hcomp : f₁ ∘ₗ (l ∘ₗ φ) = f₁ ∘ₗ (s.1 • LinearMap.id) := by
      ext x
      calc
        f₁ (l (φ x)) = (s • (rR ∘ₗ f₂)) (φ x) :=
          DFunLike.congr_fun hls (φ x)
        _ = (s.1 : R) • rR (f₂ (φ x)) := by rfl
        _ = s.1 • rR (localizedMapAtPrime φ q (f₁ x)) := by rw [hmap]
        _ = s.1 • f₁ x := by
          have hx := DFunLike.congr_fun hr (f₁ x)
          simpa [LinearMap.comp_apply] using
            congrArg (fun y : LocalizedModule q.asIdeal.primeCompl P₂ ↦
              (s.1 : R) • rR y) hx
        _ = f₁ ((s.1 • LinearMap.id) x) := by simp
    obtain ⟨t, ht⟩ :=
      Module.Finite.exists_smul_of_comp_eq_of_isLocalizedModule
        q.asIdeal.primeCompl f₁ (l ∘ₗ φ) (s.1 • LinearMap.id) hcomp
    let d := t.1 * s.1
    have hd : d ∉ q.asIdeal := by
      intro h
      rcases (q.isPrime.mul_mem_iff_mem_or_mem.mp h) with h | h
      · exact t.2 h
      · exact s.2 h
    refine ⟨PrimeSpectrum.basicOpen d, ?_, PrimeSpectrum.isOpen_basicOpen, ?_⟩
    · intro q' hq'
      have hd' : d ∉ q'.asIdeal := (PrimeSpectrum.mem_basicOpen d q').mp hq'
      change Function.Injective (fiberMapAtPrime φ q')
      let K := q'.asIdeal.ResidueField
      have hdK : algebraMap R K d ≠ 0 := by
        intro hdK
        exact hd' ((Ideal.algebraMap_residueField_eq_zero.mp hdK))
      have ht' := congrArg (fun k : P₁ →ₗ[R] P₁ => k.baseChange K) ht
      have hleft :
          ((algebraMap R K d)⁻¹ • l.baseChange K) ∘ₗ
              fiberMapAtPrime φ q' = LinearMap.id := by
        apply LinearMap.ext
        intro x
        have hx := LinearMap.congr_fun ht' x
        simpa [d, fiberMapAtPrime, LinearMap.baseChange_comp, LinearMap.baseChange_smul,
          mul_smul, LinearMap.comp_apply, hdK, inv_mul_cancel₀] using
          congrArg (fun z => (algebraMap R K d)⁻¹ • z) hx
      exact Function.LeftInverse.injective (DFunLike.congr_fun hleft)
    · exact hd
  refine ⟨hopen_injective, ?_, ?_, ?_, ?_, ?_⟩
  all_goals sorry

end

end Formalization.Books.Algebra.Unit79
