import Formalization.Books.Schemes.Unit02.LocallyRingedSpaces
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.RingTheory.Localization.Module
import Mathlib.Topology.Sheaves.Abelian

/-!
# Affine schemes

This file records the constructions and interfaces in the affine-scheme chapter.
The canonical structure sheaf and associated module sheaf are Mathlib's
`StructureSheaf` and `tilde` constructions.
-/

namespace Formalization.Books.Schemes.Unit05

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry
open AlgebraicGeometry.StructureSheaf
open TopCat

universe u

noncomputable section

/-! ## The standard-open basis -/

/-- The topological space underlying the spectrum of a commutative ring. -/
abbrev spectrumTop (R : Type u) [CommRing R] : TopCat.{u} := PrimeSpectrum.Top R

/-- The standard open `D(f)` in the spectrum of `R`. -/
abbrev standardOpen {R : Type u} [CommRing R] (f : R) :
    Opens (spectrumTop R) := PrimeSpectrum.basicOpen f

theorem standardOpen_is_open (R : Type u) [CommRing R] (f : R) :
    IsOpen (standardOpen f : Set (spectrumTop R)) :=
  PrimeSpectrum.isOpen_basicOpen

theorem standardOpen_is_compact (R : Type u) [CommRing R] (f : R) :
    IsCompact (standardOpen f : Set (spectrumTop R)) :=
  PrimeSpectrum.isCompact_basicOpen f

theorem standardOpen_is_basis (R : Type u) [CommRing R] :
    IsTopologicalBasis
      (Set.range fun f : R => (standardOpen f : Set (spectrumTop R))) :=
  PrimeSpectrum.isTopologicalBasis_basic_opens

theorem standardOpen_inter (R : Type u) [CommRing R] (f g : R) :
    standardOpen (f * g) = standardOpen f ⊓ standardOpen g :=
  PrimeSpectrum.basicOpen_mul f g

theorem standardOpen_mul_le_left {R : Type u} [CommRing R] (f g : R) :
    standardOpen (f * g) ≤ standardOpen f := by
  rw [standardOpen_inter]
  exact inf_le_left

theorem standardOpen_mul_le_right {R : Type u} [CommRing R] (f g : R) :
    standardOpen (f * g) ≤ standardOpen g := by
  rw [standardOpen_inter]
  exact inf_le_right

theorem standardOpen_mul_eq_right_of_subset {R : Type u} [CommRing R] (f g : R)
    (h : standardOpen g ≤ standardOpen f) :
    standardOpen (f * g) = standardOpen g := by
  rw [standardOpen_inter, inf_eq_right.mpr h]

/-! ## Standard-open localization maps -/

theorem standardOpen_isUnit_of_subset {R : Type u} [CommRing R] (f g : R)
    (h : standardOpen g ≤ standardOpen f) :
    IsUnit (algebraMap R (Localization.Away g) f) := by
  exact (PrimeSpectrum.basicOpen_le_basicOpen_iff_algebraMap_isUnit
    (R := R) (S := Localization.Away g) (f := g) (g := f)).mp h

/-- The power relation used to describe a standard-open inclusion. -/
theorem standardOpen_pow_eq_mul_of_subset {R : Type u} [CommRing R] (f g : R)
    (h : standardOpen g ≤ standardOpen f) :
    ∃ e : ℕ, 1 ≤ e ∧ ∃ a : R, g ^ e = a * f := by
  obtain ⟨n, a, ha⟩ :=
    (IsLocalization.Away.algebraMap_isUnit_iff (R := R) (S := Localization.Away g)
      (x := g) (y := f)).mp (standardOpen_isUnit_of_subset f g h)
  refine ⟨n + 1, Nat.succ_le_succ (Nat.zero_le n), a * g, ?_⟩
  rw [pow_succ, ha]
  ac_rfl

/-- The canonical map `R_f → R_g` when `D(g) ⊆ D(f)`. -/
noncomputable def standardOpenLocalizationMap {R : Type u} [CommRing R] (f g : R)
    (h : standardOpen g ≤ standardOpen f) :
    Localization.Away f →+* Localization.Away g :=
  IsLocalization.Away.lift f (standardOpen_isUnit_of_subset f g h)

@[simp]
theorem standardOpenLocalizationMap_algebraMap {R : Type u} [CommRing R] (f g : R)
    (h : standardOpen g ≤ standardOpen f) (a : R) :
    standardOpenLocalizationMap f g h (algebraMap R (Localization.Away f) a) =
      algebraMap R (Localization.Away g) a :=
  IsLocalization.Away.lift_eq f (standardOpen_isUnit_of_subset f g h) a

theorem exists_standardOpenSemilinearModuleMap {R M : Type u} [CommRing R]
    [AddCommGroup M] [Module R M] (f g : R)
    (h : standardOpen g ≤ standardOpen f) :
    ∃ φ : LocalizedModule.Away f M →ₛₗ[standardOpenLocalizationMap f g h]
        LocalizedModule.Away g M,
      ∀ m : M,
        φ (LocalizedModule.mkLinearMap (Submonoid.powers f) M m) =
          LocalizedModule.mkLinearMap (Submonoid.powers g) M m := by
  let : Module (Localization.Away f) (LocalizedModule.Away g M) :=
    Module.compHom (LocalizedModule.Away g M) (standardOpenLocalizationMap f g h)
  let : IsScalarTower R (Localization.Away f) (LocalizedModule.Away g M) :=
    IsScalarTower.of_algebraMap_smul fun r x => by
      change standardOpenLocalizationMap f g h (algebraMap R (Localization.Away f) r) • x = r • x
      rw [standardOpenLocalizationMap_algebraMap]
      exact IsScalarTower.algebraMap_smul (R := R) (A := Localization.Away g) r x
  let hunit : IsUnit
      (algebraMap R (Module.End R (LocalizedModule.Away g M)) f) := by
    rw [Module.End.isUnit_iff]
    let A := Localization.Away g
    let N := LocalizedModule.Away g M
    have hfA : IsUnit (algebraMap A (Module.End A N)
        (algebraMap R A f)) :=
      (standardOpen_isUnit_of_subset f g h).map
        (algebraMap A (Module.End A N))
    have hfun : (algebraMap R (Module.End R N) f : N → N) =
        (algebraMap A (Module.End A N) (algebraMap R A f) : N → N) := by
      funext x
      simp [Module.algebraMap_end_apply]
    rw [hfun]
    exact (Module.End.isUnit_iff _).mp hfA
  let hunitPowers : ∀ s : Submonoid.powers f,
      IsUnit (algebraMap R (Module.End R (LocalizedModule.Away g M)) s) := by
    rintro ⟨_, n, rfl⟩
    change IsUnit
      (algebraMap R (Module.End R (LocalizedModule.Away g M)) (f ^ n))
    simpa only [map_pow] using hunit.pow n
  let ψ := LocalizedModule.lift (Submonoid.powers f)
    (LocalizedModule.mkLinearMap (Submonoid.powers g) M) hunitPowers
  let ψ' := ψ.extendScalarsOfIsLocalization (Submonoid.powers f) (Localization.Away f)
  let φ : LocalizedModule.Away f M →ₛₗ[standardOpenLocalizationMap f g h]
      LocalizedModule.Away g M :=
    { toFun := ψ'
      map_add' := ψ'.map_add
      map_smul' := fun a m => by
        change ψ' (a • m) = standardOpenLocalizationMap f g h a • ψ' m
        exact ψ'.map_smul a m }
  refine ⟨φ, ?_⟩
  intro m
  exact DFunLike.congr_fun
    (LocalizedModule.lift_comp (Submonoid.powers f)
      (LocalizedModule.mkLinearMap (Submonoid.powers g) M) hunitPowers) m

/-- The canonical semilinear map `M_f → M_g` attached to `D(g) ⊆ D(f)`. -/
noncomputable def standardOpenSemilinearModuleLocalizationMap {R M : Type u}
    [CommRing R] [AddCommGroup M] [Module R M] (f g : R)
    (h : standardOpen g ≤ standardOpen f) :
    LocalizedModule.Away f M →ₛₗ[standardOpenLocalizationMap f g h]
      LocalizedModule.Away g M :=
  Classical.choose (exists_standardOpenSemilinearModuleMap f g h)

@[simp]
theorem standardOpenSemilinearModuleLocalizationMap_mk {R M : Type u}
    [CommRing R] [AddCommGroup M] [Module R M] (f g : R)
    (h : standardOpen g ≤ standardOpen f) (m : M) :
    standardOpenSemilinearModuleLocalizationMap f g h
        (LocalizedModule.mkLinearMap (Submonoid.powers f) M m) =
      LocalizedModule.mkLinearMap (Submonoid.powers g) M m :=
  Classical.choose_spec (exists_standardOpenSemilinearModuleMap f g h) m

/-- The restriction map on localized modules, viewed as a map of
`R_f`-modules after restricting scalars along `R_f → R_g`. -/
noncomputable def standardOpenModuleLocalizationMapOverSource {R M : Type u}
    [CommRing R] [AddCommGroup M] [Module R M] (f g : R)
    (h : standardOpen g ≤ standardOpen f) :
    ModuleCat.of (Localization.Away f) (LocalizedModule.Away f M) ⟶
      (ModuleCat.restrictScalars (standardOpenLocalizationMap f g h)).obj
        (ModuleCat.of (Localization.Away g) (LocalizedModule.Away g M)) :=
  letI : Module (Localization.Away f) (LocalizedModule.Away g M) :=
    Module.compHom (LocalizedModule.Away g M) (standardOpenLocalizationMap f g h)
  let φ : LocalizedModule.Away f M →ₗ[Localization.Away f]
      ((ModuleCat.restrictScalars (standardOpenLocalizationMap f g h)).obj
        (ModuleCat.of (Localization.Away g) (LocalizedModule.Away g M)) : Type u) :=
    { toFun := standardOpenSemilinearModuleLocalizationMap f g h
      map_add' := (standardOpenSemilinearModuleLocalizationMap f g h).map_add
      map_smul' := fun a m => by
        change _ = standardOpenLocalizationMap f g h a •
          (standardOpenSemilinearModuleLocalizationMap f g h m :
            LocalizedModule.Away g M)
        exact (standardOpenSemilinearModuleLocalizationMap f g h).map_smul' a m }
  ModuleCat.ofHom φ

/- The restriction maps satisfy the identity and composition laws required of
the presheaf described in the source.  The proof stage can establish these
from the universal properties of localization. -/

theorem standardOpenLocalizationMap_comp_of_subset {R : Type u} [CommRing R]
    (f g k : R) (hfg : standardOpen g ≤ standardOpen f)
    (hgk : standardOpen k ≤ standardOpen g) :
    standardOpenLocalizationMap f k (hgk.trans hfg) =
      (standardOpenLocalizationMap g k hgk).comp
        (standardOpenLocalizationMap f g hfg) := by
  apply IsLocalization.ringHom_ext (Submonoid.powers f)
  ext a
  simp [RingHom.comp_apply]

/-- The canonical localized-module map attached to a standard-open inclusion. -/
noncomputable def standardOpenModuleLocalizationMap {R M : Type u} [CommRing R]
    [AddCommGroup M] [Module R M] (f g : R)
    (h : standardOpen g ≤ standardOpen f) :
    LocalizedModule.Away f M →ₗ[R] LocalizedModule.Away g M :=
  let hunit : IsUnit
      (algebraMap R (Module.End R (LocalizedModule.Away g M)) f) := by
    rw [Module.End.isUnit_iff]
    let A := Localization.Away g
    let N := LocalizedModule.Away g M
    have hfA : IsUnit (algebraMap A (Module.End A N)
        (algebraMap R A f)) :=
      (standardOpen_isUnit_of_subset f g h).map
        (algebraMap A (Module.End A N))
    have hfun : (algebraMap R (Module.End R N) f : N → N) =
        (algebraMap A (Module.End A N) (algebraMap R A f) : N → N) := by
      funext x
      simp [Module.algebraMap_end_apply]
    rw [hfun]
    exact (Module.End.isUnit_iff _).mp hfA
  let hunitPowers : ∀ s : Submonoid.powers f,
      IsUnit (algebraMap R (Module.End R (LocalizedModule.Away g M)) s) := by
    rintro ⟨_, n, rfl⟩
    change IsUnit
      (algebraMap R (Module.End R (LocalizedModule.Away g M)) (f ^ n))
    simpa only [map_pow] using hunit.pow n
  LocalizedModule.lift (Submonoid.powers f)
    (LocalizedModule.mkLinearMap (Submonoid.powers g) M) hunitPowers

theorem standardOpenModuleLocalizationMap_comp {R M : Type u} [CommRing R]
    [AddCommGroup M] [Module R M] (f g : R)
    (h : standardOpen g ≤ standardOpen f) :
    (standardOpenModuleLocalizationMap f g h).comp
        (LocalizedModule.mkLinearMap (Submonoid.powers f) M) =
      LocalizedModule.mkLinearMap (Submonoid.powers g) M :=
  by
    apply LocalizedModule.lift_comp

theorem standardOpenModuleLocalizationMap_comp_of_subset {R M : Type u}
    [CommRing R] [AddCommGroup M] [Module R M]
    (f g k : R) (hfg : standardOpen g ≤ standardOpen f)
    (hgk : standardOpen k ≤ standardOpen g) :
    standardOpenModuleLocalizationMap (R := R) (M := M) f k (hgk.trans hfg) =
      (standardOpenModuleLocalizationMap (R := R) (M := M) g k hgk).comp
        (standardOpenModuleLocalizationMap (R := R) (M := M) f g hfg) := by
  let hunit : IsUnit
      (algebraMap R (Module.End R (LocalizedModule.Away k M)) f) := by
    rw [Module.End.isUnit_iff]
    let A := Localization.Away k
    let N := LocalizedModule.Away k M
    have hfA : IsUnit (algebraMap A (Module.End A N)
        (algebraMap R A f)) :=
      (standardOpen_isUnit_of_subset f k (hgk.trans hfg)).map
        (algebraMap A (Module.End A N))
    have hfun : (algebraMap R (Module.End R N) f : N → N) =
        (algebraMap A (Module.End A N) (algebraMap R A f) : N → N) := by
      funext x
      simp [Module.algebraMap_end_apply]
    rw [hfun]
    exact (Module.End.isUnit_iff _).mp hfA
  let hunitPowers : ∀ s : Submonoid.powers f,
      IsUnit (algebraMap R (Module.End R (LocalizedModule.Away k M)) s) := by
    rintro ⟨_, n, rfl⟩
    change IsUnit
      (algebraMap R (Module.End R (LocalizedModule.Away k M)) (f ^ n))
    simpa only [map_pow] using hunit.pow n
  let l := LocalizedModule.lift (Submonoid.powers f)
    (LocalizedModule.mkLinearMap (Submonoid.powers k) M) hunitPowers
  have hleft : l =
      standardOpenModuleLocalizationMap (R := R) (M := M) f k (hgk.trans hfg) := by
    apply LocalizedModule.lift_unique (Submonoid.powers f)
      (LocalizedModule.mkLinearMap (Submonoid.powers k) M) hunitPowers
    exact standardOpenModuleLocalizationMap_comp (R := R) (M := M) f k (hgk.trans hfg)
  have hright : l =
      (standardOpenModuleLocalizationMap (R := R) (M := M) g k hgk).comp
        (standardOpenModuleLocalizationMap (R := R) (M := M) f g hfg) := by
    apply LocalizedModule.lift_unique (Submonoid.powers f)
      (LocalizedModule.mkLinearMap (Submonoid.powers k) M) hunitPowers
    rw [LinearMap.comp_assoc, standardOpenModuleLocalizationMap_comp,
      standardOpenModuleLocalizationMap_comp]
  exact hleft.symm.trans hright

theorem standardOpenLocalizationMap_inverse_of_open_eq {R : Type u} [CommRing R]
    (f g : R) (h : standardOpen f = standardOpen g) :
    (standardOpenLocalizationMap g f h.le).comp
          (standardOpenLocalizationMap f g h.ge) =
        RingHom.id (Localization.Away f) ∧
      (standardOpenLocalizationMap f g h.ge).comp
          (standardOpenLocalizationMap g f h.le) =
        RingHom.id (Localization.Away g) := by
  constructor
  · apply IsLocalization.ringHom_ext (Submonoid.powers f)
    ext a
    simp [RingHom.comp_apply]
  · apply IsLocalization.ringHom_ext (Submonoid.powers g)
    ext a
    simp [RingHom.comp_apply]

theorem standardOpenModuleLocalizationMap_inverse_of_open_eq {R M : Type u}
    [CommRing R] [AddCommGroup M] [Module R M] (f g : R)
    (h : standardOpen f = standardOpen g) :
      (standardOpenModuleLocalizationMap g f h.le).comp
          (standardOpenModuleLocalizationMap f g h.ge) =
        (LinearMap.id : LocalizedModule.Away f M →ₗ[R] LocalizedModule.Away f M) ∧
      (standardOpenModuleLocalizationMap f g h.ge).comp
          (standardOpenModuleLocalizationMap g f h.le) =
        (LinearMap.id : LocalizedModule.Away g M →ₗ[R] LocalizedModule.Away g M) := by
  constructor
  · apply IsLocalizedModule.linearMap_ext (Submonoid.powers f)
      (LocalizedModule.mkLinearMap (Submonoid.powers f) M)
      (LocalizedModule.mkLinearMap (Submonoid.powers f) M)
    rw [LinearMap.comp_assoc, standardOpenModuleLocalizationMap_comp,
      standardOpenModuleLocalizationMap_comp]
    rfl
  · apply IsLocalizedModule.linearMap_ext (Submonoid.powers g)
      (LocalizedModule.mkLinearMap (Submonoid.powers g) M)
      (LocalizedModule.mkLinearMap (Submonoid.powers g) M)
    rw [LinearMap.comp_assoc, standardOpenModuleLocalizationMap_comp,
      standardOpenModuleLocalizationMap_comp]
    rfl

/-- A finite standard-open refinement of an open cover of `D(f)`. -/
theorem exists_finite_standardOpen_refinement {R : Type u} [CommRing R] (f : R)
    (𝒰 : Set (Opens (spectrumTop R)))
    (h𝒰 : ∀ x : PrimeSpectrum R, x ∈ standardOpen f →
      ∃ U ∈ 𝒰, x ∈ U) :
    ∃ n : ℕ, ∃ g : Fin n → R,
      (⨆ i, standardOpen (g i)) = standardOpen f ∧
        ∀ i, ∃ U ∈ 𝒰, standardOpen (g i) ≤ U := by
  classical
  have hlocal :
      ∀ x : {x : PrimeSpectrum R // x ∈ standardOpen f},
        ∃ g : R, ∃ U ∈ 𝒰,
          x.1 ∈ standardOpen g ∧
            standardOpen g ≤ U ∧ standardOpen g ≤ standardOpen f := by
    intro x
    obtain ⟨U, hU, hxU⟩ := h𝒰 x.1 x.2
    have hopen : IsOpen ((U : Set (spectrumTop R)) ∩
        (standardOpen f : Set (spectrumTop R))) :=
      U.isOpen.inter (standardOpen_is_open R f)
    obtain ⟨V, ⟨g, rfl⟩, hxV, hV⟩ :=
      (standardOpen_is_basis R).isOpen_iff.mp hopen x.1 ⟨hxU, x.2⟩
    refine ⟨g, U, hU, hxV, ?_, ?_⟩
    · exact hV.trans Set.inter_subset_left
    · exact hV.trans Set.inter_subset_right
  choose g hg using hlocal
  have hcover : (standardOpen f : Set (spectrumTop R)) ⊆
      ⋃ x : {x : PrimeSpectrum R // x ∈ standardOpen f},
        (standardOpen (g x) : Set (spectrumTop R)) := by
    intro x hx
    obtain ⟨U, hU, hxg, hsubU, hsubf⟩ := hg ⟨x, hx⟩
    exact Set.mem_iUnion.mpr ⟨⟨x, hx⟩, hxg⟩
  obtain ⟨t, ht⟩ :=
    (standardOpen_is_compact R f).elim_finite_subcover
      (fun x : {x : PrimeSpectrum R // x ∈ standardOpen f} =>
        (standardOpen (g x) : Set (spectrumTop R)))
      (fun x => standardOpen_is_open R (g x)) hcover
  let n := Fintype.card t
  let e : Fin n ≃ t := (Fintype.equivFin t).symm
  let g' : Fin n → R := fun i => g (e i)
  refine ⟨n, g', ?_, ?_⟩
  · apply le_antisymm
    · refine iSup_le fun i => ?_
      obtain ⟨U, hU, hxg, hsubU, hsubf⟩ := hg (e i)
      simpa [g'] using hsubf
    · intro x hx
      obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp (ht hx)
      let i : Fin n := e.symm ⟨y, hy⟩
      apply Opens.mem_iSup.mpr
      refine ⟨i, ?_⟩
      simpa [g', i] using hxy
  · intro i
    obtain ⟨U, hU, hxg, hsubU, hsubf⟩ := hg (e i)
    exact ⟨U, hU, by simpa [g'] using hsubU⟩

/-- The unit-ideal criterion for a finite standard-open covering of `D(f)`. -/
theorem standardOpen_cover_iff_unitIdeal {R : Type u} [CommRing R] (f : R)
    (n : ℕ) (g : Fin n → R) :
    standardOpen f ≤ ⨆ i, standardOpen (g i) ↔
      Ideal.span (Set.range (fun i =>
        algebraMap R (Localization.Away f) (g i))) = ⊤ := by
  classical
  let S := Localization.Away f
  let ι : PrimeSpectrum S → PrimeSpectrum R :=
    PrimeSpectrum.comap (algebraMap R S)
  constructor
  · intro hcover
    apply (PrimeSpectrum.iSup_basicOpen_eq_top_iff).mp
    apply top_unique
    intro p hp
    have hqf : (PrimeSpectrum.comap (algebraMap R S) p : PrimeSpectrum.Top R) ∈
        standardOpen f := by
      change PrimeSpectrum.comap (algebraMap R S) p ∈
        (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R))
      rw [← PrimeSpectrum.localization_away_comap_range S f]
      exact ⟨p, rfl⟩
    obtain ⟨i, hqi⟩ := Opens.mem_iSup.mp (hcover hqf)
    apply Opens.mem_iSup.mpr
    refine ⟨i, ?_⟩
    change g i ∉ (PrimeSpectrum.comap (algebraMap R S) p).asIdeal at hqi
    change algebraMap R S (g i) ∉ p.asIdeal
    simpa only [ι, PrimeSpectrum.comap_asIdeal, Ideal.mem_comap] using hqi
  · intro hspan
    have htop : (⨆ i, PrimeSpectrum.basicOpen
        (algebraMap R S (g i))) = (⊤ : Opens (PrimeSpectrum.Top S)) :=
      (PrimeSpectrum.iSup_basicOpen_eq_top_iff).mpr hspan
    intro x hx
    have hxrange : x ∈ Set.range ι := by
      rw [PrimeSpectrum.localization_away_comap_range S f]
      exact hx
    obtain ⟨p, hp⟩ := hxrange
    have hpi : p ∈ (⨆ i, PrimeSpectrum.basicOpen
        (algebraMap R S (g i))) := by
      rw [htop]
      trivial
    obtain ⟨i, hpi⟩ := Opens.mem_iSup.mp hpi
    rw [← hp]
    apply Opens.mem_iSup.mpr
    refine ⟨i, ?_⟩
    change g i ∉ (PrimeSpectrum.comap (algebraMap R S) p).asIdeal
    change algebraMap R S (g i) ∉ p.asIdeal at hpi
    simpa only [ι, PrimeSpectrum.comap_asIdeal, Ideal.mem_comap] using hpi

theorem standardOpen_mul_eq_member_of_cover {R : Type u} [CommRing R] (f : R)
    (n : ℕ) (g : Fin n → R)
    (hcover : standardOpen f = ⨆ i, standardOpen (g i)) (i : Fin n) :
    standardOpen (f * g i) = standardOpen (g i) := by
  apply standardOpen_mul_eq_right_of_subset
  rw [hcover]
  exact le_iSup (fun j => standardOpen (g j)) i

/-! ## Standard-open coverings -/

/- The source introduces this terminology after the standard-open lemma.  The
definition uses a finite family indexed by `Fin n`, which is the direct Lean
counterpart of the displayed finite union. -/

/-- A finite standard-open covering of an open `U`. -/
def StandardOpenCovering {R : Type u} [CommRing R] (U : Opens (spectrumTop R)) : Prop :=
  ∃ n : ℕ, ∃ f : Fin n → R, (⨆ i, standardOpen (f i)) = U

/-- A finite standard-open covering of the whole spectrum. -/
abbrev standardOpenCoveringSpectrum (R : Type u) [CommRing R] : Prop :=
  StandardOpenCovering (⊤ : Opens (spectrumTop R))

/-- A finite standard-open covering of the standard open `D(f)`. -/
abbrev standardOpenCoveringOf {R : Type u} [CommRing R] (f : R) : Prop :=
  StandardOpenCovering (standardOpen f)

/-! ## The canonical presheaves and sheaves -/

/-- The module-valued presheaf whose sections are local fractions. -/
abbrev moduleLocalizationPresheaf (R M : Type u) [CommRing R]
    [AddCommGroup M] [Module R M] :
    TopCat.Presheaf (ModuleCat R) (spectrumTop R) :=
  AlgebraicGeometry.structurePresheafInModuleCat R M

/-- The commutative-ring-valued localization presheaf. -/
abbrev ringLocalizationPresheaf (R : Type u) [CommRing R] :
    TopCat.Presheaf CommRingCat (spectrumTop R) :=
  AlgebraicGeometry.structurePresheafInCommRingCat R

/-- Sections of the basis presheaf on the standard open `D(f)`. -/
abbrev standardOpenModuleSections (R M : Type u) [CommRing R]
    [AddCommGroup M] [Module R M] (f : R) : Type u :=
  LocalizedModule.Away f M

/-- Ring-valued sections of the basis presheaf on the standard open `D(f)`. -/
abbrev standardOpenRingSections (R : Type u) [CommRing R] (f : R) : Type u :=
  Localization.Away f

/-! The source computes the stalk as a filtered colimit over the standard
opens containing a point.  This preorder makes that indexing assertion
explicit; the canonical stalk isomorphisms below identify its localization
colimit with the Mathlib stalk. -/

/-- The standard-open index attached to a prime `p`, consisting of elements
outside `p`. -/
def standardOpenStalkIndex {R : Type u} [CommRing R] (p : PrimeSpectrum R) :=
  {f : R // f ∉ p.asIdeal}

/-- The order on the stalk index is reverse inclusion of standard opens. -/
instance standardOpenStalkIndex_preorder {R : Type u} [CommRing R]
    (p : PrimeSpectrum R) : Preorder (standardOpenStalkIndex p) where
  le f g := standardOpen g.1 ≤ standardOpen f.1
  le_refl f := le_rfl
  le_trans a b c hab hbc := hbc.trans hab

/-- The order relation is exactly reverse inclusion of the corresponding
standard opens. -/
theorem standardOpenStalkIndex_le_iff {R : Type u} [CommRing R]
    (p : PrimeSpectrum R) (f g : standardOpenStalkIndex p) :
    f ≤ g ↔ standardOpen g.1 ≤ standardOpen f.1 :=
  Iff.rfl

/-- Equivalently, `f ≥ g` means `D(f) ⊆ D(g)`, as in the source. -/
theorem standardOpenStalkIndex_ge_iff {R : Type u} [CommRing R]
    (p : PrimeSpectrum R) (f g : standardOpenStalkIndex p) :
    f ≥ g ↔ standardOpen f.1 ≤ standardOpen g.1 :=
  Iff.rfl

/-- Products give common upper bounds in the standard-open stalk index. -/
theorem standardOpenStalkIndex_mul_upperBound {R : Type u} [CommRing R]
    (p : PrimeSpectrum R) (f g : standardOpenStalkIndex p) :
    ∃ h : standardOpenStalkIndex p, h ≥ f ∧ h ≥ g := by
  have hmem : f.1 * g.1 ∉ p.asIdeal := by
    intro h
    exact (p.isPrime.mul_mem_iff_mem_or_mem.mp h).elim f.2 g.2
  let h : standardOpenStalkIndex p := ⟨f.1 * g.1, hmem⟩
  refine ⟨h, ?_, ?_⟩
  · change standardOpen (f.1 * g.1) ≤ standardOpen f.1
    exact standardOpen_mul_le_left _ _
  · change standardOpen (f.1 * g.1) ≤ standardOpen g.1
    exact standardOpen_mul_le_right _ _

/- The two inverse-map statements above are the basis-presheaf
independence-of-presentation assertion: if `D(f) = D(g)`, either element may
be used to present the same standard-open section object. -/

noncomputable def standardOpenModuleSectionsEquiv {R M : Type u}
    [CommRing R] [AddCommGroup M] [Module R M] (f g : R)
    (h : standardOpen f = standardOpen g) :
    standardOpenModuleSections R M f ≃ₗ[R] standardOpenModuleSections R M g :=
  LinearEquiv.ofLinear
    (standardOpenModuleLocalizationMap f g h.ge)
    (standardOpenModuleLocalizationMap g f h.le)
    (standardOpenModuleLocalizationMap_inverse_of_open_eq f g h).2
    (standardOpenModuleLocalizationMap_inverse_of_open_eq f g h).1

noncomputable def standardOpenRingSectionsEquiv {R : Type u} [CommRing R]
    (f g : R) (h : standardOpen f = standardOpen g) :
    standardOpenRingSections R f ≃+* standardOpenRingSections R g :=
  RingEquiv.ofRingHom
    (standardOpenLocalizationMap f g h.ge)
    (standardOpenLocalizationMap g f h.le)
    (standardOpenLocalizationMap_inverse_of_open_eq f g h).2
    (standardOpenLocalizationMap_inverse_of_open_eq f g h).1

theorem standardOpenModuleSections_independent_of_eq {R M : Type u}
    [CommRing R] [AddCommGroup M] [Module R M] (f g : R)
    (h : standardOpen f = standardOpen g) :
    Nonempty (standardOpenModuleSections R M f ≃ₗ[R]
      standardOpenModuleSections R M g) := by
  exact ⟨standardOpenModuleSectionsEquiv f g h⟩

theorem standardOpenRingSections_independent_of_eq {R : Type u} [CommRing R]
    (f g : R) (h : standardOpen f = standardOpen g) :
    Nonempty (standardOpenRingSections R f ≃+* standardOpenRingSections R g) := by
  exact ⟨standardOpenRingSectionsEquiv f g h⟩

/-- The canonical structure sheaf on `Spec(R)`. -/
abbrev affineStructureSheaf (R : Type u) [CommRing R] :
    TopCat.Sheaf CommRingCat (spectrumTop R) :=
  AlgebraicGeometry.Spec.structureSheaf (CommRingCat.of R)

theorem affineStructureSheaf_presheaf_eq (R : Type u) [CommRing R] :
    (affineStructureSheaf R).presheaf = ringLocalizationPresheaf R :=
  rfl

/-- The canonical locally ringed space associated to the spectrum. -/
abbrev affineLocallyRingedSpace (R : Type u) [CommRing R] :
    Formalization.Books.Schemes.Unit02.LocallyRingedSpace.{u} :=
  AlgebraicGeometry.Spec.locallyRingedSpaceObj (CommRingCat.of R)

theorem affineLocallyRingedSpace_stalk_isLocal {R : Type u} [CommRing R]
    (p : PrimeSpectrum R) :
    IsLocalRing
      (Formalization.Books.Schemes.Unit02.localRing (affineLocallyRingedSpace R) p) :=
  Formalization.Books.Schemes.Unit02.localRing_isLocal (affineLocallyRingedSpace R) p

/-- The sheaf of `𝒪_{Spec(R)}`-modules associated to an `R`-module. -/
abbrev associatedModuleSheaf (R M : Type u) [CommRing R]
    [AddCommGroup M] [Module R M] :
    (AlgebraicGeometry.Spec (CommRingCat.of R)).Modules :=
  AlgebraicGeometry.tilde (R := CommRingCat.of R) (ModuleCat.of R M)

/-- The underlying sheaf of `R`-modules of the associated module sheaf. -/
abbrev associatedModuleUnderlyingSheaf (R M : Type u) [CommRing R]
    [AddCommGroup M] [Module R M] :
    TopCat.Sheaf (ModuleCat (CommRingCat.of R))
      (AlgebraicGeometry.Spec (CommRingCat.of R)) :=
  AlgebraicGeometry.modulesSpecToSheaf (R := CommRingCat.of R).obj
    (associatedModuleSheaf R M)

/-- The module localization isomorphism with sections on a standard open. -/
noncomputable def moduleLocalizationToStandardOpenSections (R M : Type u)
    [CommRing R] [AddCommGroup M] [Module R M] (f : R) :
    LocalizedModule.Away f M ≃ₗ[R]
      (AlgebraicGeometry.structureSheafInType R M).obj.obj
        (op (PrimeSpectrum.basicOpen (R := R) f)) :=
  IsLocalizedModule.linearEquiv (Submonoid.powers f)
    (LocalizedModule.mkLinearMap (Submonoid.powers f) M)
    (AlgebraicGeometry.StructureSheaf.toOpenₗ R M
      (PrimeSpectrum.basicOpen f))

/-- The ring localization isomorphism with sections on a standard open. -/
noncomputable def ringLocalizationToStandardOpenSections (R : Type u)
    [CommRing R] (f : R) :
    Localization.Away f ≃ₐ[R]
      (AlgebraicGeometry.structureSheafInType R R).obj.obj
        (op (PrimeSpectrum.basicOpen (R := R) f)) :=
  IsLocalization.algEquiv (Submonoid.powers f) _ _

/-- The associated module sheaf's localization map on a standard open. -/
noncomputable def associatedModuleToStandardOpenSections (R M : Type u)
    [CommRing R] [AddCommGroup M] [Module R M] (f : R) :
    ModuleCat.of R M ⟶
      (associatedModuleUnderlyingSheaf R M).presheaf.obj
        (op (PrimeSpectrum.basicOpen (R := R) f)) :=
  AlgebraicGeometry.tilde.toOpen (R := CommRingCat.of R) (ModuleCat.of R M)
    (PrimeSpectrum.basicOpen f)

/-- The associated module sheaf has localized sections on a standard open. -/
noncomputable def associatedModuleLocalizationToStandardOpenSections (R M : Type u)
    [CommRing R] [AddCommGroup M] [Module R M] (f : R) :
    LocalizedModule.Away f M ≃ₗ[R]
      (associatedModuleUnderlyingSheaf R M).presheaf.obj
        (op (PrimeSpectrum.basicOpen (R := R) f)) :=
  letI : IsLocalizedModule (Submonoid.powers f)
      (AlgebraicGeometry.tilde.toOpen (R := CommRingCat.of R) (ModuleCat.of R M)
        (PrimeSpectrum.basicOpen f)).hom :=
    AlgebraicGeometry.tilde.instAwayCarrierCarrierObjOppositeOpensCarrierCarrierCommRingCatSpecModuleCatPresheafModulesSheafModulesSpecToSheafOpBasicOpenHomToOpen
      (R := CommRingCat.of R) (ModuleCat.of R M) f
  IsLocalizedModule.linearEquiv (Submonoid.powers f)
    (LocalizedModule.mkLinearMap (Submonoid.powers f) M)
    (AlgebraicGeometry.tilde.toOpen (R := CommRingCat.of R) (ModuleCat.of R M)
      (PrimeSpectrum.basicOpen f)).hom

/-- The associated module sheaf has localized sections on every standard open.
The displayed target is the categorical sheaf packaging of the source's
basis-presheaf section object. -/
theorem exists_associatedModuleStandardOpenSectionsIso {R M : Type u}
    [CommRing R] [AddCommGroup M] [Module R M] (f : R) :
    Nonempty (LocalizedModule.Away f M ≃ₗ[R]
      (associatedModuleUnderlyingSheaf R M).presheaf.obj
        (op (PrimeSpectrum.basicOpen (R := R) f))) := by
  exact ⟨associatedModuleLocalizationToStandardOpenSections R M f⟩

/-! ## Stalks, sections, and the sheaf condition -/

/-- The stalk of the structure sheaf is the localization at the corresponding prime. -/
noncomputable def structureSheafStalkIso {R : Type u} [CommRing R]
    (p : PrimeSpectrum R) :
    Localization.AtPrime p.asIdeal ≃+*
      (AlgebraicGeometry.structurePresheafInCommRingCat R).stalk p :=
  letI : Algebra R ((AlgebraicGeometry.structurePresheafInCommRingCat R).stalk p) :=
    (AlgebraicGeometry.StructureSheaf.toStalk R p).hom.toAlgebra
  (AlgebraicGeometry.StructureSheaf.stalkIso R p).toRingEquiv

/-- The stalk of the associated module sheaf is the localized module `M_p`. -/
local instance associatedModuleStalkModule {R M : Type u} [CommRing R]
    [AddCommGroup M] [Module R M] (p : PrimeSpectrum R) :
    Module R ↑(TopCat.Presheaf.stalk
      (AlgebraicGeometry.moduleStructurePresheaf R M).presheaf p) :=
  AlgebraicGeometry.StructureSheaf.instModuleCarrierStalkAbPresheafOpensCarrierTopModuleStructurePresheaf p

noncomputable def associatedModuleStalkIso {R M : Type u} [CommRing R]
    [AddCommGroup M] [Module R M] (p : PrimeSpectrum R) :
    LocalizedModule p.asIdeal.primeCompl M ≃ₗ[R]
      ↑(TopCat.Presheaf.stalk (AlgebraicGeometry.moduleStructurePresheaf R M).presheaf p) :=
  letI : IsLocalizedModule p.asIdeal.primeCompl
      (AlgebraicGeometry.StructureSheaf.toStalkₗ R M p) :=
    AlgebraicGeometry.StructureSheaf.instIsLocalizedModuleCarrierStalkAbPresheafOpensCarrierTopModuleStructurePresheafPrimeComplAsIdealToStalkₗ p
  IsLocalizedModule.linearEquiv p.asIdeal.primeCompl
    (LocalizedModule.mkLinearMap p.asIdeal.primeCompl M)
    (AlgebraicGeometry.StructureSheaf.toStalkₗ R M p)

noncomputable instance associatedModuleStalkAtPrimeModule {R M : Type u} [CommRing R]
    [AddCommGroup M] [Module R M] (p : PrimeSpectrum R) :
    Module (Localization.AtPrime p.asIdeal)
      (↑(TopCat.Presheaf.stalk
        (AlgebraicGeometry.moduleStructurePresheaf R M).presheaf p)) :=
  (associatedModuleStalkIso p).symm.toAddEquiv.module _

noncomputable instance associatedModuleStalkAtPrimeScalarTower {R M : Type u} [CommRing R]
    [AddCommGroup M] [Module R M] (p : PrimeSpectrum R) :
    IsScalarTower R (Localization.AtPrime p.asIdeal)
      (↑(TopCat.Presheaf.stalk
        (AlgebraicGeometry.moduleStructurePresheaf R M).presheaf p)) :=
  (associatedModuleStalkIso p).symm.isScalarTower (Localization.AtPrime p.asIdeal)

/-- The module-stalk identification with its natural `Rₚ`-linear structure. -/
noncomputable def associatedModuleStalkIsoAtPrime {R M : Type u} [CommRing R]
    [AddCommGroup M] [Module R M] (p : PrimeSpectrum R) :
    LocalizedModule p.asIdeal.primeCompl M ≃ₗ[Localization.AtPrime p.asIdeal]
      ↑(TopCat.Presheaf.stalk (AlgebraicGeometry.moduleStructurePresheaf R M).presheaf p) := by
  exact LinearEquiv.extendScalarsOfIsLocalization p.asIdeal.primeCompl
    (Localization.AtPrime p.asIdeal) (associatedModuleStalkIso p)

/-! The canonical restriction maps are recorded through their localization
interfaces. The module statement uses the universal-property map from above,
since the section objects are not definitionally the localized-module types. -/

theorem ring_standardOpen_restriction_compatibility {R : Type u} [CommRing R]
    (f g : R) (h : standardOpen g ≤ standardOpen f) (x : Localization.Away f) :
    (AlgebraicGeometry.structureSheafInType R R).obj.map (homOfLE h).op
        (ringLocalizationToStandardOpenSections R f x) =
      ringLocalizationToStandardOpenSections R g
        (standardOpenLocalizationMap f g h x) := by
  let A_f := (AlgebraicGeometry.structureSheafInType R R).obj.obj
    (op (PrimeSpectrum.basicOpen f))
  let A_g := (AlgebraicGeometry.structureSheafInType R R).obj.obj
    (op (PrimeSpectrum.basicOpen g))
  let res : A_f →+* A_g :=
    { toFun := (AlgebraicGeometry.structureSheafInType R R).obj.map (homOfLE h).op
      map_one' := by rfl
      map_mul' := by intros; rfl
      map_zero' := by rfl
      map_add' := by intros; rfl }
  let left : Localization.Away f →+* A_g :=
    res.comp (ringLocalizationToStandardOpenSections R f).toRingHom
  let right : Localization.Away f →+* A_g :=
    (ringLocalizationToStandardOpenSections R g).toRingHom.comp
      (standardOpenLocalizationMap f g h)
  have heq : left = right := by
    apply IsLocalization.ringHom_ext (Submonoid.powers f)
    ext r
    simp [left, right, res, ringLocalizationToStandardOpenSections,
      standardOpenLocalizationMap]
    change (AlgebraicGeometry.structureSheafInType R R).obj.map (homOfLE h).op
        ((AlgebraicGeometry.StructureSheaf.toOpenₗ R R
          (PrimeSpectrum.basicOpen f)) r) =
      (AlgebraicGeometry.StructureSheaf.toOpenₗ R R
        (PrimeSpectrum.basicOpen g) r)
    unfold AlgebraicGeometry.StructureSheaf.toOpenₗ
    rfl
  change left x = right x
  rw [heq]

theorem module_standardOpen_restriction_compatibility {R M : Type u} [CommRing R]
    [AddCommGroup M] [Module R M] (f g : R) (h : standardOpen g ≤ standardOpen f) :
    ∀ x : LocalizedModule.Away f M,
      (AlgebraicGeometry.structureSheafInType R M).obj.map (homOfLE h).op
          (moduleLocalizationToStandardOpenSections R M f x) =
        moduleLocalizationToStandardOpenSections R M g
          (standardOpenModuleLocalizationMap f g h x) := by
  intro x
  let T :=
    (AlgebraicGeometry.modulesSpecToSheaf (R := CommRingCat.of R)).obj
      (AlgebraicGeometry.tilde (R := CommRingCat.of R) (ModuleCat.of R M))
  let U_f : Opens (AlgebraicGeometry.Spec (CommRingCat.of R)) :=
    PrimeSpectrum.basicOpen f
  let U_g : Opens (AlgebraicGeometry.Spec (CommRingCat.of R)) :=
    PrimeSpectrum.basicOpen g
  let T_f := T.presheaf.obj (op U_f)
  let T_g := T.presheaf.obj (op U_g)
  have hunit : IsUnit (algebraMap R (Module.End R T_g) f) := by
    exact AlgebraicGeometry.Scheme.Modules.isUnit_algebraMap_end_of_le_basicOpen
      (M := AlgebraicGeometry.tilde (R := CommRingCat.of R) (ModuleCat.of R M)) f
      (show U_g ≤ PrimeSpectrum.basicOpen f from h)
  have hunitPowers : ∀ s : Submonoid.powers f,
      IsUnit (algebraMap R (Module.End R T_g) s) := by
    rintro ⟨_, n, rfl⟩
    change IsUnit (algebraMap R (Module.End R T_g) (f ^ n))
    simpa only [map_pow] using hunit.pow n
  let hlocf : IsLocalizedModule (Submonoid.powers f)
      ((AlgebraicGeometry.tilde.toOpen
        (R := CommRingCat.of R) (ModuleCat.of R M) U_f).hom) :=
    AlgebraicGeometry.tilde.instAwayCarrierCarrierObjOppositeOpensCarrierCarrierCommRingCatSpecModuleCatPresheafModulesSheafModulesSpecToSheafOpBasicOpenHomToOpen
      (R := CommRingCat.of R) (ModuleCat.of R M) f
  let hlocg : IsLocalizedModule (Submonoid.powers g)
      ((AlgebraicGeometry.tilde.toOpen
        (R := CommRingCat.of R) (ModuleCat.of R M) U_g).hom) :=
    AlgebraicGeometry.tilde.instAwayCarrierCarrierObjOppositeOpensCarrierCarrierCommRingCatSpecModuleCatPresheafModulesSheafModulesSpecToSheafOpBasicOpenHomToOpen
      (R := CommRingCat.of R) (ModuleCat.of R M) g
  let := hlocf
  let := hlocg
  let e_f : LocalizedModule.Away f M ≃ₗ[R] T_f :=
    IsLocalizedModule.linearEquiv (Submonoid.powers f)
      (LocalizedModule.mkLinearMap (Submonoid.powers f) M)
      ((AlgebraicGeometry.tilde.toOpen
        (R := CommRingCat.of R) (ModuleCat.of R M) U_f).hom)
  let e_g : LocalizedModule.Away g M ≃ₗ[R] T_g :=
    IsLocalizedModule.linearEquiv (Submonoid.powers g)
      (LocalizedModule.mkLinearMap (Submonoid.powers g) M)
      ((AlgebraicGeometry.tilde.toOpen
        (R := CommRingCat.of R) (ModuleCat.of R M) U_g).hom)
  let res : T_f →ₗ[R] T_g :=
    (T.presheaf.map (homOfLE (show U_g ≤ U_f from h)).op).hom
  let left : LocalizedModule.Away f M →ₗ[R] T_g :=
    res.comp e_f.toLinearMap
  let right : LocalizedModule.Away f M →ₗ[R] T_g :=
    e_g.toLinearMap.comp (standardOpenModuleLocalizationMap f g h)
  have hleft : left.comp (LocalizedModule.mkLinearMap (Submonoid.powers f) M) =
      (AlgebraicGeometry.tilde.toOpen
        (R := CommRingCat.of R) (ModuleCat.of R M) U_g).hom := by
    ext m
    change res (e_f ((LocalizedModule.mkLinearMap (Submonoid.powers f) M) m)) =
      (AlgebraicGeometry.tilde.toOpen
        (R := CommRingCat.of R) (ModuleCat.of R M) U_g).hom m
    rw [IsLocalizedModule.linearEquiv_apply]
    change (T.presheaf.map (homOfLE (show U_g ≤ U_f from h)).op).hom
        ((AlgebraicGeometry.tilde.toOpen
          (R := CommRingCat.of R) (ModuleCat.of R M) U_f).hom m) =
      (AlgebraicGeometry.tilde.toOpen
        (R := CommRingCat.of R) (ModuleCat.of R M) U_g).hom m
    exact congr($(AlgebraicGeometry.tilde.toOpen_res
      (R := CommRingCat.of R) (M := ModuleCat.of R M)
      (PrimeSpectrum.basicOpen f) (PrimeSpectrum.basicOpen g) (homOfLE h)).hom m)
  have hright : right.comp (LocalizedModule.mkLinearMap (Submonoid.powers f) M) =
      (AlgebraicGeometry.tilde.toOpen
        (R := CommRingCat.of R) (ModuleCat.of R M) U_g).hom := by
    ext m
    change e_g ((standardOpenModuleLocalizationMap f g h).comp
      (LocalizedModule.mkLinearMap (Submonoid.powers f) M) m) =
      (AlgebraicGeometry.tilde.toOpen
        (R := CommRingCat.of R) (ModuleCat.of R M) U_g).hom m
    rw [standardOpenModuleLocalizationMap_comp]
    exact IsLocalizedModule.linearEquiv_apply _ _ _ m
  have hleft' := LocalizedModule.lift_unique (Submonoid.powers f)
    ((AlgebraicGeometry.tilde.toOpen
      (R := CommRingCat.of R) (ModuleCat.of R M) U_g).hom) hunitPowers left hleft
  have hright' := LocalizedModule.lift_unique (Submonoid.powers f)
    ((AlgebraicGeometry.tilde.toOpen
      (R := CommRingCat.of R) (ModuleCat.of R M) U_g).hom) hunitPowers right hright
  have heq : left x = right x := by
    rw [← hleft', ← hright']
  let α :=
    AlgebraicGeometry.tilde.modulesSpecToSheafIso
      (R := CommRingCat.of R) (ModuleCat.of R M)
  have hαf (z : T_f) :
      (α.app (op U_f)).hom.hom z =
        (z : (AlgebraicGeometry.structurePresheafInModuleCat R M).obj
          (op (PrimeSpectrum.basicOpen f))) := by
    rfl
  have hαg (z : T_g) :
      (α.app (op U_g)).hom.hom z =
        (z : (AlgebraicGeometry.structurePresheafInModuleCat R M).obj
          (op (PrimeSpectrum.basicOpen g))) := by
    rfl
  have hnat (z : T_f) :
      (α.app (op U_g)).hom.hom
          ((T.presheaf.map (homOfLE (show U_g ≤ U_f from h)).op).hom z) =
        ((AlgebraicGeometry.structurePresheafInModuleCat R M).map
          (homOfLE (show U_g ≤ U_f from h)).op).hom
          ((α.app (op U_f)).hom.hom z) := by
    exact congr($(α.hom.naturality (homOfLE (show U_g ≤ U_f from h)).op).hom z)
  have hef :
      (α.app (op U_f)).hom.hom.comp e_f.toLinearMap =
        (moduleLocalizationToStandardOpenSections R M f).toLinearMap := by
    apply IsLocalizedModule.linearMap_ext (Submonoid.powers f)
      (LocalizedModule.mkLinearMap (Submonoid.powers f) M)
      (AlgebraicGeometry.StructureSheaf.toOpenₗ R M
        (PrimeSpectrum.basicOpen f))
    ext m
    change (α.app (op U_f)).hom.hom
        (e_f ((LocalizedModule.mkLinearMap (Submonoid.powers f) M) m)) =
      (moduleLocalizationToStandardOpenSections R M f)
        ((LocalizedModule.mkLinearMap (Submonoid.powers f) M) m)
    rw [IsLocalizedModule.linearEquiv_apply]
    rw [hαf]
    change (AlgebraicGeometry.StructureSheaf.toOpenₗ R M
      (PrimeSpectrum.basicOpen f)) m = _
    simpa only [moduleLocalizationToStandardOpenSections] using
      (IsLocalizedModule.linearEquiv_apply (S := Submonoid.powers f)
        (f := LocalizedModule.mkLinearMap (Submonoid.powers f) M)
        (g := AlgebraicGeometry.StructureSheaf.toOpenₗ R M
          (PrimeSpectrum.basicOpen f)) m).symm
  have heg :
      (α.app (op U_g)).hom.hom.comp e_g.toLinearMap =
        (moduleLocalizationToStandardOpenSections R M g).toLinearMap := by
    apply IsLocalizedModule.linearMap_ext (Submonoid.powers g)
      (LocalizedModule.mkLinearMap (Submonoid.powers g) M)
      (AlgebraicGeometry.StructureSheaf.toOpenₗ R M
        (PrimeSpectrum.basicOpen g))
    ext m
    change (α.app (op U_g)).hom.hom
        (e_g ((LocalizedModule.mkLinearMap (Submonoid.powers g) M) m)) =
      (moduleLocalizationToStandardOpenSections R M g)
        ((LocalizedModule.mkLinearMap (Submonoid.powers g) M) m)
    rw [IsLocalizedModule.linearEquiv_apply]
    rw [hαg]
    change (AlgebraicGeometry.StructureSheaf.toOpenₗ R M
      (PrimeSpectrum.basicOpen g)) m = _
    simpa only [moduleLocalizationToStandardOpenSections] using
      (IsLocalizedModule.linearEquiv_apply (S := Submonoid.powers g)
        (f := LocalizedModule.mkLinearMap (Submonoid.powers g) M)
        (g := AlgebraicGeometry.StructureSheaf.toOpenₗ R M
          (PrimeSpectrum.basicOpen g)) m).symm
  have heq' := congrArg (fun z : T_g =>
      (α.app (op U_g)).hom.hom z) heq
  change
    (α.app (op U_g)).hom.hom
        ((T.presheaf.map (homOfLE (show U_g ≤ U_f from h)).op).hom (e_f x)) =
      (α.app (op U_g)).hom.hom
        (e_g (standardOpenModuleLocalizationMap f g h x)) at heq'
  rw [hnat (e_f x)] at heq'
  have hleftvalue := congrArg (fun q => q x) hef
  have hrightvalue := congrArg
    (fun q => q (standardOpenModuleLocalizationMap f g h x)) heg
  have hleftvalue' :
      (α.app (op U_f)).hom.hom (e_f x) =
        moduleLocalizationToStandardOpenSections R M f x := by
    exact hleftvalue
  have hrightvalue' :
      (α.app (op U_g)).hom.hom
          (e_g (standardOpenModuleLocalizationMap f g h x)) =
        moduleLocalizationToStandardOpenSections R M g
          (standardOpenModuleLocalizationMap f g h x) := by
    exact hrightvalue
  rw [hleftvalue', hrightvalue'] at heq'
  exact heq'

/-- Global sections of the structure sheaf recover the original ring. -/
noncomputable def structureSheafGlobalSectionsIso {R : Type u} [CommRing R] :
    CommRingCat.of R ≅
      (AlgebraicGeometry.structurePresheafInCommRingCat R).obj
        (op (⊤ : Opens (spectrumTop R))) :=
  AlgebraicGeometry.StructureSheaf.globalSectionsIso R

/-- Global sections of the associated module sheaf recover the original module. -/
noncomputable def associatedModuleGlobalSectionsIso {R M : Type u} [CommRing R]
    [AddCommGroup M] [Module R M] :
    ModuleCat.of R M ≅
      (associatedModuleUnderlyingSheaf R M).presheaf.obj
        (op (⊤ : Opens (AlgebraicGeometry.Spec (CommRingCat.of R)))) :=
  AlgebraicGeometry.tilde.isoTop (R := CommRingCat.of R) (ModuleCat.of R M)

/- The source's direct sums are represented by finite products indexed by
`Fin n` (and by `Fin n × Fin n` for the pairwise intersections). -/

/-- The first map in the finite-cover Čech sequence
`0 → M_f → ⨁ M_{g_i}`. -/
noncomputable def standardOpenCechZero {R M : Type u} [CommRing R]
    [AddCommGroup M] [Module R M] (f : R) (n : ℕ) (g : Fin n → R)
    (hcover : standardOpen f = ⨆ i, standardOpen (g i)) :
    LocalizedModule.Away f M →ₗ[R]
      (∀ i, LocalizedModule.Away (g i) M) := by
  have hle : ∀ i, standardOpen (g i) ≤ standardOpen f := by
    intro i
    rw [hcover]
    exact le_iSup (fun i => standardOpen (g i)) i
  exact
    { toFun := fun s i => standardOpenModuleLocalizationMap f (g i) (hle i) s
      map_add' := by
        intro s t
        funext i
        exact (standardOpenModuleLocalizationMap f (g i) (hle i)).map_add s t
      map_smul' := by
        intro a s
        funext i
        exact (standardOpenModuleLocalizationMap f (g i) (hle i)).map_smul a s }

/-- The second map in the finite-cover Čech sequence
`⨁ M_{g_i} → ⨁ M_{g_i g_j}`. -/
noncomputable def standardOpenCechOne {R M : Type u} [CommRing R]
    [AddCommGroup M] [Module R M] (f : R) (n : ℕ) (g : Fin n → R)
    (_hcover : standardOpen f = ⨆ i, standardOpen (g i)) :
    (∀ i, LocalizedModule.Away (g i) M) →ₗ[R]
      (∀ ij : Fin n × Fin n, LocalizedModule.Away (g ij.1 * g ij.2) M) := by
  exact
    { toFun := fun s ij =>
        let hleft : standardOpen (g ij.1 * g ij.2) ≤ standardOpen (g ij.1) := by
          exact standardOpen_mul_le_left _ _
        let hright : standardOpen (g ij.1 * g ij.2) ≤ standardOpen (g ij.2) := by
          exact standardOpen_mul_le_right _ _
        standardOpenModuleLocalizationMap (g ij.1) (g ij.1 * g ij.2) hleft (s ij.1) -
          standardOpenModuleLocalizationMap (g ij.2) (g ij.1 * g ij.2) hright (s ij.2)
      map_add' := by
        intro s t
        funext ij
        simp only [Pi.add_apply]
        rw [map_add, map_add]
        abel
      map_smul' := by
        intro a s
        funext ij
        simp only [Pi.smul_apply]
        simp only [map_smul, RingHom.id_apply, smul_sub] }

/-- Exactness of the finite-cover Čech sequence for a standard-open covering. -/
theorem standardOpenCech_exact {R M : Type u} [CommRing R]
    [AddCommGroup M] [Module R M] (f : R) (n : ℕ) (g : Fin n → R)
    (hcover : standardOpen f = ⨆ i, standardOpen (g i)) :
    Function.Injective (standardOpenCechZero (R := R) (M := M) f n g hcover) ∧
      Function.Exact (standardOpenCechZero (R := R) (M := M) f n g hcover)
        (standardOpenCechOne (R := R) (M := M) f n g hcover) := by
  classical
  let ι : Type u := ULift (Fin n)
  let U : ι → Opens (spectrumTop R) := fun i => standardOpen (g i.down)
  let F := (AlgebraicGeometry.structureSheafInType R M).presheaf
  have hiSup : iSup U = standardOpen f := by
    apply le_antisymm
    · refine iSup_le ?_
      intro i
      rw [hcover]
      exact le_iSup_of_le i.down (by rfl)
    · rw [hcover]
      refine iSup_le ?_
      intro i
      exact le_iSup_of_le (.up i) (by rfl)
  have hle (i : ι) : U i ≤ standardOpen f := by
    rw [← hiSup]
    exact le_iSup U i
  let sec (x : LocalizedModule.Away f M) (i : ι) :
      F.obj (op (U i)) :=
    moduleLocalizationToStandardOpenSections R M (g i.down)
      (standardOpenModuleLocalizationMap f (g i.down) (hle i) x)
  have hlocal_compatible (x : LocalizedModule.Away f M) :
      TopCat.Presheaf.IsCompatible F U (sec x) := by
    intro i j
    have hleft : Opens.infLELeft (U i) (U j) =
        homOfLE (show U i ⊓ U j ≤ U i from inf_le_left) :=
      Subsingleton.elim _ _
    have hright : Opens.infLERight (U i) (U j) =
        homOfLE (show U i ⊓ U j ≤ U j from inf_le_right) :=
      Subsingleton.elim _ _
    rw [hleft, hright]
    have hinter : U i ⊓ U j = standardOpen (g i.down * g j.down) := by
      dsimp [U]
      rw [standardOpen_inter]
    let hgi : standardOpen (g i.down * g j.down) ≤
        standardOpen (g i.down) := standardOpen_mul_le_left _ _
    let hgj : standardOpen (g i.down * g j.down) ≤
        standardOpen (g j.down) := standardOpen_mul_le_right _ _
    have hres_i := module_standardOpen_restriction_compatibility
      (R := R) (M := M) (g i.down) (g i.down * g j.down) hgi
        (standardOpenModuleLocalizationMap f (g i.down) (hle i) x)
    have hres_j := module_standardOpen_restriction_compatibility
      (R := R) (M := M) (g j.down) (g i.down * g j.down) hgj
        (standardOpenModuleLocalizationMap f (g j.down) (hle j) x)
    have hres_i' :
        F.map (homOfLE hgi).op
            (moduleLocalizationToStandardOpenSections R M (g i.down)
              (standardOpenModuleLocalizationMap f (g i.down) (hle i) x)) =
          moduleLocalizationToStandardOpenSections R M (g i.down * g j.down)
            (standardOpenModuleLocalizationMap (g i.down) (g i.down * g j.down)
              hgi (standardOpenModuleLocalizationMap f (g i.down) (hle i) x)) := by
      simpa [F] using hres_i
    have hres_j' :
        F.map (homOfLE hgj).op
            (moduleLocalizationToStandardOpenSections R M (g j.down)
              (standardOpenModuleLocalizationMap f (g j.down) (hle j) x)) =
          moduleLocalizationToStandardOpenSections R M (g i.down * g j.down)
            (standardOpenModuleLocalizationMap (g j.down) (g i.down * g j.down)
              hgj (standardOpenModuleLocalizationMap f (g j.down) (hle j) x)) := by
      simpa [F] using hres_j
    have hrestr_i :
        F.map (homOfLE (show U i ⊓ U j ≤ U i from inf_le_left)).op (sec x i) =
          F.map (eqToHom hinter).op
            (F.map (homOfLE hgi).op
              (moduleLocalizationToStandardOpenSections R M (g i.down)
                (standardOpenModuleLocalizationMap f (g i.down) (hle i) x))) := by
      dsimp [sec]
      rw [← Functor.map_comp_apply]
      congr 1
    have hrestr_j :
        F.map (homOfLE (show U i ⊓ U j ≤ U j from inf_le_right)).op (sec x j) =
          F.map (eqToHom hinter).op
            (F.map (homOfLE hgj).op
              (moduleLocalizationToStandardOpenSections R M (g j.down)
                (standardOpenModuleLocalizationMap f (g j.down) (hle j) x))) := by
      dsimp [sec]
      rw [← Functor.map_comp_apply]
      congr 1
    rw [hrestr_i, hrestr_j, hres_i', hres_j']
    congr 1
    rw [← LinearMap.comp_apply,
      ← standardOpenModuleLocalizationMap_comp_of_subset f (g i.down)
        (g i.down * g j.down) (hle i) hgi]
    rw [← LinearMap.comp_apply,
      ← standardOpenModuleLocalizationMap_comp_of_subset f (g j.down)
        (g i.down * g j.down) (hle j) hgj]
  have hF : TopCat.Presheaf.IsSheaf F := by
    exact (AlgebraicGeometry.structureSheafInType R M).property
  let global (x : LocalizedModule.Away f M) : F.obj (op (standardOpen f)) :=
    moduleLocalizationToStandardOpenSections R M f x
  let transported (x : LocalizedModule.Away f M) : F.obj (op (iSup U)) :=
    F.map (eqToHom hiSup).op (global x)
  have hglobal_glue (x : LocalizedModule.Away f M) :
      TopCat.Presheaf.IsGluing F U (sec x) (transported x) := by
    intro i
    dsimp [transported]
    rw [← Functor.map_comp_apply]
    rw [show (eqToHom hiSup).op ≫ (Opens.leSupr U i).op =
        (homOfLE (hle i)).op from Subsingleton.elim _ _]
    simpa [F, global, sec, U] using
      (module_standardOpen_restriction_compatibility
        (R := R) (M := M) f (g i.down) (hle i) x)
  constructor
  · intro x y hxy
    have hsec : sec x = sec y := by
      funext i
      dsimp [sec]
      congr 1
      simpa [standardOpenCechZero] using congrFun hxy i.down
    have hglue_x := hglobal_glue x
    have hglue_y :
        TopCat.Presheaf.IsGluing F U (sec x) (transported y) := by
      simpa [hsec] using hglobal_glue y
    obtain ⟨tx, htx, htx_unique⟩ :=
      hF.isSheafUniqueGluing_types (sec x) (hlocal_compatible x)
    have htransport : transported x = transported y :=
      (htx_unique (transported x) hglue_x).trans
        (htx_unique (transported y) hglue_y).symm
    have hglobal : global x = global y := by
      apply (ConcreteCategory.bijective_of_isIso
        (F.map (eqToHom hiSup).op)).1
      exact htransport
    exact (moduleLocalizationToStandardOpenSections R M f).injective hglobal
  · intro z
    constructor
    · intro hz
      have hpair (i j : Fin n) :
          standardOpenModuleLocalizationMap (g i) (g i * g j)
              (standardOpen_mul_le_left _ _) (z i) =
            standardOpenModuleLocalizationMap (g j) (g i * g j)
              (standardOpen_mul_le_right _ _) (z j) := by
        have h := congrFun hz (i, j)
        change standardOpenModuleLocalizationMap (g i) (g i * g j)
              (standardOpen_mul_le_left _ _) (z i) -
            standardOpenModuleLocalizationMap (g j) (g i * g j)
              (standardOpen_mul_le_right _ _) (z j) = 0 at h
        exact sub_eq_zero.mp h
      let zsec (i : ι) : F.obj (op (U i)) :=
        moduleLocalizationToStandardOpenSections R M (g i.down) (z i.down)
      have hzcompat : TopCat.Presheaf.IsCompatible F U zsec := by
        intro i j
        have hleft : Opens.infLELeft (U i) (U j) =
            homOfLE (show U i ⊓ U j ≤ U i from inf_le_left) :=
          Subsingleton.elim _ _
        have hright : Opens.infLERight (U i) (U j) =
            homOfLE (show U i ⊓ U j ≤ U j from inf_le_right) :=
          Subsingleton.elim _ _
        rw [hleft, hright]
        have hinter : U i ⊓ U j = standardOpen (g i.down * g j.down) := by
          dsimp [U]
          rw [standardOpen_inter]
        let hgi : standardOpen (g i.down * g j.down) ≤
            standardOpen (g i.down) := standardOpen_mul_le_left _ _
        let hgj : standardOpen (g i.down * g j.down) ≤
            standardOpen (g j.down) := standardOpen_mul_le_right _ _
        have hres_i := module_standardOpen_restriction_compatibility
          (R := R) (M := M) (g i.down) (g i.down * g j.down) hgi (z i.down)
        have hres_j := module_standardOpen_restriction_compatibility
          (R := R) (M := M) (g j.down) (g i.down * g j.down) hgj (z j.down)
        have hres_i' :
            F.map (homOfLE hgi).op (zsec i) =
              moduleLocalizationToStandardOpenSections R M
                (g i.down * g j.down)
                (standardOpenModuleLocalizationMap (g i.down)
                  (g i.down * g j.down) hgi (z i.down)) := by
          simpa [F, zsec] using hres_i
        have hres_j' :
            F.map (homOfLE hgj).op (zsec j) =
              moduleLocalizationToStandardOpenSections R M
                (g i.down * g j.down)
                (standardOpenModuleLocalizationMap (g j.down)
                  (g i.down * g j.down) hgj (z j.down)) := by
          simpa [F, zsec] using hres_j
        have hrestr_i :
            F.map (homOfLE (show U i ⊓ U j ≤ U i from inf_le_left)).op
                (zsec i) =
              F.map (eqToHom hinter).op (F.map (homOfLE hgi).op (zsec i)) := by
          rw [← Functor.map_comp_apply]
          congr 1
        have hrestr_j :
            F.map (homOfLE (show U i ⊓ U j ≤ U j from inf_le_right)).op
                (zsec j) =
              F.map (eqToHom hinter).op (F.map (homOfLE hgj).op (zsec j)) := by
          rw [← Functor.map_comp_apply]
          congr 1
        rw [hrestr_i, hrestr_j, hres_i', hres_j']
        rw [hpair i.down j.down]
      obtain ⟨t, ht, _⟩ := hF.isSheafUniqueGluing_types zsec hzcompat
      let s : F.obj (op (standardOpen f)) :=
        F.map (eqToHom hiSup.symm).op t
      let x : LocalizedModule.Away f M :=
        (moduleLocalizationToStandardOpenSections R M f).symm s
      have hs (i : ι) :
          F.map (homOfLE (hle i)).op s = zsec i := by
        dsimp [s]
        rw [← Functor.map_comp_apply]
        rw [show (eqToHom hiSup.symm).op ≫ (homOfLE (hle i)).op =
            (Opens.leSupr U i).op from Subsingleton.elim _ _]
        exact ht i
      have hx (i : ι) :
          standardOpenModuleLocalizationMap f (g i.down) (hle i) x = z i.down := by
        have h := module_standardOpen_restriction_compatibility
          (R := R) (M := M) f (g i.down) (hle i) x
        have h' :
            F.map (homOfLE (hle i)).op (s) =
              moduleLocalizationToStandardOpenSections R M (g i.down)
                (standardOpenModuleLocalizationMap f (g i.down) (hle i) x) := by
          simpa [F, s, x] using h
        rw [hs i] at h'
        exact (moduleLocalizationToStandardOpenSections R M (g i.down)).injective h'.symm
      refine ⟨x, ?_⟩
      funext i
      simpa [standardOpenCechZero, zsec, U] using hx (.up i)
    · intro hy
      obtain ⟨x, rfl⟩ := hy
      ext ij
      let hfi : standardOpen (g ij.1) ≤ standardOpen f := by
        rw [hcover]
        exact le_iSup (fun i => standardOpen (g i)) ij.1
      let hfj : standardOpen (g ij.2) ≤ standardOpen f := by
        rw [hcover]
        exact le_iSup (fun i => standardOpen (g i)) ij.2
      let hij : standardOpen (g ij.1 * g ij.2) ≤ standardOpen (g ij.1) :=
        standardOpen_mul_le_left _ _
      let hjj : standardOpen (g ij.1 * g ij.2) ≤ standardOpen (g ij.2) :=
        standardOpen_mul_le_right _ _
      change standardOpenModuleLocalizationMap (g ij.1)
              (g ij.1 * g ij.2) hij
              (standardOpenModuleLocalizationMap f (g ij.1) hfi x) -
          standardOpenModuleLocalizationMap (g ij.2)
              (g ij.1 * g ij.2) hjj
              (standardOpenModuleLocalizationMap f (g ij.2) hfj x) = 0
      rw [← LinearMap.comp_apply,
        ← standardOpenModuleLocalizationMap_comp_of_subset f (g ij.1)
          (g ij.1 * g ij.2) hfi hij]
      rw [← LinearMap.comp_apply,
        ← standardOpenModuleLocalizationMap_comp_of_subset f (g ij.2)
          (g ij.1 * g ij.2) hfj hjj]
      simp

/-! ## Functoriality and exactness of associated module sheaves -/

/-- The canonical functor sending an `R`-module to its associated sheaf. -/
abbrev associatedModuleFunctor (R : Type u) [CommRing R] :
    ModuleCat (CommRingCat.of R) ⥤
      (AlgebraicGeometry.Spec (CommRingCat.of R)).Modules :=
  AlgebraicGeometry.tilde.functor (CommRingCat.of R)

instance associatedModuleFunctor_preservesZeroMorphisms {R : Type u} [CommRing R] :
    (associatedModuleFunctor R).PreservesZeroMorphisms where
  map_zero X Y := by
    exact AlgebraicGeometry.tilde.map_zero

/-- Associated module sheaves preserve exact short complexes. -/
theorem associatedModuleFunctor_exact {R : Type u} [CommRing R]
    (S : ShortComplex (ModuleCat (CommRingCat.of R))) (hS : S.Exact) :
    (S.map (associatedModuleFunctor R)).Exact := by
  let T := SheafOfModules.toSheaf
    (R := (AlgebraicGeometry.Spec (CommRingCat.of R)).ringCatSheaf)
  let T' : (AlgebraicGeometry.Spec (CommRingCat.of R)).Modules ⥤
      TopCat.Sheaf AddCommGrpCat (AlgebraicGeometry.Spec (CommRingCat.of R)) :=
    { obj := T.obj
      map := T.map
      map_id := by intro X; exact T.map_id X
      map_comp := by intro X Y Z f g; exact T.map_comp f g }
  let hTzero : T'.PreservesZeroMorphisms := by
    constructor
    intro X Y
    change T.map (0 : X ⟶ Y) = 0
    exact T.map_zero X Y
  let ST : ShortComplex _ :=
    @ShortComplex.map _ _ _ _ _ _ (S.map (associatedModuleFunctor R)) T' hTzero
  /- Prior attempt: the explicit stalk-map construction timed out during
     elaboration and then failed in the scalar-action rewrite. -/
  /- Prior attempt body retained below for reference.
  have hST : ST.Exact := by
    rw [TopCat.Sheaf.exact_iff_stalkFunctor_map_exact]
    intro x
    rw [ShortComplex.ab_exact_iff_function_exact]
    have hfun : Function.Exact S.f.hom S.g.hom :=
      (CategoryTheory.ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).mp hS
    let x₀ : PrimeSpectrum.Top R := by
      change PrimeSpectrum R at x
      exact x
    let : x₀.asIdeal.IsPrime := x₀.2
    have hloc := IsLocalizedModule.map_exact x₀.asIdeal.primeCompl
      (AlgebraicGeometry.StructureSheaf.toStalkₗ R S.X₁ x₀)
      (AlgebraicGeometry.StructureSheaf.toStalkₗ R S.X₂ x₀)
      (AlgebraicGeometry.StructureSheaf.toStalkₗ R S.X₃ x₀)
      S.f.hom S.g.hom hfun
    let pf := ((Sheaf.forget AddCommGrpCat
      (AlgebraicGeometry.Spec (CommRingCat.of R))).map
        ((SheafOfModules.toSheaf
          (R := (AlgebraicGeometry.Spec (CommRingCat.of R)).ringCatSheaf)).map
          (AlgebraicGeometry.tilde.map S.f)))
    let lf : (↑(TopCat.Presheaf.stalk
        (AlgebraicGeometry.moduleStructurePresheaf R (S.X₁ : ModuleCat (CommRingCat.of R))).presheaf x₀)) →ₗ[R]
        (↑(TopCat.Presheaf.stalk
          (AlgebraicGeometry.moduleStructurePresheaf R (S.X₂ : ModuleCat (CommRingCat.of R))).presheaf x₀)) :=
      { toFun := ConcreteCategory.hom
          ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x₀).map pf)
        map_add' := by intros; exact map_add _ _ _
        map_smul' := by
          intros r z
          obtain ⟨U, hxU, s, rfl⟩ :=
            TopCat.Presheaf.exists_germ_eq
              (AlgebraicGeometry.moduleStructurePresheaf R S.X₁).presheaf z
          let s' : (AlgebraicGeometry.structureSheafInType R S.X₁).obj.obj (op U) := s
          change (ConcreteCategory.hom
              ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x₀).map pf))
              (AlgebraicGeometry.StructureSheaf.toStalk R x₀ r •
                (ConcreteCategory.hom (TopCat.Presheaf.germ
                  (AlgebraicGeometry.moduleStructurePresheaf R S.X₁).presheaf U x₀ hxU)) s') = _
          have hgm :=
            (AlgebraicGeometry.moduleStructurePresheaf R S.X₁).germ_smul
              (U := U) (x := x₀) (hx := hxU)
              ((algebraMap R ((AlgebraicGeometry.structureSheafInType R R).obj.obj (op U))) r) s'
          have hmap :=
            ((AlgebraicGeometry.tilde.map S.f).val.app (op U)).hom.map_smul
              ((algebraMap R ((AlgebraicGeometry.structureSheafInType R R).obj.obj (op U))) r) s'
          have hscalar :
              AlgebraicGeometry.StructureSheaf.toStalk R x₀ r •
                  (ConcreteCategory.hom (TopCat.Presheaf.germ
                    (AlgebraicGeometry.moduleStructurePresheaf R S.X₁).presheaf U x₀ hxU)) s' =
                (ConcreteCategory.hom ((AlgebraicGeometry.structurePresheafInCommRingCat R).germ
                  U x₀ hxU))
                    ((algebraMap R ((AlgebraicGeometry.structureSheafInType R R).obj.obj (op U))) r) •
                  (ConcreteCategory.hom (TopCat.Presheaf.germ
                    (AlgebraicGeometry.moduleStructurePresheaf R S.X₁).presheaf U x₀ hxU)) s' := by
            congr 1
            exact (AlgebraicGeometry.StructureSheaf.algebraMap_germ_apply U x₀ hxU r).symm
          have hstalk :
              (ConcreteCategory.hom
                ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x₀).map pf))
                  ((ConcreteCategory.hom (TopCat.Presheaf.germ
                    (AlgebraicGeometry.moduleStructurePresheaf R S.X₁).presheaf U x₀ hxU))
                    (((algebraMap R ((AlgebraicGeometry.structureSheafInType R R).obj.obj (op U))) r) • s')) =
                (ConcreteCategory.hom (TopCat.Presheaf.germ
                  (AlgebraicGeometry.moduleStructurePresheaf R S.X₂).presheaf U x₀ hxU))
                  ((ConcreteCategory.hom (pf.app (op U)))
                    (((algebraMap R ((AlgebraicGeometry.structureSheafInType R R).obj.obj (op U))) r) • s')) := by
            convert TopCat.Presheaf.stalkFunctor_map_germ_apply U x₀ hxU pf
              (((algebraMap R ((AlgebraicGeometry.structureSheafInType R R).obj.obj (op U))) r) • s') using 1 <;>
              rfl
          have hstalk₀ :
              (ConcreteCategory.hom
                ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x₀).map pf))
                  ((ConcreteCategory.hom (TopCat.Presheaf.germ
                    (AlgebraicGeometry.moduleStructurePresheaf R S.X₁).presheaf U x₀ hxU)) s') =
                (ConcreteCategory.hom (TopCat.Presheaf.germ
                  (AlgebraicGeometry.moduleStructurePresheaf R S.X₂).presheaf U x₀ hxU))
                  ((ConcreteCategory.hom (pf.app (op U))) s') := by
            convert TopCat.Presheaf.stalkFunctor_map_germ_apply U x₀ hxU pf s' using 1 <;>
              rfl
          have h1 :
              (ConcreteCategory.hom
                ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x₀).map pf))
                  (AlgebraicGeometry.StructureSheaf.toStalk R x₀ r •
                    (ConcreteCategory.hom (TopCat.Presheaf.germ
                      (AlgebraicGeometry.moduleStructurePresheaf R S.X₁).presheaf U x₀ hxU)) s') =
                (ConcreteCategory.hom
                  ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x₀).map pf))
                  ((ConcreteCategory.hom (TopCat.Presheaf.germ
                    (AlgebraicGeometry.moduleStructurePresheaf R S.X₁).presheaf U x₀ hxU))
                    (((algebraMap R ((AlgebraicGeometry.structureSheafInType R R).obj.obj (op U))) r) • s')) := by
            exact (congrArg _ hscalar).trans (congrArg _ hgm.symm)
          let t' : (AlgebraicGeometry.structureSheafInType R S.X₂).obj.obj (op U) :=
            (ConcreteCategory.hom (pf.app (op U))) s'
          have h2 :
              (ConcreteCategory.hom (TopCat.Presheaf.germ
                (AlgebraicGeometry.moduleStructurePresheaf R S.X₂).presheaf U x₀ hxU))
                ((ConcreteCategory.hom (pf.app (op U)))
                  (((algebraMap R ((AlgebraicGeometry.structureSheafInType R R).obj.obj (op U))) r) • s')) =
                (RingHom.id R) r •
                  (ConcreteCategory.hom (TopCat.Presheaf.germ
                    (AlgebraicGeometry.moduleStructurePresheaf R S.X₂).presheaf U x₀ hxU))
                    t' := by
            have hmap_pf :
                (ConcreteCategory.hom (pf.app (op U)))
                    (((algebraMap R ((AlgebraicGeometry.structureSheafInType R R).obj.obj (op U))) r) • s') =
                  ((algebraMap R ((AlgebraicGeometry.structureSheafInType R R).obj.obj (op U))) r) •
                    t' := by
              dsimp [t']
              convert hmap using 1 <;> rfl
            rw [hmap_pf]
            have hgm₂ :=
              (AlgebraicGeometry.moduleStructurePresheaf R S.X₂).germ_smul
                (U := U) (x := x₀) (hx := hxU)
                ((algebraMap R ((AlgebraicGeometry.structureSheafInType R R).obj.obj (op U))) r) t'
            have hsring :
                (ConcreteCategory.hom ((AlgebraicGeometry.structurePresheafInCommRingCat R).germ
                  U x₀ hxU))
                    ((algebraMap R ((AlgebraicGeometry.structureSheafInType R R).obj.obj (op U))) r) •
                  (ConcreteCategory.hom (TopCat.Presheaf.germ
                    (AlgebraicGeometry.moduleStructurePresheaf R S.X₂).presheaf U x₀ hxU)) t' =
                (ConcreteCategory.hom (AlgebraicGeometry.StructureSheaf.toStalk R x₀)) r •
                  (ConcreteCategory.hom (TopCat.Presheaf.germ
                    (AlgebraicGeometry.moduleStructurePresheaf R S.X₂).presheaf U x₀ hxU)) t' := by
              congr 1
              exact AlgebraicGeometry.StructureSheaf.algebraMap_germ_apply U x₀ hxU r
            exact hgm₂.trans (hsring.trans
              (IsScalarTower.algebraMap_smul
                ((AlgebraicGeometry.structurePresheafInCommRingCat R).stalk x₀) r _))
          exact h1.trans (hstalk.trans (h2.trans
            (congrArg (fun q => (RingHom.id R) r • q) hstalk₀.symm))) }
    have hlf : lf =
        IsLocalizedModule.map x₀.asIdeal.primeCompl
          (AlgebraicGeometry.StructureSheaf.toStalkₗ R S.X₁ x₀)
          (AlgebraicGeometry.StructureSheaf.toStalkₗ R S.X₂ x₀) S.f.hom := by
      /- Prior attempt: the explicit linear-map extensionality proof timed out
         while rewriting the stalk functor's map on germs.
      apply IsLocalizedModule.linearMap_ext x₀.asIdeal.primeCompl
        (AlgebraicGeometry.StructureSheaf.toStalkₗ R S.X₁ x₀)
        (AlgebraicGeometry.StructureSheaf.toStalkₗ R S.X₂ x₀)
      ext m
      simp [lf, pf, AlgebraicGeometry.StructureSheaf.toStalkₗ,
        AlgebraicGeometry.tilde.map,
        AlgebraicGeometry.tilde.modulesSpecToSheafIso]
      rw [TopCat.Presheaf.stalkFunctor_map_germ_apply]
      rw [IsLocalizedModule.map_apply] -/
      sorry
    let pg := ((Sheaf.forget AddCommGrpCat
      (AlgebraicGeometry.Spec (CommRingCat.of R))).map
        ((SheafOfModules.toSheaf
          (R := (AlgebraicGeometry.Spec (CommRingCat.of R)).ringCatSheaf)).map
          (AlgebraicGeometry.tilde.map S.g)))
    let lg : (↑(TopCat.Presheaf.stalk
        (AlgebraicGeometry.moduleStructurePresheaf R (S.X₂ : ModuleCat (CommRingCat.of R))).presheaf x₀)) →ₗ[R]
        (↑(TopCat.Presheaf.stalk
          (AlgebraicGeometry.moduleStructurePresheaf R (S.X₃ : ModuleCat (CommRingCat.of R))).presheaf x₀)) :=
      { toFun := ConcreteCategory.hom
          ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x₀).map pg)
        map_add' := by intros; exact map_add _ _ _
        map_smul' := by
          intros r z
          obtain ⟨U, hxU, s, rfl⟩ :=
            TopCat.Presheaf.exists_germ_eq
              (AlgebraicGeometry.moduleStructurePresheaf R S.X₂).presheaf z
          let s' : (AlgebraicGeometry.structureSheafInType R S.X₂).obj.obj (op U) := s
          change (ConcreteCategory.hom
              ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x₀).map pg))
              (AlgebraicGeometry.StructureSheaf.toStalk R x₀ r •
                (ConcreteCategory.hom (TopCat.Presheaf.germ
                  (AlgebraicGeometry.moduleStructurePresheaf R S.X₂).presheaf U x₀ hxU)) s') = _
          have hscalar :
              AlgebraicGeometry.StructureSheaf.toStalk R x₀ r •
                  (ConcreteCategory.hom (TopCat.Presheaf.germ
                    (AlgebraicGeometry.moduleStructurePresheaf R S.X₂).presheaf U x₀ hxU)) s' =
                (ConcreteCategory.hom ((AlgebraicGeometry.structurePresheafInCommRingCat R).germ
                  U x₀ hxU))
                    ((algebraMap R ((AlgebraicGeometry.structureSheafInType R R).obj.obj (op U))) r) •
                  (ConcreteCategory.hom (TopCat.Presheaf.germ
                    (AlgebraicGeometry.moduleStructurePresheaf R S.X₂).presheaf U x₀ hxU)) s' := by
            congr 1
            exact (AlgebraicGeometry.StructureSheaf.algebraMap_germ_apply U x₀ hxU r).symm
          rw [hscalar]
          rw [← (AlgebraicGeometry.moduleStructurePresheaf R S.X₂).germ_smul
            (U := U) (x := x₀) (hx := hxU)]
          rw [TopCat.Presheaf.stalkFunctor_map_germ_apply]
          rw [((AlgebraicGeometry.tilde.map S.g).val.app (op U)).hom.map_smul]
          rw [(AlgebraicGeometry.moduleStructurePresheaf R S.X₃).germ_smul]
          rw [IsScalarTower.algebraMap_smul
            ((AlgebraicGeometry.structurePresheafInCommRingCat R).stalk x₀) r]
          rfl }
    have hlg : lg =
        IsLocalizedModule.map x₀.asIdeal.primeCompl
          (AlgebraicGeometry.StructureSheaf.toStalkₗ R S.X₂ x₀)
          (AlgebraicGeometry.StructureSheaf.toStalkₗ R S.X₃ x₀) S.g.hom := by
      /- Prior attempt: the explicit linear-map extensionality proof reached a
         type-mismatch while rewriting the induced map on module sections.
      apply IsLocalizedModule.linearMap_ext x₀.asIdeal.primeCompl
        (AlgebraicGeometry.StructureSheaf.toStalkₗ R S.X₂ x₀)
        (AlgebraicGeometry.StructureSheaf.toStalkₗ R S.X₃ x₀)
      ext m
      simp [lg, pg, AlgebraicGeometry.StructureSheaf.toStalkₗ,
        AlgebraicGeometry.tilde.map,
        AlgebraicGeometry.tilde.modulesSpecToSheafIso]
      rw [TopCat.Presheaf.stalkFunctor_map_germ_apply]
      rw [IsLocalizedModule.map_apply] -/
      sorry
    simpa [ST, T', T, pf, lf, pg, lg, hlf, hlg] using hloc -/
  have hST : ST.Exact := by
    apply (TopCat.Sheaf.exact_iff_stalkFunctor_map_exact ST).2
    intro x
    rw [ShortComplex.ab_exact_iff_function_exact]
    have hfun : Function.Exact S.f.hom S.g.hom :=
      (CategoryTheory.ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).mp hS
    let x₀ : PrimeSpectrum.Top R := by
      change PrimeSpectrum R at x
      exact x
    let : x₀.asIdeal.IsPrime := x₀.2
    let pf := ((Sheaf.forget AddCommGrpCat
      (AlgebraicGeometry.Spec (CommRingCat.of R))).map
        ((SheafOfModules.toSheaf
          (R := (AlgebraicGeometry.Spec (CommRingCat.of R)).ringCatSheaf)).map
          (AlgebraicGeometry.tilde.map S.f)))
    let lf : (↑(TopCat.Presheaf.stalk
        (AlgebraicGeometry.moduleStructurePresheaf R (S.X₁ : ModuleCat (CommRingCat.of R))).presheaf x₀)) →ₗ[R]
        (↑(TopCat.Presheaf.stalk
          (AlgebraicGeometry.moduleStructurePresheaf R (S.X₂ : ModuleCat (CommRingCat.of R))).presheaf x₀)) :=
      { toFun := ConcreteCategory.hom
          ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x₀).map pf)
        map_add' := by intros; exact map_add _ _ _
        map_smul' := by
          intros r z
          obtain ⟨U, hxU, s, rfl⟩ :=
            TopCat.Presheaf.exists_germ_eq
              (AlgebraicGeometry.moduleStructurePresheaf R S.X₁).presheaf z
          let s' : (AlgebraicGeometry.structureSheafInType R S.X₁).obj.obj (op U) := s
          change (ConcreteCategory.hom
              ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x₀).map pf))
              (AlgebraicGeometry.StructureSheaf.toStalk R x₀ r •
                (ConcreteCategory.hom (TopCat.Presheaf.germ
                  (AlgebraicGeometry.moduleStructurePresheaf R S.X₁).presheaf U x₀ hxU)) s') = _
          have hscalar :
              AlgebraicGeometry.StructureSheaf.toStalk R x₀ r •
                  (ConcreteCategory.hom (TopCat.Presheaf.germ
                    (AlgebraicGeometry.moduleStructurePresheaf R S.X₁).presheaf U x₀ hxU)) s' =
                (ConcreteCategory.hom ((AlgebraicGeometry.structurePresheafInCommRingCat R).germ
                  U x₀ hxU))
                    ((algebraMap R ((AlgebraicGeometry.structureSheafInType R R).obj.obj (op U))) r) •
                  (ConcreteCategory.hom (TopCat.Presheaf.germ
                    (AlgebraicGeometry.moduleStructurePresheaf R S.X₁).presheaf U x₀ hxU)) s' := by
            congr 1
            exact (AlgebraicGeometry.StructureSheaf.algebraMap_germ_apply U x₀ hxU r).symm
          rw [hscalar]
          have hgerm := (AlgebraicGeometry.moduleStructurePresheaf R
            (S.X₁ : ModuleCat (CommRingCat.of R))).germ_smul
            x₀ U hxU
            ((algebraMap R ((AlgebraicGeometry.structureSheafInType R R).obj.obj (op U))) r) s'
          rw [← hgerm]
          have hstalk :
              (ConcreteCategory.hom
                ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x₀).map pf))
                  ((ConcreteCategory.hom (TopCat.Presheaf.germ
                    (AlgebraicGeometry.moduleStructurePresheaf R S.X₁).presheaf U x₀ hxU))
                    (((algebraMap R ((AlgebraicGeometry.structureSheafInType R R).obj.obj (op U))) r) • s')) =
                (ConcreteCategory.hom (TopCat.Presheaf.germ
                  (AlgebraicGeometry.moduleStructurePresheaf R S.X₂).presheaf U x₀ hxU))
                  ((ConcreteCategory.hom (pf.app (op U)))
                    (((algebraMap R ((AlgebraicGeometry.structureSheafInType R R).obj.obj (op U))) r) • s')) := by
            convert TopCat.Presheaf.stalkFunctor_map_germ_apply U x₀ hxU pf
              (((algebraMap R ((AlgebraicGeometry.structureSheafInType R R).obj.obj (op U))) r) • s') using 1 <;> rfl
          have hstalk₀ :
              (ConcreteCategory.hom
                ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x₀).map pf))
                  ((ConcreteCategory.hom (TopCat.Presheaf.germ
                    (AlgebraicGeometry.moduleStructurePresheaf R S.X₁).presheaf U x₀ hxU)) s') =
                (ConcreteCategory.hom (TopCat.Presheaf.germ
                  (AlgebraicGeometry.moduleStructurePresheaf R S.X₂).presheaf U x₀ hxU))
                  ((ConcreteCategory.hom (pf.app (op U))) s') := by
            convert TopCat.Presheaf.stalkFunctor_map_germ_apply U x₀ hxU pf s' using 1 <;> rfl
          apply hstalk.trans
          let t' : (AlgebraicGeometry.structureSheafInType R S.X₂).obj.obj (op U) :=
            (ConcreteCategory.hom (pf.app (op U))) s'
          have hmap :
              (ConcreteCategory.hom (pf.app (op U)))
                  (((algebraMap R ((AlgebraicGeometry.structureSheafInType R R).obj.obj (op U))) r) • s') =
                ((algebraMap R ((AlgebraicGeometry.structureSheafInType R R).obj.obj (op U))) r) • t' := by
            dsimp [t']
            convert ((AlgebraicGeometry.tilde.map S.f).val.app (op U)).hom.map_smul
              ((algebraMap R ((AlgebraicGeometry.structureSheafInType R R).obj.obj (op U))) r) s' using 1 <;> rfl
          rw [hmap]
          have hgm₂ :
              (ConcreteCategory.hom (TopCat.Presheaf.germ
                (AlgebraicGeometry.moduleStructurePresheaf R S.X₂).presheaf U x₀ hxU))
                  (((algebraMap R ((AlgebraicGeometry.structureSheafInType R R).obj.obj (op U))) r) • t') =
                (ConcreteCategory.hom ((AlgebraicGeometry.structurePresheafInCommRingCat R).germ
                  U x₀ hxU))
                    ((algebraMap R ((AlgebraicGeometry.structureSheafInType R R).obj.obj (op U))) r) •
                  (ConcreteCategory.hom (TopCat.Presheaf.germ
                    (AlgebraicGeometry.moduleStructurePresheaf R S.X₂).presheaf U x₀ hxU)) t' := by
            convert (AlgebraicGeometry.moduleStructurePresheaf R
              (S.X₂ : ModuleCat (CommRingCat.of R))).germ_smul
              x₀ U hxU
              ((algebraMap R ((AlgebraicGeometry.structureSheafInType R R).obj.obj (op U))) r) t' using 1 <;> rfl
          apply hgm₂.trans
          have hsring :
              (ConcreteCategory.hom ((AlgebraicGeometry.structurePresheafInCommRingCat R).germ
                U x₀ hxU))
                  ((algebraMap R ((AlgebraicGeometry.structureSheafInType R R).obj.obj (op U))) r) •
                (ConcreteCategory.hom (TopCat.Presheaf.germ
                  (AlgebraicGeometry.moduleStructurePresheaf R S.X₂).presheaf U x₀ hxU)) t' =
              AlgebraicGeometry.StructureSheaf.toStalk R x₀ r •
                (ConcreteCategory.hom (TopCat.Presheaf.germ
                  (AlgebraicGeometry.moduleStructurePresheaf R S.X₂).presheaf U x₀ hxU)) t' := by
            congr 1
            exact AlgebraicGeometry.StructureSheaf.algebraMap_germ_apply U x₀ hxU r
          rw [hsring]
          have htower :
              AlgebraicGeometry.StructureSheaf.toStalk R x₀ r •
                  (ConcreteCategory.hom (TopCat.Presheaf.germ
                    (AlgebraicGeometry.moduleStructurePresheaf R S.X₂).presheaf U x₀ hxU)) t' =
                (RingHom.id R) r •
                  (ConcreteCategory.hom (TopCat.Presheaf.germ
                    (AlgebraicGeometry.moduleStructurePresheaf R S.X₂).presheaf U x₀ hxU)) t' := by
            convert IsScalarTower.algebraMap_smul
              ((AlgebraicGeometry.structurePresheafInCommRingCat R).stalk x₀) r
              ((ConcreteCategory.hom (TopCat.Presheaf.germ
                (AlgebraicGeometry.moduleStructurePresheaf R S.X₂).presheaf U x₀ hxU)) t') using 1 <;> rfl
          rw [htower]
          exact congrArg (fun q => (RingHom.id R) r • q) hstalk₀.symm
          }
    have hlf : lf =
        IsLocalizedModule.map x₀.asIdeal.primeCompl
          (AlgebraicGeometry.StructureSheaf.toStalkₗ R S.X₁ x₀)
          (AlgebraicGeometry.StructureSheaf.toStalkₗ R S.X₂ x₀) S.f.hom := by
      apply IsLocalizedModule.linearMap_ext x₀.asIdeal.primeCompl
        (AlgebraicGeometry.StructureSheaf.toStalkₗ R S.X₁ x₀)
        (AlgebraicGeometry.StructureSheaf.toStalkₗ R S.X₂ x₀)
      ext m
      change (ConcreteCategory.hom ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x₀).map pf))
          (TopCat.Presheaf.germ
            (AlgebraicGeometry.moduleStructurePresheaf R S.X₁).presheaf ⊤ x₀ (by simp)
              (AlgebraicGeometry.StructureSheaf.toOpenₗ R S.X₁ ⊤ m)) = _
      have hstalk :
          (ConcreteCategory.hom
            ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x₀).map pf))
              ((ConcreteCategory.hom (TopCat.Presheaf.germ
                (AlgebraicGeometry.moduleStructurePresheaf R S.X₁).presheaf ⊤ x₀ (by simp)))
                ((AlgebraicGeometry.StructureSheaf.toOpenₗ R S.X₁ ⊤) m)) =
            (ConcreteCategory.hom (TopCat.Presheaf.germ
              (AlgebraicGeometry.moduleStructurePresheaf R S.X₂).presheaf ⊤ x₀ (by simp)))
              ((ConcreteCategory.hom (pf.app (op ⊤)))
                ((AlgebraicGeometry.StructureSheaf.toOpenₗ R S.X₁ ⊤) m)) := by
        convert TopCat.Presheaf.stalkFunctor_map_germ_apply ⊤ x₀ (by simp) pf
          ((AlgebraicGeometry.StructureSheaf.toOpenₗ R S.X₁ ⊤) m) using 1 <;> rfl
      rw [hstalk]
      rw [LinearMap.comp_apply, IsLocalizedModule.map_apply]
      have htop :
          (ConcreteCategory.hom (pf.app (op ⊤)))
              ((AlgebraicGeometry.StructureSheaf.toOpenₗ R S.X₁ ⊤) m) =
            (AlgebraicGeometry.StructureSheaf.toOpenₗ R S.X₂ ⊤) ((ModuleCat.Hom.hom S.f) m) := by
        have htop' := AlgebraicGeometry.tilde.toOpen_map_app S.f
          (⊤ : Opens (PrimeSpectrum.Top R))
        convert congrArg (fun q => q m) htop' using 1 <;> rfl
      rw [htop]
      rfl
    let pg := ((Sheaf.forget AddCommGrpCat
      (AlgebraicGeometry.Spec (CommRingCat.of R))).map
        ((SheafOfModules.toSheaf
          (R := (AlgebraicGeometry.Spec (CommRingCat.of R)).ringCatSheaf)).map
          (AlgebraicGeometry.tilde.map S.g)))
    let lg : (↑(TopCat.Presheaf.stalk
        (AlgebraicGeometry.moduleStructurePresheaf R (S.X₂ : ModuleCat (CommRingCat.of R))).presheaf x₀)) →ₗ[R]
        (↑(TopCat.Presheaf.stalk
          (AlgebraicGeometry.moduleStructurePresheaf R (S.X₃ : ModuleCat (CommRingCat.of R))).presheaf x₀)) :=
      { toFun := ConcreteCategory.hom
          ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x₀).map pg)
        map_add' := by intros; exact map_add _ _ _
        map_smul' := by
          intros r z
          obtain ⟨U, hxU, s, rfl⟩ :=
            TopCat.Presheaf.exists_germ_eq
              (AlgebraicGeometry.moduleStructurePresheaf R S.X₂).presheaf z
          let s' : (AlgebraicGeometry.structureSheafInType R S.X₂).obj.obj (op U) := s
          change (ConcreteCategory.hom
              ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x₀).map pg))
              (AlgebraicGeometry.StructureSheaf.toStalk R x₀ r •
                (ConcreteCategory.hom (TopCat.Presheaf.germ
                  (AlgebraicGeometry.moduleStructurePresheaf R S.X₂).presheaf U x₀ hxU)) s') = _
          have hscalar :
              AlgebraicGeometry.StructureSheaf.toStalk R x₀ r •
                  (ConcreteCategory.hom (TopCat.Presheaf.germ
                    (AlgebraicGeometry.moduleStructurePresheaf R S.X₂).presheaf U x₀ hxU)) s' =
                (ConcreteCategory.hom ((AlgebraicGeometry.structurePresheafInCommRingCat R).germ
                  U x₀ hxU))
                    ((algebraMap R ((AlgebraicGeometry.structureSheafInType R R).obj.obj (op U))) r) •
                  (ConcreteCategory.hom (TopCat.Presheaf.germ
                    (AlgebraicGeometry.moduleStructurePresheaf R S.X₂).presheaf U x₀ hxU)) s' := by
            congr 1
            exact (AlgebraicGeometry.StructureSheaf.algebraMap_germ_apply U x₀ hxU r).symm
          rw [hscalar]
          have hgerm := (AlgebraicGeometry.moduleStructurePresheaf R
            (S.X₂ : ModuleCat (CommRingCat.of R))).germ_smul
            x₀ U hxU
            ((algebraMap R ((AlgebraicGeometry.structureSheafInType R R).obj.obj (op U))) r) s'
          rw [← hgerm]
          have hstalk :
              (ConcreteCategory.hom
                ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x₀).map pg))
                  ((ConcreteCategory.hom (TopCat.Presheaf.germ
                    (AlgebraicGeometry.moduleStructurePresheaf R S.X₂).presheaf U x₀ hxU))
                    (((algebraMap R ((AlgebraicGeometry.structureSheafInType R R).obj.obj (op U))) r) • s')) =
                (ConcreteCategory.hom (TopCat.Presheaf.germ
                  (AlgebraicGeometry.moduleStructurePresheaf R S.X₃).presheaf U x₀ hxU))
                  ((ConcreteCategory.hom (pg.app (op U)))
                    (((algebraMap R ((AlgebraicGeometry.structureSheafInType R R).obj.obj (op U))) r) • s')) := by
            convert TopCat.Presheaf.stalkFunctor_map_germ_apply U x₀ hxU pg
              (((algebraMap R ((AlgebraicGeometry.structureSheafInType R R).obj.obj (op U))) r) • s') using 1 <;> rfl
          have hstalk₀ :
              (ConcreteCategory.hom
                ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x₀).map pg))
                  ((ConcreteCategory.hom (TopCat.Presheaf.germ
                    (AlgebraicGeometry.moduleStructurePresheaf R S.X₂).presheaf U x₀ hxU)) s') =
                (ConcreteCategory.hom (TopCat.Presheaf.germ
                  (AlgebraicGeometry.moduleStructurePresheaf R S.X₃).presheaf U x₀ hxU))
                  ((ConcreteCategory.hom (pg.app (op U))) s') := by
            convert TopCat.Presheaf.stalkFunctor_map_germ_apply U x₀ hxU pg s' using 1 <;> rfl
          apply hstalk.trans
          let t' : (AlgebraicGeometry.structureSheafInType R S.X₃).obj.obj (op U) :=
            (ConcreteCategory.hom (pg.app (op U))) s'
          have hmap :
              (ConcreteCategory.hom (pg.app (op U)))
                  (((algebraMap R ((AlgebraicGeometry.structureSheafInType R R).obj.obj (op U))) r) • s') =
                ((algebraMap R ((AlgebraicGeometry.structureSheafInType R R).obj.obj (op U))) r) • t' := by
            dsimp [t']
            convert ((AlgebraicGeometry.tilde.map S.g).val.app (op U)).hom.map_smul
              ((algebraMap R ((AlgebraicGeometry.structureSheafInType R R).obj.obj (op U))) r) s' using 1 <;> rfl
          rw [hmap]
          have hgm₃ :
              (ConcreteCategory.hom (TopCat.Presheaf.germ
                (AlgebraicGeometry.moduleStructurePresheaf R S.X₃).presheaf U x₀ hxU))
                  (((algebraMap R ((AlgebraicGeometry.structureSheafInType R R).obj.obj (op U))) r) • t') =
                (ConcreteCategory.hom ((AlgebraicGeometry.structurePresheafInCommRingCat R).germ
                  U x₀ hxU))
                    ((algebraMap R ((AlgebraicGeometry.structureSheafInType R R).obj.obj (op U))) r) •
                  (ConcreteCategory.hom (TopCat.Presheaf.germ
                    (AlgebraicGeometry.moduleStructurePresheaf R S.X₃).presheaf U x₀ hxU)) t' := by
            convert (AlgebraicGeometry.moduleStructurePresheaf R
              (S.X₃ : ModuleCat (CommRingCat.of R))).germ_smul
              x₀ U hxU
              ((algebraMap R ((AlgebraicGeometry.structureSheafInType R R).obj.obj (op U))) r) t' using 1 <;> rfl
          apply hgm₃.trans
          have hsring :
              (ConcreteCategory.hom ((AlgebraicGeometry.structurePresheafInCommRingCat R).germ
                U x₀ hxU))
                  ((algebraMap R ((AlgebraicGeometry.structureSheafInType R R).obj.obj (op U))) r) •
                (ConcreteCategory.hom (TopCat.Presheaf.germ
                  (AlgebraicGeometry.moduleStructurePresheaf R S.X₃).presheaf U x₀ hxU)) t' =
              AlgebraicGeometry.StructureSheaf.toStalk R x₀ r •
                (ConcreteCategory.hom (TopCat.Presheaf.germ
                  (AlgebraicGeometry.moduleStructurePresheaf R S.X₃).presheaf U x₀ hxU)) t' := by
            congr 1
            exact AlgebraicGeometry.StructureSheaf.algebraMap_germ_apply U x₀ hxU r
          rw [hsring]
          have htower :
              AlgebraicGeometry.StructureSheaf.toStalk R x₀ r •
                  (ConcreteCategory.hom (TopCat.Presheaf.germ
                    (AlgebraicGeometry.moduleStructurePresheaf R S.X₃).presheaf U x₀ hxU)) t' =
                (RingHom.id R) r •
                  (ConcreteCategory.hom (TopCat.Presheaf.germ
                    (AlgebraicGeometry.moduleStructurePresheaf R S.X₃).presheaf U x₀ hxU)) t' := by
            convert IsScalarTower.algebraMap_smul
              ((AlgebraicGeometry.structurePresheafInCommRingCat R).stalk x₀) r
              ((ConcreteCategory.hom (TopCat.Presheaf.germ
                (AlgebraicGeometry.moduleStructurePresheaf R S.X₃).presheaf U x₀ hxU)) t') using 1 <;> rfl
          rw [htower]
          exact congrArg (fun q => (RingHom.id R) r • q) hstalk₀.symm
          }
    have hlg : lg =
        IsLocalizedModule.map x₀.asIdeal.primeCompl
          (AlgebraicGeometry.StructureSheaf.toStalkₗ R S.X₂ x₀)
          (AlgebraicGeometry.StructureSheaf.toStalkₗ R S.X₃ x₀) S.g.hom := by
      apply IsLocalizedModule.linearMap_ext x₀.asIdeal.primeCompl
        (AlgebraicGeometry.StructureSheaf.toStalkₗ R S.X₂ x₀)
        (AlgebraicGeometry.StructureSheaf.toStalkₗ R S.X₃ x₀)
      ext m
      change (ConcreteCategory.hom ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x₀).map pg))
          (TopCat.Presheaf.germ
            (AlgebraicGeometry.moduleStructurePresheaf R S.X₂).presheaf ⊤ x₀ (by simp)
              (AlgebraicGeometry.StructureSheaf.toOpenₗ R S.X₂ ⊤ m)) = _
      have hstalk :
          (ConcreteCategory.hom
            ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x₀).map pg))
              ((ConcreteCategory.hom (TopCat.Presheaf.germ
                (AlgebraicGeometry.moduleStructurePresheaf R S.X₂).presheaf ⊤ x₀ (by simp)))
                ((AlgebraicGeometry.StructureSheaf.toOpenₗ R S.X₂ ⊤) m)) =
            (ConcreteCategory.hom (TopCat.Presheaf.germ
              (AlgebraicGeometry.moduleStructurePresheaf R S.X₃).presheaf ⊤ x₀ (by simp)))
              ((ConcreteCategory.hom (pg.app (op ⊤)))
                ((AlgebraicGeometry.StructureSheaf.toOpenₗ R S.X₂ ⊤) m)) := by
        convert TopCat.Presheaf.stalkFunctor_map_germ_apply ⊤ x₀ (by simp) pg
          ((AlgebraicGeometry.StructureSheaf.toOpenₗ R S.X₂ ⊤) m) using 1 <;> rfl
      rw [hstalk]
      rw [LinearMap.comp_apply, IsLocalizedModule.map_apply]
      have htop :
          (ConcreteCategory.hom (pg.app (op ⊤)))
              ((AlgebraicGeometry.StructureSheaf.toOpenₗ R S.X₂ ⊤) m) =
            (AlgebraicGeometry.StructureSheaf.toOpenₗ R S.X₃ ⊤) ((ModuleCat.Hom.hom S.g) m) := by
        have htop' := AlgebraicGeometry.tilde.toOpen_map_app S.g
          (⊤ : Opens (PrimeSpectrum.Top R))
        convert congrArg (fun q => q m) htop' using 1 <;> rfl
      rw [htop]
      rfl
    have hloc := IsLocalizedModule.map_exact x₀.asIdeal.primeCompl
      (AlgebraicGeometry.StructureSheaf.toStalkₗ R S.X₁ x₀)
      (AlgebraicGeometry.StructureSheaf.toStalkₗ R S.X₂ x₀)
      (AlgebraicGeometry.StructureSheaf.toStalkₗ R S.X₃ x₀)
      S.f.hom S.g.hom hfun
    change Function.Exact lf lg
    rw [hlf, hlg]
    exact hloc
  let : T'.Faithful := by
    constructor
    intro X Y f g h
    exact T.map_injective (show T.map f = T.map g from h)
  exact CategoryTheory.Functor.reflects_exact_of_faithful T' _ hST

/-- The standard-open section maps of associated module sheaves are functorial. -/
theorem associatedModule_section_map_natural {R : CommRingCat.{u}}
    {M N : ModuleCat R} (φ : M ⟶ N)
    (U : Opens (PrimeSpectrum.Top R)) :
    AlgebraicGeometry.tilde.toOpen M U ≫
        (AlgebraicGeometry.modulesSpecToSheaf.map
          (AlgebraicGeometry.tilde.map φ)).1.app _ =
      φ ≫ AlgebraicGeometry.tilde.toOpen N U :=
  AlgebraicGeometry.tilde.toOpen_map_app φ U

/-! ## Affine schemes and their morphisms -/

/- The source defines an affine scheme before introducing the later category of
schemes: it is a locally ringed space isomorphic to the spectrum of a ring. -/
def IsAffineScheme
    (X : Formalization.Books.Schemes.Unit02.LocallyRingedSpace.{u}) : Prop :=
  ∃ (R : Type u) (hR : CommRing R),
    Nonempty (X ≅ @affineLocallyRingedSpace R hR)

theorem affineLocallyRingedSpace_isAffineScheme {R : Type u} [CommRing R] :
    IsAffineScheme (affineLocallyRingedSpace R) :=
  ⟨R, inferInstance, ⟨Iso.refl _⟩⟩

/-- Source-facing predicate for being an affine scheme. -/
abbrev affineScheme
    (X : Formalization.Books.Schemes.Unit02.LocallyRingedSpace.{u}) : Prop :=
  IsAffineScheme X

/-- A morphism of locally ringed spaces, hence a morphism of affine schemes. -/
abbrev locallyRingedSpaceMorphism
    (X Y : Formalization.Books.Schemes.Unit02.LocallyRingedSpace.{u}) := X ⟶ Y

/-- A morphism between affine schemes is a morphism of locally ringed spaces. -/
abbrev affineSchemeMorphism
    (X Y : Formalization.Books.Schemes.Unit02.LocallyRingedSpace.{u}) :=
  locallyRingedSpaceMorphism X Y
