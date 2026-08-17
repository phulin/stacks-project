import Formalization.Books.Schemes.Unit02.LocallyRingedSpaces
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.RingTheory.Localization.Module

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
  sorry

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
  sorry

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
  sorry

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
  sorry

theorem standardOpenLocalizationMap_inverse_of_open_eq {R : Type u} [CommRing R]
    (f g : R) (h : standardOpen f = standardOpen g) :
    (standardOpenLocalizationMap g f h.le).comp
          (standardOpenLocalizationMap f g h.ge) =
        RingHom.id (Localization.Away f) ∧
      (standardOpenLocalizationMap f g h.ge).comp
          (standardOpenLocalizationMap g f h.le) =
        RingHom.id (Localization.Away g) := by
  sorry

theorem standardOpenModuleLocalizationMap_inverse_of_open_eq {R M : Type u}
    [CommRing R] [AddCommGroup M] [Module R M] (f g : R)
    (h : standardOpen f = standardOpen g) :
      (standardOpenModuleLocalizationMap g f h.le).comp
          (standardOpenModuleLocalizationMap f g h.ge) =
        (LinearMap.id : LocalizedModule.Away f M →ₗ[R] LocalizedModule.Away f M) ∧
      (standardOpenModuleLocalizationMap f g h.ge).comp
          (standardOpenModuleLocalizationMap g f h.le) =
        (LinearMap.id : LocalizedModule.Away g M →ₗ[R] LocalizedModule.Away g M) := by
  sorry

/-- A finite standard-open refinement of an open cover of `D(f)`. -/
theorem exists_finite_standardOpen_refinement {R : Type u} [CommRing R] (f : R)
    (𝒰 : Set (Opens (spectrumTop R)))
    (h𝒰 : ∀ x : PrimeSpectrum R, x ∈ standardOpen f →
      ∃ U ∈ 𝒰, x ∈ U) :
    ∃ n : ℕ, ∃ g : Fin n → R,
      (⨆ i, standardOpen (g i)) = standardOpen f ∧
        ∀ i, ∃ U ∈ 𝒰, standardOpen (g i) ≤ U := by
  sorry

/-- The unit-ideal criterion for a finite standard-open covering of `D(f)`. -/
theorem standardOpen_cover_iff_unitIdeal {R : Type u} [CommRing R] (f : R)
    (n : ℕ) (g : Fin n → R) :
    standardOpen f ≤ ⨆ i, standardOpen (g i) ↔
      Ideal.span (Set.range (fun i =>
        algebraMap R (Localization.Away f) (g i))) = ⊤ := by
  sorry

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
  sorry

theorem module_standardOpen_restriction_compatibility {R M : Type u} [CommRing R]
    [AddCommGroup M] [Module R M] (f g : R) (h : standardOpen g ≤ standardOpen f) :
    ∀ x : LocalizedModule.Away f M,
      (AlgebraicGeometry.structureSheafInType R M).obj.map (homOfLE h).op
          (moduleLocalizationToStandardOpenSections R M f x) =
        moduleLocalizationToStandardOpenSections R M g
          (standardOpenModuleLocalizationMap f g h x) := by
  sorry

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
  sorry

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
  sorry

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
