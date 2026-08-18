import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Category.ModuleCat.Ext.Finite
import Mathlib.Algebra.Category.ModuleCat.Ext.Basic
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
import Mathlib.Algebra.Homology.Homotopy
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.CategoryTheory.Abelian.Projective.Resolution
import Mathlib.RingTheory.Noetherian.Basic

/-!
# Commutative Algebra, Chapter 71: Ext groups

The chapter's resolutions are represented by Mathlib's projective-resolution
interface.  The source asks for free resolutions, so the source-facing
structures below retain the same canonical resolution together with the
degreewise freeness (and finite generation) hypotheses.
-/

namespace Formalization.Books.Algebra.Unit71

open CategoryTheory
open CategoryTheory.Limits
open scoped ZeroObject

universe u

/-! ## Resolutions -/

/-- Chain complexes of `R`-modules indexed by the nonnegative integers. -/
abbrev ModuleChainComplex (R : Type u) [Ring R] :=
  ChainComplex (ModuleCat.{u} R) ℕ

/-- Cochain complexes of `R`-modules indexed by the nonnegative integers. -/
abbrev ModuleCochainComplex (R : Type u) [Ring R] :=
  CochainComplex (ModuleCat.{u} R) ℕ

/-- A resolution is an exact nonnegative chain complex together with its
augmentation to the module in degree zero. -/
structure Resolution (R : Type u) [Ring R] (M : ModuleCat.{u} R) where
  complex : ModuleChainComplex R
  augmentation : complex.X 0 ⟶ M
  augmentation_condition : complex.d 1 0 ≫ augmentation = 0
  exact_zero :
    (ShortComplex.mk (complex.d 1 0) augmentation augmentation_condition).Exact
  exact_succ : ∀ n,
    (ShortComplex.mk (complex.d (n + 2) (n + 1))
      (complex.d (n + 1) n) (complex.d_comp_d (n + 2) (n + 1) n)).Exact

/-- A resolution whose terms are free modules. -/
structure FreeResolution (R : Type u) [Ring R] (M : ModuleCat.{u} R) where
  resolution : Resolution R M
  free : ∀ n, Module.Free R (resolution.complex.X n)

/-- A resolution whose terms are finite free modules. -/
structure FiniteFreeResolution (R : Type u) [Ring R] (M : ModuleCat.{u} R) where
  resolution : FreeResolution R M
  finite : ∀ n, Module.Finite R (resolution.resolution.complex.X n)

/-- A complex of free modules augmented to a module.

This is the source-facing hypothesis in the comparison lemma: unlike a
`FreeResolution`, the complex itself is not required to be exact. -/
structure FreeAugmentedComplex (R : Type u) [Ring R] (M : ModuleCat.{u} R) where
  complex : ModuleChainComplex R
  augmentation : complex.X 0 ⟶ M
  augmentation_condition : complex.d 1 0 ≫ augmentation = 0
  free : ∀ n, Module.Free R (complex.X n)

/-- A projective resolution supplies the preceding source-facing resolution
data. -/
noncomputable def projectiveResolutionToResolution {R : Type u} [Ring R]
    {M : ModuleCat.{u} R} (P : CategoryTheory.ProjectiveResolution M) :
    Resolution R M where
  complex := P.complex
  augmentation := P.π.f 0
  augmentation_condition := P.complex_d_comp_π_f_zero
  exact_zero := by simpa using P.exact₀
  exact_succ := fun n => by simpa using P.exact_succ n

/-- The complex underlying a free resolution. -/
abbrev FreeResolution.complex {R : Type u} [Ring R] {M : ModuleCat.{u} R}
    (F : FreeResolution R M) : ModuleChainComplex R :=
  F.resolution.complex

/-- The complex underlying a finite-free resolution. -/
abbrev FiniteFreeResolution.complex {R : Type u} [Ring R] {M : ModuleCat.{u} R}
    (F : FiniteFreeResolution R M) : ModuleChainComplex R :=
  F.resolution.resolution.complex

/-- Exactness at the augmentation term of a resolution. -/
theorem resolution_exact_zero {R : Type u} [Ring R] {M : ModuleCat.{u} R}
    (F : Resolution R M) :
    (ShortComplex.mk (F.complex.d 1 0) F.augmentation
      F.augmentation_condition).Exact :=
  F.exact_zero

/-- Exactness at every positive term of a resolution. -/
theorem resolution_exact_succ {R : Type u} [Ring R] {M : ModuleCat.{u} R}
    (F : Resolution R M) (n : ℕ) :
    (ShortComplex.mk (F.complex.d (n + 2) (n + 1))
      (F.complex.d (n + 1) n) (F.complex.d_comp_d (n + 2) (n + 1) n)).Exact :=
  F.exact_succ n

/-- Every module admits a free resolution. -/
theorem exists_free_resolution {R : Type u} [Ring R] (M : ModuleCat.{u} R) :
    Nonempty (FreeResolution R M) := by
  sorry

/-- Noetherian finite modules admit finite-free resolutions. -/
theorem exists_finite_free_resolution {R : Type u} [Ring R]
    [IsNoetherianRing R] (M : ModuleCat.{u} R) [Module.Finite R M] :
    Nonempty (FiniteFreeResolution R M) := by
  sorry

/-- A comparison map from a free augmented complex to a resolution. -/
structure FreeAugmentedComplexMap {R : Type u} [Ring R]
    {M N : ModuleCat.{u} R} (F : FreeAugmentedComplex R M) (G : Resolution R N)
    (φ : M ⟶ N) where
  hom : F.complex ⟶ G.complex
  hom_f_zero_comp_augmentation : hom.f 0 ≫ G.augmentation = F.augmentation ≫ φ

/-- An augmented complex of free modules admits a comparison map to any
resolution. -/
theorem free_augmented_complex_map_exists {R : Type u} [Ring R]
    {M N : ModuleCat.{u} R} (F : FreeAugmentedComplex R M) (G : Resolution R N)
    (φ : M ⟶ N) :
    Nonempty (FreeAugmentedComplexMap F G φ) := by
  sorry

/- A map of resolutions is a map of complexes compatible with the augmentation. -/
structure ResolutionMap {R : Type u} [Ring R] {M N : ModuleCat.{u} R}
    (F : Resolution R M) (G : Resolution R N) (φ : M ⟶ N) where
  hom : F.complex ⟶ G.complex
  hom_f_zero_comp_augmentation : hom.f 0 ≫ G.augmentation = F.augmentation ≫ φ

/-- The comparison map interface is also compatible with Mathlib's canonical
projective-resolution lift. -/
noncomputable def canonicalResolutionMap {R : Type u} [Ring R]
    {M N : ModuleCat.{u} R} (P : CategoryTheory.ProjectiveResolution M)
    (Q : CategoryTheory.ProjectiveResolution N) (φ : M ⟶ N) :
    ResolutionMap (projectiveResolutionToResolution P)
      (projectiveResolutionToResolution Q) φ where
  hom := CategoryTheory.ProjectiveResolution.lift φ P Q
  hom_f_zero_comp_augmentation := by
    simpa [projectiveResolutionToResolution] using
      CategoryTheory.ProjectiveResolution.lift_commutes_zero φ P Q

/-- A free resolution admits a comparison map to any resolution. -/
theorem resolution_map_exists {R : Type u} [Ring R] {M N : ModuleCat.{u} R}
    (F : FreeResolution R M) (G : Resolution R N) (φ : M ⟶ N) :
    Nonempty (ResolutionMap F.resolution G φ) := by
  let FF : FreeAugmentedComplex R M :=
    { complex := F.complex, augmentation := F.resolution.augmentation,
      augmentation_condition := F.resolution.augmentation_condition, free := F.free }
  rcases free_augmented_complex_map_exists FF G φ with ⟨h⟩
  exact ⟨⟨h.hom, h.hom_f_zero_comp_augmentation⟩⟩

/-! ## Homology, cohomology, maps, and homotopies -/

/-- The differential `F_{i+1} → F_i` of a chain complex. -/
abbrev chainDifferential {R : Type u} [Ring R] (F : ModuleChainComplex R) (i : ℕ) :
    F.X (i + 1) ⟶ F.X i :=
  F.d (i + 1) i

/-- The differential `F^i → F^{i+1}` of a cochain complex. -/
abbrev cochainDifferential {R : Type u} [Ring R] (F : ModuleCochainComplex R) (i : ℕ) :
    F.X i ⟶ F.X (i + 1) :=
  F.d i (i + 1)

/-- Homology of a chain complex, using the canonical kernel/cokernel homology API. -/
noncomputable def chainHomology {R : Type u} [Ring R] (F : ModuleChainComplex R) (i : ℕ) :
    ModuleCat.{u} R :=
  HomologicalComplex.homology F i

/-- Cohomology of a cochain complex, using the canonical kernel/cokernel homology API. -/
noncomputable def cochainCohomology {R : Type u} [Ring R] (F : ModuleCochainComplex R) (i : ℕ) :
    ModuleCat.{u} R :=
  HomologicalComplex.homology F i

/-- The explicit kernel/image quotient presentation of chain homology. -/
noncomputable def chainHomologyQuotientIso {R : Type u} [Ring R]
    (F : ModuleChainComplex R) (i : ℕ) :
    chainHomology F i ≅ (F.sc i).moduleCatLeftHomologyData.H :=
  (F.sc i).moduleCatHomologyIso

/-- The explicit kernel/image quotient presentation of cohomology. -/
noncomputable def cochainCohomologyQuotientIso {R : Type u} [Ring R]
    (F : ModuleCochainComplex R) (i : ℕ) :
    cochainCohomology F i ≅ (F.sc i).moduleCatLeftHomologyData.H :=
  (F.sc i).moduleCatHomologyIso

/-- The map induced on chain homology by a map of complexes. -/
noncomputable def chainHomologyMap {R : Type u} [Ring R]
    {F G : ModuleChainComplex R} (α : F ⟶ G) (i : ℕ) :
    chainHomology F i ⟶ chainHomology G i :=
  HomologicalComplex.homologyMap α i

/-- The map induced on cohomology by a map of cochain complexes. -/
noncomputable def cochainCohomologyMap {R : Type u} [Ring R]
    {F G : ModuleCochainComplex R} (α : F ⟶ G) (i : ℕ) :
    cochainCohomology F i ⟶ cochainCohomology G i :=
  HomologicalComplex.homologyMap α i

/-- Homotopy of chain maps, in Mathlib's shape-aware formulation. -/
def ChainHomotopic {R : Type u} [Ring R] {F G : ModuleChainComplex R}
    (α β : F ⟶ G) : Prop :=
  Nonempty (Homotopy α β)

/-- Homotopy of cochain maps, in Mathlib's shape-aware formulation. -/
def CochainHomotopic {R : Type u} [Ring R] {F G : ModuleCochainComplex R}
    (α β : F ⟶ G) : Prop :=
  Nonempty (Homotopy α β)

/-- Homotopy of additive-group-valued cochain maps. -/
def AdditiveCochainHomotopic
    {F G : CochainComplex (AddCommGrpCat.{u}) ℕ} (α β : F ⟶ G) : Prop :=
  Nonempty (Homotopy α β)

/-- Any two comparison maps from an augmented free complex to a resolution
are homotopic. -/
theorem free_augmented_complex_maps_homotopic {R : Type u} [Ring R]
    {M N : ModuleCat.{u} R} (F : FreeAugmentedComplex R M) (G : Resolution R N)
    (φ : M ⟶ N) (α β : FreeAugmentedComplexMap F G φ) :
    ChainHomotopic α.hom β.hom := by
  sorry

theorem chain_homotopic_maps_equal_on_homology {R : Type u} [Ring R]
    {F G : ModuleChainComplex R} {α β : F ⟶ G} (h : ChainHomotopic α β) (i : ℕ) :
    chainHomologyMap α i = chainHomologyMap β i := by
  rcases h with ⟨h⟩
  exact h.homologyMap_eq i

theorem cochain_homotopic_maps_equal_on_cohomology {R : Type u} [Ring R]
    {F G : ModuleCochainComplex R} {α β : F ⟶ G} (h : CochainHomotopic α β) (i : ℕ) :
    cochainCohomologyMap α i = cochainCohomologyMap β i := by
  rcases h with ⟨h⟩
  exact h.homologyMap_eq i

/-! ## The Hom complex attached to a resolution -/

/-- Precomposition on the additive groups of module homomorphisms. -/
def homPrecompAddMonoidHom {R : Type u} [Ring R]
    {A B N : ModuleCat.{u} R} (f : B ⟶ A) :
    (A ⟶ N) →+ (B ⟶ N) where
  toFun g := f ≫ g
  map_zero' := by simp
  map_add' g h := by simp

/-- The differential in `Hom_R(F_•,N)`, with the source's cohomological indexing. -/
noncomputable def resolutionHomDifferential {R : Type u} [Ring R]
    (F : ModuleChainComplex R) (N : ModuleCat.{u} R) (i j : ℕ) :
    AddCommGrpCat.of (F.X i ⟶ N) ⟶ AddCommGrpCat.of (F.X j ⟶ N) :=
  if i + 1 = j then
    AddCommGrpCat.ofHom (homPrecompAddMonoidHom (F.d j i))
  else 0

/-- The cochain complex `Hom_R(F_•,N)`. -/
noncomputable def resolutionHomComplex {R : Type u} [Ring R]
    (F : ModuleChainComplex R) (N : ModuleCat.{u} R) :
    CochainComplex (AddCommGrpCat.{u}) ℕ where
  X i := AddCommGrpCat.of (F.X i ⟶ N)
  d i j := resolutionHomDifferential F N i j
  shape i j hij := by
    classical
    dsimp [resolutionHomDifferential]
    split_ifs with h
    · exact (hij h).elim
    · rfl
  d_comp_d' i j k hij hjk := by
    classical
    have hij' : i + 1 = j := by
      simpa only [ComplexShape.up_Rel] using hij
    have hjk' : j + 1 = k := by
      simpa only [ComplexShape.up_Rel] using hjk
    dsimp [resolutionHomDifferential]
    rw [if_pos hij', if_pos hjk']
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro g
    change F.d k j ≫ (F.d j i ≫ g) = 0
    simp

/-- A map of resolutions induces the contravariant map of Hom complexes. -/
noncomputable def resolutionHomMap {R : Type u} [Ring R]
    {F G : ModuleChainComplex R} (α : F ⟶ G) (N : ModuleCat.{u} R) :
    resolutionHomComplex G N ⟶ resolutionHomComplex F N where
  f i := AddCommGrpCat.ofHom (homPrecompAddMonoidHom (α.f i))
  comm' i j hij := by
    classical
    have hij' : i + 1 = j := by
      simpa only [ComplexShape.up_Rel] using hij
    dsimp [resolutionHomComplex, resolutionHomDifferential]
    rw [if_pos hij']
    rw [if_pos hij']
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro g
    change F.d j i ≫ (α.f i ≫ g) = α.f j ≫ (G.d j i ≫ g)
    rw [← Category.assoc, ← Category.assoc, ← α.comm j i]

/-- Cohomology of an additive-group-valued cochain complex. -/
noncomputable def additiveCochainCohomology
    (F : CochainComplex (AddCommGrpCat.{u}) ℕ) (i : ℕ) : AddCommGrpCat.{u} :=
  HomologicalComplex.homology F i

/-- The map induced on additive cohomology by a map of cochain complexes. -/
noncomputable def additiveCochainCohomologyMap
    {F G : CochainComplex (AddCommGrpCat.{u}) ℕ} (α : F ⟶ G) (i : ℕ) :
    additiveCochainCohomology F i ⟶ additiveCochainCohomology G i :=
  HomologicalComplex.homologyMap α i

theorem additive_cochain_homotopic_maps_equal_on_cohomology
    {F G : CochainComplex (AddCommGrpCat.{u}) ℕ} {α β : F ⟶ G}
    (h : AdditiveCochainHomotopic α β) (i : ℕ) :
    additiveCochainCohomologyMap α i = additiveCochainCohomologyMap β i := by
  rcases h with ⟨h⟩
  exact h.homologyMap_eq i

/-- The induced map on the cohomology of the Hom complex. -/
noncomputable def resolutionHomCohomologyMap {R : Type u} [Ring R]
    {F G : ModuleChainComplex R} (α : F ⟶ G) (N : ModuleCat.{u} R) (i : ℕ) :
    additiveCochainCohomology (resolutionHomComplex G N) i ⟶
      additiveCochainCohomology (resolutionHomComplex F N) i :=
  additiveCochainCohomologyMap (resolutionHomMap α N) i

/-! ## Resolution Ext and its independence of choices -/

/-- The `i`th cohomology group of `Hom_R(F_•,N)`. -/
noncomputable def ResolutionExt {R : Type u} [Ring R]
    {M : ModuleCat.{u} R} (F : FreeResolution R M) (N : ModuleCat.{u} R) (i : ℕ) :
    AddCommGrpCat.{u} :=
  additiveCochainCohomology (resolutionHomComplex F.complex N) i

/-- The resolution-based Ext group, extended by zero to negative degrees. -/
noncomputable def ResolutionExtZ {R : Type u} [Ring R]
    {M : ModuleCat.{u} R} (F : FreeResolution R M) (N : ModuleCat.{u} R) (i : ℤ) :
    AddCommGrpCat.{u} :=
  if 0 ≤ i then AddCommGrpCat.of (ResolutionExt F N i.toNat) else 0

/-- The canonical Ext group in the module category. -/
abbrev ExtGroup {R : Type u} [Ring R]
    (M N : ModuleCat.{u} R) (i : ℕ) : Type u :=
  CategoryTheory.Abelian.Ext M N i

/-- The canonical Ext module over a commutative ring. -/
noncomputable def ExtModule {R : Type u} [CommRing R]
    (M N : ModuleCat.{u} R) (i : ℕ) : ModuleCat.{u} R :=
  ModuleCat.of R (ExtGroup M N i)

/-- The canonical Ext value, extended by zero to negative degrees. -/
noncomputable def ExtModuleZ {R : Type u} [CommRing R]
    (M N : ModuleCat.{u} R) (i : ℤ) : ModuleCat.{u} R :=
  if 0 ≤ i then ExtModule M N i.toNat else 0

theorem resolution_ext_negative {R : Type u} [Ring R]
    {M : ModuleCat.{u} R} (F : FreeResolution R M) (N : ModuleCat.{u} R)
    {i : ℤ} (hi : i < 0) : ResolutionExtZ F N i = 0 := by
  simp [ResolutionExtZ, not_le_of_gt hi]

theorem ext_module_negative {R : Type u} [CommRing R]
    (M N : ModuleCat.{u} R) {i : ℤ} (hi : i < 0) : ExtModuleZ M N i = 0 := by
  simp [ExtModuleZ, not_le_of_gt hi]

/-- A chosen free-resolution computation is additively equivalent to the
derived-category Ext group. The `Nonempty` wrapper records existence without
choosing a comparison equivalence. -/
theorem resolution_ext_represents_ext {R : Type u} [Ring R]
    {M N : ModuleCat.{u} R} (F : FreeResolution R M) (i : ℕ) :
    Nonempty (ResolutionExt F N i ≃+ ExtGroup M N i) := by
  sorry

/-- Degree zero Ext is the module-hom group. -/
noncomputable def extZeroLinearEquiv {R : Type u} [CommRing R]
    (M N : ModuleCat.{u} R) : ExtGroup M N 0 ≃ₗ[R] (M ⟶ N) :=
  CategoryTheory.Abelian.Ext.linearEquiv₀

/-- The degree-zero group computed from a free resolution is the Hom group. -/
theorem resolution_ext_zero_equiv_hom {R : Type u} [CommRing R]
    {M : ModuleCat.{u} R} (F : FreeResolution R M) (N : ModuleCat.{u} R) :
    Nonempty (ResolutionExt F N 0 ≃+ (M ⟶ N)) := by
  rcases resolution_ext_represents_ext F 0 with ⟨e⟩
  exact ⟨e.trans (extZeroLinearEquiv M N).toAddEquiv⟩

/-- Two comparison maps induce homotopic maps on the Hom complexes. -/
theorem resolution_maps_homotopic {R : Type u} [Ring R]
    {M₁ M₂ : ModuleCat.{u} R} (F : FreeResolution R M₁)
    (G : Resolution R M₂) (φ : M₁ ⟶ M₂) (α β : ResolutionMap F.resolution G φ) :
    ChainHomotopic α.hom β.hom := by
  exact free_augmented_complex_maps_homotopic
    { complex := F.complex, augmentation := F.resolution.augmentation,
      augmentation_condition := F.resolution.augmentation_condition, free := F.free }
    G φ ⟨α.hom, α.hom_f_zero_comp_augmentation⟩
      ⟨β.hom, β.hom_f_zero_comp_augmentation⟩

/-- Two comparison maps induce homotopic maps on the Hom complexes. -/
theorem resolution_hom_maps_homotopic {R : Type u} [Ring R]
    {M₁ M₂ : ModuleCat.{u} R} (F : FreeResolution R M₁)
    (G : Resolution R M₂) (φ : M₁ ⟶ M₂) (α β : ResolutionMap F.resolution G φ)
    (N : ModuleCat.{u} R) :
    AdditiveCochainHomotopic (resolutionHomMap α.hom N) (resolutionHomMap β.hom N) := by
  sorry

/-- The induced map on `H^i(Hom_R(-,N))` is independent of the comparison map.

The direction is contravariant: a comparison `F_• ⟶ G_•` induces a map from
`H^i(Hom_R(G_•,N))` to `H^i(Hom_R(F_•,N))`. -/
theorem resolution_ext_map_independent {R : Type u} [Ring R]
    {M₁ M₂ : ModuleCat.{u} R} (F : FreeResolution R M₁)
    (G : FreeResolution R M₂) (φ : M₁ ⟶ M₂)
    (α β : ResolutionMap F.resolution G.resolution φ) (N : ModuleCat.{u} R) (i : ℕ) :
    resolutionHomCohomologyMap α.hom N i = resolutionHomCohomologyMap β.hom N i := by
  exact additive_cochain_homotopic_maps_equal_on_cohomology
    (resolution_hom_maps_homotopic F G.resolution φ α β N) i

/-- An isomorphism of modules induces an isomorphism on the resolution Ext groups. -/
theorem isIso_resolution_ext_map_of_isIso {R : Type u} [Ring R]
    {M₁ M₂ : ModuleCat.{u} R} (F : FreeResolution R M₁)
    (G : FreeResolution R M₂) (φ : M₁ ⟶ M₂) [IsIso φ]
    (α : ResolutionMap F.resolution G.resolution φ) (N : ModuleCat.{u} R) (i : ℕ) :
    IsIso (resolutionHomCohomologyMap α.hom N i) := by
  sorry

/-- A comparison map lifting the identity between one resolution and itself
induces an isomorphism on the computed Ext groups. -/
theorem isIso_resolution_ext_identity_map {R : Type u} [Ring R]
    {M : ModuleCat.{u} R} (F : FreeResolution R M)
    (α : ResolutionMap F.resolution F.resolution (𝟙 M))
    (N : ModuleCat.{u} R) (i : ℕ) :
    IsIso (resolutionHomCohomologyMap α.hom N i) := by
  sorry

/-! ## Long exact sequences -/

/-- The five-arrow segment of the covariant long exact Ext sequence. -/
noncomputable def extCovariantSequence {R : Type u} [Ring R]
    (S : ShortComplex (ModuleCat.{u} R)) (hS : S.ShortExact)
    (M : ModuleCat.{u} R) (i : ℕ) :
    ComposableArrows (AddCommGrpCat.{u}) 5 :=
  CategoryTheory.Abelian.Ext.covariantSequence M hS i (i + 1) rfl

/-- Exactness of every five-arrow segment in the covariant long exact sequence. -/
theorem extCovariantSequence_exact {R : Type u} [Ring R]
    (S : ShortComplex (ModuleCat.{u} R)) (hS : S.ShortExact)
    (M : ModuleCat.{u} R) (i : ℕ) :
    (extCovariantSequence S hS M i).Exact := by
  simpa [extCovariantSequence] using
    (CategoryTheory.Abelian.Ext.covariantSequence_exact M hS i (i + 1) rfl)

/-- The initial map into `Ext⁰` is injective when the first map is mono. -/
theorem ext_covariant_initial_injective {R : Type u} [Ring R]
    (S : ShortComplex (ModuleCat.{u} R)) (hS : S.ShortExact)
    (M : ModuleCat.{u} R) :
    Function.Injective
      ((CategoryTheory.Abelian.Ext.mk₀ S.f).postcomp M (Nat.add_zero 0)) := by
  exact CategoryTheory.Abelian.Ext.postcomp_mk₀_injective_of_mono
    (hf := hS.mono_f) M S.f

/-- The five-arrow segment of the contravariant long exact Ext sequence. -/
noncomputable def extContravariantSequence {R : Type u} [Ring R]
    (S : ShortComplex (ModuleCat.{u} R)) (hS : S.ShortExact)
    (N : ModuleCat.{u} R) (i : ℕ) :
    ComposableArrows (AddCommGrpCat.{u}) 5 :=
  CategoryTheory.Abelian.Ext.contravariantSequence hS N i (i + 1)
    (by simp [Nat.add_comm])

/-- Exactness of every five-arrow segment in the contravariant long exact sequence. -/
theorem extContravariantSequence_exact {R : Type u} [Ring R]
    (S : ShortComplex (ModuleCat.{u} R)) (hS : S.ShortExact)
    (N : ModuleCat.{u} R) (i : ℕ) :
    (extContravariantSequence S hS N i).Exact := by
  simpa [extContravariantSequence] using
    (CategoryTheory.Abelian.Ext.contravariantSequence_exact hS N i (i + 1)
      (by simp [Nat.add_comm]))

/-- The initial map into the contravariant `Ext⁰` sequence is injective when
the second map of the short exact sequence is epi. -/
theorem ext_contravariant_initial_injective {R : Type u} [Ring R]
    (S : ShortComplex (ModuleCat.{u} R)) (hS : S.ShortExact)
    (N : ModuleCat.{u} R) :
    Function.Injective
      ((CategoryTheory.Abelian.Ext.mk₀ S.g).precomp N (Nat.zero_add 0)) := by
  exact CategoryTheory.Abelian.Ext.precomp_mk₀_injective_of_epi
    (hg := hS.epi_g) N S.g

/-! ## Annihilation and Noetherian finiteness -/

/-- If `r` belongs to the annihilator of `N`, scalar multiplication by `r`
vanishes on every Ext group. -/
theorem ext_smul_eq_zero_of_annihilates_right {R : Type u} [CommRing R]
    (r : R) (M N : ModuleCat.{u} R) (hN : r ∈ Module.annihilator R N) (i : ℕ) :
    ∀ e : ExtGroup M N i, r • e = 0 := by
  sorry

/-- If `r` belongs to the annihilator of `M`, scalar multiplication by `r`
vanishes on every Ext group. -/
theorem ext_smul_eq_zero_of_annihilates_left {R : Type u} [CommRing R]
    (r : R) (M N : ModuleCat.{u} R) (hM : r ∈ Module.annihilator R M) (i : ℕ) :
    ∀ e : ExtGroup M N i, r • e = 0 := by
  intro e
  have hz := CategoryTheory.Abelian.Ext.postcomp_smul_id_eq_zero_of_mem_annihilator
    (R := R) (M := N) (N := M) (r := r) (mem_ann := hM) i
  have hz' := congrArg (fun f => f e) hz
  rw [CategoryTheory.Abelian.Ext.mk₀_smul (C := ModuleCat R) (X := N) (Y := N) r (𝟙 N)] at hz'
  simpa [CategoryTheory.Abelian.Ext.postcomp, CategoryTheory.Abelian.Ext.comp_smul] using hz'

/-- Ext between finite modules over a Noetherian ring is finite. -/
theorem ext_finite_of_noetherian {R : Type u} [CommRing R]
    [IsNoetherianRing R] (M N : ModuleCat.{u} R)
    [Module.Finite R M] [Module.Finite R N] (i : ℕ) :
    Module.Finite R (ExtGroup M N i) := by
  infer_instance

end Formalization.Books.Algebra.Unit71
