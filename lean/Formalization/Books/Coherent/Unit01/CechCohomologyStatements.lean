import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.Algebra.Category.Grp.CartesianMonoidal
import Mathlib.Algebra.Category.ModuleCat.Localization
import Mathlib.RingTheory.LocalProperties.Exactness
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
import Mathlib.Algebra.Homology.ShortComplex.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import Mathlib.AlgebraicGeometry.Cover.Open
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.CategoryTheory.Abelian.RightDerived
import Mathlib.CategoryTheory.Functor.ReflectsIso.Exact
import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech
import Formalization.Books.Algebra.Unit24.GlueingFunctions

/-!
# Cohomology of Schemes, Chapter 1: Čech cohomology

This file records the definitions and theorem interfaces in the second source
section of the introduction.  The proof of the results is intentionally left
for the prove stage.
-/

noncomputable section

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry
open SheafOfModules
open scoped AlgebraicGeometry

namespace Formalization.Books.Coherent.Unit01

/-! ### Standard affine-open coverings -/

/-- A finite standard-open covering of an affine scheme. -/
structure StandardOpenCover (Y : Scheme.{u}) (hY : IsAffine Y) where
  /-- The number of basic opens in the covering. -/
  n : ℕ
  /-- The functions defining the basic opens. -/
  function : Fin n → Γ(Y, ⊤)
  /-- The functions generate the unit ideal. -/
  span_eq_top : Ideal.span (Set.range function) = ⊤

/-- The basic open in a standard covering corresponding to an index. -/
def StandardOpenCover.basicOpen {Y : Scheme.{u}} {hY : IsAffine Y}
    (𝒰 : StandardOpenCover Y hY) (i : Fin 𝒰.n) : Y.Opens :=
  Y.basicOpen (𝒰.function i)

/-- The same family of basic opens with its index lifted to the universe used
by the Čech complex. -/
def StandardOpenCover.basicOpenFamily {Y : Scheme.{u}} {hY : IsAffine Y}
    (𝒰 : StandardOpenCover Y hY) : ULift.{u} (Fin 𝒰.n) → Y.Opens :=
  fun i => 𝒰.basicOpen i.down

/-- A standard covering of an affine open subscheme of a scheme. -/
structure StandardOpenCoverOfAffineOpen (X : Scheme.{u}) where
  /-- The affine open being covered. -/
  U : X.Opens
  /-- Affineness of the open subscheme. -/
  isAffine : IsAffineOpen U
  /-- The chosen standard covering after restricting to the open subscheme. -/
  cover : StandardOpenCover (U : Scheme) isAffine

/-- The basic opens of a standard covering cover the affine scheme. -/
theorem StandardOpenCover.iSup_basicOpen {Y : Scheme.{u}} {hY : IsAffine Y}
    (𝒰 : StandardOpenCover Y hY) :
    ⨆ i, 𝒰.basicOpen i = ⊤ := by
  change (⨆ i, Y.basicOpen (𝒰.function i)) = ⊤
  rw [← iSup_range]
  exact iSup_basicOpen_of_span_eq_top (⊤ : Y.Opens) (Set.range 𝒰.function) 𝒰.span_eq_top

/-! ### Sheaf and Čech cohomology objects -/

/-- Cohomology of a sheaf of modules, as an object of `AddCommGrpCat`. -/
noncomputable def schemeCohomologyObject {Y : Scheme.{u}} (M : Y.Modules) (n : ℕ)
    [hY : CategoryTheory.HasExt.{u} Y.Modules] : AddCommGrpCat.{u} :=
  (@CategoryTheory.Abelian.extFunctorObj.{u, u, u + 1} Y.Modules _ _ hY
    (SheafOfModules.unit Y.ringCatSheaf) n).obj M

/-- Cohomology of a sheaf of modules on an open subscheme. -/
noncomputable def schemeCohomologyOn {X : Scheme.{u}} (M : X.Modules)
    (U : X.Opens) (n : ℕ) [CategoryTheory.HasExt.{u} (U : Scheme).Modules] :
  AddCommGrpCat.{u} :=
  schemeCohomologyObject (M.restrict U.ι) n

/-- The additive group of global sections used to augment a Čech complex. -/
noncomputable def globalSectionsObject {Y : Scheme.{u}} (M : Y.Modules) :
    AddCommGrpCat.{u} :=
  M.presheaf.obj (Opposite.op (⊤ : Y.Opens))

/-- The Čech complex of a presheaf of abelian groups for a family of opens. -/
noncomputable def cechComplex {Y : Scheme.{u}} {ι : Type u} (M : Y.Modules)
    (U : ι → Y.Opens) : CochainComplex AddCommGrpCat.{u} ℕ :=
  (CategoryTheory.cechComplexFunctor U).obj M.presheaf

/-- The `n`th Čech cohomology object of a sheaf of modules. -/
noncomputable def cechCohomologyObject {Y : Scheme.{u}} {ι : Type u}
    (M : Y.Modules) (U : ι → Y.Opens) (n : ℕ) : AddCommGrpCat.{u} :=
  (HomologicalComplex.homologyFunctor AddCommGrpCat (ComplexShape.up ℕ) n).obj
    (cechComplex M U)

/-- Vanishing of all positive Čech cohomology objects. -/
def PositiveCechExactness {Y : Scheme.{u}} {ι : Type u} (M : Y.Modules)
    (U : ι → Y.Opens) : Prop :=
  ∀ n : ℕ, 0 < n → IsZero (cechCohomologyObject M U n)

/-- The canonical map from global sections to the degree-zero Čech terms. -/
noncomputable def cechAugmentation {Y : Scheme.{u}} {ι : Type u} (M : Y.Modules)
    (U : ι → Y.Opens) : globalSectionsObject M ⟶ (cechComplex M U).X 0 := by
  simpa [globalSectionsObject, cechComplex, CategoryTheory.cechComplexFunctor,
    CategoryTheory.Limits.FormalCoproduct.cochainComplexFunctor,
    CategoryTheory.Limits.FormalCoproduct.cosimplicialObjectFunctor,
    AlgebraicTopology.alternatingCofaceMapComplex,
    AlgebraicTopology.AlternatingCofaceMapComplex.obj,
    CategoryTheory.Limits.FormalCoproduct.cech,
    CategoryTheory.Limits.FormalCoproduct.power,
    CategoryTheory.Limits.FormalCoproduct.evalOp, Functor.comp_obj,
    Functor.comp, Functor.whiskeringLeft, Functor.rightOp] using
    (Pi.lift (fun i : Fin (0 + 1) → ι =>
      M.presheaf.map (homOfLE (show (∏ᶜ U ∘ i) ≤ ⊤ by simp)).op))

/-- Data expressing exactness of the augmented Čech complex. -/
structure AugmentedCechExactnessData {Y : Scheme.{u}} {ι : Type u}
    (M : Y.Modules) (U : ι → Y.Opens) : Prop where
  augmentation_is_cycle :
    cechAugmentation M U ≫ (cechComplex M U).d 0 1 = 0
  augmentation_injective : Function.Injective (cechAugmentation M U)
  exact_at_zero :
    (ShortComplex.mk (cechAugmentation M U) ((cechComplex M U).d 0 1)
      augmentation_is_cycle).Exact
  positive_exact : ∀ n : ℕ, 0 < n → (cechComplex M U).ExactAt n

/-- The exactness assertion for the augmented Čech complex. -/
def AugmentedCechExactness {Y : Scheme.{u}} {hY : IsAffine Y}
    (𝒰 : StandardOpenCover Y hY) (M : Y.Modules) : Prop :=
  AugmentedCechExactnessData M 𝒰.basicOpenFamily

/-!
The proof ladder for `standard_open_cover_augmented_cech_exact` is:

1. Unit24 gives injectivity and exactness of `M → C⁰ → C¹`.
2. The quasi-coherent sections/localization comparison transports that
   truncation to the geometric Čech augmentation.
3. `standardOpenCechModuleComplex` retains the global-section module structure
   on the entire Čech complex.
4. Localize that complex at every prime, insert an index whose cover function
   becomes a unit, and obtain a positive contracting homotopy.
5. Contractibility gives prime-localized exactness; primewise detection gives
   exactness of the module complex; forgetting scalars gives exactness of the
   geometric Čech complex.
6. Combine the degree-zero and positive-degree branches in the final wrapper.
-/

/-- The restriction maps from global sections to a standard-open Čech
complex form an augmentation. -/
/- TODO(proof agents -- leaf: augmentation compatibility): unfold the degree
zero and degree one terms of `CategoryTheory.cechComplexFunctor`.  For every
ordered pair of basic opens, both composites are restriction from `⊤` to the
same intersection, so the two summands in the alternating differential cancel.
No localization exactness input is needed for this leaf. -/
theorem standard_open_cech_augmentation_is_cycle {Y : Scheme.{u}}
    {hY : IsAffine Y} (𝒰 : StandardOpenCover Y hY) (M : Y.Modules) :
    cechAugmentation M 𝒰.basicOpenFamily ≫
      (cechComplex M 𝒰.basicOpenFamily).d 0 1 = 0 := by
  simp [globalSectionsObject, cechAugmentation, cechComplex,
    CategoryTheory.cechComplexFunctor,
    CategoryTheory.Limits.FormalCoproduct.cochainComplexFunctor,
    CategoryTheory.Limits.FormalCoproduct.cosimplicialObjectFunctor,
    AlgebraicTopology.alternatingCofaceMapComplex,
    AlgebraicTopology.AlternatingCofaceMapComplex.obj,
    CategoryTheory.Limits.FormalCoproduct.cech,
    CategoryTheory.Limits.FormalCoproduct.power,
    CategoryTheory.Limits.FormalCoproduct.evalOp,
    Functor.comp, Functor.whiskeringLeft, Functor.rightOp,
    CochainComplex.of.d, CosimplicialObject.δ]
  apply Pi.hom_ext
  intro i
  have h0 :
      (∏ᶜ 𝒰.basicOpenFamily ∘ i ∘
        ⇑(SimplexCategory.Hom.toOrderHom (SimplexCategory.δ 0))) ≤
        (⊤ : Y.Opens) := by simp
  have h1 :
      (∏ᶜ 𝒰.basicOpenFamily ∘ i ∘
        ⇑(SimplexCategory.Hom.toOrderHom (SimplexCategory.δ 1))) ≤
        (⊤ : Y.Opens) := by simp
  let f0 :=
    ((FormalCoproduct.mapPower
        ({ I := ULift (Fin 𝒰.n), obj := 𝒰.basicOpenFamily } :
          FormalCoproduct Y.Opens)
        ⇑(SimplexCategory.Hom.toOrderHom (SimplexCategory.δ 0))).op.unop.φ i ≫
      homOfLE h0).op
  let f1 :=
    ((FormalCoproduct.mapPower
        ({ I := ULift (Fin 𝒰.n), obj := 𝒰.basicOpenFamily } :
          FormalCoproduct Y.Opens)
        ⇑(SimplexCategory.Hom.toOrderHom (SimplexCategory.δ 1))).op.unop.φ i ≫
      homOfLE h1).op
  have hmap : M.presheaf.map f0 = M.presheaf.map f1 := by
    congr 1
  simp [Category.assoc, Preadditive.add_comp, Preadditive.neg_comp,
    ← Functor.map_comp, ← op_comp]
  change M.presheaf.map f0 + -M.presheaf.map f1 = _
  rw [hmap]
  rw [add_neg_cancel]
  symm
  exact CategoryTheory.Limits.zero_comp

/-- The precise algebraic truncation supplied by Algebra Unit24 for the module
of global sections.  This deliberately says nothing about Čech degrees above
one. -/
def StandardOpenModuleTruncationExact {Y : Scheme.{u}} {hY : IsAffine Y}
    (𝒰 : StandardOpenCover Y hY) (M : Y.Modules) : Prop :=
  Function.Injective
      (Formalization.Books.Algebra.Unit24.standardCoverModuleAlpha
        𝒰.function Γ(M, ⊤)) ∧
    Function.Exact
      (Formalization.Books.Algebra.Unit24.standardCoverModuleAlpha
        𝒰.function Γ(M, ⊤))
      (Formalization.Books.Algebra.Unit24.standardCoverModuleBeta
        𝒰.function Γ(M, ⊤))

/-- Unit24 provides exactly the algebraic degree-zero truncation needed here. -/
theorem standard_open_module_truncation_exact {Y : Scheme.{u}} {hY : IsAffine Y}
    (𝒰 : StandardOpenCover Y hY) (M : Y.Modules) :
    StandardOpenModuleTruncationExact 𝒰 M := by
  exact Formalization.Books.Algebra.Unit24.cover_module_exact
    𝒰.function 𝒰.span_eq_top Γ(M, ⊤)

/-- Transport the algebraic localization sequence to the augmentation and
degree-zero differential of the geometric Čech complex. -/
/- TODO(proof agents -- leaf: sections/localization bridge): for the
quasi-coherent `M`, construct the natural linear equivalences

  `M(D(f_i)) ≃ M(Y)_{f_i}` and
  `M(D(f_i) ∩ D(f_j)) ≃ M(Y)_{f_i f_j}`,

including the comparison between Mathlib's finite-intersection sections and
`Algebra.Unit24.standardCoverJointModule`.  Prove that these equivalences
intertwine `cechAugmentation` and the degree-zero Čech differential with
`standardCoverModuleAlpha` and `standardCoverModuleBeta`.  Only then transport
the two conclusions of `Algebra.Unit24.cover_module_exact 𝒰.function
  𝒰.span_eq_top`.  That upstream theorem is already proved; this leaf remains
  an explicit obligation because the geometric section/localization comparison
  is not supplied by the imported APIs.
It supplies only the three-term truncation `M → C⁰ → C¹` (injectivity of
the first map and exactness at `C⁰`); it supplies no `ExactAt n` for positive
complex degrees, which is deliberately the separate Coherent-local
contracting-homotopy leaf below. -/
theorem standard_open_cech_degree_zero_via_localization {Y : Scheme.{u}}
    {hY : IsAffine Y} (𝒰 : StandardOpenCover Y hY) (M : Y.Modules)
    [SheafOfModules.IsQuasicoherent (R := Y.ringCatSheaf) M]
    (hcycle : cechAugmentation M 𝒰.basicOpenFamily ≫
      (cechComplex M 𝒰.basicOpenFamily).d 0 1 = 0)
    (htruncation : StandardOpenModuleTruncationExact 𝒰 M) :
    Function.Injective (cechAugmentation M 𝒰.basicOpenFamily) ∧
      (ShortComplex.mk (cechAugmentation M 𝒰.basicOpenFamily)
        ((cechComplex M 𝒰.basicOpenFamily).d 0 1) hcycle).Exact := by
  sorry

/-- A contracting homotopy in the positive degrees of a cochain complex. -/
structure PositiveContractingHomotopy {C : Type u} [Category.{v} C] [Preadditive C]
    (K : CochainComplex C ℕ) where
  homotopy : ∀ n : ℕ, K.X (n + 1) ⟶ K.X n
  identity : ∀ n : ℕ,
    homotopy n ≫ K.d n (n + 1) + K.d (n + 1) (n + 2) ≫ homotopy (n + 1) = 𝟙 _

/-- The identity supplied by a positive contracting homotopy. -/
theorem PositiveContractingHomotopy.identity_at
    {C : Type u} [Category.{v} C] [Preadditive C] {K : CochainComplex C ℕ}
    (h : PositiveContractingHomotopy K) (n : ℕ) :
    h.homotopy n ≫ K.d n (n + 1) + K.d (n + 1) (n + 2) ≫ h.homotopy (n + 1) = 𝟙 _ :=
  h.identity n

/-- A positive contracting homotopy gives exactness in every positive degree.
The homotopy identity supplies a section of the map from cycles to the middle
term, so that map is a split epimorphism. -/
theorem PositiveContractingHomotopy.exactAt
    {C : Type u} [Category.{v} C] [Abelian C] {K : CochainComplex C ℕ}
    (h : PositiveContractingHomotopy K) (n : ℕ) (hn : 0 < n) : K.ExactAt n := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  apply (HomologicalComplex.exactAt_iff'
    (K := K) (i := m) (j := m + 1) (k := m + 2)
    (CochainComplex.prev_nat_succ m) (by simp)).2
  change (ShortComplex.mk (K.d m (m + 1)) (K.d (m + 1) (m + 2))
    (K.d_comp_d m (m + 1) (m + 2))).Exact
  rw [ShortComplex.exact_iff_epi_toCycles]
  let S := ShortComplex.mk (K.d m (m + 1)) (K.d (m + 1) (m + 2))
    (K.d_comp_d m (m + 1) (m + 2))
  let section_ : S.cycles ⟶ S.X₁ := S.iCycles ≫ h.homotopy m
  have hsection : section_ ≫ S.toCycles = 𝟙 _ := by
    apply (cancel_mono S.iCycles).1
    simp only [section_, Category.assoc, ShortComplex.toCycles_i,
      Category.id_comp, Category.comp_id]
    change S.iCycles ≫ h.homotopy m ≫ K.d m (m + 1) = _
    calc
      _ = S.iCycles ≫
          (h.homotopy m ≫ K.d m (m + 1) +
            K.d (m + 1) (m + 2) ≫ h.homotopy (m + 1)) := by
        simp only [Preadditive.comp_add, Category.assoc,
          ShortComplex.iCycles_g, comp_zero, add_zero]
      _ = S.iCycles ≫ 𝟙 _ := by rw [h.identity m]
      _ = _ := by simp
  exact (⟨section_, hsection⟩ : SplitEpi S.toCycles).epi

/-- The choice data used in the source's localized Čech argument. -/
structure LocalizedCechHomotopyData {Y : Scheme.{u}} {hY : IsAffine Y}
    (𝒰 : StandardOpenCover Y hY) (p : PrimeSpectrum (Γ(Y, ⊤))) where
  fixed : Fin 𝒰.n
  fixed_not_mem : 𝒰.function fixed ∉ p.asIdeal

/-- A member of a standard covering avoids any chosen prime. -/
theorem localized_cech_index_exists {Y : Scheme.{u}} {hY : IsAffine Y}
    (𝒰 : StandardOpenCover Y hY) (p : PrimeSpectrum (Γ(Y, ⊤))) :
    ∃ i : Fin 𝒰.n, 𝒰.function i ∉ p.asIdeal := by
  by_contra h
  apply p.2.ne_top
  rw [← top_le_iff, ← 𝒰.span_eq_top, Ideal.span_le]
  intro x hx
  obtain ⟨i, rfl⟩ := hx
  by_contra hi
  exact h ⟨i, hi⟩

/-- The choice used in the localized contracting-homotopy argument exists. -/
theorem localized_cech_homotopy_data_nonempty {Y : Scheme.{u}} {hY : IsAffine Y}
    (𝒰 : StandardOpenCover Y hY) (p : PrimeSpectrum (Γ(Y, ⊤))) :
    Nonempty (LocalizedCechHomotopyData 𝒰 p) := by
  rcases localized_cech_index_exists 𝒰 p with ⟨i, hi⟩
  exact ⟨{ fixed := i, fixed_not_mem := hi }⟩

/-- The Čech complex with its natural linear structure over the ring of global
sections, used as the module-valued model for the geometric Čech complex. -/
/- TODO(proof agents -- construction leaf: global-linear Čech model): apply
`CategoryTheory.cechComplexFunctor` to the underlying presheaf of

  `SheafOfModules.forgetToSheafModuleCat Y.ringCatSheaf (.op ⊤)
    (Limits.initialOpOfTerminal Limits.isTerminalTop) |>.obj M`.

This existing functor performs the required restriction of scalars from every
`Γ(Y, V)` to `Γ(Y, ⊤)` and makes all restriction maps globally linear. -/
noncomputable def standardOpenCechModuleComplex {Y : Scheme.{u}} {hY : IsAffine Y}
    (𝒰 : StandardOpenCover Y hY) (M : Y.Modules) :
    CochainComplex (ModuleCat.{u} Γ(Y, ⊤)) ℕ := by
  exact (CategoryTheory.cechComplexFunctor 𝒰.basicOpenFamily).obj
    ((SheafOfModules.forgetToSheafModuleCat Y.ringCatSheaf (.op ⊤)
      (Limits.initialOpOfTerminal Limits.isTerminalTop)).obj M).1

/-- The global-linear Čech complex localized at one prime. -/
noncomputable def primeLocalizedStandardOpenCechComplex {Y : Scheme.{u}}
    {hY : IsAffine Y} (𝒰 : StandardOpenCover Y hY) (M : Y.Modules)
    (p : PrimeSpectrum (Γ(Y, ⊤))) :
    CochainComplex (ModuleCat.{u} (Localization p.asIdeal.primeCompl)) ℕ :=
  ((ModuleCat.localizedModuleFunctor.{u} p.asIdeal.primeCompl).mapHomologicalComplex
    (ComplexShape.up ℕ)).obj (standardOpenCechModuleComplex 𝒰 M)

/-- The degreewise index-insertion map on the prime-localized Čech complex. -/
/- TODO(proof agents -- construction leaf: localized insertion map): identify
localization of each finite product with the product of the localized terms.
Quasi-coherence identifies the factor indexed by `i₀, ..., iₙ` with the
iterated localization of `Γ(M, ⊤)` at the corresponding cover functions.
Because `choice.fixed_not_mem` makes the fixed function a unit at `p`, dropping
that factor gives the required map
`h(s) i₀ ... iₙ := s(choice.fixed, i₀, ..., iₙ)`. -/
noncomputable def standard_open_prime_localized_homotopyMap
    {Y : Scheme.{u}} {hY : IsAffine Y} (𝒰 : StandardOpenCover Y hY)
    (M : Y.Modules) [SheafOfModules.IsQuasicoherent (R := Y.ringCatSheaf) M]
    (p : PrimeSpectrum (Γ(Y, ⊤))) (choice : LocalizedCechHomotopyData 𝒰 p)
    (n : ℕ) :
    (primeLocalizedStandardOpenCechComplex 𝒰 M p).X (n + 1) ⟶
      (primeLocalizedStandardOpenCechComplex 𝒰 M p).X n := by
  sorry

/-- The localized insertion maps satisfy `d h + h d = 1`. -/
/- TODO(proof agents -- leaf: alternating-sign identity): expand the Čech
differential as the alternating sum of face maps.  The term which removes the
inserted fixed index is the identity; every other term occurs twice with
opposite signs.  This is the textbook computation verbatim. -/
theorem standard_open_prime_localized_homotopy_identity
    {Y : Scheme.{u}} {hY : IsAffine Y} (𝒰 : StandardOpenCover Y hY)
    (M : Y.Modules) [SheafOfModules.IsQuasicoherent (R := Y.ringCatSheaf) M]
    (p : PrimeSpectrum (Γ(Y, ⊤))) (choice : LocalizedCechHomotopyData 𝒰 p)
    (n : ℕ) :
    standard_open_prime_localized_homotopyMap 𝒰 M p choice n ≫
        (primeLocalizedStandardOpenCechComplex 𝒰 M p).d n (n + 1) +
      (primeLocalizedStandardOpenCechComplex 𝒰 M p).d (n + 1) (n + 2) ≫
        standard_open_prime_localized_homotopyMap 𝒰 M p choice (n + 1) = 𝟙 _ := by
  sorry

/-- Insertion of an index whose cover function is a unit after localization
contracts the prime-localized Čech complex. -/
noncomputable def standard_open_prime_localized_contracting_homotopy
    {Y : Scheme.{u}} {hY : IsAffine Y} (𝒰 : StandardOpenCover Y hY)
    (M : Y.Modules) [SheafOfModules.IsQuasicoherent (R := Y.ringCatSheaf) M]
    (p : PrimeSpectrum (Γ(Y, ⊤))) :
    PositiveContractingHomotopy (primeLocalizedStandardOpenCechComplex 𝒰 M p) := by
  let choice := Classical.choice (localized_cech_homotopy_data_nonempty 𝒰 p)
  exact
    { homotopy := standard_open_prime_localized_homotopyMap 𝒰 M p choice
      identity := standard_open_prime_localized_homotopy_identity 𝒰 M p choice }

/-- Each prime localization of the Čech module complex is exact in positive
degrees. -/
theorem standard_open_prime_localized_positive_exact
    {Y : Scheme.{u}} {hY : IsAffine Y} (𝒰 : StandardOpenCover Y hY)
    (M : Y.Modules) [SheafOfModules.IsQuasicoherent (R := Y.ringCatSheaf) M]
    (p : PrimeSpectrum (Γ(Y, ⊤))) (n : ℕ) (hn : 0 < n) :
    (primeLocalizedStandardOpenCechComplex 𝒰 M p).ExactAt n := by
  exact (standard_open_prime_localized_contracting_homotopy 𝒰 M p).exactAt n hn

/-- Exactness of a complex of modules can be checked after localization at
every prime. -/
theorem standard_open_cech_module_exactAt_of_prime_localized
    {Y : Scheme.{u}} {hY : IsAffine Y} (𝒰 : StandardOpenCover Y hY)
    (M : Y.Modules) (n : ℕ)
    (hlocal : ∀ p : PrimeSpectrum (Γ(Y, ⊤)),
      (primeLocalizedStandardOpenCechComplex 𝒰 M p).ExactAt n) :
    (standardOpenCechModuleComplex 𝒰 M).ExactAt n := by
  let S := (standardOpenCechModuleComplex 𝒰 M).sc n
  rw [HomologicalComplex.exactAt_iff]
  apply (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).2
  refine exact_of_isLocalized_maximal
    (Mₚ := fun P => S.X₁.localizedModule P.primeCompl)
    (f := fun P => S.X₁.localizedModuleMkLinearMap P.primeCompl)
    (Nₚ := fun P => S.X₂.localizedModule P.primeCompl)
    (g := fun P => S.X₂.localizedModuleMkLinearMap P.primeCompl)
    (Lₚ := fun P => S.X₃.localizedModule P.primeCompl)
    (h := fun P => S.X₃.localizedModuleMkLinearMap P.primeCompl)
    S.f.hom S.g.hom ?_
  intro J hJ
  let p : PrimeSpectrum (Γ(Y, ⊤)) := ⟨J, hJ.isPrime⟩
  have hp := hlocal p
  rw [HomologicalComplex.exactAt_iff] at hp
  change (S.map (ModuleCat.localizedModuleFunctor J.primeCompl)).Exact at hp
  have hp' := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1 hp
  change Function.Exact
    (IsLocalizedModule.map J.primeCompl
      (S.X₁.localizedModuleMkLinearMap J.primeCompl)
      (S.X₂.localizedModuleMkLinearMap J.primeCompl) S.f.hom)
    (IsLocalizedModule.map J.primeCompl
      (S.X₂.localizedModuleMkLinearMap J.primeCompl)
      (S.X₃.localizedModuleMkLinearMap J.primeCompl) S.g.hom) at hp'
  exact hp'

/-- Transfer exactness from the global-linear model back to the geometric
Čech complex. -/
theorem standard_open_cech_exactAt_of_module_model_exactAt
    {Y : Scheme.{u}} {hY : IsAffine Y} (𝒰 : StandardOpenCover Y hY)
    (M : Y.Modules) (n : ℕ)
    (hmodule : (standardOpenCechModuleComplex 𝒰 M).ExactAt n) :
    (cechComplex M 𝒰.basicOpenFamily).ExactAt n := by
  sorry

/-- Positive-degree exactness of the standard-open Čech complex, obtained by
prime localization and the textbook's contracting homotopy. -/
theorem standard_open_cech_positive_exact_via_localized_contraction
    {Y : Scheme.{u}} {hY : IsAffine Y} (𝒰 : StandardOpenCover Y hY)
    (M : Y.Modules)
    [SheafOfModules.IsQuasicoherent (R := Y.ringCatSheaf) M] :
    ∀ n : ℕ, 0 < n → (cechComplex M 𝒰.basicOpenFamily).ExactAt n := by
  intro n hn
  apply standard_open_cech_exactAt_of_module_model_exactAt 𝒰 M n
  apply standard_open_cech_module_exactAt_of_prime_localized 𝒰 M n
  intro p
  exact standard_open_prime_localized_positive_exact 𝒰 M p n hn

/-- Standard affine covers have exact augmented Čech complexes for
quasi-coherent sheaves. -/
theorem standard_open_cover_augmented_cech_exact {Y : Scheme.{u}} {hY : IsAffine Y}
    (𝒰 : StandardOpenCover Y hY) (M : Y.Modules)
    [SheafOfModules.IsQuasicoherent (R := Y.ringCatSheaf) M] :
    AugmentedCechExactness 𝒰 M := by
  let hcycle := standard_open_cech_augmentation_is_cycle 𝒰 M
  have hdegreeZero := standard_open_cech_degree_zero_via_localization
    𝒰 M hcycle (standard_open_module_truncation_exact 𝒰 M)
  exact
    { augmentation_is_cycle := hcycle
      augmentation_injective := hdegreeZero.1
      exact_at_zero := hdegreeZero.2
      positive_exact := standard_open_cech_positive_exact_via_localized_contraction 𝒰 M }

/-- The affine-open form of augmented Čech exactness. -/
theorem affine_open_augmented_cech_exact {X : Scheme.{u}}
    (𝒰 : StandardOpenCoverOfAffineOpen X) (M : X.Modules)
    [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) M] :
    AugmentedCechExactness 𝒰.cover (M.restrict 𝒰.U.ι) := by
  exact standard_open_cover_augmented_cech_exact 𝒰.cover (M.restrict 𝒰.U.ι)

/-! ### Cohomology on affine opens -/

/-- Positive augmented Čech exactness for the cofinal system of standard-open
covers of an affine scheme implies vanishing of derived global sections. -/
/- TODO(proof agents -- leaf: Čech-vanish-basis comparison): regard the finite
standard-open covers of every affine open, ordered by refinement, as a cofinal
system of covers from the affine basis.  Construct the canonical maps from
their Čech cohomology objects to `schemeCohomologyObject N n`, and invoke the
Čech-vanish-basis theorem (or prove it through the usual refinement colimit of
Čech resolutions).  For each affine open `V` and cover `𝒰`, use
`hcech V hV 𝒰 |>.positive_exact` to kill positive Čech cohomology.  Cofinality,
not exactness of any single cover, is what makes the resulting map compute
derived sheaf cohomology. -/
theorem affine_standard_cover_system_to_derived_positive_vanishing
    {Y : Scheme.{u}} {hY : IsAffine Y} (N : Y.Modules)
    [SheafOfModules.IsQuasicoherent (R := Y.ringCatSheaf) N]
    [CategoryTheory.HasExt.{u} Y.Modules]
    (hcech : ∀ (V : Y.Opens) (hV : IsAffineOpen V)
      (𝒰 : StandardOpenCover (V : Scheme) hV),
      AugmentedCechExactness 𝒰 (N.restrict V.ι))
    {n : ℕ} (hn : 0 < n) :
    IsZero (schemeCohomologyObject N n) := by
  sorry

/-- Quasi-coherent sheaves have no positive cohomology on affine opens. -/
theorem quasi_coherent_affine_cohomology_zero {X : Scheme.{u}}
    (M : X.Modules)
    [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) M]
    (U : X.Opens) (hU : IsAffineOpen U)
    [CategoryTheory.HasExt.{u} (U : Scheme).Modules] {n : ℕ} (hn : 0 < n) :
    IsZero (schemeCohomologyOn M U n) := by
  simpa [schemeCohomologyOn] using
    (affine_standard_cover_system_to_derived_positive_vanishing
      (hY := hU) (M.restrict U.ι)
      (fun V hV 𝒰 ↦
        standard_open_cover_augmented_cech_exact (hY := hV) 𝒰
          ((M.restrict U.ι).restrict V.ι)) hn)

/-! ### Affine morphisms and higher direct images -/

/-- The `i`th right-derived pushforward. -/
noncomputable def higherDirectImage {X S : Scheme.{u}} (f : X ⟶ S)
    [CategoryTheory.HasInjectiveResolutions X.Modules] (i : ℕ) : X.Modules ⥤ S.Modules :=
  (Scheme.Modules.pushforward f).rightDerived i

/-- The affine-open evaluation of a positive higher direct image is zero. -/
/- TODO(proof agents -- leaf: affine-open evaluation bridge): construct the
canonical comparison

  `(R^i f_* M)(U) ≃ H^i(f⁻¹(U), M|_{f⁻¹(U)})`

for an affine open `U`.  Derive it by restricting an injective resolution along
the open immersion (or by the right-derived pushforward/restriction base-change
map), prove that the comparison is an isomorphism, use
`hU.preimage f : IsAffineOpen (f ⁻¹ᵁ U)`, and finish with
`quasi_coherent_affine_cohomology_zero`.  This leaf owns the currently missing
local `HasExt`/injective-resolution comparison for the inverse-image open. -/
theorem higher_direct_image_affine_open_evaluation_isZero {X S : Scheme.{u}}
    (f : X ⟶ S) [IsAffineHom f]
    [CategoryTheory.HasInjectiveResolutions X.Modules]
    (M : X.Modules) [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) M]
    {i : ℕ} (hi : 0 < i) (U : S.Opens) (hU : IsAffineOpen U) :
    IsZero (((higherDirectImage f i).obj M).presheaf.obj (Opposite.op U)) := by
  sorry

/-- A sheaf of modules whose sections vanish on every affine open is zero. -/
/- TODO(proof agents -- leaf: affine-basis detection): use the affine opens as
a basis.  Either show all stalks of `N` are zero by taking the filtered colimit
over affine neighbourhoods, then apply stalkwise conservativity, or use the
sheaf ext/detection theorem for a basis directly. -/
theorem module_isZero_of_affine_open_evaluations {S : Scheme.{u}} (N : S.Modules)
    (hN : ∀ (U : S.Opens), IsAffineOpen U →
      IsZero (N.presheaf.obj (Opposite.op U))) :
    IsZero N := by
  sorry

/-- Higher direct images of quasi-coherent sheaves vanish for affine morphisms. -/
theorem relative_affine_higher_direct_image_vanishes {X S : Scheme.{u}}
    (f : X ⟶ S) [IsAffineHom f]
    [CategoryTheory.HasInjectiveResolutions X.Modules]
    (M : X.Modules) [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) M]
    {i : ℕ} (hi : 0 < i) :
    IsZero ((higherDirectImage f i).obj M) := by
  apply module_isZero_of_affine_open_evaluations
  intro U hU
  exact higher_direct_image_affine_open_evaluation_isZero f M hi U hU

/-- Degeneration data for the Leray comparison associated to an affine
morphism.  Packaging all degrees together makes the intended natural edge
comparison explicit, instead of choosing unrelated isomorphisms degree by
degree. -/
structure RelativeAffineLerayDegeneration {X S : Scheme.{u}} (f : X ⟶ S)
    (M : X.Modules) [CategoryTheory.HasExt.{u} X.Modules]
    [CategoryTheory.HasExt.{u} S.Modules] : Prop where
  edgeIso : ∀ i : ℕ,
    Nonempty
      (schemeCohomologyObject M i ≅
        schemeCohomologyObject ((Scheme.Modules.pushforward f).obj M) i)

/-- The Leray edge comparison degenerates for an affine morphism and
quasi-coherent coefficients. -/
/- TODO(proof agents -- leaf: Leray/derived-pushforward comparison): construct
the Grothendieck/Leray double complex comparing derived global sections on `X`
with derived global sections after `f_*`.  Identify its positive vertical rows
with higher direct images.  Use the affine-open evaluation argument from
`higher_direct_image_affine_open_evaluation_isZero` (or compare the `HasExt`
model here with a chosen injective-resolution model) to kill those rows, and
prove that the surviving edge morphisms give the displayed isomorphisms,
naturally in `M` and simultaneously for all degrees. -/
theorem relative_affine_leray_degeneration {X S : Scheme.{u}}
    (f : X ⟶ S) [IsAffineHom f]
    (M : X.Modules) [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) M]
    [CategoryTheory.HasExt.{u} X.Modules] [CategoryTheory.HasExt.{u} S.Modules] :
    RelativeAffineLerayDegeneration f M := by
  sorry

/-- Cohomology is unchanged by an affine relative pushforward. -/
theorem relative_affine_cohomology_comparison {X S : Scheme.{u}}
    (f : X ⟶ S) [IsAffineHom f]
    (M : X.Modules) [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) M]
    [CategoryTheory.HasExt.{u} X.Modules] [CategoryTheory.HasExt.{u} S.Modules]
    (i : ℕ) :
    Nonempty
      (schemeCohomologyObject M i ≅
        schemeCohomologyObject ((Scheme.Modules.pushforward f).obj M) i) := by
  exact (relative_affine_leray_degeneration f M).edgeIso i

/-! ### Affine diagonal -/

/-- Affineness of the diagonal of a scheme. -/
def HasAffineDiagonal (X : Scheme.{u}) : Prop :=
  IsAffineHom (pullback.diagonal (terminal.from X))

/-- Pairwise intersections of affine opens are affine. -/
def AffineOpenIntersections (X : Scheme.{u}) : Prop :=
  ∀ U V : X.Opens, IsAffineOpen U → IsAffineOpen V → IsAffineOpen (U ⊓ V)

/-- A cover all of whose finite intersections are affine. -/
structure AffineIntersectionCover (X : Scheme.{u}) where
  cover : Scheme.OpenCover.{u} X
  intersections_affine :
    ∀ (n : ℕ) (i : Fin (n + 1) → cover.I₀),
      IsAffineOpen (⨅ j, (cover.f (i j)).opensRange)

/-- The three standard characterizations of an affine diagonal. -/
theorem affine_diagonal_iff {X : Scheme.{u}} :
    (HasAffineDiagonal X ↔ AffineOpenIntersections X) ∧
      (AffineOpenIntersections X ↔ Nonempty (AffineIntersectionCover X)) := by
  have hleft : HasAffineDiagonal X ↔ AffineOpenIntersections X := by
    rw [HasAffineDiagonal, AffineOpenIntersections]
    constructor
    · intro h U V hU hV
      exact isAffineHom_diagonal_iff.mp h ⊤ (isAffineOpen_top _) U (by simp) V (by simp) hU hV
    · intro h
      apply isAffineHom_diagonal_iff.mpr
      intro U hU V₁ hV₁ V₂ hV₂ hV₁' hV₂'
      exact h V₁ V₂ hV₁' hV₂'
  refine ⟨hleft, ?_⟩
  rw [AffineOpenIntersections]
  constructor
  · intro h
    let : IsAffineHom (pullback.diagonal (terminal.from X)) := hleft.mpr h
    refine ⟨{ cover := X.affineOpenCover.openCover, intersections_affine := ?_ }⟩
    intro n i
    apply IsAffineOpen.iInf
    intro j
    have hAff : IsAffine (X.affineOpenCover.openCover.X (i j)) :=
      Scheme.isAffine_affineOpenCover X X.affineOpenCover (i j)
    let := hAff
    exact isAffineOpen_opensRange (X.affineOpenCover.openCover.f (i j))
  · rintro ⟨𝒰⟩
    have hAff (i : 𝒰.cover.I₀) : IsAffine (𝒰.cover.X i) := by
      have htop : IsAffineOpen (⊤ : (𝒰.cover.X i).Opens) := by
        apply (𝒰.cover.f i).isAffineOpen_iff_of_isOpenImmersion (U := ⊤) |>.mp
        simpa using 𝒰.intersections_affine 0 (fun _ : Fin 1 => i)
      let : IsAffine (↑(⊤ : (𝒰.cover.X i).Opens)) := htop
      exact IsAffine.of_isIso (𝒰.cover.X i).topIso.inv
    let : ∀ i, IsAffine (𝒰.cover.X i) := hAff
    let Q : AffineTargetMorphismProperty := fun X _ _ _ => IsAffine X
    let : HasAffineProperty (@IsAffineHom) Q := by
      simpa [Q] using instHasAffinePropertyIsAffineHomIsAffine
    have hQ : Q.diagonal (terminal.from X) := by
      let : Q.IsLocal :=
        HasAffineProperty.isLocal_affineProperty (P := @IsAffineHom) (Q := Q)
      apply AffineTargetMorphismProperty.diagonal_of_openCover_source
        (Q := Q) (terminal.from X) 𝒰.cover
      intro i j
      change IsAffine (pullback (𝒰.cover.f i) (𝒰.cover.f j))
      have hh := 𝒰.intersections_affine 1 (fun k : Fin 2 => ![i, j] k)
      rw [← Finset.inf_univ_eq_iInf, Finset.univ_fin2] at hh
      simp only [Finset.inf_insert, Finset.inf_singleton,
        Matrix.cons_val_zero, Matrix.cons_val_one] at hh
      have hInt : IsAffineOpen
          ((𝒰.cover.f i).opensRange ⊓ (𝒰.cover.f j).opensRange) := by
        simpa using hh
      have hRange : IsAffineOpen
          (pullback.fst (𝒰.cover.f i) (𝒰.cover.f j) ≫ 𝒰.cover.f i).opensRange := by
        convert hInt using 1
        exact Opens.ext (IsOpenImmersion.range_pullback_to_base_of_left _ _)
      change IsAffine _ at hRange
      exact IsAffine.of_isIso
        (pullback.fst (𝒰.cover.f i) (𝒰.cover.f j) ≫ 𝒰.cover.f i).isoOpensRange.hom
    have hdiag : HasAffineDiagonal X := by
      exact (HasAffineProperty.diagonal_iff (P := @IsAffineHom) (Q := Q)
        (f := terminal.from X)).mp hQ
    exact hleft.mp hdiag

/-- A separated scheme has affine diagonal. -/
theorem has_affine_diagonal_of_separated (X : Scheme.{u}) [X.IsSeparated] :
    HasAffineDiagonal X := by
  change IsAffineHom (pullback.diagonal (terminal.from X))
  infer_instance

/-! ### Čech cohomology and sheaf cohomology -/

/-- The cover Čech-to-derived comparison when every nonempty finite
intersection in the cover is affine. -/
/- TODO(proof agents -- leaf: cover double-complex collapse): apply an
injective (or Cartan--Eilenberg) resolution of `M` termwise to the cover's
cosimplicial object.  The vertical cohomology over the intersection indexed by
`i : Fin (q + 1) → 𝒱.I₀` is sheaf cohomology on
`⨅ j, (𝒱.f (i j)).opensRange`.  Use `hintersections q i` and
`quasi_coherent_affine_cohomology_zero` to kill every positive vertical row.
Identify the remaining row, including alternating signs, with
`cechComplex M (fun i ↦ (𝒱.f i).opensRange)`, and show that the edge
morphism induces the displayed isomorphism in degree `n`. -/
theorem cover_cech_to_derived_of_affine_intersections {X : Scheme.{u}}
    (𝒱 : Scheme.OpenCover.{u} X) (M : X.Modules)
    [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) M]
    [CategoryTheory.HasExt.{u} X.Modules]
    (hintersections : ∀ (q : ℕ) (i : Fin (q + 1) → 𝒱.I₀),
      IsAffineOpen (⨅ j, (𝒱.f (i j)).opensRange))
    (n : ℕ) :
    Nonempty
      (cechCohomologyObject M (fun i ↦ (𝒱.f i).opensRange) n ≅
        schemeCohomologyObject M n) := by
  sorry

/-- Čech cohomology agrees with sheaf cohomology on an affine-intersection
cover for quasi-coherent coefficients. -/
theorem cech_cohomology_eq_sheaf_cohomology {X : Scheme.{u}}
    (𝒰 : AffineIntersectionCover X) (M : X.Modules)
    [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) M]
    [CategoryTheory.HasExt.{u} X.Modules]
    (n : ℕ) :
    Nonempty
      (cechCohomologyObject M (fun i => (𝒰.cover.f i).opensRange) n ≅
        schemeCohomologyObject M n) := by
  exact cover_cech_to_derived_of_affine_intersections
    𝒰.cover M 𝒰.intersections_affine n

end Formalization.Books.Coherent.Unit01
