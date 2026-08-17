import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.Algebra.Category.Grp.CartesianMonoidal
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
import Mathlib.Algebra.Homology.ShortComplex.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import Mathlib.AlgebraicGeometry.Cover.Open
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.CategoryTheory.Abelian.RightDerived
import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech

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
  exact_at_zero :
    (ShortComplex.mk (cechAugmentation M U) ((cechComplex M U).d 0 1)
      augmentation_is_cycle).Exact
  positive_exact : ∀ n : ℕ, 0 < n → (cechComplex M U).ExactAt n

/-- The exactness assertion for the augmented Čech complex. -/
def AugmentedCechExactness {Y : Scheme.{u}} {hY : IsAffine Y}
    (𝒰 : StandardOpenCover Y hY) (M : Y.Modules) : Prop :=
  AugmentedCechExactnessData M 𝒰.basicOpenFamily

/-- Standard affine covers have exact augmented Čech complexes for
quasi-coherent sheaves. -/
theorem standard_open_cover_augmented_cech_exact {Y : Scheme.{u}} {hY : IsAffine Y}
    (𝒰 : StandardOpenCover Y hY) (M : Y.Modules)
    [SheafOfModules.IsQuasicoherent (R := Y.ringCatSheaf) M] :
    AugmentedCechExactness 𝒰 M := by
  sorry

/-- The affine-open form of augmented Čech exactness. -/
theorem affine_open_augmented_cech_exact {X : Scheme.{u}}
    (𝒰 : StandardOpenCoverOfAffineOpen X) (M : X.Modules)
    [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) M] :
    AugmentedCechExactness 𝒰.cover (M.restrict 𝒰.U.ι) := by
  exact standard_open_cover_augmented_cech_exact 𝒰.cover (M.restrict 𝒰.U.ι)

/-! ### Cohomology on affine opens -/

/-- Quasi-coherent sheaves have no positive cohomology on affine opens. -/
theorem quasi_coherent_affine_cohomology_zero {X : Scheme.{u}}
    (M : X.Modules)
    [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) M]
    (U : X.Opens) (hU : IsAffineOpen U)
    [CategoryTheory.HasExt.{u} (U : Scheme).Modules] {n : ℕ} (hn : 0 < n) :
    IsZero (schemeCohomologyOn M U n) := by
  sorry

/-! ### The contracting-homotopy identity -/

/-- A contracting homotopy in the positive degrees of a cochain complex.

For degree `n + 1`, the displayed equation is the categorical form of
`d h + h d = 1`. -/
structure PositiveContractingHomotopy
    (K : CochainComplex AddCommGrpCat.{u} ℕ) where
  homotopy : ∀ n : ℕ, K.X (n + 1) ⟶ K.X n
  identity : ∀ n : ℕ,
    homotopy n ≫ K.d n (n + 1) + K.d (n + 1) (n + 2) ≫ homotopy (n + 1) = 𝟙 _

/-- The identity supplied by a positive contracting homotopy. -/
theorem PositiveContractingHomotopy.identity_at
    {K : CochainComplex AddCommGrpCat.{u} ℕ} (h : PositiveContractingHomotopy K)
    (n : ℕ) :
    h.homotopy n ≫ K.d n (n + 1) + K.d (n + 1) (n + 2) ≫ h.homotopy (n + 1) = 𝟙 _ :=
  h.identity n

/-- The source's localized Čech argument, expressed as a positive contracting
homotopy after choosing an index whose defining function avoids a prime. -/
structure LocalizedCechHomotopyData {Y : Scheme.{u}} {hY : IsAffine Y}
    (𝒰 : StandardOpenCover Y hY) where
  prime : PrimeSpectrum (Γ(Y, ⊤))
  fixed : Fin 𝒰.n
  fixed_not_mem : 𝒰.function fixed ∉ prime.asIdeal

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
    Nonempty (LocalizedCechHomotopyData 𝒰) := by
  rcases localized_cech_index_exists 𝒰 p with ⟨i, hi⟩
  exact ⟨{ prime := p, fixed := i, fixed_not_mem := hi }⟩

/-! ### Affine morphisms and higher direct images -/

/-- The `i`th right-derived pushforward. -/
noncomputable def higherDirectImage {X S : Scheme.{u}} (f : X ⟶ S)
    [CategoryTheory.HasInjectiveResolutions X.Modules] (i : ℕ) : X.Modules ⥤ S.Modules :=
  (Scheme.Modules.pushforward f).rightDerived i

/-- Higher direct images of quasi-coherent sheaves vanish for affine morphisms. -/
theorem relative_affine_higher_direct_image_vanishes {X S : Scheme.{u}}
    (f : X ⟶ S) [IsAffineHom f]
    [CategoryTheory.HasInjectiveResolutions X.Modules]
    (M : X.Modules) [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) M]
    {i : ℕ} (hi : 0 < i) :
    IsZero ((higherDirectImage f i).obj M) := by
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
  sorry

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
  sorry

end Formalization.Books.Coherent.Unit01
