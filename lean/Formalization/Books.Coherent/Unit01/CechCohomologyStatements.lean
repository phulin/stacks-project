import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.Algebra.Category.Grp.CartesianMonoidal
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
import Mathlib.Algebra.Homology.ShortComplex.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import Mathlib.AlgebraicGeometry.Cover.Open
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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

namespace Formalization.«Books.Coherent».Unit01

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
  sorry

/-! ### Sheaf and Čech cohomology objects -/

/-- The smallness datum needed to instantiate the derived Ext construction
for sheaves of modules on a scheme.  Mathlib exposes `HasExt` as an explicit
infrastructure assumption, but does not currently choose it for `Y.Modules`.
-/
class SchemeCohomologyData (Y : Scheme.{u}) : Prop where
  hasExt : CategoryTheory.HasExt.{u} Y.Modules

attribute [instance] SchemeCohomologyData.hasExt

/-- Cohomology of a sheaf of modules, as an object of `AddCommGrpCat`. -/
noncomputable def schemeCohomologyObject {Y : Scheme.{u}} (M : Y.Modules) (n : ℕ)
    [hY : SchemeCohomologyData Y] : AddCommGrpCat.{u} :=
  let E := @CategoryTheory.Abelian.Ext.{u} _ _ _ hY.hasExt
    (SheafOfModules.unit Y.ringCatSheaf) M n
  letI : AddCommGroup E :=
    @CategoryTheory.Abelian.Ext.instAddCommGroup.{u} _ _ _ hY.hasExt
      (SheafOfModules.unit Y.ringCatSheaf) M n
  AddCommGrpCat.of E

/-- Cohomology of a sheaf of modules on an open subscheme. -/
noncomputable def schemeCohomologyOn {X : Scheme.{u}} (M : X.Modules)
    (U : X.Opens) (n : ℕ) [SchemeCohomologyData (U : Scheme)] : AddCommGrpCat.{u} :=
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
    (M : Y.Modules) (U : ι → Y.Opens) where
  augmentation_is_cycle :
    cechAugmentation M U ≫ (cechComplex M U).d 0 1 = 0
  exact_at_zero :
    (ShortComplex.mk (cechAugmentation M U) ((cechComplex M U).d 0 1)
      augmentation_is_cycle).Exact
  positive_exact : ∀ n : ℕ, 0 < n → (cechComplex M U).ExactAt n

/-- The exactness assertion for the augmented Čech complex.

It records the canonical degree-zero augmentation, exactness at degree zero
and in every positive degree, together with positive Čech cohomology
vanishing. -/
def AugmentedCechExactness {Y : Scheme.{u}} {hY : IsAffine Y}
    (𝒰 : StandardOpenCover Y hY) (M : Y.Modules) : Prop :=
  Nonempty (AugmentedCechExactnessData M 𝒰.basicOpenFamily) ∧
    PositiveCechExactness M 𝒰.basicOpenFamily

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
  sorry

/-! ### Cohomology on affine opens -/

/-- Quasi-coherent sheaves have no positive cohomology on affine opens. -/
theorem quasi_coherent_affine_cohomology_zero {X : Scheme.{u}}
    (M : X.Modules)
    [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) M]
    (U : X.Opens) (hU : IsAffineOpen U)
    [SchemeCohomologyData (U : Scheme)] {n : ℕ} (hn : 0 < n) :
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
  sorry

/-- The choice used in the localized contracting-homotopy argument exists. -/
theorem localized_cech_homotopy_data_nonempty {Y : Scheme.{u}} {hY : IsAffine Y}
    (𝒰 : StandardOpenCover Y hY) (p : PrimeSpectrum (Γ(Y, ⊤))) :
    Nonempty (LocalizedCechHomotopyData 𝒰) := by
  sorry

/-! ### Affine morphisms and higher direct images -/

/-- The missing infrastructure needed to form the right-derived pushforward.

Mathlib provides `Functor.rightDerived` for any additive functor once the
source category has chosen injective resolutions.  The scheme-module API does
not currently provide that instance. -/
class RightDerivedPushforward {X S : Scheme.{u}} (f : X ⟶ S) where
  hasInjectiveResolutions : CategoryTheory.HasInjectiveResolutions X.Modules

attribute [instance] RightDerivedPushforward.hasInjectiveResolutions

/-- The `i`th right-derived pushforward. -/
noncomputable def higherDirectImage {X S : Scheme.{u}} (f : X ⟶ S)
    (R : RightDerivedPushforward f) (i : ℕ) : X.Modules ⥤ S.Modules :=
  (Scheme.Modules.pushforward f).rightDerived i

/-- Higher direct images of quasi-coherent sheaves vanish for affine morphisms. -/
theorem relative_affine_higher_direct_image_vanishes {X S : Scheme.{u}}
    (f : X ⟶ S) [IsAffineHom f] (R : RightDerivedPushforward f)
    (M : X.Modules) [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) M]
    {i : ℕ} (hi : 0 < i) :
    IsZero ((higherDirectImage f R i).obj M) := by
  sorry

/-- Cohomology is unchanged by an affine relative pushforward. -/
theorem relative_affine_cohomology_comparison {X S : Scheme.{u}}
    (f : X ⟶ S) [IsAffineHom f]
    (M : X.Modules) [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) M]
    [SchemeCohomologyData X] [SchemeCohomologyData S] (i : ℕ) :
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
  sorry

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
    [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) M] [SchemeCohomologyData X]
    (n : ℕ) :
    Nonempty
      (cechCohomologyObject M (fun i => (𝒰.cover.f i).opensRange) n ≅
        schemeCohomologyObject M n) := by
  sorry

end Formalization.«Books.Coherent».Unit01
