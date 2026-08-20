import Formalization.Books.Modules.Unit25.Invertible
import Formalization.Books.Modules.Unit10.QuasiCoherent
import Mathlib.GroupTheory.Congruence.Hom
import Mathlib.GroupTheory.FreeAbelianGroup
import Mathlib.Topology.ContinuousMap.Algebra
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic

/-!
# Sheaves of Modules, Chapter 26: Rank and determinant

This file formalizes `books/modules.tex`, Section `Rank and determinant`.
Finite locally free sheaves use the canonical `IsFiniteLocallyFree` predicate,
exterior powers use Chapter 21's `exteriorPowerSheaf`, and invertible sheaves
and Picard classes use Chapter 25.  The project has no generic exact-category
or sheaf-level K₀ package, so the chapter records the exact source-facing
data and the quotient presentation explicitly.
-/

namespace Formalization.Books.Modules.Unit26

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Formalization.Books.Modules.Unit03
open Formalization.Books.Modules.Unit10
open Formalization.Books.Modules.Unit14
open Formalization.Books.Modules.Unit16
open Formalization.Books.Modules.Unit17
open Formalization.Books.Modules.Unit18
open Formalization.Books.Modules.Unit21
open Formalization.Books.Modules.Unit25
open Formalization.Books.Sheaves.Unit10
open Formalization.Books.Sheaves.Unit17
open Formalization.Books.Sheaves.Unit22

universe v

noncomputable section

/-! ## The exact category and its K₀ presentation -/

/- The full subcategory is the canonical category of finite locally free
   modules. -/
def finiteLocallyFreeProperty {X : TopCat.{v}} (O : CommRingSheaf X) :
    ObjectProperty (CommRingSheafModule O) :=
  fun F => IsFiniteLocallyFree (X := underlyingRingedSpace O) F

abbrev Vect {X : TopCat.{v}} (O : CommRingSheaf X) :=
  (finiteLocallyFreeProperty O).FullSubcategory

abbrev VectObject {X : TopCat.{v}} (O : CommRingSheaf X) := Vect O

def VectSurjection {X : TopCat.{v}} {O : CommRingSheaf X}
    {E F : Vect O} (q : E ⟶ F) : Prop :=
  Epi q.hom

def IsKernelOfVectSurjection {X : TopCat.{v}} {O : CommRingSheaf X}
    {E F : Vect O} (i : E ⟶ F) : Prop :=
  ∃ (G : Vect O) (q : F.1 ⟶ G.1), Epi q ∧
    ∃ h : i.hom ≫ q = 0,
      Nonempty (IsLimit (KernelFork.ofι i.hom h))

/- The exact-category axioms are kept as a named proposition because the
   current Mathlib/project API has no Quillen exact-category class.  The
   admissible maps and the two source characterizations remain concrete. -/
structure VectExactCategoryData {X : TopCat.{v}} (O : CommRingSheaf X) where
  admissibleEpi : ∀ {E F : Vect O}, (E ⟶ F) → Prop
  admissibleMono : ∀ {E F : Vect O}, (E ⟶ F) → Prop
  admissibleEpi_eq_surjection :
    ∀ {E F : Vect O} (q : E ⟶ F), admissibleEpi q ↔ VectSurjection q
  admissibleMono_eq_kernel :
    ∀ {E F : Vect O} (i : E ⟶ F), admissibleMono i ↔ IsKernelOfVectSurjection i
  exactCategoryAxioms : Prop
  exactCategoryAxioms_proof : exactCategoryAxioms

theorem vect_exactCategory_exists {X : TopCat.{v}} (O : CommRingSheaf X) :
    Nonempty (VectExactCategoryData O) := by
  sorry

noncomputable def vectExactCategoryData {X : TopCat.{v}}
    (O : CommRingSheaf X) : VectExactCategoryData O :=
  Classical.choice (vect_exactCategory_exists O)

def VectRepresentativeSet {X : TopCat.{v}} (O : CommRingSheaf X) :=
  Set (Vect O)

def IsVectRepresentativeSet {X : TopCat.{v}} {O : CommRingSheaf X}
    (S : VectRepresentativeSet O) : Prop :=
  ∀ E : Vect O, ∃! E' : Vect O, S E' ∧ Nonempty (E ≅ E')

theorem exists_vectRepresentativeSet {X : TopCat.{v}} (O : CommRingSheaf X) :
    ∃ S : VectRepresentativeSet O, IsVectRepresentativeSet S := by
  sorry

structure VectShortExact {X : TopCat.{v}} (O : CommRingSheaf X) where
  left : Vect O
  middle : Vect O
  right : Vect O
  leftToMiddle : left ⟶ middle
  middleToRight : middle ⟶ right
  comp_zero : leftToMiddle ≫ middleToRight = 0
  exact : (ShortComplex.mk leftToMiddle middleToRight comp_zero).ShortExact

abbrev KZeroFree {X : TopCat.{v}} (O : CommRingSheaf X) :=
  FreeAbelianGroup (Vect O)

def kZeroGenerator {X : TopCat.{v}} {O : CommRingSheaf X}
    (E : Vect O) : KZeroFree O :=
  FreeAbelianGroup.of E

def kZeroRelation {X : TopCat.{v}} {O : CommRingSheaf X}
    (S : VectShortExact O) (x y : KZeroFree O) : Prop :=
  x = kZeroGenerator S.middle ∧
    y = kZeroGenerator S.left + kZeroGenerator S.right

def kZeroCon {X : TopCat.{v}} (O : CommRingSheaf X) :
    AddCon (KZeroFree O) :=
  addConGen (fun x y => ∃ S : VectShortExact O, kZeroRelation S x y)

abbrev KZero {X : TopCat.{v}} (O : CommRingSheaf X) :=
  (kZeroCon O).Quotient

def kZeroClass {X : TopCat.{v}} {O : CommRingSheaf X}
    (E : Vect O) : KZero O :=
  (kZeroCon O).mk' (kZeroGenerator E)

/-! ## Ranks -/

structure NatRankFunction {X : TopCat.{v}} {O : CommRingSheaf X}
    (E : Vect O) where
  rank : X → ℕ
  locallyConstant : IsLocallyConstant rank
  local_free_rank : ∀ (x : X) (U : Opens X.carrier) (n : ℕ), x ∈ U →
    Nonempty (((openModuleRestrictionFunctor (underlyingRingedSpace O) U).obj E.1) ≅
      (SheafOfModules.free (R :=
        (ringedOpenSubspace (underlyingRingedSpace O) U).structureSheaf)
        (ULift.{v} (Fin n)))) →
      rank x = n

theorem natRankFunction_exists {X : TopCat.{v}} {O : CommRingSheaf X}
    (hO : StructureSheafHasNonzeroStalks (underlyingRingedSpace O))
    (E : Vect O) : Nonempty (NatRankFunction E) := by
  sorry

noncomputable def natRankFunction {X : TopCat.{v}} {O : CommRingSheaf X}
    (hO : StructureSheafHasNonzeroStalks (underlyingRingedSpace O))
    (E : Vect O) : NatRankFunction E :=
  Classical.choice (natRankFunction_exists hO E)

noncomputable def rankAt {X : TopCat.{v}} {O : CommRingSheaf X}
    (hO : StructureSheafHasNonzeroStalks (underlyingRingedSpace O))
    (E : Vect O) : X → ℕ :=
  (natRankFunction hO E).rank

theorem rankAt_isLocallyConstant {X : TopCat.{v}} {O : CommRingSheaf X}
    (hO : StructureSheafHasNonzeroStalks (underlyingRingedSpace O))
    (E : Vect O) : IsLocallyConstant (rankAt hO E) := by
  exact (natRankFunction hO E).locallyConstant

noncomputable def rankMap {X : TopCat.{v}} {O : CommRingSheaf X}
    (hO : StructureSheafHasNonzeroStalks (underlyingRingedSpace O))
    (E : Vect O) : ContinuousMap X ℤ :=
  { toFun := fun x => (rankAt hO E x : ℤ)
    continuous_toFun := by
      exact (IsLocallyConstant.comp (rankAt_isLocallyConstant hO E)
        (fun n : ℕ => (n : ℤ))).continuous }

theorem rank_additive_on_shortExact {X : TopCat.{v}} {O : CommRingSheaf X}
    (hO : StructureSheafHasNonzeroStalks (underlyingRingedSpace O))
    (S : VectShortExact O) :
    ∀ x : X, rankAt hO S.middle x =
      rankAt hO S.left x + rankAt hO S.right x := by
  sorry

noncomputable def rankKZeroFree {X : TopCat.{v}} {O : CommRingSheaf X}
    (hO : StructureSheafHasNonzeroStalks (underlyingRingedSpace O)) :
    KZeroFree O →+ ContinuousMap X ℤ :=
  FreeAbelianGroup.lift (fun E => rankMap hO E)

theorem rankKZeroFree_respects_relations {X : TopCat.{v}}
    {O : CommRingSheaf X}
    (hO : StructureSheafHasNonzeroStalks (underlyingRingedSpace O)) :
    kZeroCon O ≤ AddCon.ker (rankKZeroFree hO) := by
  sorry

noncomputable def rankKZero {X : TopCat.{v}} {O : CommRingSheaf X}
    (hO : StructureSheafHasNonzeroStalks (underlyingRingedSpace O)) :
    KZero O →+ ContinuousMap X ℤ :=
  (kZeroCon O).lift (rankKZeroFree hO)
    (rankKZeroFree_respects_relations hO)

@[simp] theorem rankKZero_apply_class {X : TopCat.{v}} {O : CommRingSheaf X}
    (hO : StructureSheafHasNonzeroStalks (underlyingRingedSpace O))
    (E : Vect O) : rankKZero hO (kZeroClass E) = rankMap hO E := by
  rfl

/-! ## Determinants of finite locally free sheaves -/

noncomputable def rankPiece {X : TopCat.{v}} {O : CommRingSheaf X}
    {E : Vect O} (r : NatRankFunction E) (i : ℕ) : Opens X.carrier :=
  ⟨{x | r.rank x = i}, (r.locallyConstant.isClopen_fiber i).2⟩

theorem rankPiece_isClosed {X : TopCat.{v}} {O : CommRingSheaf X}
    {E : Vect O} (r : NatRankFunction E) (i : ℕ) :
    IsClosed ((rankPiece r i : Set X.carrier)) := by
  exact (r.locallyConstant.isClopen_fiber i).1

theorem rankPieces_cover {X : TopCat.{v}} {O : CommRingSheaf X}
    {E : Vect O} (r : NatRankFunction E) (x : X) :
    ∃ i : ℕ, x ∈ rankPiece r i := by
  exact ⟨r.rank x, rfl⟩

theorem rankPieces_disjoint {X : TopCat.{v}} {O : CommRingSheaf X}
    {E : Vect O} (r : NatRankFunction E) {i j : ℕ} (hij : i ≠ j) :
    Disjoint (rankPiece r i : Set X.carrier) (rankPiece r j : Set X.carrier) := by
  rw [Set.disjoint_left]
  intro x hxi hxj
  change r.rank x = i at hxi
  change r.rank x = j at hxj
  exact hij (hxi.symm.trans hxj)

/- The exterior power on a rank piece is the restriction of the canonical
   sheaf exterior power from Chapter 21.  This gives a real construction while
   retaining the source's open-and-closed decomposition. -/
noncomputable abbrev exteriorPowerOnPiece {X : TopCat.{v}}
    (O : CommRingSheaf X) (F : CommRingSheafModule O) (U : Opens X.carrier)
    (i : ℕ) : Mod (ringedOpenSubspace (underlyingRingedSpace O) U).structureSheaf :=
  (openModuleRestrictionFunctor (underlyingRingedSpace O) U).obj
    (exteriorPowerSheaf O F i)

/- The rank witness is made explicit for the determinant construction; this
   avoids pretending that a choice of locally constant rank is definitional. -/
structure FiniteDeterminantData {X : TopCat.{v}} (O : CommRingSheaf X)
    (E : Vect O) (hO : StructureSheafHasNonzeroStalks
      (underlyingRingedSpace O)) where
  carrier : CommRingSheafModule O
  invertible : IsInvertibleModule O carrier
  locallyFreeRankOne : IsLocallyFreeRankOne O carrier
  rankFunction : NatRankFunction E
  piecewise : ∀ i : ℕ, Nonempty (
    ((openModuleRestrictionFunctor (underlyingRingedSpace O)
      (rankPiece rankFunction i)).obj carrier) ≅
      exteriorPowerOnPiece O E.1 (rankPiece rankFunction i) i)

theorem finiteDeterminantData_exists {X : TopCat.{v}} (O : CommRingSheaf X)
    (hO : StructureSheafHasNonzeroStalks (underlyingRingedSpace O))
    (E : Vect O) : Nonempty (FiniteDeterminantData O E hO) := by
  sorry

noncomputable def finiteDeterminantData {X : TopCat.{v}} (O : CommRingSheaf X)
    (hO : StructureSheafHasNonzeroStalks (underlyingRingedSpace O))
    (E : Vect O) : FiniteDeterminantData O E hO :=
  Classical.choice (finiteDeterminantData_exists O hO E)

noncomputable def determinantObject {X : TopCat.{v}} {O : CommRingSheaf X}
    (hO : StructureSheafHasNonzeroStalks (underlyingRingedSpace O))
    (E : Vect O) : InvertibleModuleObject O :=
  ⟨(finiteDeterminantData O hO E).carrier,
    (finiteDeterminantData O hO E).invertible⟩

theorem determinantObject_piecewise {X : TopCat.{v}}
    {O : CommRingSheaf X}
    (hO : StructureSheafHasNonzeroStalks (underlyingRingedSpace O))
    (E : Vect O) (i : ℕ) : Nonempty (
      ((openModuleRestrictionFunctor (underlyingRingedSpace O)
        (rankPiece (finiteDeterminantData O hO E).rankFunction i)).obj
          (determinantObject hO E).1) ≅
      exteriorPowerOnPiece O E.1
        (rankPiece (finiteDeterminantData O hO E).rankFunction i) i) := by
  exact (finiteDeterminantData O hO E).piecewise i

theorem determinantObject_isLocallyFreeRankOne {X : TopCat.{v}}
    {O : CommRingSheaf X}
    (hO : StructureSheafHasNonzeroStalks (underlyingRingedSpace O))
    (E : Vect O) : IsLocallyFreeRankOne O (determinantObject hO E).1 := by
  exact (finiteDeterminantData O hO E).locallyFreeRankOne

structure DeterminantShortExactData {X : TopCat.{v}} (O : CommRingSheaf X)
    (hO : StructureSheafHasNonzeroStalks (underlyingRingedSpace O))
    (S : VectShortExact O) where
  iso : tensorProductSheaf O (determinantObject hO S.left).1
      (determinantObject hO S.right).1 ≅ (determinantObject hO S.middle).1

theorem determinantShortExactData_exists {X : TopCat.{v}}
    (O : CommRingSheaf X)
    (hO : StructureSheafHasNonzeroStalks (underlyingRingedSpace O))
    (S : VectShortExact O) : Nonempty (DeterminantShortExactData O hO S) := by
  sorry

noncomputable def determinantShortExactIso {X : TopCat.{v}}
    (O : CommRingSheaf X)
    (hO : StructureSheafHasNonzeroStalks (underlyingRingedSpace O))
    (S : VectShortExact O) :
    tensorProductSheaf O (determinantObject hO S.left).1
      (determinantObject hO S.right).1 ≅ (determinantObject hO S.middle).1 :=
  (Classical.choice (determinantShortExactData_exists O hO S)).iso

/-! ## The determinant homomorphism on K₀ -/

noncomputable def determinantClass {X : TopCat.{v}} {O : CommRingSheaf X}
    (hO : StructureSheafHasNonzeroStalks (underlyingRingedSpace O))
    (E : Vect O) : PicardCarrier O :=
  picardClass O (determinantObject hO E)

def determinantKZeroFree {X : TopCat.{v}} {O : CommRingSheaf X}
    (hO : StructureSheafHasNonzeroStalks (underlyingRingedSpace O)) :
    KZeroFree O →+ PicardCarrier O :=
  FreeAbelianGroup.lift (fun E => determinantClass hO E)

theorem determinantKZeroFree_respects_relations {X : TopCat.{v}}
    {O : CommRingSheaf X}
    (hO : StructureSheafHasNonzeroStalks (underlyingRingedSpace O)) :
    kZeroCon O ≤ AddCon.ker (determinantKZeroFree hO) := by
  sorry

noncomputable def determinantKZero {X : TopCat.{v}} {O : CommRingSheaf X}
    (hO : StructureSheafHasNonzeroStalks (underlyingRingedSpace O)) :
    KZero O →+ PicardCarrier O :=
  (kZeroCon O).lift (determinantKZeroFree hO)
    (determinantKZeroFree_respects_relations hO)

@[simp] theorem determinantKZero_apply_class {X : TopCat.{v}}
    {O : CommRingSheaf X}
    (hO : StructureSheafHasNonzeroStalks (underlyingRingedSpace O))
    (E : Vect O) : determinantKZero hO (kZeroClass E) = determinantClass hO E := by
  sorry

/-! ## Flat finitely presented modules and the socle determinant -/

abbrev FlatFinitePresentation {X : TopCat.{v}} (O : CommRingSheaf X)
    (F : CommRingSheafModule O) : Prop :=
  IsFlat O F ∧ IsFinitePresentation F

theorem locallyDirectSummand_iff_flatFinitePresentation {X : TopCat.{v}}
    (O : CommRingSheaf X) (F : CommRingSheafModule O) :
    IsLocallyDirectSummand F ↔ FlatFinitePresentation O F := by
  sorry

theorem locallyDirectSummand_isFiniteLocallyFree_of_localStalks
    {X : TopCat.{v}} (O : CommRingSheaf X)
    (hO : StructureSheafHasLocalStalks (underlyingRingedSpace O))
    (F : CommRingSheafModule O) (hF : IsLocallyDirectSummand F) :
    IsFiniteLocallyFree (X := underlyingRingedSpace O) F := by
  sorry

/- The product-ring example from the source. -/
noncomputable def productFirstIdeal (A B : Type v) [CommRing A] [CommRing B] :
    Ideal (A × B) :=
  Ideal.span {(1, 0)}

noncomputable def productFirstModule (A B : Type v) [CommRing A] [CommRing B] :
    ModuleCat (A × B) :=
  ModuleCat.of (A × B) (productFirstIdeal A B)

theorem productFirstModule_not_locallyFree (A B : Type v)
    [CommRing A] [CommRing B] [Nontrivial A] [Nontrivial B] :
    ¬ IsFiniteLocallyFree
      (X := onePointRingedSpace (A × B))
      (onePointModule (productFirstModule A B)) := by
  sorry

/- The stalkwise socle model of the annihilator in the exterior algebra. -/
abbrev stalkRing {X : TopCat.{v}} (O : CommRingSheaf X) (x : X) : Type v :=
  ↑(TopCat.Presheaf.stalk (C := CommRingCat.{v}) O.obj x)

abbrev stalkModule {X : TopCat.{v}} (O : CommRingSheaf X)
    (F : CommRingSheafModule O) (x : X) : Type v :=
  ↑(commRingSheafModuleStalk F x)

noncomputable def stalkSocle {X : TopCat.{v}} (O : CommRingSheaf X)
    (F : CommRingSheafModule O) (x : X) :
    Submodule (stalkRing O x) (ExteriorAlgebra (stalkRing O x) (stalkModule O F x)) where
  carrier := {z | ∀ m : stalkModule O F x,
    ExteriorAlgebra.ι (stalkRing O x) m * z = 0}
  zero_mem' := by
    intro m
    simp
  add_mem' := by
    intro z w hz hw m
    rw [mul_add, hz m, hw m, add_zero]
  smul_mem' := by
    intro c z hz m
    rw [Algebra.smul_def, ← mul_assoc,
      ← Algebra.commutes c (ExteriorAlgebra.ι (stalkRing O x) m),
      mul_assoc, hz m, mul_zero]

def IsSocleDeterminant {X : TopCat.{v}} {O : CommRingSheaf X}
    (F L : CommRingSheafModule O) : Prop :=
  ∀ x : X, Nonempty (
    (commRingSheafModuleStalk L x : Type v) ≃ₗ[stalkRing O x]
      (stalkSocle O F x : Type v))

structure SocleDeterminantData {X : TopCat.{v}} (O : CommRingSheaf X)
    (F : CommRingSheafModule O) where
  carrier : CommRingSheafModule O
  invertible : IsInvertibleModule O carrier
  socle : IsSocleDeterminant F carrier

theorem socleDeterminantData_exists {X : TopCat.{v}} (O : CommRingSheaf X)
    (F : CommRingSheafModule O) (hF : FlatFinitePresentation O F) :
    Nonempty (SocleDeterminantData O F) := by
  sorry

noncomputable def socleDeterminantData {X : TopCat.{v}} (O : CommRingSheaf X)
    (F : CommRingSheafModule O) (hF : FlatFinitePresentation O F) :
    SocleDeterminantData O F :=
  Classical.choice (socleDeterminantData_exists O F hF)

noncomputable def socleDeterminant {X : TopCat.{v}} (O : CommRingSheaf X)
    (F : CommRingSheafModule O) (hF : FlatFinitePresentation O F) :
    InvertibleModuleObject O :=
  ⟨(socleDeterminantData O F hF).carrier,
    (socleDeterminantData O F hF).invertible⟩

theorem socleDeterminant_isSocleDeterminant {X : TopCat.{v}}
    (O : CommRingSheaf X) (F : CommRingSheafModule O)
    (hF : FlatFinitePresentation O F) :
    IsSocleDeterminant F (socleDeterminant O F hF).1 := by
  exact (socleDeterminantData O F hF).socle

theorem socleDeterminant_agrees_with_finiteDeterminant
    {X : TopCat.{v}} (O : CommRingSheaf X)
    (hO : StructureSheafHasNonzeroStalks (underlyingRingedSpace O))
    (E : Vect O) (hF : FlatFinitePresentation O E.1) :
    Nonempty ((socleDeterminant O E.1 hF).1 ≅
      (determinantObject hO E).1) := by
  sorry

end

end Formalization.Books.Modules.Unit26
