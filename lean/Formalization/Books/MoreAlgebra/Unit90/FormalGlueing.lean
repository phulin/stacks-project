import Formalization.Books.MoreAlgebra.Unit89.TorsionModules
import Formalization.Books.MoreAlgebra.Unit29.KoszulComplex
import Formalization.Books.Algebra.Unit71.ExtGroups
import Formalization.Books.MoreAlgebra.Unit05.FibreProductsOfRingsI
import Formalization.Books.Algebra.Unit97.CompletionForNoetherianRings
import Mathlib.Algebra.Category.ModuleCat.Localization
import Mathlib.RingTheory.AdicCompletion.Algebra
import Mathlib.RingTheory.Flat.Basic

/-!
# More on Algebra, Chapter 90: Formal glueing of module categories

This file records the commutative-algebra interfaces in the chapter section.
The torsion predicate, localizations, tensor products, Ext groups, and adic
completion are the canonical constructions from Mathlib and earlier chapters.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open Formalization.Books.MoreAlgebra.Unit53
open Formalization.Books.MoreAlgebra.Unit89
open scoped TensorProduct

universe u v

namespace Formalization.Books.MoreAlgebra.Unit90

/-! ## Flat maps and torsion modules -/

abbrev moduleCategory (R : Type u) [CommRing R] := ModuleCat.{u} R

def baseChangeFunctor {R S : Type u} [CommRing R] [CommRing S]
    (φ : R →+* S) : ModuleCat.{u} R ⥤ ModuleCat.{u} S :=
  letI : Algebra R S := φ.toAlgebra
  ModuleCat.extendScalars φ

def annihilatedByIdeal {R : Type u} [CommRing R] (I : Ideal R)
    (M : ModuleCat.{u} R) : Prop :=
  ∀ x : M, ∀ a : R, a ∈ I → a • x = 0

def baseChangeFaithfulOn {R S : Type u} [CommRing R] [CommRing S]
    (φ : R →+* S) (P : ModuleCat.{u} R → Prop) : Prop :=
  ∀ (M N : ModuleCat.{u} R), P M → P N →
    ∀ f g : M ⟶ N,
      (baseChangeFunctor φ).map f = (baseChangeFunctor φ).map g → f = g

def flatRingHom {R S : Type u} [CommRing R] [CommRing S]
    (φ : R →+* S) : Prop :=
  RingHom.Flat φ

def faithfullyFlatRingHom {R S : Type u} [CommRing R] [CommRing S]
    (φ : R →+* S) : Prop :=
  RingHom.FaithfullyFlat φ

def idealQuotientMap {R S : Type u} [CommRing R] [CommRing S]
    (φ : R →+* S) (I : Ideal R) : R ⧸ I →+* S ⧸ Ideal.map φ I :=
  Ideal.quotientMap (Ideal.map φ I) φ Ideal.le_comap_map

def quotientSpectrumMapSurjective {R S : Type u} [CommRing R] [CommRing S]
    (φ : R →+* S) : Prop :=
  Function.Surjective (PrimeSpectrum.comap φ)

theorem characterizeFlatnessOnTorsion
    {R S : Type u} [CommRing R] [CommRing S]
    (φ : R →+* S) (I : Ideal R) :
    List.TFAE
      [flatRingHom φ ∧ faithfullyFlatRingHom (idealQuotientMap φ I),
       flatRingHom φ ∧ quotientSpectrumMapSurjective (idealQuotientMap φ I),
       flatRingHom φ ∧ baseChangeFaithfulOn φ (annihilatedByIdeal I),
       flatRingHom φ ∧
         baseChangeFaithfulOn φ (fun M => IsIPowerTorsion I (M : Type u))] := by
  sorry

def tensorUnitMapOfRingHom {R S M : Type u} [CommRing R] [CommRing S]
    [AddCommGroup M] [Module R M] (φ : R →+* S) :
    letI : Algebra R S := φ.toAlgebra
    M →ₗ[R] M ⊗[R] S :=
  letI : Algebra R S := φ.toAlgebra
  tensorUnitMap (R := R) (S := S) (M := M)

def neighbourhoodIsomorphismProperty
    {R S : Type u} [CommRing R] [CommRing S]
    (φ : R →+* S) (I : Ideal R) : Prop :=
  ∀ (M : ModuleCat.{u} R), IsIPowerTorsion I (M : Type u) →
    Function.Bijective (tensorUnitMapOfRingHom (M := (M : Type u)) φ)

theorem neighbourhoodIsomorphism_iff
    {R S : Type u} [CommRing R] [CommRing S]
    (φ : R →+* S) (I : Ideal R)
    (hφ : flatRingHom φ)
    (hfaith : faithfullyFlatRingHom (idealQuotientMap φ I)) :
    neighbourhoodIsomorphismProperty φ I ↔
      Function.Bijective (idealQuotientMap φ I) := by
  sorry

abbrev torsionModuleCategory (R : Type u) [CommRing R] (I : Ideal R) :=
  iPowerTorsionModuleCategory R I

theorem neighbourhoodBaseChangeHomEquiv
    {R S : Type u} [CommRing R] [CommRing S]
    (φ : R →+* S) (I : Ideal R) (hφ : flatRingHom φ)
    (hquot : Function.Bijective (idealQuotientMap φ I))
    (M N : ModuleCat.{u} R)
    (hMN : IsIPowerTorsion I (M : Type u) ∨
      IsIPowerTorsion I (N : Type u)) :
    Nonempty ((M ⟶ N) ≃ ((baseChangeFunctor φ).obj M ⟶
      (baseChangeFunctor φ).obj N)) := by
  sorry

theorem neighbourhoodBaseChange_torsionSubmodule
    {R S : Type u} [CommRing R] [CommRing S]
    (φ : R →+* S) (I : Ideal R) (hφ : flatRingHom φ)
    (hquot : Function.Bijective (idealQuotientMap φ I))
    (M : ModuleCat.{u} R) :
    Nonempty ((idealPowerTorsionSubmoduleInfinity I :
        Submodule R (M : Type u)) ≃ₗ[R]
      (letI : Algebra R S := φ.toAlgebra
       letI : Module R ((baseChangeFunctor φ).obj M : Type u) :=
         Module.compHom _ φ
       letI : IsScalarTower R S ((baseChangeFunctor φ).obj M : Type u) :=
         IsScalarTower.of_compHom R S _
       (idealPowerTorsionSubmoduleInfinity
          (M := ((baseChangeFunctor φ).obj M : Type u)) (Ideal.map φ I)).restrictScalars R)) := by
  sorry

theorem neighbourhoodBaseChange_torsionCategoryEquivalence
    {R S : Type u} [CommRing R] [CommRing S]
    (φ : R →+* S) (I : Ideal R) (hφ : flatRingHom φ)
    (hquot : Function.Bijective (idealQuotientMap φ I)) :
    Nonempty
      (torsionModuleCategory R I ≌
        torsionModuleCategory S (Ideal.map φ I)) := by
  sorry

/-! ## Koszul and Cech interfaces -/

structure KoszulCechQuasiIsomorphismData
    {R S : Type u} [CommRing R] [CommRing S]
    (φ : R →+* S) (I : Ideal R) (r : ℕ) (f : Fin r → R) where
  koszulMap : Prop
  cechMap : Prop
  support : ∀ p : PrimeSpectrum R,
    (∀ i, f i ∈ p.asIdeal) ↔ I ≤ p.asIdeal

theorem mapIdentifiesKoszulAndCech
    {R S : Type u} [CommRing R] [CommRing S]
    (φ : R →+* S) (I : Ideal R) (hφ : flatRingHom φ)
    (hI : I.FG) (r : ℕ) (f : Fin r → R)
    (hV : ∀ p : PrimeSpectrum R,
      (∀ i, f i ∈ p.asIdeal) ↔ I ≤ p.asIdeal) :
    Nonempty (KoszulCechQuasiIsomorphismData φ I r f) := by
  sorry

def naiveKoszulRelationVector {R : Type u} [CommRing R]
    {n : ℕ} (f : Fin n → R) (i j : Fin n) : Fin n → R :=
  f i • Pi.single j 1 - f j • Pi.single i 1

def naiveKoszulRelationSubmodule {R : Type u} [CommRing R]
    {n : ℕ} (f : Fin n → R) : Submodule R (Fin n → R) :=
  Submodule.span R (Set.range (fun ij : Fin n × Fin n =>
    naiveKoszulRelationVector f ij.1 ij.2))

abbrev naiveKoszulModule {R : Type u} [CommRing R]
    {n : ℕ} (f : Fin n → R) :=
  (Fin n → R) ⧸ naiveKoszulRelationSubmodule f

def naiveKoszulModuleGenerator {R : Type u} [CommRing R]
    {n : ℕ} (f : Fin n → R) (i : Fin n) : naiveKoszulModule f :=
  (naiveKoszulRelationSubmodule f).mkQ (Pi.single i 1)

structure NaiveKoszulExactData {R : Type u} [CommRing R]
    {n : ℕ} (f : Fin n → R) where
  K : Submodule R (naiveKoszulModule f)
  map : naiveKoszulModule f →ₗ[R] Ideal.span (Set.range f)
  exact : Function.Exact K.subtype map
  annihilated : ∀ a ∈ Ideal.span (Set.range f), ∀ x : K, a • x = 0

theorem existsNaiveKoszulExactData {R : Type u} [CommRing R]
    {n : ℕ} (f : Fin n → R) : Nonempty (NaiveKoszulExactData f) := by
  sorry

def koszulCycleSubmodule {R N : Type u} [CommRing R]
    [AddCommGroup N] [Module R N] {n : ℕ} (f : Fin n → R) :
    Submodule R (Fin n → N) where
  carrier := {x | ∀ i j, f i • x j = f j • x i}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy i j
    change (∀ i j, f i • x j = f j • x i) at hx
    change (∀ i j, f i • y j = f j • y i) at hy
    simp [smul_add, add_smul, hx i j, hy i j]
  smul_mem' := by
    intro a x hx i j
    change (∀ i j, f i • x j = f j • x i) at hx
    change f i • (a • x j) = f j • (a • x i)
    calc
      f i • (a • x j) = a • (f i • x j) := by
        rw [smul_smul, smul_smul, mul_comm]
      _ = a • (f j • x i) := congrArg (fun z => a • z) (hx i j)
      _ = f j • (a • x i) := by
        rw [smul_smul, smul_smul, mul_comm]

def koszulBoundaryMapAmbient {R N : Type u} [CommRing R]
    [AddCommGroup N] [Module R N] {n : ℕ} (f : Fin n → R) :
    N →ₗ[R] (Fin n → N) where
  toFun x := fun i => f i • x
  map_add' x y := by
    ext i
    simp [add_smul]
  map_smul' a x := by
    ext i
    simp [smul_smul, mul_comm]

def koszulBoundaryMap {R N : Type u} [CommRing R]
    [AddCommGroup N] [Module R N] {n : ℕ} (f : Fin n → R) :
    N →ₗ[R] koszulCycleSubmodule (N := N) f :=
  (koszulBoundaryMapAmbient f).codRestrict (koszulCycleSubmodule f) (by
    intro x
    change ∀ i j, f i • (f j • x) = f j • (f i • x)
    intro i j
    rw [smul_smul, smul_smul, mul_comm])

def koszulBoundarySubmodule {R N : Type u} [CommRing R]
    [AddCommGroup N] [Module R N] {n : ℕ} (f : Fin n → R) :
    Submodule R (koszulCycleSubmodule (N := N) f) :=
  Submodule.map (koszulBoundaryMap f) ⊤

abbrev koszulH1 {R N : Type u} [CommRing R]
    [AddCommGroup N] [Module R N] {n : ℕ} (f : Fin n → R) :=
  (koszulCycleSubmodule (N := N) f : Type u) ⧸
    (koszulBoundarySubmodule (N := N) f)

def koszulH1Annihilated {R N : Type u} [CommRing R]
    [AddCommGroup N] [Module R N] {n : ℕ} (f : Fin n → R) : Prop :=
  ∀ a ∈ Ideal.span (Set.range f),
    ∀ x : koszulH1 (N := N) f, a • x = 0

structure ExactAddCommGroupSequence (A : Type v) (B C : Type u)
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup C] where
  f : A →+ B
  g : B →+ C
  exact : Function.Exact f g

abbrev ExtOne {R : Type u} [CommRing R] (M N : ModuleCat.{u} R) :=
  Formalization.Books.Homology.Unit06.Ext M N

structure ExplicitExtData {R N : Type u} [CommRing R]
    [AddCommGroup N] [Module R N] {n : ℕ} (f : Fin n → R) where
  K : Submodule R (naiveKoszulModule f)
  K_annihilated : ∀ a ∈ Ideal.span (Set.range f), ∀ x : K, a • x = 0
  sequence : ExactAddCommGroupSequence
    (ExtOne (ModuleCat.of R (R ⧸ Ideal.span (Set.range f)))
      (ModuleCat.of R N))
    (koszulH1 (N := N) f)
    (K →ₗ[R] N)

theorem explicitExtSequence
    {R N : Type u} [CommRing R] [AddCommGroup N] [Module R N]
    {n : ℕ} (f : Fin n → R) :
    Nonempty (ExplicitExtData (N := N) f) := by
  sorry

theorem koszulH1_annihilated
    {R N : Type u} [CommRing R] [AddCommGroup N] [Module R N]
    {n : ℕ} (f : Fin n → R) : koszulH1Annihilated (N := N) f := by
  sorry

/-! ## Extensions and the formal-glueing complex -/

structure NeighbourhoodExtensionData
    {R S : Type u} [CommRing R] [CommRing S]
    (φ : R →+* S) (M N : ModuleCat.{u} R) where
  extension : ShortComplex (ModuleCat.{u} S)
  exact : extension.ShortExact
  left : extension.X₁ ≅ (baseChangeFunctor φ).obj N
  right : extension.X₃ ≅ (baseChangeFunctor φ).obj M

structure NeighbourhoodExtensionLift
    {R S : Type u} [CommRing R] [CommRing S]
    {φ : R →+* S} {M N : ModuleCat.{u} R}
    (E : NeighbourhoodExtensionData φ M N) where
  lifted : ShortComplex (ModuleCat.{u} R)
  exact : lifted.ShortExact
  leftIso : (baseChangeFunctor φ).obj lifted.X₁ ≅ E.extension.X₁
  middleIso : (baseChangeFunctor φ).obj lifted.X₂ ≅ E.extension.X₂
  rightIso : (baseChangeFunctor φ).obj lifted.X₃ ≅ E.extension.X₃
  left_comm : (baseChangeFunctor φ).map lifted.f ≫ middleIso.hom =
    leftIso.hom ≫ E.extension.f
  right_comm : (baseChangeFunctor φ).map lifted.g ≫ rightIso.hom =
    middleIso.hom ≫ E.extension.g

theorem neighbourhoodExtensions
    {R S : Type u} [CommRing R] [CommRing S]
    (φ : R →+* S) (I : Ideal R) (hφ : flatRingHom φ)
    (hquot : Function.Bijective (idealQuotientMap φ I))
    (M N : ModuleCat.{u} R)
    (hM : IsIPowerTorsion I (M : Type u)) :
    ∀ E : NeighbourhoodExtensionData φ M N,
      Nonempty (NeighbourhoodExtensionLift E) := by
  sorry

structure FormalGlueingApplicationLeftData
    {R S : Type u} [CommRing R] [CommRing S]
    (φ : R →+* S) (I : Ideal R)
    (N : ModuleCat.{u} R) (M' : ModuleCat.{u} S) where
  map : M' ⟶ (baseChangeFunctor φ).obj N
  kernelTorsion : IsIPowerTorsion (Ideal.map φ I)
    (LinearMap.ker map.hom : Type u)
  cokernelTorsion : IsIPowerTorsion (Ideal.map φ I)
    ((cokernel map : ModuleCat.{u} S) : Type u)
  liftedModule : ModuleCat.{u} R
  liftedMap : liftedModule ⟶ N
  comparison : (baseChangeFunctor φ).obj liftedModule ≅ M'
  comm : comparison.hom ≫ map = (baseChangeFunctor φ).map liftedMap
  kernelIso : Nonempty ((LinearMap.ker map.hom : Type u) ≃+
    (LinearMap.ker liftedMap.hom : Type u))
  cokernelIso : Nonempty (((cokernel map : ModuleCat.{u} S) : Type u) ≃+
    ((cokernel liftedMap : ModuleCat.{u} R) : Type u))

structure FormalGlueingApplicationRightData
    {R S : Type u} [CommRing R] [CommRing S]
    (φ : R →+* S) (I : Ideal R)
    (M : ModuleCat.{u} R) (N' : ModuleCat.{u} S) where
  map : (baseChangeFunctor φ).obj M ⟶ N'
  kernelTorsion : IsIPowerTorsion (Ideal.map φ I)
    (LinearMap.ker map.hom : Type u)
  cokernelTorsion : IsIPowerTorsion (Ideal.map φ I)
    ((cokernel map : ModuleCat.{u} S) : Type u)
  liftedModule : ModuleCat.{u} R
  liftedMap : M ⟶ liftedModule
  comparison : (baseChangeFunctor φ).obj liftedModule ≅ N'
  comm : (baseChangeFunctor φ).map liftedMap ≫ comparison.hom = map
  kernelIso : Nonempty ((LinearMap.ker map.hom : Type u) ≃+
    (LinearMap.ker liftedMap.hom : Type u))
  cokernelIso : Nonempty (((cokernel map : ModuleCat.{u} S) : Type u) ≃+
    ((cokernel liftedMap : ModuleCat.{u} R) : Type u))

theorem applicationFormalGlueing_left
    {R S : Type u} [CommRing R] [CommRing S]
    (φ : R →+* S) (I : Ideal R) (hφ : flatRingHom φ)
    (hquot : Function.Bijective (idealQuotientMap φ I))
    (N : ModuleCat.{u} R) (M' : ModuleCat.{u} S)
    (map : M' ⟶ (baseChangeFunctor φ).obj N)
    (hker : IsIPowerTorsion (Ideal.map φ I)
      (LinearMap.ker map.hom : Type u))
    (hcoker : IsIPowerTorsion (Ideal.map φ I)
      ((cokernel map : ModuleCat.{u} S) : Type u)) :
    Nonempty (FormalGlueingApplicationLeftData φ I N M') := by
  sorry

theorem applicationFormalGlueing_right
    {R S : Type u} [CommRing R] [CommRing S]
    (φ : R →+* S) (I : Ideal R) (hφ : flatRingHom φ)
    (hquot : Function.Bijective (idealQuotientMap φ I))
    (M : ModuleCat.{u} R) (N' : ModuleCat.{u} S)
    (map : (baseChangeFunctor φ).obj M ⟶ N')
    (hker : IsIPowerTorsion (Ideal.map φ I)
      (LinearMap.ker map.hom : Type u))
    (hcoker : IsIPowerTorsion (Ideal.map φ I)
      ((cokernel map : ModuleCat.{u} S) : Type u)) :
    Nonempty (FormalGlueingApplicationRightData φ I M N') := by
  sorry

structure GlueingComplexData {R S : Type u} [CommRing R] [CommRing S]
    {t : ℕ} (φ : R →+* S) (M : ModuleCat.{u} R) where
  f : Fin t → R
  complex : ShortComplex (ModuleCat.{u} R)
  left : complex.X₁ ≅ M
  exact : complex.ShortExact

theorem recoverModuleFromGlueingData
    {R S : Type u} [CommRing R] [CommRing S]
    {t : ℕ}
    (φ : R →+* S) (I : Ideal R) (hφ : flatRingHom φ)
    (hquot : Function.Bijective (idealQuotientMap φ I))
    (M : ModuleCat.{u} R) :
    Nonempty (GlueingComplexData (t := t) φ M) := by
  sorry

/-! ## Glueing data, equivalence, and base change -/

def formalNeighbourhoodLocalizationFunctor
    {R S : Type u} [CommRing R] [CommRing S]
    (φ : R →+* S) (f : R) :
    ModuleCat.{u} S ⥤ ModuleCat.{u} (Localization.Away (φ f)) :=
  letI : Algebra S (Localization.Away (φ f)) :=
    (algebraMap S (Localization.Away (φ f))).toAlgebra
  ModuleCat.extendScalars (algebraMap S (Localization.Away (φ f)))

def openLocalizationBaseChangeFunctor
    {R S : Type u} [CommRing R] [CommRing S]
    (φ : R →+* S) (f : R) :
    ModuleCat.{u} (Localization.Away f) ⥤
      ModuleCat.{u} (Localization.Away (φ f)) :=
  letI : Algebra (Localization.Away f) (Localization.Away (φ f)) :=
    (Localization.awayMap φ f).toAlgebra
  ModuleCat.extendScalars (Localization.awayMap φ f)

structure GlueingObject {R S : Type u} [CommRing R] [CommRing S]
    {t : ℕ} (φ : R →+* S) (f : Fin t → R) where
  moduleOnFormalNeighbourhood : ModuleCat.{u} S
  moduleOnOpen : ∀ i, ModuleCat.{u} (Localization.Away (f i))
  transition : ∀ i j, AddEquiv (moduleOnOpen i) (moduleOnOpen j)
  overlap : ∀ i, AddEquiv moduleOnFormalNeighbourhood (moduleOnOpen i)
  overlapIso : ∀ i,
    (formalNeighbourhoodLocalizationFunctor φ (f i)).obj
        moduleOnFormalNeighbourhood ≅
      (openLocalizationBaseChangeFunctor φ (f i)).obj (moduleOnOpen i)
  cocycle : ∀ i j k, (transition i j).trans (transition j k) = transition i k

structure GlueingMorphism {R S : Type u} [CommRing R] [CommRing S]
    {t : ℕ} {φ : R →+* S} {f : Fin t → R}
    (X Y : GlueingObject φ f) where
  onFormalNeighbourhood : X.moduleOnFormalNeighbourhood ⟶
    Y.moduleOnFormalNeighbourhood
  onOpen : ∀ i, X.moduleOnOpen i ⟶ Y.moduleOnOpen i
  compatibleTransition : ∀ (i j : Fin t) (x : X.moduleOnOpen i),
    (Y.transition i j) ((onOpen i).hom x) =
      (onOpen j).hom ((X.transition i j) x)
  compatibleOverlap : ∀ (i : Fin t) (x : X.moduleOnFormalNeighbourhood),
    (Y.overlap i) ((onFormalNeighbourhood).hom x) =
      (onOpen i).hom ((X.overlap i) x)
  compatibleOverlapIso : ∀ i,
    (formalNeighbourhoodLocalizationFunctor φ (f i)).map onFormalNeighbourhood ≫
        (Y.overlapIso i).hom =
      (X.overlapIso i).hom ≫
        (openLocalizationBaseChangeFunctor φ (f i)).map (onOpen i)

@[ext]
theorem GlueingMorphism.ext
    {R S : Type u} [CommRing R] [CommRing S]
    {t : ℕ} {φ : R →+* S} {f : Fin t → R}
    {X Y : GlueingObject φ f} (g h : GlueingMorphism X Y)
    (hFormal : g.onFormalNeighbourhood = h.onFormalNeighbourhood)
    (hOpen : ∀ i, g.onOpen i = h.onOpen i) : g = h := by
  cases g with
  | mk gFormal gOpen gTransition gOverlap =>
    cases h with
    | mk hFormal' hOpen' hTransition' hOverlap' =>
      simp only [GlueingMorphism.mk.injEq] at hFormal hOpen ⊢
      exact ⟨hFormal, funext hOpen⟩

abbrev glueingDataCategory
    (R S : Type u) [CommRing R] [CommRing S]
    {t : ℕ} (φ : R →+* S) (f : Fin t → R) :=
  GlueingObject φ f

instance glueingDataCategoryCategory
    {R S : Type u} [CommRing R] [CommRing S]
    {t : ℕ} (φ : R →+* S) (f : Fin t → R) :
    Category (glueingDataCategory R S φ f) where
  Hom X Y := GlueingMorphism X Y
  id X :=
    { onFormalNeighbourhood := 𝟙 _
      onOpen := fun _ => 𝟙 _
      compatibleTransition := by
        intro i j x
        simp
      compatibleOverlap := by
        intro i x
        simp
      compatibleOverlapIso := by
        intro i
        simp }
  comp g h :=
    { onFormalNeighbourhood := g.onFormalNeighbourhood ≫ h.onFormalNeighbourhood
      onOpen := fun i => g.onOpen i ≫ h.onOpen i
      compatibleTransition := by
        intro i j x
        change (GlueingObject.transition _ i j)
            ((h.onOpen i).hom ((g.onOpen i).hom x)) =
          (h.onOpen j).hom ((g.onOpen j).hom
            ((GlueingObject.transition _ i j) x))
        rw [h.compatibleTransition i j ((g.onOpen i).hom x)]
        rw [g.compatibleTransition i j x]
      compatibleOverlap := by
        intro i x
        change (GlueingObject.overlap _ i) ((h.onFormalNeighbourhood).hom
            ((g.onFormalNeighbourhood).hom x)) =
          (h.onOpen i).hom ((g.onOpen i).hom
            ((GlueingObject.overlap _ i) x))
        rw [h.compatibleOverlap i ((g.onFormalNeighbourhood).hom x)]
        rw [g.compatibleOverlap i x]
      compatibleOverlapIso := by
        intro i
        rw [Functor.map_comp, Category.assoc]
        rw [h.compatibleOverlapIso i]
        rw [← Category.assoc, g.compatibleOverlapIso i]
        rw [Category.assoc, ← Functor.map_comp] }
  id_comp := by
    intro X Y g
    apply GlueingMorphism.ext
    · simp
    · intro i
      simp
  comp_id := by
    intro X Y g
    apply GlueingMorphism.ext
    · simp
    · intro i
      simp
  assoc := by
    intro W X Y Z f g h
    apply GlueingMorphism.ext
    · simp [Category.assoc]
    · intro i
      simp [Category.assoc]

def h0AddSubgroup {R S : Type u} [CommRing R] [CommRing S]
    {t : ℕ} {φ : R →+* S} {f : Fin t → R}
    (X : GlueingObject φ f) :
    AddSubgroup (X.moduleOnFormalNeighbourhood × (∀ i, X.moduleOnOpen i)) where
  carrier := {x |
    (∀ i, X.overlap i x.1 = x.2 i) ∧
      (∀ i j, X.transition i j (x.2 i) = x.2 j)}
  zero_mem' := by
    constructor
    · intro i
      simp
    · intro i j
      simp
  add_mem' := by
    intro x y hx hy
    constructor
    · intro i
      change X.overlap i (x.1 + y.1) = x.2 i + y.2 i
      rw [map_add, hx.1 i, hy.1 i]
    · intro i j
      change X.transition i j (x.2 i + y.2 i) = x.2 j + y.2 j
      rw [map_add, hx.2 i j, hy.2 i j]
  neg_mem' := by
    intro x hx
    constructor
    · intro i
      change X.overlap i (-x.1) = -(x.2 i)
      rw [map_neg, hx.1 i]
    · intro i j
      change X.transition i j (-(x.2 i)) = -(x.2 j)
      rw [map_neg, hx.2 i j]

abbrev H0 {R S : Type u} [CommRing R] [CommRing S]
    {t : ℕ} {φ : R →+* S} {f : Fin t → R}
    (X : GlueingObject φ f) : Type u :=
  h0AddSubgroup X

noncomputable def principalGlueingRingSquare
    {R S : Type u} [CommRing R] [CommRing S]
    (φ : R →+* S) (f : R) :
    Formalization.Books.MoreAlgebra.Unit05.RingSquare
      (Localization.Away (φ f)) (Localization.Away f) S R where
  t := Localization.awayMap φ f
  s := algebraMap S (Localization.Away (φ f))
  u := φ
  v := algebraMap R (Localization.Away f)
  comm := by
    ext x
    simp [Localization.awayMap, IsLocalization.Away.map]

structure H0CanAdjunctionData
    {R S : Type u} [CommRing R] [CommRing S]
    {t : ℕ} (φ : R →+* S) (f : Fin t → R) where
  Can : ModuleCat.{u} R ⥤ glueingDataCategory R S φ f
  homEquiv : ∀ (M : ModuleCat.{u} R) (X : GlueingObject φ f),
    (Can.obj M ⟶ X) ≃ ((M : Type u) →+ H0 X)

theorem H0_is_right_adjoint_to_Can
    {R S : Type u} [CommRing R] [CommRing S]
    {t : ℕ} (φ : R →+* S) (f : Fin t → R) :
    Nonempty (H0CanAdjunctionData φ f) := by
  sorry

theorem H0_is_left_quasiInverse
    {R S : Type u} [CommRing R] [CommRing S]
    {t : ℕ} (φ : R →+* S) (f : Fin t → R)
    (hφ : flatRingHom φ)
    (hquot : Function.Bijective (idealQuotientMap φ
      (Ideal.span (Set.range f)))) :
    ∃ D : H0CanAdjunctionData φ f,
      ∀ M : ModuleCat.{u} R,
        Nonempty ((M : Type u) ≃+ H0 (D.Can.obj M)) := by
  sorry

structure GlueingBaseChangeData
    (C : Type u) [Category C]
    {R S R' : Type u} [CommRing R] [CommRing S] [CommRing R']
    {t : ℕ} (φ : R →+* S) (f : Fin t → R) (ψ : R →+* R') where
  can : ModuleCat.{u} R ⥤ glueingDataCategory R S φ f
  h0 : glueingDataCategory R S φ f ⥤ ModuleCat.{u} R
  canBaseChange : ModuleCat.{u} R' ⥤ C
  h0BaseChange : C ⥤ ModuleCat.{u} R'
  moduleBaseChange : ModuleCat.{u} R ⥤ ModuleCat.{u} R'
  glueBaseChange : glueingDataCategory R S φ f ⥤ C
  can_square : can ⋙ glueBaseChange ≅ moduleBaseChange ⋙ canBaseChange
  h0_square : glueBaseChange ⋙ h0BaseChange ≅ h0 ⋙ moduleBaseChange

structure GlueingAbelianExactData
    {R S : Type u} [CommRing R] [CommRing S]
    {t : ℕ} (φ : R →+* S) (f : Fin t → R) where
  Can : ModuleCat.{u} R ⥤ glueingDataCategory R S φ f
  abelian : Abelian (glueingDataCategory R S φ f)
  exact : ∀ (c : ShortComplex (ModuleCat.{u} R)), c.ShortExact →
    ∃ h : Can.PreservesZeroMorphisms,
      letI := h
      (c.map Can).ShortExact
  commutesWithColimits : PreservesColimitsOfSize.{u, u} Can

theorem glueingCategory_isAbelian_and_Can_exact
    {R S : Type u} [CommRing R] [CommRing S]
    {t : ℕ} (φ : R →+* S) (f : Fin t → R)
    (hφ : flatRingHom φ) :
    Nonempty (GlueingAbelianExactData φ f) := by
  sorry

theorem glueing_equivalence_of_unit_ideal
    {R S : Type u} [CommRing R] [CommRing S]
    {t : ℕ} (φ : R →+* S) (f : Fin t → R)
    (hφ : flatRingHom φ)
    (hunit : Ideal.span (Set.range f) = ⊤) :
    Nonempty (ModuleCat.{u} R ≌ glueingDataCategory R S φ f) := by
  sorry

theorem glueing_base_change
    {R S R' : Type u} [CommRing R] [CommRing S] [CommRing R']
    {t : ℕ} (φ : R →+* S) (f : Fin t → R)
    (hφ : flatRingHom φ) (ψ : R →+* R') (hψ : flatRingHom ψ) :
    ∃ (C : Type u) (hC : Category C),
      Nonempty (@GlueingBaseChangeData C hC R S R' _ _ _ t φ f ψ) := by
  sorry

theorem glueing_equivalence
    {R S : Type u} [CommRing R] [CommRing S]
    {t : ℕ} (φ : R →+* S) (f : Fin t → R)
    (hφ : flatRingHom φ)
    (hquot : Function.Bijective (idealQuotientMap φ
      (Ideal.span (Set.range f)))) :
    Nonempty (ModuleCat.{u} R ≌ glueingDataCategory R S φ f) := by
  sorry

theorem proposition_equivalence
    {R S : Type u} [CommRing R] [CommRing S]
    {t : ℕ} (φ : R →+* S) (f : Fin t → R)
    (hφ : flatRingHom φ)
    (hquot : Function.Bijective (idealQuotientMap φ
      (Ideal.span (Set.range f)))) :
    Nonempty (ModuleCat.{u} R ≌ glueingDataCategory R S φ f) := by
  sorry

theorem theorem_formalGlueing
    {R S : Type u} [CommRing R] [CommRing S]
    (φ : R →+* S) (f : R) (hφ : flatRingHom φ)
    (hquot : Function.Bijective
      (idealQuotientMap φ (Ideal.span ({f} : Set R)))) :
    Nonempty (ModuleCat.{u} R ≌
      Formalization.Books.MoreAlgebra.Unit05.ModuleGluingCategory
        (principalGlueingRingSquare φ f)) := by
  sorry

/-! ## Principal and completed specializations -/

theorem formalGlueing_principal
    {R S : Type u} [CommRing R] [CommRing S]
    (φ : R →+* S) (f : R) (hφ : flatRingHom φ)
    (hquot : Function.Bijective
      (idealQuotientMap φ (Ideal.span ({f} : Set R)))) :
    Nonempty (ModuleCat.{u} R ≌
      Formalization.Books.MoreAlgebra.Unit05.ModuleGluingCategory
        (principalGlueingRingSquare φ f)) := by
  sorry

def finiteModuleCategory (R : Type u) [CommRing R] :=
  FGModuleCat.{u} R

def finiteGlueingProperty
    {R R' B B' : Type u} [CommRing R] [CommRing R'] [CommRing B] [CommRing B']
    (D : Formalization.Books.MoreAlgebra.Unit05.RingSquare R R' B B') :
    ObjectProperty (Formalization.Books.MoreAlgebra.Unit05.ModuleGluingCategory D) :=
  fun X =>
    Module.Finite B
        (Formalization.Books.MoreAlgebra.Unit05.moduleGluingLeftObj D X : Type u) ∧
      Module.Finite R'
        (Formalization.Books.MoreAlgebra.Unit05.moduleGluingRightObj D X : Type u)

abbrev finiteGlueingCategory
    {R R' B B' : Type u} [CommRing R] [CommRing R'] [CommRing B] [CommRing B']
    (D : Formalization.Books.MoreAlgebra.Unit05.RingSquare R R' B B') :=
  (finiteGlueingProperty D).FullSubcategory

theorem completion_quotient_iso
    {R : Type u} [CommRing R] [IsNoetherianRing R] (f : R) :
    Function.Bijective (idealQuotientMap
      (algebraMap R (AdicCompletion (Ideal.span ({f} : Set R)) R))
      (Ideal.span ({f} : Set R))) := by
  sorry

theorem proposition_formalGlueing
    {R : Type u} [CommRing R] [IsNoetherianRing R] (f : R) :
    Nonempty (FGModuleCat.{u} R ≌
      finiteGlueingCategory (principalGlueingRingSquare
        (algebraMap R (AdicCompletion (Ideal.span ({f} : Set R)) R)) f)) := by
  sorry

theorem formalGlueing_completion
    {R : Type u} [CommRing R] [IsNoetherianRing R] (f : R) :
    flatRingHom
      (algebraMap R (AdicCompletion (Ideal.span ({f} : Set R)) R)) := by
  exact Formalization.Books.Algebra.Unit97.completion_flat
    (Ideal.span ({f} : Set R))

def modulePropertyDescentStatement
    {R S : Type u} [CommRing R] [CommRing S]
    {t : ℕ} {φ : R →+* S} {f : Fin t → R}
    (P_R : ModuleCat.{u} R → Prop)
    (P_S : ModuleCat.{u} S → Prop)
    (P_open : ∀ i, ModuleCat.{u} (Localization.Away (f i)) → Prop)
    (M : ModuleCat.{u} R) (X : GlueingObject φ f) : Prop :=
  P_R M ↔ P_S X.moduleOnFormalNeighbourhood ∧
    ∀ i, P_open i (X.moduleOnOpen i)

end Formalization.Books.MoreAlgebra.Unit90
