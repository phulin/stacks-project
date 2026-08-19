import Formalization.Books.Cohomology.Unit03
import Formalization.Books.Modules.Unit04.Sections
import Formalization.Books.Sheaves.Unit26.RingedSpaceModules
import Formalization.Books.Derived.Unit11.DerivedCategories
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.RingTheory.LocalRing.Basic

/-!
# Cohomology of Sheaves, Chapter 47: the Berthelot--Ogus operator

This file follows the single source section in chapter 47.  Subsheaves of the
structure sheaf use Mathlib's canonical `Subobject` representation.  The
filtered terms needed by `η` are packaged as explicit data: this records the
source's powers and their inclusions while leaving the later construction of
the corresponding tensor products available to the chapter's derived and
sheaf APIs.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open Opposite
open Set
open TopologicalSpace
open Formalization.Books.Sheaves.Unit10
open Formalization.Books.Sheaves.Unit25
open Formalization.Books.Sheaves.Unit26
open Formalization.Books.Modules.Unit03
open Formalization.Books.Modules.Unit04
open Formalization.Books.Cohomology.Unit03
open Formalization.Books.Derived.Unit08
open Formalization.Books.Derived.Unit11
open Formalization.Books.Homology.Unit13

universe v w

namespace Formalization.Books.Cohomology.Unit47

abbrev RingedSpace := Formalization.Books.Sheaves.Unit25.RingedSpace

/-! ## Invertible ideal sheaves and torsion freeness -/

/- A subobject of the structure sheaf is an ideal sheaf: it is already a
   submodule for the structure-sheaf action. -/
abbrev IdealSheaf (X : RingedSpace.{v}) :=
  Subobject (SheafOfModules.unit X.structureSheaf)

abbrev idealSheafSections {X : RingedSpace.{v}} (I : IdealSheaf X)
    (U : Opens X.carrier) : ModuleCat.{v} (X.structureSheaf.obj.obj (op U)) :=
  (I : Mod X.structureSheaf).val.obj (op U)

abbrev idealSheafSectionMap {X : RingedSpace.{v}} (I : IdealSheaf X)
    (U : Opens X.carrier) : idealSheafSections I U →
      (X.structureSheaf.obj.obj (op U) : Type v) :=
  fun s => (I.arrow.val.app (op U)).hom s

abbrev moduleSheafSections' {X : RingedSpace.{v}}
    (F : Mod X.structureSheaf) (U : Opens X.carrier) :
      ModuleCat.{v} (X.structureSheaf.obj.obj (op U)) :=
  F.val.obj (op U)

def principalIdealSheafSections {X : RingedSpace.{v}} (I : IdealSheaf X)
    (U : Opens X.carrier)
    (f : (X.structureSheaf.obj.obj (op U) : Type v)) : Prop :=
  (∀ s : idealSheafSections I U, ∃ a, idealSheafSectionMap I U s = a * f) ∧
    (∀ a : (X.structureSheaf.obj.obj (op U) : Type v),
      ∃ s : idealSheafSections I U, idealSheafSectionMap I U s = a * f)

structure LocalPrincipalRegularGenerator {X : RingedSpace.{v}}
    (I : IdealSheaf X) (x : X.carrier) where
  U : Opens X.carrier
  mem : x ∈ U
  generator : (X.structureSheaf.obj.obj (op U) : Type v)
  principal : principalIdealSheafSections I U generator
  regular : Function.Injective (fun a => a * generator)

def IdealSheafLocallyPrincipalRegular {X : RingedSpace.{v}}
    (I : IdealSheaf X) : Prop :=
  ∀ x : X.carrier, Nonempty (LocalPrincipalRegularGenerator I x)

structure LocalInvertibleIdealGenerator {X : RingedSpace.{v}}
    (I : IdealSheaf X) (x : X.carrier) where
  U : Opens X.carrier
  mem : x ∈ U
  generator : (X.structureSheaf.obj.obj (op U) : Type v)
  principal : principalIdealSheafSections I U generator
  freeRankOne : Nonempty
    (ModuleCat.of (X.structureSheaf.obj.obj (op U))
      (idealSheafSections I U) ≅
      ModuleCat.of (X.structureSheaf.obj.obj (op U))
        (X.structureSheaf.obj.obj (op U)))

def IdealSheafInvertible {X : RingedSpace.{v}} (I : IdealSheaf X) : Prop :=
  ∀ x : X.carrier, Nonempty (LocalInvertibleIdealGenerator I x)

/- The ambient sheaf APIs do not expose a tensor product of two arbitrary
   `RingCat`-module sheaves.  This small piece of data records the canonical
   tensor-and-multiplication map used by the source's third criterion. -/
structure IdealMultiplicationData {X : RingedSpace.{v}}
    (I : IdealSheaf X) (F : Mod X.structureSheaf) where
  tensor : Mod X.structureSheaf
  multiplication : tensor ⟶ F

theorem locallyPrincipalRegular_iff_invertible_of_local_stalks
    {X : RingedSpace.{v}} (I : IdealSheaf X)
    (hlocal : ∀ x : X.carrier,
      IsLocalRing
        (TopCat.Presheaf.stalk (C := RingCat.{v}) X.structureSheaf.obj x)) :
    IdealSheafLocallyPrincipalRegular I ↔ IdealSheafInvertible I := by
  sorry

theorem locallyPrincipalRegular_implies_invertible
    {X : RingedSpace.{v}} (I : IdealSheaf X)
    (hI : IdealSheafLocallyPrincipalRegular I) :
    IdealSheafInvertible I := by
  sorry

structure IdealSheafSituation (X : RingedSpace.{v}) where
  ideal : IdealSheaf X
  locallyPrincipalRegular : IdealSheafLocallyPrincipalRegular ideal
  multiplication : ∀ F : Mod X.structureSheaf,
    IdealMultiplicationData ideal F

abbrev annihilatorSection {X : RingedSpace.{v}}
    (S : IdealSheafSituation X) (F : Mod X.structureSheaf)
    (U : Opens X.carrier) (s : moduleSheafSections' F U) : Prop :=
  ∀ i : idealSheafSections S.ideal U,
    idealSheafSectionMap S.ideal U i • s = 0

def idealAnnihilatorZero {X : RingedSpace.{v}}
    (S : IdealSheafSituation X) (F : Mod X.structureSheaf) : Prop :=
  ∀ (U : Opens X.carrier) (s : moduleSheafSections' F U),
    annihilatorSection S F U s → s = 0

def idealPowerAnnihilatorZero {X : RingedSpace.{v}}
    (S : IdealSheafSituation X) (F : Mod X.structureSheaf) (n : ℕ) : Prop :=
  ∀ (U : Opens X.carrier) (s : moduleSheafSections' F U),
    (∀ i : Fin n → idealSheafSections S.ideal U,
      (List.ofFn (fun j : Fin n =>
        idealSheafSectionMap S.ideal U (i j))).prod • s = 0) →
      s = 0

def idealMultiplicationInjective {X : RingedSpace.{v}}
    (S : IdealSheafSituation X) (F : Mod X.structureSheaf) : Prop :=
  Mono (S.multiplication F).multiplication

def idealLocalMultiplicationInjective {X : RingedSpace.{v}}
    (S : IdealSheafSituation X) (F : Mod X.structureSheaf) : Prop :=
  ∀ (x : X.carrier) (G : LocalPrincipalRegularGenerator S.ideal x)
    (s : moduleSheafSections' F G.U),
    G.generator • s = 0 → s = 0

def idealStalk {X : RingedSpace.{v}} (S : IdealSheafSituation X)
    (x : X.carrier) : ModuleCat.{v}
      (TopCat.Presheaf.stalk (C := RingCat.{v}) X.structureSheaf.obj x) :=
  (sheafModuleStalkFunctor X.structureSheaf x).obj (S.ideal : Mod X.structureSheaf)

def idealStalkMap {X : RingedSpace.{v}} (S : IdealSheafSituation X)
    (x : X.carrier) : idealStalk S x ⟶
      (sheafModuleStalkFunctor X.structureSheaf x).obj
        (SheafOfModules.unit X.structureSheaf) :=
  (sheafModuleStalkFunctor X.structureSheaf x).map S.ideal.arrow

/- The unit module and the stalk of the structure sheaf have canonically
   isomorphic scalar objects.  We keep this bridge explicit because their
   underlying types are not definitionally equal in Mathlib. -/
theorem unitStalk_iso_structureStalk {X : RingedSpace.{v}}
    (x : X.carrier) : Nonempty
      ((sheafModuleStalkFunctor X.structureSheaf x).obj
        (SheafOfModules.unit X.structureSheaf) ≅
        ModuleCat.of (TopCat.Presheaf.stalk (C := RingCat.{v})
          X.structureSheaf.obj x)
          (TopCat.Presheaf.stalk (C := RingCat.{v}) X.structureSheaf.obj x)) := by
  sorry

noncomputable def unitStalkToStructureStalk {X : RingedSpace.{v}}
    (x : X.carrier) :
    ((sheafModuleStalkFunctor X.structureSheaf x).obj
      (SheafOfModules.unit X.structureSheaf) : Type v) →
      (TopCat.Presheaf.stalk (C := RingCat.{v}) X.structureSheaf.obj x : Type v) :=
  (Classical.choice (unitStalk_iso_structureStalk x)).hom

abbrev idealStalkScalarImage {X : RingedSpace.{v}}
    (S : IdealSheafSituation X) (x : X.carrier) (i : idealStalk S x) :
    (TopCat.Presheaf.stalk (C := RingCat.{v}) X.structureSheaf.obj x : Type v) :=
  unitStalkToStructureStalk x ((idealStalkMap S x).hom i)

def idealStalkNonzerodivisor {X : RingedSpace.{v}}
    (S : IdealSheafSituation X) (F : Mod X.structureSheaf) : Prop :=
  ∀ (x : X.carrier)
    (f : (TopCat.Presheaf.stalk (C := RingCat.{v})
      X.structureSheaf.obj x : Type v)),
    (∃ i : idealStalk S x, idealStalkScalarImage S x i = f) →
      Function.Injective (fun s :
        ((sheafModuleStalkFunctor X.structureSheaf x).obj F : Type v) =>
          f • s)

def IsIdealTorsionFree {X : RingedSpace.{v}}
    (S : IdealSheafSituation X) (F : Mod X.structureSheaf) : Prop :=
  idealAnnihilatorZero S F

theorem ideal_torsion_free_criteria {X : RingedSpace.{v}}
    (S : IdealSheafSituation X) (F : Mod X.structureSheaf) :
    idealAnnihilatorZero S F ↔
      (∀ n : ℕ, 1 ≤ n → idealPowerAnnihilatorZero S F n) ∧
      idealMultiplicationInjective S F ∧
      idealLocalMultiplicationInjective S F ∧
      idealStalkNonzerodivisor S F := by
  sorry

/-! ## Powers and the `η` construction -/

/- This is the chapter-owned realization of the notation `I^i F^j`.  Its
   objects and inclusions are the sheaf-module tensor powers, with the
   source's negative powers included because `I` is invertible. -/
structure IdealSheafPowerSystem {X : RingedSpace.{v}} (S : IdealSheafSituation X) where
  object : ℤ → Mod X.structureSheaf
  inclusion : ∀ i : ℤ, object (i + 1) ⟶ object i
  tensor : ∀ i : ℤ, Mod X.structureSheaf → Mod X.structureSheaf
  locallyIsomorphic : ∀ (i : ℤ) (F : Mod X.structureSheaf) (x : X.carrier),
    Nonempty
      ((sheafModuleStalkFunctor X.structureSheaf x).obj (tensor i F) ≅
        (sheafModuleStalkFunctor X.structureSheaf x).obj F)

structure FilteredComplexData {X : RingedSpace.{v}}
    (S : IdealSheafSituation X) where
  powers : IdealSheafPowerSystem S
  underlying : CochainComplex (Mod X.structureSheaf) ℤ
  term : ℤ → ℤ → Mod X.structureSheaf
  termRealization : ∀ (i j : ℤ),
    Nonempty (term i j ≅ powers.tensor i (underlying.X j))
  inclusion : ∀ (i j : ℤ), term (i + 1) j ⟶ term i j
  filteredDifferential : ∀ i : ℤ, term i i ⟶ term i (i + 1)
  etaDifferential : ∀ i : ℤ,
    kernel (filteredDifferential i ≫
      cokernel.π (inclusion i (i + 1))) ⟶
      kernel (filteredDifferential (i + 1) ≫
        cokernel.π (inclusion (i + 1) (i + 1 + 1)))
  etaDifferential_sq : ∀ i : ℤ,
    etaDifferential i ≫ etaDifferential (i + 1) = 0

noncomputable def etaTerm {X : RingedSpace.{v}}
    {S : IdealSheafSituation X} (K : FilteredComplexData S) (i : ℤ) :
    Mod X.structureSheaf :=
  kernel (K.filteredDifferential i ≫
    cokernel.π (K.inclusion i (i + 1)))

noncomputable def etaDirectTerm {X : RingedSpace.{v}}
    {S : IdealSheafSituation X} (K : FilteredComplexData S) (i : ℤ) :
    Mod X.structureSheaf :=
  kernel (biprod.desc (K.filteredDifferential i)
    (-K.inclusion i (i + 1)))

theorem eta_direct_term_iso_quotient_term {X : RingedSpace.{v}}
    {S : IdealSheafSituation X} (K : FilteredComplexData S) (i : ℤ) :
    Nonempty (etaDirectTerm K i ≅ etaTerm K i) := by
  sorry

noncomputable def etaComplex {X : RingedSpace.{v}}
    {S : IdealSheafSituation X} (K : FilteredComplexData S) :
    CochainComplex (Mod X.structureSheaf) ℤ where
  X i := etaTerm K i
  d i j := if h : i + 1 = j then h ▸ K.etaDifferential i else 0
  shape i j hij := by
    classical
    split_ifs with h
    · exact (hij h).elim
    · rfl
  d_comp_d' i j k hij hjk := by
    classical
    have hij' : i + 1 = j := by
      simpa only [ComplexShape.up_Rel] using hij
    have hjk' : j + 1 = k := by
      simpa only [ComplexShape.up_Rel] using hjk
    rw [dif_pos hij', dif_pos hjk']
    subst j
    subst k
    exact K.etaDifferential_sq i

noncomputable def etaStalkComplex {X : RingedSpace.{v}}
    {S : IdealSheafSituation X} (K : FilteredComplexData S) (x : X.carrier) :
    CochainComplex
      (ModuleCat (TopCat.Presheaf.stalk (C := RingCat.{v})
        X.structureSheaf.obj x)) ℤ :=
  ((sheafModuleStalkFunctor X.structureSheaf x).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj (etaComplex K)

structure AlgebraicEtaStalkComparison {X : RingedSpace.{v}}
    {S : IdealSheafSituation X} (K : FilteredComplexData S) (x : X.carrier) where
  algebraicEta : CochainComplex
    (ModuleCat (TopCat.Presheaf.stalk (C := RingCat.{v})
      X.structureSheaf.obj x)) ℤ
  canonicalIso : Nonempty (etaStalkComplex K x ≅ algebraicEta)

theorem exists_eta_stalk_comparison {X : RingedSpace.{v}}
    {S : IdealSheafSituation X} (K : FilteredComplexData S) (x : X.carrier) :
    Nonempty (AlgebraicEtaStalkComparison K x) := by
  sorry

theorem eta_stalks {X : RingedSpace.{v}}
    {S : IdealSheafSituation X} (K : FilteredComplexData S) (x : X.carrier) :
    Nonempty (etaStalkComplex K x ≅
      (Classical.choice (exists_eta_stalk_comparison K x)).algebraicEta) := by
  exact (Classical.choice (exists_eta_stalk_comparison K x)).canonicalIso

def IsITorsionFreeComplex {X : RingedSpace.{v}}
    {S : IdealSheafSituation X} (K : FilteredComplexData S) : Prop :=
  ∀ i : ℤ, IsIdealTorsionFree S (K.underlying.X i)

structure FilteredComplexMorphism {X : RingedSpace.{v}}
    {S : IdealSheafSituation X} (K L : FilteredComplexData S) where
  underlying : K.underlying ⟶ L.underlying
  termMap : ∀ (i j : ℤ), K.term i j ⟶ L.term i j
  eta : etaComplex K ⟶ etaComplex L
  eta_square : ∀ i : ℤ,
    kernel.ι (K.filteredDifferential i ≫
      cokernel.π (K.inclusion i (i + 1))) ≫ termMap i i =
      eta.f i ≫ kernel.ι (L.filteredDifferential i ≫
        cokernel.π (L.inclusion i (i + 1)))

instance filteredComplexCategory {X : RingedSpace.{v}}
    {S : IdealSheafSituation X} : Category (FilteredComplexData S) where
  Hom K L := FilteredComplexMorphism K L
  id K :=
    { underlying := 𝟙 K.underlying
      termMap := fun i j => 𝟙 (K.term i j)
      eta := 𝟙 (etaComplex K)
      eta_square := by
        intro i
        exact (Category.id_comp _).symm }
  comp f g :=
    { underlying := f.underlying ≫ g.underlying
      termMap := fun i j => f.termMap i j ≫ g.termMap i j
      eta := f.eta ≫ g.eta
      eta_square := by
        intro i
        sorry }
  id_comp f := by
    rfl
  comp_id f := by
    rfl
  assoc f g h := by
    rfl

def etaFunctor {X : RingedSpace.{v}}
    {S : IdealSheafSituation X} :
    FilteredComplexData S ⥤ CochainComplex (Mod X.structureSheaf) ℤ where
  obj K := etaComplex K
  map f := f.eta
  map_id K := by
    rfl
  map_comp f g := by
    rfl

theorem eta_complex_is_I_torsion_free {X : RingedSpace.{v}}
    {S : IdealSheafSituation X} (K : FilteredComplexData S)
    (hK : IsITorsionFreeComplex K) :
    ∀ i : ℤ, IsIdealTorsionFree S ((etaComplex K).X i) := by
  sorry

theorem eta_morphism_exists {X : RingedSpace.{v}}
    {S : IdealSheafSituation X} {K L : FilteredComplexData S}
    (f : K.underlying ⟶ L.underlying)
    (hf : ∀ i j, K.term i j ⟶ L.term i j) :
    Nonempty (FilteredComplexMorphism K L) := by
  sorry

theorem eta_preserves_homotopy {X : RingedSpace.{v}}
    {S : IdealSheafSituation X} {K L : FilteredComplexData S}
    (f g : FilteredComplexMorphism K L)
    (h : Nonempty (Homotopy f.underlying g.underlying)) :
    Nonempty (Homotopy f.eta g.eta) := by
  sorry

/-! The source's homotopy-category endofunctor is represented by these
   homotopy-compatible maps; the canonical homotopy quotient remains
   Mathlib's `HomotopyCategory`. -/
def eta_descends_to_homotopy_category {X : RingedSpace.{v}}
    (S : IdealSheafSituation X) : Prop :=
  ∀ {K L : FilteredComplexData S} (f g : FilteredComplexMorphism K L),
    Nonempty (Homotopy f.underlying g.underlying) →
      Nonempty (Homotopy f.eta g.eta)

/-! ## First property and derived `Lη` -/

/- The quotient by the ideal-torsion subsheaf is represented by a chosen
   universal torsion-free quotient.  The universal property makes this a
   genuine quotient interface rather than a definitional copy of its input. -/
structure IdealTorsionFreeQuotientData {X : RingedSpace.{v}}
    (S : IdealSheafSituation X) (F : Mod X.structureSheaf) where
  object : Mod X.structureSheaf
  quotient : F ⟶ object
  torsionFree : IsIdealTorsionFree S object
  universal : ∀ (G : Mod X.structureSheaf), IsIdealTorsionFree S G →
    ∀ (q : F ⟶ G), ∃! u : object ⟶ G, quotient ≫ u = q

theorem exists_idealTorsionFreeQuotientData {X : RingedSpace.{v}}
    (S : IdealSheafSituation X) (F : Mod X.structureSheaf) :
    Nonempty (IdealTorsionFreeQuotientData S F) := by
  sorry

noncomputable def idealTorsionQuotient {X : RingedSpace.{v}}
    (S : IdealSheafSituation X) (F : Mod X.structureSheaf) : Mod X.structureSheaf :=
  (Classical.choice (exists_idealTorsionFreeQuotientData S F)).object

noncomputable def idealPowerCohomologySource {X : RingedSpace.{v}}
    {S : IdealSheafSituation X} (K : FilteredComplexData S) (i : ℤ) :
    Mod X.structureSheaf :=
  K.powers.tensor i
    (idealTorsionQuotient S
      ((cochainCohomologyFunctor (Mod X.structureSheaf) i).obj K.underlying))

theorem eta_first_property {X : RingedSpace.{v}}
    {S : IdealSheafSituation X} (K : FilteredComplexData S)
    (hK : IsITorsionFreeComplex K) (i : ℤ) :
    Nonempty
      (idealPowerCohomologySource K i ≅
        (cochainCohomologyFunctor (Mod X.structureSheaf) i).obj
          (etaComplex K)) := by
  sorry

theorem eta_quasi_isomorphism {X : RingedSpace.{v}}
    {S : IdealSheafSituation X} {K L : FilteredComplexData S}
    (f : FilteredComplexMorphism K L)
    (hf : QuasiIso f.underlying) : QuasiIso f.eta := by
  sorry

abbrev ringedSpaceModuleDerived (X : RingedSpace.{v}) :=
  DerivedCategory (Mod X.structureSheaf)

structure LEtaFunctorWitness {X : RingedSpace.{v}}
    (S : IdealSheafSituation X) where
  functor : ringedSpaceModuleDerived X ⥤ ringedSpaceModuleDerived X
  representative : ∀ M : ringedSpaceModuleDerived X,
    ∃ K : FilteredComplexData S,
      Nonempty ((DerivedCategory.Q (C := Mod X.structureSheaf)).obj K.underlying ≅ M)
  represented : ∀ (K : FilteredComplexData S),
    Nonempty ((DerivedCategory.Q (C := Mod X.structureSheaf)).obj (etaComplex K) ≅
      functor.obj ((DerivedCategory.Q (C := Mod X.structureSheaf)).obj K.underlying))

theorem exists_LEtaFunctorWitness {X : RingedSpace.{v}}
    (S : IdealSheafSituation X) : Nonempty (LEtaFunctorWitness S) := by
  sorry

noncomputable def LEta {X : RingedSpace.{v}}
    (S : IdealSheafSituation X) : ringedSpaceModuleDerived X ⥤
      ringedSpaceModuleDerived X :=
  (Classical.choice (exists_LEtaFunctorWitness S)).functor

def LEta_additive {X : RingedSpace.{v}} (S : IdealSheafSituation X) :
    Prop :=
  ∀ K : FilteredComplexData S,
    Nonempty ((DerivedCategory.Q (C := Mod X.structureSheaf)).obj (etaComplex K) ≅
      (LEta S).obj ((DerivedCategory.Q (C := Mod X.structureSheaf)).obj K.underlying))

theorem LEta_is_additive {X : RingedSpace.{v}}
    (S : IdealSheafSituation X) : (LEta S).Additive := by
  sorry

/-! ## Bockstein operators -/

/- The two rows and their vertical maps in the source's diagram are kept as
   short-complex data.  In particular, exactness is Mathlib's canonical
   `ShortExact` predicate rather than an informal annotation. -/
structure BocksteinExactRows {X : RingedSpace.{v}}
    (S : IdealSheafSituation X) where
  top : ShortComplex (Mod X.structureSheaf)
  bottom : ShortComplex (Mod X.structureSheaf)
  topShortExact : top.ShortExact
  bottomShortExact : bottom.ShortExact
  leftVertical : top.X₁ ⟶ bottom.X₁
  middleVertical : top.X₂ ⟶ bottom.X₂
  rightVertical : top.X₃ ⟶ bottom.X₃
  leftSquare : top.f ≫ middleVertical = leftVertical ≫ bottom.f
  rightSquare : top.g ≫ rightVertical = middleVertical ≫ bottom.g

structure BocksteinData {X : RingedSpace.{v}}
    (S : IdealSheafSituation X)
    (M : ringedSpaceModuleDerived X) where
  powers : IdealSheafPowerSystem S
  exactRows : ∀ i : ℤ, BocksteinExactRows S
  graded : ℤ → ringedSpaceModuleDerived X
  middle : ℤ → ringedSpaceModuleDerived X
  boundary : ∀ i : ℤ,
    (derivedCohomologyFunctor (Mod X.structureSheaf) i).obj (graded i) ⟶
      (derivedCohomologyFunctor (Mod X.structureSheaf) (i + 1)).obj (middle i)
  middleToGraded : ∀ i : ℤ,
    (derivedCohomologyFunctor (Mod X.structureSheaf) (i + 1)).obj (middle i) ⟶
      (derivedCohomologyFunctor (Mod X.structureSheaf) (i + 1)).obj (graded (i + 1))
  beta : ∀ i : ℤ,
    (derivedCohomologyFunctor (Mod X.structureSheaf) i).obj (graded i) ⟶
      (derivedCohomologyFunctor (Mod X.structureSheaf) (i + 1)).obj (graded (i + 1))
  factorization : ∀ i : ℤ,
    boundary i ≫ middleToGraded i = beta i
  beta_sq : ∀ i : ℤ, beta i ≫ beta (i + 1) = 0
  derivedReduction : ringedSpaceModuleDerived X

noncomputable def bocksteinComplex {X : RingedSpace.{v}}
    {S : IdealSheafSituation X} {M : ringedSpaceModuleDerived X}
    (B : BocksteinData S M) : CochainComplex (Mod X.structureSheaf) ℤ where
  X i := (derivedCohomologyFunctor (Mod X.structureSheaf) i).obj (B.graded i)
  d i j := if h : i + 1 = j then h ▸ B.beta i else 0
  shape i j hij := by
    classical
    split_ifs with h
    · exact (hij h).elim
    · rfl
  d_comp_d' i j k hij hjk := by
    classical
    have hij' : i + 1 = j := by
      simpa only [ComplexShape.up_Rel] using hij
    have hjk' : j + 1 = k := by
      simpa only [ComplexShape.up_Rel] using hjk
    rw [dif_pos hij', dif_pos hjk']
    subst j
    subst k
    exact B.beta_sq i

theorem bockstein_acyclic_iff_homology_isZero {X : RingedSpace.{v}}
    {S : IdealSheafSituation X} {M : ringedSpaceModuleDerived X}
    (B : BocksteinData S M) :
    (bocksteinComplex B).Acyclic ↔
      ∀ i : ℤ, IsZero ((bocksteinComplex B).homology i) := by
  exact cochain_acyclic_iff_cohomology_isZero
    (bocksteinComplex (X := X) (S := S) (M := M) B)

theorem bockstein_square_zero {X : RingedSpace.{v}}
    {S : IdealSheafSituation X} {M : ringedSpaceModuleDerived X}
    (B : BocksteinData S M) :
    ∀ i : ℤ, B.beta i ≫ B.beta (i + 1) = 0 :=
  B.beta_sq

theorem eta_second_property {X : RingedSpace.{v}}
    {S : IdealSheafSituation X} {M : ringedSpaceModuleDerived X}
    (B : BocksteinData S M) :
    Nonempty ((LEta S).obj M ≅ B.derivedReduction) ∧
      Nonempty
        (B.derivedReduction ≅
          (DerivedCategory.Q (C := Mod X.structureSheaf)).obj
            (bocksteinComplex B)) := by
  sorry

/-! ## Tensoring by an invertible module and local freeness -/

structure InvertibleModule {X : RingedSpace.{v}}
    (S : IdealSheafSituation X) where
  object : Mod X.structureSheaf
  locallyFreeRankOne : Prop
  tensorComplex : FilteredComplexData S → FilteredComplexData S
  tensorEtaComplex : FilteredComplexData S →
    CochainComplex (Mod X.structureSheaf) ℤ

def etaTensorInvertible {X : RingedSpace.{v}}
    {S : IdealSheafSituation X} (K : FilteredComplexData S)
    (L : InvertibleModule S) : Prop :=
  Nonempty (etaComplex (L.tensorComplex K) ≅ L.tensorEtaComplex K)

theorem eta_tensor_invertible {X : RingedSpace.{v}}
    {S : IdealSheafSituation X} (K : FilteredComplexData S)
    (hK : IsITorsionFreeComplex K) (L : InvertibleModule S) :
    etaTensorInvertible K L := by
  sorry

def FiniteFreeAtStalkOfRank {X : RingedSpace.{v}}
    (F : Mod X.structureSheaf) (x : X.carrier) (n : ℕ) : Prop :=
  Nonempty
    (((sheafModuleStalkFunctor X.structureSheaf x).obj F) ≅
      ModuleCat.of (TopCat.Presheaf.stalk (C := RingCat.{v})
        X.structureSheaf.obj x)
        (Fin n → TopCat.Presheaf.stalk (C := RingCat.{v})
          X.structureSheaf.obj x))

def FiniteFreeAtStalk {X : RingedSpace.{v}}
    (F : Mod X.structureSheaf) (x : X.carrier) (i : ℤ) : Prop :=
  ∃ (n : ℕ), FiniteFreeAtStalkOfRank F x n

theorem eta_cohomology_locally_free {X : RingedSpace.{v}}
    {S : IdealSheafSituation X} (M : ringedSpaceModuleDerived X)
    (K : FilteredComplexData S)
    (hM : Nonempty ((DerivedCategory.Q (C := Mod X.structureSheaf)).obj
      K.underlying ≅ M))
    (x : X.carrier) (i : ℤ) (n : ℕ)
    (hx : Nontrivial (TopCat.Presheaf.stalk (C := RingCat.{v})
      X.structureSheaf.obj x))
    (hfree : FiniteFreeAtStalkOfRank (X := X)
      ((cochainCohomologyFunctor (Mod X.structureSheaf) i).obj K.underlying)
      x n) :
    FiniteFreeAtStalkOfRank (X := X)
      ((cochainCohomologyFunctor (Mod X.structureSheaf) i).obj (etaComplex K))
      x n := by
  sorry

end Formalization.Books.Cohomology.Unit47
