import Formalization.Books.MoreAlgebra.Unit92.DerivedCompletion
import Formalization.Books.MoreAlgebra.Unit74.DerivedHom
import Formalization.Books.Derived.Unit09.ConesAndTermwiseSplitSequences
import Formalization.Books.MoreAlgebra.Unit87.RlimOfAbelianGroups
import Formalization.Books.Algebra.Unit31.NoetherianRings
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Noetherian.Basic

/-!
# More on Algebra, Chapter 102: Systems of modules, bis

This file records the module systems, comparison data, and derived-category
interfaces occurring in the chapter.  The preceding chapters supply the
canonical module, Ext, derived Hom, derived tensor, Koszul, and pro-category
APIs used below.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Preadditive
open CategoryTheory.Pretriangulated
open Formalization.Books.Algebra.Unit71
open Formalization.Books.Derived.Unit08
open Formalization.Books.Derived.Unit09
open Formalization.Books.MoreAlgebra.Unit56
open Formalization.Books.MoreAlgebra.Unit59
open Formalization.Books.MoreAlgebra.Unit63
open Formalization.Books.MoreAlgebra.Unit65
open Formalization.Books.MoreAlgebra.Unit74
open Formalization.Books.MoreAlgebra.Unit87
open Formalization.Books.MoreAlgebra.Unit92
open scoped BigOperators CategoryTheory.Pretriangulated.Opposite ZeroObject

universe u v w

namespace Formalization.Books.MoreAlgebra.Unit102

abbrev Mod (A : Type u) [CommRing A] := ModuleCat.{u} A

abbrev Comp (A : Type u) [CommRing A] := Unit92.Comp A

abbrev D (A : Type u) [CommRing A]
    [HasDerivedCategory.{w} (Mod A)] := Unit92.D A

/-! ## Powers of an ideal and systems of modules -/

/-- The usual submodule `I^n M`, written using Mathlib's scalar action on
submodules.  This is the normalization used in the earlier chapters. -/
def idealPowerSubmodule {A : Type u} [CommRing A]
    (I : Ideal A) (n : ℕ) (M : Mod A) : Submodule A (M : Type u) :=
  I ^ n • (⊤ : Submodule A (M : Type u))

/-- `I^n M` as an object of the category of `A`-modules. -/
abbrev idealPowerModule {A : Type u} [CommRing A]
    (I : Ideal A) (n : ℕ) (M : Mod A) : Mod A :=
  ModuleCat.of A (idealPowerSubmodule I n M)

/-- The canonical inclusion `I^m M → I^n M` when `n ≤ m`. -/
def idealPowerInclusion {A : Type u} [CommRing A]
    (I : Ideal A) (M : Mod A) {m n : ℕ} (h : n ≤ m) :
    idealPowerModule I m M ⟶ idealPowerModule I n M := by
  apply ModuleCat.ofHom
  apply Submodule.inclusion
  refine Submodule.smul_le.mpr ?_
  intro r hr x hx
  exact Submodule.smul_mem_smul (Ideal.pow_le_pow_right h hr) hx

/-- The inverse system of powers of an ideal acting on a module. -/
def idealPowerSystem {A : Type u} [CommRing A]
    (I : Ideal A) (M : Mod A) : ℕᵒᵖ ⥤ Mod A where
  obj n := idealPowerModule I n.unop M
  map f := idealPowerInclusion I M f.unop.le
  map_id := by
    intro n
    apply ModuleCat.hom_ext
    rfl
  map_comp := by
    intro X Y Z f g
    apply ModuleCat.hom_ext
    rfl

/-- The inclusion of a power into the ambient module. -/
def idealPowerToAmbient {A : Type u} [CommRing A]
    (I : Ideal A) (n : ℕ) (M : Mod A) :
    idealPowerModule I n M ⟶ M :=
  ModuleCat.ofHom (idealPowerSubmodule I n M).subtype

/-- A finite two-step complex of modules, in the form used by the
Artin--Rees statement. -/
structure FiniteModuleComplex (A : Type u) [CommRing A] where
  K : Mod A
  L : Mod A
  M : Mod A
  α : K ⟶ L
  β : L ⟶ M
  comp : α ≫ β = 0
  finite_K : Module.Finite A (K : Type u)
  finite_L : Module.Finite A (L : Type u)
  finite_M : Module.Finite A (M : Type u)

def finiteModuleShortComplex {A : Type u} [CommRing A]
    (C : FiniteModuleComplex A) : ShortComplex (Mod A) :=
  { f := C.α, g := C.β, zero := C.comp }

noncomputable def finiteModuleHomology {A : Type u} [CommRing A]
    (C : FiniteModuleComplex A) : Mod A :=
  (finiteModuleShortComplex C).moduleCatLeftHomologyData.H

/-! The restricted complex obtained by applying `I^n` termwise. -/

def powerLinearMap {A : Type u} [CommRing A]
    {M N : Mod A} (I : Ideal A) (n : ℕ) (f : M ⟶ N) :
    idealPowerModule I n M ⟶ idealPowerModule I n N := by
  apply ModuleCat.ofHom
  apply LinearMap.codRestrict
    (idealPowerSubmodule I n N)
    (f.hom.domRestrict (idealPowerSubmodule I n M))
  intro x
  change f.hom (x : M) ∈ idealPowerSubmodule I n N
  refine Submodule.smul_induction_on (I := I ^ n)
    (N := (⊤ : Submodule A (M : Type u)))
    (p := fun z : (M : Type u) => f.hom z ∈ idealPowerSubmodule I n N)
    x.property ?_ ?_
  · intro r hr y hy
    rw [map_smul]
    exact Submodule.smul_mem_smul hr trivial
  · intro x y hx hy
    rw [map_add]
    exact (idealPowerSubmodule I n N).add_mem hx hy

def powerComplex {A : Type u} [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) (C : FiniteModuleComplex A) (n : ℕ) :
    FiniteModuleComplex A where
  K := idealPowerModule I n C.K
  L := idealPowerModule I n C.L
  M := idealPowerModule I n C.M
  α := powerLinearMap I n C.α
  β := powerLinearMap I n C.β
  comp := by
    apply ModuleCat.hom_ext
    ext x
    rw [ModuleCat.hom_comp, LinearMap.comp_apply]
    dsimp [powerLinearMap]
    change C.β.hom (C.α.hom (x.1 : C.K)) = 0
    exact congrArg (fun f : C.K ⟶ C.M => f.hom (x.1 : C.K)) C.comp
  finite_K := by
    exact @Formalization.Books.Algebra.Unit31.submodule_of_finite_module_isFinite
      A (C.K : Type u) _ _ _ _ C.finite_K _
  finite_L := by
    exact @Formalization.Books.Algebra.Unit31.submodule_of_finite_module_isFinite
      A (C.L : Type u) _ _ _ _ C.finite_L _
  finite_M := by
    exact @Formalization.Books.Algebra.Unit31.submodule_of_finite_module_isFinite
      A (C.M : Type u) _ _ _ _ C.finite_M _

noncomputable def powerComplexHomology {A : Type u} [CommRing A]
    [IsNoetherianRing A]
    (I : Ideal A) (C : FiniteModuleComplex A) (n : ℕ) : Mod A :=
  finiteModuleHomology (powerComplex I C n)

/-! ## The Artin--Rees comparison -/

/-- The transition maps and stage identifications needed to regard the
homology modules of the powers as an inverse system.  The fields are
deliberately separated from the Artin--Rees theorem so later users can use
the system independently of the comparison constants. -/
structure PowerHomologySystemData {A : Type u} [CommRing A]
    [IsNoetherianRing A]
    (I : Ideal A) (C : FiniteModuleComplex A) where
  system : ℕᵒᵖ ⥤ Mod A
  stage : ∀ n, Nonempty (system.obj (Opposite.op n) ≅ powerComplexHomology I C n)
  transition : ∀ m n : ℕ, n ≤ m →
    powerComplexHomology I C m ⟶ powerComplexHomology I C n

/-- All comparison maps in the Artin--Rees conclusion, including the image
containment and the pro-isomorphism of inverse systems. -/
structure ArtinReesBisData {A : Type u} [CommRing A]
    [IsNoetherianRing A]
    (I : Ideal A) (C : FiniteModuleComplex A) where
  c : ℕ
  positive : 0 < c
  systemData : PowerHomologySystemData I C
  toH : ∀ n : ℕ,
    powerComplexHomology I C n ⟶ finiteModuleHomology C
  image_contained : ∀ (n : ℕ) (_hn : c ≤ n),
    LinearMap.range (toH n).hom ≤
      idealPowerSubmodule I (n - c) (finiteModuleHomology C)
  fromH : ∀ (n : ℕ),
    idealPowerModule I n (finiteModuleHomology C) ⟶
      powerComplexHomology I C (n - c)
  comparison_to_H : ∀ (n : ℕ) (_hn : 2 * c ≤ n),
    fromH n ≫ toH (n - c) =
      idealPowerToAmbient I n (finiteModuleHomology C)
  pro_isomorphism : IsProIsomorphism systemData.system
    (idealPowerSystem I (finiteModuleHomology C))

/-- Consequence of Artin--Rees for the homology of a finite complex. -/
theorem lemma_consequence_Artin_Rees_bis {A : Type u} [CommRing A]
    [IsNoetherianRing A] (I : Ideal A) (C : FiniteModuleComplex A) :
    Nonempty (ArtinReesBisData I C) := by
  sorry

/-! ## Ext factorization and annihilation -/

abbrev ExtAt {A : Type u} [CommRing A] (M N : Mod A) (p : ℕ) : Type u :=
  ExtGroup M N p

/- The two canonical maps on Ext used in the factorization statement.  They
are Mathlib's contravariant and covariant Ext maps, specialized to degree
zero classes representing module morphisms. -/
noncomputable def extPrecompMap {A : Type u} [CommRing A]
    {M' M N : Mod A} (f : M' ⟶ M) (p : ℕ) :
    ExtAt M N p →+ ExtAt M' N p :=
  (CategoryTheory.Abelian.Ext.mk₀ f).precomp N (Nat.zero_add p)

noncomputable def extPostcompMap {A : Type u} [CommRing A]
    {M N' N : Mod A} (g : N' ⟶ N) (p : ℕ) :
  ExtAt M N' p →+ ExtAt M N p :=
  (CategoryTheory.Abelian.Ext.mk₀ g).postcomp M (Nat.add_zero p)

def annihilatedByPower {A : Type u} [CommRing A]
    (I : Ideal A) (N : Mod A) : Prop :=
  ∃ k : ℕ, idealPowerSubmodule I k N ≤ ⊥

structure ExtFactorizationData {A : Type u} [CommRing A]
    (I : Ideal A) (M N : Mod A) (p : ℕ) where
  c : ℕ
  n : ℕ
  positive : 0 < p
  bounds : c ≤ n
  originalToPower : ExtAt M N p →+ ExtAt (idealPowerModule I n M) N p
  factor : ExtAt M N p →+ ExtAt (idealPowerModule I n M)
      (idealPowerModule I (n - c) N) p
  post : ExtAt (idealPowerModule I n M)
      (idealPowerModule I (n - c) N) p →+
    ExtAt (idealPowerModule I n M) N p
  factorization : ∀ x, originalToPower x = post (factor x)

theorem lemma_ext_factors {A : Type u} [CommRing A]
    [IsNoetherianRing A] (I : Ideal A) (M N : Mod A) (p : ℕ) (hp : 0 < p)
    (hM : Module.Finite A (M : Type u)) :
    Nonempty (ExtFactorizationData I M N p) := by
  sorry

structure ExtAnnihilationData {A : Type u} [CommRing A]
    (I : Ideal A) (M N : Mod A) (p : ℕ) where
  n : ℕ
  originalToPower : ExtAt M N p →+ ExtAt (idealPowerModule I n M) N p
  vanishes : ∀ x, originalToPower x = 0

theorem lemma_ext_annihilated {A : Type u} [CommRing A]
    [IsNoetherianRing A] (I : Ideal A) (M N : Mod A) (p : ℕ) (hp : 0 < p)
    (hM : Module.Finite A (M : Type u)) (hN : annihilatedByPower I N) :
    Nonempty (ExtAnnihilationData I M N p) := by
  sorry

/-! ## The induced topology on derived Ext -/

noncomputable def derivedExt {A : Type u} [CommRing A]
    [HasDerivedCategory.{w} (Mod A)] (K L : D A) (p : ℤ) : Mod A :=
  (derivedCohomology A p).obj (RHom K L)

noncomputable def derivedExtMap {A : Type u} [CommRing A]
    [HasDerivedCategory.{w} (Mod A)] {K K' L L' : D A} (p : ℤ)
    (f : K' ⟶ K) (g : L ⟶ L') :
    derivedExt K L p ⟶ derivedExt K' L' p :=
  (derivedCohomology A p).map (rHomMap f g)

noncomputable def moduleInDerivedMap {A : Type u} [CommRing A]
    [HasDerivedCategory.{w} (Mod A)] {M N : Mod A} (f : M ⟶ N) :
    moduleInDerived A M ⟶ moduleInDerived A N :=
  (derivedComplexQuotient A).map
    ((CochainComplex.singleFunctor (Mod A) 0).map f)

noncomputable def moduleInDerivedFunctor {A : Type u} [CommRing A]
    [HasDerivedCategory.{w} (Mod A)] : Mod A ⥤ D A where
  obj M := moduleInDerived A M
  map f := moduleInDerivedMap f
  map_id := by
    simp [moduleInDerivedMap, moduleInDerived]
  map_comp := by
    simp [moduleInDerivedMap, moduleInDerived]

noncomputable def derivedExtPowerMap {A : Type u} [CommRing A]
    [HasDerivedCategory.{w} (Mod A)] (I : Ideal A) (K : D A)
    (M : Mod A) (p : ℤ) (n : ℕ) :
    derivedExt K (moduleInDerived A (idealPowerModule I n M)) p ⟶
      derivedExt K (moduleInDerived A M) p :=
  derivedExtMap p (𝟙 K) (moduleInDerivedMap (idealPowerToAmbient I n M))

structure DerivedExtTopologyData {A : Type u} [CommRing A]
    [HasDerivedCategory.{w} (Mod A)] (I : Ideal A) (K : D A)
    (M : Mod A) (p : ℤ) where
  c : ℕ
  image_map : ∀ n : ℕ,
    derivedExt K (moduleInDerived A (idealPowerModule I n M)) p ⟶
      derivedExt K (moduleInDerived A M) p
  image_contained : ∀ {n : ℕ} (_hn : c ≤ n),
    LinearMap.range (image_map n).hom ≤
      idealPowerSubmodule I (n - c) (derivedExt K (moduleInDerived A M) p)

theorem lemma_ext_induced_topology {A : Type u} [CommRing A]
    [IsNoetherianRing A] [HasDerivedCategory.{w} (Mod A)]
    (I : Ideal A) (K : D A) (M : Mod A)
    (hK : IsPseudoCoherent A K) (hM : Module.Finite A (M : Type u)) (p : ℤ) :
    Nonempty (DerivedExtTopologyData I K M p) := by
  sorry

/-! ## Koszul truncations -/

noncomputable def koszulTruncationComplex {A : Type u} [CommRing A]
    [HasDerivedCategory.{w} (Mod A)]
    (I : Ideal A) (r : ℕ) (f : Fin r → A)
    (S : KoszulSituation A I r f) (n : ℕ) : Comp A :=
  (CochainComplex.shiftFunctor (Mod A) (-1)).obj
    (CochainComplex.truncLE (S.stage n) (-1))

def koszulPowerIdealModule {A : Type u} [CommRing A]
    (r : ℕ) (f : Fin r → A) (n : ℕ) : Mod A :=
  ModuleCat.of A (Ideal.span (Set.range (fun i => f i ^ n)))

def koszulDegreeZeroMap {A : Type u} [CommRing A]
    (r : ℕ) (f : Fin r → A) (n : ℕ) :
    ModuleCat.of A (Fin r → A) ⟶ ModuleCat.of A A := by
  classical
  apply ModuleCat.ofHom
  refine
    { toFun := fun x => ∑ i, x i * f i ^ n
      map_add' := ?_
      map_smul' := ?_ }
  · intro x y
    simp [Finset.sum_add_distrib, add_mul]
  · intro a x
    change (∑ i, (a * x i) * f i ^ n) =
      a * ∑ i, x i * f i ^ n
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _hi
    ring

structure KoszulFactorThroughData {A : Type u} [CommRing A]
    (r : ℕ) (f : Fin r → A) (n : ℕ) where
  q : ModuleCat.of A (Fin r → A) ⟶ koszulPowerIdealModule r f n
  commutes : q ≫ (ModuleCat.ofHom
      (Ideal.span (Set.range (fun i => f i ^ n))).subtype) =
    koszulDegreeZeroMap r f n

structure KoszulTruncationFacts {A : Type u} [CommRing A]
    [HasDerivedCategory.{w} (Mod A)]
    (I : Ideal A) (r : ℕ) (f : Fin r → A)
    (S : KoszulSituation A I r f) where
  termwise_split_exact : ∀ n, Nonempty (TermwiseSplitExactSequence
    ((CochainComplex.singleFunctor (Mod A) 0).obj (ModuleCat.of A A))
    (S.stage n)
    ((CochainComplex.shiftFunctor (Mod A) (1 : ℤ)).obj
      (koszulTruncationComplex I r f S n)))
  degree_zero_map : ∀ _n : ℕ,
    ModuleCat.of A (Fin r → A) ⟶ ModuleCat.of A A
  degree_zero_formula : ∀ n, degree_zero_map n = koszulDegreeZeroMap r f n
  factor_through_ideal : ∀ n, Nonempty (KoszulFactorThroughData r f n)
  homology_short_exact : ∀ n, ∃ T : ShortComplex (Mod A),
    T.X₁ = (cochainCohomologyFunctor A (-1)).obj (S.stage n) ∧
    T.X₂ = (cochainCohomologyFunctor A 0).obj
      (koszulTruncationComplex I r f S n) ∧
    T.X₃ = koszulPowerIdealModule r f n ∧ T.ShortExact
  negative_homology : ∀ (n : ℕ) (i : ℤ), i < 0 →
    Nonempty ((cochainCohomologyFunctor A i).obj
      (koszulTruncationComplex I r f S n) ≅
      (cochainCohomologyFunctor A (i - 1)).obj (S.stage n))
  transition : ∀ {m n : ℕ}, n ≤ m →
    Nonempty (koszulTruncationComplex I r f S m ⟶
      koszulTruncationComplex I r f S n)
  transition_formula : ∀ (m n : ℕ) (h : n ≤ m),
    S.transition_component_formula m n h

theorem exists_koszulTruncationFacts {A : Type u} [CommRing A]
    [HasDerivedCategory.{w} (Mod A)]
    (I : Ideal A) (r : ℕ) (f : Fin r → A)
    (S : KoszulSituation A I r f) : Nonempty (KoszulTruncationFacts I r f S) := by
  sorry

noncomputable def koszulTermwiseSplitTriangle {A : Type u} [CommRing A]
    [HasDerivedCategory.{w} (Mod A)]
    (I : Ideal A) (r : ℕ) (f : Fin r → A)
    (S : KoszulSituation A I r f) (F : KoszulTruncationFacts I r f S)
    (n : ℕ) : Triangle (BookHomotopyCategory (Mod A)) :=
  termwiseSplitTriangleh (F.termwise_split_exact n).some

theorem koszulTermwiseSplitTriangle_distinguished
    {A : Type u} [CommRing A] [HasDerivedCategory.{w} (Mod A)]
    (I : Ideal A) (r : ℕ) (f : Fin r → A)
    (S : KoszulSituation A I r f) (F : KoszulTruncationFacts I r f S)
    (n : ℕ) :
    koszulTermwiseSplitTriangle I r f S F n ∈
      distTriang (BookHomotopyCategory (Mod A)) := by
  sorry

structure KoszulDerivedSystemData {A : Type u} [CommRing A]
    [HasDerivedCategory.{w} (Mod A)] (I : Ideal A) (r : ℕ)
    (f : Fin r → A) (S : KoszulSituation A I r f) where
  system : ℕᵒᵖ ⥤ D A
  stage_iso : ∀ n, Nonempty (system.obj (Opposite.op n) ≅
    (derivedComplexQuotient A).obj (koszulTruncationComplex I r f S n))

def derivedIdealPowerSystem {A : Type u} [CommRing A]
    [HasDerivedCategory.{w} (Mod A)] (I : Ideal A) (M : Mod A) :
    ℕᵒᵖ ⥤ D A :=
  idealPowerSystem I M ⋙ moduleInDerivedFunctor

theorem lemma_sequence_powers_pro_bounded {A : Type u} [CommRing A]
    [IsNoetherianRing A] [HasDerivedCategory.{w} (Mod A)]
    (I : Ideal A) (r : ℕ) (f : Fin r → A)
    (S : KoszulSituation A I r f) (hgen : I = Ideal.span (Set.range f)) :
    ∃ T : KoszulDerivedSystemData I r f S,
      IsProIsomorphism T.system (derivedIdealPowerSystem I (ModuleCat.of A I)) := by
  sorry

/-! ## Derived tensoring of powers -/

structure BoundedFiniteModuleComplex (A : Type u) [CommRing A] where
  complex : Comp A
  bounded : IsBounded complex
  finite : ∀ i : ℤ, Module.Finite A (complex.X i : Type u)

structure DerivedTensorComparisonData {A : Type u} [CommRing A]
    [HasDerivedCategory.{w} (Mod A)] (I : Ideal A)
    (M : BoundedFiniteModuleComplex A) where
  source : ℕᵒᵖ ⥤ D A
  target : ℕᵒᵖ ⥤ D A
  comparison : ∀ n, source.obj n ⟶ target.obj n
  pro_isomorphism : IsProIsomorphism source target

theorem lemma_tensoring_Deligne_system {A : Type u} [CommRing A]
    [IsNoetherianRing A] [HasDerivedCategory.{w} (Mod A)]
    (I : Ideal A) (M : BoundedFiniteModuleComplex A) :
    Nonempty (DerivedTensorComparisonData I M) := by
  sorry

/-! ## Factorization through the derived tensor product -/

noncomputable def idealModule {A : Type u} [CommRing A]
    (I : Ideal A) : Mod A := ModuleCat.of A I

structure DerivedTensorFactorizationData {A : Type u} [CommRing A]
    [HasDerivedCategory.{w} (Mod A)] (I : Ideal A) (M : Mod A) where
  n : ℕ
  positive : 0 < n
  through : Formalization.Books.MoreAlgebra.Unit59.derivedTensor
      (moduleInDerived A (idealModule I))
      (moduleInDerived A M) ⟶ moduleInDerived A M
  factor : moduleInDerived A (idealPowerModule I n M) ⟶
      Formalization.Books.MoreAlgebra.Unit59.derivedTensor
        (moduleInDerived A (idealModule I)) (moduleInDerived A M)
  factorization : factor ≫ through =
    moduleInDerivedMap (idealPowerToAmbient I n M)

theorem lemma_factor_through_derived_tensor_product {A : Type u} [CommRing A]
    [IsNoetherianRing A] [HasDerivedCategory.{w} (Mod A)]
    (I : Ideal A) (M : Mod A) (hM : Module.Finite A (M : Type u)) :
    Nonempty (DerivedTensorFactorizationData I M) := by
  sorry

end Formalization.Books.MoreAlgebra.Unit102
