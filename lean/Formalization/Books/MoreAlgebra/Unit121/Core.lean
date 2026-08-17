/-
# More on Algebra, Chapter 121: Determinants of endomorphisms of finite length modules
-/

import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Algebra.RestrictScalars
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.LinearAlgebra.Charpoly.Basic
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.LinearAlgebra.Trace
import Mathlib.RingTheory.Length
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal

/-!
This file records the category of finite-length endomorphisms and the linear-algebraic
constructions used in the rest of the chapter.  The filtration and Jordan--Hölder arguments
are kept as interfaces: their proofs belong to the proving stage, while the definitions below
use Mathlib's module, quotient, composition-series, and linear-map APIs.
-/

namespace Formalization.Books.MoreAlgebra.Unit121

noncomputable section

open CategoryTheory
open scoped BigOperators Polynomial TensorProduct

universe u v

/-! ## The category of finite-length endomorphisms -/

/-- A finite-length `R`-module equipped with an endomorphism. -/
structure FiniteLengthEndomorphism (R : Type u) [CommRing R] where
  carrier : ModuleCat.{v} R
  finite_length : IsFiniteLength R carrier
  endomorphism : carrier ⟶ carrier

namespace FiniteLengthEndomorphism

variable {R : Type u} [CommRing R]

/-- A morphism of pairs is a module map commuting with the specified endomorphisms. -/
structure Morph (X Y : FiniteLengthEndomorphism.{u, v} R) where
  hom : X.carrier ⟶ Y.carrier
  comm : X.endomorphism ≫ hom = hom ≫ Y.endomorphism

@[ext]
theorem Morph.ext {X Y : FiniteLengthEndomorphism.{u, v} R} {f g : Morph X Y}
    (h : f.hom = g.hom) : f = g := by
  cases f
  cases g
  cases h
  rfl

instance : Category (FiniteLengthEndomorphism.{u, v} R) where
  Hom X Y := Morph X Y
  id X :=
    { hom := 𝟙 X.carrier
      comm := by simp }
  comp f g :=
    { hom := f.hom ≫ g.hom
      comm := by
        rw [← Category.assoc, f.comm, Category.assoc, g.comm]
        exact (Category.assoc _ _ _).symm }
  id_comp f := by
    apply Morph.ext
    simp
  comp_id f := by
    apply Morph.ext
    simp
  assoc f g h := by
    apply Morph.ext
    simp

/-- The pair category is abelian; kernels and cokernels are inherited from modules and
preserve finite length. -/
noncomputable instance : Abelian (FiniteLengthEndomorphism.{u, v} R) := by
  sorry

theorem isNoetherian_and_isArtinian (X : FiniteLengthEndomorphism.{u, v} R) :
    IsNoetherian R X.carrier ∧ IsArtinian R X.carrier :=
  isFiniteLength_iff_isNoetherian_isArtinian.mp X.finite_length

end FiniteLengthEndomorphism

/-! ## Simple pairs and residue-field linear algebra -/

/-- An endomorphism has no nonzero proper invariant submodule. -/
def IsSimplePair {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (φ : Module.End R M) : Prop :=
  Nontrivial M ∧
    ∀ N : Submodule R M, Submodule.map φ N ≤ N → N = ⊥ ∨ N = ⊤

/-- The simple-object predicate on a bundled finite-length endomorphism. -/
def PairSimple {R : Type*} [CommRing R]
    (X : FiniteLengthEndomorphism R) : Prop :=
  IsSimplePair X.endomorphism.hom

/-- The maximal ideal kills the underlying module of a simple pair. -/
theorem IsSimplePair.annihilated_by_maximalIdeal
    {R M : Type*} [CommRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M] (hM : IsFiniteLength R M)
    (φ : Module.End R M) (hφ : IsSimplePair φ) :
    Module.IsTorsionBySet R M (IsLocalRing.maximalIdeal R) := by
  sorry

/-- The residue-field vector space attached to a simple pair.  The explicit fields make the
source's finiteness and annihilation assertions available to later constructions. -/
structure SimplePairData (R M : Type*) [CommRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M] (φ : Module.End R M) where
  simple : IsSimplePair φ
  annihilated : Module.IsTorsionBySet R M (IsLocalRing.maximalIdeal R)
  residue_endomorphism :
    @Module.End (IsLocalRing.ResidueField R) M _ _ annihilated.module
  finite_dimensional :
    @Module.Finite (IsLocalRing.ResidueField R) M _ _ annihilated.module
  residue_endomorphism_apply : ∀ x, residue_endomorphism.toFun x = φ x

theorem exists_simplePairData
    {R M : Type*} [CommRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M] (hM : IsFiniteLength R M)
    (φ : Module.End R M) (hφ : IsSimplePair φ) :
    Nonempty (SimplePairData R M φ) := by
  sorry

noncomputable def simplePairData
    {R M : Type*} [CommRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M] (hM : IsFiniteLength R M)
    (φ : Module.End R M) (hφ : IsSimplePair φ) :
    SimplePairData R M φ :=
  Classical.choice (exists_simplePairData hM φ hφ)

/-- The endomorphism induced on a residue-field vector space. -/
noncomputable def simpleDeterminant
    {R M : Type*} [CommRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M] {φ : Module.End R M}
    (D : SimplePairData R M φ) : IsLocalRing.ResidueField R :=
  letI : Module (IsLocalRing.ResidueField R) M := D.annihilated.module
  letI : Module.Finite (IsLocalRing.ResidueField R) M := D.finite_dimensional
  D.residue_endomorphism.det

noncomputable def simpleTrace
    {R M : Type*} [CommRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M] {φ : Module.End R M}
    (D : SimplePairData R M φ) : IsLocalRing.ResidueField R :=
  letI : Module (IsLocalRing.ResidueField R) M := D.annihilated.module
  letI : Module.Finite (IsLocalRing.ResidueField R) M := D.finite_dimensional
  LinearMap.trace (IsLocalRing.ResidueField R) M D.residue_endomorphism

noncomputable def simpleCharacteristicPolynomial
    {R M : Type*} [CommRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M] {φ : Module.End R M}
    (D : SimplePairData R M φ) :
    Polynomial (IsLocalRing.ResidueField R) :=
  letI : Module (IsLocalRing.ResidueField R) M := D.annihilated.module
  letI : Module.Finite (IsLocalRing.ResidueField R) M := D.finite_dimensional
  letI : Module.Free (IsLocalRing.ResidueField R) M :=
    Module.Free.of_divisionRing (IsLocalRing.ResidueField R) M
  D.residue_endomorphism.charpoly

/-! ## Stable composition series and the three invariants -/

/-- The quotient module belonging to a step of a composition series. -/
abbrev factorModule {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (s : CompositionSeries (Submodule R M)) (i : Fin s.length) : Type _ :=
  s (Fin.succ i) ⧸
    Submodule.comap (s (Fin.succ i)).subtype (s (Fin.castSucc i))

/-- Restrict an endomorphism to an invariant submodule. -/
def restrictToStableSubmodule
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (φ : Module.End R M) (N : Submodule R M)
    (hN : Submodule.map φ N ≤ N) : Module.End R N :=
  φ.restrict (fun x hx => hN ⟨x, hx, rfl⟩)

/-- The endomorphism induced on a composition factor. -/
def factorEnd
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (s : CompositionSeries (Submodule R M)) (φ : Module.End R M)
    (hstable : ∀ j, Submodule.map φ (s j) ≤ s j) (i : Fin s.length) :
    Module.End R (factorModule s i) := by
  let U := s (Fin.succ i)
  let L : Submodule R U :=
    Submodule.comap U.subtype (s (Fin.castSucc i))
  let fU : Module.End R U :=
    restrictToStableSubmodule φ U (hstable (Fin.succ i))
  let hL : L ≤ L.comap fU := by
    intro x hx
    change φ (x : M) ∈ s (Fin.castSucc i)
    exact hstable (Fin.castSucc i) ⟨x, hx, rfl⟩
  exact L.mapQ L fU hL

/-- A stable composition series together with the simple pair carried by every factor. -/
structure StableCompositionSeries
    {R : Type u} [CommRing R] [IsLocalRing R]
    (X : FiniteLengthEndomorphism.{u, v} R) where
  series : CompositionSeries (Submodule R X.carrier)
  head_eq_bot : series.head = ⊥
  last_eq_top : series.last = ⊤
  stable : ∀ j, Submodule.map X.endomorphism.hom (series j) ≤ series j
  simple_factor :
    ∀ i, SimplePairData R (factorModule series i)
      (factorEnd series X.endomorphism.hom stable i)

theorem exists_stableCompositionSeries
    {R : Type u} [CommRing R] [IsLocalRing R]
    (X : FiniteLengthEndomorphism.{u, v} R) :
    Nonempty (StableCompositionSeries X) := by
  sorry

noncomputable def stableCompositionSeries
    {R : Type u} [CommRing R] [IsLocalRing R]
    (X : FiniteLengthEndomorphism.{u, v} R) : StableCompositionSeries X :=
  Classical.choice (exists_stableCompositionSeries X)

noncomputable def determinant
    {R : Type u} [CommRing R] [IsLocalRing R]
    (X : FiniteLengthEndomorphism.{u, v} R) : IsLocalRing.ResidueField R :=
  let s := stableCompositionSeries X
  ∏ i, simpleDeterminant (s.simple_factor i)

noncomputable def trace
    {R : Type u} [CommRing R] [IsLocalRing R]
    (X : FiniteLengthEndomorphism.{u, v} R) : IsLocalRing.ResidueField R :=
  let s := stableCompositionSeries X
  ∑ i, simpleTrace (s.simple_factor i)

noncomputable def characteristicPolynomial
    {R : Type u} [CommRing R] [IsLocalRing R]
    (X : FiniteLengthEndomorphism.{u, v} R) :
    Polynomial (IsLocalRing.ResidueField R) :=
  let s := stableCompositionSeries X
  ∏ i, simpleCharacteristicPolynomial (s.simple_factor i)

/-! ## Lengths used in the base-change statements -/

noncomputable def finiteLengthNat
    (R M : Type*) [Ring R] [AddCommGroup M] [Module R M]
    (_hM : IsFiniteLength R M) : ℕ :=
  (Module.length R M).toNat

/-- The finite residue-field dimension of a simple factor. -/
noncomputable def residueFinrank
    {R M : Type*} [CommRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M] {φ : Module.End R M}
    (D : SimplePairData R M φ) : ℕ :=
  letI : Module (IsLocalRing.ResidueField R) M := D.annihilated.module
  Module.finrank (IsLocalRing.ResidueField R) M

/-- For a simple pair, the residue-field dimension is its `R`-length. -/
theorem simplePair_residueFinrank_eq_length
    {R M : Type*} [CommRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M] (hM : IsFiniteLength R M)
    {φ : Module.End R M} (D : SimplePairData R M φ) :
    residueFinrank D = finiteLengthNat R M hM := by
  sorry

/-! The following three interfaces record the Jordan--Hölder independence of the definitions. -/

theorem determinant_eq_stableCompositionSeries_product
    {R : Type u} [CommRing R] [IsLocalRing R]
    (X : FiniteLengthEndomorphism.{u, v} R) (s : StableCompositionSeries X) :
    determinant X =
      ∏ i : Fin s.series.length, simpleDeterminant (s.simple_factor i) := by
  sorry

theorem trace_eq_stableCompositionSeries_sum
    {R : Type u} [CommRing R] [IsLocalRing R]
    (X : FiniteLengthEndomorphism.{u, v} R) (s : StableCompositionSeries X) :
    trace X =
      ∑ i : Fin s.series.length, simpleTrace (s.simple_factor i) := by
  sorry

theorem characteristicPolynomial_eq_stableCompositionSeries_product
    {R : Type u} [CommRing R] [IsLocalRing R]
    (X : FiniteLengthEndomorphism.{u, v} R) (s : StableCompositionSeries X) :
    characteristicPolynomial X =
      ∏ i : Fin s.series.length, simpleCharacteristicPolynomial (s.simple_factor i) := by
  sorry

/-- Package a module endomorphism as a finite-length pair. -/
def ofModule
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (hM : IsFiniteLength R M) (φ : Module.End R M) :
    FiniteLengthEndomorphism R :=
  { carrier := ModuleCat.of R M
    finite_length := hM
    endomorphism := ModuleCat.ofHom φ }

noncomputable def determinantOf
    {R M : Type*} [CommRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M] (hM : IsFiniteLength R M)
    (φ : Module.End R M) : IsLocalRing.ResidueField R :=
  determinant (ofModule hM φ)

noncomputable def traceOf
    {R M : Type*} [CommRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M] (hM : IsFiniteLength R M)
    (φ : Module.End R M) : IsLocalRing.ResidueField R :=
  trace (ofModule hM φ)

noncomputable def characteristicPolynomialOf
    {R M : Type*} [CommRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M] (hM : IsFiniteLength R M)
    (φ : Module.End R M) : Polynomial (IsLocalRing.ResidueField R) :=
  characteristicPolynomial (ofModule hM φ)

end
