import Formalization.Books.MoreAlgebra.Unit22.TorsionFree
import Formalization.Books.Algebra.Unit157.SerresCriterion
import Mathlib.Algebra.Module.LocalizedModule.AtPrime
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.MvPolynomial.Basic

/-!
# More on Algebra, Chapter 24: Reflexive modules

The source's reflexive-module predicate is delegated to Mathlib's canonical
`Module.IsReflexive` class.  The fractional-module intersections below use
concrete tensor-product models for `M_K`; this makes the source's phrase
“taken in `M_K`” an explicit set or submodule equality.
-/

namespace Formalization.Books.MoreAlgebra.Unit24

open Set
open Formalization.Books.Algebra.Unit37
open Formalization.Books.Algebra.Unit63
open Formalization.Books.Algebra.Unit72
open Formalization.Books.Algebra.Unit157
open scoped TensorProduct

universe u v w

noncomputable section

/-! ## Reflexivity and the double dual -/

/-- The source's reflexive-module predicate, using Mathlib's canonical class. -/
abbrev Reflexive (R M : Type*) [CommRing R] [AddCommGroup M]
    [Module R M] : Prop :=
  Module.IsReflexive R M

/-! The source notes that this definition has wider variants, but recommends
the Noetherian, finite, torsion-free setting used by the results below. -/

/-- The natural map from a module to its double dual. -/
abbrev reflexivityMap
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] :
    M →ₗ[R] Module.Dual R (Module.Dual R M) :=
  Module.Dual.eval R M

@[simp]
theorem reflexivityMap_apply
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (m : M) (φ : Module.Dual R M) :
    reflexivityMap (R := R) (M := M) m φ = φ m := by
  rfl

/-- Reflexivity is exactly bijectivity of the natural evaluation map. -/
theorem reflexive_iff_bijective_reflexivityMap
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] :
    Reflexive R M ↔ Function.Bijective (reflexivityMap (R := R) (M := M)) := by
  sorry

/-- A reflexive module is torsion free. -/
theorem reflexive_torsionFree
    {R M : Type*} [CommRing R] [IsDomain R]
    [AddCommGroup M] [Module R M]
    (hM : Reflexive R M) :
    Module.IsTorsionFree R M := by
  sorry

/-- For a finite module, the kernel and cokernel of the natural map are
torsion modules.  The cokernel is represented by the quotient by its range. -/
theorem dualEval_kernel_cokernel_isTorsion
    {R M : Type*} [CommRing R] [IsDomain R]
    [AddCommGroup M] [Module R M] [Module.Finite R M] :
    Module.IsTorsion R (LinearMap.ker (reflexivityMap (R := R) (M := M))) ∧
      Module.IsTorsion R
        (Module.Dual R (Module.Dual R M) ⧸
          LinearMap.range (reflexivityMap (R := R) (M := M))) := by
  sorry

/-- For a finite module over a domain, the natural map is injective exactly
when the module is torsion free. -/
theorem dualEval_injective_iff_torsionFree
    {R M : Type*} [CommRing R] [IsDomain R]
    [AddCommGroup M] [Module R M] [Module.Finite R M] :
    Function.Injective (reflexivityMap (R := R) (M := M)) ↔
      Module.IsTorsionFree R M := by
  sorry

/-- Over a discrete valuation ring, the natural map is surjective for every
finite module, including modules with torsion. -/
theorem dualEval_surjective_of_discreteValuationRing
    {R M : Type*} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] :
    Function.Surjective (reflexivityMap (R := R) (M := M)) := by
  sorry

/-! ## Locality and exact sequences -/

/-- Reflexivity of a finite module over a Noetherian domain can be checked at
all primes or at all maximal ideals. -/
theorem reflexive_localization_iff
    {R M : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M] :
    List.TFAE
      [Reflexive R M,
       ∀ p : PrimeSpectrum R,
         Reflexive (Localization.AtPrime p.asIdeal)
           (LocalizedModule.AtPrime p.asIdeal M),
       ∀ m : MaximalSpectrum R,
         Reflexive (Localization.AtPrime m.asIdeal)
           (LocalizedModule.AtPrime m.asIdeal M)] := by
  sorry

/-- In an exact sequence `0 → M → M' → M''`, reflexivity descends from the
middle term when the right term is torsion free. -/
theorem reflexive_of_exact
    {R M M' M'' : Type*} [CommRing R] [IsDomain R]
    [IsNoetherianRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M]
    [AddCommGroup M'] [Module R M'] [Module.Finite R M']
    [AddCommGroup M''] [Module R M''] [Module.Finite R M'']
    (f : M →ₗ[R] M') (g : M' →ₗ[R] M'')
    (hf : Function.Injective f)
    (hfg : Function.Exact (f : M → M') (g : M' → M''))
    (hM' : Reflexive R M')
    (hM'' : Module.IsTorsionFree R M'') :
    Reflexive R M := by
  sorry

/-- Characterization of finite reflexive modules by a finite-free presentation
whose cokernel is torsion free. -/
theorem reflexive_iff_finiteFree_presentation
    {R M : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M] :
    Reflexive R M ↔
      ∃ (F : Type u) (_ : AddCommGroup F) (_ : Module R F)
        (_ : Module.Finite R F) (_ : Module.Free R F)
        (N : Type u) (_ : AddCommGroup N) (_ : Module R N)
        (f : M →ₗ[R] F) (g : F →ₗ[R] N),
        Function.Injective f ∧
          Function.Exact (f : M → F) (g : F → N) ∧
            Function.Surjective g ∧ Module.IsTorsionFree R N := by
  sorry

/-- Flat base change of a finite reflexive module between Noetherian domains
is finite and reflexive. -/
theorem reflexive_flat_baseChange
    {R R' M : Type*} [CommRing R] [CommRing R']
    [IsDomain R] [IsDomain R'] [IsNoetherianRing R] [IsNoetherianRing R']
    [Algebra R R'] [Module.Flat R R']
    [AddCommGroup M] [Module R M] [Module.Finite R M]
    (hM : Reflexive R M) :
    Module.Finite R' (R' ⊗[R] M) ∧
      Reflexive R' (R' ⊗[R] M) := by
  sorry

/-- The Hom module into a finite reflexive module is reflexive. -/
theorem hom_into_reflexive_isReflexive
    {R M N : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M]
    [AddCommGroup N] [Module R N] [Module.Finite R N]
    (hN : Reflexive R N) :
    Reflexive R (M →ₗ[R] N) := by
  sorry

/-! ## Reflexive hull -/

/-- The double dual of a finite module, called its reflexive hull in the
source. -/
abbrev reflexiveHull
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] : Type _ :=
  Module.Dual R (Module.Dual R M)

/-- Under the finite Noetherian-domain hypotheses of the source, the double
dual is itself reflexive. -/
theorem reflexiveHull_isReflexive
    {R M : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M] :
    Reflexive R (reflexiveHull (R := R) (M := M)) := by
  sorry

/-- The map induced on reflexive hulls by a module map. -/
def reflexiveHullMap
    {R M N : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) :
    reflexiveHull (R := R) (M := M) →ₗ[R]
      reflexiveHull (R := R) (M := N) :=
  f.dualMap.dualMap

@[simp]
theorem reflexiveHullMap_id
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] :
    reflexiveHullMap (LinearMap.id : M →ₗ[R] M) = LinearMap.id := by
  sorry

theorem reflexiveHullMap_comp
    {R M N P : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [AddCommGroup P] [Module R P]
    (f : M →ₗ[R] N) (g : N →ₗ[R] P) :
    reflexiveHullMap (g.comp f) =
      (reflexiveHullMap g).comp (reflexiveHullMap f) := by
  sorry

/-- The canonical factor through the reflexive hull of a map into a reflexive
module. -/
noncomputable def reflexiveHullFactor
    {R M N : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [Module.IsReflexive R N] (f : M →ₗ[R] N) :
    reflexiveHull (R := R) (M := M) →ₗ[R] N :=
  (Module.evalEquiv R N).symm.toLinearMap.comp (reflexiveHullMap f)

/-- The canonical hull factor restricts to the original map. -/
theorem reflexiveHullFactor_comp_reflexivityMap
    {R M N : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [Module.IsReflexive R N] (f : M →ₗ[R] N) :
    (reflexiveHullFactor f).comp (reflexivityMap (R := R) (M := M)) = f := by
  sorry

/-- The hull factor is the unique factor through the natural evaluation map. -/
theorem reflexiveHullFactor_unique
    {R M N : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [Module.IsReflexive R N] (f : M →ₗ[R] N)
    (g : reflexiveHull (R := R) (M := M) →ₗ[R] N)
    (hg : g.comp (reflexivityMap (R := R) (M := M)) = f) :
    g = reflexiveHullFactor f := by
  sorry

/-! ## Hom modules, depth, and Serre conditions -/

/-- Hom into a module of depth at least one has depth at least one. -/
theorem hom_depth_ge_one
    {R M N : Type*} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M]
    [AddCommGroup N] [Module R N] [Module.Finite R N]
    (hN : 1 ≤ localDepth R N) :
    1 ≤ localDepth R (M →ₗ[R] N) := by
  sorry

/-- Hom into a module of depth at least two has depth at least two. -/
theorem hom_depth_ge_two
    {R M N : Type*} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M]
    [AddCommGroup N] [Module R N] [Module.Finite R N]
    (hN : 2 ≤ localDepth R N) :
    2 ≤ localDepth R (M →ₗ[R] N) := by
  sorry

/-- Hom preserves the module `(S_1)` and `(S_2)` conditions. -/
theorem hom_hasPropertySkModule
    {R M N : Type*} [CommRing R] [IsNoetherianRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M]
    [AddCommGroup N] [Module R N] [Module.Finite R N] :
    (HasPropertySkModule R N 1 → HasPropertySkModule R (M →ₗ[R] N) 1) ∧
      (HasPropertySkModule R N 2 → HasPropertySkModule R (M →ₗ[R] N) 2) := by
  sorry

/-- Over a domain, Hom into a torsion-free `(S_2)` module is torsion-free and
`(S_2)`. -/
theorem hom_torsionFree_hasPropertySkModule
    {R M N : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M]
    [AddCommGroup N] [Module R N] [Module.Finite R N]
    (hN₁ : Module.IsTorsionFree R N)
    (hN₂ : HasPropertySkModule R N 2) :
    Module.IsTorsionFree R (M →ₗ[R] N) ∧
      HasPropertySkModule R (M →ₗ[R] N) 2 := by
  sorry

/-! ## Associated-prime tests for maps -/

/-- Injectivity can be checked after localization at associated primes. -/
theorem injective_of_localized_injective_or_not_associated
    {R M N : Type*} [CommRing R] [IsNoetherianRing R]
    [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N]
    (φ : M →ₗ[R] N)
    (hφ : ∀ p : PrimeSpectrum R,
      Function.Injective
          (LocalizedModule.map p.asIdeal.primeCompl φ) ∨
        p ∉ Formalization.Books.Algebra.Unit63.associatedPrimes R M) :
    Function.Injective φ := by
  sorry

/-- A finite map is an isomorphism when it is locally an isomorphism or its
source has depth at least two away from the associated primes of the target. -/
theorem isomorphism_of_localized_isomorphism_or_depth_two
    {R M N : Type*} [CommRing R] [IsNoetherianRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M]
    [AddCommGroup N] [Module R N]
    (φ : M →ₗ[R] N)
    (hφ : ∀ p : PrimeSpectrum R,
      Function.Bijective
          (LocalizedModule.map p.asIdeal.primeCompl φ) ∨
        (2 ≤ localDepth (Localization.AtPrime p.asIdeal)
              (LocalizedModule.AtPrime p.asIdeal M) ∧
          p ∉ Formalization.Books.Algebra.Unit63.associatedPrimes R N)) :
    Function.Bijective φ := by
  sorry

/-- The preceding isomorphism criterion specializes to a torsion-free target
over a Noetherian domain. -/
theorem isomorphism_of_depth_two_torsionFree_target
    {R M N : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M]
    [AddCommGroup N] [Module R N]
    (φ : M →ₗ[R] N) (hN : Module.IsTorsionFree R N)
    (hφ : ∀ p : PrimeSpectrum R,
      Function.Bijective
          (LocalizedModule.map p.asIdeal.primeCompl φ) ∨
        2 ≤ localDepth (Localization.AtPrime p.asIdeal)
          (LocalizedModule.AtPrime p.asIdeal M)) :
    Function.Bijective φ := by
  sorry

/-- Reflexivity is equivalent to local reflexivity or depth at least two at
every prime. -/
theorem reflexive_iff_local_reflexive_or_depth_two
    {R M : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M] :
    Reflexive R M ↔
      ∀ p : PrimeSpectrum R,
        Reflexive (Localization.AtPrime p.asIdeal)
            (LocalizedModule.AtPrime p.asIdeal M) ∨
          2 ≤ localDepth (Localization.AtPrime p.asIdeal)
            (LocalizedModule.AtPrime p.asIdeal M) := by
  sorry

/-- A finite reflexive module has depth at least two wherever the ring has
depth at least two. -/
theorem reflexive_local_depth_ge_two
    {R M : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M]
    (hM : Reflexive R M) (p : PrimeSpectrum R)
    (hR : 2 ≤ localDepth (Localization.AtPrime p.asIdeal)
      (Localization.AtPrime p.asIdeal)) :
    2 ≤ localDepth (Localization.AtPrime p.asIdeal)
      (LocalizedModule.AtPrime p.asIdeal M) := by
  sorry

/-- If a Noetherian domain has property `(S_2)`, a finite reflexive module has
the module property `(S_2)`. -/
theorem reflexive_hasPropertySkModule_two
    {R M : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M]
    (hM : Reflexive R M) (hR : HasPropertySk R 2) :
    HasPropertySkModule R M 2 := by
  sorry

/-! ## The example separating reflexivity from `(S_2)` -/

/-- The subalgebra `k[y, x², xy, x³]` of `k[x, y]`, with the redundant
generator `1` retained to mirror the source. -/
def exampleRing (k : Type u) [Field k] :
    Subalgebra k (MvPolynomial (Fin 2) k) :=
  Algebra.adjoin k
    ({1, MvPolynomial.X (1 : Fin 2),
      (MvPolynomial.X (0 : Fin 2)) ^ 2,
      MvPolynomial.X (0 : Fin 2) * MvPolynomial.X (1 : Fin 2),
      (MvPolynomial.X (0 : Fin 2)) ^ 3} : Set (MvPolynomial (Fin 2) k))

def exampleY (k : Type u) [Field k] : exampleRing k :=
  ⟨MvPolynomial.X (1 : Fin 2), by
    exact Algebra.subset_adjoin (by simp)⟩

def exampleXSquared (k : Type u) [Field k] : exampleRing k :=
  ⟨(MvPolynomial.X (0 : Fin 2)) ^ 2, by
    exact Algebra.subset_adjoin (by simp)⟩

def exampleXY (k : Type u) [Field k] : exampleRing k :=
  ⟨MvPolynomial.X (0 : Fin 2) * MvPolynomial.X (1 : Fin 2), by
    exact Algebra.subset_adjoin (by simp)⟩

def exampleXCubed (k : Type u) [Field k] : exampleRing k :=
  ⟨(MvPolynomial.X (0 : Fin 2)) ^ 3, by
    exact Algebra.subset_adjoin (by simp)⟩

/-- The ideal `(y, x², xy, x³)` in the example ring. -/
def exampleMaximalIdeal (k : Type u) [Field k] : Ideal (exampleRing k) :=
  Ideal.span ({exampleY k, exampleXSquared k, exampleXY k, exampleXCubed k} :
    Set (exampleRing k))

/-- The example ring is not `(S_2)`. -/
theorem exampleRing_not_hasPropertySk_two
    (k : Type u) [Field k] :
    ¬ HasPropertySk (exampleRing k) 2 := by
  sorry

/-- The example ring is reflexive over itself. -/
theorem exampleRing_reflexive_as_module
    (k : Type u) [Field k] :
    Reflexive (exampleRing k) (exampleRing k) := by
  sorry

/-- The ambient polynomial module in the example is reflexive and `(S_2)`;
the existential records the finite-module instance required by the canonical
module-form Serre predicate. -/
theorem exampleModule_reflexive_and_hasPropertySk_two
    (k : Type u) [Field k] :
    ∃ hM : Module.Finite (exampleRing k) (MvPolynomial (Fin 2) k),
      Reflexive (exampleRing k) (MvPolynomial (Fin 2) k) ∧
        @HasPropertySkModule (exampleRing k) (MvPolynomial (Fin 2) k)
          _ _ _ hM 2 := by
  sorry

/-- The two Hom identities in the example, represented as linear
equivalences. -/
theorem example_hom_identities
    (k : Type u) [Field k] :
    Nonempty
        ((MvPolynomial (Fin 2) k →ₗ[exampleRing k] exampleRing k) ≃ₗ[
          exampleRing k] exampleMaximalIdeal k) ∧
      Nonempty
        ((exampleMaximalIdeal k →ₗ[exampleRing k] exampleRing k) ≃ₗ[
          exampleRing k] MvPolynomial (Fin 2) k) := by
  sorry

/-! ## Normal domains and height-one intersections -/

/-- The fraction-field map with the field in the left tensor factor.  This is
the tensor-product commutation of the map used in Unit 22, and gives the
target its natural `K`-module structure. -/
def fractionFieldTensorMapLeft
    (R M K : Type*) [CommRing R] [IsDomain R]
    [AddCommGroup M] [Module R M] [Field K] [Algebra R K]
    [IsFractionRing R K] :
    M →ₗ[R] K ⊗[R] M :=
  (TensorProduct.comm R M K).toLinearMap.comp
    (Formalization.Books.MoreAlgebra.Unit22.fractionFieldTensorMap
      (R := R) (M := M) (K := K))

/-- The image in `K ⊗[R] M` of the localization of `M` at a height-one
prime, after its local torsion is killed by the fraction-field map. -/
def heightOneModuleLocalizationImage
    (R M K : Type*) [CommRing R] [IsDomain R]
    [AddCommGroup M] [Module R M] [Field K] [Algebra R K]
    [IsFractionRing R K]
    (p : {p : PrimeSpectrum R // p.asIdeal.height = 1}) :
    Submodule R (K ⊗[R] M) :=
  Submodule.span R {z | ∃ m : M, ∃ s : R,
    s ∉ p.1.asIdeal ∧
      z = (algebraMap R K s)⁻¹ •
        fractionFieldTensorMapLeft (R := R) (M := M) (K := K) m}

/-- The intersection of all height-one localized module images. -/
def heightOneModuleLocalizationIntersection
    (R M K : Type*) [CommRing R] [IsDomain R]
    [AddCommGroup M] [Module R M] [Field K] [Algebra R K]
    [IsFractionRing R K] :
    Submodule R (K ⊗[R] M) :=
  ⨅ p : {p : PrimeSpectrum R // p.asIdeal.height = 1},
    heightOneModuleLocalizationImage R M K p

/-- The fraction-field map after quotienting by the torsion submodule. -/
noncomputable def fractionFieldTensorMapQuotient
    (R M K : Type*) [CommRing R] [IsDomain R]
    [AddCommGroup M] [Module R M] [Field K] [Algebra R K]
    [IsFractionRing R K] :
    (M ⧸ Submodule.torsion R M) →ₗ[R] K ⊗[R] M :=
  (TensorProduct.comm R M K).toLinearMap.comp
    ((Submodule.torsion R M).liftQ
      (Formalization.Books.MoreAlgebra.Unit22.fractionFieldTensorMap
        (R := R) (M := M) (K := K))
      (by
        rw [Formalization.Books.MoreAlgebra.Unit22.torsion_eq_ker_fractionFieldTensorMap
          (R := R) (M := M) (K := K)]))

/-- The height-one intersection written using the torsion-free quotient. -/
def heightOneTorsionQuotientIntersection
    (R M K : Type*) [CommRing R] [IsDomain R]
    [AddCommGroup M] [Module R M] [Field K] [Algebra R K]
    [IsFractionRing R K] :
    Submodule R (K ⊗[R] M) :=
  ⨅ p : {p : PrimeSpectrum R // p.asIdeal.height = 1},
    Submodule.span R {z | ∃ m : M ⧸ Submodule.torsion R M, ∃ s : R,
      s ∉ p.1.asIdeal ∧
        z = (algebraMap R K s)⁻¹ •
          fractionFieldTensorMapQuotient R M K m}

/-- The three equivalent characterizations of a finite module over a
Noetherian normal domain: reflexivity, torsion-free `(S_2)`, and the
height-one intersection criterion. -/
theorem reflexive_normal_iff_torsionFree_S2_heightOne
    {R M K : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [IsIntegrallyClosed R]
    [AddCommGroup M] [Module R M] [Module.Finite R M]
    [Field K] [Algebra R K] [IsFractionRing R K] :
    List.TFAE
      [Reflexive R M,
       Module.IsTorsionFree R M ∧ HasPropertySkModule R M 2,
       Module.IsTorsionFree R M ∧
         Set.range (fractionFieldTensorMapLeft (R := R) (M := M) (K := K)) =
           (heightOneModuleLocalizationIntersection R M K : Set (K ⊗[R] M))] := by
  sorry

/-- The reflexive hull is modeled by the height-one intersection; the two
displayed source intersections agree after using the torsion-free quotient. -/
theorem reflexiveHull_heightOne_intersection
    {R M K : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [IsIntegrallyClosed R]
    [AddCommGroup M] [Module R M] [Module.Finite R M]
    [Field K] [Algebra R K] [IsFractionRing R K] :
    Nonempty
        (reflexiveHull (R := R) (M := M) ≃ₗ[R]
          heightOneModuleLocalizationIntersection R M K) ∧
      heightOneModuleLocalizationIntersection R M K =
        heightOneTorsionQuotientIntersection R M K := by
  sorry

/-! ## Integral closures -/

/-- A finite integral closure in a finite field extension of a fraction field
is reflexive over a Noetherian normal domain. -/
theorem integralClosure_reflexive
    {A K L : Type*} [CommRing A] [IsNoetherianRing A]
    [IsDomain A] [IsIntegrallyClosed A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    [Field L] [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    [Module.Finite K L]
    [Module.Finite A (integralClosure A L)] :
    Reflexive A (integralClosure A L) := by
  sorry

end

end Formalization.Books.MoreAlgebra.Unit24
