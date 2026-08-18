/-
# More on Algebra, Chapter 128: Splitting off a free module
-/

import Formalization.Books.Topology.Unit11.CodimensionAndCatenary
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.Algebra.Module.LocalizedModule.AtPrime
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Localization.Module
import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
import Mathlib.RingTheory.Spectrum.Maximal.Topology
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.Topology.KrullDimension
import Mathlib.Topology.NoetherianSpace

namespace Formalization.Books.MoreAlgebra.Unit128

open Set
open scoped TensorProduct

noncomputable section

universe u

/-! ## The source situation and its canonical fibre -/

variable {R M : Type u} [CommRing R] [AddCommGroup M] [Module R M]

/- The source's closed-point space `Ω` is Mathlib's maximal spectrum, whose
   topology is the subspace topology induced from the prime spectrum. -/

abbrev fibre (x : MaximalSpectrum R) : Type u := x.asIdeal.Fiber M

abbrev residueField (x : MaximalSpectrum R) : Type u := x.asIdeal.ResidueField

/- `1 ⊗ s` is the canonical image of a section in its residue-field fibre. -/
def fibreClass (x : MaximalSpectrum R) (s : M) : fibre (M := M) x :=
  (1 : residueField x) ⊗ₜ[R] s

/- The dual map in the source is the base change of a functional, followed by
   the canonical right-unit equivalence for tensor products. -/
noncomputable def fibreDualMap (x : MaximalSpectrum R) (φ : M →ₗ[R] R) :
    fibre (M := M) x →ₗ[residueField x] residueField x :=
  (TensorProduct.AlgebraTensorModule.rid R (residueField x) (residueField x)).toLinearMap.comp
    (φ.baseChange (residueField x))

@[simp]
theorem fibreDualMap_fibreClass (x : MaximalSpectrum R) (φ : M →ₗ[R] R) (s : M) :
    fibreDualMap x φ (fibreClass x s) = algebraMap R (residueField x) (φ s) := by
  simp [fibreDualMap, fibreClass, Algebra.smul_def]

/- The perpendicular `B(x)` is equivalently the intersection of the kernels
   of all functionals induced on the fibre. -/
noncomputable def B (x : MaximalSpectrum R) :
    Submodule (residueField x) (fibre (M := M) x) :=
  ⨅ φ : M →ₗ[R] R, LinearMap.ker (fibreDualMap x φ)

abbrev V (x : MaximalSpectrum R) : Type u := fibre (M := M) x ⧸ B x

def fibreToV (x : MaximalSpectrum R) :
    fibre (M := M) x →ₗ[residueField x] V (M := M) x :=
  (B x).mkQ

/- The inclusion of `B(x)` and the quotient map to `V(x)` form the source's
   canonical short exact sequence. -/
theorem b_fibre_v_short_exact (x : MaximalSpectrum R) :
    Function.Injective (B (M := M) x).subtype ∧
      Function.Exact (B (M := M) x).subtype (B (M := M) x).mkQ ∧
        Function.Surjective (B (M := M) x).mkQ := by
  sorry

/- The finite-presentation hypothesis in the situation implies that the
   source fibre, and hence its quotient `V(x)`, are finite-dimensional. -/
theorem finiteDimensional_fibre [Module.FinitePresentation R M]
    (x : MaximalSpectrum R) :
    FiniteDimensional (residueField x) (fibre (M := M) x) := by
  infer_instance

theorem finiteDimensional_V [Module.FinitePresentation R M]
    (x : MaximalSpectrum R) :
    FiniteDimensional (residueField x) (V (M := M) x) := by
  infer_instance

/-! ## The direct-summand criterion -/

/- The source's map after inverting `f` is represented by the canonical
   localized-module map from the localized finite free module. -/
noncomputable def localizedSectionMap {r : ℕ} (f : R) (s : Fin r → M) :
    LocalizedModule.Away f (Fin r →₀ R) →ₗ[Localization.Away f]
      LocalizedModule.Away f M :=
  LocalizedModule.map (Submonoid.powers f) (Finsupp.linearCombination R s)

def IsLocalizedDirectSummand {r : ℕ} (f : R) (s : Fin r → M) : Prop :=
  Function.Injective (localizedSectionMap f s) ∧
    IsComplemented (LinearMap.range (localizedSectionMap f s))

/- This is the source's assertion that the displayed map becomes the
   inclusion of a direct summand after inverting `f`. -/
theorem which_elements_split [Module.FinitePresentation R M]
    (x : MaximalSpectrum R) {r : ℕ} (s : Fin r → M) :
    (∃ f : R, f ∉ x.asIdeal ∧ IsLocalizedDirectSummand f s) ↔
      LinearIndependent (residueField x)
        (fun i => fibreToV x (fibreClass x (s i))) := by
  sorry

/-! ## The dependence locus and prescribed values -/

def Z {r : ℕ} (s : Fin r → M) : Set (MaximalSpectrum R) :=
  {x | ¬ LinearIndependent (residueField x)
    (fun i => fibreToV x (fibreClass x (s i)))}

theorem isClosed_Z [Module.FinitePresentation R M]
    {r : ℕ} (s : Fin r → M) : IsClosed (Z (R := R) s) := by
  sorry

theorem choose_values {n : ℕ} (x : Fin n → MaximalSpectrum R)
    (hx : Pairwise (fun i j => x i ≠ x j))
    (v : ∀ i, V (M := M) (x i)) :
    ∃ s : M, ∀ i, fibreToV (x i) (fibreClass (x i) s) = v i := by
  sorry

/-! ## Noetherian codimension bookkeeping -/

/- `irreducibleComponents F` is formed in the subspace `F`; this predicate is
   its ambient-space formulation, which is the form needed for codimension in
   `Ω`. -/
def IsAmbientIrreducibleComponent {X : Type u} [TopologicalSpace X]
    (F : Set X) (Y : TopologicalSpace.IrreducibleCloseds X) : Prop :=
  (Y : Set X) ⊆ F ∧
    ∀ Z : TopologicalSpace.IrreducibleCloseds X,
      (Z : Set X) ⊆ F → (Y : Set X) ⊆ Z → Z = Y

def ComponentsHaveCodimensionAtLeast {X : Type u} [TopologicalSpace X]
    (F : Set X) (k : ℕ) : Prop :=
  ∀ Y : TopologicalSpace.IrreducibleCloseds X,
    IsAmbientIrreducibleComponent F Y →
      (k : ℕ∞) ≤ Formalization.Books.Topology.Unit11.codimension Y

/- The proposition below is the source's Serre induction step.  The finite
   index types encode the displayed finite lists of sections and points. -/
theorem proposition_splitting
    [Module.FinitePresentation R M]
    [TopologicalSpace.NoetherianSpace (MaximalSpectrum R)]
    {h : ℕ} (s : Fin h → M) (F : Set (MaximalSpectrum R))
    (hF : IsClosed F) (hZF : Z (R := R) s ⊆ F)
    {n : ℕ} (x : Fin n → MaximalSpectrum R)
    (hxF : ∀ i, x i ∈ F)
    (hx : Pairwise (fun i j => x i ≠ x j))
    (v : ∀ i, V (M := M) (x i)) (k : ℕ)
    (hbound : ∀ y : MaximalSpectrum R,
      h + k ≤ Module.finrank (residueField y) (V (M := M) y)) :
    ∃ t : M, ∃ F' : Set (MaximalSpectrum R),
      IsClosed F' ∧
      (∀ i, fibreToV (x i) (fibreClass (x i) t) = v i) ∧
      Z (R := R) (Fin.snoc s t) ⊆ F ∪ F' ∧
      ComponentsHaveCodimensionAtLeast F' k := by
  sorry

/-! ## Splitting off a free summand -/

/- A free direct summand of a localized module is represented by a
   complemented submodule carrying the canonical `Module.Free` instance. -/
def HasFreeDirectSummandAbove (A N : Type u) [CommRing A]
    [AddCommGroup N] [Module A N] (d : ℕ) : Prop :=
  ∃ K : Submodule A N,
    IsComplemented K ∧ Module.Free A K ∧
      (d : Cardinal) < Module.rank A K

theorem splitting_off_free
    [Module.FinitePresentation R M]
    [TopologicalSpace.NoetherianSpace (MaximalSpectrum R)]
    (d : ℕ)
    (hdim : topologicalKrullDim (MaximalSpectrum R) = d)
    (hfree : ∀ m : MaximalSpectrum R,
      HasFreeDirectSummandAbove (Localization.AtPrime m.asIdeal)
        (LocalizedModule.AtPrime m.asIdeal M) d) :
    ∃ (M' : Type u) (_ : AddCommGroup M') (_ : Module R M'),
      Nonempty (M ≃ₗ[R] R × M') := by
  sorry

end

end Formalization.Books.MoreAlgebra.Unit128
