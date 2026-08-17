import Formalization.Books.Algebra.Unit89.InterchangingDirectProductsWithTensor
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.Valuation.ValuationRing

/-!
# Commutative Algebra, Chapter 90: Coherent rings

Coherent modules are defined using Mathlib's canonical notions of finite
generation and finite presentation.  Short exact sequences are represented by
`ShortComplex.ShortExact` in the category of modules, and the category of
coherent modules is the corresponding full subcategory.
-/

namespace Formalization.Books.Algebra.Unit90

open CategoryTheory
open Formalization.Books.Algebra.Unit89

universe u v w

noncomputable section

/-! ## Coherent modules and coherent rings -/

/-- A module is coherent when it is finitely generated and each finitely
generated submodule is finitely presented. -/
def IsCoherentModule (R : Type u) [CommRing R] (M : ModuleCat.{v} R) : Prop :=
  Module.Finite R (M : Type v) ∧
    ∀ N : Submodule R (M : Type v),
      Module.Finite R (N : Type v) →
        Module.FinitePresentation R (N : Type v)

/-- A ring is coherent when it is coherent as a module over itself. -/
def IsCoherentRing (R : Type u) [CommRing R] : Prop :=
  IsCoherentModule R (ModuleCat.of R R)

/-- The module formulation of coherence specializes to finitely generated
ideals in the regular module. -/
theorem coherentRing_iff_finitelyPresented_ideals
    (R : Type u) [CommRing R] :
    IsCoherentRing R ↔
      ∀ I : Ideal R, I.FG → Module.FinitePresentation R (I : Type u) := by
  sorry

/-! ## The coherent-module category -/

/-- The object property defining the full category of coherent modules. -/
def coherentModuleProperty (R : Type u) [CommRing R] :
    ObjectProperty (ModuleCat.{v} R) :=
  fun M => IsCoherentModule R M

/-- The category of coherent `R`-modules. -/
abbrev CoherentModuleCat (R : Type u) [CommRing R] :=
  (coherentModuleProperty.{u, v} R).FullSubcategory

/-- The category of coherent modules is abelian. -/
instance coherentModuleCat_abelian
    (R : Type u) [CommRing R] : Abelian (CoherentModuleCat.{u, v} R) := by
  sorry

/-! ## Permanence of coherence -/

/-- A finitely generated submodule of a coherent module is coherent. -/
theorem coherent_submodule_of_finite
    {R : Type u} [CommRing R] {M : ModuleCat.{v} R}
    (hM : IsCoherentModule R M) (N : Submodule R (M : Type v))
    (hN : Module.Finite R (N : Type v)) :
    IsCoherentModule R (ModuleCat.of R (N : Type v)) := by
  sorry

/-- The kernel, image, and cokernel of a map from a finitely generated module
to a coherent module have the finiteness properties in the source. -/
theorem coherent_kernel_image_cokernel_of_finite
    {R : Type u} [CommRing R] {N M : ModuleCat.{v} R}
    (φ : N ⟶ M) (hN : Module.Finite R (N : Type v))
    (hM : IsCoherentModule R M) :
    Module.Finite R (LinearMap.ker φ.hom) ∧
      IsCoherentModule R (ModuleCat.of R (LinearMap.range φ.hom)) ∧
        IsCoherentModule R
          (ModuleCat.of R ((M : Type v) ⧸ LinearMap.range φ.hom)) := by
  sorry

/-- Kernels and cokernels of maps between coherent modules are coherent. -/
theorem coherent_kernel_cokernel_of_coherent
    {R : Type u} [CommRing R] {N M : ModuleCat.{v} R}
    (φ : N ⟶ M) (hN : IsCoherentModule R N)
    (hM : IsCoherentModule R M) :
    IsCoherentModule R (ModuleCat.of R (LinearMap.ker φ.hom)) ∧
      IsCoherentModule R
        (ModuleCat.of R ((M : Type v) ⧸ LinearMap.range φ.hom)) := by
  sorry

/-- In a short exact sequence, any two coherent modules imply coherence of the
third. -/
theorem coherent_of_shortExact
    {R : Type u} [CommRing R]
    {S : ShortComplex (ModuleCat.{v} R)} (hS : S.ShortExact) :
    (IsCoherentModule R S.X₁ ∧ IsCoherentModule R S.X₂ →
        IsCoherentModule R S.X₃) ∧
      (IsCoherentModule R S.X₁ ∧ IsCoherentModule R S.X₃ →
        IsCoherentModule R S.X₂) ∧
        (IsCoherentModule R S.X₂ ∧ IsCoherentModule R S.X₃ →
          IsCoherentModule R S.X₁) := by
  sorry

/-! ## Coherent rings -/

/-- A valuation ring is coherent. -/
theorem valuationRing_isCoherent
    {R : Type u} [CommRing R] [IsDomain R] [ValuationRing R] :
    IsCoherentRing R := by
  sorry

/-- Over a coherent ring, coherence of a module is equivalent to finite
presentation. -/
theorem coherentModule_iff_finitePresentation
    {R : Type u} [CommRing R] (hR : IsCoherentRing R)
    (M : ModuleCat.{v} R) :
    IsCoherentModule R M ↔ Module.FinitePresentation R (M : Type v) := by
  sorry

/-- A Noetherian ring is coherent. -/
theorem isCoherentRing_of_isNoetherianRing
    (R : Type u) [CommRing R] [IsNoetherianRing R] :
    IsCoherentRing R := by
  sorry

/-! ## Products of flat modules -/

/-- Chase's characterization of coherent rings by products of flat modules. -/
theorem coherentRing_characterization
    (R : Type u) [CommRing R] :
    List.TFAE [
      IsCoherentRing R,
      ∀ (A : Type v) (Q : A → ModuleCat.{w} R),
        (∀ a, Module.Flat R (Q a : Type w)) →
          Module.Flat R (∀ a, (Q a : Type w)),
      ∀ (A : Type v), Module.Flat R (modulePower R A)
    ] := by
  sorry

end

end Formalization.Books.Algebra.Unit90
