import Formalization.Books.Algebra.Unit82.UniversallyInjective
import Formalization.Books.Algebra.Unit87.InverseSystems
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.DualNumber
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.LinearAlgebra.TensorProduct.Basic

/-!
# Commutative Algebra, Chapter 88: Mittag-Leffler modules

The source's directed systems are represented by functors from a directed
preorder to `ModuleCat`.  For a fixed target module, the inverse system of
duals is written explicitly using precomposition with the transition maps;
the Mittag-Leffler predicate itself is Mathlib's `Functor.IsMittagLeffler`.
-/

namespace Formalization.Books.Algebra.Unit88

open CategoryTheory
open CategoryTheory.Limits
open Formalization.Books.Algebra.Unit82
open Formalization.Books.Categories.Unit21
open scoped TensorProduct

universe u v w z

noncomputable section

/-! ## Directed systems and their dual inverse systems -/

/-- The inverse system of `R`-linear duals of a directed module diagram. -/
def homInverseSystem
    {R : Type u} [CommRing R] {I : Type v} [Preorder I]
    (D : System I (ModuleCat.{w} R)) (N : ModuleCat.{z} R) :
    InverseSystem I (Type (max w z)) where
  obj i := (D.obj i.unop : Type w) →ₗ[R] (N : Type z)
  map f := ↾(fun φ => φ.comp (D.map f.unop).hom)
  map_id i := by
    ext φ x
    simp
  map_comp f g := by
    ext φ x
    simp [LinearMap.comp_apply]

/-- A directed module system is Mittag-Leffler when its stages are finitely
presented and every inverse system of duals is Mittag-Leffler. -/
def IsMittagLefflerDirectedSystem
    {R : Type u} [CommRing R] {I : Type v} [Preorder I]
    [Nonempty I] [IsDirectedOrder I]
    (D : System I (ModuleCat.{w} R)) : Prop :=
  (∀ i, Module.FinitePresentation R (D.obj i)) ∧
    ∀ N : ModuleCat.{z} R, (homInverseSystem D N).IsMittagLeffler

/-- The transition map of a module diagram, in the source's linear-map form. -/
def directedMap
    {R : Type u} [CommRing R] {I : Type v} [Preorder I]
    (D : System I (ModuleCat.{w} R)) {i j : I} (h : i ≤ j) :
    (D.obj i : Type w) →ₗ[R] (D.obj j : Type w) :=
  (D.map (homOfLE h)).hom

/-- The canonical map from a stage of a colimit presentation to its target. -/
def colimitComponentMap
    {R : Type u} [CommRing R] {I : Type v} [Preorder I]
    {M : ModuleCat.{w} R} (P : ColimitPresentation I M) (i : I) :
    (P.diag.obj i : Type w) →ₗ[R] (M : Type w) :=
  (P.ι.app i).hom

/-! ## Domination -/

/-- A map `g` dominates a map `f` when every tensor-kernel of `f` is contained
in the corresponding tensor-kernel of `g`. -/
def dominates
    {R : Type u} [CommRing R] {M N N' : Type w}
    [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N]
    [AddCommGroup N'] [Module R N']
    (g : M →ₗ[R] N') (f : M →ₗ[R] N) : Prop :=
  ∀ (Q : Type (max u w)) [AddCommGroup Q] [Module R Q],
    LinearMap.ker (f.rTensor Q) ≤ LinearMap.ker (g.rTensor Q)

/-- Two maps dominate each other. -/
def mutuallyDominates
    {R : Type u} [CommRing R] {M N N' : Type w}
    [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N]
    [AddCommGroup N'] [Module R N']
    (g : M →ₗ[R] N') (f : M →ₗ[R] N) : Prop :=
  dominates g f ∧ dominates f g

/-- Tensor-kernel inclusion only needs to be tested on finitely presented
modules. -/
theorem dominates_iff_finitelyPresented
    {R : Type u} [CommRing R] {M N N' : Type w}
    [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N]
    [AddCommGroup N'] [Module R N']
    (g : M →ₗ[R] N') (f : M →ₗ[R] N) :
    dominates g f ↔
      ∀ (Q : Type (max u w)) [AddCommGroup Q] [Module R Q],
        Module.FinitePresentation R Q →
          LinearMap.ker (f.rTensor Q) ≤ LinearMap.ker (g.rTensor Q) := by
  sorry

/-- Domination is equivalent to universal injectivity of the map from the
second leg into the pushout. -/
theorem dominates_iff_pushout_inr_universallyInjective
    {R : Type u} [CommRing R] {M N N' : Type w}
    [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N]
    [AddCommGroup N'] [Module R N']
    (f : M →ₗ[R] N) (g : M →ₗ[R] N') :
    dominates g f ↔
      universallyInjective
        ((pushout.inr (ModuleCat.ofHom f) (ModuleCat.ofHom g)).hom) := by
  sorry

/-- If the cokernel of `f` is finitely presented, domination is the usual
factorization relation. -/
theorem dominates_iff_factors_of_finitelyPresented_cokernel
    {R : Type u} [CommRing R] {M N N' : Type w}
    [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N]
    [AddCommGroup N'] [Module R N']
    (f : M →ₗ[R] N) (g : M →ₗ[R] N')
    (h : Module.FinitePresentation R
      (N ⧸ LinearMap.range f)) :
    dominates g f ↔ ∃ h' : N →ₗ[R] N', g = h'.comp f := by
  sorry

/-! ## The five equivalent characterizations -/

/-- The first condition in the source's characterization of a Mittag-Leffler
module. -/
def MLModuleCondition
    {R : Type u} [CommRing R] (M : ModuleCat.{w} R) : Prop :=
  ∀ (P : ModuleCat.{w} R), Module.FinitePresentation R P →
    ∀ (f : (P : Type w) →ₗ[R] (M : Type w)),
      ∃ Q : ModuleCat.{w} R, Module.FinitePresentation R Q ∧
        ∃ g : (P : Type w) →ₗ[R] (Q : Type w), mutuallyDominates g f

/-- The five conditions in the source are equivalent for any filtered
colimit presentation by finitely presented modules. -/
theorem mittagLeffler_characterization
    {R : Type u} [CommRing R] {I : Type v} [Preorder I]
    [Nonempty I] [IsDirectedOrder I] {M : ModuleCat.{w} R}
    (P : ColimitPresentation I M)
    (hP : ∀ i, Module.FinitePresentation R (P.diag.obj i)) :
    List.TFAE [
      MLModuleCondition M,
      ∀ i : I, ∃ (j : I) (hij : i ≤ j),
        dominates (directedMap P.diag hij) (colimitComponentMap P i),
      ∀ i : I, ∃ (j : I) (hij : i ≤ j),
        ∀ (k : I) (hik : i ≤ k),
          ∃ h : (P.diag.obj k : Type w) →ₗ[R] (P.diag.obj j : Type w),
            directedMap P.diag hij = h.comp (directedMap P.diag hik),
      ∀ N : ModuleCat.{z} R, (homInverseSystem P.diag N).IsMittagLeffler,
      (homInverseSystem P.diag
        (ModuleCat.of R (∀ s : I, (P.diag.obj s : Type w)))).IsMittagLeffler
    ] := by
  sorry

/-- A module is Mittag-Leffler when it satisfies the equivalent conditions of
the preceding characterization. -/
def IsMittagLefflerModule
    {R : Type u} [CommRing R] (M : ModuleCat.{w} R) : Prop :=
  MLModuleCondition M

/-- Every finitely presented module is Mittag-Leffler. -/
theorem isMittagLefflerModule_of_finitePresentation
    {R : Type u} [CommRing R] (M : ModuleCat.{w} R)
    (hM : Module.FinitePresentation R M) :
    IsMittagLefflerModule M := by
  sorry

/-! ## Flat modules, tensor products, and finite-free tests -/

/-- For a flat module presented as a directed colimit of finite free modules,
Mittag-Lefflerness is enough to check on the duals with target `R`. -/
theorem isMittagLefflerModule_of_flat_of_dualSystem
    {R : Type u} [CommRing R] {I : Type v} [Preorder I]
    [Nonempty I] [IsDirectedOrder I] {M : ModuleCat.{w} R}
    (P : ColimitPresentation I M) (hflat : Module.Flat R M)
    (hfree : ∀ i, Module.Free R (P.diag.obj i))
    (hfinite : ∀ i, Module.Finite R (P.diag.obj i))
    (hdual : (homInverseSystem P.diag (ModuleCat.of R R)).IsMittagLeffler) :
    IsMittagLefflerModule M := by
  sorry

/-- Tensor products of Mittag-Leffler modules are Mittag-Leffler. -/
theorem tensorProduct_isMittagLefflerModule
    {R : Type u} [CommRing R] (M N : ModuleCat.{w} R)
    (hM : IsMittagLefflerModule M) (hN : IsMittagLefflerModule N) :
    IsMittagLefflerModule
      (ModuleCat.of R ((M : Type w) ⊗[R] (N : Type w))) := by
  sorry

/-- The finite-free test for the Mittag-Leffler condition. -/
theorem isMittagLefflerModule_iff_finiteFreeTest
    {R : Type u} [CommRing R] (M : ModuleCat.{w} R) :
    IsMittagLefflerModule M ↔
      ∀ (F : ModuleCat.{w} R), Module.Free R F → Module.Finite R F →
        ∀ f : (F : Type w) →ₗ[R] (M : Type w),
          ∃ Q : ModuleCat.{w} R, Module.FinitePresentation R Q ∧
            ∃ g : (F : Type w) →ₗ[R] (Q : Type w), mutuallyDominates g f := by
  sorry

/-! ## Restriction of scalars and quotients -/

/-- Mittag-Lefflerness descends from a finite, finitely presented ring
extension to the base ring. -/
theorem isMittagLefflerModule_of_restrictScalars
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (f : R →+* S) (hfinite : RingHom.Finite f)
    (hfinitelyPresented : RingHom.FinitePresentation f)
    (M : ModuleCat.{w} S)
    (hM : IsMittagLefflerModule (R := S) M) :
    letI : Module R (M : Type w) := Module.compHom (M : Type w) f
    IsMittagLefflerModule (R := R) (ModuleCat.of R (M : Type w)) := by
  sorry

/-- For a finitely generated ideal, the Mittag-Leffler condition is unchanged
when passing between a ring and its quotient. -/
theorem isMittagLefflerModule_iff_quotient
    {R : Type u} [CommRing R] (I : Ideal R) (hI : I.FG)
    (M : ModuleCat.{w} (R ⧸ I)) :
    (letI : Module R (M : Type w) :=
      Module.compHom (M : Type w) (Ideal.Quotient.mk I);
      IsMittagLefflerModule (R := R) (ModuleCat.of R (M : Type w))) ↔
      IsMittagLefflerModule (R := R ⧸ I) M := by
  sorry

/-! ## The dual-number warning -/

/-- Restriction of scalars along the canonical inclusion into the dual
numbers. -/
def dualNumberRestriction
    {R : Type u} [CommRing R] :
    ModuleCat.{w} (DualNumber R) ⥤ ModuleCat.{w} R :=
  ModuleCat.restrictScalars (algebraMap R (DualNumber R))

/-- The dual-number construction witnesses that restriction of scalars does
not reflect the Mittag-Leffler condition in general. -/
theorem exists_dualNumber_restriction_counterexample
    {R : Type u} [CommRing R]
    (h : ∃ M₀ : ModuleCat.{w} R, ¬ IsMittagLefflerModule M₀) :
    RingHom.Finite (algebraMap R (DualNumber R)) ∧
      RingHom.FinitePresentation (algebraMap R (DualNumber R)) ∧
      ∃ M : ModuleCat.{w} (DualNumber R),
        IsMittagLefflerModule (dualNumberRestriction.obj M) ∧
          ¬ IsMittagLefflerModule M := by
  sorry

end

end Formalization.Books.Algebra.Unit88
