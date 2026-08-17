import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Jacobson.Radical

/-!
# More on Algebra, Chapter 3: Stably free modules

The source's stable-freeness predicate is Mathlib's canonical
`Module.IsStablyFree`.  The source-facing stable-isomorphism relation is
recorded separately using finite free modules `Fin n → R`; quotient modules
`M / IM` use Mathlib's canonical `M ⧸ (I • ⊤)` construction.
-/

namespace Formalization.Books.MoreAlgebra.Unit03

open CategoryTheory
open scoped Pointwise

universe u

/-! ## The definition of stable freeness -/

/-- Two modules are stably isomorphic when they become linearly equivalent
after adjoining finite free summands.  The type `Fin n → R` represents the
finite direct sum `R^{⊕ n}`. -/
def StablyIsomorphic (R M N : Type u) [Ring R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] : Prop :=
  ∃ m n : ℕ,
    Nonempty ((M × (Fin m → R)) ≃ₗ[R] (N × (Fin n → R)))

/-- The source's notion of a stably free module, delegated to Mathlib's
canonical predicate. -/
abbrev StablyFree (R M : Type u) [Ring R]
    [AddCommGroup M] [Module R M] : Prop :=
  Module.IsStablyFree R M

/-- Mathlib's canonical stably-free predicate expresses the source's second
definition: being stably isomorphic to a free module. -/
theorem stablyFree_iff_stablyIsomorphic_free
    {R M : Type u} [Ring R] [AddCommGroup M] [Module R M] :
    StablyFree R M ↔
      ∃ (F : Type u) (_ : AddCommGroup F) (_ : Module R F)
        (_ : Module.Free R F), StablyIsomorphic R M F := by
  sorry

/-- A stably free module is projective.  This is Mathlib's existing
`Module.IsStablyFree` instance, exposed under the source-facing name. -/
theorem stablyFree_projective
    {R M : Type u} [Ring R] [AddCommGroup M] [Module R M]
    [StablyFree R M] : Module.Projective R M :=
  inferInstance

/-! ## The split exact sequence lemma -/

/-- The split direct-sum decomposition used in the proof of the source
two-out-of-three lemma.  It combines Mathlib's canonical splitting of a
short exact sequence with its module biproduct/product equivalence. -/
noncomputable def shortExact_middle_linearEquiv_prod
    {R : Type u} [CommRing R]
    (S : ShortComplex (ModuleCat.{u} R)) (hS : S.ShortExact)
    [Module.Projective R S.X₃] :
    S.X₂ ≃ₗ[R] (S.X₁ × S.X₃) :=
  ((ShortComplex.ShortExact.splittingOfProjective hS).isoBinaryBiproduct ≪≫
    ModuleCat.biprodIsoProd S.X₁ S.X₃).toLinearEquiv

/-- In a short exact sequence of finite projective modules, stable freeness
has the two-out-of-three property. -/
theorem shortExact_isStablyFree_two_of_three
    {R : Type u} [CommRing R]
    (S : ShortComplex (ModuleCat.{u} R)) (hS : S.ShortExact)
    [Module.Finite R S.X₁] [Module.Projective R S.X₁]
    [Module.Finite R S.X₂] [Module.Projective R S.X₂]
    [Module.Finite R S.X₃] [Module.Projective R S.X₃] :
    (StablyFree R S.X₁ ∧ StablyFree R S.X₂ → StablyFree R S.X₃) ∧
      (StablyFree R S.X₁ ∧ StablyFree R S.X₃ → StablyFree R S.X₂) ∧
        (StablyFree R S.X₂ ∧ StablyFree R S.X₃ → StablyFree R S.X₁) := by
  have hsplit := shortExact_middle_linearEquiv_prod S hS
  sorry

/- The displayed chain of direct sums in the source proof is an informal use
of associativity and commutativity of finite products.  The preceding
decomposition together with Mathlib's `LinearEquiv.prodAssoc` and
`LinearEquiv.prodComm` is the source-faithful interface, so no artificial
equality between differently parenthesized products is introduced. -/

/-! ## Lifting across a Jacobson-radical ideal -/

/- The source phrases the hypothesis as "every element of `1 + I` is a unit".
We use the canonical equivalent condition `I ≤ Ring.jacobson R`; the earlier
Jacobson-radical API records the equivalence with the elementwise formulation.
-/

/-- Every finite stably free module over `R ⧸ I` lifts to a finite stably free
module over `R` when `I` is contained in the Jacobson radical. -/
theorem exists_finite_stablyFree_lift
    {R : Type u} [CommRing R] (I : Ideal R)
    (hI : I ≤ Ring.jacobson R)
    (E : ModuleCat.{u} (R ⧸ I))
    [Module.Finite (R ⧸ I) E] [StablyFree (R ⧸ I) E] :
    ∃ M : ModuleCat.{u} R,
      Module.Finite R M ∧ StablyFree R M ∧
        Nonempty ((M ⧸ (I • (⊤ : Submodule R M))) ≃ₗ[R ⧸ I] E) := by
  sorry

/-! ## Lifting finite projectivity -/

/-- A finite flat module whose reduction modulo a Jacobson-radical ideal is
projective is projective. -/
theorem finiteProjective_of_finiteFlat_of_projective_quotient
    {R : Type u} [CommRing R] (I : Ideal R)
    (hI : I ≤ Ring.jacobson R) (M : ModuleCat.{u} R)
    [Module.Finite R M] [Module.Flat R M]
    (hM : Module.Projective (R ⧸ I)
      (M ⧸ (I • (⊤ : Submodule R M)))) :
    Module.Projective R M := by
  sorry

/-! ## Uniqueness of finite-projective lifts -/

/-- A quotient linear equivalence is induced by an `R`-linear map when it
commutes with the canonical quotient maps. -/
def InducesQuotientEquiv
    {R M N : Type u} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (I : Ideal R) (φ : M →ₗ[R] N)
    (e : (M ⧸ (I • (⊤ : Submodule R M))) ≃ₗ[R ⧸ I]
      (N ⧸ (I • (⊤ : Submodule R N)))) : Prop :=
  ∀ x : M,
    e ((I • (⊤ : Submodule R M)).mkQ x) =
      (I • (⊤ : Submodule R N)).mkQ (φ x)

/-- A map between finite projective modules that induces an isomorphism after
reduction modulo a Jacobson-radical ideal is already an isomorphism. -/
theorem finiteProjective_map_isIso_of_inducesQuotientEquiv
    {R : Type u} [CommRing R] (I : Ideal R)
    (hI : I ≤ Ring.jacobson R)
    {P P' : Type u} [AddCommGroup P] [Module R P]
    [AddCommGroup P'] [Module R P']
    [Module.Finite R P] [Module.Projective R P]
    [Module.Finite R P'] [Module.Projective R P']
    (φ : P →ₗ[R] P')
    (hφ : ∃ e : (P ⧸ (I • (⊤ : Submodule R P))) ≃ₗ[R ⧸ I]
        (P' ⧸ (I • (⊤ : Submodule R P'))),
      InducesQuotientEquiv I φ e) :
    ∃ e : P ≃ₗ[R] P', e.toLinearMap = φ := by
  sorry

/-- Finite projective modules with isomorphic reductions modulo a
Jacobson-radical ideal are isomorphic. -/
theorem finiteProjective_quotientEquiv_imp_isomorphic
    {R : Type u} [CommRing R] (I : Ideal R)
    (hI : I ≤ Ring.jacobson R)
    {P P' : Type u} [AddCommGroup P] [Module R P]
    [AddCommGroup P'] [Module R P']
    [Module.Finite R P] [Module.Projective R P]
    [Module.Finite R P'] [Module.Projective R P']
    (h : Nonempty ((P ⧸ (I • (⊤ : Submodule R P))) ≃ₗ[R ⧸ I]
      (P' ⧸ (I • (⊤ : Submodule R P'))))) :
    Nonempty (P ≃ₗ[R] P') := by
  sorry

end Formalization.Books.MoreAlgebra.Unit03
