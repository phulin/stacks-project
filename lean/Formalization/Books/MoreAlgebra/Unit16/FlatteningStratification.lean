import Formalization.Books.Algebra.Unit14.BaseChange
import Formalization.Books.Algebra.Unit39.FlatModules
import Mathlib.Algebra.Module.Torsion.Basic

/-!
# More on Algebra, Chapter 16: Flattening stratification

The source's base changes are represented by the canonical extension-of-scalars
model `Formalization.Books.Algebra.Unit14.baseChangeModule`.  This retains the
`S ⊗[R] R'`-module structure while giving the module its induced `R'`-action.
-/

namespace Formalization.Books.MoreAlgebra.Unit16

open scoped TensorProduct

universe u v

noncomputable section

/-! ## Flattening stratification -/

/- The source's notation `S' = S ⊗[R] R'` and `M' = M ⊗[R] R'` is already
   implemented by the earlier chapter's `baseChangeRingMap` and
   `baseChangeModule`; no parallel base-change construction is introduced. -/

/-- A ring map `R → R'` flattens an `S`-module `M` when its base change is flat
over the base-changed ring `R'`.  The base-changed module uses the canonical
extension-of-scalars model from the earlier base-change chapter. -/
def Flattens
    {R S R' M : Type*} [CommRing R] [CommRing S] [CommRing R']
    [AddCommGroup M] [Module S M]
    (f : R →+* S) (g : R →+* R') : Prop :=
  letI : Algebra R S := f.toAlgebra
  letI : Algebra R R' := g.toAlgebra
  letI : Algebra R' (S ⊗[R] R') :=
    (Formalization.Books.Algebra.Unit14.baseChangeRingMap f g).toAlgebra
  letI : Module R' (Formalization.Books.Algebra.Unit14.baseChangeModule
      (M := M) f g) :=
    Module.compHom
      (Formalization.Books.Algebra.Unit14.baseChangeModule (M := M) f g)
      (Formalization.Books.Algebra.Unit14.baseChangeRingMap f g)
  Module.Flat R'
    (Formalization.Books.Algebra.Unit14.baseChangeModule (M := M) f g)

/-- The universal property of a flattening: it is a flattening, and every
other flattening `R → R''` factors through it by a ring map over `R`. -/
def IsUniversalFlattening
    {R S R' M : Type*} [CommRing R] [CommRing S] [CommRing R']
    [AddCommGroup M] [Module S M]
    (f : R →+* S) (g : R →+* R') : Prop :=
  Flattens (M := M) f g ∧
    ∀ (R'' : Type*) [CommRing R''] (g' : R →+* R''),
      Flattens (M := M) f g' → ∃ h : R' →+* R'', h.comp g = g'

/- The opening discussion of the collection of flattening maps is represented
   by `Flattens` and `IsUniversalFlattening`.  The statement that a universal
   solution “usually does not exist” is intentionally left as prose:
   “usually” is not a precise proposition.  The scheme-theoretic setting
   `𝓕 / X / S`, and the conditional identification of the corresponding
   morphism `Spec(R_univ) ⟶ Spec(R)` as a universal flattening of `M tilde`,
   are roadmap assertions for the later scheme-theoretic source section and
   have no separate algebraic declaration at this source boundary. -/

/-! ## The intersection lemma -/

/-- If the reductions of an `R`-module modulo two ideals are flat over the
corresponding quotient rings, then the reduction modulo their intersection is
flat over the quotient by that intersection.  Ideal intersection is written
using the canonical lattice infimum `I₁ ⊓ I₂`. -/
theorem flat_quotient_inf_of_flat_quotients
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (I₁ I₂ : Ideal R)
    (h₁ : Module.Flat (R ⧸ I₁)
      (M ⧸ (I₁ • (⊤ : Submodule R M))))
    (h₂ : Module.Flat (R ⧸ I₂)
      (M ⧸ (I₂ • (⊤ : Submodule R M)))) :
    Module.Flat (R ⧸ (I₁ ⊓ I₂))
      (M ⧸ ((I₁ ⊓ I₂) • (⊤ : Submodule R M))) := by
  sorry

/- The proof's displayed tensor identity identifies the quotient of `J` by
`J ∩ I₁` with `(J + I₁) / I₁`, after tensoring with the corresponding module
quotient.  Its exact-sequence diagram is the standard right-exact tensor
sequence used by the flatness criterion; these proof details are subsumed by
the source-faithful theorem above and the canonical tensor/flatness APIs. -/

end

end Formalization.Books.MoreAlgebra.Unit16
