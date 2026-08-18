import Formalization.Books.Algebra.Unit71.ExtGroups
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.Algebra.Module.Projective
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.RingTheory.Ideal.Maps

/-!
# More on Algebra, Chapter 71: Modules which are close to being projective

The source's factorization conditions are expressed using the canonical
`Module.Projective`, `Module.Free`, and `Module.Finite` predicates.  Modules
are represented by `ModuleCat`, so exact sequences and the canonical `ExtGroup`
API can be used directly.
-/

namespace Formalization.Books.MoreAlgebra.Unit71

open CategoryTheory
open Formalization.Books.Algebra.Unit71

universe u

section FactorThrough

variable {R : Type u} [CommRing R]

/-- A module map factors through a projective module. -/
def FactorsThroughProjective {M N : ModuleCat.{u} R} (φ : M ⟶ N) : Prop :=
  ∃ (P : ModuleCat.{u} R) (_ : Module.Projective R P),
    ∃ (f : M ⟶ P) (g : P ⟶ N), f ≫ g = φ

/-- A module map factors through a free module. -/
def FactorsThroughFree {M N : ModuleCat.{u} R} (φ : M ⟶ N) : Prop :=
  ∃ (P : ModuleCat.{u} R) (_ : Module.Free R P),
    ∃ (f : M ⟶ P) (g : P ⟶ N), f ≫ g = φ

/-- A module map factors through a finite projective module. -/
def FactorsThroughFiniteProjective {M N : ModuleCat.{u} R} (φ : M ⟶ N) : Prop :=
  ∃ (P : ModuleCat.{u} R) (_ : Module.Finite R P) (_ : Module.Projective R P),
    ∃ (f : M ⟶ P) (g : P ⟶ N), f ≫ g = φ

/-- The maps factoring through projectives form the span of those maps. -/
def factorsThroughProjectiveSubmodule (M N : ModuleCat.{u} R) :
    Submodule R (M ⟶ N) :=
  Submodule.span R {φ : M ⟶ N | FactorsThroughProjective φ}

/-- Every map factoring through a projective module factors through a free module. -/
theorem factorsThroughProjective_iff_factorsThroughFree
    {M N : ModuleCat.{u} R} (φ : M ⟶ N) :
    FactorsThroughProjective φ ↔ FactorsThroughFree φ := by
  sorry

/-- The maps factoring through projectives are exactly the carrier of the
submodule introduced above. -/
theorem mem_factorsThroughProjectiveSubmodule_iff
    {M N : ModuleCat.{u} R} (φ : M ⟶ N) :
    φ ∈ factorsThroughProjectiveSubmodule M N ↔ FactorsThroughProjective φ := by
  sorry

/-- Factoring through a projective module is stable under pre- and
postcomposition. -/
theorem factorsThroughProjective_comp
    {M M' N N' : ModuleCat.{u} R} {φ : M ⟶ N}
    (hφ : FactorsThroughProjective φ) (ψ : M' ⟶ M) (ξ : N ⟶ N') :
    FactorsThroughProjective (ψ ≫ φ ≫ ξ) := by
  sorry

/-- Factoring through a free module is stable under pre- and postcomposition. -/
theorem factorsThroughFree_comp
    {M M' N N' : ModuleCat.{u} R} {φ : M ⟶ N}
    (hφ : FactorsThroughFree φ) (ψ : M' ⟶ M) (ξ : N ⟶ N') :
    FactorsThroughFree (ψ ≫ φ ≫ ξ) := by
  sorry

/-- A module is projective exactly when its identity map factors through a
projective module. -/
theorem moduleProjective_iff_id_factorsThroughProjective
    (M : ModuleCat.{u} R) :
    Module.Projective R M ↔ FactorsThroughProjective (𝟙 M) := by
  sorry

/-- If the source module is finite, a factorization through a projective module
can be chosen through a finite projective module. -/
theorem factorsThroughFiniteProjective_of_factorsThroughProjective
    {M N : ModuleCat.{u} R} [Module.Finite R M] {φ : M ⟶ N}
    (hφ : FactorsThroughProjective φ) :
    FactorsThroughFiniteProjective φ := by
  sorry

end FactorThrough

section NearProjective

variable {R : Type u} [CommRing R]

/-- Every degree-one `Ext` group with first argument `M` is annihilated by `I`.
This is the Ext formulation of being close to projective. -/
def ExtOneAnnihilatedByIdeal (I : Ideal R) (M : ModuleCat.{u} R) : Prop :=
  ∀ (N : ModuleCat.{u} R) (a : R), a ∈ I →
    ∀ e : ExtGroup M N 1, a • e = 0

/-- The three source characterizations of an `I`-projective module. -/
theorem nearProjective_characterization (I : Ideal R) (M : ModuleCat.{u} R) :
    List.TFAE [
      (∀ a : R, a ∈ I → FactorsThroughProjective (a • 𝟙 M)),
      (∀ a : R, a ∈ I → FactorsThroughFree (a • 𝟙 M)),
      ExtOneAnnihilatedByIdeal I M] := by
  sorry

/-- A module is `I`-projective when multiplication by every element of `I`
factors through a projective module.  This notation is nonstandard. -/
def IsIdealProjective (I : Ideal R) (M : ModuleCat.{u} R) : Prop :=
  ∀ a : R, a ∈ I → FactorsThroughProjective (a • 𝟙 M)

/-- A module annihilated by `I` is `I`-projective. -/
theorem isIdealProjective_of_annihilated
    (I : Ideal R) (M : ModuleCat.{u} R)
    (hM : I ≤ Module.annihilator R M) :
    IsIdealProjective I M := by
  sorry

/-- In a short exact sequence, an `I`-projective quotient and a projective
middle module imply that the left module is `I`-projective. -/
theorem isIdealProjective_of_shortExact
    (I : Ideal R) (S : ShortComplex (ModuleCat.{u} R))
    (hS : S.ShortExact) (hP : Module.Projective R S.X₂)
    (hM : IsIdealProjective I S.X₃) :
    IsIdealProjective I S.X₁ := by
  sorry

/-- The dual of a finite `I`-projective module is `I`-projective. -/
theorem isIdealProjective_dual
    (I : Ideal R) (M : ModuleCat.{u} R) [Module.Finite R M]
    (hM : IsIdealProjective I M) :
    IsIdealProjective I (ModuleCat.of R (Module.Dual R M)) := by
  sorry

end NearProjective

end Formalization.Books.MoreAlgebra.Unit71
