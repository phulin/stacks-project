import Formalization.Books.Algebra.Unit03.BasicNotions
import Formalization.Books.Algebra.Unit10.InternalHom
import Formalization.Books.Algebra.Unit71.ExtGroups
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.Algebra.Module.Projective
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.RingTheory.FiniteLength
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Noetherian.Basic

/-!
# Commutative Algebra, Chapter 77: Projective modules

The source's projective-module predicate is Mathlib's canonical
`Module.Projective`.  The source's `Ext^1` groups are represented by the
canonical `ExtGroup` interface from Chapter 71, and quotients by `IM` use the
canonical submodule quotient `M ⧸ I • ⊤`.
-/

namespace Formalization.Books.Algebra.Unit77

open Formalization.Books.Algebra.Unit10
open Formalization.Books.Algebra.Unit71
open scoped Pointwise

universe u

/-! ## The definition and the three characterizations -/

/- The source defines projectivity by exactness of `Hom_R(P, -)`.  We use
Mathlib's equivalent canonical predicate `Module.Projective`; the lifting
statement below records the source's immediate surjectivity consequence. -/

/-- The `Hom_R(P, -)` map induced by a surjection is surjective for a
projective module. -/
theorem projective_hom_map_surjective
    {R P M N : Type u} [CommRing R]
    [AddCommGroup P] [Module R P]
    [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N]
    [Module.Projective R P]
    (f : M →ₗ[R] N) (hf : Function.Surjective f) :
    Function.Surjective (internalHomPostcomp (M := P) f) := by
  intro g
  obtain ⟨h, hh⟩ := Module.projective_lifting_property f g hf
  exact ⟨h, hh⟩

/- `Module.Projective.iff_split` is Mathlib's source-faithful direct-summand
characterization.  The following TFAE records all three conditions in the
source, including its Ext formulation. -/

/- The predicate is stated on the bundled module category because Chapter 71's
canonical `ExtGroup` is indexed by `ModuleCat` objects. -/
def ExtOneVanishes {R : Type u} [Ring R] (P : ModuleCat.{u} R) : Prop :=
  ∀ M : ModuleCat.{u} R, ∀ e : ExtGroup P M 1, e = 0

/-- The three equivalent characterizations of a projective module. -/
theorem projective_characterization
    {R P : Type u} [CommRing R]
    [AddCommGroup P] [Module R P] :
    List.TFAE [
      Module.Projective R P,
      ∃ (F : Type u) (_ : AddCommGroup F) (_ : Module R F) (_ : Module.Free R F)
        (i : P →ₗ[R] F) (s : F →ₗ[R] P), s.comp i = LinearMap.id,
      ExtOneVanishes (ModuleCat.of R P)] := by
  sorry

/-! ## Ext-vanishing criteria for finite modules -/

/-- Vanishing of `Ext^1_R(P, -)` on finite modules. -/
def ExtOneVanishesOnFiniteModules {R : Type u} [Ring R]
    (P : ModuleCat.{u} R) : Prop :=
  ∀ M : ModuleCat.{u} R, Module.Finite R M →
    ∀ e : ExtGroup P M 1, e = 0

/-- Over a Noetherian ring, Ext-vanishing on finite modules detects
projectivity of a finite module. -/
theorem projective_of_ext_one_vanishes_on_finite_modules
    {R P : Type u} [CommRing R] [IsNoetherianRing R]
    [AddCommGroup P] [Module R P] [Module.Finite R P]
    (hP : ExtOneVanishesOnFiniteModules (ModuleCat.of R P)) :
    Module.Projective R P := by
  sorry

/- The source also records the two standard strengthenings of this criterion:
finite presentation removes Noetherianity, and finite-length test modules
suffice in the Noetherian case. -/

/-- The finite-presentation strengthening of the finite-module criterion. -/
theorem projective_of_ext_one_vanishes_of_finite_presentation
    {R P : Type u} [CommRing R]
    [AddCommGroup P] [Module R P] [Module.FinitePresentation R P]
    (hP : ExtOneVanishesOnFiniteModules (ModuleCat.of R P)) :
    Module.Projective R P := by
  sorry

/-- Over a Noetherian ring, finite-length test modules suffice for the
Ext-vanishing criterion. -/
theorem projective_of_ext_one_vanishes_on_finite_length_modules
    {R P : Type u} [CommRing R] [IsNoetherianRing R]
    [AddCommGroup P] [Module R P] [Module.Finite R P]
    (hP : ∀ M : ModuleCat.{u} R, IsFiniteLength R M →
      ∀ e : ExtGroup (ModuleCat.of R P) M 1, e = 0) :
    Module.Projective R P := by
  sorry

/-! ## Direct sums and lifting across nilpotent ideals -/

/- The direct-sum assertion is exactly Mathlib's existing instance and theorem
`Module.Projective.directSum`, so no parallel wrapper is introduced. -/

/-- A projective module over `R ⧸ I` lifts to a projective `R`-module when
`I` is nilpotent. -/
theorem exists_projective_lift_of_isNilpotent
    {R : Type u} [CommRing R] (I : Ideal R)
    (Pbar : ModuleCat.{u} (R ⧸ I))
    (hPbar : Module.Projective (R ⧸ I) Pbar)
    : ∃ P : ModuleCat.{u} R,
        Module.Projective R P ∧
          Nonempty ((P ⧸ (I • (⊤ : Submodule R P))) ≃ₗ[R ⧸ I] Pbar) := by
  sorry

/- The source calls an ideal locally nilpotent when each of its elements is
nilpotent; this is the earlier chapter's canonical `locallyNilpotentIdeal`. -/

/-- A finite projective module over `R ⧸ I` lifts to a finite projective
`R`-module when `I` is locally nilpotent. -/
theorem exists_finite_projective_lift_of_locallyNilpotent
    {R : Type u} [CommRing R] (I : Ideal R)
    (hI : Formalization.Books.Algebra.Unit03.locallyNilpotentIdeal I)
    (Pbar : ModuleCat.{u} (R ⧸ I))
    [Module.Finite (R ⧸ I) Pbar]
    (hPbar : Module.Projective (R ⧸ I) Pbar) :
    ∃ P : ModuleCat.{u} R,
      Module.Finite R P ∧ Module.Projective R P ∧
        Nonempty ((P ⧸ (I • (⊤ : Submodule R P))) ≃ₗ[R ⧸ I] Pbar) := by
  sorry

/-- A flat module whose reduction modulo a nilpotent ideal is projective is
projective. -/
theorem projective_of_flat_of_isNilpotent_of_quotient_projective
    {R : Type u} [CommRing R] (I : Ideal R) (M : ModuleCat.{u} R)
    (hI : IsNilpotent I)
    [Module.Flat R M]
    (hMbar : Module.Projective (R ⧸ I)
      (M ⧸ (I • (⊤ : Submodule R M)))) :
    Module.Projective R M := by
  sorry

/-- Projectivity modulo two ideals with zero intersection implies
projectivity over the original ring. -/
theorem projective_of_projective_quotients_of_inf_eq_bot
    {R : Type u} [CommRing R] (I J : Ideal R) (M : ModuleCat.{u} R)
    (hIJ : I ⊓ J = ⊥)
    (hI : Module.Projective (R ⧸ I)
      (M ⧸ (I • (⊤ : Submodule R M))))
    (hJ : Module.Projective (R ⧸ J)
      (M ⧸ (J • (⊤ : Submodule R M)))) :
    Module.Projective R M := by
  sorry

end Formalization.Books.Algebra.Unit77
