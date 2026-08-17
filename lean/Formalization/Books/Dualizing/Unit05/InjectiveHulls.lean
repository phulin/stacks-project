import Formalization.Books.Dualizing.Unit02.Essential
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.DirectSum.Module
import Mathlib.Algebra.Module.Injective
import Mathlib.RingTheory.Ideal.Maximal
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.LocalRing.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Mathlib.RingTheory.Noetherian.Defs

/-!
# Dualizing Complexes, Chapter 5: Injective hulls

This file records the definitions, examples, and theorem interfaces in the
chapter.  Proofs are intentionally deferred to the proving stage.
-/

namespace Formalization.Books.Dualizing.Unit05

open CategoryTheory
open CategoryTheory.Limits
open DirectSum
open Formalization.Books.Dualizing.Unit02
open Set

universe u v w

noncomputable section

/-! ## Injective hulls -/

/- The canonical `CategoryTheory.Injective` predicate is used for injective
objects, and `EssentialExtension` is the essential-monomorphism predicate
introduced in Chapter 2. -/

/-- An essential extension whose target is an injective module. -/
def InjectiveHull {R : Type u} [Ring R] {M E : ModuleCat.{v} R}
    (f : M ⟶ E) : Prop :=
  EssentialExtension f ∧ CategoryTheory.Injective E

/-- Every module has an injective hull. -/
theorem exists_injective_hull {R : Type u} [Ring R] (M : ModuleCat.{v} R) :
    ∃ (E : ModuleCat.{v} R) (f : M ⟶ E), InjectiveHull f := by
  sorry

/-! The extension and uniqueness assertions are separated so that the map
chosen by extension remains available to the subsequent assertions. -/

/-- A map between the modules extends across their injective hulls. -/
theorem injective_hull_extend
    {R : Type u} [Ring R] {M N E E' : ModuleCat.{v} R}
    {f : M ⟶ E} {g : N ⟶ E'}
    (hf : InjectiveHull f) (hg : InjectiveHull g) (φ : M ⟶ N) :
    ∃ ψ : E ⟶ E', f ≫ ψ = φ ≫ g := by
  sorry

/-- The extension of a monomorphism is a monomorphism. -/
theorem injective_hull_extend_mono
    {R : Type u} [Ring R] {M N E E' : ModuleCat.{v} R}
    {f : M ⟶ E} {g : N ⟶ E'}
    (hf : InjectiveHull f) (hg : InjectiveHull g)
    (φ : M ⟶ N) (hφ : Mono φ) (ψ : E ⟶ E')
    (hψ : f ≫ ψ = φ ≫ g) : Mono ψ := by
  sorry

/-- An extension of an essential monomorphism is an isomorphism. -/
theorem injective_hull_extend_isIso_of_essential
    {R : Type u} [Ring R] {M N E E' : ModuleCat.{v} R}
    {f : M ⟶ E} {g : N ⟶ E'}
    (hf : InjectiveHull f) (hg : InjectiveHull g)
    (φ : M ⟶ N) (hφ : EssentialExtension φ) (ψ : E ⟶ E')
    (hψ : f ≫ ψ = φ ≫ g) : IsIso ψ := by
  sorry

/-- If the map on modules is an isomorphism, so is its extension. -/
theorem injective_hull_extend_isIso_of_isIso
    {R : Type u} [Ring R] {M N E E' : ModuleCat.{v} R}
    {f : M ⟶ E} {g : N ⟶ E'}
    (hf : InjectiveHull f) (hg : InjectiveHull g)
    (φ : M ⟶ N) [IsIso φ] (ψ : E ⟶ E')
    (hψ : f ≫ ψ = φ ≫ g) : IsIso ψ := by
  sorry

/-- An injective module containing the source splits off the hull. -/
theorem injective_hull_split
    {R : Type u} [Ring R] {M E I : ModuleCat.{v} R}
    {f : M ⟶ E} {h : M ⟶ I}
    (hf : InjectiveHull f) (hh : Mono h)
    (hI : CategoryTheory.Injective I) :
    ∃ (I' : ModuleCat.{v} R) (e : I ≅ E ⊞ I'),
      h ≫ e.hom ≫ biprod.fst = f := by
  sorry

/-- Injective hulls of a fixed module are isomorphic. -/
theorem injective_hull_unique_up_to_iso
    {R : Type u} [Ring R] {M E E' : ModuleCat.{v} R}
    {f : M ⟶ E} {g : M ⟶ E'}
    (hf : InjectiveHull f) (hg : InjectiveHull g) :
    Nonempty (E ≅ E') := by
  sorry

/-! The domain example uses the standard fraction-field embedding. -/

/-- The canonical module map from a domain to its fraction field. -/
def fractionFieldModuleMap
    {R K : Type u} [CommRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] :
    ModuleCat.of R R ⟶ ModuleCat.of R K :=
  ModuleCat.ofHom (Algebra.linearMap R K)

/-- For a domain, its inclusion in the fraction field is an injective hull. -/
theorem fractionField_is_injective_hull
    {R K : Type u} [CommRing R] [IsDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] :
    InjectiveHull (fractionFieldModuleMap (R := R) (K := K)) := by
  sorry

/-! ## Indecomposable injectives -/

/- `CategoryTheory.Indecomposable` is Mathlib's canonical additive-category
form of the source's indecomposable-object definition. -/

/-- Every nonzero submodule of an indecomposable injective is essential. -/
theorem indecomposable_injective_submodule_hull
    {R : Type u} [Ring R] (E : ModuleCat.{v} R)
    (hE : CategoryTheory.Injective E)
    (hInd : CategoryTheory.Indecomposable E) :
    ∀ S : Submodule R (E : Type v), S ≠ ⊥ →
      InjectiveHull (ModuleCat.ofHom S.subtype) := by
  sorry

/-- Any two nonzero submodules of an indecomposable injective meet nontrivially. -/
theorem indecomposable_injective_submodule_intersection
    {R : Type u} [Ring R] (E : ModuleCat.{v} R)
    (hE : CategoryTheory.Injective E)
    (hInd : CategoryTheory.Indecomposable E) :
    ∀ S T : Submodule R (E : Type v), S ≠ ⊥ → T ≠ ⊥ → S ⊓ T ≠ ⊥ := by
  sorry

/-- The endomorphism ring of an indecomposable injective is local, with its
maximal ideal detected by nonzero kernels. -/
theorem indecomposable_injective_end_is_local
    {R : Type u} [Ring R] (E : ModuleCat.{v} R)
    (hE : CategoryTheory.Injective E)
    (hInd : CategoryTheory.Indecomposable E) :
    IsLocalRing (Module.End R (E : Type v)) ∧
      ∃ I : Ideal (Module.End R (E : Type v)),
        I.IsTwoSided ∧ I.IsMaximal ∧
          ∀ φ : Module.End R (E : Type v),
            φ ∈ I ↔ LinearMap.ker φ ≠ ⊥ := by
  sorry

/- The zero divisors acting on an indecomposable injective form a prime ideal,
and the module is injective after localizing at that ideal. -/
def ModuleZeroDivisors (R M : Type*) [CommRing R] [AddCommGroup M]
    [Module R M] : Set R :=
  {r | ∃ x : M, x ≠ 0 ∧ r • x = 0}

theorem indecomposable_injective_zero_divisors
    {R : Type u} [CommRing R] (E : ModuleCat.{v} R)
    (hE : CategoryTheory.Injective E)
    (hInd : CategoryTheory.Indecomposable E) :
    ∃ (p : Ideal R) (hp : p.IsPrime),
      (p : Set R) = ModuleZeroDivisors R (E : Type v) ∧
        letI := hp
        ∃ Eₚ : ModuleCat.{v} (Localization.AtPrime p),
          Nonempty
              (ModuleCat.of R (E : Type v) ≅
                (ModuleCat.restrictScalars (algebraMap R (Localization.AtPrime p))).obj Eₚ) ∧
            CategoryTheory.Injective Eₚ := by
  sorry

/-! ## Prime residue fields and the Noetherian classification -/

/-- The quotient-to-residue-field map, viewed as an R-linear module map. -/
def residueFieldQuotientMap
    {R : Type u} [CommRing R] (p : Ideal R) [p.IsPrime] :
    ModuleCat.of R (R ⧸ p) ⟶ ModuleCat.of R p.ResidueField :=
  ModuleCat.ofHom
    ((Algebra.linearMap (R ⧸ p) p.ResidueField).restrictScalars R)

/-- The injective hull of R/p is indecomposable and is also the hull of the
residue field, over both R and the localization at p. -/
theorem prime_injective_hull_residue_field
    {R : Type u} [CommRing R] (p : Ideal R) [p.IsPrime]
    (E : ModuleCat.{u} R)
    (f : ModuleCat.of R (R ⧸ p) ⟶ E) (hf : InjectiveHull f) :
    CategoryTheory.Indecomposable E ∧
      (∃ g : ModuleCat.of R p.ResidueField ⟶ E,
        InjectiveHull g ∧ residueFieldQuotientMap p ≫ g = f) ∧
        ∃ Eₚ : ModuleCat.{u} (Localization.AtPrime p),
          Nonempty
              (E ≅
                (ModuleCat.restrictScalars (algebraMap R (Localization.AtPrime p))).obj Eₚ) ∧
            ∃ g : ModuleCat.of (Localization.AtPrime p) p.ResidueField ⟶ Eₚ,
              InjectiveHull g := by
  sorry

/-- Over a Noetherian ring, every indecomposable injective is a residue-field
injective hull. -/
theorem noetherian_indecomposable_injective_residue_field_hull
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    (E : ModuleCat.{u} R) (hE : CategoryTheory.Injective E)
    (hInd : CategoryTheory.Indecomposable E) :
    ∃ (p : Ideal R) (hp : p.IsPrime),
      letI := hp
      ∃ g : ModuleCat.of R p.ResidueField ⟶ E, InjectiveHull g := by
  sorry

/-- A Noetherian injective module is a direct sum of indecomposable injectives. -/
def IsDirectSumOfIndecomposableInjectives
    {R : Type u} [CommRing R] (I : ModuleCat.{v} R) : Prop :=
  ∃ (ι : Type w) (E : ι → ModuleCat.{v} R),
    (∀ i, CategoryTheory.Indecomposable (E i) ∧
      CategoryTheory.Injective (E i)) ∧
      Nonempty ((I : Type v) ≃ₗ[R] (⨁ i, (E i : Type v)))

/-- Structure theorem for injectives over a Noetherian ring. -/
theorem structure_of_injectives_noetherian
    {R : Type u} [CommRing R] [IsNoetherianRing R] :
    (∀ I : ModuleCat.{v} R, CategoryTheory.Injective I →
      IsDirectSumOfIndecomposableInjectives I) ∧
      (∀ E : ModuleCat.{u} R, CategoryTheory.Injective E →
        CategoryTheory.Indecomposable E →
          ∃ (p : Ideal R) (hp : p.IsPrime),
            letI := hp
            ∃ g : ModuleCat.of R p.ResidueField ⟶ E, InjectiveHull g) := by
  sorry

end

end Formalization.Books.Dualizing.Unit05
