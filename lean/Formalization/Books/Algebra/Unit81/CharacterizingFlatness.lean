import Formalization.Books.Algebra.Unit10.InternalHom
import Formalization.Books.Algebra.Unit11.CharacterizingFinite
import Formalization.Books.Algebra.Unit39.FlatModules
import Mathlib.Algebra.Colimit.DirectLimit

/-!
# Commutative Algebra, Chapter 81: Characterizing flatness

The source's finite free modules are represented by `Fin n →₀ R`, Mathlib's
canonical finite-rank free modules.  Directed module systems are represented
by `DirectedSystem` data and the explicit directed colimit `DirectLimit`.
The filtered-colimit presentation of an arbitrary module is already exposed
by Chapter 11, and flatness of a directed limit is already exposed by Chapter
39; the declarations below use those interfaces rather than introducing
parallel predicates.
-/

namespace Formalization.Books.Algebra.Unit81

open Formalization.Books.Algebra.Unit10

universe u v w z

/-! ## Factorization through finite free modules -/

/- The source's phrase `N + Rx` is the submodule supremum
   `N ⊔ Submodule.span R {x}`. -/

/-- The four equivalent factorization conditions for a flat module.

This is the source's `lemma-flat-factors-free`.  The finite free modules
`R^n` and `R^m` are written as `Fin n →₀ R` and `Fin m →₀ R`, respectively.
-/
theorem flat_factors_free
    {R : Type u} {M : Type v} [CommRing R]
    [AddCommGroup M] [Module R M] :
    List.TFAE [
      Module.Flat R M,
      ∀ {n : ℕ} (f : (Fin n →₀ R) →ₗ[R] M)
        {x : Fin n →₀ R}, x ∈ LinearMap.ker f →
        ∃ (m : ℕ) (h : (Fin n →₀ R) →ₗ[R] (Fin m →₀ R))
          (g : (Fin m →₀ R) →ₗ[R] M),
          f = g.comp h ∧ x ∈ LinearMap.ker h,
      ∀ {n m : ℕ} (f : (Fin n →₀ R) →ₗ[R] M)
        (N : Submodule R (Fin n →₀ R)),
        N ≤ LinearMap.ker f →
        ∀ (h : (Fin n →₀ R) →ₗ[R] (Fin m →₀ R)),
        N ≤ LinearMap.ker h →
        (∃ g : (Fin m →₀ R) →ₗ[R] M, f = g.comp h) →
        ∀ {x : Fin n →₀ R}, x ∈ LinearMap.ker f →
          ∃ (m' : ℕ) (h' : (Fin n →₀ R) →ₗ[R] (Fin m' →₀ R)),
            N ⊔ Submodule.span R ({x} : Set (Fin n →₀ R)) ≤
                LinearMap.ker h' ∧
              ∃ g' : (Fin m' →₀ R) →ₗ[R] M, f = g'.comp h',
      ∀ {n : ℕ} (f : (Fin n →₀ R) →ₗ[R] M)
        (N : Submodule R (Fin n →₀ R)),
        N ≤ LinearMap.ker f → N.FG →
        ∃ (m : ℕ) (h : (Fin n →₀ R) →ₗ[R] (Fin m →₀ R))
          (g : (Fin m →₀ R) →ₗ[R] M),
          f = g.comp h ∧ N ≤ LinearMap.ker h] := by
  sorry

/-! ## Finitely presented sources and Hom lifting -/

/-- A map from a finitely presented module to a flat module factors through a
finite free module.

This is the source's `lemma-flat-factors-fp`; the finite free target is put in
Mathlib's canonical `Fin n →₀ R` form. -/
theorem flat_factors_finitePresentation
    {R : Type u} {M : Type v} [CommRing R]
    [AddCommGroup M] [Module R M] :
    Module.Flat R M ↔
      ∀ (P : Type w) [AddCommGroup P] [Module R P]
        [Module.FinitePresentation R P] (f : P →ₗ[R] M),
        ∃ (n : ℕ) (h : P →ₗ[R] (Fin n →₀ R))
          (g : (Fin n →₀ R) →ₗ[R] M), f = g.comp h := by
  sorry

/-- Flatness is equivalent to lifting maps from finitely presented modules
through every surjection by postcomposition on `Hom`.

This is the source's `lemma-flat-surjective-hom`; `internalHomPostcomp` is
Chapter 10's canonical implementation of the induced Hom map. -/
theorem flat_iff_surjective_hom
    {R : Type u} {M : Type v} [CommRing R]
    [AddCommGroup M] [Module R M] :
    Module.Flat R M ↔
      ∀ (P : Type w) [AddCommGroup P] [Module R P]
        [Module.FinitePresentation R P]
        (N : Type z) [AddCommGroup N] [Module R N]
        (q : N →ₗ[R] M), Function.Surjective q →
        Function.Surjective (internalHomPostcomp (M := P) q) := by
  sorry

/-! ## Directed systems and Lazard's theorem -/

/- A directed system of finite free modules together with its identification
   with the target module.  `DirectLimit` is Mathlib's explicit colimit model
   for a directed system; the existing `directLimit_flat` theorem from Chapter
   39 supplies the flatness assertion used in the source's forward direction.
-/
structure DirectedFreeFiniteSystem
    {R : Type u} {M : Type v} [CommRing R]
    [AddCommGroup M] [Module R M] where
  index : Type (max u v)
  [indexPreorder : Preorder index]
  [indexNonempty : Nonempty index]
  [indexDirected : IsDirectedOrder index]
  stage : index → Type (max u v)
  [stageAddCommGroup : ∀ i, AddCommGroup (stage i)]
  [stageModule : ∀ i, Module R (stage i)]
  map : ∀ i j, i ≤ j → stage i →ₗ[R] stage j
  [stageDirectedSystem : DirectedSystem stage (map · · ·)]
  free : ∀ i, Module.Free R (stage i)
  finite : ∀ i, Module.Finite R (stage i)
  targetIso : Nonempty (DirectLimit stage map ≃ₗ[R] M)

/- The preliminary assertion in Lazard's proof that every module is a
   filtered colimit of finitely presented modules is already represented by
   `Unit11.exists_filteredColimit_finitelyPresented`, with its canonical
   `FilteredFinitelyPresentedModuleColimit` witness. -/

/-- **Lazard's theorem.** A module is flat exactly when it is a directed
colimit of finite free modules. -/
theorem lazard
    {R : Type u} {M : Type v} [CommRing R]
    [AddCommGroup M] [Module R M] :
    Module.Flat R M ↔ Nonempty (DirectedFreeFiniteSystem (R := R) (M := M)) := by
  sorry

end Formalization.Books.Algebra.Unit81
