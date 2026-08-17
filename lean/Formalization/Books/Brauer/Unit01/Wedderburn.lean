import Formalization.Books.Brauer.Unit01.NoncommutativeAlgebras
import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.RingTheory.SimpleModule.WedderburnArtin

/-!
# Wedderburn's theorem

The source's bicommutant statement is expressed using the canonical
endomorphism-ring construction.  The finite Wedderburn--Artin conclusion is
reused directly from Mathlib.
-/

namespace Formalization.Books.Brauer

universe u v

/- The right action of a ring `A` is represented by a left action of
   `Aᵐᵒᵖ`. -/
abbrev Bicommutant (A : Type u) [Ring A] (M : Submodule Aᵐᵒᵖ A) : Type u :=
  (Module.End (Module.End Aᵐᵒᵖ M) M)ᵐᵒᵖ

theorem rieffel_bicommutant (A : Type u) [Ring A] [IsSimpleRing A]
    (M : Submodule Aᵐᵒᵖ A) (hM : M ≠ ⊥) :
    Nonempty (A ≃+* Bicommutant A M) := by
  sorry

private theorem exists_simple_submodule_of_finite_algebra (k A M : Type*)
    [Field k] [Ring A] [Algebra k A] [FiniteDimensional k A]
    [AddCommGroup M] [Module A M] [Nontrivial M] :
    ∃ S : Submodule A M, IsSimpleModule A S := by
  classical
  obtain ⟨m, hm⟩ := exists_ne (0 : M)
  let N : Submodule A M := Submodule.span A {m}
  have hN : N ≠ ⊥ := by
    intro h
    exact hm ((Submodule.span_eq_bot.mp h) m (by simp))
  haveI : Nontrivial N := Submodule.nontrivial_iff_ne_bot.mpr hN
  haveI : IsArtinianRing A := IsArtinianRing.of_finite k A
  haveI : Module.Finite A N := Module.Finite.of_fg (Submodule.fg_span (Set.finite_singleton m))
  obtain ⟨S, hS, hmin⟩ :=
    IsArtinian.set_has_minimal (R := A) (M := N)
      {P : Submodule A N | P ≠ ⊥} ⟨⊤, top_ne_bot⟩
  have hsimple : IsSimpleModule A S := by
    rw [isSimpleModule_iff_isAtom]
    refine ⟨hS, ?_⟩
    intro P hP
    by_contra hp
    exact (hmin P hp hP).elim
  let e := Submodule.equivMapOfInjective N.subtype N.subtype_injective S
  refine ⟨S.map N.subtype, ?_⟩
  exact e.isSimpleModule_iff.mp hsimple

theorem finite_algebra_has_simple_submodule (k A : Type*) [Field k] [Ring A]
    [Algebra k A] [FiniteDimensional k A] [Nontrivial A] :
    ∃ S : Submodule A A, IsSimpleModule A S := by
  exact exists_simple_submodule_of_finite_algebra k A A

theorem finite_algebra_nonzero_module_has_simple_submodule (k A M : Type*)
    [Field k] [Ring A] [Algebra k A] [FiniteDimensional k A]
    [AddCommGroup M] [Module A M] [Nontrivial M] :
    ∃ S : Submodule A M, IsSimpleModule A S := by
  exact exists_simple_submodule_of_finite_algebra k A M

theorem simple_module_over_finite_algebra_is_finite_dimensional
    (k A M : Type*) [Field k] [Ring A] [Algebra k A] [FiniteDimensional k A]
    [AddCommGroup M] [Module A M] [Module k M] [IsScalarTower k A M]
    [IsSimpleModule A M] : FiniteDimensional k M := by
  haveI : Nontrivial M := IsSimpleModule.nontrivial A M
  obtain ⟨m, hm⟩ := exists_ne (0 : M)
  haveI : Module.Finite A M :=
    Module.Finite.of_surjective (LinearMap.toSpanSingleton A M m)
      (IsSimpleModule.toSpanSingleton_surjective A hm)
  exact Module.Finite.trans A M

theorem simple_module_end_is_division_ring (A M : Type*) [Ring A]
    [AddCommGroup M] [Module A M] [IsSimpleModule A M] :
    Nonempty (DivisionRing (Module.End A M)) := by
  classical
  exact ⟨inferInstance⟩

theorem wedderburn_artin_finite (k : Type v) (A : Type u) [Field k] [Ring A]
    [Algebra k A] [IsSimpleRing A] [FiniteDimensional k A] :
    ∃ (n : ℕ) (_ : NeZero n) (D : Type u) (_ : DivisionRing D)
      (_ : Algebra k D) (_ : FiniteDimensional k D),
      Nonempty (A ≃ₐ[k] Matrix (Fin n) (Fin n) D) := by
  let hA : IsArtinianRing A := IsArtinianRing.of_finite k A
  exact @IsSimpleRing.exists_algEquiv_matrix_divisionRing_finite k A _ _ _ _ hA _

end Formalization.Books.Brauer
