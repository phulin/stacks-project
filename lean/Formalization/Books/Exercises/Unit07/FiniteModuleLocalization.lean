import Mathlib.Algebra.Module.LocalizedModule.Basic
import Mathlib.RingTheory.Finiteness.Basic

/-!
# Exercises, Chapter 7: Localization

This file records the finite-module localization exercise.  A zero module is
represented by the canonical `Subsingleton` predicate, and principal module
localization uses `LocalizedModule (Submonoid.powers f) M`.
-/

noncomputable section

universe u v

namespace Formalization.Books.Exercises.Unit07

/-! ## A finite module killed by one principal localization -/

/-- If a finite module becomes zero after localization at `S`, then one
element of `S` already kills its principal localization. -/
theorem exists_principal_localization_subsingleton_of_localization_subsingleton
    {A : Type u} [CommRing A] (S : Submonoid A)
    {M : Type v} [AddCommGroup M] [Module A M] [Module.Finite A M]
    (hM : Subsingleton (LocalizedModule S M)) :
    ∃ f : A, f ∈ S ∧
      Subsingleton (LocalizedModule (Submonoid.powers f) M) := by
  classical
  obtain ⟨n, s, hs⟩ := Module.Finite.exists_fin (R := A) (M := M)
  choose r hr hkill using fun i => (LocalizedModule.subsingleton_iff.mp hM) (s i)
  let f : A := ∏ i, r i
  have hfS : f ∈ S := by
    exact S.prod_mem (fun i _ => hr i)
  have hfkill : ∀ m : M, f • m = 0 := by
    intro m
    have hm : m ∈ (Submodule.span A (Set.range s)) := by
      rw [hs]
      exact Submodule.mem_top
    induction hm using Submodule.span_induction with
    | mem x hx =>
        obtain ⟨i, rfl⟩ := hx
        rw [show f = (∏ j ∈ {i}ᶜ, r j) * r i by
          simpa [f] using (Fintype.prod_eq_prod_compl_mul i r)]
        rw [mul_smul, hkill i]
        exact smul_zero _
    | zero => simp
    | add x y _ _ hx hy => simp [hx, hy]
    | smul a x _ hx =>
        calc
          f • a • x = a • f • x := by rw [smul_comm]
          _ = 0 := by rw [hx, smul_zero]
  refine ⟨f, hfS, ?_⟩
  rw [LocalizedModule.subsingleton_iff]
  intro m
  refine ⟨f, ?_, hfkill m⟩
  exact Submonoid.mem_powers f

end Formalization.Books.Exercises.Unit07
