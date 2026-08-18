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
  classical
  let E := Module.End Aᵐᵒᵖ M
  let T := Module.End E M
  let : Nontrivial M := Submodule.nontrivial_iff_ne_bot.mpr hM
  let r : Aᵐᵒᵖ →+* T := Module.toModuleEnd E (S := Aᵐᵒᵖ) M
  have hr : Function.Bijective r := by
    constructor
    · intro a b hab
      have hAnn : Module.annihilator Aᵐᵒᵖ M = ⊥ := by
        have h := (isSimpleRing_iff_isTwoSided_imp.mp
          (inferInstance : IsSimpleRing Aᵐᵒᵖ)).2
          (Module.annihilator Aᵐᵒᵖ M) inferInstance
        exact h.resolve_right (by
          intro htop
          exact (not_subsingleton M)
            (Module.annihilator_eq_top_iff.mp htop))
      let : FaithfulSMul Aᵐᵒᵖ M := Module.annihilator_eq_bot.mp hAnn
      apply FaithfulSMul.eq_of_smul_eq_smul (α := M)
      intro m
      exact DFunLike.congr_fun hab m
    · intro f
      let leftMul : M → E := fun n =>
        ((LinearMap.mulLeft Aᵐᵒᵖ (n : A)).domRestrict M).codRestrict M
          (fun z => M.smul_mem (MulOpposite.op (z : A)) n.property)
      let I : Ideal A := Submodule.span A (M : Set A)
      let : I.IsTwoSided := ⟨fun b ha => by
        induction ha using Submodule.span_induction with
        | mem x hx =>
            exact Submodule.subset_span (by simpa using M.smul_mem (MulOpposite.op b) hx)
        | zero => simp
        | add x y _ _ hx hy => simpa [add_mul] using I.add_mem hx hy
        | smul a x _ hx =>
            simpa [smul_eq_mul, mul_assoc] using I.mul_mem_left a hx⟩
      have hI : I ≠ ⊥ := by
        intro hbot
        obtain ⟨m, hm⟩ := exists_ne (0 : M)
        have hmI : (m : A) ∈ I := Submodule.subset_span m.property
        rw [hbot] at hmI
        exact hm (by simpa using hmI)
      have hItop : I = ⊤ :=
        ((isSimpleRing_iff_isTwoSided_imp.mp (inferInstance : IsSimpleRing A)).2 I inferInstance)
          |>.resolve_left hI
      have h1 : (1 : A) ∈ I := hItop ▸ Submodule.mem_top
      change (1 : A) ∈ Submodule.span A (M : Set A) at h1
      obtain ⟨c, t, ht, hc, hct⟩ :=
        (Submodule.mem_span_iff_exists_finset_subset).mp h1
      let xM : t → M := fun x => ⟨x.1, ht x.2⟩
      let nM (m : M) (x : t) : M :=
        ⟨(m : A) * c x.1, M.smul_mem (MulOpposite.op (c x.1)) m.property⟩
      let a0 : A := (∑ x ∈ t.attach, c x.1 * (f (xM x) : A))
      have hct' : (∑ x ∈ t.attach, c x.1 * x.1) = 1 := by
        have hs := Finset.sum_attach t (fun x : A => c x * x)
        calc
          (∑ x ∈ t.attach, c x.1 * x.1) = ∑ x ∈ t, c x * x := hs
          _ = 1 := by simpa [smul_eq_mul] using hct
      refine ⟨MulOpposite.op a0, ?_⟩
      apply LinearMap.ext
      intro m
      have hm : m = ∑ x ∈ t.attach, leftMul (nM m x) • xM x := by
        apply Subtype.ext
        calc
          (m : A) = (m : A) * 1 := by simp
          _ = (m : A) * (∑ x ∈ t.attach, c x.1 * x.1) := by rw [hct']
          _ = ∑ x ∈ t.attach, ((m : A) * c x.1) * x.1 := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro x hx
            rw [mul_assoc]
          _ = (∑ x ∈ t.attach, leftMul (nM m x) • xM x : M) := by
            rw [Submodule.coe_sum]
            apply Finset.sum_congr rfl
            intro x hx
            rfl
      have hf : f m = ∑ x ∈ t.attach, leftMul (nM m x) • f (xM x) := by
        calc
          f m = f (∑ x ∈ t.attach, leftMul (nM m x) • xM x) := congrArg f hm
          _ = ∑ x ∈ t.attach, leftMul (nM m x) • f (xM x) := by
            simp only [map_sum, map_smul]
      apply Subtype.ext
      calc
        ((r (MulOpposite.op a0)) m : A) = (m : A) * a0 := by rfl
        _ = ∑ x ∈ t.attach, ((m : A) * c x.1) * (f (xM x) : A) := by
          simp [a0, Finset.mul_sum, mul_assoc]
        _ = (f m : A) := by
          rw [hf]
          rw [Submodule.coe_sum]
          apply Finset.sum_congr rfl
          intro x hx
          rfl
  let e : Aᵐᵒᵖ ≃+* T := RingEquiv.ofBijective r hr
  exact ⟨(RingEquiv.opOp A).trans e.op⟩

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
  have : Nontrivial N := Submodule.nontrivial_iff_ne_bot.mpr hN
  have : IsArtinianRing A := IsArtinianRing.of_finite k A
  have : Module.Finite A N := Module.Finite.of_fg (Submodule.fg_span (Set.finite_singleton m))
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
  have : Nontrivial M := IsSimpleModule.nontrivial A M
  obtain ⟨m, hm⟩ := exists_ne (0 : M)
  have : Module.Finite A M :=
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
