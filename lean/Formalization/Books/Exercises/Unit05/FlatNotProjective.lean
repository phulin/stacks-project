import Mathlib.RingTheory.Flat.EquationalCriterion
import Mathlib.Algebra.Module.Projective
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.Ideal.IdempotentFG
import Mathlib.RingTheory.Ideal.Pure

/-!
# Exercises, Chapter 5: Flat ring maps

This file records the finite flat non-projective example and the warning that
finite presentation rules out such an example.  The exercise asks for an
example rather than prescribing a particular presentation, so its existence
is stated with the ring and module as explicit witnesses.
-/

universe u

namespace Formalization.Books.Exercises.Unit05

/-! ## Finite flat modules need not be projective -/

/-- Every finitely presented flat module is projective.  This is the existing
Mathlib theorem used by the source remark. -/
theorem projective_of_flat_of_finitePresentation
    {A M : Type u} [CommRing A] [AddCommGroup M] [Module A M]
    (hflat : Module.Flat A M) (hfinitePresentation : Module.FinitePresentation A M) :
    Module.Projective A M := by
  exact @Module.Flat.projective_of_finitePresentation A M _ _ _ hflat
    hfinitePresentation

/-! The finite-support ideal in a product of copies of `𝔽₂`. -/

def finiteSupportIdeal : Ideal (ULift.{u} ℕ → ZMod 2) where
  carrier := {x | (Function.support x).Finite}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy
    apply (hx.union hy).subset
    intro n hn
    by_contra hzero
    have hxzero : x n = 0 := by
      by_contra hxzero
      exact hzero (Or.inl hxzero)
    have hyzero : y n = 0 := by
      by_contra hyzero
      exact hzero (Or.inr hyzero)
    simp [hxzero, hyzero] at hn
  smul_mem' := by
    intro r x hx
    exact hx.subset (Function.support_smul_subset_right r x)

private lemma product_zmodTwo_idempotent (x : ULift.{u} ℕ → ZMod 2) :
    IsIdempotentElem x := by
  funext n
  let i : Fin 2 := (ZMod.finEquiv 2).symm (x n)
  have hi : ZMod.finEquiv 2 i = x n :=
    (ZMod.finEquiv 2).apply_symm_apply _
  change x n * x n = x n
  rw [← hi]
  have hi' : i = 0 ∨ i = 1 := by omega
  rcases hi' with h | h
  · rw [h]
    simp
  · rw [h]
    simp

private lemma finiteSupportIdeal_pure :
    Ideal.Pure (finiteSupportIdeal : Ideal (ULift.{u} ℕ → ZMod 2)) := by
  apply Ideal.Pure.of_inf_eq_mul
  intro J hJ
  have hJid : IsIdempotentElem J := by
    rw [IsIdempotentElem]
    apply le_antisymm
    · exact Ideal.mul_le.mpr fun x hx y hy => J.mul_mem_left x hy
    · intro x hx
      convert Ideal.mul_mem_mul hx hx using 1
      exact (product_zmodTwo_idempotent x).eq.symm
  obtain ⟨e, he, hJe⟩ := (J.isIdempotentElem_iff_of_fg hJ).mp hJid
  subst J
  apply le_antisymm
  · intro x hx
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp hx.2
    have hxe : x * e = x := by
      rw [← ha, mul_assoc, he.eq]
    rw [← hxe]
    exact Ideal.mul_mem_mul hx.1 (Ideal.subset_span (by simp))
  · refine Ideal.mul_le.mpr ?_
    intro x hx y hy
    refine ⟨(finiteSupportIdeal : Ideal (ULift.{u} ℕ → ZMod 2)).mul_mem_right y hx, ?_⟩
    obtain ⟨a, ha⟩ := (Submodule.mem_span_singleton).mp hy
    rw [← ha]
    simpa [smul_eq_mul, mul_assoc] using
      (Submodule.smul_mem (R := ULift.{u} ℕ → ZMod 2) (M := ULift.{u} ℕ → ZMod 2)
        ((ULift.{u} ℕ → ZMod 2) ∙ e) (x * a)
        (Submodule.subset_span (show e ∈ ({e} : Set (ULift.{u} ℕ → ZMod 2)) by simp)))

private lemma finiteSupportIdeal_not_fg :
    ¬ (finiteSupportIdeal : Ideal (ULift.{u} ℕ → ZMod 2)).FG := by
  intro hI
  obtain ⟨s, hs⟩ := hI
  have hsI : ∀ x ∈ s, x ∈ (finiteSupportIdeal : Ideal (ULift.{u} ℕ → ZMod 2)) := by
    intro x hx
    rw [← hs]
    exact Ideal.subset_span hx
  let T : Set (ULift.{u} ℕ) :=
    ⋃ x ∈ (s : Set (ULift.{u} ℕ → ZMod 2)), Function.support x
  have hT : T.Finite := by
    dsimp [T]
    apply Set.Finite.biUnion s.finite_toSet
    intro x hx
    exact hsI x hx
  obtain ⟨m, hm⟩ := hT.exists_notMem
  let n : ℕ := m.down
  let d : ULift.{u} ℕ → ZMod 2 := fun i =>
    if i.down = n then 1 else 0
  have hd : d ∈ (finiteSupportIdeal : Ideal (ULift.{u} ℕ → ZMod 2)) := by
    apply Set.Finite.subset (Set.finite_singleton (ULift.up n))
    intro i hi
    have hi' : i.down = n := by
      simpa [d, Function.mem_support] using hi
    exact Set.mem_singleton_iff.mpr (ULift.ext i (ULift.up n) hi')
  have hds : d ∈ Ideal.span (s : Set (ULift.{u} ℕ → ZMod 2)) := by
    rw [hs]
    exact hd
  have hs0 : ∀ x ∈ s, x m = 0 := by
    intro x hx
    by_contra hzero
    apply hm
    exact Set.mem_iUnion.mpr ⟨x, Set.mem_iUnion.mpr ⟨hx, hzero⟩⟩
  let ev : (ULift.{u} ℕ → ZMod 2) →+* ZMod 2 :=
    Pi.evalRingHom (fun _ : ULift.{u} ℕ => ZMod 2) m
  have hker : Ideal.span (s : Set (ULift.{u} ℕ → ZMod 2)) ≤ RingHom.ker ev := by
    rw [Ideal.span_le]
    intro x hx
    exact RingHom.mem_ker.mpr (hs0 x hx)
  have hz : ev d = 0 := RingHom.mem_ker.mp (hker hds)
  have hone : ev d = 1 := by
    simp [ev, d, n]
  rw [hone] at hz
  exact one_ne_zero hz

private lemma finiteSupportQuotient_not_projective :
    ¬ Module.Projective (ULift.{u} ℕ → ZMod 2)
      ((ULift.{u} ℕ → ZMod 2) ⧸ finiteSupportIdeal) := by
  intro hprojective
  let R := ULift.{u} ℕ → ZMod 2
  let I : Ideal R := finiteSupportIdeal
  let q : R →ₗ[R] (R ⧸ I) := I.mkQ
  obtain ⟨sec, hsection⟩ :=
    (Module.Projective.iff_split_of_projective q Ideal.Quotient.mk_surjective).mp
      hprojective
  let retraction : R →ₗ[R] I :=
    { toFun := fun x => ⟨x - sec (q x), by
        apply (Ideal.Quotient.eq_zero_iff_mem).mp
        change q (x - sec (q x)) = 0
        rw [map_sub]
        have hqsec : q (sec (q x)) = q x := by
          have h := LinearMap.congr_fun hsection (q x)
          simpa [LinearMap.comp_apply] using h
        rw [hqsec, sub_self]
        ⟩
      map_add' := by
        intro x y
        apply Subtype.ext
        dsimp
        rw [map_add, map_add]
        ring
      map_smul' := by
        intro r x
        apply Subtype.ext
        dsimp
        change r • x - sec (q (r • x)) = r • (x - sec (q x))
        rw [map_smul, map_smul]
        rw [smul_sub] }
  have hretraction_surjective : Function.Surjective retraction := by
    intro x
    refine ⟨(x : R), ?_⟩
    apply Subtype.ext
    dsimp [retraction]
    have hqx : q (x : R) = 0 := by
      exact (Ideal.Quotient.eq_zero_iff_mem).mpr x.property
    rw [hqx, map_zero, sub_zero]
  have hfinite : Module.Finite R I :=
    Module.Finite.of_surjective retraction hretraction_surjective
  exact finiteSupportIdeal_not_fg (Module.Finite.iff_fg.mp hfinite)

/-- There is a finite flat module which is not projective. -/
theorem exists_finite_flat_nonprojective :
    ∃ (A : Type u) (_ : CommRing A) (M : Type u) (_ : AddCommGroup M)
      (_ : Module A M),
      Module.Finite A M ∧ Module.Flat A M ∧ ¬ Module.Projective A M := by
  let R := ULift.{u} ℕ → ZMod 2
  let I : Ideal R := finiteSupportIdeal
  have hflat : Module.Flat R (R ⧸ I) := finiteSupportIdeal_pure
  refine ⟨R, inferInstance, R ⧸ I, inferInstance, inferInstance, ?_⟩
  exact ⟨inferInstance, hflat, finiteSupportQuotient_not_projective⟩

/-- Any finite flat non-projective module must be over a non-Noetherian ring. -/
theorem finite_flat_nonprojective_base_not_noetherian
    {A M : Type u} [CommRing A] [AddCommGroup M] [Module A M]
    (hfinite : Module.Finite A M) (hflat : Module.Flat A M)
    (hnotProjective : ¬ Module.Projective A M) :
    ¬ IsNoetherianRing A := by
  intro hnoeth
  exact hnotProjective
    (projective_of_flat_of_finitePresentation hflat
      (@Module.finitePresentation_of_finite A M _ _ _ hnoeth hfinite))

end Formalization.Books.Exercises.Unit05
