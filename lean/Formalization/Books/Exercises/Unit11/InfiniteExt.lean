import Formalization.Books.Algebra.Unit71.ExtGroups
import Mathlib.Algebra.TrivSqZeroExt.Ideal
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Exercises, Chapter 11: Ext groups — non-finite Ext¹

An infinite square-zero extension of a field supplies a ring and ideal for
which the first self-Ext group of the residue module is not finite.
-/

namespace Formalization.Books.Exercises.Unit11

open CategoryTheory
open Formalization.Books.Algebra.Unit71

universe u

noncomputable section

/-! ## An infinite square-zero example -/

/-- The infinite-dimensional square-zero module used in the example. -/
abbrev infiniteSquareZeroModule (k : Type u) [Field k] := ℕ →₀ k

/-- The trivial square-zero extension of `k` by an infinite-dimensional module. -/
abbrev infiniteSquareZeroRing (k : Type u) [Field k] :=
  TrivSqZeroExt k (infiniteSquareZeroModule k)

/-- The square-zero ideal in the trivial square-zero extension. -/
def infiniteSquareZeroIdeal (k : Type u) [Field k] :
    Ideal (infiniteSquareZeroRing k) :=
  TrivSqZeroExt.kerIdeal k (infiniteSquareZeroModule k)

/-- The residue module of the infinite square-zero extension. -/
abbrev infiniteSquareZeroResidueModule (k : Type u) [Field k] :
    ModuleCat (infiniteSquareZeroRing k) :=
  ModuleCat.of (infiniteSquareZeroRing k)
    (infiniteSquareZeroRing k ⧸ infiniteSquareZeroIdeal k)

/-- The first self-Ext of the residue module is not finite over the ring. -/
theorem infinite_square_zero_ext_one_not_finite (k : Type u) [Field k] :
    ¬ Module.Finite (infiniteSquareZeroRing k)
        (ExtGroup (infiniteSquareZeroResidueModule k)
          (infiniteSquareZeroResidueModule k) 1) := by
  let A := infiniteSquareZeroRing k
  let K := infiniteSquareZeroIdeal k
  let M := infiniteSquareZeroResidueModule k
  intro hfin
  letI : Module.Finite A (ExtGroup M M 1) := by
    simpa [A, M] using hfin
  let f : ModuleCat.of A K ⟶ ModuleCat.of A A :=
    ModuleCat.ofHom K.subtype
  let g : ModuleCat.of A A ⟶ M :=
    ModuleCat.ofHom ((Ideal.Quotient.mkₐ A K).toLinearMap)
  have hfg : f ≫ g = 0 := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change Ideal.Quotient.mk K x = 0
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    exact x.property
  have hex : Function.Exact K.subtype ((Ideal.Quotient.mkₐ A K).toLinearMap) := by
    intro x
    constructor
    · intro hx
      have hxK : x ∈ K := Ideal.Quotient.eq_zero_iff_mem.mp hx
      exact ⟨⟨x, hxK⟩, rfl⟩
    · rintro ⟨y, rfl⟩
      exact Ideal.Quotient.eq_zero_iff_mem.mpr y.property
  have hmono : Function.Injective K.subtype := by
    intro x y hxy
    exact Subtype.ext hxy
  have hepi : Function.Surjective ((Ideal.Quotient.mkₐ A K).toLinearMap) := by
    exact Ideal.Quotient.mkₐ_surjective A K
  let S : ShortComplex (ModuleCat A) := ShortComplex.mk f g hfg
  have hS : S.ShortExact := ModuleCat.shortComplex_shortExact S hex hmono hepi
  have hcomp : ∀ w : ModuleCat.of A A ⟶ M, f ≫ w = 0 := by
    intro w
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rcases x with ⟨x, hx⟩
    have hx' : x = TrivSqZeroExt.inr x.snd :=
      (TrivSqZeroExt.mem_kerIdeal_iff_inr k
        (infiniteSquareZeroModule k) x).mp hx
    change w x = 0
    rw [hx']
    rw [show TrivSqZeroExt.inr x.snd = x • (1 : A) by
      rw [← hx']
      simp]
    rw [map_smul]
    obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective (w 1)
    rw [← hb]
    change Ideal.Quotient.mk K (x * b) = 0
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    simpa [mul_comm] using K.mul_mem_left b hx
  have hzero : ∀ z : ExtGroup (ModuleCat.of A A) M 0,
      (CategoryTheory.Abelian.Ext.mk₀ f).comp z (zero_add 0) = 0 := by
    intro z
    rw [← CategoryTheory.Abelian.Ext.mk₀_addEquiv₀_apply z,
      CategoryTheory.Abelian.Ext.mk₀_comp_mk₀,
      CategoryTheory.Abelian.Ext.mk₀_eq_zero_iff]
    exact hcomp (CategoryTheory.Abelian.Ext.addEquiv₀ z)
  have hscalarQ (a : A) (q : A ⧸ K) :
      a • q = a.fst • q := by
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective q
    apply (Submodule.Quotient.eq K).mpr
    change a * b - TrivSqZeroExt.inl a.fst * b ∈ K
    apply RingHom.mem_ker.mpr
    change TrivSqZeroExt.fst
      (a * b - TrivSqZeroExt.inl (TrivSqZeroExt.fst a) * b) = 0
    rw [TrivSqZeroExt.fst_sub, TrivSqZeroExt.fst_mul,
      TrivSqZeroExt.fst_mul, TrivSqZeroExt.fst_inl]
    simp
  have hscalarH (a : A) (w : S.X₁ ⟶ M) :
      a • w = a.fst • w := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change a • w x = a.fst • w x
    exact hscalarQ a (w x)
  let alpha : (S.X₁ ⟶ M) →ₗ[A]
      ExtGroup M M 1 := by
    exact (hS.extClass.precompOfLinear A M (Nat.add_zero 1)).comp
      (CategoryTheory.Abelian.Ext.linearEquiv₀
        (R := A) (X := S.X₁) (Y := M)).symm.toLinearMap
  have halpha : Function.Injective alpha := by
    intro p q hpq
    have hx : alpha (p - q) = 0 := by
      rw [map_sub, hpq, sub_self]
    obtain ⟨z, hz⟩ :=
      CategoryTheory.Abelian.Ext.contravariant_sequence_exact₁ hS M
        ((CategoryTheory.Abelian.Ext.linearEquiv₀
          (R := A) (X := S.X₁) (Y := M)).symm (p - q))
        (n₁ := 1) (Nat.add_zero 1) (by simpa [alpha] using hx)
    have hz0 :
        (CategoryTheory.Abelian.Ext.mk₀ f).comp z (zero_add 0) = 0 := by
      rw [← CategoryTheory.Abelian.Ext.mk₀_addEquiv₀_apply z,
        CategoryTheory.Abelian.Ext.mk₀_comp_mk₀,
        CategoryTheory.Abelian.Ext.mk₀_eq_zero_iff]
      simpa [S] using hcomp (CategoryTheory.Abelian.Ext.addEquiv₀ z)
    have hx0 :
        (CategoryTheory.Abelian.Ext.linearEquiv₀
          (R := A) (X := S.X₁) (Y := M)).symm (p - q) = 0 := by
      rw [← hz]
      exact hz0
    have hpq0 : p - q = 0 := by
      apply (CategoryTheory.Abelian.Ext.linearEquiv₀
        (R := A) (X := S.X₁) (Y := M)).symm.injective
      simpa using hx0
    exact sub_eq_zero.mp hpq0
  have hsurj : Function.Surjective alpha := by
    intro z
    have hz :
        (CategoryTheory.Abelian.Ext.mk₀ S.g).comp z (zero_add 1) = 0 := by
      exact CategoryTheory.Abelian.Ext.eq_zero_of_projective
        ((CategoryTheory.Abelian.Ext.mk₀ S.g).comp z (zero_add 1))
    obtain ⟨x, hx⟩ :=
      CategoryTheory.Abelian.Ext.contravariant_sequence_exact₃ hS M z hz
        (n₀ := 0) (Nat.add_zero 1)
    refine ⟨(CategoryTheory.Abelian.Ext.linearEquiv₀
      (R := A) (X := S.X₁) (Y := M)) x, ?_⟩
    simpa [alpha] using hx
  let ealpha : (S.X₁ ⟶ M) ≃ₗ[A] ExtGroup M M 1 :=
    LinearEquiv.ofBijective alpha ⟨halpha, hsurj⟩
  have hfiniteH : Module.Finite A (S.X₁ ⟶ M) := by
    exact Module.Finite.equiv ealpha.symm
  have hfiniteK : Module.Finite k (S.X₁ ⟶ M) := by
    have hfg : (⊤ : Submodule A (S.X₁ ⟶ M)).FG := hfiniteH.fg_top
    obtain ⟨s, hsfin, hs⟩ := Submodule.fg_def.mp hfg
    refine ⟨?_⟩
    rw [Submodule.fg_def]
    refine ⟨s, hsfin, ?_⟩
    apply top_unique
    intro x hx
    have hxA : x ∈ Submodule.span A s := by
      rw [hs]
      trivial
    refine Submodule.span_induction (s := (s : Set (S.X₁ ⟶ M)))
      (fun x hx => Submodule.subset_span hx) (Submodule.zero_mem _)
      (fun x y hx hy hxp hyp => Submodule.add_mem _ hxp hyp)
      (fun a x hx hxp => by
        rw [hscalarH a x]
        exact Submodule.smul_mem _ a.fst hxp) hxA
  let sndK : (S.X₁ : Type u) →ₗ[k] (infiniteSquareZeroModule k) :=
    (TrivSqZeroExt.sndHom k (infiniteSquareZeroModule k)).comp
      (K.subtype.restrictScalars k)
  let coord (n : ℕ) : (S.X₁ : Type u) →ₗ[k] k :=
    (Finsupp.lapply n).comp sndK
  let qInl : k →ₗ[k] (A ⧸ K) := Algebra.linearMap k (A ⧸ K)
  have hsnd (a : A) (x : (S.X₁ : Type u)) :
      sndK (a • x) = a.fst • sndK x := by
    have hx0 : (x : A).fst = 0 := by
      have hx' := (TrivSqZeroExt.mem_kerIdeal_iff_inr k
        (infiniteSquareZeroModule k) (x : A)).mp x.property
      rw [hx']
      rfl
    change (a * (x : A)).snd = a.fst • (x : A).snd
    rw [TrivSqZeroExt.snd_mul]
    simp [hx0]
  let φ (n : ℕ) : (S.X₁ : Type u) →ₗ[A] (M : Type u) :=
    { toFun := fun x => qInl (coord n x)
      map_add' := by intro x y; simp [coord, qInl]
      map_smul' := by
        intro a x
        change qInl (coord n (a • x)) = a • qInl (coord n x)
        rw [show coord n (a • x) = a.fst • coord n x by
          dsimp [coord]
          change (sndK (a • x)) n = a.fst * (sndK x) n
          rw [hsnd]
          simp]
        rw [map_smul, hscalarQ] }
  let v (n : ℕ) : S.X₁ ⟶ M := ModuleCat.ofHom (φ n)
  let fstA : A →+* k := (TrivSqZeroExt.fstHom k k
    (infiniteSquareZeroModule k)).toRingHom
  have hfstK : ∀ x : A, x ∈ K → fstA x = 0 := by
    intro x hx
    have hx' : x ∈ TrivSqZeroExt.kerIdeal k
        (infiniteSquareZeroModule k) := by
      simpa [K, infiniteSquareZeroIdeal] using hx
    change x ∈ RingHom.ker fstA at hx'
    exact RingHom.mem_ker.mp hx'
  let qfst : (A ⧸ K) →+* k := Ideal.Quotient.lift K fstA hfstK
  have hqfst_qInl (z : k) : qfst (qInl z) = z := by
    change fstA (TrivSqZeroExt.inl z) = z
    rfl
  have hqfst_smul (a : k) (q : A ⧸ K) :
      qfst (a • q) = a * qfst q := by
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective q
    change qfst (a • (Submodule.Quotient.mk (p := K) b)) =
      a * qfst (Submodule.Quotient.mk (p := K) b)
    rw [← Submodule.Quotient.mk_smul]
    change fstA (a • b) = a * fstA b
    rw [Algebra.smul_def, map_mul]
    rfl
  have hvli : LinearIndependent k v := by
    classical
    rw [linearIndependent_iff']
    intro s c hsum i hi
    let x : (S.X₁ : Type u) :=
      ⟨TrivSqZeroExt.inr (Finsupp.single i (1 : k)), by
        apply (TrivSqZeroExt.mem_kerIdeal_iff_inr k
          (infiniteSquareZeroModule k) _).2
        rfl⟩
    have hsndx : sndK x = Finsupp.single i (1 : k) := by
      change TrivSqZeroExt.snd (x : A) = _
      rw [show (x : A) = TrivSqZeroExt.inr
        (Finsupp.single i (1 : k)) by rfl]
      simp
    have hcoord (j : ℕ) : coord j x = if j = i then 1 else 0 := by
      change (Finsupp.lapply (R := k) j) (sndK x) = _
      rw [hsndx, Finsupp.lapply_apply]
      by_cases hji : j = i
      · simp [hji]
      · simp [Finsupp.single_apply, hji]
    have hv (j : ℕ) :
        v j x = qInl (if j = i then 1 else 0) := by
      change qInl (coord j x) = _
      rw [hcoord]
    have hval : ∑ j ∈ s, c j • v j x = 0 := by
      simpa using congrArg (fun w : S.X₁ ⟶ M => w x) hsum
    have hval' := congrArg qfst hval
    have hterm (j : ℕ) :
        qfst (c j • v j x) = if j = i then c j else 0 := by
      by_cases hji : j = i
      · subst j
        rw [hv]
        simp [hqfst_smul, hqfst_qInl]
      · rw [hv]
        simp [hji, hqfst_smul, hqfst_qInl]
    have hsum' : ∑ j ∈ s, (if j = i then c j else 0) = 0 := by
      simpa only [map_sum, map_zero, hterm] using hval'
    simpa [Finset.sum_ite_irrel, hi] using hsum'
  letI : Module.Finite k (S.X₁ ⟶ M) := hfiniteK
  exact (Module.Finite.not_linearIndependent_of_infinite v) hvli

/-! ## The Noetherian contrast -/

/-- Over a Noetherian ring, the corresponding Ext group of a quotient by an
ideal is finite. -/
theorem noetherian_quotient_ext_one_finite
    {R : Type u} [CommRing R] [IsNoetherianRing R] (I : Ideal R) :
    Module.Finite R
      (ExtGroup (ModuleCat.of R (R ⧸ I))
        (ModuleCat.of R (R ⧸ I)) 1) := by
  let _ : Module.Finite R (R ⧸ I) :=
    Module.Finite.of_surjective
      (Ideal.Quotient.mkₐ R I).toLinearMap
      (Ideal.Quotient.mkₐ_surjective R I)
  exact ext_finite_of_noetherian
    (ModuleCat.of R (R ⧸ I)) (ModuleCat.of R (R ⧸ I)) 1

end

end Formalization.Books.Exercises.Unit11
