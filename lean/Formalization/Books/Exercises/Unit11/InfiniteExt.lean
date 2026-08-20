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

private abbrev sqRing (k : Type u) [Field k] := infiniteSquareZeroRing k
private abbrev sqIdeal (k : Type u) [Field k] := infiniteSquareZeroIdeal k
private abbrev sqResidue (k : Type u) [Field k] := infiniteSquareZeroResidueModule k

private abbrev sqInclusion (k : Type u) [Field k] :
    ModuleCat.of (sqRing k) (sqIdeal k) ⟶ ModuleCat.of (sqRing k) (sqRing k) :=
  ModuleCat.ofHom (sqIdeal k).subtype

private abbrev sqQuotient (k : Type u) [Field k] :
    ModuleCat.of (sqRing k) (sqRing k) ⟶ sqResidue k :=
  ModuleCat.ofHom ((Ideal.Quotient.mkₐ (sqRing k) (sqIdeal k)).toLinearMap)

private lemma sq_inclusion_quotient_zero (k : Type u) [Field k] :
    sqInclusion k ≫ sqQuotient k = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact Ideal.Quotient.eq_zero_iff_mem.mpr x.property

private lemma sq_quotient_exact (k : Type u) [Field k] :
    Function.Exact (sqIdeal k).subtype
      ((Ideal.Quotient.mkₐ (sqRing k) (sqIdeal k)).toLinearMap) := by
  intro x
  constructor
  · intro hx
    exact ⟨⟨x, Ideal.Quotient.eq_zero_iff_mem.mp hx⟩, rfl⟩
  · rintro ⟨y, rfl⟩
    exact Ideal.Quotient.eq_zero_iff_mem.mpr y.property

private abbrev sqShortComplex (k : Type u) [Field k] : ShortComplex (ModuleCat (sqRing k)) :=
  ShortComplex.mk (sqInclusion k) (sqQuotient k) (sq_inclusion_quotient_zero k)

private lemma sq_shortExact (k : Type u) [Field k] : (sqShortComplex k).ShortExact := by
  apply ModuleCat.shortComplex_shortExact
  · exact sq_quotient_exact k
  · intro x y hxy
    exact Subtype.ext hxy
  · exact Ideal.Quotient.mkₐ_surjective (sqRing k) (sqIdeal k)

private lemma sq_inclusion_comp_zero (k : Type u) [Field k]
    (w : ModuleCat.of (sqRing k) (sqRing k) ⟶ sqResidue k) :
    sqInclusion k ≫ w = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  rintro ⟨x, hx⟩
  have hx' := (TrivSqZeroExt.mem_kerIdeal_iff_inr k (infiniteSquareZeroModule k) x).mp hx
  change w x = 0
  rw [hx', show TrivSqZeroExt.inr x.snd = x • (1 : sqRing k) by rw [← hx']; simp, map_smul]
  obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective (w 1)
  rw [← hb]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (by
    simpa [mul_comm] using (sqIdeal k).mul_mem_left b hx)

private lemma sq_scalar_on_quotient (k : Type u) [Field k]
    (a : sqRing k) (q : sqRing k ⧸ sqIdeal k) : a • q = a.fst • q := by
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective q
  apply (Submodule.Quotient.eq (sqIdeal k)).mpr
  apply RingHom.mem_ker.mpr
  change TrivSqZeroExt.fst
    (a * b - TrivSqZeroExt.inl (TrivSqZeroExt.fst a) * b) = 0
  rw [TrivSqZeroExt.fst_sub, TrivSqZeroExt.fst_mul,
    TrivSqZeroExt.fst_mul, TrivSqZeroExt.fst_inl]
  simp

private lemma sq_ext_comp_zero (k : Type u) [Field k]
    (z : ExtGroup (ModuleCat.of (sqRing k) (sqRing k)) (sqResidue k) 0) :
    (CategoryTheory.Abelian.Ext.mk₀ (sqInclusion k)).comp z (zero_add 0) = 0 := by
  rw [← CategoryTheory.Abelian.Ext.mk₀_addEquiv₀_apply z,
    CategoryTheory.Abelian.Ext.mk₀_comp_mk₀,
    CategoryTheory.Abelian.Ext.mk₀_eq_zero_iff]
  exact sq_inclusion_comp_zero k (CategoryTheory.Abelian.Ext.addEquiv₀ z)

private lemma sq_scalar_on_hom (k : Type u) [Field k]
    (a : sqRing k) (w : (sqShortComplex k).X₁ ⟶ sqResidue k) :
    a • w = a.fst • w := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact sq_scalar_on_quotient k a (w x)

private def sqAlpha (k : Type u) [Field k] :
    ((sqShortComplex k).X₁ ⟶ sqResidue k) →ₗ[sqRing k]
      ExtGroup (sqResidue k) (sqResidue k) 1 :=
  ((sq_shortExact k).extClass.precompOfLinear (sqRing k) (sqResidue k)
    (Nat.add_zero 1)).comp
      (CategoryTheory.Abelian.Ext.linearEquiv₀
        (R := sqRing k) (X := (sqShortComplex k).X₁) (Y := sqResidue k)).symm.toLinearMap

private lemma sq_alpha_injective (k : Type u) [Field k] :
    Function.Injective (sqAlpha k) := by
  intro p q hpq
  have hx : sqAlpha k (p - q) = 0 := by rw [map_sub, hpq, sub_self]
  obtain ⟨z, hz⟩ := CategoryTheory.Abelian.Ext.contravariant_sequence_exact₁
    (sq_shortExact k) (sqResidue k)
      ((CategoryTheory.Abelian.Ext.linearEquiv₀
        (R := sqRing k) (X := (sqShortComplex k).X₁) (Y := sqResidue k)).symm (p - q))
      (n₁ := 1) (Nat.add_zero 1) (by simpa [sqAlpha] using hx)
  have hx0 : (CategoryTheory.Abelian.Ext.linearEquiv₀
      (R := sqRing k) (X := (sqShortComplex k).X₁) (Y := sqResidue k)).symm (p - q) = 0 := by
    rw [← hz]
    exact sq_ext_comp_zero k z
  apply sub_eq_zero.mp
  apply (CategoryTheory.Abelian.Ext.linearEquiv₀
    (R := sqRing k) (X := (sqShortComplex k).X₁) (Y := sqResidue k)).symm.injective
  simpa using hx0

private lemma sq_alpha_surjective (k : Type u) [Field k] :
    Function.Surjective (sqAlpha k) := by
  intro z
  have hz : (CategoryTheory.Abelian.Ext.mk₀ (sqShortComplex k).g).comp
      z (zero_add 1) = 0 :=
    CategoryTheory.Abelian.Ext.eq_zero_of_projective _
  obtain ⟨x, hx⟩ := CategoryTheory.Abelian.Ext.contravariant_sequence_exact₃
    (sq_shortExact k) (sqResidue k) z hz (n₀ := 0) (Nat.add_zero 1)
  refine ⟨(CategoryTheory.Abelian.Ext.linearEquiv₀
    (R := sqRing k) (X := (sqShortComplex k).X₁) (Y := sqResidue k)) x, ?_⟩
  simpa [sqAlpha] using hx

private lemma finite_over_field_of_sq_scalar (k H : Type u) [Field k]
    [AddCommGroup H] [Module (sqRing k) H] [Module k H]
    [Module.Finite (sqRing k) H]
    (hscalar : ∀ (a : sqRing k) (x : H), a • x = a.fst • x) :
    Module.Finite k H := by
  obtain ⟨s, hsfin, hs⟩ := Submodule.fg_def.mp
    (show (⊤ : Submodule (sqRing k) H).FG from Module.Finite.fg_top)
  refine ⟨Submodule.fg_def.mpr ⟨s, hsfin, ?_⟩⟩
  apply top_unique
  intro x _
  have hx : x ∈ Submodule.span (sqRing k) s := by rw [hs]; trivial
  exact Submodule.span_induction (s := (s : Set H))
    (fun y hy => Submodule.subset_span hy) (Submodule.zero_mem _)
    (fun y z _ _ hy hz => Submodule.add_mem _ hy hz)
    (fun a y _ hy => by rw [hscalar a y]; exact Submodule.smul_mem _ a.fst hy) hx

private abbrev sqSnd (k : Type u) [Field k] :
    ((sqShortComplex k).X₁ : Type u) →ₗ[k] infiniteSquareZeroModule k :=
  (TrivSqZeroExt.sndHom k (infiniteSquareZeroModule k)).comp
    ((sqIdeal k).subtype.restrictScalars k)

private abbrev sqCoord (k : Type u) [Field k] (n : ℕ) :
    ((sqShortComplex k).X₁ : Type u) →ₗ[k] k :=
  (Finsupp.lapply n).comp (sqSnd k)

private abbrev sqQInl (k : Type u) [Field k] : k →ₗ[k] (sqRing k ⧸ sqIdeal k) :=
  Algebra.linearMap k (sqRing k ⧸ sqIdeal k)

private lemma sq_snd_smul (k : Type u) [Field k] (a : sqRing k)
    (x : ((sqShortComplex k).X₁ : Type u)) :
    sqSnd k (a • x) = a.fst • sqSnd k x := by
  have hx0 : (x : sqRing k).fst = 0 := by
    rw [(TrivSqZeroExt.mem_kerIdeal_iff_inr k
      (infiniteSquareZeroModule k) (x : sqRing k)).mp x.property]
    rfl
  change (a * (x : sqRing k)).snd = a.fst • (x : sqRing k).snd
  rw [TrivSqZeroExt.snd_mul]
  simp [hx0]

private def sqCoordinateMap (k : Type u) [Field k] (n : ℕ) :
    ((sqShortComplex k).X₁ : Type u) →ₗ[sqRing k] (sqResidue k : Type u) where
  toFun x := sqQInl k (sqCoord k n x)
  map_add' x y := by simp [sqCoord, sqQInl]
  map_smul' a x := by
    change sqQInl k (sqCoord k n (a • x)) = a • sqQInl k (sqCoord k n x)
    rw [show sqCoord k n (a • x) = a.fst • sqCoord k n x by
      change (sqSnd k (a • x)) n = a.fst * (sqSnd k x) n
      rw [sq_snd_smul]
      simp]
    rw [map_smul, sq_scalar_on_quotient]

private abbrev sqCoordinateHom (k : Type u) [Field k] (n : ℕ) :
    (sqShortComplex k).X₁ ⟶ sqResidue k := ModuleCat.ofHom (sqCoordinateMap k n)

private abbrev sqFst (k : Type u) [Field k] : sqRing k →+* k :=
  (TrivSqZeroExt.fstHom k k (infiniteSquareZeroModule k)).toRingHom

private lemma sq_fst_mem (k : Type u) [Field k] (x : sqRing k) (hx : x ∈ sqIdeal k) :
    sqFst k x = 0 := by
  have hx' : x ∈ TrivSqZeroExt.kerIdeal k (infiniteSquareZeroModule k) := by
    simpa [sqIdeal, infiniteSquareZeroIdeal] using hx
  change x ∈ RingHom.ker (sqFst k) at hx'
  exact RingHom.mem_ker.mp hx'

private abbrev sqQuotientFst (k : Type u) [Field k] : sqRing k ⧸ sqIdeal k →+* k :=
  Ideal.Quotient.lift (sqIdeal k) (sqFst k) (sq_fst_mem k)

private lemma sq_quotientFst_inl (k : Type u) [Field k] (z : k) :
    sqQuotientFst k (sqQInl k z) = z := by
  rfl

private lemma sq_quotientFst_smul (k : Type u) [Field k]
    (a : k) (q : sqRing k ⧸ sqIdeal k) :
    sqQuotientFst k (a • q) = a * sqQuotientFst k q := by
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective q
  change sqQuotientFst k (a • (Submodule.Quotient.mk (p := sqIdeal k) b)) =
    a * sqQuotientFst k (Submodule.Quotient.mk (p := sqIdeal k) b)
  rw [← Submodule.Quotient.mk_smul]
  change sqFst k (a • b) = a * sqFst k b
  rw [Algebra.smul_def, map_mul]
  rfl

private def sqBasisElement (k : Type u) [Field k] (i : ℕ) :
    ((sqShortComplex k).X₁ : Type u) :=
  ⟨TrivSqZeroExt.inr (Finsupp.single i (1 : k)), by
    apply (TrivSqZeroExt.mem_kerIdeal_iff_inr k (infiniteSquareZeroModule k) _).2
    rfl⟩

private lemma sq_snd_basis (k : Type u) [Field k] (i : ℕ) :
    sqSnd k (sqBasisElement k i) = Finsupp.single i (1 : k) := by
  change TrivSqZeroExt.snd (sqBasisElement k i : sqRing k) = _
  simp [sqBasisElement]

private lemma sq_coord_basis (k : Type u) [Field k] (i j : ℕ) :
    sqCoord k j (sqBasisElement k i) = if j = i then 1 else 0 := by
  change (Finsupp.lapply (R := k) j) (sqSnd k (sqBasisElement k i)) = _
  rw [sq_snd_basis, Finsupp.lapply_apply]
  by_cases hji : j = i <;> simp [hji]

private lemma sq_hom_basis (k : Type u) [Field k] (i j : ℕ) :
    sqCoordinateHom k j (sqBasisElement k i) =
      sqQInl k (if j = i then 1 else 0) := by
  change sqQInl k (sqCoord k j (sqBasisElement k i)) = _
  rw [sq_coord_basis]

private lemma sq_quotientFst_coordinate_term (k : Type u) [Field k]
    (c : ℕ → k) (i j : ℕ) :
    sqQuotientFst k
      (c j • (ConcreteCategory.hom (sqCoordinateHom k j)) (sqBasisElement k i)) =
      if j = i then c j else 0 := by
  by_cases hji : j = i
  · subst j
    rw [sq_hom_basis]
    simp [sq_quotientFst_smul]
  · rw [sq_hom_basis]
    simp [hji, sq_quotientFst_smul]

private lemma sq_coordinate_linearIndependent (k : Type u) [Field k] :
    LinearIndependent k (sqCoordinateHom k) := by
  classical
  rw [linearIndependent_iff']
  intro s c hsum i hi
  have hval : ∑ j ∈ s, c j • sqCoordinateHom k j (sqBasisElement k i) = 0 := by
    simpa using congrArg
      (fun w : (sqShortComplex k).X₁ ⟶ sqResidue k => w (sqBasisElement k i)) hsum
  have hval' := congrArg (sqQuotientFst k) hval
  have hterm (j : ℕ) :
      sqQuotientFst k
        (c j • (ConcreteCategory.hom (sqCoordinateHom k j)) (sqBasisElement k i)) =
          if j = i then c j else 0 :=
    sq_quotientFst_coordinate_term k c i j
  have hsum' : ∑ j ∈ s, (if j = i then c j else 0) = 0 := by
    simpa only [map_sum, map_zero, hterm] using hval'
  simpa [Finset.sum_ite_irrel, hi] using hsum'

/-- The first self-Ext of the residue module is not finite over the ring. -/
theorem infinite_square_zero_ext_one_not_finite (k : Type u) [Field k] :
    ¬ Module.Finite (infiniteSquareZeroRing k)
        (ExtGroup (infiniteSquareZeroResidueModule k)
          (infiniteSquareZeroResidueModule k) 1) := by
  let A := infiniteSquareZeroRing k
  let M := infiniteSquareZeroResidueModule k
  intro hfin
  let : Module.Finite A (ExtGroup M M 1) := by
    simpa [A, M] using hfin
  let S : ShortComplex (ModuleCat A) := sqShortComplex k
  have hscalarH (a : A) (w : S.X₁ ⟶ M) :
      a • w = a.fst • w := sq_scalar_on_hom k a w
  let alpha : (S.X₁ ⟶ M) →ₗ[A] ExtGroup M M 1 := sqAlpha k
  have halpha : Function.Injective alpha := sq_alpha_injective k
  have hsurj : Function.Surjective alpha := sq_alpha_surjective k
  let ealpha : (S.X₁ ⟶ M) ≃ₗ[A] ExtGroup M M 1 :=
    LinearEquiv.ofBijective alpha ⟨halpha, hsurj⟩
  have hfiniteH : Module.Finite A (S.X₁ ⟶ M) := by
    exact Module.Finite.equiv ealpha.symm
  have hfiniteK : Module.Finite k (S.X₁ ⟶ M) := by
    let _ : Module.Finite A (S.X₁ ⟶ M) := hfiniteH
    exact finite_over_field_of_sq_scalar k (S.X₁ ⟶ M) hscalarH
  let v (n : ℕ) : S.X₁ ⟶ M := sqCoordinateHom k n
  have hvli : LinearIndependent k v := sq_coordinate_linearIndependent k
  let : Module.Finite k (S.X₁ ⟶ M) := hfiniteK
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
