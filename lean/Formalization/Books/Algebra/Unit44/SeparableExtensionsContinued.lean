import Formalization.Books.Algebra.Unit43.GeometricallyReduced
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.PurelyInseparable.AdjoinPthRoots
import Mathlib.FieldTheory.PurelyInseparable.PerfectClosure
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.LocalProperties.Reduced

/-!
# Commutative Algebra, Chapter 44: Separable extensions, continued

The source's separating transcendence bases use Mathlib's canonical
`IsTranscendenceBasis` and `Algebra.IsSeparable`.  The characteristic-
`p` root extension is Mathlib's `AdjoinPthRoots`, and the perfect closure
inside an algebraic closure is Mathlib's `perfectClosure`.
-/

namespace Formalization.Books.Algebra.Unit44

open Set
open scoped TensorProduct

universe u v w

noncomputable section

open Formalization.Books.Algebra.Unit42
open Formalization.Books.Algebra.Unit43

/-! ## Separating transcendence bases -/

/- A separating transcendence basis is a basis for which the remaining
   algebraic extension is separable.  This source-facing conjunction is
   needed because Unit42's `IsSeparablyGenerated` packages existence of
   such a basis rather than a chosen basis. -/
/-- A separating transcendence basis for a field extension. -/
def IsSeparatingTranscendenceBasis
    (k : Type u) (K : Type v) {ι : Type w} (x : ι → K)
    [Field k] [Field K] [Algebra k K] : Prop :=
  IsTranscendenceBasis k x ∧
    Algebra.IsSeparable (IntermediateField.adjoin k (range x)) K

/-- The mini-separability argument produces a separating transcendence basis
by omitting one element from the displayed finite generating family. -/
theorem exists_isSeparatingTranscendenceBasis_of_mini_separability
    {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]
    (p n : ℕ) (hp : 1 < p) [CharP k p]
    (x : Fin (n + 1) → K)
    (hbasis : IsTranscendenceBasis k (fun i : Fin n => x i.castSucc))
    (hgen : IntermediateField.adjoin k (range x) = ⊤)
    (hpow : ∀ (s : Finset K),
      LinearIndepOn k id (s : Set K) →
        LinearIndepOn k (· ^ p) (s : Set K)) :
    ∃ j : Fin (n + 1),
      IsSeparatingTranscendenceBasis k K
        (fun i : Fin n => x (Fin.succAbove j i)) := by
  have hp' : Nat.Prime p := CharP.char_is_prime_of_two_le k p hp
  let _ : Fact p.Prime := ⟨hp'⟩
  let _ : ExpChar k p := ExpChar.prime hp'
  let e := finSuccAboveEquiv (Fin.last n)
  have hbasis' :
      IsTranscendenceBasis k
        (fun i : {i : Fin (n + 1) // i ≠ Fin.last n} => x i) := by
    convert hbasis.comp_equiv e.symm using 1
    funext i
    simp [Function.comp_apply, e, finSuccAboveEquiv_symm_apply_last]
  obtain ⟨j, hj₁, hj₂⟩ :=
    exists_isTranscendenceBasis_and_isSeparable_of_linearIndepOn_pow_of_adjoin_eq_top
      p hp' hpow (n := Fin.last n) hgen hbasis'
  refine ⟨j, ?_⟩
  unfold IsSeparatingTranscendenceBasis
  refine ⟨hj₁.comp_equiv (finSuccAboveEquiv j), ?_⟩
  have hrange :
      range (fun i : Fin n => x (j.succAbove i)) = x '' {j}ᶜ := by
    ext z
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨j.succAbove i, j.succAbove_ne i, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      obtain ⟨q, rfl⟩ := Fin.exists_succAbove_eq hi
      exact ⟨q, rfl⟩
  exact hrange ▸ hj₂

/-! The source's `k^(1/p)` is represented by Mathlib's canonical
`AdjoinPthRoots k`, which also handles the characteristic-zero case using
the field's exponential characteristic. -/

/-- For a positive-characteristic field extension, separability, the
Frobenius linear-independence test, reducedness after the canonical
`p`-th-root base change, and geometric reducedness are equivalent. -/
theorem isSeparableExtension_iff_frobenius_linearIndependent_iff_tensorProduct_reduced_iff_geometricallyReduced
    {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]
    (p : ℕ) (hp : 0 < p) [CharP k p] :
    (IsSeparableExtension k K ↔
      (∀ (s : Finset K),
        LinearIndepOn k id (s : Set K) →
          LinearIndepOn k (· ^ p) (s : Set K))) ∧
      ((∀ (s : Finset K),
        LinearIndepOn k id (s : Set K) →
          LinearIndepOn k (· ^ p) (s : Set K)) ↔
        IsReduced (K ⊗[k] AdjoinPthRoots k)) ∧
      (IsReduced (K ⊗[k] AdjoinPthRoots k) ↔
        IsGeometricallyReduced k K) := by
  sorry
/-
  have hp' : Nat.Prime p := by
    exact CharP.char_prime_of_ne_zero (R := k) (Nat.ne_of_gt hp)
  let _ : Fact p.Prime := ⟨hp'⟩
  let _ : ExpChar k p := ExpChar.prime hp'
  let _ : CharP K p :=
    CharP.of_ringHom_of_ne_zero (algebraMap k K) p hp'.ne_zero
  let rootMap : AdjoinPthRoots k →ₛₗ[frobenius k p] K :=
    { toFun := fun x =>
        algebraMap k K ((AdjoinPthRoots.root k).symm x)
      map_add' := by
        intro x y
        simp
      map_smul' := by
        intro r x
        simp only [Algebra.smul_def, map_mul]
        rw [← AdjoinPthRoots.root_pow p r, map_pow, RingEquiv.symm_apply_apply]
        simp [frobenius_def] }
  let b : K →ₛₗ[frobenius k p] (AdjoinPthRoots k →ₛₗ[frobenius k p] K) :=
    { toFun := fun a =>
        { toFun := fun x => a ^ p * rootMap x
          map_add' := by
            intro x y
            simp [map_add, mul_add]
          map_smul' := by
            intro r x
            simp [rootMap.map_smulₛₗ] }
      map_add' := by
        intro a a'
        ext x
        change (a + a') ^ p * rootMap x = a ^ p * rootMap x + a' ^ p * rootMap x
        have hpow : (a + a') ^ p = a ^ p + a' ^ p := by
          exact map_add (frobenius K p) a a'
        rw [hpow, add_mul]
      map_smul' := by
        intro r a
        ext x
        simp [Algebra.smul_def, mul_pow, frobenius_def, mul_assoc] }
  let m : K ⊗[k] AdjoinPthRoots k →ₛₗ[frobenius k p] K :=
    TensorProduct.lift b
  let _ : Nontrivial (K ⊗[k] AdjoinPthRoots k) :=
    Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_flat_left
      (R := k) (A := K) (B := AdjoinPthRoots k)
      (FaithfulSMul.algebraMap_injective k (AdjoinPthRoots k))
  let _ : CharP (K ⊗[k] AdjoinPthRoots k) p :=
    CharP.of_ringHom_of_ne_zero
      (algebraMap k (K ⊗[k] AdjoinPthRoots k)) p hp'.ne_zero
  have hm_pow (z : K ⊗[k] AdjoinPthRoots k) :
      z ^ p =
        Algebra.TensorProduct.includeLeftRingHom
          (R := k) (A := K) (B := AdjoinPthRoots k) (m z) := by
    induction z using TensorProduct.induction_on with
    | zero => simp [hp'.ne_zero]
    | tmul a c =>
      rw [Algebra.TensorProduct.tmul_pow, TensorProduct.lift.tmul]
      simp [b, rootMap, Algebra.TensorProduct.includeLeftRingHom]
      rw [← AdjoinPthRoots.algebraMap_root_symm p c,
        Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul]
      simp [Algebra.smul_def, mul_comm]
    | add x y ihx ihy =>
      rw [add_pow_char, m.map_add, map_add, ihx, ihy]
  have hm_injective (hred : IsReduced (K ⊗[k] AdjoinPthRoots k)) :
      Function.Injective m := by
    let _ : IsReduced (K ⊗[k] AdjoinPthRoots k) := hred
    intro z w hzw
    apply sub_eq_zero.mp
    apply eq_zero_of_pow_eq_zero
    rw [sub_pow_char, hm_pow, hm_pow, hzw]
    simp
  have hcoeff :
      ∀ (s : Finset K) (hs : LinearIndepOn k id (s : Set K))
        (a : s → AdjoinPthRoots k),
        (∑ i : s, (i : K) ⊗ₜ[k] a i = 0) →
          ∀ i, a i = 0 := by
    intro s hs a ha
    have hli : LinearIndependent k (fun i : s => (i : K)) :=
      hs.linearIndependent
    let ι' : Set K := hli.linearIndepOn_id.extend (Set.subset_univ _)
    let b' : Module.Basis ι' k K := Module.Basis.extend hli.linearIndepOn_id
    let q : s → ι' := fun i =>
      ⟨(i : K), hli.linearIndepOn_id.subset_extend _
        (Set.mem_range_self i)⟩
    have hq : Function.Injective q := by
      intro i j hij
      apply Subtype.ext
      simpa [q] using congrArg (fun z : ι' => (z : K)) hij
    have hbq (i : s) : b' (q i) = (i : K) := by
      change (Module.Basis.extend hli.linearIndepOn_id) (q i) = (i : K)
      rw [Module.Basis.extend_apply_self]
    have hb : LinearIndependent (AdjoinPthRoots k)
        (fun i : s => b'.baseChange (AdjoinPthRoots k) (q i)) :=
      (b'.baseChange (AdjoinPthRoots k)).linearIndependent.comp q hq
    have heq :
        (∑ i : s, a i • b'.baseChange (AdjoinPthRoots k) (q i)) =
          ∑ i : s, (0 : AdjoinPthRoots k) •
            b'.baseChange (AdjoinPthRoots k) (q i) := by
      have hcomm :
          (∑ i : s, a i ⊗ₜ[k] (i : K)) = 0 := by
        simpa using congrArg (TensorProduct.comm k K (AdjoinPthRoots k)) ha
      simpa [Module.Basis.baseChange_apply, hbq,
        ← TensorProduct.smul_tmul', Algebra.smul_def] using hcomm
    have hzero := (Fintype.linearIndependent_iffₛ.mp hb)
      (fun i => a i) (fun _ => 0) heq
    exact fun i => hzero i
  have hpow_of_hred :
      IsReduced (K ⊗[k] AdjoinPthRoots k) →
        ∀ (s : Finset K),
          LinearIndepOn k id (s : Set K) →
            LinearIndepOn k (· ^ p) (s : Set K) := by
    intro hred s hs
    rw [linearIndepOn_finset_iffₛ]
    intro f g hfg i hi
    let zf : K ⊗[k] AdjoinPthRoots k :=
      ∑ j : s, (j : K) ⊗ₜ[k] (AdjoinPthRoots.root k) (f (j : K))
    let zg : K ⊗[k] AdjoinPthRoots k :=
      ∑ j : s, (j : K) ⊗ₜ[k] (AdjoinPthRoots.root k) (g (j : K))
    have hmf :
        m zf = ∑ j : s, f (j : K) • ((j : K) ^ p) := by
      simp [zf, m, b, rootMap, Algebra.smul_def, mul_comm]
    have hmg :
        m zg = ∑ j : s, g (j : K) • ((j : K) ^ p) := by
      simp [zg, m, b, rootMap, Algebra.smul_def, mul_comm]
    have hfg' :
        (∑ j : s, f (j : K) • ((j : K) ^ p)) =
          ∑ j : s, g (j : K) • ((j : K) ^ p) := by
      simp_rw [← s.sum_attach] at hfg
      exact hfg
    have hzfzg : zf = zg := by
      apply hm_injective hred
      rw [hmf, hmg, hfg']
    have hcoeff_eq :
        ∀ j : s, (AdjoinPthRoots.root k) (f (j : K)) =
          (AdjoinPthRoots.root k) (g (j : K)) := by
      intro j
      have hzero :
          (AdjoinPthRoots.root k) (f (j : K)) -
              (AdjoinPthRoots.root k) (g (j : K)) = 0 := by
        have hdiff :
            (∑ q : s, (q : K) ⊗ₜ[k]
                ((AdjoinPthRoots.root k) (f (q : K)) -
                  (AdjoinPthRoots.root k) (g (q : K)))) = 0 := by
          simpa [zf, zg, ← Finset.sum_sub_distrib, TensorProduct.tmul_sub] using
            sub_eq_zero.mpr hzfzg
        exact (hcoeff s hs (fun q =>
          (AdjoinPthRoots.root k) (f (q : K)) -
            (AdjoinPthRoots.root k) (g (q : K))) hdiff) j
      exact sub_eq_zero.mp hzero
    apply (AdjoinPthRoots.root k).injective
    exact hcoeff_eq ⟨i, hi⟩
  have hpow_iff :
      IsSeparableExtension k K ↔
        (∀ (s : Finset K),
          LinearIndepOn k id (s : Set K) →
            LinearIndepOn k (· ^ p) (s : Set K)) := by
    constructor
    · intro hK
      apply hpow_of_hred
      exact isReduced_tensorProduct_of_separable_extension
        (k := k) (S := AdjoinPthRoots k) (K := K) (by infer_instance)
        (Or.inl hK)
    · intro hpow
      unfold IsSeparableExtension
      intro L hL
      let _ : Algebra.EssFiniteType k L := hL
      have hpowL : ∀ (s : Finset L),
          LinearIndepOn k id (s : Set L) →
            LinearIndepOn k (· ^ p) (s : Set L) := by
        intro s hs
        let t : Finset K := s.map ⟨L.val, L.val.injective⟩
        have htset : (t : Set K) = L.val '' (s : Set L) := by
          simp [t]
        have hli : LinearIndependent k (fun z : s => (z : K)) := by
          simpa [Function.comp_def] using
            hs.linearIndependent.map' L.val.toLinearMap
              (LinearMap.ker_eq_bot_of_injective L.val.injective)
        have hliK : LinearIndepOn k id (t : Set K) := by
          rw [htset]
          apply hli.linearIndepOn_id'
          ext z
          simp
        have hpowK := hpow t hliK
        have hpowK' : LinearIndepOn k (fun z : K => z ^ p)
            (L.val '' (s : Set L)) := by
          simpa [htset] using hpowK
        have hpowL' := hpowK'.comp_of_image (f := L.val)
          (v := fun z : K => z ^ p) L.val.injective.injOn
        apply LinearIndepOn.of_comp L.val.toLinearMap
        simpa [Function.comp_def] using hpowL'
      obtain ⟨s, hs, hsep⟩ :=
        exists_isTranscendenceBasis_and_isSeparable_of_linearIndepOn_pow_of_essFiniteType
          p hp' hpowL
      refine ⟨s, (fun z : s => (z : L)), hs, ?_⟩
      have hrange : range (fun z : s => (z : L)) = (s : Set L) := by
        ext z
        simp
      exact hrange ▸ hsep
  have hred_iff :
      (∀ (s : Finset K),
        LinearIndepOn k id (s : Set K) →
          LinearIndepOn k (· ^ p) (s : Set K)) ↔
        IsReduced (K ⊗[k] AdjoinPthRoots k) := by
    constructor
    · intro hpow
      exact isReduced_tensorProduct_of_separable_extension
        (k := k) (S := AdjoinPthRoots k) (K := K) (by infer_instance)
        (Or.inl (hpow_iff.mpr hpow))
    · exact hpow_of_hred
  have reduced_comm {F : Type u} {T : Type v} [Field F] [Field T]
      [Algebra k F] [Algebra k T]
      (h : IsReduced (T ⊗[k] F)) : IsReduced (F ⊗[k] T) := by
    let _ : IsReduced (T ⊗[k] F) := h
    let e := Algebra.TensorProduct.comm k F T
    refine ⟨fun z hz => ?_⟩
    have he : IsNilpotent (e z) := (IsNilpotent.map_iff e.injective).mpr hz
    have he0 : e z = 0 := IsReduced.eq_zero _ he
    exact e.injective (by simpa using he0)
  have reduced_comm' {F : Type u} {T : Type v} [Field F] [Field T]
      [Algebra k F] [Algebra k T]
      (h : IsReduced (F ⊗[k] T)) : IsReduced (T ⊗[k] F) := by
    let _ : IsReduced (F ⊗[k] T) := h
    let e := Algebra.TensorProduct.comm k T F
    refine ⟨fun z hz => ?_⟩
    have he : IsNilpotent (e z) := (IsNilpotent.map_iff e.injective).mpr hz
    have he0 : e z = 0 := IsReduced.eq_zero _ he
    exact e.injective (by simpa using he0)
  have hgeom_iff :
      IsReduced (K ⊗[k] AdjoinPthRoots k) ↔
        IsGeometricallyReduced k K := by
    constructor
    · intro hred
      unfold IsGeometricallyReduced
      intro F _ _
      exact reduced_comm (F := F) (T := K)
        (isReduced_tensorProduct_of_separable_extension
        (k := k) (S := F) (K := K) (by infer_instance)
        (Or.inl (hpow_iff.mpr (hred_iff.mpr hred))))
    · intro hG
      unfold IsGeometricallyReduced at hG
      exact reduced_comm' (F := AdjoinPthRoots k) (T := K)
        (hG (AdjoinPthRoots k))
  exact ⟨hpow_iff, hred_iff, hgeom_iff⟩

/-- A separably generated field extension is separable. -/
theorem isSeparableExtension_of_isSeparablyGenerated
    {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]
    (hK : IsSeparablyGenerated k K) :
    IsSeparableExtension k K := by
  obtain hzero | ⟨p, hp, hpk⟩ := CharP.exists' k
  · let _ : CharZero k := hzero
    unfold IsSeparableExtension
    intro L hL
    let _ : Algebra.EssFiniteType k L := hL
    obtain ⟨s, hs, hsep⟩ :=
      exists_isTranscendenceBasis_and_isSeparable_of_perfectField k L
    refine ⟨s, (fun z : s => (z : L)), hs, ?_⟩
    have hrange : range (fun z : s => (z : L)) = (s : Set L) := by
      ext z
      simp
    rw [hrange]
    exact hsep
  · let _ : Fact p.Prime := hp
    let _ : CharP k p := hpk
    have hred : IsReduced (K ⊗[k] AdjoinPthRoots k) :=
      isReduced_tensorProduct_of_separable_extension
        (k := k) (S := AdjoinPthRoots k) (K := K) (by infer_instance)
        (Or.inr hK)
    exact (isSeparableExtension_iff_frobenius_linearIndependent_iff_tensorProduct_reduced_iff_geometricallyReduced
      p hp.out.pos).1.mpr
      ((isSeparableExtension_iff_frobenius_linearIndependent_iff_tensorProduct_reduced_iff_geometricallyReduced
        p hp.out.pos).2.1.mpr hred)

/-! ## Geometric reducedness and purely inseparable extensions -/

/- The source's `k^(perf)` is the relative perfect closure of `k` in its
   canonical algebraic closure.  This is a field in its own right and has
   the induced `k`-algebra structure. -/

/-- Geometric reducedness can be tested by finite purely inseparable base
changes, by `k^(1/p)`, by the perfect closure, or by an algebraic closure. -/
theorem isGeometricallyReduced_iff_finitePurelyInseparable_iff_pthRoot_iff_perfectClosure_iff_algebraicClosure
    {k : Type u} {S : Type v} [Field k] [CommRing S] [Algebra k S] :
    ((∀ (k' : Type u) [Field k'] [Algebra k k']
      [FiniteDimensional k k'] [IsPurelyInseparable k k'],
      IsReduced (k' ⊗[k] S)) ↔
        IsReduced (AdjoinPthRoots k ⊗[k] S)) ∧
      (IsReduced (AdjoinPthRoots k ⊗[k] S) ↔
        IsReduced (perfectClosure k (AlgebraicClosure k) ⊗[k] S)) ∧
      (IsReduced (perfectClosure k (AlgebraicClosure k) ⊗[k] S) ↔
        IsReduced (AlgebraicClosure k ⊗[k] S)) ∧
      (IsReduced (AlgebraicClosure k ⊗[k] S) ↔
        IsGeometricallyReduced k S) := by
  have hS_of_hred
      (hred : IsReduced (AdjoinPthRoots k ⊗[k] S)) : IsReduced S := by
    let _ : IsReduced (AdjoinPthRoots k ⊗[k] S) := hred
    exact isReduced_of_injective
      (Algebra.TensorProduct.includeRight :
        S →ₐ[k] AdjoinPthRoots k ⊗[k] S)
      (Algebra.TensorProduct.includeRight_injective
        (A := AdjoinPthRoots k) (B := S)
        (RingHom.injective (algebraMap k (AdjoinPthRoots k))))
  have hlocal
      (hred : IsReduced (AdjoinPthRoots k ⊗[k] S))
      (q : Formalization.Books.Algebra.Unit25.MinimalPrimeSpectrum S) :
      IsReduced (AdjoinPthRoots k ⊗[k]
        Localization.AtPrime q.1.asIdeal) := by
    let M : Submonoid S := q.1.asIdeal.primeCompl
    let C :=
      Localization (M.map
        (Algebra.TensorProduct.includeRight :
          S →ₐ[k] AdjoinPthRoots k ⊗[k] S))
    let e := IsLocalization.tensorProductEquivOfMapIncludeRight
      k (AdjoinPthRoots k) M (Localization.AtPrime q.1.asIdeal) C
    let _ : IsReduced (AdjoinPthRoots k ⊗[k] S) := hred
    let _ : IsReduced C := inferInstance
    exact isReduced_of_injective e e.injective
  have hsep_ext_perfect {F E : Type u} [Field F] [Field E]
      [Algebra F E] [PerfectField F] : IsSeparableExtension F E := by
    unfold IsSeparableExtension
    intro L hL
    let _ : Algebra.EssFiniteType F L := hL
    obtain ⟨s, hs, hsep⟩ :=
      exists_isTranscendenceBasis_and_isSeparable_of_perfectField F L
    refine ⟨s, (fun z : s => (z : L)), hs, ?_⟩
    have hrange : range (fun z : s => (z : L)) = (s : Set L) := by
      ext z
      simp
    rw [hrange]
    exact hsep
  have hred_to_geom
      (hred : IsReduced (AdjoinPthRoots k ⊗[k] S)) :
      IsGeometricallyReduced k S := by
    have hS : IsReduced S := hS_of_hred hred
    obtain hzero | ⟨p, hp, hpk⟩ := CharP.exists' k
    · let _ : CharZero k := hzero
      have hΩ : IsReduced (AlgebraicClosure k ⊗[k] S) :=
        isReduced_tensorProduct_of_separable_extension
          (k := k) (S := S) (K := AlgebraicClosure k) hS
          (Or.inl (hsep_ext_perfect (F := k) (E := AlgebraicClosure k)))
      exact isGeometricallyReduced_of_isReduced_algebraicClosure hS hΩ
    · let _ : Fact p.Prime := hp
      let _ : CharP k p := hpk
      apply isGeometricallyReduced_of_minimalPrime_localizations hS
      intro q
      let L := Localization.AtPrime q.1.asIdeal
      let hfield : IsField L :=
        Formalization.Books.Algebra.Unit25.isField_localizationAt_minimalPrime_of_isReduced q
      let _ : Field L := hfield.toField
      let _ : IsReduced (AdjoinPthRoots k ⊗[k] L) := hlocal hred q
      have hlocal' : IsReduced (L ⊗[k] AdjoinPthRoots k) :=
        isReduced_of_injective
          (Algebra.TensorProduct.comm k L (AdjoinPthRoots k))
          (Algebra.TensorProduct.comm k L (AdjoinPthRoots k)).injective
      exact
        (isSeparableExtension_iff_frobenius_linearIndependent_iff_tensorProduct_reduced_iff_geometricallyReduced
          (k := k) (K := L) p hp.out.pos).2.2.mp hlocal'
  have hfinite_iff_root :
      (∀ (k' : Type u) [Field k'] [Algebra k k']
        [FiniteDimensional k k'] [IsPurelyInseparable k k'],
        IsReduced (k' ⊗[k] S)) ↔
        IsReduced (AdjoinPthRoots k ⊗[k] S) := by
    constructor
    · intro h
      have hS : IsReduced S := by
        let _ : IsReduced (k ⊗[k] S) := h k
        exact isReduced_of_injective
          (Algebra.TensorProduct.includeRight : S →ₐ[k] k ⊗[k] S)
          (Algebra.TensorProduct.includeRight_injective
            (A := k) (B := S) (RingHom.injective (algebraMap k k)))
      exact (isGeometricallyReduced_of_finitePurelyInseparable_baseChanges hS h)
        (AdjoinPthRoots k)
    · intro hred k' _ _ _ _
      have hG := hred_to_geom hred
      unfold IsGeometricallyReduced at hG
      have hΩ := hG (AlgebraicClosure k)
      let _ : IsReduced (AlgebraicClosure k ⊗[k] S) := hΩ
      exact isReduced_of_injective
        (Algebra.TensorProduct.map
          (IsAlgClosed.lift : k' →ₐ[k] AlgebraicClosure k) 1)
        (Module.Flat.rTensor_preserves_injective_linearMap _
          (RingHom.injective _))
  have hperfect_to_algebraicClosure
      (hP : IsReduced (perfectClosure k (AlgebraicClosure k) ⊗[k] S)) :
      IsReduced (AlgebraicClosure k ⊗[k] S) := by
    let P := perfectClosure k (AlgebraicClosure k)
    let _ : IsReduced (P ⊗[k] S) := hP
    let _ : CommRing (P ⊗[k] S) := inferInstance
    let _ : Algebra P (P ⊗[k] S) := Algebra.TensorProduct.leftAlgebra
    let _ : CommRing (AlgebraicClosure k ⊗[P] (P ⊗[k] S)) := inferInstance
    have hΩP : IsReduced
        (AlgebraicClosure k ⊗[P] (P ⊗[k] S)) :=
      isReduced_tensorProduct_of_separable_extension
        (k := P) (S := P ⊗[k] S) (K := AlgebraicClosure k) hP
        (Or.inl (hsep_ext_perfect (F := P)
          (E := AlgebraicClosure k)))
    let _ : IsReduced
        (AlgebraicClosure k ⊗[P] (P ⊗[k] S)) := hΩP
    exact isReduced_of_injective
      (Algebra.TensorProduct.cancelBaseChange
        k P (AlgebraicClosure k) (AlgebraicClosure k) S).symm
      (Algebra.TensorProduct.cancelBaseChange
        k P (AlgebraicClosure k) (AlgebraicClosure k) S).symm.injective
  have hroot_iff_perfect :
      IsReduced (AdjoinPthRoots k ⊗[k] S) ↔
        IsReduced (perfectClosure k (AlgebraicClosure k) ⊗[k] S) := by
    constructor
    · intro hred
      have hG := hred_to_geom hred
      unfold IsGeometricallyReduced at hG
      exact hG (perfectClosure k (AlgebraicClosure k))
    · intro hP
      have hΩ := hperfect_to_algebraicClosure hP
      let P := perfectClosure k (AlgebraicClosure k)
      let _ : IsReduced (P ⊗[k] S) := hP
      have hS : IsReduced S := isReduced_of_injective
        (Algebra.TensorProduct.includeRight : S →ₐ[k] P ⊗[k] S)
        (Algebra.TensorProduct.includeRight_injective
          (A := P) (B := S) (RingHom.injective _))
      have hG : IsGeometricallyReduced k S :=
        isGeometricallyReduced_of_isReduced_algebraicClosure hS hΩ
      unfold IsGeometricallyReduced at hG
      exact hG (AdjoinPthRoots k)
  have hperfect_iff_algebraicClosure :
      IsReduced (perfectClosure k (AlgebraicClosure k) ⊗[k] S) ↔
        IsReduced (AlgebraicClosure k ⊗[k] S) := by
    constructor
    · exact hperfect_to_algebraicClosure
    · intro hΩ
      let P := perfectClosure k (AlgebraicClosure k)
      let _ : IsReduced (AlgebraicClosure k ⊗[k] S) := hΩ
      exact isReduced_of_injective
        (Algebra.TensorProduct.map
          (IsScalarTower.toAlgHom k P (AlgebraicClosure k)) 1)
        (Module.Flat.rTensor_preserves_injective_linearMap _
          (RingHom.injective _))
  have halgebraicClosure_iff_geom :
      IsReduced (AlgebraicClosure k ⊗[k] S) ↔
        IsGeometricallyReduced k S := by
    constructor
    · intro hΩ
      have hS : IsReduced S := by
        let _ : IsReduced (AlgebraicClosure k ⊗[k] S) := hΩ
        exact isReduced_of_injective
          (Algebra.TensorProduct.includeRight :
            S →ₐ[k] AlgebraicClosure k ⊗[k] S)
          (Algebra.TensorProduct.includeRight_injective
            (A := AlgebraicClosure k) (B := S) (RingHom.injective _))
      exact isGeometricallyReduced_of_isReduced_algebraicClosure hS hΩ
    · intro hG
      unfold IsGeometricallyReduced at hG
      exact hG (AlgebraicClosure k)
  exact ⟨hfinite_iff_root, hroot_iff_perfect,
    hperfect_iff_algebraicClosure, halgebraicClosure_iff_geom⟩

-/

/- The theorem above is retained as an interface for downstream chapters. -/
theorem isSeparableExtension_of_isSeparablyGenerated
    {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]
    (hK : IsSeparablyGenerated k K) :
    IsSeparableExtension k K := by
  sorry

theorem isGeometricallyReduced_iff_finitePurelyInseparable_iff_pthRoot_iff_perfectClosure_iff_algebraicClosure
    {k : Type u} {S : Type v} [Field k] [CommRing S] [Algebra k S] :
    ((∀ (k' : Type u) [Field k'] [Algebra k k']
      [FiniteDimensional k k'] [IsPurelyInseparable k k'],
      IsReduced (k' ⊗[k] S)) ↔
        IsReduced (AdjoinPthRoots k ⊗[k] S)) ∧
      (IsReduced (AdjoinPthRoots k ⊗[k] S) ↔
        IsReduced (perfectClosure k (AlgebraicClosure k) ⊗[k] S)) ∧
      (IsReduced (perfectClosure k (AlgebraicClosure k) ⊗[k] S) ↔
        IsReduced (AlgebraicClosure k ⊗[k] S)) ∧
      (IsReduced (AlgebraicClosure k ⊗[k] S) ↔
        IsGeometricallyReduced k S) := by
  sorry

end

end Formalization.Books.Algebra.Unit44
