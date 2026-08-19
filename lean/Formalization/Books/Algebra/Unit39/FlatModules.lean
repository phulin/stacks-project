import Mathlib.Algebra.Colimit.DirectLimit
import Mathlib.LinearAlgebra.TensorProduct.DirectLimit
import Mathlib.LinearAlgebra.TensorProduct.Prod
import Mathlib.RingTheory.Flat.EquationalCriterion
import Mathlib.RingTheory.Flat.Equalizer
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.Ideal.GoingDown
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Mathlib.RingTheory.RingHom.FaithfullyFlat
import Mathlib.RingTheory.Spectrum.Prime.RingHom
import Formalization.Books.Algebra.Unit12.TensorProducts

/-!
# Commutative Algebra, Chapter 39: Flat modules and flat ring maps

This file records the definitions and theorem interfaces from the flatness chapter.  The
canonical predicates are Mathlib's `Module.Flat`, `Module.FaithfullyFlat`, `RingHom.Flat`, and
`RingHom.FaithfullyFlat`; no parallel predicates are introduced here.
-/

namespace Formalization.Books.Algebra.Unit39

open Function
open scoped BigOperators TensorProduct

noncomputable section

universe u v w z

/- The introductory facts that tensor commutes with colimits and is right exact are already
   represented by `Formalization.Books.Algebra.Unit12.tensorProductColimitIso` and
   `Formalization.Books.Algebra.Unit12.tensorProduct_right_exact`, so no parallel declarations
   are introduced here. -/

section Definitions

theorem flat_module_iff_tensor_exact
    {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M] :
    Module.Flat R M ↔
      ∀ {N N' N'' : Type (max u v)} [AddCommGroup N] [AddCommGroup N'] [AddCommGroup N'']
        [Module R N] [Module R N'] [Module R N'']
        {f : N →ₗ[R] N'} {g : N' →ₗ[R] N''},
        Exact f g → Exact (f.lTensor M) (g.lTensor M) :=
  Module.Flat.iff_lTensor_exact

theorem faithfullyFlat_module_iff_tensor_exact
    {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M] :
    Module.FaithfullyFlat R M ↔
      ∀ {N : Type (max u v)} [AddCommGroup N] [Module R N]
        {N' : Type (max u v)} [AddCommGroup N'] [Module R N']
        {N'' : Type (max u v)} [AddCommGroup N''] [Module R N'']
        (f : N →ₗ[R] N') (g : N' →ₗ[R] N''),
        Exact f g ↔ Exact (f.lTensor M) (g.lTensor M) :=
  Module.FaithfullyFlat.iff_exact_iff_lTensor_exact R M

theorem ringHom_flat_iff_module_flat
    {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) :
    RingHom.Flat f ↔ @Module.Flat R S _ _ f.toModule := by
  change (letI : Algebra R S := f.toAlgebra; Module.Flat R S) ↔
    @Module.Flat R S _ _ f.toModule
  rfl

theorem ringHom_faithfullyFlat_iff_module_faithfullyFlat
    {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) :
    RingHom.FaithfullyFlat f ↔ @Module.FaithfullyFlat R S _ _ f.toModule := by
  change (letI : Algebra R S := f.toAlgebra; Module.FaithfullyFlat R S) ↔
    @Module.FaithfullyFlat R S _ _ f.toModule
  rfl

end Definitions

section Flatness

theorem flat_intersect_ideals
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] [Module.Flat R M]
    (I J : Ideal R) :
    (I • (⊤ : Submodule R M)) ⊓ (J • (⊤ : Submodule R M)) =
      (I ⊓ J) • (⊤ : Submodule R M) := by
  let g : R →ₗ[R] (R ⧸ I) × (R ⧸ J) := I.mkQ.prod J.mkQ
  have hker : LinearMap.ker g = I ⊓ J := by
    simp [g, LinearMap.ker_prod]
  apply le_antisymm
  · intro x hx
    rw [← Ideal.subtype_rTensor_range, ← hker]
    have hxI' : x ∈ LinearMap.range ((TensorProduct.lid R M).comp (I.subtype.rTensor M)) := by
      rw [Ideal.subtype_rTensor_range]
      exact hx.1
    obtain ⟨y, hy⟩ := hxI'
    have hy' : (TensorProduct.lid R M).symm x = (I.subtype.rTensor M) y := by
      rw [← hy]
      simp
    have hI : (I.mkQ.rTensor M) ((TensorProduct.lid R M).symm x) = 0 := by
      rw [hy', ← LinearMap.rTensor_comp_apply]
      rw [show I.mkQ.comp I.subtype = 0 by
        ext x
        exact Ideal.Quotient.eq_zero_iff_mem.mpr x.property]
      simp
    have hxJ' : x ∈ LinearMap.range ((TensorProduct.lid R M).comp (J.subtype.rTensor M)) := by
      rw [Ideal.subtype_rTensor_range]
      exact hx.2
    obtain ⟨z, hz⟩ := hxJ'
    have hz' : (TensorProduct.lid R M).symm x = (J.subtype.rTensor M) z := by
      rw [← hz]
      simp
    have hJ : (J.mkQ.rTensor M) ((TensorProduct.lid R M).symm x) = 0 := by
      rw [hz', ← LinearMap.rTensor_comp_apply]
      rw [show J.mkQ.comp J.subtype = 0 by
        ext x
        exact Ideal.Quotient.eq_zero_iff_mem.mpr x.property]
      simp
    have hprod :
        (TensorProduct.prodLeft R R (R ⧸ I) (R ⧸ J) M).toLinearMap.comp (g.rTensor M) =
          (I.mkQ.rTensor M).prod (J.mkQ.rTensor M) := by
      apply LinearMap.ext
      intro t
      induction t using TensorProduct.induction_on with
      | zero => rfl
      | add x y ihx ihy =>
          rw [map_add, map_add, ihx, ihy]
      | tmul r m => simp [g]
    have hgzero : (g.rTensor M) ((TensorProduct.lid R M).symm x) = 0 := by
      apply (TensorProduct.prodLeft R R (R ⧸ I) (R ⧸ J) M).injective
      simp only [map_zero]
      change (TensorProduct.prodLeft R R (R ⧸ I) (R ⧸ J) M).toLinearMap
        ((g.rTensor M) ((TensorProduct.lid R M).symm x)) = 0
      rw [← LinearMap.comp_apply, hprod]
      exact Prod.ext hI hJ
    have hex : Function.Exact ((LinearMap.ker g).subtype.rTensor M) (g.rTensor M) :=
      Module.Flat.rTensor_exact (M := M) (LinearMap.exact_subtype_ker_map g)
    have hxrange : (TensorProduct.lid R M).symm x ∈
        LinearMap.range ((LinearMap.ker g).subtype.rTensor M) := by
      rw [← hex.linearMap_ker_eq]
      exact hgzero
    obtain ⟨w, hw⟩ := hxrange
    refine ⟨w, ?_⟩
    change (TensorProduct.lid R M) ((LinearMap.ker g).subtype.rTensor M w) = x
    rw [hw]
    exact (TensorProduct.lid R M).apply_symm_apply x
  · exact le_inf (Submodule.smul_mono inf_le_left le_rfl)
      (Submodule.smul_mono inf_le_right le_rfl)

theorem directLimit_flat
    {R : Type u} [CommRing R] {ι : Type v} [Preorder ι] [Nonempty ι]
    [IsDirectedOrder ι] {G : ι → Type w} [∀ i, AddCommGroup (G i)] [∀ i, Module R (G i)]
    (f : ∀ i j, i ≤ j → G i →ₗ[R] G j)
    [DirectedSystem G (f · · ·)]
    (hflat : ∀ i, Module.Flat R (G i)) :
    Module.Flat R (DirectLimit G f) := by
  classical
  rw [Module.Flat.iff_rTensor_injective']
  intro I
  let q : ∀ i, (I ⊗[R] G i) →ₗ[R] (R ⊗[R] G i) :=
    fun i => I.subtype.rTensor (G i)
  have hq : ∀ i j (h : i ≤ j),
      (q j).comp (LinearMap.lTensor I (f i j h)) =
        (LinearMap.lTensor R (f i j h)).comp (q i) := by
    intro i j h
    apply LinearMap.ext
    intro x
    induction x using TensorProduct.induction_on with
    | zero => rfl
    | add x y ihx ihy => rw [map_add, map_add, ihx, ihy]
    | tmul a x => simp [q]
  let Q : Module.DirectLimit (fun i => I ⊗[R] G i)
      (fun i j h => LinearMap.lTensor I (f i j h)) →ₗ[R]
      Module.DirectLimit (fun i => R ⊗[R] G i)
        (fun i j h => LinearMap.lTensor R (f i j h)) :=
    Module.DirectLimit.map q hq
  have hQ : Function.Injective Q := by
    intro x y hxy
    have hzero : Q (x - y) = 0 := by
      rw [map_sub, sub_eq_zero.mpr hxy]
    obtain ⟨i, t, ht⟩ := Module.DirectLimit.exists_of (x - y)
    have hzero' : Q (Module.DirectLimit.of R ι _ _ i t) = 0 := by
      rw [ht]
      exact hzero
    have hqzero :
        Module.DirectLimit.of R ι (fun i => R ⊗[R] G i)
          (fun i j h => LinearMap.lTensor R (f i j h)) i (q i t) = 0 := by
      simpa [Q] using hzero'
    obtain ⟨j, hij, htrans⟩ :=
      Module.DirectLimit.of.zero_exact hqzero
    have hqtrans : q j ((LinearMap.lTensor I (f i j hij)) t) = 0 := by
      rw [show q j ((LinearMap.lTensor I (f i j hij)) t) =
          (LinearMap.lTensor R (f i j hij)) (q i t) by
            exact LinearMap.congr_fun (hq i j hij) t]
      exact htrans
    have htzero : (LinearMap.lTensor I (f i j hij)) t = 0 :=
      ((Module.Flat.iff_rTensor_injective'.mp (hflat j) I) hqtrans)
    have hsourcezero :
        Module.DirectLimit.of R ι (fun i => I ⊗[R] G i)
          (fun i j h => LinearMap.lTensor I (f i j h)) i t = 0 := by
      rw [← Module.DirectLimit.of_f (R := R) (ι := ι)
        (G := fun i => I ⊗[R] G i)
        (f := fun i j h => LinearMap.lTensor I (f i j h))
        (i := i) (j := j) (hij := hij), htzero, map_zero]
    have hsub : x - y = 0 := by
      rw [← ht, hsourcezero]
    exact sub_eq_zero.mp hsub
  let e : Module.DirectLimit G f ≃ₗ[R] DirectLimit G f :=
    Module.DirectLimit.linearEquiv G f
  let eI : I ⊗[R] Module.DirectLimit G f ≃ₗ[R]
      Module.DirectLimit (fun i => I ⊗[R] G i)
        (fun i j h => LinearMap.lTensor I (f i j h)) :=
    TensorProduct.directLimitRight f I
  let eR : R ⊗[R] Module.DirectLimit G f ≃ₗ[R]
      Module.DirectLimit (fun i => R ⊗[R] G i)
        (fun i j h => LinearMap.lTensor R (f i j h)) :=
    TensorProduct.directLimitRight f R
  have hcomm :
      Q.comp eI.toLinearMap =
        eR.toLinearMap.comp (I.subtype.rTensor (Module.DirectLimit G f)) := by
    apply LinearMap.ext
    intro x
    induction x using TensorProduct.induction_on with
    | zero => rfl
    | add x y ihx ihy => rw [map_add, map_add, ihx, ihy]
    | tmul a x =>
        induction x using Module.DirectLimit.induction_on with
        | ih i x => simp [Q, eI, eR, q]
  have hD : Function.Injective (I.subtype.rTensor (Module.DirectLimit G f)) := by
    intro x y hxy
    apply eI.injective
    apply hQ
    change (Q.comp eI.toLinearMap) x = (Q.comp eI.toLinearMap) y
    rw [hcomm]
    simpa only [LinearMap.comp_apply] using congrArg (fun z => eR.toLinearMap z) hxy
  let uI := e.symm.toLinearMap.lTensor I
  let uR := e.symm.toLinearMap.lTensor R
  have huI : Function.Injective uI := by
    have hleft : (e.toLinearMap.lTensor I).comp uI = LinearMap.id := by
      apply LinearMap.ext
      intro x
      induction x using TensorProduct.induction_on with
      | zero => rfl
      | add x y ihx ihy => rw [map_add, map_add, ihx, ihy]
      | tmul a x => simp [uI, e]
    intro x y hxy
    have h' := congrArg (fun z => (e.toLinearMap.lTensor I) z) hxy
    change ((e.toLinearMap.lTensor I).comp uI) x =
      ((e.toLinearMap.lTensor I).comp uI) y at h'
    rw [hleft, LinearMap.id_apply] at h'
    exact h'
  have hucomm :
      uR.comp (I.subtype.rTensor (DirectLimit G f)) =
        (I.subtype.rTensor (Module.DirectLimit G f)).comp uI := by
    apply LinearMap.ext
    intro x
    induction x using TensorProduct.induction_on with
    | zero => rfl
    | add x y ihx ihy => rw [map_add, map_add, ihx, ihy]
    | tmul a x => simp [uI, uR, e]
  exact fun x y hxy => by
    apply huI
    apply hD
    have h' := congrArg (fun z => uR z) hxy
    change (uR.comp (I.subtype.rTensor (DirectLimit G f))) x =
      (uR.comp (I.subtype.rTensor (DirectLimit G f))) y at h'
    rw [hucomm, LinearMap.comp_apply] at h'
    exact h'

theorem module_flat_trans
    {R S M : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
    [Module.Flat R S] [Module.Flat S M] : Module.Flat R M :=
  Module.Flat.trans R S M

theorem module_faithfullyFlat_trans
    {R S M : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
    [Module.FaithfullyFlat R S] [Module.FaithfullyFlat S M] :
    Module.FaithfullyFlat R M :=
  Module.FaithfullyFlat.trans R S M

theorem ringHom_flat_comp
    {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    {f : R →+* S} {g : S →+* T} (hf : RingHom.Flat f) (hg : RingHom.Flat g) :
    RingHom.Flat (g.comp f) :=
  RingHom.Flat.comp hf hg

theorem ringHom_faithfullyFlat_comp
    {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    {f : R →+* S} {g : S →+* T}
    (hf : RingHom.FaithfullyFlat f) (hg : RingHom.FaithfullyFlat g) :
    RingHom.FaithfullyFlat (g.comp f) := by
  algebraize [f, g, g.comp f]
  exact Module.FaithfullyFlat.trans R S T

theorem flat_criteria
    {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M] :
    List.TFAE [
      Module.Flat R M,
      ∀ {N N' : Type (max u v)} [AddCommGroup N] [AddCommGroup N']
        [Module R N] [Module R N'] (f : N →ₗ[R] N'),
        Injective f → Injective (f.rTensor M),
      ∀ (I : Ideal R), Injective (I.subtype.rTensor M),
      ∀ (I : Ideal R), I.FG → Injective (I.subtype.rTensor M)] := by
  tfae_have 1 ↔ 2 := Module.Flat.iff_rTensor_preserves_injective_linearMap
  tfae_have 1 ↔ 3 := Module.Flat.iff_rTensor_injective'
  tfae_have 1 ↔ 4 := Module.Flat.iff_rTensor_injective
  tfae_finish

end Flatness

section ColimitsOfRings

theorem directLimit_ring_flat
    {ι : Type u} [Preorder ι] [Nonempty ι] [IsDirectedOrder ι]
    {A : ι → Type v} [∀ i, CommRing (A i)]
    (f : ∀ i j, i ≤ j → A i →+* A j)
    [DirectedSystem A (f · · ·)]
    {M : Type w} [AddCommGroup M] [Module (DirectLimit A f) M]
    (hflat : ∀ i,
      letI : Module (A i) M := Module.compHom M (DirectLimit.Ring.of A f i)
      Module.Flat (A i) M) :
    Module.Flat (DirectLimit A f) M := by
  classical
  apply Module.Flat.of_forall_isTrivialRelation
  intro l c x hcx
  have hrep : ∀ z : DirectLimit A f, ∃ i a, DirectLimit.Ring.of A f i a = z := by
    intro z
    induction z using DirectLimit.induction with
    | _ i a => exact ⟨i, a, rfl⟩
  choose i ci hci using fun n => hrep (c n)
  obtain ⟨j, hj⟩ := Finset.exists_le (Finset.univ.image i)
  let _ : Module (A j) M := Module.compHom M (DirectLimit.Ring.of A f j)
  let cj : Fin l → A j := fun n =>
    f (i n) j (hj (i n) (Finset.mem_image.mpr ⟨n, Finset.mem_univ _, rfl⟩)) (ci n)
  have hc : ∀ n, DirectLimit.Ring.of A f j (cj n) = c n := by
    intro n
    change DirectLimit.Ring.of A f j
      (f (i n) j (hj (i n) (Finset.mem_image.mpr ⟨n, Finset.mem_univ _, rfl⟩)) (ci n)) = c n
    rw [DirectLimit.Ring.of_f, hci n]
  have hcj : ∑ n, cj n • x n = 0 := by
    calc
      ∑ n, cj n • x n =
          ∑ n, (DirectLimit.Ring.of A f (i n) (ci n)) • x n := by
            apply Finset.sum_congr rfl
            intro n hn
            change (DirectLimit.Ring.of A f j (cj n)) • x n =
              (DirectLimit.Ring.of A f (i n) (ci n)) • x n
            rw [hc n, hci n]
      _ = ∑ n, c n • x n := by
        apply Finset.sum_congr rfl
        intro n hn
        rw [hci n]
      _ = 0 := hcx
  obtain ⟨k, a, y, hay, ha⟩ :=
    (Module.Flat.iff_forall_isTrivialRelation.mp (hflat j)) hcj
  refine ⟨k, fun n m => DirectLimit.Ring.of A f j (a n m), y, ?_, ?_⟩
  · intro n
    rw [hay n]
    apply Finset.sum_congr rfl
    intro m hm
    rfl
  · intro m
    calc
      ∑ n, c n * DirectLimit.Ring.of A f j (a n m) =
          DirectLimit.Ring.of A f j (∑ n, cj n * a n m) := by
            simp [hc, map_sum, map_mul]
      _ = 0 := by
        have hz : ∑ n, cj n * a n m = 0 := ha m
        simpa [hz] using (map_zero (DirectLimit.Ring.of A f j))

theorem directLimit_ring_baseChange_flat
    {R : Type u} [CommRing R] {ι : Type v} [Preorder ι] [Nonempty ι]
    [IsDirectedOrder ι] {A : ι → Type w} [∀ i, CommRing (A i)]
    (f : ∀ i j, i ≤ j → A i →+* A j)
    [DirectedSystem A (f · · ·)]
    [∀ i, Algebra (A i) R]
    {M : ι → Type z} [∀ i, AddCommGroup (M i)] [∀ i, Module (A i) (M i)]
    (φ : ∀ i j (h : i ≤ j), M i →ₛₗ[f i j h] M j)
    (g : ∀ i j, i ≤ j → (R ⊗[A i] M i) →ₗ[R] (R ⊗[A j] M j))
    [DirectedSystem (fun i => R ⊗[A i] M i) (g · · ·)]
    (hcanonical : ∀ i j (h : i ≤ j) (r : R) (x : M i),
      g i j h (r ⊗ₜ[A i] x) = r ⊗ₜ[A j] φ i j h x)
    (hflat : ∀ i, Module.Flat (A i) (M i)) :
    Module.Flat R (DirectLimit (fun i => R ⊗[A i] M i) g) := by
  have hcan := hcanonical
  apply directLimit_flat g
  intro i
  let _ := hflat i
  infer_instance

end ColimitsOfRings

section BaseChangeAndDescent

theorem flat_base_change
    {R S M : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M] (hflat : Module.Flat R M) :
    Module.Flat S (S ⊗[R] M) := by
  infer_instance

theorem faithfullyFlat_base_change
    {R S M : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M] (hflat : Module.FaithfullyFlat R M) :
    Module.FaithfullyFlat S (S ⊗[R] M) := by
  infer_instance

theorem flatness_descends
    {R S M : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M] [Module.FaithfullyFlat R S] :
    Module.Flat R M ↔ Module.Flat S (S ⊗[R] M) := by
  exact (Module.Flat.iff_flat_tensorProduct (R := R) (M := M) S).symm

theorem flatness_descends_more_general
    {R S S' M : Type*} [CommRing R] [CommRing S] [CommRing S']
    [Algebra R S] [Algebra R S'] [Algebra S S'] [IsScalarTower R S S']
    [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
    (hflat : Module.Flat S S') :
    (Module.Flat R M → Module.Flat R (S' ⊗[S] M)) ∧
      (Module.FaithfullyFlat S S' →
        (Module.Flat R M ↔ Module.Flat R (S' ⊗[S] M))) := by
  have hforward : Module.Flat R M → Module.Flat R (S' ⊗[S] M) := by
    intro hM
    let _ : Module.Flat R M := hM
    let _ : Module.Flat S S' := hflat
    apply (Module.Flat.iff_lTensor_preserves_injective_linearMap).2
    intro N N' _ _ _ _ f hf
    have hfM : Function.Injective (f.lTensor M) :=
      Module.Flat.lTensor_preserves_injective_linearMap f hf
    let fS := TensorProduct.AlgebraTensorModule.lTensor S M f
    have hfS0 : Function.Injective (fS.restrictScalars R) := by
      simpa [fS] using hfM
    have hfS : Function.Injective ((fS.lTensor S').restrictScalars R) := by
      simpa using (Module.Flat.lTensor_preserves_injective_linearMap fS hfS0)
    let eN := TensorProduct.AlgebraTensorModule.assoc R S S' S' M N
    let eN' := TensorProduct.AlgebraTensorModule.assoc R S S' S' M N'
    have hcomm :
        (eN'.toLinearMap.restrictScalars R).comp (f.lTensor (S' ⊗[S] M)) =
          ((fS.lTensor S').restrictScalars R).comp (eN.toLinearMap.restrictScalars R) := by
      apply LinearMap.ext
      intro x
      induction x using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy => rw [map_add, map_add, hx, hy]
      | tmul a n =>
        induction a using TensorProduct.induction_on with
        | zero => simp
        | add a b ha hb =>
          rw [TensorProduct.add_tmul]
          simp only [LinearMap.comp_apply, map_add]
          have ha' :
              (eN'.toLinearMap.restrictScalars R)
                  ((f.lTensor (S' ⊗[S] M)) (a ⊗ₜ[R] n)) =
                ((fS.lTensor S').restrictScalars R)
                  ((eN.toLinearMap.restrictScalars R) (a ⊗ₜ[R] n)) := by
            simpa only [LinearMap.comp_apply] using ha
          have hb' :
              (eN'.toLinearMap.restrictScalars R)
                  ((f.lTensor (S' ⊗[S] M)) (b ⊗ₜ[R] n)) =
                ((fS.lTensor S').restrictScalars R)
                  ((eN.toLinearMap.restrictScalars R) (b ⊗ₜ[R] n)) := by
            simpa only [LinearMap.comp_apply] using hb
          rw [ha', hb']
        | tmul s m => simp [eN, eN', fS]
    intro x y hxy
    apply eN.injective
    apply hfS
    have hxy' := congrArg (fun z => eN' z) hxy
    change ((eN'.toLinearMap.restrictScalars R).comp
        (f.lTensor (S' ⊗[S] M))) x =
      ((eN'.toLinearMap.restrictScalars R).comp
        (f.lTensor (S' ⊗[S] M))) y at hxy'
    rw [hcomm, LinearMap.comp_apply] at hxy'
    exact hxy'
  refine ⟨hforward, ?_⟩
  intro hfaithful
  let _ : Module.FaithfullyFlat S S' := hfaithful
  constructor
  · exact hforward
  · intro hT
    let _ : Module.Flat R (S' ⊗[S] M) := hT
    apply (Module.Flat.iff_lTensor_preserves_injective_linearMap).2
    intro N N' _ _ _ _ f hf
    have hfT : Function.Injective (f.lTensor (S' ⊗[S] M)) :=
      Module.Flat.lTensor_preserves_injective_linearMap f hf
    let fS := TensorProduct.AlgebraTensorModule.lTensor S M f
    let eN := TensorProduct.AlgebraTensorModule.assoc R S S' S' M N
    let eN' := TensorProduct.AlgebraTensorModule.assoc R S S' S' M N'
    have hcomm :
        (eN'.toLinearMap.restrictScalars R).comp (f.lTensor (S' ⊗[S] M)) =
          ((fS.lTensor S').restrictScalars R).comp (eN.toLinearMap.restrictScalars R) := by
      apply LinearMap.ext
      intro x
      induction x using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy => rw [map_add, map_add, hx, hy]
      | tmul a n =>
        induction a using TensorProduct.induction_on with
        | zero => simp
        | add a b ha hb =>
          rw [TensorProduct.add_tmul]
          simp only [LinearMap.comp_apply, map_add]
          have ha' :
              (eN'.toLinearMap.restrictScalars R)
                  ((f.lTensor (S' ⊗[S] M)) (a ⊗ₜ[R] n)) =
                ((fS.lTensor S').restrictScalars R)
                  ((eN.toLinearMap.restrictScalars R) (a ⊗ₜ[R] n)) := by
            simpa only [LinearMap.comp_apply] using ha
          have hb' :
              (eN'.toLinearMap.restrictScalars R)
                  ((f.lTensor (S' ⊗[S] M)) (b ⊗ₜ[R] n)) =
                ((fS.lTensor S').restrictScalars R)
                  ((eN.toLinearMap.restrictScalars R) (b ⊗ₜ[R] n)) := by
            simpa only [LinearMap.comp_apply] using hb
          rw [ha', hb']
        | tmul s m => simp [eN, eN', fS]
    have hfbase : Function.Injective ((fS.lTensor S').restrictScalars R) := by
      intro x y hxy
      apply eN.symm.injective
      apply hfT
      apply eN'.injective
      have hxy' :
          (((fS.lTensor S').restrictScalars R).comp
              (eN.toLinearMap.restrictScalars R)) (eN.symm x) =
            (((fS.lTensor S').restrictScalars R).comp
              (eN.toLinearMap.restrictScalars R)) (eN.symm y) := by
        simp [LinearMap.comp_apply, hxy]
      rw [← hcomm] at hxy'
      exact hxy'
    have hfS : Function.Injective fS := by
      apply (Module.FaithfullyFlat.lTensor_injective_iff_injective S S' fS).mp
      exact hfbase
    simpa [fS] using hfS

theorem flat_permanence
    {R S M : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
    (hflat : Module.Flat R M) (hfaithful : Module.FaithfullyFlat S M) :
    Module.Flat R S := by
  let _ : Module.FaithfullyFlat S M := hfaithful
  rw [Module.Flat.iff_lTensor_preserves_injective_linearMap]
  intro N N' _ _ _ _ f hf
  have hfM : Function.Injective (f.lTensor M) :=
    Module.Flat.lTensor_preserves_injective_linearMap f hf
  let fS := TensorProduct.AlgebraTensorModule.lTensor S S f
  have hfS : Function.Injective fS := by
    apply (Module.FaithfullyFlat.lTensor_injective_iff_injective S M fS).mp
    let eN := TensorProduct.AlgebraTensorModule.cancelBaseChange R S S M N
    let eN' := TensorProduct.AlgebraTensorModule.cancelBaseChange R S S M N'
    have hcomm :
        (TensorProduct.AlgebraTensorModule.lTensor S M f).comp eN.toLinearMap =
          eN'.toLinearMap.comp
            (TensorProduct.AlgebraTensorModule.lTensor S M
              (TensorProduct.AlgebraTensorModule.lTensor S S f)) := by
      have hcomp :=
        TensorProduct.AlgebraTensorModule.lTensor_comp_cancelBaseChange
          (R := R) (A := S) (B := S) (M := M) (N := N) (Q := N') f
      simpa [eN, eN', fS, LinearMap.baseChange] using hcomp
    intro x y hxy
    apply eN.injective
    apply hfM
    change
      (TensorProduct.AlgebraTensorModule.lTensor S M
        (TensorProduct.AlgebraTensorModule.lTensor S S f)) x =
      (TensorProduct.AlgebraTensorModule.lTensor S M
        (TensorProduct.AlgebraTensorModule.lTensor S S f)) y at hxy
    have hxy' := congrArg (fun z => eN' z) hxy
    change
      (eN'.toLinearMap.comp
        (TensorProduct.AlgebraTensorModule.lTensor S M
          (TensorProduct.AlgebraTensorModule.lTensor S S f))) x =
      (eN'.toLinearMap.comp
        (TensorProduct.AlgebraTensorModule.lTensor S M
          (TensorProduct.AlgebraTensorModule.lTensor S S f))) y at hxy'
    rw [← hcomm, LinearMap.comp_apply] at hxy'
    simpa using hxy'
  simpa [fS] using hfS

end BaseChangeAndDescent

section EquationalCriterion

theorem equational_criterion
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] :
    Module.Flat R M ↔
      ∀ {l : ℕ} {f : Fin l → R} {x : Fin l → M},
        (∑ i, f i • x i = 0) → Module.IsTrivialRelation f x :=
  Module.Flat.iff_forall_isTrivialRelation

end EquationalCriterion

section ExactSequences

theorem flat_tensor_short_exact
    {R M'' M' M N : Type*} [CommRing R]
    [AddCommGroup M''] [AddCommGroup M'] [AddCommGroup M] [AddCommGroup N]
    [Module R M''] [Module R M'] [Module R M] [Module R N] [Module.Flat R M]
    (f : M'' →ₗ[R] M') (g : M' →ₗ[R] M)
    (hexact : Exact f g) (hinjective : Injective f) (hsurjective : Surjective g) :
    Injective (f.lTensor N) ∧ Exact (f.lTensor N) (g.lTensor N) ∧
      Surjective (g.lTensor N) := by
  refine ⟨?_, lTensor_exact N hexact hsurjective, LinearMap.lTensor_surjective N hsurjective⟩
  exact LinearMap.lTensor_injective_of_exact_of_flat g hsurjective f hinjective hexact N

theorem flat_quotient_of_ideal_quotient_injective
    {R M N : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) (hflat : Module.Flat R N)
    (hquot : ∀ (I : Ideal R), I.FG →
      Function.Injective
        ((I • (⊤ : Submodule R M)).mapQ (I • (⊤ : Submodule R N)) f
          (Submodule.smul_top_le_comap_smul_top I f))) :
    Module.Flat R (N ⧸ LinearMap.range f) := by
  have hf : Function.Injective f := by
    have hzero := hquot (⊥ : Ideal R) Submodule.fg_bot
    intro x y hxy
    have hmk :
        ((⊥ : Ideal R) • (⊤ : Submodule R M)).mkQ x =
          ((⊥ : Ideal R) • (⊤ : Submodule R M)).mkQ y := by
      apply hzero
      simp [Submodule.mapQ_apply, hxy]
    have hrel := Quotient.exact hmk
    have hmem : x - y ∈ ((⊥ : Ideal R) • (⊤ : Submodule R M)) :=
      (Submodule.quotientRel_def ((⊥ : Ideal R) • (⊤ : Submodule R M))).mp hrel
    exact sub_eq_zero.mp (by simpa using hmem)
  apply Module.Flat.of_forall_isTrivialRelation
  intro l a x hx
  choose n hn using fun i =>
    (Submodule.mkQ_surjective (p := LinearMap.range f)) (x i)
  have hsum0 :
      (Submodule.mkQ (LinearMap.range f)) (∑ i, a i • n i) = 0 := by
    simp only [map_sum, map_smul, hn]
    exact hx
  have hsum : ∑ i, a i • n i ∈ LinearMap.range f := by
    have hrel := Quotient.exact hsum0
    have hmem :=
      (Submodule.quotientRel_def (LinearMap.range f)).mp hrel
    simpa using hmem
  obtain ⟨m, hm⟩ := hsum
  let I : Ideal R := Ideal.span (Set.range a)
  have hIFG : I.FG := Submodule.fg_span (Set.finite_range a)
  have hfmI : f m ∈ I • (⊤ : Submodule R N) := by
    rw [hm]
    exact Submodule.sum_mem (I • (⊤ : Submodule R N)) (fun i hi =>
      Submodule.smul_mem_smul (Ideal.subset_span (Set.mem_range.mpr ⟨i, rfl⟩))
        (show n i ∈ (⊤ : Submodule R N) from trivial))
  have hmI : m ∈ I • (⊤ : Submodule R M) := by
    have hI := hquot I hIFG
    have hmap :
        ((I • (⊤ : Submodule R M)).mapQ (I • (⊤ : Submodule R N)) f
          (Submodule.smul_top_le_comap_smul_top I f))
            ((I • (⊤ : Submodule R M)).mkQ m) =
          ((I • (⊤ : Submodule R M)).mapQ (I • (⊤ : Submodule R N)) f
            (Submodule.smul_top_le_comap_smul_top I f))
            ((I • (⊤ : Submodule R M)).mkQ 0) := by
      simp only [Submodule.mapQ_apply, Submodule.mkQ_apply]
      change (I • (⊤ : Submodule R N)).mkQ (f m) =
        (I • (⊤ : Submodule R N)).mkQ (f 0)
      have hzero : (I • (⊤ : Submodule R N)).mkQ (f m) =
          (I • (⊤ : Submodule R N)).mkQ 0 := by
        apply Quotient.sound
        exact (Submodule.quotientRel_def (I • (⊤ : Submodule R N))).2
          (by simpa [map_zero] using hfmI)
      simpa using hzero
    have hmk := hI hmap
    have hrel := Quotient.exact hmk
    have hmem :=
      (Submodule.quotientRel_def (I • (⊤ : Submodule R M))).mp hrel
    simpa using hmem
  have hrep : ∃ b : Fin l → M, m = ∑ i, a i • b i := by
    let P : M → Prop := fun z => ∃ b : Fin l → M, z = ∑ i, a i • b i
    have hP : P m := by
      refine Submodule.smul_induction_on hmI ?_ ?_
      · intro r hr z hz
        obtain ⟨c, hc⟩ := (Ideal.mem_span_range_iff_exists_fun.mp hr)
        refine ⟨fun i => c i • z, ?_⟩
        rw [← hc, Finset.sum_smul]
        apply Finset.sum_congr rfl
        intro i hi
        calc
          (c i * a i) • z = (a i * c i) • z := by rw [mul_comm]
          _ = a i • (c i • z) := by rw [smul_smul]
      · intro z₁ z₂ hz₁ hz₂
        obtain ⟨b₁, hb₁⟩ := hz₁
        obtain ⟨b₂, hb₂⟩ := hz₂
        refine ⟨fun i => b₁ i + b₂ i, ?_⟩
        rw [hb₁, hb₂, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i hi
        rw [smul_add]
    exact hP
  obtain ⟨b, hb⟩ := hrep
  have hrelN : ∑ i, a i • (n i - f (b i)) = 0 := by
    calc
      ∑ i, a i • (n i - f (b i)) =
          (∑ i, a i • n i) - ∑ i, a i • f (b i) := by
            simp_rw [smul_sub, Finset.sum_sub_distrib]
      _ = f m - f (∑ i, a i • b i) := by
        rw [← hm]
        simp only [map_sum, map_smul]
      _ = 0 := by rw [← hb]; simp
  obtain ⟨k, d, y, hdy, hda⟩ :=
    (Module.Flat.iff_forall_isTrivialRelation.mp hflat) hrelN
  refine ⟨k, d, fun j => Submodule.mkQ (LinearMap.range f) (y j), ?_, hda⟩
  intro i
  have hdi := congrArg (Submodule.mkQ (LinearMap.range f)) (hdy i)
  rw [← hn i]
  have hfb : (Submodule.mkQ (LinearMap.range f)) (f (b i)) = 0 := by
    apply Quotient.sound
    exact (Submodule.quotientRel_def (LinearMap.range f)).2 (by
      change f (b i) - 0 ∈ LinearMap.range f
      exact ⟨b i, by simp⟩)
  change (Submodule.mkQ (LinearMap.range f)) (n i - f (b i)) =
    (Submodule.mkQ (LinearMap.range f)) (∑ j, d i j • y j) at hdi
  rw [map_sub, hfb, sub_zero] at hdi
  simpa [map_sum, map_smul] using hdi

theorem linearMap_rTensor_injective_of_ideal_quotient_injective
    {R M N : Type u} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) (hflat : Module.Flat R N)
    (hquot : ∀ (I : Ideal R), I.FG →
      Function.Injective
        ((I • (⊤ : Submodule R M)).mapQ (I • (⊤ : Submodule R N)) f
          (Submodule.smul_top_le_comap_smul_top I f))) :
    ∀ (Q : Type u) [AddCommGroup Q] [Module R Q],
      Function.Injective (f.rTensor Q) := by
  have hf : Function.Injective f := by
    have hzero := hquot (⊥ : Ideal R) Submodule.fg_bot
    intro x y hxy
    have hmk :
        ((⊥ : Ideal R) • (⊤ : Submodule R M)).mkQ x =
          ((⊥ : Ideal R) • (⊤ : Submodule R M)).mkQ y := by
      apply hzero
      simp [Submodule.mapQ_apply, hxy]
    have hrel := Quotient.exact hmk
    have hmem : x - y ∈ ((⊥ : Ideal R) • (⊤ : Submodule R M)) :=
      (Submodule.quotientRel_def ((⊥ : Ideal R) • (⊤ : Submodule R M))).mp hrel
    exact sub_eq_zero.mp (by simpa using hmem)
  let C := N ⧸ LinearMap.range f
  let g : N →ₗ[R] C := Submodule.mkQ (LinearMap.range f)
  have hC : Module.Flat R C :=
    flat_quotient_of_ideal_quotient_injective f hflat hquot
  let _ : Module.Flat R C := hC
  have hex : Function.Exact f g := LinearMap.exact_map_mkQ_range f
  intro Q _ _
  have ht := flat_tensor_short_exact f g hex hf (Submodule.mkQ_surjective (p := LinearMap.range f))
    (N := Q)
  exact (f.lTensor_inj_iff_rTensor_inj Q).mp ht.1

theorem linearMap_rTensor_injective_iff_ideal_quotient_injective
    {R M N : Type u} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) (hflat : Module.Flat R N) :
    (∀ (Q : Type u) [AddCommGroup Q] [Module R Q],
      Function.Injective (f.rTensor Q)) ↔
      ∀ (I : Ideal R), I.FG →
        Function.Injective
          ((I • (⊤ : Submodule R M)).mapQ (I • (⊤ : Submodule R N)) f
            (Submodule.smul_top_le_comap_smul_top I f)) := by
  constructor
  · intro hf I _
    let Q := R ⧸ I
    let eM : M ⊗[R] Q ≃ₗ[R]
        M ⧸ (I • (⊤ : Submodule R M)) :=
      (TensorProduct.comm R M Q).trans
        (TensorProduct.quotTensorEquivQuotSMul M I)
    let eN : N ⊗[R] Q ≃ₗ[R]
        N ⧸ (I • (⊤ : Submodule R N)) :=
      (TensorProduct.comm R N Q).trans
        (TensorProduct.quotTensorEquivQuotSMul N I)
    have hcomm :
        eN.toLinearMap.comp (f.rTensor Q) =
          ((I • (⊤ : Submodule R M)).mapQ (I • (⊤ : Submodule R N)) f
            (Submodule.smul_top_le_comap_smul_top I f)).comp eM.toLinearMap := by
      apply LinearMap.ext
      intro z
      induction z using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy => simp only [map_add, hx, hy]
      | tmul x y =>
          obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective y
          simp only [eM, eN, LinearMap.comp_apply, LinearMap.rTensor_tmul]
          change (TensorProduct.quotTensorEquivQuotSMul N I)
              ((Ideal.Quotient.mk I) r ⊗ₜ[R] f x) =
            ((I • (⊤ : Submodule R M)).mapQ (I • (⊤ : Submodule R N)) f
              (Submodule.smul_top_le_comap_smul_top I f))
              ((TensorProduct.quotTensorEquivQuotSMul M I)
                ((Ideal.Quotient.mk I) r ⊗ₜ[R] x))
          rw [TensorProduct.quotTensorEquivQuotSMul_mk_tmul]
          rw [TensorProduct.quotTensorEquivQuotSMul_mk_tmul]
          simp [Submodule.mapQ_apply]
    have hcomm_apply (z : M ⊗[R] Q) :
        eN ((f.rTensor Q) z) =
          ((I • (⊤ : Submodule R M)).mapQ (I • (⊤ : Submodule R N)) f
            (Submodule.smul_top_le_comap_smul_top I f)) (eM z) := by
      have h := congrArg (fun g => g z) hcomm
      simpa [LinearMap.comp_apply] using h
    intro x y hxy
    apply eM.symm.injective
    apply hf Q
    apply eN.injective
    calc
      eN ((f.rTensor Q) (eM.symm x)) =
          ((I • (⊤ : Submodule R M)).mapQ (I • (⊤ : Submodule R N)) f
            (Submodule.smul_top_le_comap_smul_top I f)) (eM (eM.symm x)) := by
              exact hcomm_apply _
      _ = ((I • (⊤ : Submodule R M)).mapQ (I • (⊤ : Submodule R N)) f
            (Submodule.smul_top_le_comap_smul_top I f)) x := by
              rw [eM.apply_symm_apply]
      _ = ((I • (⊤ : Submodule R M)).mapQ (I • (⊤ : Submodule R N)) f
            (Submodule.smul_top_le_comap_smul_top I f)) y := hxy
      _ = eN ((f.rTensor Q) (eM.symm y)) := by
        simpa using (hcomm_apply (eM.symm y)).symm
  · intro hquot
    exact linearMap_rTensor_injective_of_ideal_quotient_injective f hflat hquot

theorem flat_short_exact
    {R M' M M'' : Type*} [CommRing R]
    [AddCommGroup M'] [AddCommGroup M] [AddCommGroup M'']
    [Module R M'] [Module R M] [Module R M'']
    (f : M' →ₗ[R] M) (g : M →ₗ[R] M'') (hexact : Exact f g)
    (hinjective : Injective f) (hsurjective : Surjective g) :
    (Module.Flat R M' → Module.Flat R M'' → Module.Flat R M) ∧
      (Module.Flat R M → Module.Flat R M'' → Module.Flat R M') := by
  constructor
  · intro hM' hM''
    let _ : Module.Flat R M' := hM'
    let _ : Module.Flat R M'' := hM''
    apply (Module.Flat.iff_rTensor_preserves_injective_linearMap).2
    intro N N' _ _ _ _ i hi
    have hiM' : Function.Injective (i.rTensor M') :=
      Module.Flat.rTensor_preserves_injective_linearMap i hi
    have hiM'' : Function.Injective (i.rTensor M'') :=
      Module.Flat.rTensor_preserves_injective_linearMap i hi
    have hshortN :=
      flat_tensor_short_exact (R := R) (M'' := M') (M' := M) (M := M'') (N := N)
        f g hexact hinjective hsurjective
    have hfN : Function.Injective (f.lTensor N) := hshortN.1
    have hexN : Exact (f.lTensor N) (g.lTensor N) := hshortN.2.1
    have hshortN' :=
      flat_tensor_short_exact (R := R) (M'' := M') (M' := M) (M := M'') (N := N')
        f g hexact hinjective hsurjective
    have hfN' : Function.Injective (f.lTensor N') := hshortN'.1
    have hcommg :
        (i.rTensor M'').comp (g.lTensor N) =
          (g.lTensor N').comp (i.rTensor M) := by
      rw [LinearMap.rTensor_comp_lTensor, LinearMap.lTensor_comp_rTensor]
    have hcommf :
        (i.rTensor M).comp (f.lTensor N) =
          (f.lTensor N').comp (i.rTensor M') := by
      rw [LinearMap.rTensor_comp_lTensor, LinearMap.lTensor_comp_rTensor]
    apply LinearMap.ker_eq_bot.mp
    rw [eq_bot_iff]
    intro x hx
    change (i.rTensor M) x = 0 at hx
    have hgx : (g.lTensor N) x = 0 := by
      apply hiM''
      change ((i.rTensor M'').comp (g.lTensor N)) x = 0
      rw [hcommg, LinearMap.comp_apply, hx]
      simp
    have hxker : x ∈ LinearMap.ker (g.lTensor N) := by
      change (g.lTensor N) x = 0
      exact hgx
    rw [hexN.linearMap_ker_eq] at hxker
    obtain ⟨y, hy⟩ := hxker
    have hfy : (f.lTensor N') ((i.rTensor M') y) = 0 := by
      have htemp : (i.rTensor M) ((f.lTensor N) y) = 0 := by
        rw [hy, hx]
      change ((f.lTensor N').comp (i.rTensor M')) y = 0
      rw [← hcommf, LinearMap.comp_apply]
      exact htemp
    have hiy : (i.rTensor M') y = 0 := hfN' hfy
    have hy0 : y = 0 := hiM' hiy
    have hx0 : x = 0 := by
      rw [← hy, hy0]
      simp
    simpa using hx0
  · intro hM hM''
    let _ : Module.Flat R M := hM
    let _ : Module.Flat R M'' := hM''
    apply (Module.Flat.iff_rTensor_preserves_injective_linearMap).2
    intro N N' _ _ _ _ i hi
    have hiM : Function.Injective (i.rTensor M) :=
      Module.Flat.rTensor_preserves_injective_linearMap i hi
    have hshortN :=
      flat_tensor_short_exact (R := R) (M'' := M') (M' := M) (M := M'') (N := N)
        f g hexact hinjective hsurjective
    have hfN : Function.Injective (f.lTensor N) := hshortN.1
    have hcommf :
        (i.rTensor M).comp (f.lTensor N) =
          (f.lTensor N').comp (i.rTensor M') := by
      rw [LinearMap.rTensor_comp_lTensor, LinearMap.lTensor_comp_rTensor]
    apply LinearMap.ker_eq_bot.mp
    rw [eq_bot_iff]
    intro x hx
    change (i.rTensor M') x = 0 at hx
    have hfx : (f.lTensor N) x = 0 := by
      apply hiM
      change ((i.rTensor M).comp (f.lTensor N)) x = 0
      rw [hcommf, LinearMap.comp_apply, hx]
      simp
    have hx0 : x = 0 := hfN hfx
    simpa using hx0

end ExactSequences

section FaithfulFlatness

theorem faithfullyFlat_iff_flat_and_tensor_zero
    {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M] :
    Module.FaithfullyFlat R M ↔
      (Module.Flat R M ∧
        ∀ {N N' : Type (max u v)} [AddCommGroup N] [AddCommGroup N']
          [Module R N] [Module R N'] (α : N →ₗ[R] N'),
          α = 0 ↔ α.rTensor M = 0) := by
  constructor
  · intro h
    let := h
    refine ⟨inferInstance, ?_⟩
    intro N N' _ _ _ _ α
    exact Module.FaithfullyFlat.zero_iff_rTensor_zero R M α
  · rintro ⟨hflat, hzero⟩
    apply (Module.FaithfullyFlat.iff_zero_iff_rTensor_zero (R := R) (M := M)).2
    refine ⟨hflat, ?_⟩
    intro N _ _ N' _ _ α
    exact (hzero α).symm

theorem faithfullyFlat_criteria
    {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]
    [Module.Flat R M] :
    List.TFAE [
      Module.FaithfullyFlat R M,
      ∀ (N : Type (max u v)) [AddCommGroup N] [Module R N],
        Nontrivial N → Nontrivial (M ⊗[R] N),
      ∀ (p : PrimeSpectrum R),
        Nontrivial (M ⊗[R] p.asIdeal.ResidueField),
      ∀ (m : Ideal R) [m.IsMaximal],
        Nontrivial (M ⊗[R] m.ResidueField)] := by
  tfae_have 1 ↔ 2 := by
    constructor
    · intro h
      let := h
      intro N _ _ hN
      let := hN
      exact inferInstance
    · intro h
      apply (Module.FaithfullyFlat.iff_flat_and_lTensor_faithful R M).2
      exact ⟨inferInstance, h⟩
  tfae_have 2 → 3 := by
    intro h p
    let : Nontrivial (ULift.{max u v, u} p.asIdeal.ResidueField) := inferInstance
    let : Nontrivial (M ⊗[R] ULift.{max u v, u} p.asIdeal.ResidueField) :=
      h (ULift.{max u v, u} p.asIdeal.ResidueField) inferInstance
    exact (TensorProduct.congr (LinearEquiv.refl R M)
      (ULift.moduleEquiv : ULift.{max u v, u} p.asIdeal.ResidueField ≃ₗ[R] p.asIdeal.ResidueField)).symm.toEquiv.nontrivial
  tfae_have 3 → 4 := by
    intro h m hm
    let p : PrimeSpectrum R := ⟨m, hm.isPrime⟩
    simpa [p] using h p
  tfae_have 4 → 1 := by
    intro h
    apply (Module.FaithfullyFlat.iff_flat_and_proper_ideal R M).2
    refine ⟨inferInstance, ?_⟩
    intro I hI
    obtain ⟨m, hm, hIm⟩ := I.exists_le_maximal hI
    let : m.IsMaximal := hm
    intro htop
    have hm_top : m • (⊤ : Submodule R M) = ⊤ := by
      apply top_unique
      calc
        (⊤ : Submodule R M) = I • ⊤ := htop.symm
        _ ≤ m • ⊤ := Submodule.smul_mono hIm le_rfl
    let e : (R ⧸ m) ≃ₗ[R] m.ResidueField :=
      LinearEquiv.ofBijective (Algebra.linearMap (R ⧸ m) m.ResidueField)
        (Ideal.bijective_algebraMap_quotient_residueField m) |>.restrictScalars R
    let e' : M ⊗[R] (R ⧸ m) ≃ₗ[R] M ⊗[R] m.ResidueField :=
      TensorProduct.congr (LinearEquiv.refl R M) e
    have htensor : Nontrivial (M ⊗[R] (R ⧸ m)) := by
      let : Nontrivial (M ⊗[R] m.ResidueField) := h m
      exact e'.toEquiv.nontrivial
    have hquot : Nontrivial (M ⧸ (m • (⊤ : Submodule R M))) := by
      let : Nontrivial (M ⊗[R] (R ⧸ m)) := htensor
      let : Nontrivial ((R ⧸ m) ⊗[R] M) :=
        (TensorProduct.comm R (R ⧸ m) M).toEquiv.nontrivial
      exact (TensorProduct.quotTensorEquivQuotSMul M m).toEquiv.symm.nontrivial
    let := hquot
    exact not_subsingleton _ (Submodule.Quotient.subsingleton_iff.mpr hm_top)
  tfae_finish

theorem faithfullyFlat_ringHom_criteria
    {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (hflat : RingHom.Flat f) :
    List.TFAE [
      RingHom.FaithfullyFlat f,
      Function.Surjective (PrimeSpectrum.comap f),
      ∀ p : PrimeSpectrum R, p.asIdeal.IsMaximal →
        ∃ q : PrimeSpectrum S, PrimeSpectrum.comap f q = p] := by
  algebraize [f]
  tfae_have 1 ↔ 2 := by
    rw [RingHom.FaithfullyFlat.iff_flat_and_comap_surjective]
    exact and_iff_right hflat
  tfae_have 2 → 3 := by
    intro h p hp
    exact h ⟨p, hp.isPrime⟩
  tfae_have 3 → 2 := by
    intro h p
    obtain ⟨m, hm, hpm⟩ := p.asIdeal.exists_le_maximal p.isPrime.ne_top
    obtain ⟨q, hq⟩ := h ⟨m, hm.isPrime⟩ hm
    let : q.asIdeal.LiesOver m := ⟨by
      change m = Ideal.comap (algebraMap R S) q.asIdeal
      rw [RingHom.algebraMap_toAlgebra f]
      rw [← PrimeSpectrum.comap_asIdeal f q, hq]
    ⟩
    obtain ⟨P, hPq, hPprime, hPover⟩ :=
      Ideal.exists_ideal_le_liesOver_of_le q.asIdeal (p := p.asIdeal) (q := m) hpm
    refine ⟨⟨P, hPprime⟩, ?_⟩
    apply PrimeSpectrum.ext
    simpa [Ideal.under_def, RingHom.algebraMap_toAlgebra f] using hPover.over.symm
  tfae_finish

theorem faithfullyFlat_of_localRingHom
    {R S : Type*} [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]
    (f : R →+* S) [IsLocalHom f] (hflat : RingHom.Flat f) :
    RingHom.FaithfullyFlat f := by
  algebraize [f]
  exact Module.FaithfullyFlat.of_flat_of_isLocalHom

end FaithfulFlatness

section Localization

theorem localization_flat
    {R : Type*} [CommRing R] (S : Submonoid R) :
    RingHom.Flat (algebraMap R (Localization S)) := by
  exact (RingHom.flat_algebraMap_iff).2 (inferInstance : Module.Flat R (Localization S))

theorem flat_localization_iff
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (S : Submonoid R) [Module (Localization S) M]
    [IsScalarTower R (Localization S) M] :
    Module.Flat R M ↔ Module.Flat (Localization S) M := by
  exact (Module.flat_iff_of_isLocalization (Localization S) S M).symm

theorem flat_iff_localized_at_primes
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] :
    Module.Flat R M ↔
      ∀ p : PrimeSpectrum R,
        Module.Flat (Localization.AtPrime p.asIdeal)
          (LocalizedModule p.asIdeal.primeCompl M) := by
  constructor
  · intro h p
    let : Module.Flat R M := h
    infer_instance
  · intro h
    apply Module.flat_of_localized_maximal M
    intro m hm
    let : m.IsMaximal := hm
    exact (Module.flat_iff_of_isLocalization (Localization.AtPrime m)
      m.primeCompl (LocalizedModule m.primeCompl M)).1 (h ⟨m, hm.isPrime⟩)

theorem flat_iff_localized_at_maximals
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] :
    Module.Flat R M ↔
      ∀ (m : Ideal R) [m.IsMaximal],
        Module.Flat (Localization.AtPrime m)
          (LocalizedModule m.primeCompl M) := by
  constructor
  · intro h m
    let : Module.Flat R M := h
    infer_instance
  · intro h
    apply Module.flat_of_localized_maximal M
    intro m hm
    let : m.IsMaximal := hm
    exact (Module.flat_iff_of_isLocalization (Localization.AtPrime m)
      m.primeCompl (LocalizedModule m.primeCompl M)).1 (h m)

theorem flat_iff_localized_on_generators
    {R A M : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M]
    {n : ℕ} (g : Fin n → A) (hg : Ideal.span (Set.range g) = ⊤) :
    Module.Flat R M ↔
      ∀ i : Fin n,
        Module.Flat R (LocalizedModule (Submonoid.powers (g i)) M) := by
  constructor
  · intro h i
    rw [Module.Flat.iff_lTensor_injectiveₛ]
    simp_rw [← TensorProduct.AlgebraTensorModule.coe_lTensor (A := A)]
    intro P _ _ N
    let gLoc : M →ₗ[A] LocalizedModule (Submonoid.powers (g i)) M :=
      LocalizedModule.mkLinearMap (Submonoid.powers (g i)) M
    have hF : Function.Injective
        (TensorProduct.AlgebraTensorModule.lTensor A M N.subtype) :=
      (Module.Flat.iff_lTensor_injectiveₛ.mp h) N
    have hmap := IsLocalizedModule.map_injective
      (S := Submonoid.powers (g i))
      (f := TensorProduct.AlgebraTensorModule.rTensor R N gLoc)
      (g := TensorProduct.AlgebraTensorModule.rTensor R P gLoc)
      (TensorProduct.AlgebraTensorModule.lTensor A M N.subtype) hF
    simpa [IsLocalizedModule.map_lTensor] using hmap
  · intro h
    refine Module.flat_of_isLocalized_span A M (Set.range g) hg
      (fun r : Set.range g => LocalizedModule (Submonoid.powers (r : A)) M)
      (fun (r : Set.range g) => LocalizedModule.mkLinearMap
        (Submonoid.powers (r : A)) M) ?_
    rintro ⟨a, ⟨i, rfl⟩⟩
    exact h i

private theorem flat_localizedModule_of_flat
    {R A M : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M]
    (S : Submonoid A) (h : Module.Flat R M) :
    Module.Flat R (LocalizedModule S M) := by
  rw [Module.Flat.iff_lTensor_injectiveₛ]
  simp_rw [← TensorProduct.AlgebraTensorModule.coe_lTensor (A := A)]
  intro P _ _ N
  let gLoc : M →ₗ[A] LocalizedModule S M := LocalizedModule.mkLinearMap S M
  have hF : Function.Injective
      (TensorProduct.AlgebraTensorModule.lTensor A M N.subtype) :=
    (Module.Flat.iff_lTensor_injectiveₛ.mp h) N
  have hmap := IsLocalizedModule.map_injective
    (S := S)
    (f := TensorProduct.AlgebraTensorModule.rTensor R N gLoc)
    (g := TensorProduct.AlgebraTensorModule.rTensor R P gLoc)
    (TensorProduct.AlgebraTensorModule.lTensor A M N.subtype) hF
  simpa [IsLocalizedModule.map_lTensor] using hmap

noncomputable def flat_at_prime_over
    {R A M : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M]
    (P : Ideal A) [P.IsPrime] : Prop :=
  let p := P.comap (algebraMap R A)
  letI : Algebra (Localization.AtPrime p) (Localization.AtPrime P) :=
    Localization.AtPrime.algebraOfLiesOver p P
  letI : Module (Localization.AtPrime p) (LocalizedModule P.primeCompl M) :=
    Module.compHom _ (algebraMap (Localization.AtPrime p) (Localization.AtPrime P))
  Module.Flat (Localization.AtPrime p) (LocalizedModule P.primeCompl M)

theorem flat_iff_localized_over_primes
    {R A M : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M] :
    Module.Flat R M ↔
      ∀ (P : Ideal A) [P.IsPrime], flat_at_prime_over (R := R) (A := A) (M := M) P := by
  constructor
  · intro h P hP
    let : P.IsPrime := hP
    let p := P.comap (algebraMap R A)
    let : Algebra (Localization.AtPrime p) (Localization.AtPrime P) :=
      Localization.AtPrime.algebraOfLiesOver p P
    let : IsScalarTower R (Localization.AtPrime p) (Localization.AtPrime P) := inferInstance
    let : Module (Localization.AtPrime p) (LocalizedModule P.primeCompl M) :=
      Module.compHom _ (algebraMap (Localization.AtPrime p) (Localization.AtPrime P))
    let : IsScalarTower R (Localization.AtPrime p) (LocalizedModule P.primeCompl M) :=
      IsScalarTower.of_algebraMap_smul fun r x => by
        change algebraMap (Localization.AtPrime p) (Localization.AtPrime P)
            (algebraMap R (Localization.AtPrime p) r) • x = r • x
        rw [← IsScalarTower.algebraMap_apply R (Localization.AtPrime p)
          (Localization.AtPrime P)]
        exact algebraMap_smul (Localization.AtPrime P) r x
    change Module.Flat (Localization.AtPrime p) (LocalizedModule P.primeCompl M)
    apply (Module.flat_iff_of_isLocalization (Localization.AtPrime p)
      p.primeCompl (LocalizedModule P.primeCompl M)).2
    exact flat_localizedModule_of_flat P.primeCompl h
  · intro h
    refine Module.flat_of_isLocalized_maximal A M
      (fun P _ => LocalizedModule P.primeCompl M)
      (fun P _ => LocalizedModule.mkLinearMap P.primeCompl M) ?_
    intro P hP
    let : P.IsMaximal := hP
    let p := P.comap (algebraMap R A)
    let : Algebra (Localization.AtPrime p) (Localization.AtPrime P) :=
      Localization.AtPrime.algebraOfLiesOver p P
    let : IsScalarTower R (Localization.AtPrime p) (Localization.AtPrime P) := inferInstance
    let : Module (Localization.AtPrime p) (LocalizedModule P.primeCompl M) :=
      Module.compHom _ (algebraMap (Localization.AtPrime p) (Localization.AtPrime P))
    let : IsScalarTower R (Localization.AtPrime p) (LocalizedModule P.primeCompl M) :=
      IsScalarTower.of_algebraMap_smul fun r x => by
        change algebraMap (Localization.AtPrime p) (Localization.AtPrime P)
            (algebraMap R (Localization.AtPrime p) r) • x = r • x
        rw [← IsScalarTower.algebraMap_apply R (Localization.AtPrime p)
          (Localization.AtPrime P)]
        exact algebraMap_smul (Localization.AtPrime P) r x
    apply (Module.flat_iff_of_isLocalization (Localization.AtPrime p)
      p.primeCompl (LocalizedModule P.primeCompl M)).1
    simpa [flat_at_prime_over] using h P

theorem flat_iff_localized_over_maximals
    {R A M : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M] :
    Module.Flat R M ↔
      ∀ (P : Ideal A) [P.IsMaximal], flat_at_prime_over (R := R) (A := A) (M := M) P := by
  constructor
  · intro h P hP
    let : P.IsMaximal := hP
    exact (flat_iff_localized_over_primes (R := R) (A := A) (M := M)).1 h P
  · intro h
    refine Module.flat_of_isLocalized_maximal A M
      (fun P _ => LocalizedModule P.primeCompl M)
      (fun P _ => LocalizedModule.mkLinearMap P.primeCompl M) ?_
    intro P hP
    let : P.IsMaximal := hP
    let p := P.comap (algebraMap R A)
    let : Algebra (Localization.AtPrime p) (Localization.AtPrime P) :=
      Localization.AtPrime.algebraOfLiesOver p P
    let : IsScalarTower R (Localization.AtPrime p) (Localization.AtPrime P) := inferInstance
    let : Module (Localization.AtPrime p) (LocalizedModule P.primeCompl M) :=
      Module.compHom _ (algebraMap (Localization.AtPrime p) (Localization.AtPrime P))
    let : IsScalarTower R (Localization.AtPrime p) (LocalizedModule P.primeCompl M) :=
      IsScalarTower.of_algebraMap_smul fun r x => by
        change algebraMap (Localization.AtPrime p) (Localization.AtPrime P)
            (algebraMap R (Localization.AtPrime p) r) • x = r • x
        rw [← IsScalarTower.algebraMap_apply R (Localization.AtPrime p)
          (Localization.AtPrime P)]
        exact algebraMap_smul (Localization.AtPrime P) r x
    apply (Module.flat_iff_of_isLocalization (Localization.AtPrime p)
      p.primeCompl (LocalizedModule P.primeCompl M)).1
    simpa [flat_at_prime_over] using h P

end Localization

section GoingDown

theorem flat_going_down
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] [Module.Flat R S]
    {p p' : Ideal R} [p.IsPrime] [p'.IsPrime] (hpp : p ≤ p')
    (Q : Ideal S) [Q.IsPrime] [Q.LiesOver p'] :
    ∃ P : Ideal S, P ≤ Q ∧ P.IsPrime ∧ P.LiesOver p := by
  exact Ideal.exists_ideal_le_liesOver_of_le Q hpp

end GoingDown

section FaithfullyFlatColimits

theorem directLimit_faithfullyFlat
    {R : Type u} [CommRing R] {ι : Type v} [Preorder ι] [Nonempty ι]
    [IsDirectedOrder ι] {S : ι → Type w} [∀ i, CommRing (S i)] [∀ i, Algebra R (S i)]
    (f : ∀ i j, i ≤ j → S i →ₐ[R] S j)
    [DirectedSystem S (f · · ·)]
    (hff : ∀ i, Module.FaithfullyFlat R (S i)) :
    Module.FaithfullyFlat R (DirectLimit S f) := by
  classical
  let _ : DirectedSystem S (fun i j h => (f i j h).toLinearMap) :=
    { map_self := by
        intro i x
        change f i i le_rfl x = x
        exact DirectedSystem.map_self (f := fun i j h => f i j h) x
      map_map := by
        intro k j i hij hjk x
        change f j k hjk (f i j hij x) = f i k (hij.trans hjk) x
        exact DirectedSystem.map_map (f := fun i j h => f i j h) hij hjk x }
  let e : Module.DirectLimit S (fun i j h => (f i j h).toLinearMap) ≃ₗ[R]
      DirectLimit S f := Module.DirectLimit.linearEquiv S
        (fun i j h => (f i j h).toLinearMap)
  have hflat : Module.Flat R (DirectLimit S f) := by
    change Module.Flat R
      (DirectLimit S (fun i j h => (f i j h).toLinearMap))
    exact directLimit_flat (fun i j h => (f i j h).toLinearMap)
      (fun i => (hff i).toFlat)
  let _ : Module.Flat R (DirectLimit S f) := hflat
  have hflat' : Module.Flat R
      (Module.DirectLimit S (fun i j h => (f i j h).toLinearMap)) :=
    Module.Flat.of_linearEquiv e
  have hff' : Module.FaithfullyFlat R
      (Module.DirectLimit S (fun i j h => (f i j h).toLinearMap)) := by
    apply (Module.FaithfullyFlat.iff_flat_and_lTensor_faithful R _).2
    refine ⟨hflat', ?_⟩
    intro N _ _ hN
    let _ : Nontrivial N := hN
    apply (nontrivial_iff_exists_ne
      (0 : Module.DirectLimit S (fun i j h => (f i j h).toLinearMap) ⊗[R] N)).2
    obtain ⟨n, hn⟩ := nontrivial_iff_exists_ne (0 : N) |>.1 inferInstance
    let i : ι := Classical.arbitrary ι
    refine ⟨(Module.DirectLimit.of R ι S
      (fun i j h => (f i j h).toLinearMap) i 1) ⊗ₜ[R] n, ?_⟩
    intro hzero
    have hzero' := congrArg (TensorProduct.directLimitLeft
      (fun i j h => (f i j h).toLinearMap) N) hzero
    rw [TensorProduct.directLimitLeft_tmul_of] at hzero'
    obtain ⟨j, hij, htrans⟩ := Module.DirectLimit.of.zero_exact hzero'
    let _ : Module.FaithfullyFlat R (S j) := hff j
    have htrans' : (1 : S j) ⊗ₜ[R] n = 0 := by
      simpa using htrans
    exact hn ((Module.FaithfullyFlat.one_tmul_eq_zero_iff R N n).1 htrans')
  let _ : Module.FaithfullyFlat R
      (Module.DirectLimit S (fun i j h => (f i j h).toLinearMap)) := hff'
  exact Module.FaithfullyFlat.of_linearEquiv R
    (Module.DirectLimit S (fun i j h => (f i j h).toLinearMap)) e.symm

end FaithfullyFlatColimits

end
end Formalization.Books.Algebra.Unit39
