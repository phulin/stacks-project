import Formalization.Books.Algebra.Unit66.WeaklyAssociatedPrimes

namespace Formalization.Books.Algebra.Unit66

open Set
open scoped TensorProduct

noncomputable section

/-- Going down contracts a minimal annihilator of a pure base-change tensor
to a minimal annihilator over the source ring. -/
theorem weaklyAssociatedPrime_contract_tmul_of_flat
    {A S X : Type*} [CommRing A] [CommRing S] [Algebra A S]
    [Module.Flat A S] [AddCommGroup X] [Module A X]
    (q : PrimeSpectrum S) (x : X)
    (hq : q.asIdeal ∈
      ((⊥ : Submodule S (TensorProduct A S X)).colon
        ({(1 : S) ⊗ₜ[A] x} : Set _)).minimalPrimes) :
    letI : Module A (TensorProduct A S X) :=
      Module.compHom _ (algebraMap A S)
    PrimeSpectrum.comap (algebraMap A S) q ∈
      weaklyAssociatedPrimes A X := by
  let I : Ideal A := (⊥ : Submodule A X).colon ({x} : Set X)
  let J : Ideal S :=
    (⊥ : Submodule S (TensorProduct A S X)).colon
      ({(1 : S) ⊗ₜ[A] x} : Set _)
  have hJ : J = I.map (algebraMap A S) :=
    annihilator_one_tmul_eq_map x
  let p : Ideal A := q.asIdeal.comap (algebraMap A S)
  have hpprime : p.IsPrime := Ideal.comap_isPrime _ q.asIdeal
  have hIle : I ≤ p := by
    rw [← Ideal.map_le_iff_le_comap, ← hJ]
    exact hq.1.2
  have hpmin : p ∈ I.minimalPrimes := by
    refine ⟨⟨hpprime, hIle⟩, ?_⟩
    intro P hP hPle
    letI : P.IsPrime := hP.1
    letI : q.asIdeal.IsPrime := q.2
    have hqover : q.asIdeal.LiesOver p := ⟨rfl⟩
    letI : q.asIdeal.LiesOver p := hqover
    obtain ⟨Q, hQle, hQprime, hQover⟩ :=
      Ideal.exists_ideal_le_liesOver_of_le q.asIdeal hPle
    have hmaple : I.map (algebraMap A S) ≤ Q := by
      rw [Ideal.map_le_iff_le_comap]
      change I ≤ Q.under A
      have hoverQ : P = Q.under A :=
        @Ideal.LiesOver.over A _ S _ _ Q P hQover
      exact hP.2.trans_eq hoverQ
    have hqle : q.asIdeal ≤ Q := by
      apply hq.2 ⟨hQprime, ?_⟩ hQle
      change J ≤ Q
      rw [hJ]
      exact hmaple
    have hQeq : Q = q.asIdeal := le_antisymm hQle hqle
    have hoverQ : P = Q.under A :=
      @Ideal.LiesOver.over A _ S _ _ Q P hQover
    have hoverq : p = q.asIdeal.under A :=
      @Ideal.LiesOver.over A _ S _ _ q.asIdeal p hqover
    have hpP : p = P := hoverq.trans <|
      (congrArg (Ideal.under A) hQeq.symm).trans hoverQ.symm
    exact hpP.le
  exact ⟨x, hpmin⟩

/-- Every element of the base-changed module is defined over a finitely
generated intermediate coefficient field. -/
theorem exists_fg_intermediateField_module_preimage
    {k K R M : Type*} [Field k] [Field K] [Algebra k K]
    [CommRing R] [Algebra k R] [AddCommGroup M] [Module R M]
    (z : TensorProduct R (R ⊗[k] K) M) :
    ∃ L : IntermediateField k K, L.FG ∧
      let f := Algebra.TensorProduct.map (AlgHom.id k R) L.val
      let fR : (R ⊗[k] L) →ₗ[R] (R ⊗[k] K) :=
        { toFun := f
          map_add' := f.map_add
          map_smul' := by
            intro r b
            induction b using TensorProduct.induction_on with
            | zero => simp
            | tmul a x => simp [f, TensorProduct.smul_tmul']
            | add x y hx hy => simp [smul_add, hx, hy] }
      z ∈ LinearMap.range (fR.rTensor M) := by
  classical
  obtain ⟨s, hs⟩ := TensorProduct.exists_multiset z
  let rep (b : R ⊗[k] K) : Multiset (R × K) :=
    Classical.choose (TensorProduct.exists_multiset b)
  have hrep (b : R ⊗[k] K) :
      ((rep b).map (fun a => a.1 ⊗ₜ[k] a.2)).sum = b :=
    (Classical.choose_spec (TensorProduct.exists_multiset b)).symm
  let u : Multiset K := s.bind fun bm => (rep bm.1).map Prod.snd
  let t : Finset K := u.toFinset
  let L : IntermediateField k K := IntermediateField.adjoin k (t : Set K)
  have hmem (bm : (R ⊗[k] K) × M) (hbm : bm ∈ s)
      (a : R × K) (ha : a ∈ rep bm.1) : a.2 ∈ L := by
    apply IntermediateField.subset_adjoin
    apply Finset.mem_coe.mpr
    apply Multiset.mem_toFinset.mpr
    apply Multiset.mem_bind.mpr
    exact ⟨bm, hbm, Multiset.mem_map.mpr ⟨a, ha, rfl⟩⟩
  let coeff (x : K) : L := if hx : x ∈ L then ⟨x, hx⟩ else 0
  let liftB (b : R ⊗[k] K) : R ⊗[k] L :=
    ((rep b).map fun a => a.1 ⊗ₜ[k] coeff a.2).sum
  let zL : TensorProduct R (R ⊗[k] L) M :=
    (s.map fun bm => liftB bm.1 ⊗ₜ[R] bm.2).sum
  let f := Algebra.TensorProduct.map (AlgHom.id k R) L.val
  let fR : (R ⊗[k] L) →ₗ[R] (R ⊗[k] K) :=
    { toFun := f
      map_add' := f.map_add
      map_smul' := by
        intro r b
        induction b using TensorProduct.induction_on with
        | zero => simp
        | tmul a x => simp [f, TensorProduct.smul_tmul']
        | add x y hx hy => simp [smul_add, hx, hy] }
  refine ⟨L, IntermediateField.fg_adjoin_finset t, zL, ?_⟩
  rw [hs]
  dsimp only [zL]
  rw [map_multiset_sum, Multiset.map_map]
  apply congrArg Multiset.sum
  refine Multiset.map_congr rfl ?_
  intro bm hbm
  change fR (liftB bm.1) ⊗ₜ[R] bm.2 = bm.1 ⊗ₜ[R] bm.2
  congr 1
  dsimp only [liftB]
  rw [map_multiset_sum, Multiset.map_map]
  calc
    (Multiset.map (⇑fR ∘ fun a => a.1 ⊗ₜ[k] coeff a.2) (rep bm.1)).sum =
        (Multiset.map (fun a => a.1 ⊗ₜ[k] a.2) (rep bm.1)).sum := by
      apply congrArg Multiset.sum
      refine Multiset.map_congr rfl ?_
      intro a ha
      simp [fR, f, coeff, hmem bm hbm a ha]
    _ = bm.1 := hrep bm.1

end
end Formalization.Books.Algebra.Unit66
