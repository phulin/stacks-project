import Formalization.Books.MoreAlgebra.Unit129.BigProjectiveFree
import Formalization.Books.Algebra.Unit85.ProjectiveModulesLocalRing
import Mathlib.Algebra.Module.LocalizedModule.Exact
import Mathlib.Algebra.Module.LocalizedModule.Submodule
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.RingTheory.Localization.Finiteness
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Mathlib.RingTheory.LocalProperties.Projective
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.TensorProduct.Quotient
import Mathlib.RingTheory.Localization.BaseChange
import Formalization.Books.Algebra.Unit19.Radical

namespace Formalization.Books.MoreAlgebra.Unit129

noncomputable section

open scoped TensorProduct

private theorem test_functional
    {k : Type u} {Q : Type v} [Field k]
    [AddCommGroup Q] [Module k Q] (x y : Q)
    (hy : y ∉ Submodule.span k ({x} : Set Q)) :
    ∃ f : Q →ₗ[k] k, f y = 1 ∧ f x = 0 := by
  let W : Submodule k Q := Submodule.span k ({x} : Set Q)
  obtain ⟨f, hf, hfy⟩ :=
    LinearMap.exists_extend_of_notMem (0 : W →ₗ[k] k) hy 1
  refine ⟨f, hfy, ?_⟩
  have hxW : x ∈ W := Submodule.subset_span (by simp)
  have hfx := congrArg (fun g => g ⟨x, hxW⟩) hf
  simpa using hfx

private theorem test_basechange_projective
    {R A P : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [AddCommGroup P] [Module R P] [Module.Projective R P] :
    Module.Projective A (TensorProduct R A P) := by
  obtain ⟨i, hi⟩ := (inferInstance : Module.Projective R P).out
  let F : Type _ := P →₀ R
  let j : F →ₗ[R] P := Finsupp.linearCombination R (id : P → P)
  let i' : TensorProduct R A P →ₗ[A] TensorProduct R A F :=
    TensorProduct.AlgebraTensorModule.map (LinearMap.id : A →ₗ[A] A) i
  let j' : TensorProduct R A F →ₗ[A] TensorProduct R A P :=
    TensorProduct.AlgebraTensorModule.map (LinearMap.id : A →ₗ[A] A) j
  apply Module.Projective.of_split i' j'
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a p => simp [i', j', j, hi p]
  | add z z' hz hz' => rw [map_add, hz, hz']; simp

private theorem test_basechange_span
    {R : Type u} {P : Type v} [CommRing R]
    [AddCommGroup P] [Module R P]
    (M : Submodule R P) (s : P)
    (hgen : Submodule.span R ({s} : Set P) ⊔ M = ⊤) :
    let A := R ⧸ Ring.jacobson R
    let PB := TensorProduct R A P
    let q : P →ₗ[R] PB := TensorProduct.mk R A P 1
    let N : Submodule A PB := Submodule.span A (q '' (M : Set P))
    Submodule.span A ({q s} : Set PB) ⊔ N = ⊤ := by
  dsimp
  let A := R ⧸ Ring.jacobson R
  let PB := TensorProduct R A P
  let q : P →ₗ[R] PB := TensorProduct.mk R A P 1
  let N : Submodule A PB := Submodule.span A (q '' (M : Set P))
  let W : Submodule A PB := Submodule.span A ({q s} : Set PB) ⊔ N
  apply top_unique
  intro z _
  have hall : ∀ z : PB, z ∈ W := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => exact W.zero_mem
    | tmul a p =>
        have hp : p ∈ Submodule.span R (({s} : Set P) ∪ (M : Set P)) := by
          rw [Submodule.span_union]
          simpa [hgen]
        have hqp : q p ∈ W := by
          refine Submodule.span_induction
            (p := fun x _ => q x ∈ W) ?_ ?_ ?_ ?_ hp
          · rintro x (rfl | hx)
            · exact Submodule.mem_sup_left (Submodule.subset_span (by simp))
            · exact Submodule.mem_sup_right (Submodule.subset_span ⟨x, hx, rfl⟩)
          · simpa [q] using W.zero_mem
          · intro x y _ _ hx hy
            simpa only [map_add] using W.add_mem hx hy
          · intro r x _ hx
            rw [map_smul]
            exact W.smul_mem (Ideal.Quotient.mk (Ring.jacobson R) r) hx
        have htmul : a ⊗ₜ[R] p = a • q p := by
          calc
            a ⊗ₜ[R] p = a • (1 ⊗ₜ[R] p) :=
              TensorProduct.tmul_eq_smul_one_tmul a p
            _ = a • q p := by rfl
        rw [htmul]
        exact W.smul_mem a hqp
    | add z z' hz hz' => exact W.add_mem hz hz'
  exact hall z

private theorem test_basechange_span_lift
    {R : Type u} {P : Type v} [CommRing R]
    [AddCommGroup P] [Module R P]
    (M : Submodule R P) (s : P) (z : TensorProduct R (R ⧸ Ring.jacobson R) P)
    (hz : z ∈ Submodule.span (R ⧸ Ring.jacobson R)
      ((TensorProduct.mk R (R ⧸ Ring.jacobson R) P 1) '' (M : Set P))) :
    ∃ m : P, m ∈ M ∧
      TensorProduct.mk R (R ⧸ Ring.jacobson R) P 1 m = z := by
  let A := R ⧸ Ring.jacobson R
  let PB := TensorProduct R A P
  let q : P →ₗ[R] PB := TensorProduct.mk R A P 1
  refine Submodule.span_induction (p := fun z _ => ∃ m : P, m ∈ M ∧ q m = z)
    ?_ ?_ ?_ ?_ hz
  · rintro z ⟨m, hm, rfl⟩
    exact ⟨m, hm, rfl⟩
  · exact ⟨0, M.zero_mem, by simp [q]⟩
  · rintro x y _ _ ⟨m, hm, rfl⟩ ⟨m', hm', rfl⟩
    exact ⟨m + m', M.add_mem hm hm', by simp [q]⟩
  · intro a z _ hz'
    rcases hz' with ⟨m, hm, hzm⟩
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective a
    exact ⟨r • m, M.smul_mem r hm, by
      rw [map_smul, hzm]
      exact (IsScalarTower.algebraMap_smul A r z).symm⟩

private theorem test_basechange_rank
    {R : Type u} {P : Type v} [CommRing R]
    [AddCommGroup P] [Module R P] [Module.Projective R P]
    (hP : HasInfiniteMaximalRank R P) :
    HasInfiniteMaximalRank (R ⧸ Ring.jacobson R)
      (TensorProduct R (R ⧸ Ring.jacobson R) P) := by
  intro m
  let A := R ⧸ Ring.jacobson R
  let PB := TensorProduct R A P
  let q := m.asIdeal.comap (algebraMap R A)
  letI : q.IsMaximal := Ideal.comap_isMaximal_of_surjective
      (Ideal.Quotient.mk (Ring.jacobson R)) Ideal.Quotient.mk_surjective
  letI : Algebra (Localization.AtPrime q) (Localization.AtPrime m.asIdeal) :=
    Localization.AtPrime.algebraOfLiesOver q m.asIdeal
  let LA := Localization.AtPrime m.asIdeal
  let LR := Localization.AtPrime q
  let e : LocalizedModule m.asIdeal.primeCompl PB ≃ₗ[LA]
      LA ⊗[LR] LocalizedModule q.primeCompl P :=
    LocalizedModule.equivTensorProduct _ _ ≪≫ₗ
      (TensorProduct.AlgebraTensorModule.cancelBaseChange R A _ _ P) ≪≫ₗ
      (TensorProduct.AlgebraTensorModule.cancelBaseChange R _ _ _ P).symm ≪≫ₗ
      (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl _ _)
        (LocalizedModule.equivTensorProduct _ P).symm)
  letI : Module.Projective LR (LocalizedModule q.primeCompl P) := inferInstance
  letI : Module.Free LR (LocalizedModule q.primeCompl P) :=
    Formalization.Books.Algebra.Unit85.projective_free_over_local_ring inferInstance
  have hbase := Module.rank_baseChange (R := LA) (S := LR)
      (M' := LocalizedModule q.primeCompl P)
  have hq : Cardinal.aleph0 ≤
      Module.rank LR (LocalizedModule q.primeCompl P) :=
    hP ⟨q, inferInstance⟩
  rw [e.rank_eq, hbase]
  exact Cardinal.aleph0_le_lift.mpr hq

private theorem test_finite_kernel
    {R : Type u} {P : Type v} [CommRing R] [IsNoetherianRing R]
    [AddCommGroup P] [Module R P]
    (M : Submodule R P) (x : P) {n : ℕ}
    (fs : Fin n → P →ₗ[R] R)
    (hgen : Submodule.span R ({x} : Set P) ⊔ M = ⊤) :
    Module.Finite R
      (P ⧸ (M ⊓ ⨅ i : Fin n, LinearMap.ker (fs i))) := by
  let K : Submodule R P := M ⊓ ⨅ i : Fin n, LinearMap.ker (fs i)
  have hqtop : Submodule.span R ({M.mkQ x} : Set (P ⧸ M)) = ⊤ := by
    have hmap : Submodule.map M.mkQ (Submodule.span R ({x} : Set P)) = ⊤ := by
      apply (Submodule.map_mkQ_eq_top M (Submodule.span R ({x} : Set P))).mpr
      simpa [sup_comm] using hgen
    simpa only [Submodule.map_span, Set.image_singleton] using hmap
  let q : R →ₗ[R] (P ⧸ M) :=
    LinearMap.toSpanSingleton R (P ⧸ M) (M.mkQ x)
  have hqsurj : Function.Surjective q := by
    intro z
    obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective M z
    have hy : y ∈ Submodule.span R (({x} : Set P) ∪ (M : Set P)) := by
      rw [Submodule.span_union]
      simpa [hgen]
    refine Submodule.span_induction
      (p := fun z _ => ∃ r, q r = M.mkQ z) ?_ ?_ ?_ ?_ hy
    · rintro z (rfl | hz)
      · exact ⟨1, by simp [q]⟩
      · refine ⟨0, ?_⟩
        simpa [q] using ((Submodule.Quotient.mk_eq_zero M).mpr hz).symm
    · exact ⟨0, by simp [q]⟩
    · rintro z z' _ _ ⟨a, ha⟩ ⟨b, hb⟩
      refine ⟨a + b, ?_⟩
      simp only [q, map_add, ha, hb]
    · intro a z _ ⟨b, hb⟩
      refine ⟨a * b, ?_⟩
      calc
        (q (a * b)) = a • q b := by simp [q, smul_smul]
        _ = a • M.mkQ z := by rw [hb]
  letI : Module.Finite R (P ⧸ M) := Module.Finite.of_surjective q hqsurj
  letI : Module.Finite R (Fin n → R) := inferInstance
  let f : P →ₗ[R] (P ⧸ M) × (Fin n → R) :=
    (M.mkQ).prod (LinearMap.pi fs)
  have hfK : LinearMap.ker f = K := by
    ext y
    change y ∈ LinearMap.ker ((M.mkQ).prod (LinearMap.pi fs)) ↔
      y ∈ (M ⊓ ⨅ i : Fin n, LinearMap.ker (fs i))
    constructor
    · intro h
      have h' : M.mkQ y = 0 ∧ (LinearMap.pi fs) y = 0 := by
        simpa [LinearMap.mem_ker, LinearMap.prod_apply] using h
      apply Submodule.mem_inf.mpr
      refine ⟨(Submodule.Quotient.mk_eq_zero M).mp h'.1, ?_⟩
      rw [Submodule.mem_iInf]
      intro i
      have hi := congrFun h'.2 i
      simpa using hi
    · intro h
      rcases (Submodule.mem_inf.mp h) with ⟨hy, hi⟩
      apply LinearMap.mem_ker.mpr
      apply Prod.ext
      · exact (Submodule.Quotient.mk_eq_zero M).mpr hy
      · ext i
        exact (Submodule.mem_iInf _).mp hi i
  let fQ : (P ⧸ K) →ₗ[R] (P ⧸ M) × (Fin n → R) :=
    K.liftQ f (by rw [hfK])
  have hfQinj : Function.Injective fQ := by
    apply LinearMap.ker_eq_bot.mp
    rw [Submodule.ker_liftQ_eq_bot' K f hfK.symm]
  exact Module.Finite.of_injective fQ hfQinj

example
    {L k N : Type*} [CommRing L] [Field k] [Algebra L k]
    [AddCommGroup N] [Module L N] : Module k (TensorProduct L k N) := by infer_instance

example
    {L k N : Type*} [CommRing L] [Field k] [Algebra L k]
    [AddCommGroup N] [Module L N] :
    Module k ((TensorProduct L k N) ⧸ (⊥ : Submodule k (TensorProduct L k N))) := by
  infer_instance

private theorem test_localized_exact_finite
    {A : Type u} {P : Type v} [CommRing A]
    [AddCommGroup P] [Module A P] (K : Submodule A P)
    [Module.Finite A (P ⧸ K)] (p : Ideal A) [p.IsPrime] :
    let L := Localization.AtPrime p
    let Ploc := LocalizedModule p.primeCompl P
    let Hloc := LocalizedModule p.primeCompl (P ⧸ K)
    let k := p.ResidueField
    let q : Ploc →ₗ[L] TensorProduct L k Ploc :=
      TensorProduct.mk L k Ploc 1
    let f : LocalizedModule p.primeCompl K →ₗ[L] Ploc :=
      LocalizedModule.map p.primeCompl K.subtype
    let g : Ploc →ₗ[L] Hloc :=
      LocalizedModule.map p.primeCompl K.mkQ
    Module.Finite k
      ((TensorProduct L k Ploc) ⧸ LinearMap.range (f.baseChange k)) := by
  dsimp
  let L := Localization.AtPrime p
  let Ploc := LocalizedModule p.primeCompl P
  let Hloc := LocalizedModule p.primeCompl (P ⧸ K)
  let k := p.ResidueField
  let f : LocalizedModule p.primeCompl K →ₗ[L] Ploc :=
    LocalizedModule.map p.primeCompl K.subtype
  let g : Ploc →ₗ[L] Hloc :=
    LocalizedModule.map p.primeCompl K.mkQ
  have hfg : Function.Exact f g := by
    exact LocalizedModule.map_exact p.primeCompl K.subtype K.mkQ
      (LinearMap.exact_subtype_mkQ K)
  have hgs : Function.Surjective g :=
    LocalizedModule.map_surjective p.primeCompl K.mkQ
      (Submodule.mkQ_surjective K)
  have hfg' : Function.Exact (f.baseChange k) (g.baseChange k) := by
    simpa only [LinearMap.baseChange_eq_ltensor] using lTensor_exact k hfg hgs
  have hgs' : Function.Surjective (g.baseChange k) :=
    LinearMap.baseChange_surjective k hgs
  letI : Module.Finite L Hloc := Module.Finite.of_isLocalizedModule
    p.primeCompl (LocalizedModule.mkLinearMap p.primeCompl (P ⧸ K))
  letI : Module.Finite k (TensorProduct L k Hloc) := Module.Finite.base_change L k Hloc
  let q : TensorProduct L k Ploc →ₗ[k] TensorProduct L k Hloc := g.baseChange k
  have hqker : LinearMap.ker q = LinearMap.range (f.baseChange k) := by
    exact hfg'.linearMap_ker_eq
  let qbar : ((TensorProduct L k Ploc) ⧸ LinearMap.range (f.baseChange k)) →ₗ[k]
      TensorProduct L k Hloc :=
    (LinearMap.range (f.baseChange k)).liftQ q (by rw [hqker])
  have hqbar_surj : Function.Surjective qbar := by
    intro z
    obtain ⟨y, rfl⟩ := hgs' z
    exact ⟨Submodule.mkQ (LinearMap.range (f.baseChange k)) y, by simp [qbar, q]⟩
  have hqbar_inj : Function.Injective qbar := by
    intro x y hxy
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective (LinearMap.range (f.baseChange k)) x
    obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective (LinearMap.range (f.baseChange k)) y
    apply (Submodule.Quotient.eq (LinearMap.range (f.baseChange k))).mpr
    have hz : q (x - y) = 0 := by
      rw [map_sub, sub_eq_zero]
      simpa [qbar] using hxy
    obtain ⟨z, hz⟩ := (hfg' (x - y)).mp hz
    exact ⟨z, by simpa [map_sub] using hz⟩
  let e : ((TensorProduct L k Ploc) ⧸ LinearMap.range (f.baseChange k)) ≃ₗ[k]
      TensorProduct L k Hloc := LinearEquiv.ofBijective qbar ⟨hqbar_inj, hqbar_surj⟩
  exact Module.Finite.equiv e.symm

set_option maxHeartbeats 1000000 in
private theorem test_localized_range_le
    {A : Type u} {P : Type v} [CommRing A]
    [AddCommGroup P] [Module A P] (K : Submodule A P)
    (p : Ideal A) [p.IsPrime]
    (s : P) (m : P)
    (hnot : ∀ y : P, y ∈ K →
      (TensorProduct.mk (Localization.AtPrime p) p.ResidueField
        (LocalizedModule p.primeCompl P) 1)
          (LocalizedModule.mkLinearMap p.primeCompl P y) ∈
        Submodule.span p.ResidueField
          ({(TensorProduct.mk (Localization.AtPrime p) p.ResidueField
            (LocalizedModule p.primeCompl P) 1)
            (LocalizedModule.mkLinearMap p.primeCompl P (s + m))} :
            Set (TensorProduct (Localization.AtPrime p) p.ResidueField
              (LocalizedModule p.primeCompl P)))) :
    LinearMap.range ((LocalizedModule.map p.primeCompl K.subtype).baseChange
      p.ResidueField) ≤
      Submodule.span p.ResidueField
        ({(TensorProduct.mk (Localization.AtPrime p) p.ResidueField
          (LocalizedModule p.primeCompl P) 1)
          (LocalizedModule.mkLinearMap p.primeCompl P (s + m))} :
          Set (TensorProduct (Localization.AtPrime p) p.ResidueField
            (LocalizedModule p.primeCompl P))) := by
  let L := Localization.AtPrime p
  let Ploc := LocalizedModule p.primeCompl P
  let k := p.ResidueField
  let f : LocalizedModule p.primeCompl K →ₗ[L] Ploc :=
    LocalizedModule.map p.primeCompl K.subtype
  let q : Ploc →ₗ[L] TensorProduct L k Ploc := TensorProduct.mk L k Ploc 1
  let v : TensorProduct L k Ploc := q (LocalizedModule.mkLinearMap p.primeCompl P (s + m))
  let W : Submodule k (TensorProduct L k Ploc) := Submodule.span k ({v} : Set _)
  have hu (u : LocalizedModule p.primeCompl K) : q (f u) ∈ W := by
    obtain ⟨⟨y, d⟩, rfl⟩ := IsLocalizedModule.mk'_surjective
      p.primeCompl (LocalizedModule.mkLinearMap p.primeCompl K) u
    have hmk' :
        IsLocalizedModule.mk' (LocalizedModule.mkLinearMap p.primeCompl P) (y : P) d =
          IsLocalization.mk' (Localization.AtPrime p) (1 : A) d •
            IsLocalizedModule.mk' (LocalizedModule.mkLinearMap p.primeCompl P)
              (y : P) (1 : p.primeCompl) := by
      simpa using (IsLocalizedModule.mk'_smul_mk'
        (f := LocalizedModule.mkLinearMap p.primeCompl P)
        (Localization.AtPrime p) 1 (y : P) d 1).symm
    have hy : q (LocalizedModule.mkLinearMap p.primeCompl P (y : P)) ∈ W := by
      exact hnot (y : P) y.property
    change q (f (IsLocalizedModule.mk' (LocalizedModule.mkLinearMap
      p.primeCompl K) y d)) ∈ W
    have hf : f (IsLocalizedModule.mk' (LocalizedModule.mkLinearMap
        p.primeCompl K) y d) =
        IsLocalizedModule.mk' (LocalizedModule.mkLinearMap p.primeCompl P)
          (y : P) d := by
      change IsLocalizedModule.map p.primeCompl
        (LocalizedModule.mkLinearMap p.primeCompl K)
        (LocalizedModule.mkLinearMap p.primeCompl P) K.subtype
          (IsLocalizedModule.mk' (LocalizedModule.mkLinearMap p.primeCompl K) y d) = _
      exact IsLocalizedModule.map_mk' _ _ _ _ _ _
    rw [hf]
    rw [hmk', map_smul]
    rw [← algebraMap_smul k]
    exact Submodule.smul_mem W _ (by simpa using hy)
  rintro z ⟨w, rfl⟩
  change (f.baseChange k) w ∈ W
  induction w using TensorProduct.induction_on with
  | zero => exact W.zero_mem
  | tmul a u =>
      rw [LinearMap.baseChange_tmul, TensorProduct.tmul_eq_smul_one_tmul]
      exact Submodule.smul_mem W a (hu u)
  | add z z' hz hz' => rw [map_add]; exact W.add_mem hz hz'

private theorem test_exists_global_element
    {A : Type u} {P : Type v} [CommRing A]
    [AddCommGroup P] [Module A P] (K : Submodule A P)
    (p : Ideal A) [p.IsPrime]
    (s m : P)
    (hQ : Cardinal.aleph0 ≤ Module.rank p.ResidueField
      (TensorProduct (Localization.AtPrime p) p.ResidueField
        (LocalizedModule p.primeCompl P)))
    (hfin : Module.Finite p.ResidueField
      ((TensorProduct (Localization.AtPrime p) p.ResidueField
        (LocalizedModule p.primeCompl P)) ⧸
        LinearMap.range ((LocalizedModule.map p.primeCompl K.subtype).baseChange
          p.ResidueField))) :
    ∃ y : P, y ∈ K ∧
      (TensorProduct.mk (Localization.AtPrime p) p.ResidueField
        (LocalizedModule p.primeCompl P) 1)
          (LocalizedModule.mkLinearMap p.primeCompl P y) ∉
        Submodule.span p.ResidueField
          ({(TensorProduct.mk (Localization.AtPrime p) p.ResidueField
            (LocalizedModule p.primeCompl P) 1)
            (LocalizedModule.mkLinearMap p.primeCompl P (s + m))} :
            Set (TensorProduct (Localization.AtPrime p) p.ResidueField
              (LocalizedModule p.primeCompl P))) := by
  let L := Localization.AtPrime p
  let Ploc := LocalizedModule p.primeCompl P
  let k := p.ResidueField
  let f : LocalizedModule p.primeCompl K →ₗ[L] Ploc :=
    LocalizedModule.map p.primeCompl K.subtype
  let q : Ploc →ₗ[L] TensorProduct L k Ploc := TensorProduct.mk L k Ploc 1
  let qglobal : P →ₗ[A] TensorProduct L k Ploc :=
    q.restrictScalars A |>.comp (LocalizedModule.mkLinearMap p.primeCompl P)
  let v := qglobal (s + m)
  let W : Submodule k (TensorProduct L k Ploc) := Submodule.span k ({v} : Set _)
  by_contra h
  push_neg at h
  have hle : LinearMap.range (f.baseChange k) ≤ W := by
    apply test_localized_range_le K p s m
    intro y hy
    simpa [qglobal, q, v, W] using h y hy
  let qbar : ((TensorProduct L k Ploc) ⧸ LinearMap.range (f.baseChange k)) →ₗ[k]
      (TensorProduct L k Ploc) ⧸ W :=
    (LinearMap.range (f.baseChange k)).liftQ W.mkQ (by
      rw [LinearMap.range_le_iff_comap]
      apply top_unique
      intro x hx
      exact (Submodule.Quotient.mk_eq_zero W).mpr (hle ⟨x, rfl⟩))
  letI : Module.Finite k
      ((TensorProduct L k Ploc) ⧸ LinearMap.range (f.baseChange k)) := hfin
  have hqbar_surj : Function.Surjective qbar := by
    intro z
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective W z
    exact ⟨Submodule.mkQ (LinearMap.range (f.baseChange k)) x, rfl⟩
  letI : Module.Finite k ((TensorProduct L k Ploc) ⧸ W) :=
    Module.Finite.of_surjective qbar hqbar_surj
  letI : Module.Finite k W := inferInstance
  letI : Module.Finite k (TensorProduct L k Ploc) :=
    Module.Finite.of_submodule_quotient W
  exact (not_lt_of_ge hQ) (Module.rank_lt_aleph0 k (TensorProduct L k Ploc))

private theorem test_good_element_noetherian
    {A : Type u} {P : Type v} [CommRing A] [IsNoetherianRing A]
    [AddCommGroup P] [Module A P] [Module.Projective A P]
    (hP : HasInfiniteMaximalRank A P) (s : P) (M : Submodule A P)
    (hgen : Submodule.span A ({s} : Set P) ⊔ M = ⊤) :
    ∃ m : P, m ∈ M ∧ ∃ φ : P →ₗ[A] A, φ (s + m) = 1 := by
  let states : Set (Ideal A) := {I |
    ∃ n : ℕ, ∃ m : P, m ∈ M ∧ ∃ fs : Fin n → P →ₗ[A] A,
      I = Ideal.span (Set.range (fun i => fs i (s + m)))}
  have hstates : states.Nonempty := by
    refine ⟨⊥, ?_⟩
    refine ⟨0, 0, Submodule.zero_mem M, (fun i => Fin.elim0 i), ?_⟩
    simp [states]
  obtain ⟨I, hI, hmax⟩ :=
    (set_has_maximal_iff_noetherian (R := A) (M := A)).mpr inferInstance
      states hstates
  rcases hI with ⟨n, m, hm, fs, rfl⟩
  by_contra htopGood
  have hnotop : Ideal.span (Set.range (fun i => fs i (s + m))) ≠ ⊤ := by
    intro htop
    have hone : (1 : A) ∈ Ideal.span (Set.range (fun i => fs i (s + m))) := by
      rw [htop]
      exact Submodule.mem_top
    obtain ⟨c, hc⟩ := Ideal.mem_span_range_iff_exists_fun.mp hone
    apply htopGood
    refine ⟨m, hm, ∑ i, c i • fs i, ?_⟩
    simpa [LinearMap.sum_apply, smul_eq_mul] using hc
  obtain ⟨p, hp, hIp⟩ := Ideal.ne_top_iff_exists_maximal.mp hnotop
  letI : p.IsMaximal := hp
  let K : Submodule A P := M ⊓ ⨅ i : Fin n, LinearMap.ker (fs i)
  letI : Module.Finite A (P ⧸ K) := by
    simpa [K] using test_finite_kernel M s fs hgen
  have hQ : Cardinal.aleph0 ≤ Module.rank p.ResidueField
      (TensorProduct (Localization.AtPrime p) p.ResidueField
        (LocalizedModule p.primeCompl P)) := by
    letI : Module.Projective (Localization.AtPrime p)
        (LocalizedModule p.primeCompl P) := inferInstance
    letI : Module.Free (Localization.AtPrime p)
        (LocalizedModule p.primeCompl P) :=
      Formalization.Books.Algebra.Unit85.projective_free_over_local_ring inferInstance
    have hr := Module.rank_baseChange (R := p.ResidueField)
      (S := Localization.AtPrime p)
      (M' := LocalizedModule p.primeCompl P)
    rw [hr]
    simpa using hP ⟨p, hp⟩
  have hfin := test_localized_exact_finite K p
  obtain ⟨y, hyK, hyind⟩ := test_exists_global_element K p s m hQ hfin
  obtain ⟨fres, hfres_y, hfres_sm⟩ :=
    test_functional
      ((TensorProduct.mk (Localization.AtPrime p) p.ResidueField
        (LocalizedModule p.primeCompl P) 1)
        (LocalizedModule.mkLinearMap p.primeCompl P (s + m)))
      ((TensorProduct.mk (Localization.AtPrime p) p.ResidueField
        (LocalizedModule p.primeCompl P) 1)
        (LocalizedModule.mkLinearMap p.primeCompl P y)) hyind
  let qglobal : P →ₗ[A] p.ResidueField :=
    fres.restrictScalars A |>.comp
      ((TensorProduct.mk (Localization.AtPrime p) p.ResidueField
        (LocalizedModule p.primeCompl P) 1).restrictScalars A |>.comp
        (LocalizedModule.mkLinearMap p.primeCompl P))
  have hqglobal_y : qglobal y = 1 := by
    simpa [qglobal] using hfres_y
  have hqglobal_sm : qglobal (s + m) = 0 := by
    simpa [qglobal] using hfres_sm
  obtain ⟨φ, hφ⟩ := Module.projective_lifting_property
    (Algebra.linearMap A p.ResidueField) qglobal
    p.algebraMap_residueField_surjective
  have hφ_y : algebraMap A p.ResidueField (φ y) = 1 := by
    have h := congrArg (fun g : P →ₗ[A] p.ResidueField => g y) hφ
    simpa [qglobal, LinearMap.comp_apply] using h.trans hqglobal_y
  have hφ_sm : algebraMap A p.ResidueField (φ (s + m)) = 0 := by
    have h := congrArg (fun g : P →ₗ[A] p.ResidueField => g (s + m)) hφ
    simpa [qglobal, LinearMap.comp_apply] using h.trans hqglobal_sm
  have hφ_sum : algebraMap A p.ResidueField (φ (s + m + y)) = 1 := by
    rw [map_add, map_add, hφ_sm, hφ_y]
    abel
  have hsum_not_mem : φ (s + m + y) ∉ p := by
    intro hmem
    have hz := Ideal.algebraMap_residueField_eq_zero.mpr hmem
    rw [hφ_sum] at hz
    exact one_ne_zero hz
  let fs' : Fin (n + 1) → P →ₗ[A] A :=
    Fin.cases φ (fun i => fs i)
  let I' : Ideal A := Ideal.span (Set.range (fun i => fs' i (s + (m + y))))
  have hI'state : I' ∈ states := by
    refine ⟨n + 1, m + y, M.add_mem hm (Submodule.mem_inf.mp hyK).1, fs', rfl⟩
  have hker_y : ∀ i : Fin n, fs i y = 0 := by
    intro i
    exact LinearMap.mem_ker.mp
      ((Submodule.mem_iInf _).mp (Submodule.mem_inf.mp hyK).2 i)
  have hle : Ideal.span (Set.range (fun i => fs i (s + m))) ≤ I' := by
    apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    apply Ideal.subset_span
    refine ⟨Fin.succ i, ?_⟩
    simp [fs', hker_y, add_assoc, add_left_comm, add_comm]
  have hnle : ¬ I' ≤ Ideal.span (Set.range (fun i => fs i (s + m))) := by
    intro hle'
    have hmemp : φ (s + m + y) ∈ I' := by
      apply Ideal.subset_span
      exact ⟨0, by simp [fs', add_assoc]⟩
    exact hsum_not_mem (hIp (hle' hmemp))
  have hlt : Ideal.span (Set.range (fun i => fs i (s + m))) < I' := by
    exact lt_of_le_of_ne hle (by
      intro heq
      apply hnle
      rw [← heq]
      )
  exact (hmax I' hI'state) hlt

private theorem test_good_element
    {R : Type u} {P : Type v} [CommRing R]
    (hR : IsNoetherianRing (R ⧸ Ring.jacobson R))
    [AddCommGroup P] [Module R P] [Module.Projective R P]
    (hP : HasInfiniteMaximalRank R P) (s : P) (M : Submodule R P)
    (hgen : Submodule.span R ({s} : Set P) ⊔ M = ⊤) :
    ∃ m : P, m ∈ M ∧
      IsComplemented (Submodule.span R ({s + m} : Set P)) ∧
        Nonempty (R ≃ₗ[R] Submodule.span R ({s + m} : Set P)) := by
  let A := R ⧸ Ring.jacobson R
  let PB := TensorProduct R A P
  let q : P →ₗ[R] PB := TensorProduct.mk R A P 1
  let N : Submodule A PB := Submodule.span A (q '' (M : Set P))
  letI : IsNoetherianRing A := hR
  letI : Module.Projective A PB :=
    test_basechange_projective (R := R) (A := A) (P := P)
  have hgenPB : Submodule.span A ({q s} : Set PB) ⊔ N = ⊤ := by
    change Submodule.span A ({q s} : Set PB) ⊔
      Submodule.span A (q '' (M : Set P)) = ⊤
    simpa [A, PB, q] using test_basechange_span M s hgen
  obtain ⟨z, hz, φ, hφ⟩ := test_good_element_noetherian
    (A := A) (P := PB) (test_basechange_rank hP) (q s) N hgenPB
  obtain ⟨m, hm, hqm⟩ := test_basechange_span_lift M s z (by
    simpa [N] using hz)
  have hqm' : q m = z := by
    change (1 ⊗ₜ[R] m) = z
    exact hqm
  let φR : P →ₗ[R] A := φ.restrictScalars R |>.comp q
  obtain ⟨ψ, hψ⟩ := Module.projective_lifting_property
    (Algebra.linearMap R A) φR Ideal.Quotient.mk_surjective
  let x : P := s + m
  have hφx : φR x = 1 := by
    have hqsm : q x = q s + z := by
      dsimp [x]
      rw [map_add, hqm']
    have hφq : φ (q x) = 1 := by rw [hqsm]; exact hφ
    simpa [φR, LinearMap.comp_apply] using hφq
  have hψxmod : algebraMap R A (ψ x) = 1 := by
    have hh := congrArg (fun g : P →ₗ[R] A => g x) hψ
    simpa [φR, x, LinearMap.comp_apply] using hh.trans hφx
  have hψxquot : Ideal.Quotient.mk (Ring.jacobson R) (ψ x) = 1 := by
    simpa [A] using hψxmod
  have hunit_quot : IsUnit (Ideal.Quotient.mk (Ring.jacobson R) (ψ x)) := by
    rw [hψxquot]
    exact isUnit_one
  have hunit : IsUnit (ψ x) :=
    Formalization.Books.Algebra.Unit19.isUnit_of_isUnit_quotient_of_le_jacobson
      (Ring.jacobson R) le_rfl hunit_quot
  let χ : P →ₗ[R] R := (↑(IsUnit.unit hunit).inv : R) • ψ
  have hχx : χ x = 1 := by
    simpa [χ, LinearMap.smul_apply, mul_comm] using hunit.val_inv_mul
  let S : Submodule R P := Submodule.span R ({x} : Set P)
  let ix0 : R →ₗ[R] P := LinearMap.toSpanSingleton R P x
  let ix : R →ₗ[R] S := ix0.codRestrict S (by
    intro r
    exact Submodule.smul_mem S r (Submodule.subset_span (by simp)))
  have hχix (r : R) : χ (ix r : P) = r := by
    change χ (r • x) = r
    rw [map_smul, hχx]
    simp [smul_eq_mul]
  let pr : P →ₗ[R] S := ix.comp χ
  have hpr : ∀ y : S, pr y = y := by
    intro y
    apply Subtype.ext
    change (ix (χ (y : P)) : P) = (y : P)
    refine Submodule.span_induction
      (p := fun z _ => (ix (χ z) : P) = z) ?_ ?_ ?_ ?_ y.property
    · intro z hz
      have hz' : z = x := Set.mem_singleton_iff.mp hz
      subst z
      rw [hχx]
      change (1 : R) • x = x
      simp
    · simp
    · intro z z' _ _ hz hz'
      change (ix (χ (z + z')) : P) = z + z'
      rw [map_add, map_add]
      change (ix (χ z) : P) + (ix (χ z') : P) = z + z'
      exact congrArg₂ (· + ·) hz hz'
    · intro r z _ hz
      change (ix (χ (r • z)) : P) = r • z
      rw [map_smul, map_smul]
      change r • (ix (χ z) : P) = r • z
      exact congrArg (fun w : P => r • w) hz
  have hcomp : IsComplemented S :=
    ⟨LinearMap.ker pr, LinearMap.isCompl_of_proj hpr⟩
  have hix_inj : Function.Injective ix := by
    intro a b hab
    have := congrArg (fun y : S => χ (y : P)) hab
    simpa [hχix] using this
  have hix_surj : Function.Surjective ix := by
    intro y
    refine ⟨χ (y : P), ?_⟩
    simpa [pr] using hpr y
  refine ⟨m, hm, hcomp, ?_⟩
  exact ⟨LinearEquiv.ofBijective ix ⟨hix_inj, hix_surj⟩⟩

private theorem test_hasInfinite_product
    {R : Type u} {P : Type v} {F : Type u} [CommRing R]
    [AddCommGroup P] [Module R P] [Module.Projective R P]
    [AddCommGroup F] [Module R F] [Module.Finite R F]
    (hP : HasInfiniteMaximalRank R P) :
    HasInfiniteMaximalRank R (F × P) := by
  intro m
  let L := Localization.AtPrime m.asIdeal
  let S := m.asIdeal.primeCompl
  let e : LocalizedModule S (F × P) ≃ₗ[L]
      LocalizedModule S F × LocalizedModule S P :=
    IsLocalizedModule.linearEquiv S (LocalizedModule.mkLinearMap S (F × P))
      ((LocalizedModule.mkLinearMap S F).prodMap
        (LocalizedModule.mkLinearMap S P)) |>.extendScalarsOfIsLocalization S L
  let i : LocalizedModule S P →ₗ[L] LocalizedModule S (F × P) :=
    e.symm.toLinearMap.comp (LinearMap.inr L
      (LocalizedModule S F) (LocalizedModule S P))
  have hi : Function.Injective i := by
    intro x y hxy
    simpa [i] using congrArg e hxy
  have hr := i.lift_rank_le_of_injective hi
  have hq := hP m
  have hr' : Module.rank L (LocalizedModule S P) ≤
      Module.rank L (LocalizedModule S (F × P)) :=
    Cardinal.lift_le.mp hr
  exact hq.trans hr'

private theorem test_complement_infinite
    {R : Type u} {P : Type v} [CommRing R]
    [AddCommGroup P] [Module R P] [Module.Projective R P]
    (hP : HasInfiniteMaximalRank R P)
    (K C : Submodule R (R × P)) (hKC : IsCompl K C)
    [Module.Finite R K] :
    HasInfiniteMaximalRank R C := by
  intro m
  by_contra hC
  have hlt : Module.rank (Localization.AtPrime m.asIdeal)
      (LocalizedModule m.asIdeal.primeCompl C) < Cardinal.aleph0 :=
    lt_of_not_ge hC
  let L := Localization.AtPrime m.asIdeal
  let S := m.asIdeal.primeCompl
  let projC : (R × P) →ₗ[R] C := C.projectionOnto K hKC.symm
  letI : Module.Projective R C := Module.Projective.of_split C.subtype projC (by
    apply LinearMap.ext
    intro c
    exact C.projectionOnto_apply_left hKC.symm c)
  letI : Module.Projective L (LocalizedModule S C) := inferInstance
  letI : Module.Free L (LocalizedModule S C) :=
    Formalization.Books.Algebra.Unit85.projective_free_over_local_ring
      (R := L) (P := LocalizedModule S C) inferInstance
  letI : Module.Finite L (LocalizedModule S C) :=
    Module.rank_lt_aleph0_iff.mp hlt
  letI : Module.Finite L (LocalizedModule S K) :=
    Module.Finite.of_isLocalizedModule S (LocalizedModule.mkLinearMap S K)
  let eProd : LocalizedModule S (K × C) ≃ₗ[L]
      LocalizedModule S K × LocalizedModule S C :=
    IsLocalizedModule.linearEquiv S (LocalizedModule.mkLinearMap S (K × C))
      ((LocalizedModule.mkLinearMap S K).prodMap
        (LocalizedModule.mkLinearMap S C)) |>.extendScalarsOfIsLocalization S L
  letI : Module.Finite L (LocalizedModule S (K × C)) :=
    Module.Finite.equiv eProd.symm
  let eKC : (K × C) ≃ₗ[R] (R × P) :=
    Submodule.prodEquivOfIsCompl K C hKC
  let eLoc : LocalizedModule S (K × C) ≃ₗ[L]
      LocalizedModule S (R × P) :=
    IsLocalizedModule.mapEquiv S (LocalizedModule.mkLinearMap S (K × C))
      (LocalizedModule.mkLinearMap S (R × P)) L eKC
  letI : Module.Finite L (LocalizedModule S (R × P)) :=
    Module.Finite.equiv eLoc
  exact (not_lt_of_ge (test_hasInfinite_product (F := R) hP m)) (Module.rank_lt_aleph0 L
    (LocalizedModule S (R × P)))

set_option maxHeartbeats 1000000 in
private theorem test_rank_one_step
    {R : Type u} {P : Type v} [CommRing R]
    [AddCommGroup P] [Module R P] [Module.Projective R P]
    (hR : IsNoetherianRing (R ⧸ Ring.jacobson R))
    (hP : HasInfiniteMaximalRank R P)
    (K : Submodule R (R × P)) (hKcomp : IsComplemented K)
    (hKfin : Module.Finite R K) (hKfree : Module.Free R K)
    (s : P) (hs : (0, s) ∈ K) :
    ∃ L : Submodule R P, s ∈ L ∧ IsComplemented L ∧
      Module.Finite R L ∧ Module.IsStablyFree R L := by
  letI : Module.Finite R K := hKfin
  letI : Module.Free R K := hKfree
  obtain ⟨C, hKC⟩ := hKcomp
  let projC : (R × P) →ₗ[R] C := C.projectionOnto K hKC.symm
  letI : Module.Projective R C := Module.Projective.of_split C.subtype projC (by
    apply LinearMap.ext
    intro c
    exact C.projectionOnto_apply_left hKC.symm c)
  have hCP : HasInfiniteMaximalRank R C :=
    test_complement_infinite hP K C hKC
  let eKC : (K × C) ≃ₗ[R] (R × P) :=
    Submodule.prodEquivOfIsCompl K C hKC
  let π : (R × P) →ₗ[R] C :=
    (LinearMap.snd R K C).comp eKC.symm.toLinearMap
  let inrP : P →ₗ[R] (R × P) := LinearMap.inr R R P
  let t : C := π (1, 0)
  let MC : Submodule R C := LinearMap.range (π.comp inrP)
  have hπsurj : Function.Surjective π := by
    intro c
    refine ⟨eKC (0, c), ?_⟩
    simp [π, eKC]
  have hgenC : Submodule.span R ({t} : Set C) ⊔ MC = ⊤ := by
    apply top_unique
    intro c _
    obtain ⟨⟨a, p⟩, hp⟩ := hπsurj c
    have hsplit (a : R) (p : P) :
        π (a, p) = a • t + π (0, p) := by
      rw [show (a, p) = a • (1, 0) + (0, p) by ext <;> simp,
        map_add, map_smul]
    rw [← hp, hsplit]
    apply Submodule.add_mem
    · exact Submodule.smul_mem _ a
        (Submodule.mem_sup_left (Submodule.subset_span (Set.mem_singleton t)))
    · apply Submodule.mem_sup_right
      exact ⟨p, by simp [MC, inrP]⟩
  obtain ⟨mc, hmc, hU, ⟨eU⟩⟩ :=
    test_good_element hR hCP t MC hgenC
  obtain ⟨p, hp⟩ := hmc
  let y : C := t + mc
  let U : Submodule R C := Submodule.span R ({y} : Set C)
  have hU' : IsComplemented U := by simpa [U, y] using hU
  have hπone : π (1, p) = y := by
    have hp' : π (0, p) = mc := by simpa [inrP] using hp
    calc
      π (1, p) = π ((1, 0) + (0, p)) := by congr 1 <;> ext <;> simp
      _ = π (1, 0) + π (0, p) := map_add π (1, 0) (0, p)
      _ = t + mc := by rw [hp']
      _ = y := rfl
  obtain ⟨C₂, hUC₂⟩ := hU'
  let proj₂ : C →ₗ[R] C₂ := C₂.projectionOnto U hUC₂.symm
  let π' : P →ₗ[R] C₂ := proj₂.comp (π.comp inrP)
  have hπ'surj : Function.Surjective π' := by
    intro z
    obtain ⟨⟨a, p₀⟩, hp₀⟩ := hπsurj (z : C)
    have hsplit (a : R) (p : P) :
        π (a, p) = a • t + π (0, p) := by
      rw [show (a, p) = a • (1, 0) + (0, p) by ext <;> simp,
        map_add, map_smul]
    have heq : (z : C) = a • y + π (0, p₀ - a • p) := by
      have hp' : π (0, p) = mc := by simpa [inrP] using hp
      rw [← hp₀, hsplit]
      dsimp [y]
      have hpairs : (0, p₀ - a • p) = (0, p₀) - a • (0, p) := by
        ext <;> simp
      have hdiff := congrArg π hpairs
      rw [map_sub, map_smul, hp'] at hdiff
      rw [hdiff]
      abel
    have hy0 : proj₂ y = 0 :=
      C₂.projectionOnto_apply_of_mem_right hUC₂.symm
        (Submodule.subset_span (Set.mem_singleton y))
    have hproj2 (z : C₂) : proj₂ (z : C) = z :=
      C₂.projectionOnto_apply_left hUC₂.symm z
    refine ⟨p₀ - a • p, ?_⟩
    change proj₂ (π (0, p₀ - a • p)) = z
    rw [← hproj2 z, heq, map_add, map_smul, hy0]
    simp
  letI : Module.Projective R C₂ := Module.Projective.of_split C₂.subtype proj₂ (by
    apply LinearMap.ext
    intro z
    exact C₂.projectionOnto_apply_left hUC₂.symm z)
  obtain ⟨g, hg⟩ := Module.projective_lifting_property
    π' (LinearMap.id : C₂ →ₗ[R] C₂) hπ'surj
  let L : Submodule R P := LinearMap.ker π'
  let fL : P →ₗ[R] L :=
    (LinearMap.id - g.comp π').codRestrict L (by
      intro q
      apply LinearMap.mem_ker.mpr
      simp only [LinearMap.id_apply, LinearMap.sub_apply, LinearMap.comp_apply]
      rw [map_sub]
      have hh : π' (g (π' q)) = π' q := by
        have hh0 := congrArg (fun f : C₂ →ₗ[R] C₂ => f (π' q)) hg
        simpa only [LinearMap.comp_apply, LinearMap.id_apply] using hh0
      rw [hh]
      simp)
  have hfL : ∀ z : L, fL z = z := by
    intro z
    apply Subtype.ext
    change (z : P) - g (π' z) = (z : P)
    rw [LinearMap.mem_ker.mp z.property]
    simp
  have hLcomp : IsComplemented L :=
    ⟨LinearMap.ker fL, LinearMap.isCompl_of_proj hfL⟩
  have hsL : s ∈ L := by
    apply LinearMap.mem_ker.mpr
    have hπs : π (0, s) = 0 := by
      change (eKC.symm (0, s)).2 = 0
      exact (Submodule.prodEquivOfIsCompl_symm_apply_snd_eq_zero K C hKC).mpr hs
    simp [π', inrP, hπs]
  refine ⟨L, hsL, hLcomp, ?_, ?_⟩
  · exact Module.Finite.of_surjective π' hπ'surj
  · sorry

end

end Formalization.Books.MoreAlgebra.Unit129
