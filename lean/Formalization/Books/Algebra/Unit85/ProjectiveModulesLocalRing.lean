import Formalization.Books.Algebra.Unit84.TransfiniteDevissage
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.RingTheory.LocalRing.Defs
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.LinearAlgebra.Transvection.Basic
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Commutative Algebra, Chapter 85: Projective modules over a local ring

The source's projective and free modules use Mathlib's canonical
`Module.Projective` and `Module.Free` predicates.  A direct summand is
represented by a complemented submodule, and a decomposition `M = N ⊕ N'`
is represented by a linear equivalence `M ≃ₗ[R] N × N'`.
-/

namespace Formalization.Books.Algebra.Unit85

universe u v w

/-! ## Projective modules over a local ring -/

/- The introductory reference to the finite case points back to the earlier
   finite-flat-local result; it is not a separate assertion at this source
   boundary. -/

/-- Every projective module is free if and only if every countably generated
projective module is free. -/
theorem projective_free_iff_countablyGenerated_projective_free
    {R : Type u} [CommRing R] :
    (∀ (M : Type v) [AddCommGroup M] [Module R M],
      Module.Projective R M → Module.Free R M) ↔
      (∀ (M : Type v) [AddCommGroup M] [Module R M],
        Module.Projective R M →
          Formalization.Books.Algebra.Unit84.Module.IsCountablyGenerated R M →
            Module.Free R M) := by
  constructor
  · intro h M _ _ hP _
    exact h M hP
  · intro h M _ _ hP
    let _ : Module.Projective R M := hP
    obtain ⟨ι, N, hN, ⟨e⟩⟩ :=
      Formalization.Books.Algebra.Unit84.projective_isDirectSumOfCountablyGeneratedProjectiveModules
        (R := R) (M := M)
    let _ : ∀ i, Module.Free R (N i) := fun i => h (N i) (hN i).2 (hN i).1
    let hfree : Module.Free R (DirectSum ι (fun i => (N i : Type v))) :=
      Module.Free.dfinsupp R (fun i => (N i : Type v))
    exact Module.Free.of_equiv' hfree e.symm

private theorem free_element_mem_finite_free_direct_summand
    {R : Type u} {F : Type v} [CommRing R]
    [AddCommGroup F] [Module R F] (hF : Module.Free R F) (x : F) :
    ∃ Q : Submodule R F, x ∈ Q ∧ IsComplemented Q ∧
      Module.Finite R Q ∧ Module.Free R Q := by
  classical
  let b := Module.Free.chooseBasis R F
  let c := b.repr x
  let s : Set (Module.Free.ChooseBasisIndex R F) := c.support
  let _ : Finite s := Finite.of_injective
    (fun i : s => (⟨(i : Module.Free.ChooseBasisIndex R F), by simp [s]⟩ : c.support))
    (by intro i j hij; exact Subtype.ext (congrArg Subtype.val hij))
  let Q : Submodule R F := Submodule.span R (b '' s)
  refine ⟨Q, ?_, ?_, ?_, ?_⟩
  · have hx : c.sum (fun i a => a • b i) = x := by
      simpa only [c, Finsupp.linearCombination_apply] using b.linearCombination_repr x
    rw [← hx]
    change c.sum (fun i a => a • b i) ∈ Q
    apply Submodule.sum_mem
    intro i hi
    exact Submodule.smul_mem Q (c i)
      (Submodule.subset_span ⟨i, hi, rfl⟩)
  · refine ⟨Submodule.span R (b '' sᶜ), ?_⟩
    exact b.linearIndependent.isCompl_span_image (Module.Basis.span_eq b)
      isCompl_compl
  · let v : s → Q := fun i =>
      ⟨b i, Submodule.subset_span ⟨i, i.property, rfl⟩⟩
    let bQ : Module.Basis s R Q := Module.Basis.mk (v := v) (by
      apply LinearIndependent.of_comp Q.subtype
      change LinearIndependent R (fun i : s => b (i : Module.Free.ChooseBasisIndex R F))
      exact
        b.linearIndependent.comp (fun i : s => (i : Module.Free.ChooseBasisIndex R F))
          Subtype.val_injective) (by
      intro y hy
      have hy' : (y : F) ∈ Submodule.span R (b '' s) := y.property
      refine Submodule.span_induction (p := fun z hz =>
        (⟨z, hz⟩ : Q) ∈ Submodule.span R (Set.range v)) ?_ ?_ ?_ ?_ hy'
      · rintro z ⟨i, hi, rfl⟩
        exact Submodule.subset_span ⟨⟨i, hi⟩, rfl⟩
      · exact Submodule.zero_mem _
      · intro z w hz hw hz' hw'
        exact Submodule.add_mem _ hz' hw'
      · intro a z hz hz'
        exact Submodule.smul_mem _ a hz')
    exact Module.Finite.of_basis bQ
  · let v : s → Q := fun i =>
      ⟨b i, Submodule.subset_span ⟨i, i.property, rfl⟩⟩
    let bQ : Module.Basis s R Q := Module.Basis.mk (v := v) (by
      apply LinearIndependent.of_comp Q.subtype
      change LinearIndependent R (fun i : s => b (i : Module.Free.ChooseBasisIndex R F))
      exact
        b.linearIndependent.comp (fun i : s => (i : Module.Free.ChooseBasisIndex R F))
          Subtype.val_injective) (by
      intro y hy
      have hy' : (y : F) ∈ Submodule.span R (b '' s) := y.property
      refine Submodule.span_induction (p := fun z hz =>
        (⟨z, hz⟩ : Q) ∈ Submodule.span R (Set.range v)) ?_ ?_ ?_ ?_ hy'
      · rintro z ⟨i, hi, rfl⟩
        exact Submodule.subset_span ⟨⟨i, hi⟩, rfl⟩
      · exact Submodule.zero_mem _
      · intro z w hz hw hz' hw'
        exact Submodule.add_mem _ hz' hw'
      · intro a z hz hz'
        exact Submodule.smul_mem _ a hz')
    exact Module.Free.of_basis bQ

private theorem matrix_isUnit_det_of_isUnit_diag_of_nonunit_offdiag
    {R : Type u} [CommRing R] [IsLocalRing R]
    {ι : Type v} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι R)
    (hdiag : ∀ i, IsUnit (A i i))
    (hoff : ∀ i j, i ≠ j → ¬ IsUnit (A i j)) :
    IsUnit A.det := by
  let k := IsLocalRing.ResidueField R
  let f := IsLocalRing.residue R
  let A' := f.mapMatrix A
  have hA' : A' = Matrix.diagonal (fun i => f (A i i)) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [A']
    · have hzero : f (A i j) = 0 := by
        rw [IsLocalRing.residue_eq_zero_iff]
        exact (IsLocalRing.mem_maximalIdeal _).2
          (mem_nonunits_iff.mpr (hoff i j hij))
      simp [A', Matrix.diagonal, hij, hzero]
  have hdiag' : ∀ i, f (A i i) ≠ 0 := by
    intro i
    exact (IsLocalRing.residue_ne_zero_iff_isUnit _).2 (hdiag i)
  have hdet' : A'.det ≠ 0 := by
    rw [hA']
    simp only [Matrix.det_diagonal]
    exact Finset.prod_ne_zero_iff.mpr (fun i _ => hdiag' i)
  apply (IsLocalRing.residue_ne_zero_iff_isUnit _).1
  rw [RingHom.map_det, RingHom.mapMatrix_apply]
  exact hdet'

/-- A countably generated module is free when every decomposition with a
finite free complement has the free-direct-summand property from the source.

The decomposition `M = N ⊕ N'` is represented by a linear equivalence with
the product module `N × N'`. -/
theorem free_of_countablyGenerated_of_free_direct_summand_property
    {R : Type u} {M : Type v} [CommRing R]
    [AddCommGroup M] [Module R M]
    (hM : Formalization.Books.Algebra.Unit84.Module.IsCountablyGenerated R M)
    (hproperty :
      ∀ (N N' : Type w) [AddCommGroup N] [Module R N]
        [AddCommGroup N'] [Module R N']
        [Module.Finite R N'] [Module.Free R N'],
        Nonempty (M ≃ₗ[R] N × N') →
          ∀ x : N, ∃ Q : Submodule R N,
            x ∈ Q ∧ IsComplemented Q ∧ Module.Free R Q) :
    Module.Free R M := by
  sorry

/-- Every element of a projective module over a local ring lies in a free
direct summand. -/
theorem projective_element_mem_free_direct_summand
    {R : Type u} {P : Type v} [CommRing R] [IsLocalRing R]
    [AddCommGroup P] [Module R P]
    (hP : Module.Projective R P) :
    ∀ x : P, ∃ Q : Submodule R P,
      x ∈ Q ∧ IsComplemented Q ∧ Module.Free R Q := by
  classical
  intro x
  obtain ⟨i, hi⟩ := hP.out
  let F := P →₀ R
  let b0 : Module.Basis (Module.Free.ChooseBasisIndex R F) R F :=
    Module.Free.chooseBasis R F
  let c0 := b0.repr (i x)
  let S : Set ℕ := {n | ∃ b : Module.Basis (Module.Free.ChooseBasisIndex R F) R F,
    (b.repr (i x)).support.card = n}
  have hS : S.Nonempty := ⟨c0.support.card, b0, rfl⟩
  let n := Nat.find hS
  obtain ⟨b, hb⟩ := Nat.find_spec hS
  have hbmin : ∀ b' : Module.Basis (Module.Free.ChooseBasisIndex R F) R F,
      n ≤ (b'.repr (i x)).support.card := by
    intro b'
    exact Nat.find_min' hS ⟨b', rfl⟩
  let c := b.repr (i x)
  let s := c.support
  have hno : ∀ (j : Module.Free.ChooseBasisIndex R F), j ∈ s →
      ∀ β : Module.Free.ChooseBasisIndex R F → R,
        c j ≠ Finset.sum (s.erase j) (fun k => c k * β k) := by
    intro j hj β heq
    let f : F →ₗ[R] R := Finset.sum (s.erase j) (fun k => β k • b.coord k)
    have hf : f (b j) = 0 := by
      simp only [f, LinearMap.sum_apply, LinearMap.smul_apply]
      apply Finset.sum_eq_zero
      intro k hk
      simp [b.coord_apply, Finsupp.single_eq_of_ne (Finset.ne_of_mem_erase hk)]
    let e := LinearEquiv.transvection hf
    let b' := b.map e
    let z := Finsupp.linearCombination R b (c.erase j)
    have hz' : z = b.repr.symm (c.erase j) := by
      simp [z]
    have hfz : f z = c j := by
      rw [hz']
      simp only [f, LinearMap.sum_apply, LinearMap.smul_apply]
      simp only [b.coord_repr_symm]
      rw [Finset.sum_congr rfl]
      · exact heq.symm
      · intro k hk
        rw [Finsupp.erase_ne (Finset.ne_of_mem_erase hk)]
        simp [mul_comm]
    have hsum : z + c j • b j = i x := by
      rw [← b.linearCombination_repr (i x)]
      change Finsupp.linearCombination R b (c.erase j) + c j • b j =
        Finsupp.linearCombination R b c
      conv_rhs => rw [← Finsupp.erase_add_single j c]
      simp [Finsupp.linearCombination_apply, Finsupp.sum_add_index', add_smul]
    have hez : e z = i x := by
      rw [LinearEquiv.transvection.apply, hfz, hsum]
    have hez' : e.symm (i x) = z := by
      rw [← hez, e.symm_apply_apply]
    have hb'repr : b'.repr (i x) = c.erase j := by
      simp [b', Module.Basis.map, hez', z]
    have hlt : (b'.repr (i x)).support.card < n := by
      rw [hb'repr, Finsupp.support_erase]
      have hc : c.support.card = n := by simpa [c, n] using hb
      simpa only [hc] using
        (Finset.card_erase_lt_of_mem (s := c.support) (a := j)
          (by simpa [s] using hj))
    exact (Nat.not_lt_of_ge (hbmin b')) hlt
  let p : F →ₗ[R] P := Finsupp.linearCombination R id
  let E : F →ₗ[R] F := i.comp p
  have hE : E (i x) = i x := by
    change i (Finsupp.linearCombination R id (i x)) = i x
    exact congrArg i (hi x)
  let q : s → P := fun j => p (b j)
  have hxrepr : i x = Finset.sum s (fun j => c j • b j) := by
    rw [← b.linearCombination_repr (i x)]
    simp [c, s, Finsupp.linearCombination_apply, Finsupp.sum]
  have hix : i x = Finset.sum Finset.univ (fun j : s => c j • i (q j)) := by
    rw [← hE, hxrepr]
    simp only [map_sum, map_smul]
    simp [E, q, p, s]
    rw [← c.support.sum_attach]
  let e : Module.Basis s R (s → R) := Pi.basisFun R s
  let g : (s → R) →ₗ[R] P := e.constr R q
  let d : F →ₗ[R] (s → R) :=
    { toFun := fun y j => b.coord (j : Module.Free.ChooseBasisIndex R F) y
      map_add' := by intro y z; ext j; simp
      map_smul' := by intro a y; ext j; simp }
  let L : (s → R) →ₗ[R] (s → R) := d.comp (i.comp g)
  let A : Matrix s s R := fun j k =>
    b.coord (j : Module.Free.ChooseBasisIndex R F) (i (q k))
  have hL : L.toMatrix e e = A := by
    ext j k
    rw [LinearMap.toMatrix_apply]
    change e.repr (d (i (g (e k)))) j = _
    rw [show g (e k) = q k by simp [g]]
    simp [d, A, q, e]
  have hA : ∀ j : s, c j = Finset.sum Finset.univ (fun k : s => c k * A j k) := by
    intro j
    have hj := congrArg (b.coord (j : Module.Free.ChooseBasisIndex R F)) hix
    simpa [A, q] using hj
  let B : Matrix s s R := Matrix.transpose A
  have hB : ∀ j : s, c j = Finset.sum Finset.univ (fun k : s => c k * B k j) := by
    intro j
    simpa [B, mul_comm] using hA j
  have hnoSub : ∀ (j : s)
      (β : {k : Module.Free.ChooseBasisIndex R F // k ∈ s.erase (j : Module.Free.ChooseBasisIndex R F)} → R),
      c j ≠ Finset.sum Finset.univ
        (fun k : {k : Module.Free.ChooseBasisIndex R F //
          k ∈ s.erase (j : Module.Free.ChooseBasisIndex R F)} => c k * β k) := by
    intro j β hrel
    apply hno (j : Module.Free.ChooseBasisIndex R F) j.property
    let β' : Module.Free.ChooseBasisIndex R F → R := fun k =>
      if hk : k ∈ s.erase (j : Module.Free.ChooseBasisIndex R F) then β ⟨k, hk⟩ else 0
    have hsum := Finset.sum_subtype (p := fun k => k ∈ s.erase
        (j : Module.Free.ChooseBasisIndex R F))
      (F := Finset.Subtype.fintype (s.erase (j : Module.Free.ChooseBasisIndex R F)))
      (s.erase (j : Module.Free.ChooseBasisIndex R F)) (by intro k; simp)
      (fun k => c k * β' k)
    rw [hsum]
    convert hrel using 1
    change Finset.sum (Finset.univ : Finset {a : Module.Free.ChooseBasisIndex R F //
        a ∈ s.erase (j : Module.Free.ChooseBasisIndex R F)})
        (fun a => c (a : Module.Free.ChooseBasisIndex R F) * β' a) =
      Finset.sum (Finset.univ : Finset {a : Module.Free.ChooseBasisIndex R F //
        a ∈ s.erase (j : Module.Free.ChooseBasisIndex R F)}) (fun k =>
          c (k : Module.Free.ChooseBasisIndex R F) * β k)
    apply Finset.sum_congr rfl
    intro k hk
    simp only [β', dif_pos k.property]
  have hB' (j : s) :
      c j = Finset.sum s (fun k => c k *
        if hk : k ∈ s then B ⟨k, hk⟩ j else 0) := by
    rw [← s.sum_attach]
    simpa using hB j
  have hB'' (j : s) :
      c j = Finset.sum (s.erase (j : Module.Free.ChooseBasisIndex R F))
          (fun k => c k * if hk : k ∈ s then B ⟨k, hk⟩ j else 0) +
        c j * B j j := by
    have hj := hB' j
    rw [← s.sum_erase_add _ j.property] at hj
    simpa using hj
  have hdiagB : ∀ j : s, IsUnit (B j j) := by
    intro j
    by_contra hjunit
    have hu : IsUnit (1 - B j j) :=
      (IsLocalRing.isUnit_or_isUnit_one_sub_self (B j j)).resolve_left hjunit
    let u : R := 1 - B j j
    let uinv : R := ↑(hu.unit⁻¹)
    let β : {k : Module.Free.ChooseBasisIndex R F //
        k ∈ s.erase (j : Module.Free.ChooseBasisIndex R F)} → R := fun k =>
      (if hk : (k : Module.Free.ChooseBasisIndex R F) ∈ s then
        B ⟨(k : Module.Free.ChooseBasisIndex R F), hk⟩ j else 0) * uinv
    have huinv : u * uinv = 1 := by
      rw [show u = (hu.unit : R) from hu.unit_spec.symm]
      simp [uinv]
    have hsum := Finset.sum_subtype (p := fun k => k ∈ s.erase
        (j : Module.Free.ChooseBasisIndex R F))
      (F := Finset.Subtype.fintype (s.erase (j : Module.Free.ChooseBasisIndex R F)))
      (s.erase (j : Module.Free.ChooseBasisIndex R F)) (by intro k; simp)
      (fun k => c k * (if hk : k ∈ s then B ⟨k, hk⟩ j else 0) * uinv)
    have hrel0 : c j * u = Finset.sum (s.erase
        (j : Module.Free.ChooseBasisIndex R F))
          (fun k => c k * if hk : k ∈ s then B ⟨k, hk⟩ j else 0) := by
      calc
        c j * u = c j - c j * B j j := by simp [u, sub_eq_add_neg, mul_add, mul_one]
        _ = (Finset.sum (s.erase (j : Module.Free.ChooseBasisIndex R F))
            (fun k => c k * if hk : k ∈ s then B ⟨k, hk⟩ j else 0) +
              c j * B j j) - c j * B j j :=
          congrArg (fun z => z - c j * B j j) (hB'' j)
        _ = _ := by ring
    have hrel : c j = Finset.sum (Finset.univ : Finset {k : Module.Free.ChooseBasisIndex R F //
        k ∈ s.erase (j : Module.Free.ChooseBasisIndex R F)})
        (fun k => c (k : Module.Free.ChooseBasisIndex R F) * β k) := by
      calc
        c j = c j * 1 := by simp
        _ = c j * (u * uinv) := by rw [huinv]
        _ = (c j * u) * uinv := by ring
        _ = Finset.sum (s.erase (j : Module.Free.ChooseBasisIndex R F))
            (fun k => c k * if hk : k ∈ s then B ⟨k, hk⟩ j else 0) * uinv := by
          rw [hrel0]
        _ = Finset.sum
            (Finset.univ : Finset {k : Module.Free.ChooseBasisIndex R F //
              k ∈ s.erase (j : Module.Free.ChooseBasisIndex R F)})
            (fun k => c (k : Module.Free.ChooseBasisIndex R F) * β k) := by
          rw [Finset.sum_mul]
          simpa [β, mul_assoc] using hsum
    exact (hnoSub j β) hrel
  have hoffB : ∀ a b : s, a ≠ b → ¬ IsUnit (B a b) := by
    intro a b hab habunit
    let u : R := B a b
    let uinv : R := ↑(habunit.unit⁻¹)
    let t : Finset (Module.Free.ChooseBasisIndex R F) :=
      s.erase (a : Module.Free.ChooseBasisIndex R F)
    let f : Module.Free.ChooseBasisIndex R F → R := fun k =>
      c k * if hk : k ∈ s then B ⟨k, hk⟩ b else 0
    have hrelA : c b = Finset.sum t f + c a * u := by
      have hb' := hB' b
      rw [← s.sum_erase_add _ a.property] at hb'
      simpa [t, f, u] using hb'
    have huinv : u * uinv = 1 := by
      rw [show u = (habunit.unit : R) from habunit.unit_spec.symm]
      simp [uinv]
    have hbt : (b : Module.Free.ChooseBasisIndex R F) ∈ t := by
      exact Finset.mem_erase.mpr ⟨by simpa using hab.symm, b.property⟩
    let f0 : Module.Free.ChooseBasisIndex R F → R := fun k =>
      if hk : k ∈ s then B ⟨k, hk⟩ b else 0
    let β : {k : Module.Free.ChooseBasisIndex R F // k ∈ t} → R := fun k =>
      if hkb : (k : Module.Free.ChooseBasisIndex R F) = b then
        (1 - B b b) * uinv
      else -f0 (k : Module.Free.ChooseBasisIndex R F) * uinv
    have hsumβ := Finset.sum_subtype (p := fun k => k ∈ t)
      (F := Finset.Subtype.fintype t) t (by intro k; simp)
      (fun k => c k * (if hkb : k = b then (1 - B b b) * uinv
        else -f0 k * uinv))
    have hrel0 : c a * u = c b - Finset.sum t f := by
      calc
        c a * u = (Finset.sum t f + c a * u) - Finset.sum t f := by ring
        _ = c b - Finset.sum t f := by rw [hrelA]
    have hmul : Finset.sum t f * uinv = Finset.sum t (fun k => f k * uinv) := by
      rw [Finset.sum_mul]
    have hbeta : c b * uinv - Finset.sum t f * uinv =
        Finset.sum t (fun k => c k *
          if hkb : k = b then (1 - B b b) * uinv else -f0 k * uinv) := by
      rw [hmul]
      rw [← t.sum_erase_add _ hbt]
      rw [← t.sum_erase_add _ hbt]
      have hsumeq : Finset.sum (t.erase b) (fun k => f k * uinv) =
          Finset.sum (t.erase b) (fun k => c k * (f0 k * uinv)) := by
        apply Finset.sum_congr rfl
        intro k hk
        have hkb' : k ≠ b := Finset.ne_of_mem_erase hk
        have hks : k ∈ s := by
          exact (Finset.mem_erase.mp (Finset.mem_erase.mp hk).2).2
        simp [f, f0, hkb', hks, mul_assoc]
      have hsumzero : Finset.sum (t.erase b) (fun k => c k *
          if hkb : k = b then (1 - B b b) * uinv else -f0 k * uinv) =
          Finset.sum (t.erase b) (fun k => c k * (-f0 k * uinv)) := by
        apply Finset.sum_congr rfl
        intro k hk
        simp [Finset.ne_of_mem_erase hk]
      have hsumneg : Finset.sum (t.erase b) (fun k => c k * (-f0 k * uinv)) =
          -Finset.sum (t.erase b) (fun k => c k * (f0 k * uinv)) := by
        calc
          Finset.sum (t.erase b) (fun k => c k * (-f0 k * uinv)) =
              Finset.sum (t.erase b) (fun k => -(c k * (f0 k * uinv))) := by
            apply Finset.sum_congr rfl
            intro k hk
            ring
          _ = -Finset.sum (t.erase b) (fun k => c k * (f0 k * uinv)) := by
            rw [Finset.sum_neg_distrib]
      rw [hsumeq]
      rw [hsumzero]
      rw [hsumneg]
      simp only [dif_pos trivial]
      have hfb : f b = c b * B b b := by simp [f]
      rw [hfb]
      ring
    have hrel : c a = Finset.sum (Finset.univ : Finset {k : Module.Free.ChooseBasisIndex R F //
        k ∈ t}) (fun k => c (k : Module.Free.ChooseBasisIndex R F) * β k) := by
      calc
        c a = c a * 1 := by simp
        _ = c a * (u * uinv) := by rw [huinv]
        _ = (c a * u) * uinv := by ring
        _ = (c b - Finset.sum t f) * uinv := by rw [hrel0]
        _ = c b * uinv - Finset.sum t f * uinv := by rw [sub_mul]
        _ = Finset.sum t (fun k => c k *
            if hkb : k = b then (1 - B b b) * uinv else -f0 k * uinv) := hbeta
        _ = Finset.sum (Finset.univ : Finset {k : Module.Free.ChooseBasisIndex R F //
            k ∈ t}) (fun k => c (k : Module.Free.ChooseBasisIndex R F) * β k) := by
          simpa [β] using hsumβ
    exact (hnoSub a β) hrel
  have hBunit : IsUnit B.det :=
    matrix_isUnit_det_of_isUnit_diag_of_nonunit_offdiag B hdiagB hoffB
  have hAunit : IsUnit A.det := by
    simpa [B] using hBunit
  let eL : (s → R) ≃ₗ[R] (s → R) := Matrix.toLinearEquiv e A hAunit
  have hLeq : L = eL.toLinearMap := by
    apply (LinearMap.toMatrix e e).injective
    rw [hL]
    symm
    change LinearMap.toMatrix e e (Matrix.toLin e e A) = A
    exact LinearMap.toMatrix_toLin e e A
  let r : P →ₗ[R] P := g.comp (eL.symm.toLinearMap.comp (d.comp i))
  have hrange : ∀ y, r y ∈ LinearMap.range g := by
    intro y
    exact ⟨eL.symm (d (i y)), rfl⟩
  have hrange_id : ∀ y ∈ LinearMap.range g, r y = y := by
    rintro y ⟨z, rfl⟩
    change g (eL.symm (d (i (g z)))) = g z
    change g (eL.symm (L z)) = g z
    rw [hLeq]
    simp
  let hproj : LinearMap.IsProj (LinearMap.range g) r :=
    ⟨hrange, hrange_id⟩
  have hg : Function.Injective g := by
    intro z z' hzz
    apply eL.injective
    change eL.toLinearMap z = eL.toLinearMap z'
    rw [← hLeq]
    change d (i (g z)) = d (i (g z'))
    rw [hzz]
  have hfreeQ : Module.Free R (LinearMap.range g) :=
    Module.Free.of_equiv' (Module.Free.of_basis e)
      (LinearEquiv.ofInjective g hg)
  have hxg : x = g (fun j => c j) := by
    apply hi.injective
    simpa [g, e] using hix
  refine ⟨LinearMap.range g, ?_, ⟨LinearMap.ker r, hproj.isCompl⟩, hfreeQ⟩
  exact ⟨fun j => c j, hxg.symm⟩

/-- **Projective modules over local rings are free.** -/
theorem projective_free_over_local_ring
    {R : Type u} {P : Type v} [CommRing R] [IsLocalRing R]
    [AddCommGroup P] [Module R P]
    (hP : Module.Projective R P) :
    Module.Free R P := by
  let _ : Module.Projective R P := hP
  obtain ⟨ι, N, hN, ⟨e⟩⟩ :=
    Formalization.Books.Algebra.Unit84.projective_isDirectSumOfCountablyGeneratedProjectiveModules
      (R := R) (M := P)
  let _ : ∀ i, Module.Projective R (N i) := fun i => (hN i).2
  have hfree : ∀ i, Module.Free R (N i) := by
    intro i
    refine free_of_countablyGenerated_of_free_direct_summand_property
      (R := R) (M := (N i : Type v)) (hN i).1 ?_
    intro (A : Type v) (B : Type v) _ _ _ _ _ _ hAB x
    rcases hAB with ⟨eAB⟩
    let inc : A →ₗ[R] (N i : Type v) := eAB.symm.toLinearMap.comp
      (LinearMap.inl R A B)
    let proj : (N i : Type v) →ₗ[R] A := (LinearMap.fst R A B).comp eAB.toLinearMap
    have hproj : proj.comp inc = LinearMap.id := by
      ext a
      simp [inc, proj]
    let _ : Module.Projective R A := Module.Projective.of_split inc proj hproj
    exact projective_element_mem_free_direct_summand (R := R) (P := A)
      (inferInstance : Module.Projective R A) x
  let _ : ∀ j, Module.Free R (N j) := fun j => hfree j
  let _ : Module.Free R (DirectSum ι (fun j => (N j : Type v))) :=
    Module.Free.dfinsupp R (fun j : ι => (N j : Type v))
  exact Module.Free.of_equiv' (by infer_instance) e.symm

end Formalization.Books.Algebra.Unit85
