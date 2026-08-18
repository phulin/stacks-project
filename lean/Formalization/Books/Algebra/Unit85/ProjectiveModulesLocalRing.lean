import Formalization.Books.Algebra.Unit84.TransfiniteDevissage
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.RingTheory.Finiteness.Prod
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.LinearAlgebra.Basis.Prod
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

universe u v

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

private structure CountableFreeDecomposition
    {R : Type u} {M : Type v} [CommRing R]
    [AddCommGroup M] [Module R M] where
  F : ModuleCat.{v} R
  C : ModuleCat.{v} R
  e : M ≃ₗ[R] (ModuleCat.carrier F) × (ModuleCat.carrier C)
  finiteF : Module.Finite R (ModuleCat.carrier F)
  freeF : Module.Free R (ModuleCat.carrier F)

private structure CountableFreeExtension
    {R : Type u} {M : Type v} [CommRing R]
    [AddCommGroup M] [Module R M]
    (D : CountableFreeDecomposition (R := R) (M := M)) (x : M) where
  Q : Submodule R (ModuleCat.carrier D.C)
  U : Submodule R (ModuleCat.carrier D.C)
  hQU : IsCompl Q U
  T : Submodule R Q
  V : Submodule R Q
  hTV : IsCompl T V
  finiteT : Module.Finite R T
  freeT : Module.Free R T
  eC : ModuleCat.carrier D.C ≃ₗ[R] T × (V × U)
  e : M ≃ₗ[R] (ModuleCat.carrier D.F × T) × (V × U)
  e_eq : e =
    ((D.e.trans ((LinearEquiv.refl R (ModuleCat.carrier D.F)).prodCongr eC)).trans
      (LinearEquiv.prodAssoc R (ModuleCat.carrier D.F) T (V × U)).symm)
  contains : ∃ z : ModuleCat.carrier D.F × T,
    e.symm (z, (0, 0)) = x

private def CountableFreeExtension.next
    {R : Type u} {M : Type v} [CommRing R]
    [AddCommGroup M] [Module R M]
    {D : CountableFreeDecomposition (R := R) (M := M)} {x : M}
    (E : CountableFreeExtension D x) :
    CountableFreeDecomposition (R := R) (M := M) := by
  letI : Module.Finite R (ModuleCat.carrier D.F) := D.finiteF
  letI : Module.Free R (ModuleCat.carrier D.F) := D.freeF
  letI : Module.Finite R E.T := E.finiteT
  letI : Module.Free R E.T := E.freeT
  exact
    { F := ModuleCat.of R (ModuleCat.carrier D.F × E.T)
      C := ModuleCat.of R (E.V × E.U)
      e := E.e
      finiteF := inferInstance
      freeF := inferInstance }

private theorem countableFreeExtension_exists
    {R : Type u} {M : Type v} [CommRing R]
    [AddCommGroup M] [Module R M]
    (hproperty :
      ∀ (N N' : Type v) [AddCommGroup N] [Module R N]
        [AddCommGroup N'] [Module R N']
        [Module.Finite R N'] [Module.Free R N'],
        Nonempty (M ≃ₗ[R] N × N') →
          ∀ x : N, ∃ Q : Submodule R N,
            x ∈ Q ∧ IsComplemented Q ∧ Module.Free R Q)
    (D : CountableFreeDecomposition (R := R) (M := M)) (x : M) :
    Nonempty (CountableFreeExtension D x) := by
  classical
  let eCF : M ≃ₗ[R] ModuleCat.carrier D.C × ModuleCat.carrier D.F :=
    D.e.trans (LinearEquiv.prodComm R (ModuleCat.carrier D.F)
      (ModuleCat.carrier D.C))
  obtain ⟨Q, hyQ, hQcomp, hQfree⟩ :=
    @hproperty (ModuleCat.carrier D.C) (ModuleCat.carrier D.F) _ _ _ _
      D.finiteF D.freeF ⟨eCF⟩ (eCF x).1
  obtain ⟨U, hQU⟩ := hQcomp
  obtain ⟨T, hTmem, hTcomp, hTfinite, hTfree⟩ :=
    free_element_mem_finite_free_direct_summand hQfree ⟨(eCF x).1, hyQ⟩
  obtain ⟨V, hTV⟩ := hTcomp
  let eC : ModuleCat.carrier D.C ≃ₗ[R] T × (V × U) :=
    ((Submodule.prodEquivOfIsCompl Q U hQU).symm.trans
      ((Submodule.prodEquivOfIsCompl T V hTV).symm.prodCongr
        (LinearEquiv.refl R U))).trans
      (LinearEquiv.prodAssoc R T V U)
  let e : M ≃ₗ[R] (ModuleCat.carrier D.F × T) × (V × U) :=
    (D.e.trans ((LinearEquiv.refl R (ModuleCat.carrier D.F)).prodCongr eC)).trans
      (LinearEquiv.prodAssoc R (ModuleCat.carrier D.F) T (V × U)).symm
  have hcontains : ∃ z : ModuleCat.carrier D.F × T,
      e.symm (z, (0, 0)) = x := by
    let zQ : Q := ⟨(eCF x).1, hyQ⟩
    let zT : T := ((Submodule.prodEquivOfIsCompl T V hTV).symm zQ).1
    refine ⟨((eCF x).2, zT), ?_⟩
    apply e.injective
    rw [e.apply_symm_apply]
    simp only [e, LinearEquiv.trans_apply,
      LinearEquiv.prodCongr_apply]
    change (((eCF x).2, zT), 0, 0) =
      (((D.e x).1, (eC (D.e x).2).1), (eC (D.e x).2).2)
    have hD : D.e x = ((eCF x).2, (eCF x).1) := by rfl
    have hprojQ : Q.projectionOnto U hQU (eCF x).1 = zQ := by
      exact Submodule.projectionOnto_apply_of_mem_left hQU hyQ
    have hTVzero : V.projectionOnto T hTV.symm zQ = 0 :=
      Submodule.projectionOnto_apply_of_mem_right hTV.symm hTmem
    have hQUzero : U.projectionOnto Q hQU.symm (eCF x).1 = 0 :=
      Submodule.projectionOnto_apply_of_mem_right hQU.symm hyQ
    rw [hD]
    congr 1
    all_goals
      simp [eC, zT, zQ,
        hprojQ, hTVzero, hQUzero]
  refine ⟨{
    Q := Q
    U := U
    hQU := hQU
    T := T
    V := V
    hTV := hTV
    finiteT := hTfinite
    freeT := hTfree
    eC := eC
    e := e
    e_eq := by rfl
    contains := hcontains }⟩

/-- A countably generated module is free when every decomposition with a
finite free complement has the free-direct-summand property from the source.

The decomposition `M = N ⊕ N'` is represented by a linear equivalence with
the product module `N × N'`. -/
theorem free_of_countablyGenerated_of_free_direct_summand_property
    {R : Type u} {M : Type v} [CommRing R]
    [AddCommGroup M] [Module R M]
    (hM : Formalization.Books.Algebra.Unit84.Module.IsCountablyGenerated R M)
    (hproperty :
      ∀ (N N' : Type v) [AddCommGroup N] [Module R N]
        [AddCommGroup N'] [Module R N']
        [Module.Finite R N'] [Module.Free R N'],
        Nonempty (M ≃ₗ[R] N × N') →
          ∀ x : N, ∃ Q : Submodule R N,
            x ∈ Q ∧ IsComplemented Q ∧ Module.Free R Q) :
    Module.Free R M := by
  classical
  rcases hM with ⟨s, hs, hspan⟩
  obtain ⟨x, hxs⟩ := Set.countable_iff_exists_subset_range.mp hs
  have hxspan : Submodule.span R (Set.range x) = ⊤ := by
    apply top_unique
    rw [← hspan]
    exact Submodule.span_mono hxs
  let b0 : Module.Basis (PEmpty.{v + 1}) R (⊥ : Submodule R M) :=
    Module.Basis.empty (⊥ : Submodule R M)
  let D0 : CountableFreeDecomposition (R := R) (M := M) :=
    { F := ModuleCat.of R (⊥ : Submodule R M)
      C := ModuleCat.of R M
      e := (LinearEquiv.uniqueProd (R := R) (M := M)
        (M₂ := (⊥ : Submodule R M))).symm
      finiteF := Module.Finite.of_basis b0
      freeF := Module.Free.of_basis b0 }
  let pick : ∀ (D : CountableFreeDecomposition (R := R) (M := M)) (n : ℕ),
      CountableFreeExtension D (x n) := fun D n =>
    Classical.choice (countableFreeExtension_exists hproperty D (x n))
  let D : ℕ → CountableFreeDecomposition (R := R) (M := M) :=
    Nat.rec D0 (fun n Dn => (pick Dn n).next)
  let E (n : ℕ) : CountableFreeExtension (D n) (x n) := pick (D n) n
  have hDnext (n : ℕ) : D (n + 1) = (E n).next := by
    rfl
  let inc (n : ℕ) : ModuleCat.carrier (D n).F →ₗ[R] M :=
    (D n).e.symm.toLinearMap.comp
      (LinearMap.inl R (ModuleCat.carrier (D n).F) (ModuleCat.carrier (D n).C))
  let P (n : ℕ) : Submodule R M := LinearMap.range (inc n)
  let incT (n : ℕ) : (E n).T →ₗ[R] M :=
    (D n).e.symm.toLinearMap.comp
      ((LinearMap.inr R (ModuleCat.carrier (D n).F) (ModuleCat.carrier (D n).C)).comp
        ((E n).eC.symm.toLinearMap.comp
          (LinearMap.inl R (E n).T ((E n).V × (E n).U))))
  let A (n : ℕ) : Submodule R M := LinearMap.range (incT n)
  have hPnext (n : ℕ) : P (n + 1) = P n ⊔ A n := by
    change LinearMap.range (inc (n + 1)) =
      LinearMap.range (inc n) ⊔ LinearMap.range (incT n)
    cases hDnext n
    change LinearMap.range
        ((E n).e.symm.toLinearMap.comp
          (LinearMap.inl R (ModuleCat.carrier (D n).F × (E n).T)
            ((E n).V × (E n).U))) =
      LinearMap.range (inc n) ⊔ LinearMap.range (incT n)
    ext y
    constructor
    · rintro ⟨z, rfl⟩
      rcases z with ⟨f, t⟩
      change (E n).e.symm ((f, t), (0, 0)) ∈
        LinearMap.range (inc n) ⊔ LinearMap.range (incT n)
      rw [(E n).e_eq]
      change (D n).e.symm (f, (E n).eC.symm (t, (0, 0))) ∈
        LinearMap.range (inc n) ⊔ LinearMap.range (incT n)
      rw [show (D n).e.symm (f, (E n).eC.symm (t, (0, 0))) =
          (D n).e.symm (f, 0) + (D n).e.symm (0, (E n).eC.symm (t, (0, 0))) by
        rw [← map_add]
        congr 1; simp]
      apply Submodule.mem_sup.mpr
      refine ⟨(D n).e.symm (f, 0), ?_,
        (D n).e.symm (0, (E n).eC.symm (t, (0, 0))), ?_, rfl⟩
      · exact ⟨f, by
          simp [inc]⟩
      · exact ⟨t, by
          simp [incT, E]
          rfl⟩
    · intro hy
      rcases Submodule.mem_sup'.mp hy with
        ⟨⟨y₁, hy₁⟩, ⟨y₂, hy₂⟩, rfl⟩
      rcases hy₁ with ⟨f, rfl⟩
      rcases hy₂ with ⟨t, rfl⟩
      refine ⟨(f, t), ?_⟩
      change (E n).e.symm ((f, t), (0, 0)) = _
      rw [(E n).e_eq]
      change (D n).e.symm (f, (E n).eC.symm (t, (0, 0))) = _
      change (D n).e.symm (f, (E n).eC.symm (t, (0, 0))) =
        (D n).e.symm (f, 0) + (D n).e.symm (0, (E n).eC.symm (t, (0, 0)))
      rw [← map_add]
      congr 1; simp
  have hincE (n : ℕ) (f : ModuleCat.carrier (D n).F) :
      (E n).e (inc n f) = ((f, 0), (0, 0)) := by
    rw [(E n).e_eq]
    simp [inc]; rfl
  have hincTE (n : ℕ) (t : (E n).T) :
      (E n).e (incT n t) = ((0, t), (0, 0)) := by
    rw [(E n).e_eq]
    simp [incT]; rfl
  have hdisjoint (n : ℕ) : Disjoint (A n) (P n) := by
    rw [Submodule.disjoint_def]
    intro y hyA hyP
    rcases hyA with ⟨t, hty⟩
    rcases hyP with ⟨f, hfy⟩
    have heq0 : incT n t = inc n f := hty.trans hfy.symm
    have heq : (E n).e (incT n t) = (E n).e (inc n f) := congrArg (E n).e heq0
    rw [hincTE, hincE] at heq
    have hf : f = 0 :=
      (congrArg Prod.fst (congrArg Prod.fst heq)).symm
    have ht : t = 0 := by
      exact congrArg Prod.snd (congrArg Prod.fst heq)
    apply (E n).e.injective
    rw [← hty, hincTE, ht]
    simp
  have hPzero : P 0 = ⊥ := by
    apply le_antisymm
    · rintro y ⟨z, rfl⟩
      simp [inc, D, D0]
    · exact (bot_le : (⊥ : Submodule R M) ≤ P 0)
  have hPmono : Monotone P := by
    intro m n hmn
    induction n, hmn using Nat.le_induction with
    | base => exact le_rfl
    | succ n hmn ih =>
        rw [hPnext n]
        exact ih.trans le_sup_left
  have hPtop : ∀ n : ℕ, P n ≤ ⨆ i : ℕ, A i := by
    intro n
    induction n with
    | zero => rw [hPzero]; exact bot_le
    | succ n ih =>
        rw [hPnext n]
        exact sup_le ih (le_iSup A n)
  have hxP : ∀ n : ℕ, x n ∈ P (n + 1) := by
    intro n
    rcases (E n).contains with ⟨z, hz⟩
    rw [← hz]
    change (E n).e.symm (z, (0, 0)) ∈ LinearMap.range (inc (n + 1))
    cases hDnext n
    exact ⟨z, rfl⟩
  have hAtop : (⨆ i : ℕ, A i) = ⊤ := by
    apply top_unique
    rw [← hxspan]
    apply Submodule.span_le.2
    rintro y ⟨n, rfl⟩
    exact hPtop (n + 1) (hxP n)
  have hInternal : DirectSum.IsInternal A := by
    apply DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    · apply iSupIndep_of_dfinsupp_lsum_injective A
      intro f g hfg
      by_contra hne
      let s := (f - g).support
      have hs : s.Nonempty := by
        rw [Finset.nonempty_iff_ne_empty]
        intro hs0
        apply hne
        ext j
        have hnot : j ∉ (f - g).support := by simp [s, hs0]
        have hzeroDF : (f - g) j = 0 := by
          by_contra hne0
          exact hnot (DFinsupp.mem_support_iff.mpr hne0)
        have hzero : f j - g j = 0 := by
          simpa only [DFinsupp.sub_apply] using hzeroDF
        exact congrArg Subtype.val (sub_eq_zero.mp hzero)
      let n := s.max' hs
      have hnmem : n ∈ s := Finset.max'_mem s hs
      have hnne : (f - g) n ≠ 0 := DFinsupp.mem_support_iff.mp hnmem
      have hrest :
          DFinsupp.lsum ℕ (fun j => (A j).subtype) ((f - g).erase n) ∈ P n := by
        rw [DFinsupp.lsum_apply_apply]
        apply Submodule.dfinsuppSumAddHom_mem
        intro j hj
        have hjne : j ≠ n := by
          intro hjeq
          subst j
          simp at hj
        have hjmem : j ∈ s := by
          apply DFinsupp.mem_support_iff.mpr
          simpa [DFinsupp.erase_apply, hjne] using hj
        have hjlt : j < n :=
          lt_of_le_of_ne (Finset.le_max' s j hjmem) hjne
        have hAj : A j ≤ P (j + 1) := by
          rw [hPnext j]
          exact le_sup_right
        exact (hPmono (Nat.succ_le_iff.mpr hjlt))
          (hAj ((f - g).erase n j).property)
      have hsum :
          DFinsupp.lsum ℕ (fun j => (A j).subtype) ((f - g).erase n) +
            (A n).subtype ((f - g) n) = 0 := by
        calc
          _ = DFinsupp.lsum ℕ (fun j => (A j).subtype)
              ((f - g).erase n + DFinsupp.single n ((f - g) n)) := by
            rw [map_add, DFinsupp.lsum_single]
          _ = DFinsupp.lsum ℕ (fun j => (A j).subtype) (f - g) := by
            rw [DFinsupp.erase_add_single]
          _ = 0 := by rw [map_sub, hfg]; simp
      have hmem : (A n).subtype ((f - g) n) ∈ P n := by
        rw [eq_neg_of_add_eq_zero_right hsum]
        exact (P n).neg_mem hrest
      have hzero : (f - g) n = 0 := by
        apply Subtype.ext
        exact Submodule.disjoint_def.mp (hdisjoint n) _
          ((f - g) n).property hmem
      exact hnne hzero
    · exact hAtop
  let _ : ∀ n, Module.Free R (A n) := fun n => by
    apply Module.Free.of_equiv' (E n).freeT
    apply LinearEquiv.ofInjective (incT n)
    intro a b hab
    have heq := congrArg (E n).e hab
    rw [hincTE, hincTE] at heq
    exact congrArg Prod.snd (congrArg Prod.fst heq)
  let _ : Module.Free R (DirectSum ℕ (fun n => (A n : Type v))) :=
    Module.Free.dfinsupp R (fun n : ℕ => (A n : Type v))
  exact Module.Free.of_equiv' (by infer_instance)
    (LinearEquiv.ofBijective (DirectSum.coeLinearMap A) hInternal)

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
        simp only [mul_dite, mul_zero, dite_mul, mul_assoc, zero_mul, f, f0]
      have hsumzero : Finset.sum (t.erase b) (fun k => c k *
          if hkb : k = b then (1 - B b b) * uinv else -f0 k * uinv) =
          Finset.sum (t.erase b) (fun k => c k * (-f0 k * uinv)) := by
        apply Finset.sum_congr rfl
        intro k hk
        simp [show k ≠ b from Finset.ne_of_mem_erase hk]
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
