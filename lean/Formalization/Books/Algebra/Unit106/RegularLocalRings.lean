import Formalization.Books.Algebra.Unit69.QuasiRegularSequences
import Formalization.Books.Algebra.Unit103.CohenMacaulayModules
import Mathlib.Algebra.Colimit.DirectLimit
import Mathlib.RingTheory.LocalRing.RingHom.Basic
import Mathlib.RingTheory.Regular.Free
import Mathlib.RingTheory.RegularLocalRing.Defs

/-!
# Commutative Algebra, Chapter 106: Regular local rings

The source's regular-local property is Mathlib's `IsRegularLocalRing`.  The
associated graded ring is represented by the associated graded target from
Chapter 69; in particular, its polynomial description is stated as the
corresponding linear equivalence over the residue quotient.
-/

namespace Formalization.Books.Algebra.Unit106

open Formalization.Books.Algebra.Unit103
open Formalization.Books.Algebra.Unit72
open IsLocalRing

universe u v

noncomputable section

/-! ## Generators and the associated graded ring -/

/-- A list is a minimal generating list for an ideal when no entry is generated
by the remaining entries. -/
def IsMinimalIdealGeneratingList
    {R : Type u} [CommRing R] (I : Ideal R) (xs : List R) : Prop :=
  Ideal.ofList xs = I ∧
    ∀ i : Fin xs.length,
      xs.get i ∉ Ideal.ofList (xs.eraseIdx i.1)

private theorem exists_minimalIdealGeneratingList
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R] :
    ∃ xs : List R,
      IsMinimalIdealGeneratingList (maximalIdeal R) xs ∧
        xs.length = (maximalIdeal R).spanFinrank := by
  classical
  let S : Set R := (maximalIdeal R).generators
  let hfg : (maximalIdeal R).FG := IsNoetherian.noetherian (maximalIdeal R)
  let hS : S.Finite :=
    Submodule.FG.finite_generators hfg
  let F : Finset R := hS.toFinset
  let xs : List R := F.toList
  have hSF : (F : Set R) = S := hS.coe_toFinset
  have hspan : Ideal.ofList xs = maximalIdeal R := by
    simpa [Ideal.ofList, xs, hSF] using (maximalIdeal R).span_generators
  have hgen : (maximalIdeal R).spanFinrank = F.card := by
    rw [← Submodule.FG.generators_ncard hfg]
    simpa [F, S] using Set.ncard_eq_toFinset_card (hs := hS)
  refine ⟨xs, ⟨hspan, ?_⟩, ?_⟩
  intro i hi
  have hcard : (xs.eraseIdx i.1).length + 1 = xs.length :=
    List.length_eraseIdx_add_one i.isLt
  have hspan_erase : Ideal.ofList (xs.eraseIdx i.1) = maximalIdeal R := by
    apply le_antisymm
    · rw [← hspan]
      apply Ideal.span_le.mpr
      intro y hy
      change y ∈ Ideal.span {r | r ∈ xs}
      exact Ideal.subset_span (List.eraseIdx_subset hy)
    · rw [← hspan]
      apply Ideal.span_le.mpr
      intro y hy
      by_cases hyeq : y = xs.get i
      · simpa [hyeq] using hi
      · have hy' : y ∈ xs.eraseIdx i.1 := by
          change y ∈ xs at hy
          obtain ⟨j, hj, hget⟩ := (List.mem_iff_getElem.mp hy)
          have hji : j ≠ i.1 := by
            intro hji
            apply hyeq
            subst j
            exact hget.symm
          rw [List.mem_eraseIdx_iff_getElem]
          exact ⟨j, hj, hji, hget⟩
        change y ∈ Ideal.span {r | r ∈ xs.eraseIdx i.1}
        exact Ideal.subset_span hy'
  let E : Finset R := (xs.eraseIdx i.1).toFinset
  have hspanE : Ideal.span (↑E : Set R) = maximalIdeal R := by
    simpa [E, Ideal.ofList] using hspan_erase
  have hspanE' : Submodule.span R (↑E : Set R) = maximalIdeal R := hspanE
  have hle := Submodule.spanFinrank_span_le_ncard_of_finite
    (R := R) (M := R) (s := (↑E : Set R)) E.finite_toSet
  rw [hspanE'] at hle
  rw [hgen] at hle
  have hcard' : E.card ≤ (xs.eraseIdx i.1).length := by
    simpa [E] using List.toFinset_card_le (xs.eraseIdx i.1)
  have hle' : F.card ≤ (xs.eraseIdx i.1).length := by
    exact le_trans (by simpa using hle) hcard'
  have hle'' : xs.length ≤ (xs.eraseIdx i.1).length := by
    simpa [xs] using hle'
  omega
  simpa [xs] using hgen.symm

/-- The associated graded ring of a regular local ring is polynomial over its
residue field.  Chapter 69's `quasiRegularTarget` is the established
degreewise direct-sum representation of the associated graded object. -/
theorem regular_graded
    {R : Type u} [CommRing R] [IsRegularLocalRing R]
    (d : ℕ) (hd : ringKrullDim R = d)
    (xs : List R)
    (hxs : IsMinimalIdealGeneratingList (maximalIdeal R) xs)
    (hxd : xs.length = d) :
    Nonempty
      (MvPolynomial (Fin d) (R ⧸ maximalIdeal R) ≃ₗ[R ⧸ maximalIdeal R]
        Formalization.Books.Algebra.Unit69.quasiRegularTarget R R
          (maximalIdeal R)) := by
  sorry

/-! ## Basic properties -/

/-- A regular local ring is a domain. -/
theorem regular_domain
    {R : Type u} [CommRing R] [IsRegularLocalRing R] :
    IsDomain R := by
  sorry

/-- A minimal generating list of the maximal ideal is a regular sequence; all
successive quotients are regular local of the expected dimension, so the ring
is Cohen--Macaulay. -/
theorem regular_ring_CM
    {R : Type u} [CommRing R] [IsRegularLocalRing R]
    (xs : List R)
    (hxs : IsMinimalIdealGeneratingList (maximalIdeal R) xs) :
    RingTheory.Sequence.IsRegular R xs ∧
      (∀ c : ℕ, c ≤ xs.length →
        IsRegularLocalRing (R ⧸ Ideal.ofList (xs.take c)) ∧
          ringKrullDim (R ⧸ Ideal.ofList (xs.take c)) = xs.length - c) ∧
      IsCohenMacaulay R R := by
  sorry

/-- If both a regular local ring and one of its quotients are regular local,
the quotient ideal is generated by an initial segment of a minimal generating
list of the maximal ideal. -/
theorem regular_quotient_regular
    {R : Type u} [CommRing R] [IsRegularLocalRing R]
    (I : Ideal R) (hI : IsRegularLocalRing (R ⧸ I)) :
    ∃ xs : List R, ∃ c : ℕ,
      IsMinimalIdealGeneratingList (maximalIdeal R) xs ∧
        c ≤ xs.length ∧ I = Ideal.ofList (xs.take c) := by
  sorry

/-! ## Freeness and Cohen--Macaulay modules -/

/-- A finite module that is regular in `x` is free when its quotient by `x` is
free over the quotient ring. -/
theorem free_mod_x
    {R M : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M]
    (x : R) (hx : x ∈ maximalIdeal R)
    (hreg : IsSMulRegular M x)
    (hfree : Module.Free (R ⧸ Ideal.span ({x} : Set R)) (QuotSMulTop x M)) :
    Module.Free R M := by
  have hmem : x ∈ (⊥ : Ideal R).jacobson :=
    (maximalIdeal_le_jacobson (⊥ : Ideal R)) hx
  letI : Module.FinitePresentation R M := Module.finitePresentation_of_finite R M
  exact (Module.free_quotSMulTop_iff_free (R := R) (M := M) hmem hreg).mp hfree

private theorem free_of_regular_sequence
    {R M : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M]
    (xs : List R) (hxs : RingTheory.Sequence.IsRegular M xs)
    (hfree : Module.Free (R ⧸ Ideal.ofList xs)
      (M ⧸ (Ideal.ofList xs • (⊤ : Submodule R M)))) :
    Module.Free R M := by
  let rec aux {R M : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
      [AddCommGroup M] [Module R M] [Module.Finite R M]
      (xs : List R) (hxs : RingTheory.Sequence.IsRegular M xs)
      (hfree : Module.Free (R ⧸ Ideal.ofList xs)
        (M ⧸ (Ideal.ofList xs • (⊤ : Submodule R M)))) :
      Module.Free R M := by
    cases xs with
    | nil =>
      let er : R ⧸ Ideal.ofList [] ≃+* R :=
        (Ideal.quotientEquivAlgOfEq R (by simp [Ideal.ofList])).toRingEquiv.trans
          (RingEquiv.quotientBot R)
      letI : RingHomInvPair er.toRingHom er.symm.toRingHom :=
        RingHomInvPair.of_ringEquiv er
      letI : RingHomInvPair er.symm.toRingHom er.toRingHom :=
        RingHomInvPair.of_ringEquiv er.symm
      let em : (M ⧸ (Ideal.ofList [] • (⊤ : Submodule R M)))
          ≃ₛₗ[er.toRingHom] M :=
        { (Submodule.quotEquivOfEqBot
            (Ideal.ofList [] • (⊤ : Submodule R M))
              (by
                simpa only [Ideal.ofList_nil] using
                  (Submodule.bot_smul (R := R) (A := R) (M := M)
                    (N := (⊤ : Submodule R M))))).toAddEquiv with
          map_smul' := by
            intro a z
            obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective a
            refine Submodule.Quotient.induction_on
              (Ideal.ofList [] • (⊤ : Submodule R M)) z ?_
            intro m
            rfl }
      exact Module.Free.of_equiv em
    | cons x rs =>
      obtain ⟨hxreg, htail⟩ :=
        (RingTheory.Sequence.isRegular_cons_iff' M x rs).mp hxs
      have hx : x ∈ maximalIdeal R := by
        by_contra hx
        have hunit : IsUnit x := IsLocalRing.notMem_maximalIdeal.mp hx
        have htop : Ideal.span ({x} : Set R) = ⊤ :=
          Ideal.span_singleton_eq_top.mpr hunit
        have hI : Ideal.ofList (x :: rs) = ⊤ := by
          apply top_unique
          rw [← htop]
          apply Ideal.span_le.mpr
          intro y hy
          rcases Set.mem_singleton_iff.mp hy with rfl
          exact Ideal.subset_span (by simp)
        have heq : (⊤ : Submodule R M) =
            Ideal.ofList (x :: rs) • (⊤ : Submodule R M) := by
          simp [hI]
        exact hxs.top_ne_smul heq
      let K : Ideal R := Ideal.span ({x} : Set R)
      let S := R ⧸ K
      let f : R →+* S := Ideal.Quotient.mk K
      have hKne : K ≠ ⊤ := by
        have hKle : K ≤ maximalIdeal R := by
          apply Ideal.span_le.mpr
          intro y hy
          rcases Set.mem_singleton_iff.mp hy with rfl
          exact hx
        intro hK
        apply (maximalIdeal.isMaximal R).ne_top
        exact le_antisymm le_top (by simpa [hK] using hKle)
      haveI : Nontrivial S := Ideal.Quotient.nontrivial_iff.mpr hKne
      haveI : IsLocalRing S := IsLocalRing.of_surjective' f f.surjective
      let I : Ideal R := Ideal.ofList (x :: rs)
      let J : Ideal S := Ideal.ofList (rs.map f)
      have hIJ : J = I.map f := by
        rw [show I = Ideal.span ({x} : Set R) ⊔ Ideal.ofList rs by
          simp [I, Ideal.ofList]]
        rw [Ideal.map_sup, Ideal.map_span, Ideal.map_ofList]
        simp only [Set.image_singleton]
        have hx0 : f x = 0 := by
          apply Ideal.Quotient.eq_zero_iff_mem.mpr
          exact Ideal.subset_span (by simp [K])
        rw [hx0]
        simp [J]
      have hH : I ≤ J.comap f := by
        rw [hIJ]
        exact Ideal.le_comap_map
      have hH' : J.comap f ≤ I := by
        rw [hIJ, Ideal.comap_map_of_surjective f f.surjective]
        apply sup_le le_rfl
        have hKle : K ≤ I := by
          apply Ideal.span_le.mpr
          intro y hy
          rcases Set.mem_singleton_iff.mp hy with rfl
          exact Ideal.subset_span (by simp [I])
        intro y hy
        apply hKle
        apply Ideal.Quotient.eq_zero_iff_mem.mp
        change f y = 0
        simpa using hy
      let qmap : R ⧸ I →+* S ⧸ J := Ideal.quotientMap J f hH
      let he : R ⧸ I ≃+* S ⧸ J :=
        RingEquiv.ofBijective qmap ⟨
          Ideal.quotientMap_injective' hH',
          Ideal.quotientMap_surjective f.surjective⟩
      letI : RingHomInvPair he.toRingHom he.symm.toRingHom :=
        RingHomInvPair.of_ringEquiv he
      letI : RingHomInvPair he.symm.toRingHom he.toRingHom :=
        RingHomInvPair.of_ringEquiv he.symm
      have he_mk (r : R) :
          he.toRingHom (Ideal.Quotient.mk I r) =
            Ideal.Quotient.mk J (f r) := by
        simp [he, qmap, Ideal.quotientMap]
      have hsub :
          (Ideal.ofList rs • (⊤ : Submodule R (QuotSMulTop x M))).toAddSubgroup =
            (Ideal.ofList (rs.map f) •
              (⊤ : Submodule S (QuotSMulTop x M))).toAddSubgroup := by
        have hsub' :
            (Ideal.ofList (rs.map f) •
                (⊤ : Submodule S (QuotSMulTop x M))).restrictScalars R =
              Ideal.ofList rs • (⊤ : Submodule R (QuotSMulTop x M)) := by
          rw [← Ideal.map_ofList]
          change (Ideal.map (Ideal.Quotient.mk K) (Ideal.ofList rs) •
            (⊤ : Submodule S (QuotSMulTop x M))).restrictScalars R = _
          have hf : algebraMap R S = Ideal.Quotient.mk K :=
            Ideal.Quotient.algebraMap_eq K
          simpa only [hf, Submodule.restrictScalars_top] using
            (Ideal.smul_restrictScalars (Ideal.ofList rs)
            (⊤ : Submodule S (QuotSMulTop x M)))
        exact congrArg Submodule.toAddSubgroup hsub'.symm
      let eqAdd :
          (QuotSMulTop x M ⧸
              (Ideal.ofList rs • (⊤ : Submodule R (QuotSMulTop x M)))) ≃+
            (QuotSMulTop x M ⧸
              (Ideal.ofList (rs.map f) •
                (⊤ : Submodule S (QuotSMulTop x M)))) :=
        QuotientAddGroup.congr _ _ (AddEquiv.refl (QuotSMulTop x M)) (by
          simpa using hsub)
      let qinner :=
        Submodule.quotOfListConsSMulTopEquivQuotSMulTopInner M x rs
      let eadd := qinner.toAddEquiv.trans eqAdd
      let esem :
          (M ⧸ (Ideal.ofList (x :: rs) • (⊤ : Submodule R M))) ≃ₛₗ[he.toRingHom]
            (QuotSMulTop x M ⧸
              (Ideal.ofList (rs.map f) •
                (⊤ : Submodule S (QuotSMulTop x M)))) :=
        { eadd with
          map_smul' := by
            intro a z
            obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective a
            refine Submodule.Quotient.induction_on
              (Ideal.ofList (x :: rs) • (⊤ : Submodule R M)) z ?_
            intro m
            change eqAdd (qinner (r • Submodule.Quotient.mk m)) =
              he.toRingHom (Ideal.Quotient.mk I r) •
                eqAdd (qinner (Submodule.Quotient.mk m))
            rw [he_mk, qinner.map_smul]
            obtain ⟨q, hq⟩ := Submodule.Quotient.mk_surjective
              (Ideal.ofList rs • (⊤ : Submodule R (QuotSMulTop x M)))
              (qinner (Submodule.Quotient.mk m))
            rw [← hq]
            rw [← Submodule.Quotient.mk_smul]
            dsimp [eqAdd]
            rw [← Submodule.Quotient.mk_smul]
            change Submodule.Quotient.mk (r • q) =
              Submodule.Quotient.mk (f r • q)
            congr 1 }
      have hfreeQ : Module.Free (S ⧸ J)
          (QuotSMulTop x M ⧸
            (Ideal.ofList (rs.map f) •
              (⊤ : Submodule S (QuotSMulTop x M)))) := by
        exact Module.Free.of_equiv esem
      letI : Module.Finite R (QuotSMulTop x M) :=
        Module.Finite.of_surjective (Submodule.mkQ _) (Submodule.mkQ_surjective _)
      letI : Module.Finite S (QuotSMulTop x M) :=
        Module.Finite.of_restrictScalars_finite R S (QuotSMulTop x M)
      have hfreeM : Module.Free S (QuotSMulTop x M) :=
        aux (R := S) (M := QuotSMulTop x M) (rs.map f) htail hfreeQ
      exact free_mod_x x hx hxreg (by simpa [S, K] using hfreeM)
  termination_by xs.length
  decreasing_by
    simp_all only [List.length_map, List.length_cons]
    omega
  exact aux xs hxs hfree

private theorem spanFinrank_maximalIdeal_le_of_regular_quotient
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (x : R) (hx : x ∈ maximalIdeal R) (hreg : IsSMulRegular R x)
    (hquot : IsRegularLocalRing (R ⧸ Ideal.span ({x} : Set R))) :
    (maximalIdeal R).spanFinrank ≤ ringKrullDim R := by
  classical
  let K : Ideal R := Ideal.span ({x} : Set R)
  let S := R ⧸ K
  haveI : IsRegularLocalRing S := hquot
  haveI : IsLocalHom (Ideal.Quotient.mk K) :=
    (Ideal.Quotient.mk_surjective (I := K)).isLocalHom
  obtain ⟨ys, hys, hyslen⟩ :=
    exists_minimalIdealGeneratingList (R := S)
  let lift : S → R := fun y => Classical.choose (Ideal.Quotient.mk_surjective y)
  have hlift (y : S) : Ideal.Quotient.mk K (lift y) = y :=
    Classical.choose_spec (Ideal.Quotient.mk_surjective y)
  let ys' := ys.map lift
  let I : Ideal R := Ideal.ofList (x :: ys')
  have hysmem : ∀ y ∈ ys, y ∈ maximalIdeal S := by
    intro y hy
    rw [← hys.1]
    exact Ideal.subset_span hy
  have hImap : Ideal.map (Ideal.Quotient.mk K) I = Ideal.ofList ys := by
    rw [show I = Ideal.span ({x} : Set R) ⊔ Ideal.ofList ys' by
      simp [I, Ideal.ofList]]
    rw [Ideal.map_sup]
    have hxmap : Ideal.map (Ideal.Quotient.mk K) (Ideal.span ({x} : Set R)) = ⊥ := by
      rw [Ideal.map_span]
      simp [K]
    rw [hxmap, bot_sup_eq, Ideal.map_ofList]
    have hlist : List.map (Ideal.Quotient.mk K) ys' = ys := by
      simpa [ys', Function.comp_def] using
        (List.map_congr_left (l := ys)
          (f := fun y => Ideal.Quotient.mk K (lift y)) (g := id)
          (fun y hy => by simpa [Function.comp_def] using hlift y))
    exact congrArg Ideal.ofList hlist
  have hIle : I ≤ maximalIdeal R := by
    apply Ideal.span_le.mpr
    intro y hy
    rcases List.mem_cons.mp hy with rfl | hy
    · exact hx
    · obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hy
      rw [← IsLocalRing.maximalIdeal_comap (Ideal.Quotient.mk K)]
      simpa [hlift z] using hysmem z hz
  have hIe : I = maximalIdeal R := by
    apply le_antisymm hIle
    intro r hr
    have hmr0 : Ideal.Quotient.mk K r ∈ maximalIdeal S := by
      change r ∈ Ideal.comap (Ideal.Quotient.mk K) (maximalIdeal S)
      rw [IsLocalRing.maximalIdeal_comap (Ideal.Quotient.mk K)]
      exact hr
    have hmr : Ideal.Quotient.mk K r ∈ Ideal.ofList ys := by
      rw [hys.1]
      exact hmr0
    have hmr' : Ideal.Quotient.mk K r ∈ Ideal.map (Ideal.Quotient.mk K) I := by
      rw [hImap]
      exact hmr
    obtain ⟨a, ha, hma⟩ :=
      (Ideal.mem_map_iff_of_surjective (Ideal.Quotient.mk K)
        Ideal.Quotient.mk_surjective).mp hmr'
    have hdiff : r - a ∈ K := by
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      rw [map_sub, hma, sub_self]
    have hdiff' : r - a ∈ I := by
      have hKI : K ≤ I := by
        apply Ideal.span_le.mpr
        intro y hy
        rcases Set.mem_singleton_iff.mp hy with rfl
        exact Ideal.subset_span (by simp [I])
      exact hKI (by simpa [K] using hdiff)
    simpa [sub_eq_add_neg] using add_mem ha hdiff'
  have hspan : Ideal.span ((↑((x :: ys').toFinset) : Finset R) : Set R) =
      maximalIdeal R := by
    simpa [I, Ideal.ofList, Ideal.span_insert] using hIe
  have hspan' : Submodule.span R (↑((x :: ys').toFinset) : Set R) =
      maximalIdeal R := hspan
  have hle := Submodule.spanFinrank_span_le_ncard_of_finite
    (R := R) (M := R) (s := (↑((x :: ys').toFinset) : Set R))
      ((x :: ys').toFinset).finite_toSet
  rw [hspan'] at hle
  have hcard : ((x :: ys').toFinset).card ≤ (x :: ys').length :=
    List.toFinset_card_le _
  have hcard' : (↑((x :: ys').toFinset) : Set R).ncard ≤ 1 + ys.length := by
    calc
      (↑((x :: ys').toFinset) : Set R).ncard = (x :: ys').toFinset.card :=
        Set.ncard_coe_finset _
      _ ≤ (x :: ys').length := hcard
      _ = 1 + ys.length := by simp [ys']; omega
  have hle' : (maximalIdeal R).spanFinrank ≤ 1 + ys.length := by
    exact le_trans hle hcard'
  have hdimS : ringKrullDim S = ys.length := by
    simpa [hyslen] using ((isRegularLocalRing_iff S).mp hquot).symm
  have hdim : ringKrullDim S + 1 = ringKrullDim R :=
    ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim
      (R := R) (x := x) hreg hx
  rw [hdimS] at hdim
  rw [← hdim]
  exact_mod_cast (by simpa [Nat.add_comm] using hle')

/-- Every maximal Cohen--Macaulay module over a regular local ring is free. -/
theorem regular_mcm_free
    {R M : Type u} [CommRing R] [IsRegularLocalRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M]
    (hM : IsMaximalCohenMacaulay R M) :
    Module.Free R M := by
  classical
  by_cases hsub : Subsingleton M
  · letI : Subsingleton M := hsub
    infer_instance
  · letI : Nontrivial M := not_subsingleton_iff_nontrivial.mp hsub
    obtain ⟨xs, hxs, hxslen⟩ :=
      exists_minimalIdealGeneratingList (R := R)
    have hMcm : IsCohenMacaulay R M :=
      (isMaximalCohenMacaulay_iff.mp hM).1
    let N := M ⧸ (maximalIdeal R • (⊤ : Submodule R M))
    have hNtop : maximalIdeal R • (⊤ : Submodule R M) ≠ ⊤ :=
      Formalization.Books.Algebra.Unit72.smul_top_ne_top_of_le_ring_jacobson
        (maximalIdeal R) M
        (maximalIdeal_le_jacobson (⊥ : Ideal R))
    have hNnontr : Nontrivial N := by
      exact Submodule.Quotient.nontrivial_iff.mpr hNtop
    have hNsupp : Module.support R N ⊆
        PrimeSpectrum.zeroLocus (maximalIdeal R) := by
      rw [Module.support_quotient]
      exact Set.inter_subset_right
    have hNdim : Module.supportDim R N = 0 := by
      have hsubsupp : ∀ p q : Module.support R N, p = q := by
        intro p q
        apply Subtype.ext
        have hp := hNsupp p.property
        have hq := hNsupp q.property
        rw [PrimeSpectrum.zeroLocus_eq_singleton] at hp hq
        exact (Set.mem_singleton_iff.mp hp).trans (Set.mem_singleton_iff.mp hq).symm
      letI : Subsingleton (Module.support R N) := ⟨hsubsupp⟩
      have hle : Module.supportDim R N ≤ 0 := by
        change Order.krullDim (Module.support R N) ≤ 0
        exact Order.krullDim_nonpos_of_subsingleton
      have hne : Module.supportDim R N ≠ ⊥ :=
        (Module.supportDim_ne_bot_iff_nontrivial R N).mpr hNnontr
      have hge : (0 : WithBot ℕ∞) ≤ Module.supportDim R N := by
        cases hdN : Module.supportDim R N with
        | bot => exact (hne hdN).elim
        | coe q => exact WithBot.coe_le_coe.mpr (by simp)
      exact le_antisymm hle hge
    let g : Fin xs.length → R := fun i => xs.get i
    have hlist : List.ofFn g = xs := by
      simpa only [g] using List.ofFn_get xs
    have hg : ∀ i, g i ∈ maximalIdeal R := by
      intro i
      change xs.get i ∈ maximalIdeal R
      rw [← hxs.1]
      exact Ideal.subset_span (List.get_mem xs i)
    have hMdim : Module.supportDim R M =
        (((xs.length : ℕ∞) : WithBot ℕ∞)) := by
      calc
        Module.supportDim R M = ringKrullDim R :=
          (isMaximalCohenMacaulay_iff.mp hM).2
        _ = (maximalIdeal R).spanFinrank :=
          (IsRegularLocalRing.spanFinrank_maximalIdeal (R := R)).symm
        _ = (((xs.length : ℕ∞) : WithBot ℕ∞)) := by
          rw [← hxslen]
          rfl
    have hquot : Module.supportDim R
        (Formalization.Books.Algebra.Unit103.quotientByList M
          (List.ofFn g)) = 0 := by
      change Module.supportDim R
        (M ⧸ (Ideal.ofList (List.ofFn g) • (⊤ : Submodule R M))) = 0
      rw [hlist, hxs.1]
      exact hNdim
    have hregM : RingTheory.Sequence.IsRegular M xs := by
      have hres :=
        Formalization.Books.Algebra.Unit103.regularSequence_of_supportDim_quotient_eq
          xs.length xs.length hMcm g le_rfl hMdim hg (by simpa using hquot)
      simpa only [hlist] using hres.1
    letI : Field (R ⧸ maximalIdeal R) := Ideal.Quotient.field (maximalIdeal R)
    have hfreeN : Module.Free (R ⧸ maximalIdeal R) N := by infer_instance
    exact free_of_regular_sequence xs hregM (by
      rw [hxs.1]
      simpa [N] using hfreeN)

/-! ## Cutting by regular sequences -/

/-- A nonzerodivisor whose quotient is regular local lifts regularity to the
original Noetherian local ring. -/
theorem regular_local_of_regular_element
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (x : R) (hx : x ∈ maximalIdeal R)
    (hreg : IsSMulRegular R x)
    (hquot : IsRegularLocalRing (R ⧸ Ideal.span ({x} : Set R))) :
    IsRegularLocalRing R := by
  exact IsRegularLocalRing.of_spanFinrank_maximalIdeal_le (R := R)
    (spanFinrank_maximalIdeal_le_of_regular_quotient x hx hreg hquot)

open scoped Pointwise in
/-- The preceding lifting statement for a regular sequence and its quotient. -/
theorem regular_local_of_regular_sequence
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (xs : List R) (hxs : RingTheory.Sequence.IsRegular R xs)
    (hquot : IsRegularLocalRing (R ⧸ Ideal.ofList xs)) :
    IsRegularLocalRing R := by
  let rec aux {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
      (xs : List R) (hxs : RingTheory.Sequence.IsRegular R xs)
      (hquot : IsRegularLocalRing (R ⧸ Ideal.ofList xs)) :
      IsRegularLocalRing R := by
    cases xs with
    | nil =>
      have hnil : Ideal.ofList ([] : List R) = (⊥ : Ideal R) := by
        simp [Ideal.ofList]
      haveI : IsRegularLocalRing (R ⧸ (⊥ : Ideal R)) := hnil ▸ hquot
      exact IsRegularLocalRing.of_ringEquiv (RingEquiv.quotientBot R)
    | cons x rs =>
      obtain ⟨hxreg, htail⟩ :=
        (RingTheory.Sequence.isRegular_cons_iff' R x rs).mp hxs
      have hx : x ∈ maximalIdeal R := by
        by_contra hx
        have hunit : IsUnit x := IsLocalRing.notMem_maximalIdeal.mp hx
        have htop : Ideal.span ({x} : Set R) = ⊤ :=
          Ideal.span_singleton_eq_top.mpr hunit
        have hI : Ideal.ofList (x :: rs) = ⊤ := by
          apply top_unique
          rw [← htop]
          apply Ideal.span_le.mpr
          intro y hy
          rcases Set.mem_singleton_iff.mp hy with rfl
          exact Ideal.subset_span (by simp)
        have hsub : Subsingleton (R ⧸ Ideal.ofList (x :: rs)) := by
          simp [hI]
        exact (not_subsingleton_iff_nontrivial.mpr inferInstance) hsub
      let K : Ideal R := Ideal.span ({x} : Set R)
      let S := R ⧸ K
      let f : R →+* S := Ideal.Quotient.mk K
      have hKne : K ≠ ⊤ := by
        have hKle : K ≤ maximalIdeal R := by
          apply Ideal.span_le.mpr
          intro y hy
          rcases Set.mem_singleton_iff.mp hy with rfl
          exact hx
        intro hK
        apply (maximalIdeal.isMaximal R).ne_top
        exact le_antisymm le_top (by simpa [hK] using hKle)
      haveI : Nontrivial S := Ideal.Quotient.nontrivial_iff.mpr hKne
      haveI : IsLocalRing S := IsLocalRing.of_surjective' f f.surjective
      have htailS : RingTheory.Sequence.IsRegular S
          (rs.map f) := by
        let e : QuotSMulTop x R ≃+* S :=
          (Ideal.quotientEquivAlgOfEq R (by
            symm
            rw [← Submodule.ideal_span_singleton_smul]
            change (Ideal.span ({x} : Set R) : Ideal R) * (⊤ : Ideal R) = K
            rw [Ideal.mul_top])).symm.toRingEquiv
        let ea : QuotSMulTop x R ≃ₗ[S] S :=
          { e.toAddEquiv with
            map_smul' := by
              intro a z
              obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective a
              rw [Module.IsTorsionBy.mk_smul
                (Module.isTorsionBy_quotient_element_smul (R := R) R x)]
              refine Submodule.Quotient.induction_on (x • (⊤ : Submodule R R)) z ?_
              intro m
              rfl }
        simpa using (ea.isRegular_congr' (rs.map f)).mp htail
      let I : Ideal R := Ideal.ofList (x :: rs)
      let J : Ideal S := Ideal.ofList (rs.map f)
      have hIJ : J = I.map f := by
        rw [show I = Ideal.span ({x} : Set R) ⊔ Ideal.ofList rs by
          simp [I, Ideal.ofList]]
        rw [Ideal.map_sup, Ideal.map_span, Ideal.map_ofList]
        simp only [Set.image_singleton]
        have hx0 : f x = 0 := by
          apply Ideal.Quotient.eq_zero_iff_mem.mpr
          exact Ideal.subset_span (by simp [K])
        rw [hx0]
        simp [J]
      have hH : I ≤ J.comap f := by
        rw [hIJ]
        exact Ideal.le_comap_map
      have hH' : J.comap f ≤ I := by
        rw [hIJ, Ideal.comap_map_of_surjective f f.surjective]
        apply sup_le le_rfl
        have hKle : K ≤ I := by
          apply Ideal.span_le.mpr
          intro y hy
          rcases Set.mem_singleton_iff.mp hy with rfl
          exact Ideal.subset_span (by simp [I])
        intro y hy
        apply hKle
        apply Ideal.Quotient.eq_zero_iff_mem.mp
        change f y = 0
        simpa using hy
      let qmap : R ⧸ I →+* S ⧸ J := Ideal.quotientMap J f hH
      have he : R ⧸ I ≃+* S ⧸ J :=
        RingEquiv.ofBijective qmap ⟨
          Ideal.quotientMap_injective' hH',
          Ideal.quotientMap_surjective f.surjective⟩
      have hquotS : IsRegularLocalRing (S ⧸ J) := by
        haveI : IsRegularLocalRing (R ⧸ I) := by simpa [I] using hquot
        exact IsRegularLocalRing.of_ringEquiv he
      have hbaseS : IsRegularLocalRing S :=
        aux (R := S) (rs.map f) htailS hquotS
      exact regular_local_of_regular_element x hx hxreg (by
        simpa [S, K] using hbaseS)
  termination_by xs.length
  decreasing_by
    simp_all
  exact aux xs hxs hquot

/-! ## Directed colimits -/

/-- A Noetherian directed colimit of regular local rings along local maps is
regular local. -/
theorem colimit_regular
    {ι : Type u} [Preorder ι] [Nonempty ι] [IsDirectedOrder ι]
    {A : ι → Type v} [∀ i, CommRing (A i)]
    (f : ∀ i j, i ≤ j → A i →+* A j)
    [DirectedSystem A (f · · ·)]
    (hlocal : ∀ i j (hij : i ≤ j), IsLocalHom (f i j hij))
    (hregular : ∀ i, IsRegularLocalRing (A i))
    (hnoetherian : IsNoetherianRing (DirectLimit A f)) :
    IsRegularLocalRing (DirectLimit A f) := by
  sorry

end

end Formalization.Books.Algebra.Unit106
