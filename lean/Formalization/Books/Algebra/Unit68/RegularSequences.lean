import Mathlib.Algebra.Module.LocalizedModule.AtPrime
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.MvPolynomial
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.RingTheory.MvPolynomial.Ideal
import Mathlib.RingTheory.Polynomial.Quotient
import Mathlib.RingTheory.Regular.Flat
import Mathlib.RingTheory.RingHom.Flat

/-!
# Commutative Algebra, Chapter 68: Regular sequences

The source uses the convention that the final quotient of a regular sequence is nonzero.
Mathlib's `RingTheory.Sequence.IsRegular` has exactly this convention, while
`RingTheory.Sequence.IsWeaklyRegular` is the corresponding predicate with that final
condition omitted.  We therefore use those canonical predicates directly instead of
introducing a parallel definition.
-/

namespace Formalization.Books.Algebra.Unit68

open Function
open scoped TensorProduct

noncomputable section

universe u v

/-! ## Definition and examples -/

/-
The source's phrase “regular sequence in `I`” is the canonical regular-sequence predicate
together with the membership hypotheses `f ∈ I`; no additional predicate is needed.  The
order dependence is likewise already visible in the list argument of `IsRegular`.

The source warning about dropping the nonzero final quotient is represented by the distinction
between `IsRegular` and `IsWeaklyRegular` in the module API above.  The localization warning
concerns that convention and requires no separate declaration.
-/

abbrev globalExampleRing (k : Type u) [Field k] := MvPolynomial (Fin 3) k

def globalExampleSequence (k : Type u) [Field k] : List (globalExampleRing k) :=
  [ MvPolynomial.X 0,
    MvPolynomial.X 1 * (MvPolynomial.C 1 - MvPolynomial.X 0),
    MvPolynomial.X 2 * (MvPolynomial.C 1 - MvPolynomial.X 0) ]

def globalExampleReorderedSequence (k : Type u) [Field k] : List (globalExampleRing k) :=
  [ MvPolynomial.X 1 * (MvPolynomial.C 1 - MvPolynomial.X 0),
    MvPolynomial.X 2 * (MvPolynomial.C 1 - MvPolynomial.X 0),
    MvPolynomial.X 0 ]

theorem global_example_regular_sequence (k : Type u) [Field k] :
    RingTheory.Sequence.IsRegular (globalExampleRing k) (globalExampleSequence k) := by
  let e := MvPolynomial.finSuccEquiv k 2
  have h1e : (_root_.finSuccEquiv 2) (1 : Fin 3) = some (0 : Fin 2) := by
    rw [show (1 : Fin 3) = (0 : Fin 2).succ by decide, finSuccEquiv_succ]
  have h2e : (_root_.finSuccEquiv 2) (2 : Fin 3) = some (1 : Fin 2) := by
    rw [show (2 : Fin 3) = (1 : Fin 2).succ by decide, finSuccEquiv_succ]
  have hforall :
      List.Forall₂
        (fun (r : globalExampleRing k) (s : Polynomial (MvPolynomial (Fin 2) k)) =>
          ∀ x : globalExampleRing k, e.toAddEquiv (r • x) = s • e.toAddEquiv x)
        (globalExampleSequence k) ((globalExampleSequence k).map e) := by
    exact List.forall₂_map_right_iff.mpr <|
      List.forall₂_same.mpr fun r _ x => e.map_mul r x
  apply (e.toAddEquiv.isRegular_congr
    (as := globalExampleSequence k) (bs := (globalExampleSequence k).map e) hforall).mpr
  simp [globalExampleSequence, e, MvPolynomial.finSuccEquiv,
    MvPolynomial.optionEquivLeft_apply, MvPolynomial.renameEquiv_apply, h1e, h2e]
  refine ⟨Polynomial.isRegular_X.left, ?_⟩
  let P := Polynomial (MvPolynomial (Fin 2) k)
  let a : P := Polynomial.C (MvPolynomial.X (0 : Fin 2)) * ((1 : P) - Polynomial.X)
  have hs :
      IsSMulRegular (P ⧸ (Ideal.span {Polynomial.X} : Ideal P)) a := by
    rw [isSMulRegular_quotient_iff_mem_of_smul_mem]
    intro p hp
    have hspker :
        a * p ∈ RingHom.ker (Polynomial.evalRingHom (0 : MvPolynomial (Fin 2) k)) := by
      rw [Polynomial.ker_evalRingHom]
      simpa [a, smul_eq_mul] using hp
    have hprod :
        (Polynomial.evalRingHom (0 : MvPolynomial (Fin 2) k)) (a * p) = 0 := hspker
    change (a * p).eval 0 = 0 at hprod
    rw [Polynomial.eval_mul, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_sub, Polynomial.eval_one, Polynomial.eval_X, sub_zero, mul_one] at hprod
    have hzero : p.eval 0 = 0 := by
      apply (MvPolynomial.isRegular_X (n := 0)).left
      simpa only [mul_zero] using hprod
    have hpker : p ∈ RingHom.ker (Polynomial.evalRingHom (0 : MvPolynomial (Fin 2) k)) := by
      change p.eval 0 = 0
      exact hzero
    rw [Polynomial.ker_evalRingHom] at hpker
    simpa only [Polynomial.C_0, sub_zero] using hpker
  have hq :
      QuotSMulTop (Polynomial.X : P) P ≃ₗ[P]
        P ⧸ (Ideal.span {Polynomial.X} : Ideal P) := by
    apply Submodule.quotEquivOfEq
    rw [← Submodule.ideal_span_singleton_smul]
    change (Ideal.span {Polynomial.X} : Ideal P) * (⊤ : Ideal P) =
      Ideal.span {Polynomial.X}
    exact Ideal.mul_top _
  have hqa :
      IsSMulRegular (QuotSMulTop (Polynomial.X : P) P) a := by
    exact (hq.isSMulRegular_congr _).mpr hs
  have hI :
      Ideal.span ({Polynomial.X, a} : Set P) =
        Ideal.span ({Polynomial.X, Polynomial.C (MvPolynomial.X (0 : Fin 2))} : Set P) := by
    let I : Ideal P := Ideal.span ({Polynomial.X, a} : Set P)
    let J : Ideal P := Ideal.span
      ({Polynomial.X, Polynomial.C (MvPolynomial.X (0 : Fin 2))} : Set P)
    have hxa : Polynomial.X ∈ I := Ideal.subset_span (by simp)
    have haa : a ∈ I := Ideal.subset_span (by simp)
    have hxj : Polynomial.X ∈ J := Ideal.subset_span (by simp)
    have hcj : Polynomial.C (MvPolynomial.X (0 : Fin 2)) ∈ J := Ideal.subset_span (by simp)
    apply le_antisymm
    · rw [show Ideal.span ({Polynomial.X, a} : Set P) = I by rfl,
      show Ideal.span ({Polynomial.X, Polynomial.C (MvPolynomial.X (0 : Fin 2))} : Set P) = J by rfl]
      exact Ideal.span_le.mpr (by
        intro p hp
        rcases (by simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hp :
          p = Polynomial.X ∨ p = a) with rfl | rfl
        · exact hxj
        · exact J.mul_mem_right _ hcj)
    · rw [show Ideal.span ({Polynomial.X, a} : Set P) = I by rfl,
      show Ideal.span ({Polynomial.X, Polynomial.C (MvPolynomial.X (0 : Fin 2))} : Set P) = J by rfl]
      exact Ideal.span_le.mpr (by
        intro p hp
        rcases (by simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hp :
          p = Polynomial.X ∨ p = Polynomial.C (MvPolynomial.X (0 : Fin 2))) with rfl | rfl
        · exact hxa
        · rw [show Polynomial.C (MvPolynomial.X (0 : Fin 2)) =
            a + Polynomial.X * Polynomial.C (MvPolynomial.X (0 : Fin 2)) by
              dsimp [a]
              ring]
          exact I.add_mem haa (I.mul_mem_right _ hxa))
  have heq :
      (P ⧸ (Ideal.ofList [Polynomial.X, a] • (⊤ : Submodule P P))) ≃ₗ[P]
        QuotSMulTop a (QuotSMulTop (Polynomial.X : P) P) := by
    let e := Submodule.quotOfListConsSMulTopEquivQuotSMulTopInner P Polynomial.X [a]
    convert e using 1
    rw [Ideal.ofList_singleton, Submodule.ideal_span_singleton_smul]
  refine ⟨hqa, ?_⟩
  let B := MvPolynomial (Fin 1) k
  let eb := MvPolynomial.finSuccEquiv k 1
  have eb0 : eb (MvPolynomial.X (0 : Fin 2)) = Polynomial.X := by
    simp [eb, MvPolynomial.finSuccEquiv, MvPolynomial.optionEquivLeft_apply,
      MvPolynomial.renameEquiv_apply]
  have eb1 : eb (MvPolynomial.X (1 : Fin 2)) = Polynomial.C (MvPolynomial.X (0 : Fin 1)) := by
    have hb1 : (_root_.finSuccEquiv 1) (1 : Fin 2) = some (0 : Fin 1) := by
      rw [show (1 : Fin 2) = (0 : Fin 1).succ by decide, finSuccEquiv_succ]
    simp [eb, MvPolynomial.finSuccEquiv, MvPolynomial.optionEquivLeft_apply,
      MvPolynomial.renameEquiv_apply, hb1]
  let C := MvPolynomial (Fin 2) k
  let J0 : Ideal C := Ideal.span {MvPolynomial.X (0 : Fin 2)}
  let K0 : Ideal (Polynomial B) := Ideal.span {Polynomial.X}
  let cx : Polynomial B := Polynomial.C (MvPolynomial.X (0 : Fin 1) : B)
  have hebmap : K0 = J0.map (eb : C →+* Polynomial B) := by
    dsimp [J0, K0]
    rw [Ideal.map_span]
    simp only [Set.image_singleton]
    exact congrArg (fun z => Ideal.span ({z} : Set (Polynomial B))) eb0.symm
  let eqb : (C ⧸ J0) ≃ₐ[k] (Polynomial B ⧸ K0) :=
    Ideal.quotientEquivAlg J0 K0 eb hebmap
  have heqbx : eqb (Ideal.Quotient.mk J0 (MvPolynomial.X (1 : Fin 2))) =
      Ideal.Quotient.mk K0 cx := by
    simp [eqb, eb1, cx]
  have hpolyreg :
      IsSMulRegular (Polynomial B ⧸ K0)
        cx := by
    rw [isSMulRegular_quotient_iff_mem_of_smul_mem]
    intro p hp
    have hker :
        cx * p ∈
          RingHom.ker (Polynomial.evalRingHom (0 : B)) := by
      rw [Polynomial.ker_evalRingHom]
      simpa [smul_eq_mul] using hp
    have hprod :
        (Polynomial.evalRingHom (0 : B)) (cx * p) = 0 := hker
    change (cx * p).eval 0 = 0 at hprod
    rw [Polynomial.eval_mul, Polynomial.eval_C] at hprod
    have hzero : p.eval 0 = 0 := by
      apply (MvPolynomial.isRegular_X (n := 0)).left
      simpa only [mul_zero] using hprod
    have hpker : p ∈ RingHom.ker (Polynomial.evalRingHom (0 : B)) := by
      change p.eval 0 = 0
      exact hzero
    rw [Polynomial.ker_evalRingHom] at hpker
    simpa [K0, Polynomial.C_0, sub_zero] using hpker
  have hcreg :
      IsSMulRegular (C ⧸ J0) (Ideal.Quotient.mk J0 (MvPolynomial.X (1 : Fin 2))) := by
    have heqmul : ∀ z : C ⧸ J0,
        eqb (Ideal.Quotient.mk J0 (MvPolynomial.X (1 : Fin 2)) * z) =
          Ideal.Quotient.mk K0 (Polynomial.C (MvPolynomial.X (0 : Fin 1))) * eqb z := by
      intro z
      rw [map_mul, heqbx]
    exact (eqb.toEquiv.isSMulRegular_congr heqmul).mpr hpolyreg
  let Jp : Ideal P := Ideal.span
    ({Polynomial.X, Polynomial.C (MvPolynomial.X (0 : Fin 2) : C)} : Set P)
  let Kp : Ideal P := Ideal.span
    ({Polynomial.C (MvPolynomial.X (0 : Fin 2) : C),
      Polynomial.X - Polynomial.C (0 : C)} : Set P)
  have hswap : Ideal.span
      ({Polynomial.X, Polynomial.C (MvPolynomial.X (0 : Fin 2) : C)} : Set P) =
      Ideal.span
        ({Polynomial.C (MvPolynomial.X (0 : Fin 2) : C), Polynomial.X} : Set P) := by
    apply le_antisymm
    · refine Ideal.span_le.mpr ?_
      intro z hz
      rcases (by simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hz :
        z = Polynomial.X ∨ z = Polynomial.C (MvPolynomial.X (0 : Fin 2) : C)) with rfl | rfl
      · exact Ideal.subset_span (by simp)
      · exact Ideal.subset_span (by simp)
    · refine Ideal.span_le.mpr ?_
      intro z hz
      rcases (by simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hz :
        z = Polynomial.C (MvPolynomial.X (0 : Fin 2) : C) ∨ z = Polynomial.X) with rfl | rfl
      · exact Ideal.subset_span (by simp)
      · exact Ideal.subset_span (by simp)
  have hJK : Jp = Kp := by
    calc
      Jp = Ideal.span ({Polynomial.X, a} : Set P) := by
        dsimp [Jp]
        exact hI.symm
      _ = Ideal.span
          ({Polynomial.X, Polynomial.C (MvPolynomial.X (0 : Fin 2) : C)} : Set P) := by
        exact hI
      _ = Ideal.span
          ({Polynomial.C (MvPolynomial.X (0 : Fin 2) : C),
            Polynomial.X - Polynomial.C (0 : C)} : Set P) := by
        rw [hswap]
        simp [Polynomial.C_0, sub_zero]
      _ = Kp := by rfl
  let qP0 : (P ⧸ Jp) ≃ₐ[C] (P ⧸ Kp) :=
    Ideal.quotientEquivAlgOfEq C hJK
  let qP : (P ⧸ Jp) ≃ₐ[C] (C ⧸ J0) :=
    qP0.trans
      (Polynomial.quotientSpanCXSubCAlgEquiv
        (MvPolynomial.X (0 : Fin 2) : C) (0 : C))
  let b : P := Polynomial.C (MvPolynomial.X (1 : Fin 2) : C) * (1 - Polynomial.X)
  have hqPb : qP (Ideal.Quotient.mk Jp b) =
      Ideal.Quotient.mk J0 (MvPolynomial.X (1 : Fin 2)) := by
    have hc : qP (Ideal.Quotient.mk Jp
        (Polynomial.C (MvPolynomial.X (1 : Fin 2) : C))) =
        Ideal.Quotient.mk J0 (MvPolynomial.X (1 : Fin 2)) := by
      rw [show Polynomial.C (MvPolynomial.X (1 : Fin 2) : C) =
          algebraMap C P (MvPolynomial.X (1 : Fin 2) : C) by rfl,
        Ideal.Quotient.mk_algebraMap]
      exact (qP.commutes (MvPolynomial.X (1 : Fin 2) : C)).trans
        (by rfl)
    have hx : qP (Ideal.Quotient.mk Jp (Polynomial.X : P)) = 0 := by
      have hx0 : Ideal.Quotient.mk Jp (Polynomial.X : P) = 0 := by
        apply Ideal.Quotient.eq_zero_iff_mem.2
        exact Ideal.subset_span (by simp [Jp])
      rw [hx0, map_zero]
    calc
      qP (Ideal.Quotient.mk Jp b) =
          qP (Ideal.Quotient.mk Jp
            (Polynomial.C (MvPolynomial.X (1 : Fin 2) : C)) *
              (1 - Ideal.Quotient.mk Jp (Polynomial.X : P))) := by rfl
      _ = qP (Ideal.Quotient.mk Jp
            (Polynomial.C (MvPolynomial.X (1 : Fin 2) : C))) *
          qP (1 - Ideal.Quotient.mk Jp (Polynomial.X : P)) := qP.map_mul _ _
      _ = Ideal.Quotient.mk J0 (MvPolynomial.X (1 : Fin 2)) := by
        have hsub : qP (1 - Ideal.Quotient.mk Jp (Polynomial.X : P)) =
            1 - qP (Ideal.Quotient.mk Jp (Polynomial.X : P)) := by
          simpa only [AlgEquiv.coe_ringEquiv, RingEquiv.coe_toRingHom,
            AlgEquiv.toRingEquiv_toRingHom, map_one] using
            qP.toRingEquiv.map_sub (1 : P ⧸ Jp)
              (Ideal.Quotient.mk Jp (Polynomial.X : P))
        rw [hsub, hc, hx, sub_zero, mul_one]
  have hsource :
      IsSMulRegular (P ⧸ Jp) (Ideal.Quotient.mk Jp b) := by
    have hcreg' :
        IsSMulRegular (C ⧸ J0) (qP (Ideal.Quotient.mk Jp b)) := by
      rw [hqPb]
      exact hcreg
    intro x y hxy
    apply qP.injective
    apply hcreg'
    simpa only [smul_eq_mul, map_mul] using congrArg qP hxy
  have hlistI :
      (Ideal.ofList [Polynomial.X, a] • (⊤ : Submodule P P)) =
        (Jp : Submodule P P) := by
    change (Ideal.ofList [Polynomial.X, a] : Ideal P) * (⊤ : Ideal P) = Jp
    rw [Ideal.mul_top]
    change Ideal.span {r : P | r ∈ [Polynomial.X, a]} = Jp
    have hset : {r : P | r ∈ [Polynomial.X, a]} =
        ({Polynomial.X, a} : Set P) := by
      ext r
      simp [Set.mem_insert_iff, Set.mem_singleton_iff, or_comm]
    rw [hset]
    exact hI
  have hlist :
      (P ⧸ (Ideal.ofList [Polynomial.X, a] • (⊤ : Submodule P P))) ≃ₗ[P]
        P ⧸ Jp := by
    apply Submodule.quotEquivOfEq
    exact hlistI
  have hthird :
      IsSMulRegular
        (P ⧸ (Ideal.ofList [Polynomial.X, a] • (⊤ : Submodule P P))) b := by
    exact (hlist.isSMulRegular_congr _).mpr hsource
  have hnested :
      IsSMulRegular (QuotSMulTop a (QuotSMulTop (Polynomial.X : P) P)) b := by
    exact (heq.isSMulRegular_congr _).mp hthird
  let evC : C →+* k :=
    MvPolynomial.eval₂Hom (RingHom.id k) (fun _ => 0)
  let ev : P →+* k := Polynomial.eval₂RingHom evC 0
  let J3 : Ideal P := Ideal.span
    ({Polynomial.X, a, b} : Set P)
  have hJ3ker : J3 ≤ RingHom.ker ev := by
    dsimp [J3]
    refine Ideal.span_le.mpr ?_
    intro p hp
    rcases (by simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hp :
      p = Polynomial.X ∨
        p = a ∨ p = b) with rfl | rfl | rfl
    · change (Polynomial.X : P).eval₂ evC 0 = 0
      rw [Polynomial.eval₂_X]
    · change (Polynomial.C (MvPolynomial.X (0 : Fin 2) : C) *
        (1 - Polynomial.X)).eval₂ evC 0 = 0
      rw [Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_sub,
        Polynomial.eval₂_one, Polynomial.eval₂_X]
      rw [MvPolynomial.eval₂Hom_X']
      simp
    · change (Polynomial.C (MvPolynomial.X (1 : Fin 2) : C) *
        (1 - Polynomial.X)).eval₂ evC 0 = 0
      rw [Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_sub,
        Polynomial.eval₂_one, Polynomial.eval₂_X]
      rw [MvPolynomial.eval₂Hom_X']
      simp
  have hJ3 : J3 ≠ (⊤ : Ideal P) := by
    intro htop
    have h1 : (1 : P) ∈ J3 := by
      rw [htop]
      simp
    have h10 : ev (1 : P) = 0 := hJ3ker h1
    have hzero : (1 : k) = 0 := by
      simpa [ev] using h10
    exact one_ne_zero hzero
  have hlist3I :
      (Ideal.ofList [Polynomial.X, a, b] • (⊤ : Submodule P P)) =
        (J3 : Submodule P P) := by
    change (Ideal.ofList [Polynomial.X, a, b] : Ideal P) * (⊤ : Ideal P) = J3
    rw [Ideal.mul_top]
    change Ideal.span {r : P | r ∈ [Polynomial.X, a, b]} = J3
    have hset : {r : P | r ∈ [Polynomial.X, a, b]} =
        ({Polynomial.X, a, b} : Set P) := by
      ext r
      simp only [Set.mem_setOf_eq, List.mem_cons, List.mem_singleton,
        List.not_mem_nil, or_false, Set.mem_insert_iff, Set.mem_singleton_iff]
    rw [hset]
  have hquot3 :
      Nontrivial (P ⧸ (Ideal.ofList [Polynomial.X, a, b] • (⊤ : Submodule P P))) := by
    rw [hlist3I, Ideal.Quotient.nontrivial_iff]
    exact hJ3
  have hperm :
      (Ideal.ofList [Polynomial.X, a, b] • (⊤ : Submodule P P)) =
        (Ideal.ofList [b, Polynomial.X, a] • (⊤ : Submodule P P)) := by
    change (Ideal.ofList [Polynomial.X, a, b] : Ideal P) * (⊤ : Ideal P) =
      (Ideal.ofList [b, Polynomial.X, a] : Ideal P) * (⊤ : Ideal P)
    rw [Ideal.mul_top, Ideal.mul_top]
    change Ideal.span {r : P | r ∈ [Polynomial.X, a, b]} =
      Ideal.span {r : P | r ∈ [b, Polynomial.X, a]}
    apply congrArg Ideal.span
    ext r
    change r ∈ [Polynomial.X, a, b] ↔ r ∈ [b, Polynomial.X, a]
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false]
    constructor
    · intro hr
      rcases hr with rfl | rfl | rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr rfl)
      · exact Or.inl rfl
    · intro hr
      rcases hr with rfl | rfl | rfl
      · exact Or.inr (Or.inr rfl)
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
  have hfinal_equiv :
      (P ⧸ (Ideal.ofList [Polynomial.X, a, b] • (⊤ : Submodule P P))) ≃ₗ[P]
        QuotSMulTop b (QuotSMulTop a (QuotSMulTop (Polynomial.X : P) P)) := by
    let eouter :=
      Submodule.quotOfListConsSMulTopEquivQuotSMulTopOuter P b
        [Polynomial.X, a]
    exact (Submodule.quotEquivOfEq
      (Ideal.ofList [Polynomial.X, a, b] • (⊤ : Submodule P P))
      (Ideal.ofList [b, Polynomial.X, a] • (⊤ : Submodule P P)) hperm).trans
      (eouter.trans (QuotSMulTop.congr b heq))
  letI : Nontrivial
      (QuotSMulTop b (QuotSMulTop a (QuotSMulTop (Polynomial.X : P) P))) :=
    hfinal_equiv.toEquiv.nontrivial_congr.mp hquot3
  exact ⟨hnested, RingTheory.Sequence.IsRegular.nil _ _⟩

theorem global_example_reordered_not_regular (k : Type u) [Field k] :
    ¬ RingTheory.Sequence.IsRegular (globalExampleRing k)
        (globalExampleReorderedSequence k) := by
  intro hreg
  let R := globalExampleRing k
  let x : R := MvPolynomial.X 0
  let y : R := MvPolynomial.X 1
  let z : R := MvPolynomial.X 2
  let first : R := y * (1 - x)
  let second : R := z * (1 - x)
  have hreg' : RingTheory.Sequence.IsRegular R (first :: [second, x]) := by
    simpa [globalExampleReorderedSequence, R, x, y, z, first, second] using hreg
  have hsecond :
      IsSMulRegular (QuotSMulTop first R) second := by
    have hparts :=
      (RingTheory.Sequence.isRegular_cons_iff R first [second, x]).mp hreg'
    exact
      ((RingTheory.Sequence.isRegular_cons_iff
        (QuotSMulTop first R) second [x]).mp hparts.2).1
  have hq :
      QuotSMulTop first R ≃ₗ[R]
        R ⧸ (Ideal.span {first} : Ideal R) := by
    apply Submodule.quotEquivOfEq
    rw [← Submodule.ideal_span_singleton_smul]
    change (Ideal.span {first} : Ideal R) * (⊤ : Ideal R) =
      Ideal.span {first}
    exact Ideal.mul_top _
  have hsecond' :
      IsSMulRegular (R ⧸ (Ideal.span {first} : Ideal R)) second := by
    exact (hq.isSMulRegular_congr _).mp hsecond
  have hyzero :
      Ideal.Quotient.mk (Ideal.span {first} : Ideal R) y = 0 := by
    apply hsecond'
    have hprod :
        Ideal.Quotient.mk (Ideal.span {first} : Ideal R) (second * y) = 0 := by
      apply Ideal.Quotient.eq_zero_iff_mem.2
      rw [show second * y = first * z by
        dsimp [first, second]
        ring]
      exact (Ideal.span {first} : Ideal R).mul_mem_right z
        (Ideal.subset_span (by simp))
    have hmk :
        second • (Ideal.Quotient.mk (Ideal.span {first} : Ideal R) y) =
          Ideal.Quotient.mk (Ideal.span {first} : Ideal R) (second * y) := by
      change second • (Submodule.Quotient.mk y : R ⧸ (Ideal.span {first} : Ideal R)) =
        (Submodule.Quotient.mk (second * y) : R ⧸ (Ideal.span {first} : Ideal R))
      simpa only [smul_eq_mul] using
        (Submodule.Quotient.mk_smul
          (p := (Ideal.span {first} : Ideal R)) second y).symm
    change second • (Ideal.Quotient.mk (Ideal.span {first} : Ideal R) y) =
      second • (0 : R ⧸ (Ideal.span {first} : Ideal R))
    rw [hmk, smul_zero]
    exact hprod
  let ev : R →+* k :=
    MvPolynomial.eval₂Hom (RingHom.id k)
      (fun i => if i = (0 : Fin 3) then 1 else if i = (1 : Fin 3) then 1 else 0)
  have hevy : ev y = 1 := by
    change MvPolynomial.eval₂Hom (RingHom.id k)
        (fun i => if i = (0 : Fin 3) then 1 else if i = (1 : Fin 3) then 1 else 0)
        (MvPolynomial.X 1) = 1
    rw [MvPolynomial.eval₂Hom_X']
    simp
  have hevx : ev x = 1 := by
    change MvPolynomial.eval₂Hom (RingHom.id k)
        (fun i => if i = (0 : Fin 3) then 1 else if i = (1 : Fin 3) then 1 else 0)
        (MvPolynomial.X 0) = 1
    rw [MvPolynomial.eval₂Hom_X']
    simp
  have hevfirst : ev first = 0 := by
    dsimp [first]
    rw [map_mul, map_sub, map_one, hevy, hevx]
    simp
  have hker :
      (Ideal.span {first} : Ideal R) ≤ RingHom.ker ev := by
    refine Ideal.span_le.mpr ?_
    intro p hp
    rcases (by simpa only [Set.mem_singleton_iff] using hp : p = first) with rfl
    exact hevfirst
  have hyI : y ∈ (Ideal.span {first} : Ideal R) :=
    (Ideal.Quotient.eq_zero_iff_mem).mp hyzero
  have hy0 : ev y = 0 := hker hyI
  have hone : (1 : k) = 0 := by
    simpa [hevy] using hy0
  exact one_ne_zero hone

inductive localExampleVariable
  | x
  | y
  | w (n : ℕ)
deriving DecidableEq

def localExampleX (k : Type u) [CommRing k] :
    MvPolynomial localExampleVariable k :=
  MvPolynomial.X .x

def localExampleY (k : Type u) [CommRing k] :
    MvPolynomial localExampleVariable k :=
  MvPolynomial.X .y

def localExampleW (k : Type u) [CommRing k] (n : ℕ) :
    MvPolynomial localExampleVariable k :=
  MvPolynomial.X (.w n)

def localExampleRelations (k : Type u) [CommRing k] :
    Set (MvPolynomial localExampleVariable k) :=
  Set.range (fun n : ℕ => localExampleY k * localExampleW k n) ∪
    Set.range (fun n : ℕ =>
      localExampleW k n - localExampleX k * localExampleW k (n + 1))

def localExampleIdeal (k : Type u) [CommRing k] :
    Ideal (MvPolynomial localExampleVariable k) :=
  Ideal.span (localExampleRelations k)

abbrev localExampleRing (k : Type u) [Field k] :=
  MvPolynomial localExampleVariable k ⧸ localExampleIdeal k

def localExampleXbar (k : Type u) [Field k] : localExampleRing k :=
  Ideal.Quotient.mk (localExampleIdeal k) (localExampleX k)

def localExampleYbar (k : Type u) [Field k] : localExampleRing k :=
  Ideal.Quotient.mk (localExampleIdeal k) (localExampleY k)

def localExampleWbar (k : Type u) [Field k] (n : ℕ) : localExampleRing k :=
  Ideal.Quotient.mk (localExampleIdeal k) (localExampleW k n)

def localExampleMaximalIdealGenerators (k : Type u) [Field k] :
    Set (localExampleRing k) :=
  {localExampleXbar k, localExampleYbar k} ∪ Set.range (localExampleWbar k)

def localExampleMaximalIdeal (k : Type u) [Field k] : Ideal (localExampleRing k) :=
  Ideal.span (localExampleMaximalIdealGenerators k)

theorem local_example_maximal_ideal_is_maximal (k : Type u) [Field k] :
    (localExampleMaximalIdeal k).IsMaximal := by
  let P := MvPolynomial localExampleVariable k
  let ev : P →+* k :=
    MvPolynomial.eval₂Hom (RingHom.id k) (fun _ => 0)
  have hev (i : localExampleVariable) :
      ev (MvPolynomial.X i) = 0 := by
    change MvPolynomial.eval₂Hom (RingHom.id k) (fun _ => 0)
      (MvPolynomial.X i) = 0
    rw [MvPolynomial.eval₂Hom_X']
  have hrel : localExampleIdeal k ≤ RingHom.ker ev := by
    rw [localExampleIdeal, localExampleRelations]
    refine Ideal.span_le.mpr ?_
    rintro p (hp | hp)
    · rcases hp with ⟨n, rfl⟩
      change ev (localExampleY k * localExampleW k n) = 0
      simp only [map_mul, show localExampleY k = MvPolynomial.X .y by rfl,
        show localExampleW k n = MvPolynomial.X (.w n) by rfl, hev, zero_mul]
    · rcases hp with ⟨n, rfl⟩
      change ev (localExampleW k n - localExampleX k * localExampleW k (n + 1)) = 0
      simp only [map_sub, map_mul, show localExampleW k n = MvPolynomial.X (.w n) by rfl,
        show localExampleX k = MvPolynomial.X .x by rfl,
        show localExampleW k (n + 1) = MvPolynomial.X (.w (n + 1)) by rfl,
        hev, zero_mul, sub_self]
  have hrel' : ∀ a, a ∈ localExampleIdeal k → ev a = 0 := by
    intro a ha
    exact hrel ha
  let f : localExampleRing k →+* k :=
    Ideal.Quotient.lift (localExampleIdeal k) ev hrel'
  have hf : Function.Surjective f := by
    intro c
    refine ⟨Ideal.Quotient.mk (localExampleIdeal k) (MvPolynomial.C c), ?_⟩
    change MvPolynomial.eval₂Hom (RingHom.id k) (fun _ => 0)
      (MvPolynomial.C c) = c
    rw [MvPolynomial.eval₂Hom_C]
    rfl
  have hbarX : f (localExampleXbar k) = 0 := by
    change f (Ideal.Quotient.mk (localExampleIdeal k) (localExampleX k)) = 0
    dsimp [f]
    exact hev .x
  have hbarY : f (localExampleYbar k) = 0 := by
    change f (Ideal.Quotient.mk (localExampleIdeal k) (localExampleY k)) = 0
    dsimp [f]
    exact hev .y
  have hbarW (n : ℕ) : f (localExampleWbar k n) = 0 := by
    change f (Ideal.Quotient.mk (localExampleIdeal k) (localExampleW k n)) = 0
    dsimp [f]
    exact hev (.w n)
  have hker : RingHom.ker f = localExampleMaximalIdeal k := by
    apply le_antisymm
    · intro a ha
      obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
      have hp0 : ev p = 0 := by
        change f (Ideal.Quotient.mk (localExampleIdeal k) p) = 0 at ha
        dsimp [f] at ha
        exact ha
      have hpc : MvPolynomial.constantCoeff p = 0 := by
        have he := MvPolynomial.eval₂Hom_eq_constantCoeff_of_vars
          (RingHom.id k) (p := p) (fun i hi => rfl)
        have he' : ev p = MvPolynomial.constantCoeff p := by
          change MvPolynomial.eval₂Hom (RingHom.id k) (fun _ => 0) p =
            MvPolynomial.constantCoeff p
          exact he
        exact he'.symm.trans hp0
      have hpI : p ∈ MvPolynomial.idealOfVars localExampleVariable k := by
        rw [MvPolynomial.idealOfVars, ← Set.image_univ,
          MvPolynomial.mem_ideal_span_X_image]
        intro m hm
        by_cases hm0 : m = 0
        · subst m
          exfalso
          apply (MvPolynomial.mem_support_iff.mp hm)
          simpa [MvPolynomial.constantCoeff_eq] using hpc
        · have hex : ∃ i, m i ≠ 0 := by
            by_contra h
            push Not at h
            apply hm0
            exact Finsupp.ext fun i => h i
          rcases hex with ⟨i, hi⟩
          exact ⟨i, Set.mem_univ _, hi⟩
      have hmap :
          Ideal.map (Ideal.Quotient.mk (localExampleIdeal k))
              (MvPolynomial.idealOfVars localExampleVariable k) ≤
            localExampleMaximalIdeal k := by
        rw [Ideal.map_le_iff_le_comap, MvPolynomial.idealOfVars]
        refine Ideal.span_le.mpr ?_
        rintro _ ⟨i, rfl⟩
        change Ideal.Quotient.mk (localExampleIdeal k) (MvPolynomial.X i) ∈
          localExampleMaximalIdeal k
        apply Ideal.subset_span
        cases i with
        | x =>
            simp [localExampleMaximalIdealGenerators, localExampleXbar, localExampleX]
        | y =>
            simp [localExampleMaximalIdealGenerators, localExampleYbar, localExampleY]
        | w n =>
            simp [localExampleMaximalIdealGenerators, localExampleWbar, localExampleW]
      exact hmap (Ideal.mem_map_of_mem _ hpI)
    · rw [localExampleMaximalIdeal, localExampleMaximalIdealGenerators]
      refine Ideal.span_le.mpr ?_
      intro a ha
      rcases ha with ha | ⟨n, rfl⟩
      · rcases ha with (rfl | rfl)
        · exact hbarX
        · exact hbarY
      · exact hbarW n
  have hfield : IsField (localExampleRing k ⧸ localExampleMaximalIdeal k) := by
    rw [← hker]
    exact (RingHom.quotientKerEquivOfSurjective hf).toMulEquiv.isField
      (Field.toIsField k)
  exact Ideal.Quotient.maximal_of_isField _ hfield

/- The `letI` supplies the prime instance needed by the canonical `AtPrime` localization. -/
noncomputable abbrev localExampleLocalizedRing (k : Type u) [Field k] : Type _ :=
  letI : (localExampleMaximalIdeal k).IsMaximal :=
    local_example_maximal_ideal_is_maximal k
  Localization.AtPrime (localExampleMaximalIdeal k)

def localExampleLocalizedX (k : Type u) [Field k] :
    localExampleLocalizedRing k :=
  algebraMap (localExampleRing k) (localExampleLocalizedRing k) (localExampleXbar k)

def localExampleLocalizedY (k : Type u) [Field k] :
    localExampleLocalizedRing k :=
  algebraMap (localExampleRing k) (localExampleLocalizedRing k) (localExampleYbar k)

theorem local_example_regular_sequence (k : Type u) [Field k] :
    RingTheory.Sequence.IsRegular (localExampleRing k)
      [localExampleXbar k, localExampleYbar k] := by
  have hregx : IsSMulRegular (localExampleRing k) (localExampleXbar k) := by
    apply (isSMulRegular_quotient_iff_mem_of_smul_mem
      (localExampleIdeal k) (localExampleX k)).mpr
    intro p hp
    classical
    let v : Sum ℕ ℕ → MvPolynomial localExampleVariable k
      | Sum.inl n => localExampleY k * localExampleW k n
      | Sum.inr n => localExampleW k n - localExampleX k * localExampleW k (n + 1)
    have hv :
        Ideal.span (Set.range v) = localExampleIdeal k := by
      rw [localExampleIdeal]
      congr 1
      ext z
      constructor
      · rintro ⟨i, rfl⟩
        rcases i with i | i
        · exact Or.inl ⟨i, rfl⟩
        · exact Or.inr ⟨i, rfl⟩
      · intro hz
        rcases hz with ⟨i, rfl⟩ | ⟨i, rfl⟩
        · exact ⟨Sum.inl i, rfl⟩
        · exact ⟨Sum.inr i, rfl⟩
    have hp' : localExampleX k * p ∈ Ideal.span (Set.range v) := by
      rw [hv]
      simpa only [smul_eq_mul] using hp
    obtain ⟨c, hc⟩ :=
      Finsupp.mem_ideal_span_range_iff_exists_finsupp.mp hp'
    let phi : Sum ℕ ℕ → ℕ := fun i =>
      match i with | Sum.inl n => n | Sum.inr n => n + 1
    let T : Finset ℕ := c.support.image phi
    obtain ⟨N, hN⟩ := T.exists_nat_subset_range
    have hcN (i : Sum ℕ ℕ) (hi : i ∈ c.support) :
        phi i < N := by
      simpa [T] using hN (Finset.mem_image.mpr ⟨i, hi, rfl⟩)
    let B := MvPolynomial (Option ℕ) k
    let J : Ideal B := Ideal.span {MvPolynomial.X none * MvPolynomial.X (some 0)}
    let Bq := B ⧸ J
    let q : B →+* Bq := Ideal.Quotient.mk J
    have hqYW : q (MvPolynomial.X none) * q (MvPolynomial.X (some 0)) = 0 := by
      change Ideal.Quotient.mk J (MvPolynomial.X none * MvPolynomial.X (some 0)) = 0
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
    let q0 : k →+* Bq := q.comp (MvPolynomial.C : k →+* B)
    let wmap : localExampleVariable → Polynomial Bq := fun i =>
      match i with
      | localExampleVariable.x => Polynomial.X
      | localExampleVariable.y => Polynomial.C (q (MvPolynomial.X none))
      | localExampleVariable.w n =>
          if h : n < N then
            Polynomial.C (q (MvPolynomial.X (some 0))) * Polynomial.X ^ (N - n)
          else Polynomial.C (q (MvPolynomial.X (some (n - N))))
    let f : MvPolynomial localExampleVariable k →+* Polynomial Bq :=
      MvPolynomial.eval₂Hom (Polynomial.C.comp q0) wmap
    have hfx : f (localExampleX k) = Polynomial.X := by
      dsimp [f, localExampleX, wmap]
      rw [MvPolynomial.eval₂_X]
    have hfy : f (localExampleY k) = Polynomial.C (q (MvPolynomial.X none)) := by
      dsimp [f, localExampleY, wmap]
      rw [MvPolynomial.eval₂_X]
    have hfw (n : ℕ) : f (localExampleW k n) =
        if h : n < N then
          Polynomial.C (q (MvPolynomial.X (some 0))) * Polynomial.X ^ (N - n)
        else Polynomial.C (q (MvPolynomial.X (some (n - N)))) := by
      dsimp [f, localExampleW, wmap]
      rw [MvPolynomial.eval₂_X]
    have hfyw (n : ℕ) (hn : n < N) :
        f (localExampleY k * localExampleW k n) = 0 := by
      rw [map_mul, hfy, hfw n, dif_pos hn]
      rw [← mul_assoc, ← Polynomial.C_mul, hqYW]
      simp
    have hfwrel (n : ℕ) (hn : n < N) :
        f (localExampleW k n - localExampleX k * localExampleW k (n + 1)) = 0 := by
      rw [map_sub, map_mul, hfw n, hfx, hfw (n + 1)]
      by_cases hn1 : n + 1 < N
      · rw [dif_pos hn, dif_pos hn1]
        have hp' : N - n = (N - (n + 1)) + 1 := by omega
        rw [hp', pow_succ]
        ring
      · rw [dif_pos hn, dif_neg hn1]
        have heq : n + 1 = N := by omega
        rw [← heq]
        simp
    have hf_sum : f (c.sum (fun i a => a * v i)) = 0 := by
      change f (Finset.sum c.support (fun i => c i * v i)) = 0
      rw [map_sum]
      apply Finset.sum_eq_zero
      intro i hi
      rw [map_mul]
      rcases i with n | n
      · rw [hfyw n (hcN (Sum.inl n) hi)]
        exact mul_zero _
      · have hn' : n + 1 < N := by simpa [phi] using hcN (Sum.inr n) hi
        have hn0 : n < N := by omega
        rw [hfwrel n hn0]
        exact mul_zero _
    have hprod : Polynomial.X * f p = 0 := by
      calc
        Polynomial.X * f p = f (localExampleX k * p) := by rw [map_mul, hfx]
        _ = f (c.sum (fun i a => a * v i)) := by rw [hc]
        _ = 0 := hf_sum
    have hfp : f p = 0 := by
      apply Polynomial.isRegular_X.left
      simpa using hprod
    let I : Ideal (MvPolynomial localExampleVariable k) := localExampleIdeal k
    let R := localExampleRing k
    let mkI : MvPolynomial localExampleVariable k →+* R := Ideal.Quotient.mk I
    let bmap : Option ℕ → R := fun i =>
      match i with
      | none => localExampleYbar k
      | some m => localExampleWbar k (N + m)
    let qP : B →+* R :=
      MvPolynomial.eval₂Hom
        (mkI.comp (MvPolynomial.C : k →+* MvPolynomial localExampleVariable k)) bmap
    have hqPnone : qP (MvPolynomial.X none) = localExampleYbar k := by
      dsimp [qP, bmap]
      rw [MvPolynomial.eval₂Hom_X']
    have hqPsome (m : ℕ) :
        qP (MvPolynomial.X (some m)) = localExampleWbar k (N + m) := by
      dsimp [qP, bmap]
      rw [MvPolynomial.eval₂Hom_X']
    have hYWN : localExampleYbar k * localExampleWbar k N = 0 := by
      change Ideal.Quotient.mk I (localExampleY k * localExampleW k N) = 0
      apply Ideal.Quotient.eq_zero_iff_mem.mpr
      change localExampleY k * localExampleW k N ∈ localExampleIdeal k
      exact Ideal.subset_span (by
        rw [localExampleRelations]
        exact Or.inl ⟨N, rfl⟩)
    have hqPgen : qP (MvPolynomial.X none * MvPolynomial.X (some 0)) = 0 := by
      rw [map_mul, hqPnone, hqPsome]
      simpa using hYWN
    have hle : J ≤ RingHom.ker qP := by
      apply Ideal.span_le.mpr
      intro b hb
      rcases Set.mem_singleton_iff.mp hb with rfl
      exact hqPgen
    have hqPJ : ∀ a : B, a ∈ J → qP a = 0 := fun a ha => hle ha
    let qB : Bq →+* R := Ideal.Quotient.lift J qP hqPJ
    let g : Polynomial Bq →+* R :=
      Polynomial.eval₂RingHom qB (localExampleXbar k)
    have hgC (b : Bq) : g (Polynomial.C b) = qB b := by
      dsimp [g]
      simp
    have hgX : g Polynomial.X = localExampleXbar k := by
      dsimp [g]
      simp
    have hqB (a : B) : qB (q a) = qP a := by
      rfl
    have hqBnone : qB (q (MvPolynomial.X none)) = localExampleYbar k := by
      rw [hqB, hqPnone]
    have hqBsome (m : ℕ) : qB (q (MvPolynomial.X (some m))) =
        localExampleWbar k (N + m) := by
      rw [hqB, hqPsome]
    have hfC (c : k) : f (MvPolynomial.C c) = Polynomial.C (q (MvPolynomial.C c)) := by
      dsimp [f]
      rw [MvPolynomial.eval₂_C]
      dsimp [q0]
    have hrel (n : ℕ) : localExampleWbar k n =
        localExampleXbar k * localExampleWbar k (n + 1) := by
      apply sub_eq_zero.mp
      change Ideal.Quotient.mk I
        (localExampleW k n - localExampleX k * localExampleW k (n + 1)) = 0
      apply Ideal.Quotient.eq_zero_iff_mem.mpr
      change localExampleW k n - localExampleX k * localExampleW k (n + 1) ∈
        localExampleIdeal k
      exact Ideal.subset_span (by
        rw [localExampleRelations]
        exact Or.inr ⟨n, rfl⟩)
    have hshift (n m : ℕ) : localExampleWbar k n =
        localExampleXbar k ^ m * localExampleWbar k (n + m) := by
      induction m generalizing n with
      | zero => simp
      | succ m ih =>
        rw [hrel n, ih (n + 1), pow_succ]
        have harith : n + 1 + m = n + (m + 1) := by omega
        rw [harith]
        ring
    have hgf : g.comp f = mkI := by
      apply MvPolynomial.ringHom_ext'
      · ext c
        simp only [RingHom.comp_apply]
        change g (f (MvPolynomial.C c)) = mkI (MvPolynomial.C c)
        rw [hfC, hgC, hqB]
        dsimp [qP]
        rw [MvPolynomial.eval₂Hom_C]
        rfl
      · intro i
        rcases i with _ | _ | n
        · calc
            g (f (localExampleX k)) = g Polynomial.X := by rw [hfx]
            _ = localExampleXbar k := hgX
            _ = mkI (localExampleX k) := rfl
        · calc
            g (f (localExampleY k)) =
                g (Polynomial.C (q (MvPolynomial.X none))) := by rw [hfy]
            _ = qB (q (MvPolynomial.X none)) := hgC _
            _ = localExampleYbar k := hqBnone
            _ = mkI (localExampleY k) := rfl
        · by_cases hn : n < N
          · have hnle : n ≤ N := Nat.le_of_lt hn
            have hadd : n + (N - n) = N := Nat.add_sub_of_le hnle
            calc
              g (f (localExampleW k n)) =
                  g (Polynomial.C (q (MvPolynomial.X (some 0))) *
                    Polynomial.X ^ (N - n)) := by rw [hfw n, dif_pos hn]
              _ = localExampleWbar k N * localExampleXbar k ^ (N - n) := by
                simp only [map_mul, hgC, map_pow, hgX, hqBsome]
                simp only [Nat.add_zero]
              _ = localExampleXbar k ^ (N - n) * localExampleWbar k N := by ring
              _ = localExampleWbar k n := by
                have hW : localExampleWbar k N =
                    localExampleWbar k (n + (N - n)) := by rw [hadd]
                calc
                  localExampleXbar k ^ (N - n) * localExampleWbar k N =
                      localExampleXbar k ^ (N - n) *
                        localExampleWbar k (n + (N - n)) := by rw [hW]
                  _ = localExampleWbar k n := by
                    exact (hshift n (N - n)).symm
          · have hNn : N ≤ n := Nat.le_of_not_gt hn
            have hadd : N + (n - N) = n := Nat.add_sub_of_le hNn
            calc
              g (f (localExampleW k n)) =
                  g (Polynomial.C (q (MvPolynomial.X (some (n - N))))) := by
                    rw [hfw n, dif_neg hn]
              _ = localExampleWbar k (N + (n - N)) := by
                rw [hgC, hqBsome]
              _ = localExampleWbar k n := by rw [hadd]
    have hmk : mkI p = 0 := by
      rw [← hgf]
      change g (f p) = 0
      rw [hfp, map_zero]
    exact Ideal.Quotient.eq_zero_iff_mem.mp hmk
  let P := MvPolynomial localExampleVariable k
  let I : Ideal P := localExampleIdeal k
  let R := localExampleRing k
  let mkI : P →+* R := Ideal.Quotient.mk I
  let K : Ideal R := Ideal.span {localExampleXbar k}
  let qx : R →+* (R ⧸ K) := Ideal.Quotient.mk K
  let f2 : P →+* Polynomial k :=
    MvPolynomial.eval₂Hom (Polynomial.C : k →+* Polynomial k) (fun i =>
      match i with
      | localExampleVariable.x => 0
      | localExampleVariable.y => Polynomial.X
      | localExampleVariable.w _ => 0)
  have h2x : f2 (localExampleX k) = 0 := by
    dsimp [f2, localExampleX]
    rw [MvPolynomial.eval₂Hom_X']
  have h2y : f2 (localExampleY k) = Polynomial.X := by
    dsimp [f2, localExampleY]
    rw [MvPolynomial.eval₂Hom_X']
  have h2w (n : ℕ) : f2 (localExampleW k n) = 0 := by
    dsimp [f2, localExampleW]
    rw [MvPolynomial.eval₂Hom_X']
  have h2C (c : k) : f2 (MvPolynomial.C c) = Polynomial.C c := by
    dsimp [f2]
    rw [MvPolynomial.eval₂Hom_C]
  have hf2I : I ≤ RingHom.ker f2 := by
    rw [show I = localExampleIdeal k by rfl, localExampleIdeal, localExampleRelations]
    apply Ideal.span_le.mpr
    intro z hz
    rcases hz with ⟨n, rfl⟩ | ⟨n, rfl⟩
    · change f2 (localExampleY k * localExampleW k n) = 0
      rw [map_mul, h2y, h2w]
      simp
    · change f2 (localExampleW k n - localExampleX k * localExampleW k (n + 1)) = 0
      rw [map_sub, map_mul, h2w, h2x]
      simp
  have hf2I' : ∀ a : P, a ∈ I → f2 a = 0 := fun a ha => hf2I ha
  let fI : R →+* Polynomial k := Ideal.Quotient.lift I f2 hf2I'
  have hfIx : fI (localExampleXbar k) = 0 := by
    change fI (Ideal.Quotient.mk I (localExampleX k)) = 0
    dsimp [fI]
    exact h2x
  have hfIy : fI (localExampleYbar k) = Polynomial.X := by
    change fI (Ideal.Quotient.mk I (localExampleY k)) = Polynomial.X
    dsimp [fI]
    exact h2y
  have hrelR (n : ℕ) : localExampleWbar k n =
      localExampleXbar k * localExampleWbar k (n + 1) := by
    apply sub_eq_zero.mp
    change Ideal.Quotient.mk I
      (localExampleW k n - localExampleX k * localExampleW k (n + 1)) = 0
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    change localExampleW k n - localExampleX k * localExampleW k (n + 1) ∈
      localExampleIdeal k
    exact Ideal.subset_span (by
      rw [localExampleRelations]
      exact Or.inr ⟨n, rfl⟩)
  have hqxX : qx (localExampleXbar k) = 0 := by
    change Ideal.Quotient.mk K (localExampleXbar k) = 0
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
  have hqxW (n : ℕ) : qx (localExampleWbar k n) = 0 := by
    rw [hrelR n, map_mul, hqxX]
    exact zero_mul (qx (localExampleWbar k (n + 1)))
  let cR : k →+* R := mkI.comp (MvPolynomial.C : k →+* P)
  let cQ : k →+* (R ⧸ K) := qx.comp cR
  let g2 : Polynomial k →+* (R ⧸ K) :=
    Polynomial.eval₂RingHom cQ (qx (localExampleYbar k))
  have hcompP : (g2.comp fI).comp mkI = qx.comp mkI := by
    apply MvPolynomial.ringHom_ext'
    · ext c
      simp only [RingHom.comp_apply]
      change g2 (fI (mkI (MvPolynomial.C c))) = qx (mkI (MvPolynomial.C c))
      change g2 (f2 (MvPolynomial.C c)) = qx (mkI (MvPolynomial.C c))
      rw [h2C]
      simp [g2, cQ, cR]
    · intro i
      rcases i with _ | _ | n
      · change g2 (fI (mkI (localExampleX k))) = qx (mkI (localExampleX k))
        change g2 (f2 (localExampleX k)) = qx (localExampleXbar k)
        rw [h2x, map_zero, hqxX]
      · change g2 (fI (mkI (localExampleY k))) = qx (mkI (localExampleY k))
        change g2 (f2 (localExampleY k)) = qx (localExampleYbar k)
        rw [h2y]
        simp [g2]
      · change g2 (fI (mkI (localExampleW k n))) = qx (mkI (localExampleW k n))
        change g2 (f2 (localExampleW k n)) = qx (localExampleWbar k n)
        rw [h2w, map_zero, hqxW]
  have hcomp : g2.comp fI = qx := by
    apply RingHom.ext
    intro a
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective a
    exact RingHom.congr_fun hcompP b
  have hregyQ : IsSMulRegular (R ⧸ K) (localExampleYbar k) := by
    apply (isSMulRegular_quotient_iff_mem_of_smul_mem K
      (localExampleYbar k)).mpr
    intro a ha
    have hK : K ≤ RingHom.ker fI := by
      apply Ideal.span_le.mpr
      intro z hz
      rcases Set.mem_singleton_iff.mp hz with rfl
      exact hfIx
    have hzero : fI (localExampleYbar k * a) = 0 := hK ha
    have hprod : Polynomial.X * fI a = 0 := by
      calc
        Polynomial.X * fI a = fI (localExampleYbar k * a) := by
          rw [map_mul, hfIy]
        _ = 0 := hzero
    have hfa : fI a = 0 := by
      apply Polynomial.isRegular_X.left
      simpa using hprod
    have hqa : qx a = 0 := by
      rw [← hcomp]
      change g2 (fI a) = 0
      rw [hfa, map_zero]
    exact Ideal.Quotient.eq_zero_iff_mem.mp hqa
  have hq : QuotSMulTop (localExampleXbar k) R ≃ₗ[R]
      R ⧸ K := by
    apply Submodule.quotEquivOfEq
    dsimp [K]
    rw [← Submodule.ideal_span_singleton_smul]
    change (Ideal.span {localExampleXbar k} : Ideal R) * (⊤ : Ideal R) =
      Ideal.span {localExampleXbar k}
    exact Ideal.mul_top _
  have hregy : IsSMulRegular (QuotSMulTop (localExampleXbar k) R)
      (localExampleYbar k) := by
    exact (hq.isSMulRegular_congr _).mpr hregyQ
  apply (RingTheory.Sequence.isRegular_cons_iff R (localExampleXbar k)
    [localExampleYbar k]).mpr
  refine ⟨hregx, ?_⟩
  apply (RingTheory.Sequence.isRegular_cons_iff
    (QuotSMulTop (localExampleXbar k) R) (localExampleYbar k) []).mpr
  refine ⟨hregy, ?_⟩
  let fK : R →+* k := (Polynomial.evalRingHom (0 : k)).comp fI
  have hfKx : fK (localExampleXbar k) = 0 := by
    dsimp [fK]
    rw [hfIx]
    simp
  have hfKy : fK (localExampleYbar k) = 0 := by
    dsimp [fK]
    rw [hfIy]
    simp
  let ell0 : R →ₛₗ[fK] k :=
    { toFun := fK
      map_add' := by intro a b; exact fK.map_add a b
      map_smul' := by
        intro a b
        change fK (a • b) = fK a • fK b
        simpa only [smul_eq_mul] using fK.map_mul a b }
  let Sx : Submodule R R :=
    (Ideal.span {localExampleXbar k} : Ideal R) • (⊤ : Submodule R R)
  have hSx : Sx ≤ LinearMap.ker ell0 := by
    apply Submodule.smul_le.2
    intro a ha b hb
    rw [LinearMap.mem_ker]
    change ell0 (a • b) = 0
    rw [map_smulₛₗ]
    have hspanx : Ideal.span {localExampleXbar k} ≤ RingHom.ker fK := by
      apply Ideal.span_le.mpr
      intro c hc
      rcases Set.mem_singleton_iff.mp hc with rfl
      exact hfKx
    have ha0 : fK a = 0 := by
      exact hspanx ha
    rw [ha0, zero_smul]
  let eSx : QuotSMulTop (localExampleXbar k) R ≃ₗ[R] R ⧸ Sx := by
    apply Submodule.quotEquivOfEq
    dsimp [Sx]
    exact (Submodule.ideal_span_singleton_smul
      (localExampleXbar k) (⊤ : Submodule R R)).symm
  let ell1 : QuotSMulTop (localExampleXbar k) R →ₛₗ[fK] k :=
    (Sx.liftQ ell0 hSx).comp eSx.toLinearMap
  have hell1y : ell1 (Submodule.Quotient.mk (localExampleYbar k)) = 0 := by
    change (Sx.liftQ ell0 hSx)
      (eSx (Submodule.Quotient.mk (localExampleYbar k))) = 0
    change ell0 (localExampleYbar k) = 0
    dsimp [ell0]
    exact hfKy
  let Sy : Submodule R (QuotSMulTop (localExampleXbar k) R) :=
    (Ideal.span {localExampleYbar k} : Ideal R) •
      (⊤ : Submodule R (QuotSMulTop (localExampleXbar k) R))
  have hSy : Sy ≤ LinearMap.ker ell1 := by
    apply Submodule.smul_le.2
    intro a ha b hb
    rw [LinearMap.mem_ker]
    change ell1 (a • b) = 0
    rw [map_smulₛₗ]
    have hspany : Ideal.span {localExampleYbar k} ≤ RingHom.ker fK := by
      apply Ideal.span_le.mpr
      intro c hc
      rcases Set.mem_singleton_iff.mp hc with rfl
      exact hfKy
    have ha0 : fK a = 0 := by
      exact hspany ha
    rw [ha0, zero_smul]
  let eSy : QuotSMulTop (localExampleYbar k)
      (QuotSMulTop (localExampleXbar k) R) ≃ₗ[R]
      (QuotSMulTop (localExampleXbar k) R) ⧸ Sy := by
    apply Submodule.quotEquivOfEq
    dsimp [Sy]
    exact (Submodule.ideal_span_singleton_smul
      (localExampleYbar k)
      (⊤ : Submodule R (QuotSMulTop (localExampleXbar k) R))).symm
  let ell2 : QuotSMulTop (localExampleYbar k)
      (QuotSMulTop (localExampleXbar k) R) →ₛₗ[fK] k :=
    (Sy.liftQ ell1 hSy).comp eSy.toLinearMap
  have hell2_one : ell2 (Submodule.Quotient.mk (1 : QuotSMulTop (localExampleXbar k) R)) = 1 := by
    change (Sy.liftQ ell1 hSy)
      (eSy (Submodule.Quotient.mk (1 : QuotSMulTop (localExampleXbar k) R))) = 1
    change ell1 (1 : QuotSMulTop (localExampleXbar k) R) = 1
    change ell0 (1 : R) = 1
    dsimp [ell0]
    exact fK.map_one
  have hnontrivial : Nontrivial (QuotSMulTop (localExampleYbar k)
      (QuotSMulTop (localExampleXbar k) R)) := by
    refine ⟨⟨0, Submodule.Quotient.mk (1 : QuotSMulTop (localExampleXbar k) R), ?_⟩⟩
    intro h
    have hh := congrArg ell2 h
    rw [map_zero, hell2_one] at hh
    exact zero_ne_one hh
  exact @RingTheory.Sequence.IsRegular.nil R
    (QuotSMulTop (localExampleYbar k)
      (QuotSMulTop (localExampleXbar k) R)) _ _ _ hnontrivial

theorem local_example_y_is_zero_divisor (k : Type u) [Field k] :
    ¬ IsSMulRegular (localExampleRing k) (localExampleYbar k) := by
  let ev : MvPolynomial localExampleVariable k →+* k :=
    MvPolynomial.eval₂Hom (RingHom.id k) (fun i =>
      match i with
      | localExampleVariable.x => 1
      | localExampleVariable.y => 0
      | localExampleVariable.w _ => 1)
  have hev (i : localExampleVariable) :
      ev (MvPolynomial.X i) =
        match i with
        | localExampleVariable.x => 1
        | localExampleVariable.y => 0
        | localExampleVariable.w _ => 1 := by
    change MvPolynomial.eval₂Hom (RingHom.id k) (fun i =>
      match i with
      | localExampleVariable.x => 1
      | localExampleVariable.y => 0
      | localExampleVariable.w _ => 1) (MvPolynomial.X i) = _
    rw [MvPolynomial.eval₂Hom_X']
  have hrel : localExampleIdeal k ≤ RingHom.ker ev := by
    rw [localExampleIdeal, localExampleRelations]
    refine Ideal.span_le.mpr ?_
    rintro p (hp | hp)
    · rcases hp with ⟨n, rfl⟩
      change ev (localExampleY k * localExampleW k n) = 0
      rw [map_mul]
      change ev (MvPolynomial.X .y) * ev (MvPolynomial.X (.w n)) = 0
      rw [hev, hev]
      simp
    · rcases hp with ⟨n, rfl⟩
      change ev (localExampleW k n - localExampleX k * localExampleW k (n + 1)) = 0
      rw [map_sub, map_mul]
      change ev (MvPolynomial.X (.w n)) - ev (MvPolynomial.X .x) *
        ev (MvPolynomial.X (.w (n + 1))) = 0
      rw [hev, hev, hev]
      simp
  have hrel' : ∀ a, a ∈ localExampleIdeal k → ev a = 0 := by
    intro a ha
    exact hrel ha
  let f : localExampleRing k →+* k :=
    Ideal.Quotient.lift (localExampleIdeal k) ev hrel'
  have hfW : f (localExampleWbar k 0) = 1 := by
    change ev (localExampleW k 0) = 1
    change ev (MvPolynomial.X (.w 0)) = 1
    rw [hev]
  intro h
  have hzero : localExampleWbar k 0 = 0 := by
    apply h
    simp only [smul_eq_mul, mul_zero]
    change Ideal.Quotient.mk (localExampleIdeal k)
      (localExampleY k * localExampleW k 0) = 0
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    exact Ideal.subset_span (by
      rw [localExampleRelations]
      exact Or.inl ⟨0, rfl⟩)
  have hh := congrArg f hzero
  rw [map_zero, hfW] at hh
  exact one_ne_zero hh

theorem local_example_after_localization (k : Type u) [Field k] :
    RingTheory.Sequence.IsRegular (localExampleLocalizedRing k)
        [localExampleLocalizedX k, localExampleLocalizedY k] ∧
      ¬ IsSMulRegular (localExampleLocalizedRing k) (localExampleLocalizedY k) := by
  letI : (localExampleMaximalIdeal k).IsMaximal :=
    local_example_maximal_ideal_is_maximal k
  have hreg : RingTheory.Sequence.IsRegular (localExampleLocalizedRing k)
      [localExampleLocalizedX k, localExampleLocalizedY k] := by
    have hmem : ∀ r ∈ ([localExampleXbar k, localExampleYbar k] : List (localExampleRing k)),
        r ∈ localExampleMaximalIdeal k := by
      intro r hr
      have hr' : r = localExampleXbar k ∨ r = localExampleYbar k := by
        simpa using hr
      rcases hr' with rfl | rfl
      · exact Ideal.subset_span (by
          simp [localExampleMaximalIdealGenerators])
      · exact Ideal.subset_span (by
          simp [localExampleMaximalIdealGenerators])
    simpa [localExampleLocalizedX, localExampleLocalizedY] using
      (local_example_regular_sequence k).1.isRegular_of_isLocalization_of_mem
        (localExampleLocalizedRing k) (localExampleMaximalIdeal k) hmem
  constructor
  · exact hreg
  · intro hy
    have hrelR (n : ℕ) : localExampleWbar k n =
        localExampleXbar k * localExampleWbar k (n + 1) := by
      apply sub_eq_zero.mp
      change Ideal.Quotient.mk (localExampleIdeal k)
        (localExampleW k n - localExampleX k * localExampleW k (n + 1)) = 0
      apply Ideal.Quotient.eq_zero_iff_mem.mpr
      exact Ideal.subset_span (by
        rw [localExampleRelations]
        exact Or.inr ⟨n, rfl⟩)
    have hregx : IsSMulRegular (localExampleRing k) (localExampleXbar k) := by
      exact (RingTheory.Sequence.isRegular_cons_iff
        (localExampleRing k) (localExampleXbar k)
        [localExampleYbar k]).mp (local_example_regular_sequence k) |>.1
    have hann (s : localExampleRing k) (hs : s * localExampleWbar k 0 = 0) :
        ∀ n : ℕ, s * localExampleWbar k n = 0 := by
      intro n
      induction n with
      | zero => exact hs
      | succ n ih =>
          apply hregx
          change localExampleXbar k * (s * localExampleWbar k (n + 1)) =
            localExampleXbar k * 0
          calc
            localExampleXbar k * (s * localExampleWbar k (n + 1)) =
                s * (localExampleXbar k * localExampleWbar k (n + 1)) := by ring
            _ = s * localExampleWbar k n := by rw [← hrelR n]
            _ = 0 := ih
            _ = localExampleXbar k * 0 := by simp
    have hW0 : algebraMap (localExampleRing k) (localExampleLocalizedRing k)
        (localExampleWbar k 0) ≠ 0 := by
      intro hz
      obtain ⟨s, hs⟩ :=
        (IsLocalization.map_eq_zero_iff (localExampleMaximalIdeal k).primeCompl
          (localExampleLocalizedRing k) (localExampleWbar k 0)).mp hz
      have hsann : ∀ n : ℕ, (s : localExampleRing k) * localExampleWbar k n = 0 :=
        hann (s : localExampleRing k) hs
      have hsmem : (s : localExampleRing k) ∈ localExampleMaximalIdeal k := by
        let P := MvPolynomial localExampleVariable k
        let v : Sum ℕ ℕ → P
            | Sum.inl n => localExampleY k * localExampleW k n
            | Sum.inr n => localExampleW k n - localExampleX k * localExampleW k (n + 1)
        have hv : Ideal.span (Set.range v) = localExampleIdeal k := by
          rw [localExampleIdeal]
          congr 1
          ext z
          constructor
          · rintro ⟨i, rfl⟩
            rcases i with i | i
            · exact Or.inl ⟨i, rfl⟩
            · exact Or.inr ⟨i, rfl⟩
          · intro hz
            rcases hz with ⟨i, rfl⟩ | ⟨i, rfl⟩
            · exact ⟨Sum.inl i, rfl⟩
            · exact ⟨Sum.inr i, rfl⟩
        obtain ⟨p, hp⟩ := Ideal.Quotient.mk_surjective (s : localExampleRing k)
        have hs0 :
            Ideal.Quotient.mk (localExampleIdeal k) p * localExampleWbar k 0 = 0 := by
          rw [hp]
          exact hsann 0
        have hp0 : p * localExampleW k 0 ∈ localExampleIdeal k := by
          apply Ideal.Quotient.eq_zero_iff_mem.mp
          change Ideal.Quotient.mk (localExampleIdeal k)
            (p * localExampleW k 0) = 0
          simpa only [map_mul, localExampleWbar] using hs0
        rw [← hv] at hp0
        obtain ⟨c, hc⟩ :=
          Finsupp.mem_ideal_span_range_iff_exists_finsupp.mp hp0
        let phi : Sum ℕ ℕ → ℕ := fun i =>
          match i with | Sum.inl n => n | Sum.inr n => n + 1
        let T : Finset ℕ := c.support.image phi
        obtain ⟨N, hN⟩ := T.exists_nat_subset_range
        have hcN (i : Sum ℕ ℕ) (hi : i ∈ c.support) :
            phi i < N := by
          simpa [T] using hN (Finset.mem_image.mpr ⟨i, hi, rfl⟩)
        let Q := MvPolynomial (Option ℕ) k
        let wmap : localExampleVariable → Q := fun i =>
          match i with
          | localExampleVariable.x => MvPolynomial.X none
          | localExampleVariable.y => 0
          | localExampleVariable.w n =>
              if h : n ≤ N then
                MvPolynomial.X (some 0) * MvPolynomial.X none ^ (N - n)
              else MvPolynomial.X (some 0)
        let f : P →+* Q :=
          MvPolynomial.eval₂Hom (MvPolynomial.C : k →+* Q) wmap
        have hfx : f (localExampleX k) = MvPolynomial.X none := by
          dsimp [f, localExampleX, wmap]
          rw [MvPolynomial.eval₂Hom_X']
        have hfy : f (localExampleY k) = 0 := by
          dsimp [f, localExampleY, wmap]
          rw [MvPolynomial.eval₂Hom_X']
        have hfw (n : ℕ) : f (localExampleW k n) =
            if h : n ≤ N then
              MvPolynomial.X (some 0) * MvPolynomial.X none ^ (N - n)
            else MvPolynomial.X (some 0) := by
          dsimp [f, localExampleW, wmap]
          rw [MvPolynomial.eval₂Hom_X']
        have hfyw (n : ℕ) (hn : n < N) :
            f (localExampleY k * localExampleW k n) = 0 := by
          rw [map_mul, hfy]
          simp
        have hfwrel (n : ℕ) (hn : n < N) :
            f (localExampleW k n - localExampleX k * localExampleW k (n + 1)) = 0 := by
          rw [map_sub, map_mul, hfw n, hfx, hfw (n + 1)]
          have hnle : n ≤ N := Nat.le_of_lt hn
          by_cases hn1 : n + 1 ≤ N
          · rw [dif_pos hnle, dif_pos hn1]
            have hp' : N - n = (N - (n + 1)) + 1 := by omega
            rw [hp', pow_succ]
            ring
          · have heq : n + 1 = N := by omega
            have hpow : N - n = 1 := by omega
            rw [dif_pos hnle, dif_neg hn1, hpow]
            ring
        have hf_sum : f (c.sum (fun i a => a * v i)) = 0 := by
          change f (Finset.sum c.support (fun i => c i * v i)) = 0
          rw [map_sum]
          apply Finset.sum_eq_zero
          intro i hi
          rw [map_mul]
          rcases i with n | n
          · rw [hfyw n (hcN (Sum.inl n) hi)]
            exact mul_zero _
          · have hn' : n + 1 < N := by simpa [phi] using hcN (Sum.inr n) hi
            have hn0 : n < N := by omega
            rw [hfwrel n hn0]
            exact mul_zero _
        have hfprod : f (p * localExampleW k 0) = 0 := by
          rw [← hc]
          exact hf_sum
        have hfw0 : f (localExampleW k 0) =
            MvPolynomial.X (some 0) * MvPolynomial.X none ^ N := by
          rw [hfw 0, dif_pos (Nat.zero_le N)]
          simp
        have hfp : f p = 0 := by
          have hprod : MvPolynomial.X none ^ N *
              (MvPolynomial.X (some 0) * f p) = 0 := by
            calc
              MvPolynomial.X none ^ N *
                    (MvPolynomial.X (some 0) * f p) =
                  f (p * localExampleW k 0) := by
                    rw [map_mul, hfw0]
                    ring
              _ = 0 := hfprod
          have hprod' : MvPolynomial.X (some 0) * f p = 0 := by
            apply (MvPolynomial.isRegular_X_pow (n := none) N).left
            simpa only [mul_zero] using hprod
          apply (MvPolynomial.isRegular_X (n := some 0)).left
          simpa only [mul_zero] using hprod'
        let g : Q →+* k :=
          MvPolynomial.eval₂Hom (RingHom.id k) (fun _ => 0)
        have hcomp : g.comp f =
            MvPolynomial.eval₂Hom (RingHom.id k)
              (fun _ : localExampleVariable => 0) := by
          apply MvPolynomial.ringHom_ext'
          · ext c'
            simp [f, g, MvPolynomial.constantCoeff_eq,
              MvPolynomial.constantCoeff_C (Option ℕ)]
          · intro i
            rcases i with _ | _ | n
            · change g (f (localExampleX k)) =
                MvPolynomial.eval₂Hom (RingHom.id k)
                  (fun _ : localExampleVariable => 0) (MvPolynomial.X .x)
              rw [hfx]
              simp [g, MvPolynomial.constantCoeff_eq,
                MvPolynomial.constantCoeff_X k]
            · change g (f (localExampleY k)) =
                MvPolynomial.eval₂Hom (RingHom.id k)
                  (fun _ : localExampleVariable => 0) (MvPolynomial.X .y)
              rw [hfy]
              simp
            · change g (f (localExampleW k n)) =
                MvPolynomial.eval₂Hom (RingHom.id k)
                  (fun _ : localExampleVariable => 0) (MvPolynomial.X (.w n))
              rw [hfw n]
              by_cases hn : n ≤ N
              · rw [dif_pos hn]
                simp [g, MvPolynomial.constantCoeff_eq,
                  MvPolynomial.constantCoeff_C (Option ℕ),
                  MvPolynomial.constantCoeff_X k]
              · rw [dif_neg hn]
                simp [g, MvPolynomial.constantCoeff_eq,
                  MvPolynomial.constantCoeff_C (Option ℕ),
                  MvPolynomial.constantCoeff_X k]
        have heval : MvPolynomial.eval₂Hom (RingHom.id k)
              (fun _ : localExampleVariable => 0) p = 0 := by
          rw [← hcomp]
          change g (f p) = 0
          rw [hfp, map_zero]
        have hconst : MvPolynomial.constantCoeff p = 0 := by
          have hc' := MvPolynomial.eval₂Hom_eq_constantCoeff_of_vars
            (RingHom.id k) (p := p) (fun i hi => rfl)
          rw [heval] at hc'
          simpa using hc'.symm
        have hpI : p ∈ MvPolynomial.idealOfVars localExampleVariable k := by
          rw [MvPolynomial.idealOfVars, ← Set.image_univ,
            MvPolynomial.mem_ideal_span_X_image]
          intro m hm
          by_cases hm0 : m = 0
          · subst m
            exfalso
            apply (MvPolynomial.mem_support_iff.mp hm)
            simpa [MvPolynomial.constantCoeff_eq] using hconst
          · have hex : ∃ i, m i ≠ 0 := by
              by_contra h'
              push Not at h'
              apply hm0
              exact Finsupp.ext fun i => h' i
            rcases hex with ⟨i, hi⟩
            exact ⟨i, Set.mem_univ _, hi⟩
        let mkI : P →+* localExampleRing k :=
          Ideal.Quotient.mk (localExampleIdeal k)
        have hmap :
            Ideal.map mkI (MvPolynomial.idealOfVars localExampleVariable k) ≤
              localExampleMaximalIdeal k := by
          rw [Ideal.map_le_iff_le_comap, MvPolynomial.idealOfVars]
          refine Ideal.span_le.mpr ?_
          rintro _ ⟨i, rfl⟩
          change Ideal.Quotient.mk (localExampleIdeal k) (MvPolynomial.X i) ∈
            localExampleMaximalIdeal k
          apply Ideal.subset_span
          cases i with
          | x =>
              simp [localExampleMaximalIdealGenerators, localExampleXbar, localExampleX]
          | y =>
              simp [localExampleMaximalIdealGenerators, localExampleYbar, localExampleY]
          | w n =>
              simp [localExampleMaximalIdealGenerators, localExampleWbar, localExampleW]
        rw [← hp]
        exact hmap (Ideal.mem_map_of_mem _ hpI)
      exact s.2 hsmem
    apply hW0
    apply hy
    simp only [smul_eq_mul]
    dsimp [localExampleLocalizedY]
    have hprod : localExampleYbar k * localExampleWbar k 0 = 0 := by
      change Ideal.Quotient.mk (localExampleIdeal k)
        (localExampleY k * localExampleW k 0) = 0
      apply Ideal.Quotient.eq_zero_iff_mem.mpr
      exact Ideal.subset_span (by
        rw [localExampleRelations]
        exact Or.inl ⟨0, rfl⟩)
    calc
      algebraMap (localExampleRing k) (localExampleLocalizedRing k)
          (localExampleYbar k) *
            algebraMap (localExampleRing k) (localExampleLocalizedRing k)
              (localExampleWbar k 0) =
        algebraMap (localExampleRing k) (localExampleLocalizedRing k)
          (localExampleYbar k * localExampleWbar k 0) := by rw [map_mul]
      _ = 0 := by rw [hprod, map_zero]
      _ = algebraMap (localExampleRing k) (localExampleLocalizedRing k)
          (localExampleYbar k) * 0 := by simp

/-! ## Basic properties -/

theorem regular_sequence_permutation
    {R M : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M]
    {xs ys : List R}
    (hxs : RingTheory.Sequence.IsRegular M xs)
    (hperm : xs.Perm ys) :
    RingTheory.Sequence.IsRegular M ys := by
  exact IsLocalRing.isRegular_of_perm hxs hperm

private theorem faithfullyFlat_reflect_smulRegular
    {R S M N : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [Module S N] [IsScalarTower R S N] [Module.FaithfullyFlat R S]
    (f : M →ₗ[R] N) (hf : IsBaseChange S f) (r : R)
    (hr : IsSMulRegular N (algebraMap R S r)) : IsSMulRegular M r := by
  intro m n hmn
  let L : N →ₗ[S] N :=
    hf.lift (f.comp (LinearMap.lsmul R M r))
  have hL : L = LinearMap.lsmul S N (algebraMap R S r) := by
    apply hf.algHom_ext
    intro z
    dsimp [L]
    rw [hf.lift_eq]
    simpa only [LinearMap.comp_apply, LinearMap.lsmul_apply] using
      (f.map_smul r z).trans (IsScalarTower.algebraMap_smul S r (f z)).symm
  have hLi : Function.Injective L := by
    rw [hL]
    exact hr
  let C : N →ₗ[S] N :=
    hf.equiv.toLinearMap.comp
      ((TensorProduct.AlgebraTensorModule.lTensor S S
        (LinearMap.lsmul R M r)).comp
        (hf.equiv.symm.toLinearMap : N →ₗ[S] S ⊗[R] M))
  have hC : C = L := by
    apply hf.algHom_ext
    intro z
    dsimp [C, L]
    rw [hf.equiv_symm_apply, LinearMap.lTensor_tmul,
      hf.equiv_tmul, hf.lift_eq]
    simp only [one_smul, LinearMap.comp_apply]
  have hlt : Function.Injective ((LinearMap.lsmul R M r).lTensor S) := by
    intro x y hxy
    apply hf.equiv.injective
    apply hLi
    have hxy' :
        (TensorProduct.AlgebraTensorModule.lTensor S S
          (LinearMap.lsmul R M r)) x =
        (TensorProduct.AlgebraTensorModule.lTensor S S
          (LinearMap.lsmul R M r)) y := by
      simpa only [TensorProduct.AlgebraTensorModule.coe_lTensor] using hxy
    rw [← hC]
    dsimp [C]
    simp only [LinearMap.comp_apply, LinearEquiv.symm_apply_apply]
    exact congrArg hf.equiv hxy'
  exact (Module.FaithfullyFlat.lTensor_injective_iff_injective R S
    (LinearMap.lsmul R M r)).mp hlt hmn

private theorem faithfullyFlat_reflect_weaklyRegular
    {R S M N : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [Module S N] [IsScalarTower R S N] [Module.FaithfullyFlat R S]
    (f : M →ₗ[R] N) (hf : IsBaseChange S f) (xs : List R)
    (h : RingTheory.Sequence.IsWeaklyRegular N (xs.map (algebraMap R S))) :
    RingTheory.Sequence.IsWeaklyRegular M xs := by
  induction xs generalizing M N with
  | nil =>
      exact RingTheory.Sequence.IsWeaklyRegular.nil R M
  | cons r rs ih =>
      simp only [List.map_cons, RingTheory.Sequence.isWeaklyRegular_cons_iff] at h ⊢
      refine ⟨faithfullyFlat_reflect_smulRegular f hf r h.1, ?_⟩
      let e := (QuotSMulTop.algebraMapTensorEquivTensorQuotSMulTop r M S).symm ≪≫ₗ
        QuotSMulTop.congr (algebraMap R S r) hf.equiv
      have hg : IsBaseChange S
          (e.toLinearMap.restrictScalars R ∘ₗ
            TensorProduct.mk R S (QuotSMulTop r M) 1) := by
        exact IsBaseChange.of_equiv e (fun _ ↦ by simp)
      exact ih (e.toLinearMap.restrictScalars R ∘ₗ
        TensorProduct.mk R S (QuotSMulTop r M) 1) hg h.2

/- A flat local map is faithfully flat by the canonical local-flatness theorem.  The tensor
   product is written as `S ⊗[R] M`, the orientation for which Mathlib exposes the natural
   `S`-module structure; it is canonically equivalent to the source's `M ⊗[R] S` order. -/
theorem regular_sequence_flat_local
    {R S M : Type*} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S]
    [Algebra R S] [IsLocalHom (algebraMap R S)]
    [AddCommGroup M] [Module R M]
    (hflat : RingHom.Flat (algebraMap R S)) (xs : List R) :
    RingTheory.Sequence.IsRegular M xs ↔
      RingTheory.Sequence.IsRegular (S ⊗[R] M)
        (xs.map (algebraMap R S)) := by
  haveI : Module.Flat R S := (RingHom.flat_algebraMap_iff.mp hflat)
  letI : Module.FaithfullyFlat R S :=
    Module.FaithfullyFlat.of_flat_of_isLocalHom
  constructor
  · intro h
    have hbc : IsBaseChange S (TensorProduct.mk R S M 1) :=
      TensorProduct.isBaseChange R M S
    exact RingTheory.Sequence.IsRegular.of_faithfullyFlat_of_isBaseChange hbc h
  · intro h
    have hw := faithfullyFlat_reflect_weaklyRegular (M := M) (N := S ⊗[R] M)
      (TensorProduct.mk R S M 1)
      (TensorProduct.isBaseChange R M S) xs h.1
    have htop : (Ideal.ofList xs).map (algebraMap R S) •
        (⊤ : Submodule S (S ⊗[R] M)) ≠ ⊤ := by
      rw [Ideal.map_ofList]
      exact h.2.symm
    refine ⟨hw, ?_⟩
    exact ((TensorProduct.isBaseChange R M S).map_smul_top_ne_top_iff_of_faithfullyFlat
      R M (Ideal.ofList xs)).mp htop |>.symm

theorem regular_sequence_in_neighborhood
    {R M : Type*} [CommRing R] [IsNoetherianRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M]
    (p : Ideal R) [p.IsPrime] (xs : List R)
    (hp : RingTheory.Sequence.IsRegular
      (LocalizedModule.AtPrime p M)
      (xs.map (algebraMap R (Localization.AtPrime p)))) :
    ∃ g : R, g ∉ p ∧
      RingTheory.Sequence.IsRegular
        (LocalizedModule (Submonoid.powers g) M)
        (xs.map (algebraMap R (Localization (Submonoid.powers g)))) := by
  sorry

theorem regular_sequence_join
    {A : Type*} [CommRing A] (I : Ideal A)
    {fs gs : List A}
    (hI : I = Ideal.ofList fs)
    (hfs : RingTheory.Sequence.IsRegular A fs)
    (hgs : RingTheory.Sequence.IsRegular (A ⧸ I)
      (gs.map (Ideal.Quotient.mk I))) :
    RingTheory.Sequence.IsRegular A (fs ++ gs) := by
  sorry

theorem regular_sequence_of_short_exact
    {R M₁ M₂ M₃ : Type*} [CommRing R]
    [AddCommGroup M₁] [AddCommGroup M₂] [AddCommGroup M₃]
    [Module R M₁] [Module R M₂] [Module R M₃]
    (f : M₁ →ₗ[R] M₂) (g : M₂ →ₗ[R] M₃)
    (hf : Injective f) (hfg : Exact f g) (hg : Surjective g)
    (xs : List R)
    (h₁ : RingTheory.Sequence.IsRegular M₁ xs)
    (h₃ : RingTheory.Sequence.IsRegular M₃ xs) :
    RingTheory.Sequence.IsRegular M₂ xs := by
  sorry

/- The source's first induction step uses the displayed short exact sequence
  `0 → M/fM → M/f^eM → M/f^(e-1)M → 0`; it is an intermediate proof interface, so the
  public chapter statement is the following powers equivalence and no duplicate auxiliary
  predicate is introduced. -/
theorem regular_sequence_powers_iff
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (n : ℕ) (f : Fin n → R) (e : Fin n → ℕ)
    (he : ∀ i, 0 < e i) :
    RingTheory.Sequence.IsRegular M (List.ofFn f) ↔
      RingTheory.Sequence.IsRegular M
        (List.ofFn (fun i => f i ^ e i)) := by
  sorry

/- The source's polynomial proof uses the direct-sum decomposition indexed by multi-indices
  and the ideals `I_E`; these are proof-level bookkeeping for the final TFAE, not additional
  chapter-facing structures. -/
theorem regular_sequence_polynomial_iff
    {R : Type u} [CommRing R] (n : ℕ) (f : Fin n → R)
    (hnotunit : Ideal.ofList (List.ofFn f) ≠ (⊤ : Ideal R)) :
    List.TFAE
      [ (∀ ys : List R, List.Perm (List.ofFn f) ys →
            RingTheory.Sequence.IsRegular R ys),
        (∀ ys : List R, List.Sublist ys (List.ofFn f) →
            RingTheory.Sequence.IsRegular R ys),
        RingTheory.Sequence.IsRegular (MvPolynomial (Fin n) R)
          (List.ofFn (fun i => MvPolynomial.C (f i) * MvPolynomial.X i)) ] := by
  sorry

end

end Formalization.Books.Algebra.Unit68
