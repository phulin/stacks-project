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
  sorry

theorem local_example_y_is_zero_divisor (k : Type u) [Field k] :
    ¬ IsSMulRegular (localExampleRing k) (localExampleYbar k) := by
  sorry

theorem local_example_after_localization (k : Type u) [Field k] :
    RingTheory.Sequence.IsRegular (localExampleLocalizedRing k)
        [localExampleLocalizedX k, localExampleLocalizedY k] ∧
      ¬ IsSMulRegular (localExampleLocalizedRing k) (localExampleLocalizedY k) := by
  sorry

/-! ## Basic properties -/

theorem regular_sequence_permutation
    {R M : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M]
    {xs ys : List R}
    (hxs : RingTheory.Sequence.IsRegular M xs)
    (hperm : xs.Perm ys) :
    RingTheory.Sequence.IsRegular M ys := by
  sorry

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
  sorry

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
