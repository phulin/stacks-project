import Mathlib.Algebra.Module.LocalizedModule.AtPrime
import Mathlib.Algebra.Module.LocalizedModule.Submodule
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Support
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
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
open scoped Pointwise TensorProduct

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
        exact Ideal.subset_span (by simp)
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
      simp [ev] at h10
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
      simp only [Set.mem_ofPred_eq, List.mem_cons,
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
    simp only [List.mem_cons, List.not_mem_nil, or_false]
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
  let : Nontrivial
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
    simp [hevy] at hy0
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
  let : (localExampleMaximalIdeal k).IsMaximal :=
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
  let : (localExampleMaximalIdeal k).IsMaximal :=
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
            simp [f, g,
              MvPolynomial.constantCoeff_C (Option ℕ)]
          · intro i
            rcases i with _ | _ | n
            · change g (f (localExampleX k)) =
                MvPolynomial.eval₂Hom (RingHom.id k)
                  (fun _ : localExampleVariable => 0) (MvPolynomial.X .x)
              rw [hfx]
              simp [g,
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
                simp [g,
                  MvPolynomial.constantCoeff_X k]
              · rw [dif_neg hn]
                simp [g,
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
    simp only [LinearEquiv.symm_apply_apply]
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
  have : Module.Flat R S := (RingHom.flat_algebraMap_iff.mp hflat)
  let : Module.FaithfullyFlat R S :=
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

private theorem localized_prefix_smul_eq
    {R M S N : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [Module S N] [IsScalarTower R S N]
    (p : Submonoid R) [IsLocalization p S]
    (f : M →ₗ[R] N) [IsLocalizedModule p f]
    (xs : List R) (i : Fin xs.length) :
    (Ideal.ofList (xs.take i) • (⊤ : Submodule R M)).localized' S p f =
      Ideal.ofList ((xs.map (algebraMap R S)).take i) •
        (⊤ : Submodule S N) := by
  rw [Submodule.localized'_smul, Ideal.localized'_eq_map,
    Submodule.localized'_top, Ideal.map_ofList]
  simp only [List.map_take]

private theorem isSMulRegular_localized_of_kernel
    {R Q : Type*} [CommRing R] [AddCommGroup Q] [Module R Q]
    (p : Submonoid R) (r : R)
    (hK : (LinearMap.ker (LinearMap.lsmul R Q r)).localized'
        (Localization p) p (LocalizedModule.mkLinearMap p Q) = ⊥) :
    IsSMulRegular (LocalizedModule p Q)
      (algebraMap R (Localization p) r) := by
  have hmap :
      LocalizedModule.map p (LinearMap.lsmul R Q r) =
        LinearMap.lsmul (Localization p) (LocalizedModule p Q)
          (algebraMap R (Localization p) r) := by
    ext x
    obtain ⟨⟨x, s⟩, rfl⟩ :=
      IsLocalizedModule.mk'_surjective p (LocalizedModule.mkLinearMap p Q) x
    simp only [Function.uncurry_apply_pair]
    rw [← IsLocalizedModule.mk_eq_mk' (S := p)]
    rw [LocalizedModule.map_mk]
    simp only [LinearMap.lsmul_apply]
    rw [IsScalarTower.algebraMap_smul (Localization p) r]
    rw [LocalizedModule.smul'_mk]
  have hk :
      (LinearMap.ker (LinearMap.lsmul R Q r)).localized'
          (Localization p) p (LocalizedModule.mkLinearMap p Q) =
        LinearMap.ker (LocalizedModule.map p (LinearMap.lsmul R Q r)) := by
    exact LinearMap.localized'_ker_eq_ker_localizedMap
      (p := p) (S := Localization p)
      (f := LocalizedModule.mkLinearMap p Q)
      (f' := LocalizedModule.mkLinearMap p Q)
      (g := LinearMap.lsmul R Q r)
  rw [isSMulRegular_iff_ker_lsmul_eq_bot]
  rw [← hmap]
  exact hk.symm.trans hK

private theorem weakly_regular_localized_of_quotient
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (p : Submonoid R) (xs : List R)
    (hreg : ∀ i : Fin xs.length,
      IsSMulRegular
        (LocalizedModule p
          (M ⧸ (Ideal.ofList (xs.take i) • (⊤ : Submodule R M))))
        (algebraMap R (Localization p) xs[i])) :
    RingTheory.Sequence.IsWeaklyRegular (LocalizedModule p M)
      (xs.map (algebraMap R (Localization p))) := by
  rw [RingTheory.Sequence.isWeaklyRegular_iff_Fin]
  intro i
  let j : Fin xs.length := ⟨i, by simpa using i.isLt⟩
  let I : Submodule R M := Ideal.ofList (xs.take j) • (⊤ : Submodule R M)
  let Q := M ⧸ I
  let e :
      (LocalizedModule p M ⧸
          (Ideal.ofList ((xs.map (algebraMap R (Localization p))).take i) •
            (⊤ : Submodule (Localization p) (LocalizedModule p M)))) ≃ₗ[Localization p]
        LocalizedModule p Q := by
    exact Submodule.quotEquivOfEq _ _
        (localized_prefix_smul_eq p (LocalizedModule.mkLinearMap p M) xs j).symm ≪≫ₗ
      localizedQuotientEquiv p I
  have hq : IsSMulRegular (LocalizedModule p Q)
      (algebraMap R (Localization p) xs[j]) := by
    simpa [j, I, Q] using hreg j
  have hsource : IsSMulRegular
      (LocalizedModule p M ⧸
        (Ideal.ofList ((xs.map (algebraMap R (Localization p))).take i) •
          (⊤ : Submodule (Localization p) (LocalizedModule p M))))
      (algebraMap R (Localization p) xs[j]) := by
    intro x y hxy
    apply e.injective
    apply hq
    change (algebraMap R (Localization p) xs[j]) • x =
      (algebraMap R (Localization p) xs[j]) • y at hxy
    calc
      (algebraMap R (Localization p) xs[j]) • e x =
          e ((algebraMap R (Localization p) xs[j]) • x) := (e.map_smul _ _).symm
      _ =
          e ((algebraMap R (Localization p) xs[j]) • y) := congrArg e hxy
      _ = (algebraMap R (Localization p) xs[j]) • e y := e.map_smul _ _
  simpa [j] using hsource

private theorem localized_kernel_eq_bot_of_isSMulRegular
    {R Q : Type*} [CommRing R] [AddCommGroup Q] [Module R Q]
    (p : Submonoid R) (r : R)
    (hreg : IsSMulRegular (LocalizedModule p Q)
      (algebraMap R (Localization p) r)) :
    (LinearMap.ker (LinearMap.lsmul R Q r)).localized'
        (Localization p) p (LocalizedModule.mkLinearMap p Q) = ⊥ := by
  have hmap :
      LocalizedModule.map p (LinearMap.lsmul R Q r) =
        LinearMap.lsmul (Localization p) (LocalizedModule p Q)
          (algebraMap R (Localization p) r) := by
    ext x
    obtain ⟨⟨x, s⟩, rfl⟩ :=
      IsLocalizedModule.mk'_surjective p (LocalizedModule.mkLinearMap p Q) x
    simp only [Function.uncurry_apply_pair]
    rw [← IsLocalizedModule.mk_eq_mk' (S := p)]
    rw [LocalizedModule.map_mk]
    simp only [LinearMap.lsmul_apply]
    rw [IsScalarTower.algebraMap_smul (Localization p) r]
    rw [LocalizedModule.smul'_mk]
  have hk :
      (LinearMap.ker (LinearMap.lsmul R Q r)).localized'
          (Localization p) p (LocalizedModule.mkLinearMap p Q) =
        LinearMap.ker (LocalizedModule.map p (LinearMap.lsmul R Q r)) := by
    exact LinearMap.localized'_ker_eq_ker_localizedMap
      (p := p) (S := Localization p)
      (f := LocalizedModule.mkLinearMap p Q)
      (f' := LocalizedModule.mkLinearMap p Q)
      (g := LinearMap.lsmul R Q r)
  rw [hk, hmap]
  exact (isSMulRegular_iff_ker_lsmul_eq_bot _ _).mp hreg

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
  classical
  let Q := fun i : Fin xs.length ↦
    M ⧸ (Ideal.ofList (xs.take i) • (⊤ : Submodule R M))
  let K : ∀ i, Submodule R (Q i) := fun i ↦
    LinearMap.ker (LinearMap.lsmul R (Q i) xs[i])
  have hregQ : ∀ i : Fin xs.length,
      IsSMulRegular (LocalizedModule p.primeCompl (Q i))
        (algebraMap R (Localization p.primeCompl) xs[i]) := by
    intro i
    let e :
        (LocalizedModule p.primeCompl M ⧸
            (Ideal.ofList ((xs.map (algebraMap R (Localization p.primeCompl))).take i) •
              (⊤ : Submodule (Localization p.primeCompl)
                (LocalizedModule p.primeCompl M)))) ≃ₗ[Localization p.primeCompl]
          LocalizedModule p.primeCompl (Q i) := by
      exact Submodule.quotEquivOfEq _ _
          (localized_prefix_smul_eq p.primeCompl
            (LocalizedModule.mkLinearMap p.primeCompl M) xs i).symm ≪≫ₗ
        localizedQuotientEquiv p.primeCompl
          (Ideal.ofList (xs.take i) • (⊤ : Submodule R M))
    let j : Fin (xs.map (algebraMap R (Localization p.primeCompl))).length :=
      ⟨i, by
        simp only [List.length_map]
        exact i.isLt⟩
    have hsource : IsSMulRegular
        (LocalizedModule p.primeCompl M ⧸
          (Ideal.ofList ((xs.map (algebraMap R (Localization p.primeCompl))).take i) •
            (⊤ : Submodule (Localization p.primeCompl)
              (LocalizedModule p.primeCompl M))))
        (algebraMap R (Localization p.primeCompl) xs[i]) := by
      simpa [j] using hp.1.regular_mod_prev j j.isLt
    intro x y hxy
    apply e.symm.injective
    apply hsource
    change (algebraMap R (Localization p.primeCompl) xs[i]) • e.symm x =
      (algebraMap R (Localization p.primeCompl) xs[i]) • e.symm y
    calc
      (algebraMap R (Localization p.primeCompl) xs[i]) • e.symm x =
          e.symm ((algebraMap R (Localization p.primeCompl) xs[i]) • x) :=
            (e.symm.map_smul _ _).symm
      _ = e.symm ((algebraMap R (Localization p.primeCompl) xs[i]) • y) :=
        congrArg e.symm hxy
      _ = (algebraMap R (Localization p.primeCompl) xs[i]) • e.symm y :=
        e.symm.map_smul _ _
  have hKp : ∀ i : Fin xs.length,
      (K i).localized' (Localization p.primeCompl) p.primeCompl
        (LocalizedModule.mkLinearMap p.primeCompl (Q i)) = ⊥ := by
    intro i
    exact localized_kernel_eq_bot_of_isSMulRegular p.primeCompl xs[i] (hregQ i)
  have hsubp : ∀ i : Fin xs.length,
      Subsingleton (LocalizedModule p.primeCompl (K i)) := by
    intro i
    rw [LocalizedModule.subsingleton_iff (S := p.primeCompl)]
    intro x
    have hxmem :
        LocalizedModule.mkLinearMap p.primeCompl (Q i) (x : Q i) ∈
          (K i).localized' (Localization p.primeCompl) p.primeCompl
            (LocalizedModule.mkLinearMap p.primeCompl (Q i)) := by
      rw [Submodule.localized'_eq_span]
      exact Submodule.subset_span ⟨(x : Q i), x.property, rfl⟩
    rw [hKp i] at hxmem
    have hxzero :
        LocalizedModule.mkLinearMap p.primeCompl (Q i) (x : Q i) = 0 := by
      simpa only [Submodule.mem_bot] using hxmem
    have hxker : (x : Q i) ∈
        LinearMap.ker (LocalizedModule.mkLinearMap p.primeCompl (Q i)) := hxzero
    obtain ⟨r, hr, hrx⟩ :=
      (IsLocalizedModule.mem_ker_iff p.primeCompl
        (g := LocalizedModule.mkLinearMap p.primeCompl (Q i))).mp hxker
    refine ⟨r, hr, ?_⟩
    apply Subtype.ext
    exact hrx
  have haway : ∀ i : Fin xs.length, ∃ f : R, f ∉ p ∧
      Subsingleton (LocalizedModule.Away f (K i)) := by
    intro i
    exact @LocalizedModule.exists_subsingleton_away R (K i) _ _ _ _ p
      inferInstance (hsubp i)
  let gi : ∀ i : Fin xs.length, R := fun i ↦
    Classical.choose (haway i)
  have hgi_notp : ∀ i : Fin xs.length, gi i ∉ p := by
    intro i
    exact (Classical.choose_spec (haway i)).1
  have hgi_sub : ∀ i : Fin xs.length,
      Subsingleton (LocalizedModule.Away (gi i) (K i)) := by
    intro i
    exact (Classical.choose_spec (haway i)).2
  let g : R := ∏ i : Fin xs.length, gi i
  have hdiv : ∀ i : Fin xs.length, gi i ∣ g := by
    intro i
    dsimp [g]
    exact Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
  have hg_notp : g ∉ p := by
    have hmem : g ∈ p.primeCompl := by
      dsimp [g]
      exact p.primeCompl.prod_mem (fun i _ ↦ hgi_notp i)
    simpa [Ideal.primeCompl] using hmem
  have hKg : ∀ i : Fin xs.length,
      (K i).localized' (Localization (Submonoid.powers g)) (Submonoid.powers g)
        (LocalizedModule.mkLinearMap (Submonoid.powers g) (Q i)) = ⊥ := by
    intro i
    rw [Submodule.localized'_eq_span]
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro z ⟨x, hx, rfl⟩
      let xi : K i := ⟨x, hx⟩
      obtain ⟨s, hs, hxs⟩ :=
        (LocalizedModule.subsingleton_iff (S := Submonoid.powers (gi i))).mp
          (hgi_sub i) xi
      obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff _ _).mp hs
      have hxs' : s • (x : Q i) = 0 := by
        exact congrArg (fun z : K i ↦ (z : Q i)) hxs
      have hpow : (gi i) ^ n • (x : Q i) = 0 := by
        rw [hn]
        exact hxs'
      obtain ⟨c, hc⟩ := hdiv i
      have hgpow : g ^ n • (x : Q i) = 0 := by
        calc
          g ^ n • (x : Q i) = (gi i ^ n * c ^ n) • (x : Q i) := by
            rw [hc, mul_pow]
          _ = c ^ n • (gi i ^ n • (x : Q i)) := by
            rw [mul_comm (gi i ^ n) (c ^ n), mul_smul]
          _ = 0 := by rw [hpow, smul_zero]
      have hz :
          LocalizedModule.mkLinearMap (Submonoid.powers g) (Q i) (x : Q i) = 0 := by
        rw [IsLocalizedModule.eq_zero_iff (Submonoid.powers g)
          (LocalizedModule.mkLinearMap (Submonoid.powers g) (Q i))]
        exact ⟨⟨g ^ n, (Submonoid.powers g).pow_mem (Submonoid.mem_powers g) n⟩,
          hgpow⟩
      change LocalizedModule.mkLinearMap (Submonoid.powers g) (Q i) (x : Q i) = 0
      exact hz
    · exact bot_le
  have hregAway : ∀ i : Fin xs.length,
      IsSMulRegular (LocalizedModule (Submonoid.powers g) (Q i))
        (algebraMap R (Localization (Submonoid.powers g)) xs[i]) := by
    intro i
    exact isSMulRegular_localized_of_kernel (Submonoid.powers g) xs[i] (hKg i)
  have hweak := weakly_regular_localized_of_quotient
    (Submonoid.powers g) xs hregAway
  have hfull_atPrime :
      (Ideal.ofList xs • (⊤ : Submodule R M)).localized'
          (Localization p.primeCompl) p.primeCompl
          (LocalizedModule.mkLinearMap p.primeCompl M) =
        Ideal.ofList (xs.map (algebraMap R (Localization p.primeCompl))) •
          (⊤ : Submodule (Localization p.primeCompl)
            (LocalizedModule p.primeCompl M)) := by
    rw [Submodule.localized'_smul, Ideal.localized'_eq_map,
      Submodule.localized'_top, Ideal.map_ofList]
  have hfull_away :
      (Ideal.ofList xs • (⊤ : Submodule R M)).localized'
          (Localization (Submonoid.powers g)) (Submonoid.powers g)
          (LocalizedModule.mkLinearMap (Submonoid.powers g) M) =
        Ideal.ofList (xs.map (algebraMap R (Localization (Submonoid.powers g)))) •
          (⊤ : Submodule (Localization (Submonoid.powers g))
            (LocalizedModule (Submonoid.powers g) M)) := by
    rw [Submodule.localized'_smul, Ideal.localized'_eq_map,
      Submodule.localized'_top, Ideal.map_ofList]
  let C := M ⧸ (Ideal.ofList xs • (⊤ : Submodule R M))
  let eprime :
      (LocalizedModule p.primeCompl M ⧸
          (Ideal.ofList (xs.map (algebraMap R (Localization p.primeCompl))) •
            (⊤ : Submodule (Localization p.primeCompl)
              (LocalizedModule p.primeCompl M)))) ≃ₗ[Localization p.primeCompl]
        LocalizedModule p.primeCompl C := by
    exact Submodule.quotEquivOfEq _ _ hfull_atPrime.symm ≪≫ₗ
      localizedQuotientEquiv p.primeCompl
        (Ideal.ofList xs • (⊤ : Submodule R M))
  have hprime_subsingleton_of_away :
      Subsingleton (LocalizedModule (Submonoid.powers g) C) →
        Subsingleton (LocalizedModule p.primeCompl C) := by
    intro hawayC
    rw [LocalizedModule.subsingleton_iff (S := p.primeCompl)]
    intro c
    obtain ⟨s, hs, hsc⟩ :=
      (LocalizedModule.subsingleton_iff (S := Submonoid.powers g)).mp
        hawayC c
    obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff _ _).mp hs
    have hgprime : g ∈ p.primeCompl := by
      simpa [Ideal.primeCompl] using hg_notp
    have hspr : s ∈ p.primeCompl := by
      rw [← hn]
      exact p.primeCompl.pow_mem hgprime n
    exact ⟨s, hspr, hsc⟩
  refine ⟨g, hg_notp, ⟨hweak, ?_⟩⟩
  intro heq
  have hqaway_sub :
      Subsingleton
        (LocalizedModule (Submonoid.powers g) M ⧸
          (Ideal.ofList (xs.map (algebraMap R (Localization (Submonoid.powers g)))) •
            (⊤ : Submodule (Localization (Submonoid.powers g))
              (LocalizedModule (Submonoid.powers g) M)))) := by
    apply not_nontrivial_iff_subsingleton.mp
    intro hnon
    exact (Submodule.Quotient.nontrivial_iff.mp hnon) heq.symm
  let eaway :
      (LocalizedModule (Submonoid.powers g) M ⧸
          (Ideal.ofList (xs.map (algebraMap R (Localization (Submonoid.powers g)))) •
            (⊤ : Submodule (Localization (Submonoid.powers g))
              (LocalizedModule (Submonoid.powers g) M)))) ≃ₗ[Localization (Submonoid.powers g)]
        LocalizedModule (Submonoid.powers g) C := by
    exact Submodule.quotEquivOfEq _ _ hfull_away.symm ≪≫ₗ
      localizedQuotientEquiv (Submonoid.powers g)
        (Ideal.ofList xs • (⊤ : Submodule R M))
  have hCsub : Subsingleton (LocalizedModule (Submonoid.powers g) C) := by
    constructor
    intro x y
    obtain ⟨x', rfl⟩ := eaway.surjective x
    obtain ⟨y', rfl⟩ := eaway.surjective y
    exact congrArg eaway (hqaway_sub.elim _ _)
  have hCprime : Subsingleton (LocalizedModule p.primeCompl C) :=
    hprime_subsingleton_of_away hCsub
  have hI_top :
      Ideal.ofList (xs.map (algebraMap R (Localization p.primeCompl))) •
          (⊤ : Submodule (Localization p.primeCompl)
            (LocalizedModule p.primeCompl M)) = ⊤ :=
    Submodule.Quotient.subsingleton_iff.mp (by
      constructor
      intro x y
      apply eprime.injective
      exact hCprime.elim _ _)
  exact hp.2 hI_top.symm

theorem regular_sequence_join
    {A : Type*} [CommRing A] (I : Ideal A)
    {fs gs : List A}
    (hI : I = Ideal.ofList fs)
    (hfs : RingTheory.Sequence.IsRegular A fs)
    (hgs : RingTheory.Sequence.IsRegular (A ⧸ I)
      (gs.map (Ideal.Quotient.mk I))) :
    RingTheory.Sequence.IsRegular A (fs ++ gs) := by
  subst I
  rw [RingTheory.Sequence.isRegular_iff]
  refine ⟨(RingTheory.Sequence.isWeaklyRegular_append_iff' A fs gs).2 ⟨hfs.1, ?_⟩, ?_⟩
  ·
    have hS : (Ideal.ofList fs : Submodule A A) • (⊤ : Submodule A A) = Ideal.ofList fs := by
      rw [Ideal.smul_eq_mul, Ideal.mul_top]
    let e : (A ⧸ (Ideal.ofList fs • (⊤ : Submodule A A))) ≃ₗ[A ⧸ Ideal.ofList fs]
        (A ⧸ Ideal.ofList fs) := {
      (Submodule.quotEquivOfEq _ _ hS).toAddEquiv with
      map_smul' := by
        intro r x
        obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r
        induction x using Submodule.Quotient.induction_on with
        | _ x => rfl }
    exact (e.isWeaklyRegular_congr
      (gs.map (Ideal.Quotient.mk (Ideal.ofList fs)))).mpr hgs.1
  · intro htop
    have hmap :
        (Ideal.ofList gs).map (Ideal.Quotient.mk (Ideal.ofList fs)) =
          Ideal.ofList (gs.map (Ideal.Quotient.mk (Ideal.ofList fs))) := by
      rw [Ideal.map_ofList]
    have hsup : Ideal.ofList fs ⊔ Ideal.ofList gs = (⊤ : Ideal A) := by
      simpa [Ideal.ofList_append, Ideal.smul_eq_mul, Ideal.mul_top] using htop.symm
    have hsubQ : Subsingleton ((A ⧸ Ideal.ofList fs) ⧸
          (Ideal.ofList (gs.map (Ideal.Quotient.mk (Ideal.ofList fs))) :
            Submodule (A ⧸ Ideal.ofList fs) (A ⧸ Ideal.ofList fs))) := by
      rw [← hmap]
      apply (DoubleQuot.quotQuotEquivQuotSup
        (Ideal.ofList fs) (Ideal.ofList gs)).toEquiv.subsingleton_congr.mpr
      rw [hsup]
      infer_instance
    have hJ :
        (Ideal.ofList (gs.map (Ideal.Quotient.mk (Ideal.ofList fs))) :
          Submodule (A ⧸ Ideal.ofList fs) (A ⧸ Ideal.ofList fs)) •
            (⊤ : Submodule (A ⧸ Ideal.ofList fs) (A ⧸ Ideal.ofList fs)) =
          Ideal.ofList (gs.map (Ideal.Quotient.mk (Ideal.ofList fs))) := by
      rw [Ideal.smul_eq_mul, Ideal.mul_top]
    have hsub : Subsingleton ((A ⧸ Ideal.ofList fs) ⧸
          ((Ideal.ofList (gs.map (Ideal.Quotient.mk (Ideal.ofList fs))) :
              Submodule (A ⧸ Ideal.ofList fs) (A ⧸ Ideal.ofList fs)) •
            (⊤ : Submodule (A ⧸ Ideal.ofList fs) (A ⧸ Ideal.ofList fs)))) := by
      rw [hJ]
      exact hsubQ
    exact hgs.top_ne_smul (Submodule.Quotient.subsingleton_iff.mp hsub).symm

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
  induction xs generalizing M₁ M₂ M₃ with
  | nil =>
      have hn₃ : Nontrivial M₃ := h₃.nontrivial
      have hn₂ : Nontrivial M₂ :=
        @Function.Surjective.nontrivial M₂ M₃ hn₃ g hg
      exact @RingTheory.Sequence.IsRegular.nil R M₂ _ _ _ hn₂
  | cons r rs ih =>
      simp only [RingTheory.Sequence.isRegular_cons_iff] at h₁ h₃ ⊢
      refine ⟨?_, ?_⟩
      · rw [isSMulRegular_iff_right_eq_zero_of_smul]
        intro x hx
        have hxg0 : r • g x = 0 := by
          rw [← g.map_smul, hx, map_zero]
        have hxg : g x = 0 := by
          apply h₃.1
          change r • g x = r • (0 : M₃)
          simpa only [smul_zero] using hxg0
        obtain ⟨y, hy⟩ := hfg x |>.mp hxg
        have hfy : f (r • y) = 0 := by
          rw [f.map_smul, hy, hx]
        have hy0 : y = 0 := h₁.1 (hf (by
          simpa only [smul_zero, map_zero] using hfy))
        rw [← hy, hy0, map_zero]
      · let M₄ := M₃ ⧸ (⊤ : Submodule R M₃)
        let q₃ : M₃ →ₗ[R] M₄ := (⊤ : Submodule R M₃).mkQ
        have hq₃ : Exact g q₃ := by
          intro x
          constructor
          · intro _
            exact hg x
          · rintro ⟨y, rfl⟩
            rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
            exact Submodule.mem_top
        have hr₄ : IsSMulRegular M₄ r := by
          rw [isSMulRegular_iff_right_eq_zero_of_smul]
          intro x hx
          exact Subsingleton.elim _ _
        have hfi : Function.Injective (QuotSMulTop.map r f) := by
          intro x
          induction x using Submodule.Quotient.induction_on with
          | _ x =>
            intro y hxy
            induction y using Submodule.Quotient.induction_on with
            | _ y =>
              have hzero :
                  (Submodule.Quotient.mk (f x - f y) : QuotSMulTop r M₂) = 0 := by
                rw [Submodule.Quotient.mk_sub]
                simpa only [QuotSMulTop.map_apply_mk] using sub_eq_zero.mpr hxy
              have hmem : f x - f y ∈ r • (⊤ : Submodule R M₂) :=
                (Submodule.Quotient.mk_eq_zero _).mp hzero
              obtain ⟨z, _, hz⟩ :=
                (Submodule.mem_smul_pointwise_iff_exists (f x - f y) r
                  (⊤ : Submodule R M₂)).mp hmem
              have hz' : r • z = f (x - y) := by
                rw [f.map_sub]
                exact hz
              have hgz : g (r • z) = 0 := by
                rw [hz']
                exact (hfg (f (x - y))).mpr ⟨x - y, rfl⟩
              have hgz0 : r • g z = 0 := by
                simpa only [g.map_smul] using hgz
              have hgz : g z = 0 := by
                apply h₃.1
                change r • g z = r • (0 : M₃)
                simpa only [smul_zero] using hgz0
              obtain ⟨w, hw⟩ := (hfg z).mp hgz
              have hxy' : x - y = r • w := by
                apply hf
                rw [f.map_sub, f.map_smul, hw]
                exact (f.map_sub x y).symm.trans hz'.symm
              apply sub_eq_zero.mp
              rw [← Submodule.Quotient.mk_sub,
                Submodule.Quotient.mk_eq_zero]
              rw [hxy']
              exact (Submodule.mem_smul_pointwise_iff_exists _ _ _).2
                ⟨w, Submodule.mem_top, rfl⟩
        have hq : Exact (QuotSMulTop.map r f) (QuotSMulTop.map r g) :=
          QuotSMulTop.map_first_exact_on_four_term_exact_of_isSMulRegular_last
            hfg hq₃ hr₄
        exact ih (QuotSMulTop.map r f) (QuotSMulTop.map r g) hfi hq
          (QuotSMulTop.map_surjective r hg) h₁.2 h₃.2

private theorem regular_sequence_power_map_injective
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (a : R) (e : ℕ) (ha : IsSMulRegular M a) :
    Function.Injective
      (Submodule.mapQ (a • (⊤ : Submodule R M))
        (a ^ (e + 1) • (⊤ : Submodule R M))
        (LinearMap.lsmul R M (a ^ e)) (by
          rintro x ⟨z, _hz, rfl⟩
          change a ^ e • (a • z) ∈ a ^ (e + 1) • (⊤ : Submodule R M)
          rw [← mul_smul, pow_succ']
          exact (Submodule.mem_smul_pointwise_iff_exists _ _ _).mpr
            ⟨z, Submodule.mem_top, by rw [mul_comm]⟩)) := by
  intro x
  induction x using Submodule.Quotient.induction_on with
  | _ x =>
    intro y hxy
    induction y using Submodule.Quotient.induction_on with
    | _ y =>
      have hzero :
          (Submodule.Quotient.mk (a ^ e • x - a ^ e • y) :
            QuotSMulTop (a ^ (e + 1)) M) = 0 := by
        rw [Submodule.Quotient.mk_sub]
        have hxy' :
            (Submodule.Quotient.mk (a ^ e • x) :
                QuotSMulTop (a ^ (e + 1)) M) =
              Submodule.Quotient.mk (a ^ e • y) := by
          simpa only [Submodule.mapQ_apply, LinearMap.lsmul_apply] using hxy
        exact sub_eq_zero.mpr hxy'
      have hmem : a ^ e • (x - y) ∈ a ^ (e + 1) • (⊤ : Submodule R M) := by
        simpa only [smul_sub] using (Submodule.Quotient.mk_eq_zero _).mp hzero
      obtain ⟨z, _, hz⟩ :=
        (Submodule.mem_smul_pointwise_iff_exists (a ^ e • (x - y))
          (a ^ (e + 1)) (⊤ : Submodule R M)).mp hmem
      have hcancel : x - y = a • z := by
        apply ha.pow e
        change a ^ e • (x - y) = a ^ e • (a • z)
        rw [← hz, pow_succ, mul_smul]
      apply sub_eq_zero.mp
      rw [← Submodule.Quotient.mk_sub, Submodule.Quotient.mk_eq_zero]
      rw [hcancel]
      exact (Submodule.mem_smul_pointwise_iff_exists _ _ _).mpr
        ⟨z, Submodule.mem_top, rfl⟩

private theorem regular_sequence_power_short_exact
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (a : R) (e : ℕ) (ha : IsSMulRegular M a) :
    ∃ (f : QuotSMulTop a M →ₗ[R] QuotSMulTop (a ^ (e + 1)) M)
      (g : QuotSMulTop (a ^ (e + 1)) M →ₗ[R] QuotSMulTop (a ^ e) M),
      Function.Injective f ∧ Exact f g ∧ Function.Surjective g := by
  let hf : (a • (⊤ : Submodule R M)) ≤
      (a ^ (e + 1) • (⊤ : Submodule R M)).comap
        (LinearMap.lsmul R M (a ^ e)) := by
    rintro x ⟨z, hz, rfl⟩
    change a ^ e • (a • z) ∈ a ^ (e + 1) • (⊤ : Submodule R M)
    rw [← mul_smul, pow_succ']
    exact (Submodule.mem_smul_pointwise_iff_exists _ _ _).mpr
      ⟨z, Submodule.mem_top, by rw [mul_comm]⟩
  let hg : (a ^ (e + 1) • (⊤ : Submodule R M)) ≤
      (a ^ e • (⊤ : Submodule R M)).comap LinearMap.id := by
    rintro x ⟨z, hz, rfl⟩
    change a ^ (e + 1) • z ∈ a ^ e • (⊤ : Submodule R M)
    exact (Submodule.mem_smul_pointwise_iff_exists _ _ _).mpr
      ⟨a • z, Submodule.mem_top, by rw [pow_succ, mul_smul]⟩
  let f := Submodule.mapQ _ _ (LinearMap.lsmul R M (a ^ e)) hf
  let g := Submodule.mapQ _ _ (LinearMap.id : M →ₗ[R] M) hg
  refine ⟨f, g, ?_, ?_, ?_⟩
  · exact regular_sequence_power_map_injective a e ha
  · intro x
    constructor
    · intro hx
      induction x using Submodule.Quotient.induction_on with
      | _ x =>
        have hx' : x ∈ a ^ e • (⊤ : Submodule R M) := by
          exact (Submodule.Quotient.mk_eq_zero _).mp (by simpa [g] using hx)
        obtain ⟨z, _, hz⟩ :=
          (Submodule.mem_smul_pointwise_iff_exists x (a ^ e)
            (⊤ : Submodule R M)).mp hx'
        refine ⟨Submodule.Quotient.mk z, ?_⟩
        simp only [f, Submodule.mapQ_apply, LinearMap.lsmul_apply]
        exact congrArg Submodule.Quotient.mk hz
    · rintro ⟨y, rfl⟩
      induction y using Submodule.Quotient.induction_on with
      | _ y =>
        simp only [f, g, Submodule.mapQ_apply, LinearMap.lsmul_apply]
        exact (Submodule.Quotient.mk_eq_zero _).mpr
          ((Submodule.mem_smul_pointwise_iff_exists _ _ _).mpr
            ⟨y, Submodule.mem_top, rfl⟩)
  · intro x
    induction x using Submodule.Quotient.induction_on with
    | _ x => exact ⟨Submodule.Quotient.mk x, by simp [g]⟩

private noncomputable def regular_sequence_quot_smul_comm
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (a r : R) :
    QuotSMulTop r (QuotSMulTop a M) ≃ₗ[R]
      QuotSMulTop a (QuotSMulTop r M) := by
  have hsingleA : Ideal.ofList [r] • (⊤ : Submodule R (QuotSMulTop a M)) =
      r • (⊤ : Submodule R (QuotSMulTop a M)) := by
    rw [Ideal.ofList_singleton, Submodule.ideal_span_singleton_smul]
  have hsingleR : Ideal.ofList [a] • (⊤ : Submodule R (QuotSMulTop r M)) =
      a • (⊤ : Submodule R (QuotSMulTop r M)) := by
    rw [Ideal.ofList_singleton, Submodule.ideal_span_singleton_smul]
  let e₁ : QuotSMulTop r (QuotSMulTop a M) ≃ₗ[R]
      M ⧸ (Ideal.ofList [a, r] • (⊤ : Submodule R M)) := by
    exact
      (Submodule.quotEquivOfEq _ _
        hsingleA.symm) ≪≫ₗ
        (Submodule.quotOfListConsSMulTopEquivQuotSMulTopInner M a [r]).symm
  let e₂ : (M ⧸ (Ideal.ofList [r, a] • (⊤ : Submodule R M))) ≃ₗ[R]
      QuotSMulTop a (QuotSMulTop r M) := by
    let q₂ : (QuotSMulTop r M ⧸
        (Ideal.ofList [a] • (⊤ : Submodule R (QuotSMulTop r M)))) ≃ₗ[R]
        QuotSMulTop a (QuotSMulTop r M) :=
      Submodule.quotEquivOfEq _ _ hsingleR
    exact Submodule.quotOfListConsSMulTopEquivQuotSMulTopInner M r [a] ≪≫ₗ q₂
  let h : Ideal.ofList [a, r] • (⊤ : Submodule R M) =
      Ideal.ofList [r, a] • (⊤ : Submodule R M) := by
    calc
      Ideal.ofList [a, r] • (⊤ : Submodule R M) =
          (a • (⊤ : Submodule R M)) ⊔ (r • (⊤ : Submodule R M)) := by
        simp [Ideal.ofList_cons, Ideal.ofList_nil, Submodule.sup_smul,
          Submodule.ideal_span_singleton_smul]
      _ = (r • (⊤ : Submodule R M)) ⊔ (a • (⊤ : Submodule R M)) := sup_comm _ _
      _ = Ideal.ofList [r, a] • (⊤ : Submodule R M) := by
        simp [Ideal.ofList_cons, Ideal.ofList_nil, Submodule.sup_smul,
          Submodule.ideal_span_singleton_smul]
  exact e₁ ≪≫ₗ Submodule.quotEquivOfEq _ _ h ≪≫ₗ e₂

private theorem regular_sequence_power_quotient_iff
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (a : R) (xs : List R) (e : ℕ) (he : 0 < e)
    (ha : IsSMulRegular M a) :
    RingTheory.Sequence.IsRegular (QuotSMulTop a M) xs ↔
      RingTheory.Sequence.IsRegular (QuotSMulTop (a ^ e) M) xs := by
  induction xs generalizing M e with
  | nil =>
      have hpow_le : a ^ e • (⊤ : Submodule R M) ≤ a • (⊤ : Submodule R M) := by
        obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt he)
        rintro x ⟨z, _, rfl⟩
        refine (Submodule.mem_smul_pointwise_iff_exists _ _ _).mpr
          ⟨a ^ k • z, Submodule.mem_top, ?_⟩
        have hz : a • (a ^ k • z) = (a ^ k * a) • z := by
          rw [← mul_smul, mul_comm]
        simpa [pow_succ, LinearMap.lsmul_apply] using hz
      constructor
      · intro h
        have htop : (a ^ e • (⊤ : Submodule R M)) ≠ (⊤ : Submodule R M) := by
          intro heq
          have hle : (⊤ : Submodule R M) ≤ a • (⊤ : Submodule R M) := by
            have hle' := hpow_le
            rw [heq] at hle'
            exact hle'
          exact (Submodule.Quotient.nontrivial_iff.mp h.nontrivial)
            (le_antisymm le_top hle)
        exact @RingTheory.Sequence.IsRegular.nil R (QuotSMulTop (a ^ e) M)
          _ _ _ (Submodule.Quotient.nontrivial_iff.mpr htop)
      · intro h
        have htop : (a • (⊤ : Submodule R M)) ≠ (⊤ : Submodule R M) := by
          intro heq
          have hpow : ∀ k : ℕ, a ^ k • (⊤ : Submodule R M) = ⊤ := by
            intro k
            induction k with
            | zero => simp
            | succ k ih =>
                calc
                  a ^ (k + 1) • (⊤ : Submodule R M) =
                      a ^ k • (a • (⊤ : Submodule R M)) := by
                    rw [pow_succ, mul_smul]
                  _ = a ^ k • (⊤ : Submodule R M) :=
                    congrArg (fun N : Submodule R M => a ^ k • N) heq
                  _ = ⊤ := ih
          exact (Submodule.Quotient.nontrivial_iff.mp h.nontrivial)
            (hpow e)
        exact @RingTheory.Sequence.IsRegular.nil R (QuotSMulTop a M)
          _ _ _ (Submodule.Quotient.nontrivial_iff.mpr htop)
  | cons r rs ih =>
      constructor
      · intro h
        have hforward : ∀ k : ℕ,
            RingTheory.Sequence.IsRegular (QuotSMulTop a M) (r :: rs) →
              RingTheory.Sequence.IsRegular (QuotSMulTop (a ^ (k + 1)) M) (r :: rs) := by
          intro k hA
          induction k with
          | zero =>
              change RingTheory.Sequence.IsRegular
                (QuotSMulTop (a ^ 1) M) (r :: rs)
              rw [pow_one]
              exact hA
          | succ k ihk =>
              obtain ⟨f, g, hf, hfg, hg⟩ :=
                regular_sequence_power_short_exact a (k + 1) ha
              have hC := ihk
              exact regular_sequence_of_short_exact f g hf hfg hg (r :: rs) hA hC
        have he' : 1 ≤ e := he
        have heqpow : e - 1 + 1 = e := by omega
        have hforward' := hforward (e - 1) h
        rw [heqpow] at hforward'
        exact hforward'
      · intro h
        have heqpow : e - 1 + 1 = e := by omega
        rw [← heqpow] at h
        have hcons :=
          (RingTheory.Sequence.isRegular_cons_iff
            (M := QuotSMulTop (a ^ (e - 1 + 1)) M) r rs).mp h
        obtain ⟨f, g, hf, hfg, hg⟩ :=
          regular_sequence_power_short_exact a (e - 1) ha
        have hr : IsSMulRegular (QuotSMulTop a M) r := by
          rw [isSMulRegular_iff_right_eq_zero_of_smul]
          intro x hx
          apply hf
          apply hcons.1
          change r • f x = r • f 0
          rw [← f.map_smul, hx, map_zero]
          simp
        have ha' : IsSMulRegular (QuotSMulTop r M) a := by
          rw [isSMulRegular_iff_right_eq_zero_of_smul]
          intro x hx
          induction x using Submodule.Quotient.induction_on with
          | _ x =>
              have hmem : a • x ∈ r • (⊤ : Submodule R M) := by
                exact (Submodule.Quotient.mk_eq_zero _).mp (by simpa using hx)
              obtain ⟨y, _, hy⟩ :=
                (Submodule.mem_smul_pointwise_iff_exists (a • x) r
                  (⊤ : Submodule R M)).mp hmem
              have hry : r • (Submodule.Quotient.mk y : QuotSMulTop a M) = 0 := by
                change (Submodule.Quotient.mk (r • y) : QuotSMulTop a M) = 0
                rw [hy, Submodule.Quotient.mk_eq_zero]
                exact (Submodule.mem_smul_pointwise_iff_exists _ _ _).mpr
                  ⟨x, Submodule.mem_top, rfl⟩
              have hy0 : (Submodule.Quotient.mk y : QuotSMulTop a M) = 0 := by
                apply hr
                simpa only [smul_zero] using hry
              obtain ⟨z, _, hz⟩ :=
                (Submodule.mem_smul_pointwise_iff_exists y a
                  (⊤ : Submodule R M)).mp
                  ((Submodule.Quotient.mk_eq_zero _).mp hy0)
              have hcancel : x = r • z := by
                apply ha
                change a • x = a • (r • z)
                calc
                  a • x = r • y := hy.symm
                  _ = r • (a • z) := by rw [← hz]
                  _ = a • (r • z) := by rw [smul_comm]
              rw [hcancel, Submodule.Quotient.mk_eq_zero]
              exact (Submodule.mem_smul_pointwise_iff_exists _ _ _).mpr
                ⟨z, Submodule.mem_top, rfl⟩
        have htail' :
            RingTheory.Sequence.IsRegular
              (QuotSMulTop (a ^ (e - 1 + 1)) (QuotSMulTop r M)) rs := by
          exact ((regular_sequence_quot_smul_comm (a ^ (e - 1 + 1)) r).isRegular_congr rs).mp
            hcons.2
        have htail :
            RingTheory.Sequence.IsRegular
              (QuotSMulTop a (QuotSMulTop r M)) rs :=
          (ih (M := QuotSMulTop r M) (e := e - 1 + 1) (by omega) ha').mpr htail'
        have htail'' :
            RingTheory.Sequence.IsRegular
              (QuotSMulTop r (QuotSMulTop a M)) rs := by
          exact ((regular_sequence_quot_smul_comm a r).isRegular_congr rs).mpr htail
        exact (RingTheory.Sequence.isRegular_cons_iff
          (M := QuotSMulTop a M) r rs).mpr ⟨hr, htail''⟩

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
  induction n generalizing M with
  | zero =>
      simp only [List.ofFn_zero]
  | succ n ih =>
      simp only [List.ofFn_succ]
      constructor
      · intro h
        have hcons :=
          (RingTheory.Sequence.isRegular_cons_iff (M := M) (f 0)
            (List.ofFn (fun i : Fin n => f i.succ))).mp h
        have htail :=
          (ih (M := QuotSMulTop (f 0) M)
            (f := fun i : Fin n => f i.succ)
            (e := fun i : Fin n => e i.succ)
            (fun i => he i.succ)).mp hcons.2
        have htailpow :=
          (regular_sequence_power_quotient_iff (f 0)
            (List.ofFn (fun i : Fin n => f i.succ ^ e i.succ))
            (e 0) (he 0) hcons.1).mp htail
        exact (RingTheory.Sequence.isRegular_cons_iff (M := M) (f 0 ^ e 0)
          (List.ofFn (fun i : Fin n => f i.succ ^ e i.succ))).mpr
          ⟨hcons.1.pow (e 0), htailpow⟩
      · intro h
        have hcons :=
          (RingTheory.Sequence.isRegular_cons_iff (M := M) (f 0 ^ e 0)
            (List.ofFn (fun i : Fin n => f i.succ ^ e i.succ))).mp h
        have ha : IsSMulRegular M (f 0) :=
          (IsSMulRegular.pow_iff (M := M) (a := f 0) (he 0)).mp hcons.1
        have htailpow :
            RingTheory.Sequence.IsRegular (QuotSMulTop (f 0) M)
              (List.ofFn (fun i : Fin n => f i.succ ^ e i.succ)) :=
          (regular_sequence_power_quotient_iff (f 0)
            (List.ofFn (fun i : Fin n => f i.succ ^ e i.succ))
            (e 0) (he 0) ha).mpr hcons.2
        have htail :=
          (ih (M := QuotSMulTop (f 0) M)
            (f := fun i : Fin n => f i.succ)
            (e := fun i : Fin n => e i.succ)
            (fun i => he i.succ)).mpr htailpow
        exact (RingTheory.Sequence.isRegular_cons_iff (M := M) (f 0)
          (List.ofFn (fun i : Fin n => f i.succ))).mpr ⟨ha, htail⟩

/- The source's polynomial proof uses the direct-sum decomposition indexed by multi-indices
  and the ideals `I_E`; these are proof-level bookkeeping for the final TFAE, not additional
  chapter-facing structures. -/
private def polynomialCoefficientIdeal
    {R : Type u} [CommRing R] {n : ℕ} (f : Fin n → R)
    (xs : List (Fin n)) (m : Fin n →₀ ℕ) : Ideal R :=
  Ideal.span {r | ∃ i ∈ xs, m i ≠ 0 ∧ r = f i}

private theorem mvPolynomial_mem_ofList_C_mul_X_iff
    {R : Type u} [CommRing R] {n : ℕ} (f : Fin n → R)
    (xs : List (Fin n)) (p : MvPolynomial (Fin n) R) :
    p ∈ Ideal.ofList
        (xs.map (fun i => MvPolynomial.C (f i) * MvPolynomial.X i)) ↔
      ∀ m, p.coeff m ∈ polynomialCoefficientIdeal f xs m := by
  classical
  constructor
  · intro hp
    change p ∈ Ideal.span {r |
      r ∈ xs.map (fun i => MvPolynomial.C (f i) * MvPolynomial.X i)} at hp
    induction hp using Submodule.span_induction with
    | mem q hq =>
        have hq' : q ∈ xs.map (fun i => MvPolynomial.C (f i) * MvPolynomial.X i) := hq
        obtain ⟨i, hi, hqi⟩ := List.mem_map.mp hq'
        subst q
        intro m
        by_cases hmi : Finsupp.single i 1 = m
        · subst m
          apply Ideal.subset_span
          exact ⟨i, hi, by simp⟩
        · rw [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_X]
          simp [hmi]
    | zero =>
        intro m
        simp
    | add q₁ q₂ _ _ hq₁ hq₂ =>
        intro m
        exact (polynomialCoefficientIdeal f xs m).add_mem (hq₁ m) (hq₂ m)
    | smul q₀ q _ hq =>
        intro m
        change MvPolynomial.coeff m (q₀ * q) ∈ polynomialCoefficientIdeal f xs m
        rw [MvPolynomial.coeff_mul]
        apply Submodule.sum_mem _
        intro z hz
        have hsum : z.1 + z.2 = m := Finset.mem_antidiagonal.mp hz
        have hle : polynomialCoefficientIdeal f xs z.2 ≤
            polynomialCoefficientIdeal f xs m := by
          apply Ideal.span_le.mpr
          rintro r ⟨i, hi, hzi, rfl⟩
          apply Ideal.subset_span
          refine ⟨i, hi, ?_, rfl⟩
          intro hmi
          apply hzi
          have hcoord := congrArg (fun w : Fin n →₀ ℕ => w i) hsum
          simp only [Finsupp.add_apply] at hcoord
          omega
        exact (polynomialCoefficientIdeal f xs m).mul_mem_left
          (MvPolynomial.coeff z.1 q₀) (hle (hq z.2))
  · intro hp
    rw [p.as_sum]
    apply Submodule.sum_mem
    intro m hm
    let K : Ideal R :=
      { carrier := {r | MvPolynomial.monomial m r ∈
            Ideal.ofList (xs.map (fun i => MvPolynomial.C (f i) * MvPolynomial.X i))}
        zero_mem' := by simp
        add_mem' := by
          intro a b ha hb
          change MvPolynomial.monomial m (a + b) ∈
            Ideal.ofList (xs.map (fun i => MvPolynomial.C (f i) * MvPolynomial.X i))
          rw [map_add]
          exact
            (Ideal.ofList (xs.map (fun i => MvPolynomial.C (f i) * MvPolynomial.X i))).add_mem ha hb
        smul_mem' := by
          intro a b hb
          change MvPolynomial.monomial m (a * b) ∈
            Ideal.ofList (xs.map (fun i => MvPolynomial.C (f i) * MvPolynomial.X i))
          have h :=
            (Ideal.ofList (xs.map (fun i => MvPolynomial.C (f i) * MvPolynomial.X i))).mul_mem_left
              (MvPolynomial.C a) hb
          simpa [MvPolynomial.C_mul_monomial] using h }
    have hIK : polynomialCoefficientIdeal f xs m ≤ K := by
      apply Ideal.span_le.mpr
      rintro r ⟨i, hi, hmi, rfl⟩
      have hgen : MvPolynomial.C (f i) * MvPolynomial.X i ∈
          Ideal.ofList (xs.map (fun j => MvPolynomial.C (f j) * MvPolynomial.X j)) :=
        Ideal.subset_span (List.mem_map.mpr ⟨i, hi, rfl⟩)
      have hmul :=
        (Ideal.ofList (xs.map (fun j => MvPolynomial.C (f j) * MvPolynomial.X j))).mul_mem_right
          (MvPolynomial.monomial (m - Finsupp.single i 1) 1) hgen
      show MvPolynomial.monomial m (f i) ∈
        Ideal.ofList (xs.map (fun j => MvPolynomial.C (f j) * MvPolynomial.X j))
      have hsum : Finsupp.single i 1 + (m - Finsupp.single i 1) = m := by
        rw [add_comm, Finsupp.sub_add_single_one_cancel hmi]
      simpa [MvPolynomial.C_mul_monomial, MvPolynomial.X,
        MvPolynomial.monomial_mul, hsum] using hmul
    exact hIK (hp m)

private theorem polynomial_smulRegular_quotient_iff
    {R : Type u} [CommRing R] {n : ℕ} (f : Fin n → R)
    (xs : List (Fin n)) (i : Fin n) (hi : i ∉ xs) :
    IsSMulRegular
        (MvPolynomial (Fin n) R ⧸
          (Ideal.ofList
            (xs.map (fun j => MvPolynomial.C (f j) * MvPolynomial.X j)) :
            Submodule (MvPolynomial (Fin n) R) (MvPolynomial (Fin n) R)))
        (MvPolynomial.C (f i) * MvPolynomial.X i) ↔
      ∀ m, IsSMulRegular
        (R ⧸ polynomialCoefficientIdeal f xs m) (f i) := by
  classical
  let P := MvPolynomial (Fin n) R
  let J : Ideal P := Ideal.ofList
    (xs.map (fun j => MvPolynomial.C (f j) * MvPolynomial.X j))
  have hterm : MvPolynomial.C (f i) * MvPolynomial.X i =
      MvPolynomial.monomial (Finsupp.single i 1) (f i) := by
    simp [MvPolynomial.X, MvPolynomial.C_mul_monomial]
  have hIeq (m : Fin n →₀ ℕ) :
      polynomialCoefficientIdeal f xs (Finsupp.single i 1 + m) =
        polynomialCoefficientIdeal f xs m := by
    apply congrArg Ideal.span
    ext r
    constructor <;> rintro ⟨j, hj, hne, rfl⟩ <;>
      refine ⟨j, hj, ?_, rfl⟩
    · intro hm
      apply hne
      have hij : i ≠ j := by
        intro hij
        exact hi (hij ▸ hj)
      simpa [Finsupp.add_apply, Finsupp.single_apply, hij] using hm
    · intro hm
      apply hne
      have hij : i ≠ j := by
        intro hij
        exact hi (hij ▸ hj)
      simpa [Finsupp.add_apply, Finsupp.single_apply, hij] using hm
  constructor
  · intro hreg m
    rw [isSMulRegular_iff_right_eq_zero_of_smul] at hreg ⊢
    intro x hx
    induction x using Submodule.Quotient.induction_on with
    | _ x =>
        have hxm : f i * x ∈ polynomialCoefficientIdeal f xs m := by
          apply (Submodule.Quotient.mk_eq_zero _).mp
          change (f i) • (Submodule.Quotient.mk x :
            R ⧸ polynomialCoefficientIdeal f xs m) = 0
          exact hx
        let p : P := MvPolynomial.monomial m x
        have hpJ :
            (MvPolynomial.C (f i) * MvPolynomial.X i) * p ∈ J := by
          apply (mvPolynomial_mem_ofList_C_mul_X_iff f xs _).mpr
          intro k
          by_cases hk : Finsupp.single i 1 + m = k
          · subst k
            rw [hIeq]
            rw [hterm]
            dsimp [p]
            rw [MvPolynomial.coeff_monomial_mul]
            simpa [p] using hxm
          · rw [hterm]
            dsimp [p]
            rw [MvPolynomial.coeff_monomial_mul']
            split_ifs with hle
            · rw [MvPolynomial.coeff_monomial]
              split_ifs with hkm
              · exfalso
                apply hk
                rw [hkm, add_comm]
                exact tsub_add_cancel_of_le hle
              · simp
            · simp
        have hzero := hreg (Submodule.Quotient.mk p)
        have hzero' : (Submodule.Quotient.mk p : P ⧸ (J : Submodule P P)) = 0 :=
          hzero (by
            change Submodule.Quotient.mk ((MvPolynomial.C (f i) * MvPolynomial.X i) * p) = 0
            exact (Submodule.Quotient.mk_eq_zero _).mpr hpJ)
        have hpzero : p ∈ J := (Submodule.Quotient.mk_eq_zero _).mp hzero'
        have hpcoeff := (mvPolynomial_mem_ofList_C_mul_X_iff f xs p).mp hpzero
        simpa [p] using (Submodule.Quotient.mk_eq_zero _).mpr (hpcoeff m)
  · intro hreg
    rw [isSMulRegular_iff_right_eq_zero_of_smul]
    intro x hx
    induction x using Submodule.Quotient.induction_on with
    | _ p =>
        have hpJ :
            (MvPolynomial.C (f i) * MvPolynomial.X i) * p ∈ J := by
          apply (Submodule.Quotient.mk_eq_zero _).mp
          change (MvPolynomial.C (f i) * MvPolynomial.X i) •
            (Submodule.Quotient.mk p : P ⧸ (J : Submodule P P)) = 0
          exact hx
        have hpcoeff :=
          (mvPolynomial_mem_ofList_C_mul_X_iff f xs
            ((MvPolynomial.C (f i) * MvPolynomial.X i) * p)).mp hpJ
        apply (Submodule.Quotient.mk_eq_zero _).mpr
        apply (mvPolynomial_mem_ofList_C_mul_X_iff f xs p).mpr
        intro m
        have hcoeff := hpcoeff (Finsupp.single i 1 + m)
        have hcoeff' :
            f i * MvPolynomial.coeff m p ∈
              polynomialCoefficientIdeal f xs m := by
          rw [hIeq (m := m)] at hcoeff
          simpa [MvPolynomial.C_mul_monomial, MvPolynomial.X,
            MvPolynomial.coeff_monomial_mul] using hcoeff
        let q : R ⧸ polynomialCoefficientIdeal f xs m :=
          Submodule.Quotient.mk (MvPolynomial.coeff m p)
        have hq : (f i) • q = 0 := by
          change (Submodule.Quotient.mk (f i * MvPolynomial.coeff m p) :
            R ⧸ polynomialCoefficientIdeal f xs m) = 0
          exact (Submodule.Quotient.mk_eq_zero _).mpr hcoeff'
        have hq' := (isSMulRegular_iff_right_eq_zero_of_smul.mp (hreg m)) q hq
        exact (Submodule.Quotient.mk_eq_zero _).mp hq'

private theorem polynomial_weaklyRegular_of_sublist
    {R : Type u} [CommRing R] (n : ℕ) (f : Fin n → R)
    (hsub : ∀ ys : List R, ys.Sublist (List.ofFn f) →
      RingTheory.Sequence.IsWeaklyRegular R ys) :
    RingTheory.Sequence.IsWeaklyRegular (MvPolynomial (Fin n) R)
      (List.ofFn (fun i => MvPolynomial.C (f i) * MvPolynomial.X i)) := by
  classical
  rw [RingTheory.Sequence.isWeaklyRegular_iff_Fin]
  intro k
  let i : Fin n := ⟨k, by simpa using k.isLt⟩
  let xs : List (Fin n) := (List.ofFn (fun j : Fin n => j)).take (i : ℕ)
  have htake :
      (List.ofFn (fun j : Fin n => MvPolynomial.C (f j) * MvPolynomial.X j)).take (i : ℕ) =
        xs.map (fun j => MvPolynomial.C (f j) * MvPolynomial.X j) := by
    simp [xs, List.ofFn_eq_map, List.map_take]
  have hi : i ∉ xs := by
    intro hi'
    have hi'' : i ∈ (List.ofFn (fun j : Fin n => j)).take (i : ℕ) := by
      simpa [xs] using hi'
    have hi'lt :=
      (List.mem_take_iff_idxOf_lt (l := List.ofFn (fun j : Fin n => j))
        (a := i) (by simp [i])).mp hi''
    have hnodup : (List.ofFn (fun j : Fin n => j)).Nodup := by
      exact (List.nodup_ofFn).mpr (Function.injective_id)
    have hidx : (List.ofFn (fun j : Fin n => j)).idxOf i = (i : ℕ) := by
      have hget := List.get_idxOf hnodup
        (⟨(i : ℕ), by simpa only [List.length_ofFn] using i.isLt⟩ :
          Fin (List.ofFn (fun j : Fin n => j)).length)
      simpa [i] using hget
    rw [hidx] at hi'lt
    exact (Nat.lt_irrefl _ hi'lt)
  have hpoly :
      IsSMulRegular
        (MvPolynomial (Fin n) R ⧸
          (Ideal.ofList
            (xs.map (fun j => MvPolynomial.C (f j) * MvPolynomial.X j)) :
            Submodule (MvPolynomial (Fin n) R) (MvPolynomial (Fin n) R)))
        (MvPolynomial.C (f i) * MvPolynomial.X i) := by
    apply (polynomial_smulRegular_quotient_iff f xs i hi).mpr
    intro m
    let filt := xs.filter (fun j => m j ≠ 0)
    let ys := filt.map f
    have hxs : xs.Sublist (List.ofFn (fun j : Fin n => j)) := by
      exact List.take_sublist _ _
    have hsucc : (xs ++ [i]).Sublist (List.ofFn (fun j : Fin n => j)) := by
      have heq :
          (List.ofFn (fun j : Fin n => j)).take ((i : ℕ) + 1) = xs ++ [i] := by
        rw [List.take_succ_eq_append_getElem]
        · have hget :
              (List.ofFn (fun j : Fin n => j)).get
                  (⟨(i : ℕ), by simpa only [List.length_ofFn] using i.isLt⟩ :
                    Fin (List.ofFn (fun j : Fin n => j)).length) = i := by
            rw [List.get_ofFn]
            apply Fin.ext
            rfl
          simp [xs]
        · simpa only [List.length_ofFn] using i.isLt
      rw [← heq]
      exact List.take_sublist _ _
    have hfilt : (filt ++ [i]).Sublist (List.ofFn (fun j : Fin n => j)) := by
      exact (List.filter_sublist.append (List.Sublist.refl _)).trans hsucc
    have hys : (ys ++ [f i]).Sublist (List.ofFn f) := by
      have hmap := hfilt.map f
      simpa [ys, List.map_append, List.ofFn_eq_map] using hmap
    have hreg := hsub (ys ++ [f i]) hys
    have hri := hreg.regular_mod_prev ys.length (by simp)
    have hI : polynomialCoefficientIdeal f xs m = Ideal.ofList ys := by
      apply le_antisymm
      · apply Ideal.span_le.mpr
        rintro r ⟨j, hjxs, hjm, rfl⟩
        apply Ideal.subset_span
        apply List.mem_map.mpr
        exact ⟨j, by simp [filt, hjxs, hjm], rfl⟩
      · apply Ideal.span_le.mpr
        intro r hr
        obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hr
        have hj' := List.mem_filter.mp hj
        apply Ideal.subset_span
        exact ⟨j, List.filter_sublist.subset hj, by simpa using hj'.2, rfl⟩
    have hri' :
        IsSMulRegular (R ⧸ (Ideal.ofList ys • (⊤ : Submodule R R))) (f i) := by
      rw [List.take_append_of_le_length (Nat.le_refl _)] at hri
      rw [List.take_length] at hri
      simpa using hri
    rw [Ideal.smul_eq_mul, ← hI, Ideal.mul_top] at hri'
    exact hri'
  have htake' :
      (List.ofFn (fun j : Fin n => MvPolynomial.C (f j) * MvPolynomial.X j)).take
          (k : ℕ) = xs.map (fun j => MvPolynomial.C (f j) * MvPolynomial.X j) := by
    simpa [i] using htake
  have hget' :
      (List.ofFn (fun j : Fin n => MvPolynomial.C (f j) * MvPolynomial.X j))[k] =
        MvPolynomial.C (f i) * MvPolynomial.X i := by
    change (List.ofFn (fun j : Fin n => MvPolynomial.C (f j) * MvPolynomial.X j)).get
        k = MvPolynomial.C (f i) * MvPolynomial.X i
    simp [i]
  rw [htake', Ideal.smul_eq_mul, Ideal.mul_top, hget']
  exact hpoly

private theorem sublist_weaklyRegular_of_polynomial_weaklyRegular
    {R : Type u} [CommRing R] (n : ℕ) (f : Fin n → R)
    (hpoly : RingTheory.Sequence.IsWeaklyRegular (MvPolynomial (Fin n) R)
      (List.ofFn (fun i => MvPolynomial.C (f i) * MvPolynomial.X i))) :
    ∀ ys : List R, ys.Sublist (List.ofFn f) →
      RingTheory.Sequence.IsWeaklyRegular R ys := by
  classical
  intro ys hys
  have hsource : List.ofFn f =
      (List.ofFn (fun j : Fin n => j)).map f := by
    simp [List.ofFn_eq_map]
  rw [hsource] at hys
  obtain ⟨js, hjs, rfl⟩ := List.sublist_map_iff.mp hys
  rw [RingTheory.Sequence.isWeaklyRegular_iff_Fin]
  intro k
  let kk : Fin js.length := ⟨k, by simpa using k.isLt⟩
  let j : Fin n := js[kk]
  let xs : List (Fin n) :=
    (List.ofFn (fun q : Fin n => q)).take (j : ℕ)
  have hsourcepair :
      (List.ofFn (fun q : Fin n => q)).Pairwise (fun a b => a < b) := by
    rw [List.pairwise_ofFn]
    intro a b hab
    exact hab
  have hpair : js.Pairwise (fun a b => a < b) :=
    hsourcepair.sublist hjs
  have hsourceNodup : (List.ofFn (fun q : Fin n => q)).Nodup := by
    exact (List.nodup_ofFn).mpr Function.injective_id
  have hprev : ∀ q ∈ js.take (k : ℕ), q < j := by
    intro q hq
    have hqmem : q ∈ js := List.mem_of_mem_take hq
    have hqidx : js.idxOf q < (k : ℕ) :=
      (List.mem_take_iff_idxOf_lt hqmem).mp hq
    have hqget :
        js.get ⟨js.idxOf q, List.idxOf_lt_length_of_mem hqmem⟩ = q := by
      exact List.idxOf_get (List.idxOf_lt_length_of_mem hqmem)
    have hrel := (List.pairwise_iff_get.mp hpair)
      ⟨js.idxOf q, List.idxOf_lt_length_of_mem hqmem⟩ kk hqidx
    change q < js.get kk
    rw [← hqget]
    exact hrel
  have hprev_mem : ∀ q ∈ js.take (k : ℕ), q ∈ xs := by
    intro q hq
    have hqsource : q ∈ List.ofFn (fun q : Fin n => q) :=
      hjs.subset (List.mem_of_mem_take hq)
    have hqidx :
        (List.ofFn (fun q : Fin n => q)).idxOf q = (q : ℕ) := by
      have hget := List.get_idxOf hsourceNodup
        (⟨(q : ℕ), by simp⟩ : Fin (List.ofFn (fun q : Fin n => q)).length)
      simpa using hget
    apply (List.mem_take_iff_idxOf_lt hqsource).mpr
    rw [hqidx]
    exact hprev q hq
  have hp := hpoly.regular_mod_prev (j : ℕ) (by simp [j])
  have htakej :
      (List.ofFn (fun q : Fin n => MvPolynomial.C (f q) * MvPolynomial.X q)).take
          (j : ℕ) = xs.map (fun q => MvPolynomial.C (f q) * MvPolynomial.X q) := by
    simp [xs, List.ofFn_eq_map, List.map_take]
  have hgetj :
      (List.ofFn (fun q : Fin n => MvPolynomial.C (f q) * MvPolynomial.X q))[j] =
        MvPolynomial.C (f j) * MvPolynomial.X j := by
    simp [j]
  have hjnot : j ∉ xs := by
    intro hjx
    have hjx' : j ∈ (List.ofFn (fun q : Fin n => q)).take (j : ℕ) := by
      simpa [xs] using hjx
    have hjlt :=
      (List.mem_take_iff_idxOf_lt (l := List.ofFn (fun q : Fin n => q))
        (a := j) (by simp [j])).mp hjx'
    have hjidx :
        (List.ofFn (fun q : Fin n => q)).idxOf j = (j : ℕ) := by
      have hget := List.get_idxOf hsourceNodup
        (⟨(j : ℕ), by simp⟩ : Fin (List.ofFn (fun q : Fin n => q)).length)
      simpa using hget
    rw [hjidx] at hjlt
    exact (Nat.lt_irrefl _ hjlt)
  have hp' := hp
  rw [htakej, Ideal.smul_eq_mul, Ideal.mul_top] at hp'
  have hp'' :
      IsSMulRegular
        (MvPolynomial (Fin n) R ⧸
          (Ideal.ofList
            (xs.map (fun q => MvPolynomial.C (f q) * MvPolynomial.X q)) :
            Submodule (MvPolynomial (Fin n) R) (MvPolynomial (Fin n) R)))
        (MvPolynomial.C (f j) * MvPolynomial.X j) := by
    simpa [j] using hp'
  have hcoeff := (polynomial_smulRegular_quotient_iff f xs j hjnot).mp hp''
  let lt : List (Fin n) := js.take (k : ℕ)
  let t : Fin n →₀ ℕ :=
    Finsupp.onFinset lt.toFinset (fun q => if q ∈ lt then 1 else 0) (by simp)
  have ht (q : Fin n) : t q = if q ∈ lt then 1 else 0 := by
    by_cases hq : q ∈ lt <;> simp [t, hq]
  have hI : polynomialCoefficientIdeal f xs t = Ideal.ofList (List.map f lt) := by
    apply le_antisymm
    · apply Ideal.span_le.mpr
      rintro r ⟨q, hqxs, hqt, rfl⟩
      have hq : q ∈ lt := by
        by_contra hq'
        exact hqt (by simp [ht, hq'])
      apply Ideal.subset_span
      exact List.mem_map.mpr ⟨q, hq, rfl⟩
    · apply Ideal.span_le.mpr
      intro r hr
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hr
      apply Ideal.subset_span
      refine ⟨q, hprev_mem q ?_, ?_, rfl⟩
      · simpa [lt] using hq
      · rw [ht]
        simp [hq]
  have htarget :
      IsSMulRegular (R ⧸ Ideal.ofList (List.map f lt)) (f j) := by
    rw [← hI]
    exact hcoeff t
  have htop :
      (Ideal.ofList (List.take (k : ℕ) (List.map f js)) : Submodule R R) •
          (⊤ : Submodule R R) = Ideal.ofList (List.take (k : ℕ) (List.map f js)) := by
    rw [Ideal.smul_eq_mul, Ideal.mul_top]
  have htake_map :
      List.map f (List.take (k : ℕ) js) = List.take (k : ℕ) (List.map f js) := by
    have aux (r : ℕ) :
        List.map f (List.take r js) = List.take r (List.map f js) := by
      induction js generalizing r with
      | nil => simp
      | cons a as ih =>
          cases r with
          | zero => simp
          | succ r => simp
    exact aux (k : ℕ)
  rw [htop]
  rw [← htake_map]
  simpa [lt, kk, j] using htarget

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
  have hpoly_ne :
      Ideal.ofList
          (List.ofFn (fun i => MvPolynomial.C (f i) * MvPolynomial.X i)) ≠
        (⊤ : Ideal (MvPolynomial (Fin n) R)) := by
    let ev : MvPolynomial (Fin n) R →+* R :=
      MvPolynomial.eval₂Hom (RingHom.id R) (fun _ => 0)
    have hker :
        Ideal.ofList
            (List.ofFn (fun i => MvPolynomial.C (f i) * MvPolynomial.X i)) ≤
          RingHom.ker ev := by
      apply Ideal.span_le.mpr
      intro p hp
      have hp' : p ∈ List.map
          (fun i : Fin n => MvPolynomial.C (f i) * MvPolynomial.X i)
          (List.finRange n) := by
        simpa [List.ofFn_eq_map] using hp
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hp'
      simp [ev]
    intro htop
    have h1 : (1 : MvPolynomial (Fin n) R) ∈
        Ideal.ofList
          (List.ofFn (fun i => MvPolynomial.C (f i) * MvPolynomial.X i)) := by
      rw [htop]
      simp
    have hzero := hker h1
    have hzero' : (1 : R) = 0 := by
      simpa [ev] using hzero
    apply hnotunit
    apply le_antisymm le_top
    intro r hr
    rw [← mul_one r, hzero', mul_zero]
    exact Ideal.zero_mem _
  have ideal_sublist : ∀ {ys : List R}, ys.Sublist (List.ofFn f) →
      Ideal.ofList ys ≤ Ideal.ofList (List.ofFn f) := by
    intro ys hys
    apply Ideal.span_le.mpr
    intro r hr
    apply Ideal.subset_span
    exact hys.subset hr
  have regular_of_weak_of_ne_top : ∀ (ys : List R),
      RingTheory.Sequence.IsWeaklyRegular R ys →
        Ideal.ofList ys ≠ (⊤ : Ideal R) →
          RingTheory.Sequence.IsRegular R ys := by
    intro ys hweak hne
    apply (RingTheory.Sequence.isRegular_iff R ys).mpr
    refine ⟨hweak, ?_⟩
    intro htop
    apply hne
    rw [Ideal.smul_eq_mul, Ideal.mul_top] at htop
    exact htop.symm
  have regular_prefix {xs zs : List R}
      (hreg : RingTheory.Sequence.IsRegular R (xs ++ zs)) :
      RingTheory.Sequence.IsRegular R xs := by
    rw [RingTheory.Sequence.isRegular_iff] at hreg ⊢
    refine ⟨(RingTheory.Sequence.isWeaklyRegular_append_iff' R xs zs).mp hreg.1 |>.1, ?_⟩
    intro htop
    apply hreg.2
    rw [Ideal.smul_eq_mul, Ideal.mul_top] at htop
    rw [Ideal.smul_eq_mul, Ideal.mul_top, Ideal.ofList_append]
    rw [← htop]
    simp
  have perm_move : ∀ (a : R) (ys zs : List R),
      (a :: ys ++ zs).Perm (ys ++ a :: zs) := by
    intro a ys zs
    exact List.perm_cons_append_cons a (List.Perm.refl (ys ++ zs))
  have sublist_perm_append : ∀ {ys xs : List R}, ys.Sublist xs →
      ∃ zs, xs.Perm (ys ++ zs) := by
    intro ys xs
    induction xs generalizing ys with
    | nil =>
        intro hys
        have hnil : ys = [] := List.eq_nil_of_sublist_nil hys
        subst ys
        exact ⟨[], List.Perm.refl _⟩
    | cons a xs ih =>
        intro hys
        cases ys with
        | nil => exact ⟨a :: xs, by simp⟩
        | cons b ys =>
            rcases (List.cons_sublist_cons').mp hys with hskip | ⟨hba, htail⟩
            · obtain ⟨zs, hzs⟩ := ih hskip
              refine ⟨a :: zs, ?_⟩
              exact (List.Perm.cons a hzs).trans (perm_move a (b :: ys) zs)
            · subst b
              obtain ⟨zs, hzs⟩ := ih htail
              exact ⟨zs, List.Perm.cons a hzs⟩
  have swap_smulRegular : ∀ {M : Type u} [AddCommGroup M] [Module R M] (a b : R),
      IsSMulRegular M a → IsSMulRegular M b →
        IsSMulRegular (QuotSMulTop b M) a →
          IsSMulRegular (QuotSMulTop a M) b := by
    intro M _ _ a b ha hb hab
    rw [isSMulRegular_iff_right_eq_zero_of_smul]
    intro x hx
    induction x using Submodule.Quotient.induction_on with
    | _ x =>
        have hmem : b • x ∈ a • (⊤ : Submodule R M) := by
          exact (Submodule.Quotient.mk_eq_zero _).mp (by simpa using hx)
        obtain ⟨y, _, hy⟩ :=
          (Submodule.mem_smul_pointwise_iff_exists (b • x) a
            (⊤ : Submodule R M)).mp hmem
        have hay : a • (Submodule.Quotient.mk y : QuotSMulTop b M) = 0 := by
          change (Submodule.Quotient.mk (a • y) : QuotSMulTop b M) = 0
          rw [hy, Submodule.Quotient.mk_eq_zero]
          exact (Submodule.mem_smul_pointwise_iff_exists _ _ _).mpr
            ⟨x, Submodule.mem_top, rfl⟩
        have hy0 : (Submodule.Quotient.mk y : QuotSMulTop b M) = 0 := by
          apply hab
          simpa only [smul_zero] using hay
        obtain ⟨z, _, hz⟩ :=
          (Submodule.mem_smul_pointwise_iff_exists y b
            (⊤ : Submodule R M)).mp
            ((Submodule.Quotient.mk_eq_zero _).mp hy0)
        have hcancel : x = a • z := by
          apply hb
          change b • x = b • (a • z)
          calc
            b • x = a • y := hy.symm
            _ = a • (b • z) := by rw [← hz]
            _ = b • (a • z) := by rw [smul_comm]
        rw [hcancel, Submodule.Quotient.mk_eq_zero]
        exact (Submodule.mem_smul_pointwise_iff_exists _ _ _).mpr
          ⟨z, Submodule.mem_top, rfl⟩
  have swap_regular_tail : ∀ {M : Type u} [AddCommGroup M] [Module R M]
      (a b : R) (rs : List R),
      IsSMulRegular M a → IsSMulRegular M b →
        IsSMulRegular (QuotSMulTop b M) a →
          RingTheory.Sequence.IsRegular
            (QuotSMulTop a (QuotSMulTop b M)) rs →
            RingTheory.Sequence.IsRegular M (a :: b :: rs) := by
    intro M _ _ a b rs ha hb hab hrest
    have hba : IsSMulRegular (QuotSMulTop a M) b :=
      swap_smulRegular (M := M) a b ha hb hab
    have hrest' :
        RingTheory.Sequence.IsRegular
          (QuotSMulTop b (QuotSMulTop a M)) rs := by
      exact ((regular_sequence_quot_smul_comm b a).isRegular_congr rs).mp hrest
    apply (RingTheory.Sequence.isRegular_cons_iff M a (b :: rs)).mpr
    refine ⟨ha, ?_⟩
    exact (RingTheory.Sequence.isRegular_cons_iff
      (QuotSMulTop a M) b rs).mpr ⟨hba, hrest'⟩
  have sublist_skip : ∀ (a : R) {xs ys : List R}, xs.Sublist ys →
      xs.Sublist (a :: ys) := by
    intro a xs ys h
    exact List.Sublist.cons a h
  have perm_preserves_all_sublist_regular : ∀ {M : Type u}
      [AddCommGroup M] [Module R M] {rs rs' : List R},
      (∀ ys, ys.Sublist rs → RingTheory.Sequence.IsRegular M ys) →
        rs.Perm rs' →
          ∀ ys, ys.Sublist rs' → RingTheory.Sequence.IsRegular M ys := by
    intro M _ _ rs rs' hsub hperm
    revert hsub
    induction hperm generalizing M with
    | nil =>
        intro hsub ys hys
        have hnil : ys = [] := List.eq_nil_of_sublist_nil hys
        subst ys
        exact hsub [] (by simp)
    | cons a h ih =>
        intro hsub ys hys
        cases ys with
        | nil => exact hsub [] (by simp)
        | cons b ys =>
            rcases (List.cons_sublist_cons').mp hys with hskip | ⟨hba, htail⟩
            ·
              exact ih (fun zs hzs => hsub zs (sublist_skip a hzs))
                (b :: ys) hskip
            · subst b
              have ha : IsSMulRegular M a :=
                ((RingTheory.Sequence.isRegular_cons_iff M a []).mp
                  (hsub [a] (by simp))).1
              exact (RingTheory.Sequence.isRegular_cons_iff M a ys).mpr
                ⟨ha, ih (M := QuotSMulTop a M)
                  (fun zs hzs =>
                    ((RingTheory.Sequence.isRegular_cons_iff M a zs).mp
                      (hsub (a :: zs) (List.Sublist.cons_cons a hzs))).2)
                  ys htail⟩
    | swap a b rs =>
        intro hsub ys hys
        have ha : IsSMulRegular M a :=
          ((RingTheory.Sequence.isRegular_cons_iff M a []).mp
            (hsub [a] (by simp))).1
        have hdrop : ∀ {tail : List R}, tail.Sublist (b :: rs) →
            RingTheory.Sequence.IsRegular M (a :: tail) := by
          intro tail htail0
          cases tail with
          | nil => exact hsub [a] (by simp)
          | cons c tail =>
              rcases (List.cons_sublist_cons').mp htail0 with hskip | ⟨hcb, htail⟩
              · exact hsub (a :: c :: tail)
                  (List.Sublist.cons b (List.Sublist.cons_cons a hskip))
              · subst c
                have hreg := hsub (b :: a :: tail)
                  (List.Sublist.cons_cons b
                    (List.Sublist.cons_cons a htail))
                have hreg₁ :=
                  (RingTheory.Sequence.isRegular_cons_iff M b (a :: tail)).mp hreg
                have hreg₂ :=
                  (RingTheory.Sequence.isRegular_cons_iff
                    (QuotSMulTop b M) a tail).mp hreg₁.2
                exact swap_regular_tail (M := M) a b tail ha hreg₁.1
                  hreg₂.1 hreg₂.2
        cases ys with
        | nil => exact hsub [] (by simp)
        | cons c ys =>
            rcases (List.cons_sublist_cons').mp hys with hskip | ⟨hca, htail⟩
            · rcases (List.cons_sublist_cons').mp hskip with hskipb | ⟨hcb, htailb⟩
              · exact hsub (c :: ys)
                  (sublist_skip b (sublist_skip a hskipb))
              · subst c
                exact hsub (b :: ys)
                  (List.Sublist.cons_cons b (sublist_skip a htailb))
            · subst c
              exact hdrop htail
    | trans h₁ h₂ ih₁ ih₂ =>
        intro hsub ys hys
        exact ih₂ (ih₁ hsub) ys hys
  tfae_have 2 → 3 := by
    intro h
    have hw := polynomial_weaklyRegular_of_sublist n f (fun ys hys =>
      ((RingTheory.Sequence.isRegular_iff R ys).mp (h ys hys)).1)
    apply (RingTheory.Sequence.isRegular_iff _ _).mpr
    refine ⟨hw, ?_⟩
    intro htop
    apply hpoly_ne
    rw [Ideal.smul_eq_mul, Ideal.mul_top] at htop
    exact htop.symm
  tfae_have 3 → 2 := by
    intro h ys hys
    have hwpoly := (RingTheory.Sequence.isRegular_iff _ _).mp h |>.1
    have hw := sublist_weaklyRegular_of_polynomial_weaklyRegular n f hwpoly ys hys
    apply regular_of_weak_of_ne_top ys hw
    intro htop
    apply hnotunit
    apply le_antisymm le_top
    rw [← htop]
    exact ideal_sublist hys
  tfae_have 1 → 2 := by
    intro h ys hys
    obtain ⟨zs, hperm⟩ := sublist_perm_append hys
    exact regular_prefix (h (ys ++ zs) hperm)
  tfae_have 2 → 1 := by
    intro h ys hperm
    exact perm_preserves_all_sublist_regular h hperm ys (List.Sublist.refl _)
  tfae_finish

end

end Formalization.Books.Algebra.Unit68
