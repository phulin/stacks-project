import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.GroupWithZero.NonZeroDivisors
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.ObjectProperty.Extensions
import Mathlib.RingTheory.MvPolynomial
import Mathlib.RingTheory.Ideal.Oka
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Noetherian.OfPrime
import Mathlib.RingTheory.PrincipalIdealDomainOfPrime
import Mathlib.RingTheory.Spectrum.Prime.Noetherian
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.SetTheory.Cardinal.Basic

namespace Formalization.Books.Algebra.Unit28

open Set
open CategoryTheory
open CategoryTheory.Limits
open TopologicalSpace
open scoped ZeroObject

universe u

noncomputable section

/-! ## Colon ideals and Oka families -/

/-- The colon of an ideal by a single element, expressed using the canonical ideal colon. -/
abbrev idealColonByElement {R : Type u} [CommRing R] (I : Ideal R) (a : R) : Ideal R :=
  I.colon (Ideal.span ({a} : Set R))

/-- The colon of an ideal by another ideal, expressed using the canonical ideal colon. -/
abbrev idealColonByIdeal {R : Type u} [CommRing R] (I J : Ideal R) : Ideal R :=
  I.colon (J : Set R)

theorem mem_idealColonByElement {R : Type u} [CommRing R] {I : Ideal R} {a x : R} :
    x ∈ idealColonByElement I a ↔ x * a ∈ I := by
  simp [idealColonByElement]

theorem mem_idealColonByIdeal {R : Type u} [CommRing R] {I J : Ideal R} {x : R} :
    x ∈ idealColonByIdeal I J ↔ ∀ y ∈ J, x * y ∈ I := by
  simp [idealColonByIdeal, Submodule.mem_colon, smul_eq_mul]

/-- If `I ≤ J` and `J` is principal, then `I = J (I : J)`. -/
theorem ideal_eq_principal_mul_colon {R : Type u} [CommRing R]
    {I J : Ideal R} (hIJ : I ≤ J) (hJ : J.IsPrincipal) :
    I = J * idealColonByIdeal I J := by
  obtain ⟨a, ha⟩ := hJ.principal
  rw [ha]
  ext x
  constructor
  · intro hx
    have hxJ : x ∈ R ∙ a := by
      rw [← ha]
      exact hIJ hx
    obtain ⟨c, hcx⟩ := (Ideal.mem_span_singleton').mp hxJ
    apply Ideal.mem_span_singleton_mul.mpr
    refine ⟨c, ?_, ?_⟩
    · exact (mem_idealColonByElement (I := I) (a := a) (x := c)).mpr
        (hcx ▸ hx)
    · simpa [mul_comm] using hcx
  · intro hx
    obtain ⟨c, hc, hcx⟩ := (Ideal.mem_span_singleton_mul).mp hx
    rw [← hcx]
    simpa [mul_comm] using
      (mem_idealColonByElement (I := I) (a := a) (x := c)).mp hc

/-- A set of ideals satisfying the Oka-family condition. -/
abbrev OkaFamily {R : Type u} [CommRing R] (F : Set (Ideal R)) : Prop :=
  Ideal.IsOka (fun I => I ∈ F)

/-! ## Examples of Oka families -/

def idealsMeeting {R : Type u} [CommRing R] (S : Submonoid R) : Set (Ideal R) :=
  {I : Ideal R | ((I : Set R) ∩ (S : Set R)).Nonempty}

theorem idealsMeeting_isOka {R : Type u} [CommRing R] (S : Submonoid R) :
    OkaFamily (idealsMeeting S) := by
  change Ideal.IsOka (fun I : Ideal R => ((I : Set R) ∩ (S : Set R)).Nonempty)
  refine { top := ?_, oka := ?_ }
  · exact ⟨1, by simp, S.one_mem⟩
  · intro I a hsup hcolon
    obtain ⟨s, hsI, hsS⟩ := hsup
    obtain ⟨t, htI, htS⟩ := hcolon
    obtain ⟨i, hi, j, hj, hs⟩ := Submodule.mem_sup.mp hsI
    obtain ⟨r, hr⟩ := (Ideal.mem_span_singleton').mp hj
    refine ⟨s * t, ?_, S.mul_mem hsS htS⟩
    rw [← hs, add_mul]
    apply I.add_mem
    · exact I.mul_mem_right t hi
    · rw [← hr, mul_assoc, mul_comm a t]
      exact I.mul_mem_left r
        ((mem_idealColonByElement (I := I) (a := a) (x := t)).mp htI)

theorem ideal_eq_span_mul_colon_generators {R : Type u} [CommRing R]
    {I : Ideal R} {a : R} {n m : ℕ} (a₁ : Fin n → R) (b₁ : Fin m → R)
    (hcolon : Ideal.span (Set.range a₁) = idealColonByElement I a)
    (hsup : Ideal.span (insert a (Set.range b₁)) =
      I ⊔ Ideal.span ({a} : Set R))
    (hb : ∀ i, b₁ i ∈ I) :
    I = Ideal.span (Set.range (fun i => a * a₁ i) ∪ Set.range b₁) := by
  apply le_antisymm
  · intro x hx
    have hx' : x ∈ Ideal.span (insert a (Set.range b₁)) := by
      rw [hsup]
      exact (show I ≤ I ⊔ Ideal.span ({a} : Set R) from le_sup_left) hx
    obtain ⟨r, z, hz, hzx⟩ := Ideal.mem_span_insert.mp hx'
    have hzI : z ∈ I := by
      apply (Ideal.span_le.2 ?_) hz
      rintro _ ⟨i, rfl⟩
      exact hb i
    have hra : r * a ∈ I := by
      have hsub := I.sub_mem hx hzI
      rw [hzx] at hsub
      simpa using hsub
    have hrspan : r ∈ Ideal.span (Set.range a₁) := by
      rw [hcolon]
      exact (mem_idealColonByElement (I := I) (a := a) (x := r)).mpr hra
    obtain ⟨c, hc⟩ := (Ideal.mem_span_range_iff_exists_fun).mp hrspan
    let K : Ideal R := Ideal.span (Set.range (fun i => a * a₁ i) ∪ Set.range b₁)
    have hraK : r * a ∈ K := by
      rw [← hc, Finset.sum_mul]
      exact K.sum_mem fun i hi => by
        simpa [mul_assoc, mul_comm, mul_left_comm] using
          K.mul_mem_left (c i)
            (Ideal.subset_span (Or.inl (Set.mem_range_self i)))
    have hzK : z ∈ K := by
      apply (Ideal.span_le.2 ?_) hz
      rintro _ ⟨i, rfl⟩
      exact Ideal.subset_span (Or.inr (Set.mem_range_self i))
    rw [hzx]
    exact K.add_mem hraK hzK
  · rw [Ideal.span_union]
    apply sup_le
    · refine Ideal.span_le.2 ?_
      rintro _ ⟨i, rfl⟩
      have hai : a₁ i ∈ idealColonByElement I a := by
        rw [← hcolon]
        exact Ideal.mem_span_range_self
      simpa [mul_comm] using
        (mem_idealColonByElement (I := I) (a := a) (x := a₁ i)).mp hai
    · refine Ideal.span_le.2 ?_
      rintro _ ⟨i, rfl⟩
      exact hb i

def finitelyGeneratedIdeals {R : Type u} [CommRing R] : Set (Ideal R) :=
  {I : Ideal R | I.FG}

theorem finitelyGeneratedIdeals_isOka {R : Type u} [CommRing R] :
    OkaFamily (finitelyGeneratedIdeals (R := R)) := by
  change Ideal.IsOka (fun I : Ideal R => I.FG)
  exact Ideal.isOka_fg

theorem idealColonByElement_eq_adjoin_colon {R : Type u} [CommRing R]
    (I : Ideal R) (a : R) :
    idealColonByElement I a =
      idealColonByIdeal I (I ⊔ Ideal.span ({a} : Set R)) := by
  ext x
  constructor
  · intro hx
    apply (mem_idealColonByIdeal (I := I)
      (J := I ⊔ Ideal.span ({a} : Set R)) (x := x)).mpr
    intro y hy
    obtain ⟨i, hi, z, hz, hyz⟩ := Submodule.mem_sup.mp hy
    obtain ⟨r, hr⟩ := (Ideal.mem_span_singleton').mp hz
    rw [← hyz, mul_add]
    apply I.add_mem
    · exact I.mul_mem_left x hi
    · rw [← hr, ← mul_assoc, mul_comm x r, mul_assoc]
      exact I.mul_mem_left r
        ((mem_idealColonByElement (I := I) (a := a) (x := x)).mp hx)
  · intro hx
    apply (mem_idealColonByElement (I := I) (a := a) (x := x)).mpr
    apply (mem_idealColonByIdeal (I := I)
      (J := I ⊔ Ideal.span ({a} : Set R)) (x := x)).mp hx
    exact (show Ideal.span ({a} : Set R) ≤ I ⊔ Ideal.span ({a} : Set R) from
      le_sup_right) (Ideal.mem_span_singleton_self a)

def principalIdeals {R : Type u} [CommRing R] : Set (Ideal R) :=
  {I : Ideal R | I.IsPrincipal}

theorem principalIdeals_isOka {R : Type u} [CommRing R] :
    OkaFamily (principalIdeals (R := R)) := by
  change Ideal.IsOka (fun I : Ideal R => I.IsPrincipal)
  exact Ideal.isOka_isPrincipal

def generatedByAtMost {R : Type u} [CommRing R] (κ : Cardinal.{u}) : Set (Ideal R) :=
  {I : Ideal R | ∃ s : Set R, Cardinal.mk s ≤ κ ∧ Ideal.span s = I}

theorem generatedByAtMost_isOka {R : Type u} [CommRing R]
    (κ : Cardinal.{u}) (hκ : Cardinal.aleph0 ≤ κ) :
    OkaFamily (generatedByAtMost (R := R) κ) := by
  sorry

/-! ## Oka families from module properties -/

abbrev ModuleProperty (A : Type u) [CommRing A] :=
  ObjectProperty (ModuleCat.{u} A)

def moduleQuotientIdeals {A : Type u} [CommRing A] (P : ModuleProperty A) : Set (Ideal A) :=
  {I : Ideal A | P (ModuleCat.of A (A ⧸ I))}

def quotientColonMultiplicationMap {A : Type u} [CommRing A]
    (I : Ideal A) (a : A) :
    (A ⧸ idealColonByElement I a) →ₗ[A] (A ⧸ I) :=
  (idealColonByElement I a).liftQ
    ((Ideal.Quotient.mkₐ A I).toLinearMap.comp (LinearMap.mulLeft A a))
    (by
      intro x hx
      change Ideal.Quotient.mk I (a * x) = 0
      rw [Ideal.Quotient.eq_zero_iff_mem]
      simpa [mul_comm] using (mem_idealColonByElement (I := I) (a := a) (x := x)).mp hx)

@[simp] theorem quotientColonMultiplicationMap_mk {A : Type u} [CommRing A]
    (I : Ideal A) (a x : A) :
    quotientColonMultiplicationMap I a (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (a * x) := by
  rfl

def quotientAdjoinMap {A : Type u} [CommRing A]
    (I : Ideal A) (a : A) :
    (A ⧸ I) →ₗ[A] (A ⧸ (I ⊔ Ideal.span ({a} : Set A))) :=
  I.liftQ
    ((Ideal.Quotient.mkₐ A (I ⊔ Ideal.span ({a} : Set A))).toLinearMap)
    (by
      intro x hx
      change Ideal.Quotient.mk (I ⊔ Ideal.span ({a} : Set A)) x = 0
      rw [Ideal.Quotient.eq_zero_iff_mem]
      exact (show I ≤ I ⊔ Ideal.span ({a} : Set A) from le_sup_left) hx)

@[simp] theorem quotientAdjoinMap_mk {A : Type u} [CommRing A]
    (I : Ideal A) (a x : A) :
    quotientAdjoinMap I a (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk x := by
  rfl

def idealColonShortComplex {A : Type u} [CommRing A]
    (I : Ideal A) (a : A) : ShortComplex (ModuleCat.{u} A) :=
  ShortComplex.moduleCatMk
    (quotientColonMultiplicationMap I a)
    (quotientAdjoinMap I a)
    (by
      apply LinearMap.ext
      intro x
      induction x using Submodule.Quotient.induction_on with
      | _ x =>
        rw [LinearMap.comp_apply, quotientColonMultiplicationMap_mk,
          quotientAdjoinMap_mk]
        change Ideal.Quotient.mk (I ⊔ Ideal.span ({a} : Set A)) (a * x) = 0
        rw [Ideal.Quotient.eq_zero_iff_mem]
        simpa [mul_comm, smul_eq_mul] using
          (I ⊔ Ideal.span ({a} : Set A)).smul_mem x
            (Submodule.mem_sup_right (Ideal.mem_span_singleton_self a)))

theorem idealColonShortComplex_shortExact {A : Type u} [CommRing A]
    (I : Ideal A) (a : A) :
    (idealColonShortComplex I a).ShortExact := by
  refine ModuleCat.shortComplex_shortExact (idealColonShortComplex I a) ?_ ?_ ?_
  · change Function.Exact (quotientColonMultiplicationMap I a)
      (quotientAdjoinMap I a)
    apply Function.Exact.of_comp_of_mem_range
    · funext x
      induction x using Submodule.Quotient.induction_on with
      | _ x =>
        rw [Function.comp_apply, quotientColonMultiplicationMap_mk,
          quotientAdjoinMap_mk]
        change Ideal.Quotient.mk (I ⊔ Ideal.span ({a} : Set A)) (a * x) = 0
        rw [Ideal.Quotient.eq_zero_iff_mem]
        simpa [mul_comm, smul_eq_mul] using
          (I ⊔ Ideal.span ({a} : Set A)).smul_mem x
            (Submodule.mem_sup_right (Ideal.mem_span_singleton_self a))
    · intro y hy
      induction y using Submodule.Quotient.induction_on with
      | _ x =>
        rw [quotientAdjoinMap_mk] at hy
        change Ideal.Quotient.mk (I ⊔ Ideal.span ({a} : Set A)) x = 0 at hy
        have hx := (Ideal.Quotient.eq_zero_iff_mem).mp hy
        obtain ⟨i, hi, z, hz, hzx⟩ := Submodule.mem_sup.mp hx
        obtain ⟨r, hr⟩ := (Ideal.mem_span_singleton').mp hz
        refine ⟨Submodule.Quotient.mk r, ?_⟩
        rw [quotientColonMultiplicationMap_mk]
        apply Ideal.Quotient.eq.mpr
        rw [← hzx, ← hr]
        simpa [mul_comm, sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using
          I.neg_mem hi
  · change Function.Injective (quotientColonMultiplicationMap I a)
    intro x y hxy
    induction x using Submodule.Quotient.induction_on with
    | _ x =>
      induction y using Submodule.Quotient.induction_on with
      | _ y =>
        change Submodule.Quotient.mk (a * x) = Submodule.Quotient.mk (a * y) at hxy
        apply (Submodule.Quotient.eq (idealColonByElement I a)).mpr
        apply (mem_idealColonByElement (I := I) (a := a) (x := x - y)).mpr
        simpa [mul_sub, mul_comm] using (Submodule.Quotient.eq I).mp hxy
  · change Function.Surjective (quotientAdjoinMap I a)
    intro y
    induction y using Submodule.Quotient.induction_on with
    | _ x =>
      exact ⟨Submodule.Quotient.mk x, quotientAdjoinMap_mk I a x⟩

theorem moduleQuotientIdeals_isOka {A : Type u} [CommRing A]
    (P : ModuleProperty A)
    [ObjectProperty.IsClosedUnderExtensions P]
    (hP0 : P (0 : ModuleCat.{u} A)) :
    OkaFamily (moduleQuotientIdeals (A := A) P) := by
  change Ideal.IsOka (fun I : Ideal A => P (ModuleCat.of A (A ⧸ I)))
  refine { top := ?_, oka := ?_ }
  · let Q : ModuleCat.{u} A := ModuleCat.of A (A ⧸ (⊤ : Ideal A))
    let S : ShortComplex (ModuleCat.{u} A) :=
      ShortComplex.mk (0 : (0 : ModuleCat.{u} A) ⟶ Q)
        (0 : Q ⟶ (0 : ModuleCat.{u} A)) (by simp)
    have hS : S.ShortExact :=
      { exact := ShortComplex.exact_of_isZero_X₂ S
          (ModuleCat.isZero_of_subsingleton Q)
        mono_f := (isZero_zero _).mono S.f
        epi_g := (isZero_zero _).epi S.g }
    change P Q
    exact P.prop_X₂_of_shortExact hS hP0 hP0
  · intro I a hsup hcolon
    exact P.prop_X₂_of_shortExact
      (idealColonShortComplex_shortExact I a) hcolon hsup

/-! ## Maximal ideals and the converse constructions -/

theorem prime_of_maximal_not_mem {R : Type u} [CommRing R]
    {F : Set (Ideal R)} (hF : OkaFamily F) {I : Ideal R}
    (hI : Maximal (fun J : Ideal R => J ∉ F) I) :
    I.IsPrime := by
  exact hF.isPrime_of_maximal_not hI

theorem prime_of_maximal_disjoint {R : Type u} [CommRing R]
    (S : Submonoid R) {I : Ideal R}
    (hI : Maximal
      (fun J : Ideal R => (J : Set R) ∩ (S : Set R) = ∅) I) :
    I.IsPrime := by
  apply Ideal.isPrime_of_maximally_disjoint I S
  · refine Set.disjoint_left.2 ?_
    intro x hxI hxS
    have hx : x ∈ (I : Set R) ∩ (S : Set R) := ⟨hxI, hxS⟩
    rw [hI.1] at hx
    have hfalse : ¬ x ∈ (∅ : Set R) := by simp
    exact (hfalse hx).elim
  · intro J hIJ hJ
    apply hI.not_prop_of_gt hIJ
    ext x
    constructor
    · intro hx
      exact (Set.disjoint_left.mp hJ hx.1 hx.2).elim
    · intro hx
      have hfalse : ¬ x ∈ (∅ : Set R) := by simp
      exact (hfalse hx).elim

theorem prime_of_maximal_not_finitelyGenerated {R : Type u} [CommRing R]
    {I : Ideal R} (hI : Maximal (fun J : Ideal R => ¬ J.FG) I) :
    I.IsPrime := by
  exact Ideal.isOka_fg.isPrime_of_maximal_not hI

theorem finitelyGenerated_of_all_prime_finitelyGenerated {R : Type u} [CommRing R]
    (hP : ∀ P : Ideal R, P.IsPrime → P.FG) (I : Ideal R) : I.FG := by
  let _ : IsNoetherianRing R := IsNoetherianRing.of_prime hP
  exact Ideal.fg_of_isNoetherianRing I

theorem prime_of_maximal_not_principal {R : Type u} [CommRing R]
    {I : Ideal R} (hI : Maximal (fun J : Ideal R => ¬ J.IsPrincipal) I) :
    I.IsPrime := by
  exact Ideal.isOka_isPrincipal.isPrime_of_maximal_not hI

theorem principal_of_all_prime_principal {R : Type u} [CommRing R]
    (hP : ∀ P : Ideal R, P.IsPrime → P.IsPrincipal) (I : Ideal R) :
    I.IsPrincipal := by
  let _ : IsPrincipalIdealRing R := IsPrincipalIdealRing.of_prime hP
  exact IsPrincipalIdealRing.principal I

theorem prime_of_maximal_without_nonZeroDivisor {R : Type u} [CommRing R]
    {I : Ideal R}
    (hI : Maximal (fun J : Ideal R =>
      Disjoint (J : Set R) (nonZeroDivisors R)) I) :
    I.IsPrime := by
  exact Ideal.isPrime_of_maximally_disjoint I (nonZeroDivisors R) hI.1
    (fun J hIJ => hI.not_prop_of_gt hIJ)

theorem isDomain_of_nontrivial_of_nonzero_prime_contains_nonZeroDivisor
    {R : Type u} [CommRing R] [Nontrivial R]
    (h : ∀ P : Ideal R, P.IsPrime → P ≠ ⊥ →
      ∃ x : R, x ∈ P ∧ x ∈ nonZeroDivisors R) :
    IsDomain R := by
  have hdis : Disjoint ((⊥ : Ideal R) : Set R) (nonZeroDivisors R) := by
    refine Set.disjoint_left.2 ?_
    intro x hxbot hxreg
    have hxzero : x = 0 := by simpa using hxbot
    exact (nonZeroDivisors.ne_zero hxreg) hxzero
  obtain ⟨P, hP, _, hPdis⟩ :=
    Ideal.exists_le_prime_disjoint (I := (⊥ : Ideal R))
      (nonZeroDivisors R) hdis
  have hPbot : P = ⊥ := by
    by_contra hPbot
    obtain ⟨x, hxP, hxreg⟩ := h P hP hPbot
    exact Set.disjoint_left.mp hPdis hxP hxreg
  subst P
  letI : (⊥ : Ideal R).IsPrime := hP
  exact IsDomain.of_bot_isPrime R

/-! ## The cardinality variant and its example -/

theorem prime_of_maximal_not_generatedByAtMost {R : Type u} [CommRing R]
    (κ : Cardinal.{u}) (hκ : Cardinal.aleph0 ≤ κ) {I : Ideal R}
    (hI : Maximal (fun J : Ideal R =>
      J ∉ generatedByAtMost (R := R) κ) I) :
    I.IsPrime := by
  exact prime_of_maximal_not_mem (generatedByAtMost_isOka (R := R) κ hκ) hI

abbrev okaCounterexampleVariables (T : Type u) := Sum ℕ (T × ℕ)

def okaCounterexampleRelationSet (k T : Type u) [Field k] :
    Set (MvPolynomial (okaCounterexampleVariables T) k) :=
  Set.range (fun n : ℕ =>
      (MvPolynomial.X (Sum.inl (n + 1)) :
        MvPolynomial (okaCounterexampleVariables T) k) ^ 2) ∪
    Set.range (fun p : T × ℕ =>
      (MvPolynomial.X (Sum.inr p) :
        MvPolynomial (okaCounterexampleVariables T) k) ^ 2) ∪
    Set.range (fun p : T × ℕ =>
      (MvPolynomial.X (Sum.inl (p.2 + 1)) :
          MvPolynomial (okaCounterexampleVariables T) k) *
        MvPolynomial.X (Sum.inr (p.1, p.2 + 1)) -
        MvPolynomial.X (Sum.inr p))

abbrev okaCounterexampleRelationIdeal (k T : Type u) [Field k] :
    Ideal (MvPolynomial (okaCounterexampleVariables T) k) :=
  Ideal.span (okaCounterexampleRelationSet k T)

abbrev okaCounterexampleRing (k T : Type u) [Field k] :=
  MvPolynomial (okaCounterexampleVariables T) k ⧸
    okaCounterexampleRelationIdeal k T

def okaCounterexampleX (k T : Type u) [Field k] (n : ℕ) :
    okaCounterexampleRing k T :=
  Ideal.Quotient.mk (okaCounterexampleRelationIdeal k T)
    (MvPolynomial.X (Sum.inl (n + 1)))

def okaCounterexampleZ (k T : Type u) [Field k] (t : T) (n : ℕ) :
    okaCounterexampleRing k T :=
  Ideal.Quotient.mk (okaCounterexampleRelationIdeal k T)
    (MvPolynomial.X (Sum.inr (t, n)))

def okaCounterexampleMaximalIdeal (k T : Type u) [Field k] :
    Ideal (okaCounterexampleRing k T) :=
  Ideal.span (Set.range (okaCounterexampleX k T))

def okaCounterexampleZIdeal (k T : Type u) [Field k] :
    Ideal (okaCounterexampleRing k T) :=
  Ideal.span (Set.range (fun p : T × ℕ => okaCounterexampleZ k T p.1 p.2))

theorem okaCounterexample_spec {k T : Type u} [Field k]
    (hT : Cardinal.aleph0 < Cardinal.mk T) :
    IsLocalRing (okaCounterexampleRing k T) ∧
      (okaCounterexampleMaximalIdeal k T).IsPrime ∧
      (∀ P : Ideal (okaCounterexampleRing k T), P.IsPrime →
        P = okaCounterexampleMaximalIdeal k T) ∧
      ¬ generatedByAtMost (R := okaCounterexampleRing k T)
          Cardinal.aleph0 (okaCounterexampleZIdeal k T) := by
  sorry

/-! ## The Noetherian spectrum example -/

/- The source's correspondence between closed subsets of the spectrum and radical ideals is
   provided by the canonical `PrimeSpectrum.isClosed_iff_zeroLocus_radical_ideal` and
   `PrimeSpectrum.vanishingIdeal_zeroLocus_eq_radical` declarations. -/

def RadicalIdealACC {R : Type u} [CommRing R] : Prop :=
  ∀ C : Set (Ideal R), C.Nonempty →
    (∀ I ∈ C, I.IsRadical) →
    IsChain (· ≤ ·) C →
    ∃ M ∈ C, ∀ I ∈ C, I ≤ M

def radicalOfFiniteGeneratedIdeals {R : Type u} [CommRing R] : Set (Ideal R) :=
  {I : Ideal R | ∃ n : ℕ, ∃ f : Fin n → R,
    I.radical = (Ideal.span (Set.range f)).radical}

theorem radical_eq_radical_adjoin_mul_colon {R : Type u} [CommRing R]
    (I : Ideal R) (a : R) :
    I.radical =
      ((I ⊔ Ideal.span ({a} : Set R)) * idealColonByElement I a).radical := by
  apply le_antisymm
  · intro x hx
    rw [Ideal.mem_radical_iff] at hx ⊢
    obtain ⟨n, hn⟩ := hx
    refine ⟨n * 2, ?_⟩
    rw [pow_mul]
    simpa [pow_two] using Ideal.mul_mem_mul
      ((show I ≤ I ⊔ Ideal.span ({a} : Set R) from le_sup_left) hn)
      ((mem_idealColonByElement (I := I) (a := a) (x := x ^ n)).mpr
        (I.mul_mem_right a hn))
  · apply Ideal.radical_mono
    apply Ideal.mul_le.mpr
    intro x hx y hy
    obtain ⟨i, hi, z, hz, hxz⟩ := Submodule.mem_sup.mp hx
    obtain ⟨r, hr⟩ := (Ideal.mem_span_singleton').mp hz
    rw [← hxz, add_mul]
    apply I.add_mem
    · exact I.mul_mem_right y hi
    · rw [← hr, mul_assoc, mul_comm a y]
      exact I.mul_mem_left r
        ((mem_idealColonByElement (I := I) (a := a) (x := y)).mp hy)

theorem radicalOfFiniteGeneratedIdeals_isOka {R : Type u} [CommRing R] :
    OkaFamily (radicalOfFiniteGeneratedIdeals (R := R)) := by
  change Ideal.IsOka (fun I : Ideal R => ∃ n : ℕ, ∃ f : Fin n → R,
    I.radical = (Ideal.span (Set.range f)).radical)
  refine { top := ?_, oka := ?_ }
  · exact ⟨1, fun _ => 1, by simp⟩
  · intro I a hsup hcolon
    obtain ⟨n, f, hf⟩ := hsup
    obtain ⟨m, g, hg⟩ := hcolon
    refine ⟨n * m, fun p => f p.1 * g p.2, ?_⟩
    rw [radical_eq_radical_adjoin_mul_colon, Ideal.radical_mul, hf, hg,
      ← Ideal.radical_mul, Ideal.span_mul_span']
    congr 1
    ext x
    constructor
    · rintro ⟨y, hy, z, hz, rfl⟩
      rcases hy with ⟨i, rfl⟩
      rcases hz with ⟨j, rfl⟩
      exact ⟨⟨i, j⟩, rfl⟩
    · rintro ⟨⟨i, j⟩, rfl⟩
      exact ⟨f i, ⟨i, rfl⟩, g j, ⟨j, rfl⟩, rfl⟩

theorem sSup_not_radicalOfFiniteGeneratedIdeals {R : Type u} [CommRing R]
    (C : Set (Ideal R)) (hC : C.Nonempty) (hchain : IsChain (· ≤ ·) C)
    (hCnot : ∀ I ∈ C, I ∉ radicalOfFiniteGeneratedIdeals (R := R)) :
    sSup C ∉ radicalOfFiniteGeneratedIdeals (R := R) := by
  sorry

theorem exists_maximal_not_radicalOfFiniteGeneratedIdeals {R : Type u} [CommRing R]
    (h : ∃ I : Ideal R, I ∉ radicalOfFiniteGeneratedIdeals (R := R)) :
    ∃ M : Ideal R, Maximal
      (fun I : Ideal R => I ∉ radicalOfFiniteGeneratedIdeals (R := R)) M := by
  sorry

theorem primeSpectrum_noetherian_iff_radicalIdealACC {R : Type u} [CommRing R] :
    NoetherianSpace (PrimeSpectrum R) ↔ RadicalIdealACC (R := R) := by
  sorry

theorem radicalIdealACC_iff_radicalOfFiniteGenerated {R : Type u} [CommRing R] :
    RadicalIdealACC (R := R) ↔
      ∀ I : Ideal R, I.IsRadical →
        I ∈ radicalOfFiniteGeneratedIdeals (R := R) := by
  sorry

theorem primeSpectrum_noetherian_iff_prime_radical_finite {R : Type u} [CommRing R] :
    NoetherianSpace (PrimeSpectrum R) ↔
      ∀ P : Ideal R, P.IsPrime →
        ∃ n : ℕ, ∃ f : Fin n → R,
          P = (Ideal.span (Set.range f)).radical := by
  sorry

end

end Formalization.Books.Algebra.Unit28
