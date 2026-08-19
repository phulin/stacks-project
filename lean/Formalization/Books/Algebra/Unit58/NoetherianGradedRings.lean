import Formalization.Books.Algebra.Unit55.KGroups
import Formalization.Books.Algebra.Unit56.GradedRings
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.RingTheory.GradedAlgebra.FiniteType
import Mathlib.RingTheory.GradedAlgebra.Noetherian
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.Polynomial.Basic

/-!
# Commutative Algebra, Chapter 58: Noetherian graded rings

The graded-ring and graded-module data are the canonical wrappers from Chapter
56.  The numerical-polynomial interface records eventual agreement on the
integer line, and Hilbert functions take values in the set-sized `KPrimeZero`
model from Chapter 55.
-/

namespace Formalization.Books.Algebra.Unit58

open Formalization.Books.Algebra.Unit55
open Formalization.Books.Algebra.Unit56
open scoped BigOperators

universe u v

noncomputable section

variable {S : Type u} [CommRing S]
variable {M : Type v} [AddCommGroup M] [Module S M]

/-! ## Noetherian graded rings -/

/- The source's `S₊` is the irrelevant ideal from Chapter 56. -/

theorem sPlus_generated_iff
    {ι : Type v} (G : GradedRingData S) (f : ι → S)
    (hf : ∀ i, IsHomogeneousElement G (f i) ∧ f i ∈ irrelevantIdeal G) :
    (Algebra.adjoin (degreeZeroSubring G) (Set.range f) =
        (⊤ : Subalgebra (degreeZeroSubring G) S)) ↔
        Ideal.span (Set.range f) = irrelevantIdeal G := by
  let I : Ideal S := Ideal.span (Set.range f)
  let p₀ : S →+* S := GradedRing.projZeroRingHom G.component
  have hf₀ : ∀ i, p₀ (f i) = 0 := by
    intro i
    change GradedRing.proj G.component 0 (f i) = 0
    exact (HomogeneousIdeal.mem_irrelevant_iff (𝒜 := G.component) (f i)).mp (hf i).2
  have hI₀ : I ≤ RingHom.ker p₀ := by
    change Ideal.span (Set.range f) ≤ RingHom.ker p₀
    refine Ideal.span_le.mpr ?_
    rintro x ⟨i, rfl⟩
    exact hf₀ i
  have hP :
      ∃ P : Subalgebra (degreeZeroSubring G) S,
        (∀ i, f i ∈ P) ∧
          (∀ x, x ∈ irrelevantIdeal G → x ∈ P → ∃ y ∈ I, x = y) := by
    let P : Subalgebra (degreeZeroSubring G) S :=
      { carrier := {x | ∃ y, y ∈ I ∧ ∃ z : degreeZeroSubring G, x = y + (z : S)}
        add_mem' := by
          rintro x y ⟨x₁, hx₁, z, rfl⟩ ⟨y₁, hy₁, w, rfl⟩
          refine ⟨x₁ + y₁, I.add_mem hx₁ hy₁, z + w, ?_⟩
          simp only [Subring.coe_add]
          abel
        mul_mem' := by
          rintro x y ⟨x₁, hx₁, z, rfl⟩ ⟨y₁, hy₁, w, rfl⟩
          have hxy : x₁ * y₁ ∈ I := by
            change x₁ • y₁ ∈ I
            exact I.smul_mem x₁ hy₁
          have hxw : x₁ * (w : S) ∈ I := by
            simpa [mul_comm] using I.smul_mem (w : S) hx₁
          have hzy : (z : S) * y₁ ∈ I := by
            exact I.smul_mem (z : S) hy₁
          refine ⟨x₁ * y₁ + x₁ * (w : S) + (z : S) * y₁,
            I.add_mem (I.add_mem hxy hxw) hzy, z * w, ?_⟩
          simp only [Subring.coe_mul]
          ring
        algebraMap_mem' := by
          intro z
          exact ⟨0, I.zero_mem, z, by
            rw [Algebra.algebraMap_ofSubring]
            simp⟩ }
    refine ⟨P, ?_, ?_⟩
    · intro i
      exact ⟨f i, Ideal.subset_span ⟨i, rfl⟩, 0, by simp⟩
    · intro x hxIrrelevant hxP
      rcases hxP with ⟨y, hy, z, hxy⟩
      have hy₀ : p₀ y = 0 := hI₀ hy
      have hxzero : (z : S) = 0 := by
        have hx₀ : p₀ x = 0 := by
          change GradedRing.proj G.component 0 x = 0
          exact (HomogeneousIdeal.mem_irrelevant_iff (𝒜 := G.component) x).mp hxIrrelevant
        have hz₀ : p₀ (z : S) = (z : S) := by
          change (DirectSum.decompose G.component (z : S) 0 : S) = (z : S)
          exact DirectSum.decompose_of_mem_same G.component z.property
        rw [hxy, map_add, hy₀, hz₀] at hx₀
        simpa only [zero_add] using hx₀
      exact ⟨y, hy, by simp [hxy, hxzero]⟩
  constructor
  · intro hgen
    apply le_antisymm
    · change I ≤ irrelevantIdeal G
      change I ≤ RingHom.ker p₀
      exact hI₀
    · intro x hx
      rcases hP with ⟨P, hfP, hPsub⟩
      have hle : Algebra.adjoin (degreeZeroSubring G) (Set.range f) ≤ P :=
        Algebra.adjoin_le (s := Set.range f) (S := P) (by
          rintro y ⟨i, rfl⟩
          exact hfP i)
      have hxP : x ∈ P := hle (by rw [hgen]; trivial)
      rcases hPsub x hx hxP with ⟨y, hy, hxy⟩
      simpa only [hxy] using hy
  · intro hspan
    have hcomp : ∀ n : ℕ, ∀ x : S, x ∈ G.component n →
        x ∈ Algebra.adjoin (degreeZeroSubring G) (Set.range f) := by
      intro n
      induction n using Nat.strong_induction_on with
      | h n ih =>
          intro x hx
          by_cases hn : n = 0
          · subst n
            have hmem :=
              (Algebra.adjoin (degreeZeroSubring G) (Set.range f)).algebraMap_mem
                (⟨x, hx⟩ : degreeZeroSubring G)
            change x ∈ Algebra.adjoin (degreeZeroSubring G) (Set.range f) at hmem
            exact hmem
          · have hxI : x ∈ I := by
              change x ∈ Ideal.span (Set.range f)
              exact hspan.symm ▸
                (HomogeneousIdeal.mem_irrelevant_of_mem
                  (𝒜 := G.component) (i := n) (x := x)
                  (Nat.pos_of_ne_zero hn) hx)
            have hspan_ind :
                (DirectSum.decompose G.component x n : S) ∈
                  Algebra.adjoin (degreeZeroSubring G) (Set.range f) :=
              by
                refine Submodule.closure_induction
                  (R := S) (M := S) (s := Set.range f) (x := x)
                  (p := fun y _ =>
                    (DirectSum.decompose G.component y n : S) ∈
                      Algebra.adjoin (degreeZeroSubring G) (Set.range f)) ?_ ?_ ?_ hxI
                · simp
                · intro y z hy hz py pz
                  rw [DirectSum.decompose_add]
                  exact (Algebra.adjoin (degreeZeroSubring G) (Set.range f)).add_mem
                    py pz
                · intro a y hy
                  rcases hy with ⟨i, rfl⟩
                  rcases hf i with ⟨⟨d, hd⟩, hi⟩
                  by_cases hd0 : d = 0
                  · have hzero : f i = 0 := by
                      subst d
                      have hi₀ := (HomogeneousIdeal.mem_irrelevant_iff
                        (𝒜 := G.component) (f i)).mp hi
                      change (DirectSum.decompose G.component (f i) 0 : S) = 0 at hi₀
                      rw [DirectSum.decompose_of_mem_same G.component hd] at hi₀
                      exact hi₀
                    simp [hzero]
                  · by_cases hdk : d ≤ n
                    · have hlt : n - d < n :=
                        Nat.sub_lt (lt_of_lt_of_le (Nat.pos_of_ne_zero hd0) hdk)
                          (Nat.pos_of_ne_zero hd0)
                      have ha : (DirectSum.decompose G.component a (n - d) : S) ∈
                          Algebra.adjoin (degreeZeroSubring G) (Set.range f) :=
                        ih (n - d) hlt _ (DirectSum.decompose G.component a (n - d)).property
                      change (DirectSum.decompose G.component (a * f i) n : S) ∈
                        Algebra.adjoin (degreeZeroSubring G) (Set.range f)
                      rw [DirectSum.coe_decompose_mul_of_right_mem_of_le
                        G.component hd hdk]
                      exact (Algebra.adjoin (degreeZeroSubring G) (Set.range f)).mul_mem
                        ha (Algebra.subset_adjoin ⟨i, rfl⟩)
                    · change (DirectSum.decompose G.component (a * f i) n : S) ∈
                        Algebra.adjoin (degreeZeroSubring G) (Set.range f)
                      rw [DirectSum.coe_decompose_mul_of_right_mem_of_not_le
                        (a := a) G.component hd hdk]
                      exact (Algebra.adjoin (degreeZeroSubring G) (Set.range f)).zero_mem
            have h := hspan_ind
            rw [DirectSum.decompose_of_mem_same G.component hx] at h
            exact h
    apply le_antisymm le_top
    intro x hx
    exact DirectSum.Decomposition.inductionOn (ℳ := G.component)
      (motive := fun x => x ∈ Algebra.adjoin (degreeZeroSubring G) (Set.range f))
      (by exact (Algebra.adjoin (degreeZeroSubring G) (Set.range f)).zero_mem)
      (by intro i y; exact hcomp i y y.property)
      (by intro x y hx hy
          exact (Algebra.adjoin (degreeZeroSubring G) (Set.range f)).add_mem hx hy)
      x
/- Original nontrivial proof retained for later completion:
  let I : Ideal S := Ideal.span (Set.range f)
  let p₀ : S →+* S := GradedRing.projZeroRingHom G.component
  have hf₀ : ∀ i, p₀ (f i) = 0 := by
    intro i
    change GradedRing.proj G.component 0 (f i) = 0
    exact (HomogeneousIdeal.mem_irrelevant_iff (𝒜 := G.component) (f i)).mp (hf i).2
  have hI₀ : I ≤ RingHom.ker p₀ := by
    change Ideal.span (Set.range f) ≤ RingHom.ker p₀
    refine Ideal.span_le.mpr ?_
    rintro x ⟨i, rfl⟩
    exact hf₀ i
  have hP :
      ∃ P : Subalgebra (degreeZeroSubring G) S,
        (∀ i, f i ∈ P) ∧
          (∀ x, x ∈ irrelevantIdeal G → x ∈ P → ∃ y ∈ I, x = y) := by
    let P : Subalgebra (degreeZeroSubring G) S :=
      { carrier := {x | ∃ y, y ∈ I ∧ ∃ z : degreeZeroSubring G, x = y + (z : S)}
        add_mem' := by
          rintro x y ⟨x₁, hx₁, z, rfl⟩ ⟨y₁, hy₁, w, rfl⟩
          refine ⟨x₁ + y₁, I.add_mem hx₁ hy₁, z + w, ?_⟩
          simp only [Subring.coe_add]
          abel
        mul_mem' := by
          rintro x y ⟨x₁, hx₁, z, rfl⟩ ⟨y₁, hy₁, w, rfl⟩
          have hxy : x₁ * y₁ ∈ I := by
            change x₁ • y₁ ∈ I
            exact I.smul_mem x₁ hy₁
          have hxw : x₁ * (w : S) ∈ I := by
            simpa [mul_comm] using I.smul_mem (w : S) hx₁
          have hzy : (z : S) * y₁ ∈ I := by
            exact I.smul_mem (z : S) hy₁
          refine ⟨x₁ * y₁ + x₁ * (w : S) + (z : S) * y₁,
            I.add_mem (I.add_mem hxy hxw) hzy, z * w, ?_⟩
          simp only [Subring.coe_mul]
          ring
        algebraMap_mem' := by
          intro z
          exact ⟨0, I.zero_mem, z, by
            rw [Algebra.algebraMap_ofSubring]
            simp⟩ }
    refine ⟨P, ?_, ?_⟩
    · intro i
      exact ⟨f i, Ideal.subset_span ⟨i, rfl⟩, 0, by simp⟩
    · intro x hxIrrelevant hxP
      have hx := hxP
      rcases hx with ⟨y, hy, z, hxy⟩
      have hy₀ : p₀ y = 0 := hI₀ hy
      have hxzero : (z : S) = 0 := by
        have hx₀ : p₀ x = 0 := by
          change GradedRing.proj G.component 0 x = 0
          exact (HomogeneousIdeal.mem_irrelevant_iff (𝒜 := G.component) x).mp hxIrrelevant
        have hz₀ : p₀ (z : S) = (z : S) := by
          change (DirectSum.decompose G.component (z : S) 0 : S) = (z : S)
          exact DirectSum.decompose_of_mem_same G.component z.property
        rw [hxy, map_add, hy₀, hz₀] at hx₀
        simpa only [zero_add] using hx₀
      exact ⟨y, hy, by simpa [hxy, hxzero]⟩
  constructor
  · intro hgen
    apply le_antisymm
    · change I ≤ irrelevantIdeal G
      change I ≤ RingHom.ker p₀
      exact hI₀
    · intro x hx
      rcases hP with ⟨P, hfP, hPsub⟩
      have hle : Algebra.adjoin (degreeZeroSubring G) (Set.range f) ≤ P :=
        Algebra.adjoin_le (s := Set.range f) (S := P) (by
          rintro y ⟨i, rfl⟩
          exact hfP i)
      have hxP : x ∈ P := hle (by rw [hgen]; trivial)
      rcases hPsub x hx hxP with ⟨y, hy, hxy⟩
      simpa only [hxy] using hy
  · intro hspan
    have hcomp : ∀ n : ℕ, ∀ x : S, x ∈ G.component n →
        x ∈ Algebra.adjoin (degreeZeroSubring G) (Set.range f) := by
      intro n
      induction n using Nat.strong_induction_on with
      | h n ih =>
          intro x hx
          by_cases hn : n = 0
          · subst n
            have hmem :=
              (Algebra.adjoin (degreeZeroSubring G) (Set.range f)).algebraMap_mem
                (⟨x, hx⟩ : degreeZeroSubring G)
            change x ∈ Algebra.adjoin (degreeZeroSubring G) (Set.range f) at hmem
            exact hmem
          · have hxI : x ∈ I := by
              change x ∈ Ideal.span (Set.range f)
              exact hspan.symm ▸
                (HomogeneousIdeal.mem_irrelevant_of_mem
                  (𝒜 := G.component) (i := n) (x := x)
                  (Nat.pos_of_ne_zero hn) hx)
            have hspan_ind : ∀ k : ℕ,
                (DirectSum.decompose G.component x k : S) ∈
                  Algebra.adjoin (degreeZeroSubring G) (Set.range f) :=
              by
                refine Submodule.span_induction
                  (R := S) (M := S) (s := Set.range f) (x := x)
                  (p := fun y _ => ∀ k : ℕ,
                    (DirectSum.decompose G.component y k : S) ∈
                      Algebra.adjoin (degreeZeroSubring G) (Set.range f)) ?_ ?_ ?_ ?_ hxI
                · rintro y ⟨i, rfl⟩ k
                  rcases (hf i).1 with ⟨d, hd⟩
                  by_cases hdk : d = k
                  · subst k
                    rw [DirectSum.decompose_of_mem_same G.component hd]
                    exact Algebra.subset_adjoin ⟨i, rfl⟩
                  · rw [DirectSum.decompose_of_mem_ne G.component hd hdk]
                    exact (Algebra.adjoin (degreeZeroSubring G) (Set.range f)).zero_mem
                · intro k
                  exact (Algebra.adjoin (degreeZeroSubring G) (Set.range f)).zero_mem
                · intro y z hy hz py pz k
                  rw [DirectSum.decompose_add]
                  exact (Algebra.adjoin (degreeZeroSubring G) (Set.range f)).add_mem
                    (py k) (pz k)
                · intro a y hy py k
                  rcases hy with ⟨i, rfl⟩
                  rcases hf i with ⟨⟨d, hd⟩, hi⟩
                  by_cases hd0 : d = 0
                  · have hzero : f i = 0 := by
                      have hi₀ := (HomogeneousIdeal.mem_irrelevant_iff
                        (𝒜 := G.component) (f i)).mp hi
                      rw [DirectSum.decompose_of_mem_same G.component hd] at hi₀
                      exact hi₀
                    simp [hzero]
                  · by_cases hdk : d ≤ k
                    · have hlt : k - d < k :=
                        Nat.sub_lt (lt_of_lt_of_le (Nat.pos_of_ne_zero hd0) hdk)
                          (Nat.pos_of_ne_zero hd0)
                      have ha : (DirectSum.decompose G.component a (k - d) : S) ∈
                          Algebra.adjoin (degreeZeroSubring G) (Set.range f) :=
                        ih (k - d) hlt _ (DirectSum.decompose G.component a (k - d)).property
                      rw [DirectSum.coe_decompose_mul_of_right_mem_of_le
                        G.component hd hdk]
                      exact (Algebra.adjoin (degreeZeroSubring G) (Set.range f)).mul_mem
                        ha (Algebra.subset_adjoin ⟨i, rfl⟩)
                    · have hzero := DirectSum.coe_decompose_mul_of_right_mem_of_not_le
                        G.component hd hdk
                      simp [hzero]
            rw [DirectSum.decompose_of_mem_same G.component hx] at hspan_ind
            exact hspan_ind n
    apply le_antisymm le_top
    intro x hx
    exact DirectSum.Decomposition.inductionOn (ℳ := G.component)
      (motive := fun x => x ∈ Algebra.adjoin (degreeZeroSubring G) (Set.range f))
      (by exact (Algebra.adjoin (degreeZeroSubring G) (Set.range f)).zero_mem)
      (by intro i y; exact hcomp i y y.property)
      (by intro x y hx hy
          exact (Algebra.adjoin (degreeZeroSubring G) (Set.range f)).add_mem hx hy)
      x
-/

private theorem finiteType_of_irrelevant_fg (G : GradedRingData S)
    (hfg : (irrelevantIdeal G).FG) :
    Algebra.FiniteType (degreeZeroSubring G) S := by
  classical
  rcases hfg with ⟨s, hs⟩
  let ι₀ := Σ x : s, (DirectSum.decompose G.component (x : S)).support
  let f₀ : ι₀ → S := fun i =>
    (DirectSum.decompose G.component (i.1 : S) i.2 : S)
  let : Fintype ι₀ := inferInstance
  have hf₀ : ∀ i, IsHomogeneousElement G (f₀ i) ∧ f₀ i ∈ irrelevantIdeal G := by
    intro i
    constructor
    · exact SetLike.isHomogeneousElem_coe _
    · have hi : (i.1 : S) ∈ irrelevantIdeal G := by
        rw [← hs]
        exact Ideal.subset_span i.1.property
      exact (HomogeneousIdeal.irrelevant G.component).isHomogeneous i.2 hi
  have hspan : Ideal.span (Set.range f₀) = irrelevantIdeal G := by
    apply le_antisymm
    · exact Ideal.span_le.mpr (by
        rintro y ⟨i, rfl⟩
        exact (hf₀ i).2)
    · rw [← hs]
      refine Ideal.span_le.mpr ?_
      intro x hx
      rw [← DirectSum.sum_support_decompose G.component (x : S)]
      apply Ideal.sum_mem
      intro n hn
      apply Ideal.subset_span
      exact ⟨⟨⟨x, hx⟩, ⟨n, hn⟩⟩, by rfl⟩
  have hadj : Algebra.adjoin (degreeZeroSubring G) (Set.range f₀) = ⊤ :=
    (sPlus_generated_iff G f₀ hf₀).mpr hspan
  exact ⟨Subalgebra.fg_def.mpr ⟨Set.range f₀, Set.finite_range f₀, hadj⟩⟩

theorem graded_noetherian_iff (G : GradedRingData S) :
    IsNoetherianRing S ↔
      IsNoetherianRing (degreeZeroSubring G) ∧ (irrelevantIdeal G).FG := by
  constructor
  · intro hS
    let : IsNoetherianRing S := hS
    have h₀ : IsNoetherianRing (degreeZeroSubring G) := by
      exact isNoetherianRing_of_surjective S (degreeZeroSubring G)
        (GradedRing.projZeroRingHom' G.component)
        (GradedRing.projZeroRingHom'_surjective G.component)
    let : IsNoetherianRing (degreeZeroSubring G) := h₀
    exact ⟨h₀, Ideal.fg_of_isNoetherianRing _⟩
  · rintro ⟨h₀, hfg⟩
    let : IsNoetherianRing (degreeZeroSubring G) := h₀
    let : Algebra.FiniteType (degreeZeroSubring G) S :=
      finiteType_of_irrelevant_fg G hfg
    exact Algebra.FiniteType.isNoetherianRing (degreeZeroSubring G) S

theorem finiteType_of_noetherian_graded
    (G : GradedRingData S) (hS : IsNoetherianRing S) :
    Algebra.FiniteType (degreeZeroSubring G) S := by
  let : IsNoetherianRing S := hS
  exact finiteType_of_irrelevant_fg G (Ideal.fg_of_isNoetherianRing _)

/-! ## Numerical polynomials -/

/-- The integer binomial coefficient used in the eventual formula below.

The value at negative integers is immaterial to an eventual statement; it is
set to zero so that this is a total function on `ℤ`. -/
def integerBinomial (n : ℤ) (i : ℕ) : ℤ :=
  if 0 ≤ n then (n.toNat.choose i : ℤ) else 0

/-- A function on the integers is a numerical polynomial if it is eventually
of binomial-coefficient form with coefficients in an abelian group. -/
def IsNumericalPolynomial {A : Type v} [AddCommGroup A] (f : ℤ → A) : Prop :=
  ∃ r : ℕ, ∃ a : ℕ → A,
    ∀ᶠ n : ℤ in Filter.atTop,
      f n = ∑ i ∈ Finset.range (r + 1), integerBinomial n i • a i

/-- A numerical polynomial with a prescribed upper bound on the index of its
binomial expansion. -/
def IsNumericalPolynomialOfDegreeLessThan
    {A : Type v} [AddCommGroup A] (f : ℤ → A) (d : ℕ) : Prop :=
  ∃ r : ℕ, r < d ∧ ∃ a : ℕ → A,
    ∀ᶠ n : ℤ in Filter.atTop,
      f n = ∑ i ∈ Finset.range (r + 1), integerBinomial n i • a i

/-- Eventual vanishing, used for the zero-polynomial exception in the
one-variable quotient statement. -/
def IsEventuallyZero {A : Type v} [AddCommGroup A] (f : ℤ → A) : Prop :=
  ∀ᶠ n : ℤ in Filter.atTop, f n = 0

theorem numericalPolynomial_comp_addMonoidHom
    {A A' : Type v} [AddCommGroup A] [AddCommGroup A']
    (φ : A →+ A') (f : ℤ → A) (hf : IsNumericalPolynomial f) :
    IsNumericalPolynomial (fun n => φ (f n)) := by
  rcases hf with ⟨r, a, ha⟩
  refine ⟨r, fun i => φ (a i), ha.mono (fun n hn => by simp [hn])⟩

private lemma integerBinomial_sub_shift (n : ℤ) (hn : 0 ≤ n) (i : ℕ) :
    integerBinomial (n + 1) (i + 1) - integerBinomial n (i + 1) =
      integerBinomial n i := by
  have hnp : 0 ≤ n + 1 := add_nonneg hn (by norm_num)
  simp only [integerBinomial, if_pos hn, if_pos hnp]
  rw [Int.toNat_add hn (by norm_num)]
  simp only [Int.toNat_one]
  rw [Nat.choose_succ_succ']
  norm_num

theorem isNumericalPolynomial_of_sub
    {A : Type v} [AddCommGroup A] (f : ℤ → A)
    (hf : IsNumericalPolynomial (fun n => f n - f (n - 1))) :
    IsNumericalPolynomial f := by
  rcases hf with ⟨r, a, ha⟩
  let g : ℤ → A := fun n =>
    ∑ i ∈ Finset.range (r + 1), integerBinomial (n + 1) (i + 1) • a i
  let d : ℤ → A := fun n => f n - g n
  have hg : ∀ᶠ n : ℤ in Filter.atTop,
      g n - g (n - 1) = ∑ i ∈ Finset.range (r + 1), integerBinomial n i • a i := by
    filter_upwards [Filter.Ici_mem_atTop (0 : ℤ)] with n hn
    dsimp [g]
    have hnm : (n - 1) + 1 = n := by ring
    rw [hnm, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    rw [← sub_smul, integerBinomial_sub_shift n hn i]
  have hd : ∀ᶠ n : ℤ in Filter.atTop, d n = d (n - 1) := by
    filter_upwards [ha, hg] with n hn hgn
    dsimp [d]
    calc
      f n - g n = (f n - f (n - 1)) - (g n - g (n - 1)) +
          (f (n - 1) - g (n - 1)) := by abel
      _ = f (n - 1) - g (n - 1) := by rw [hn, hgn]; abel
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1
    (hd.and (Filter.Ici_mem_atTop (0 : ℤ)))
  have hconst_nat : ∀ k : ℕ, d (N + k) = d N := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        have h := (hN (N + (k + 1)) (by omega)).1
        calc
          d (N + (k + 1)) = d ((N + (k + 1)) - 1) := h
          _ = d (N + k) := by
            congr 1
            ring
          _ = d N := ih
  have hconst : ∀ n : ℤ, N ≤ n → d n = d N := by
    intro n hn
    have hrepr : n = N + (n - N).toNat := by omega
    rw [hrepr]
    exact hconst_nat _
  let b : ℕ → A := fun j =>
    if j = 0 then d N + a 0
    else a (j - 1) + if j ≤ r then a j else 0
  have hsum (n : ℤ) (hn : 0 ≤ n) :
      (∑ j ∈ Finset.range (r + 2), integerBinomial n j • b j) =
        d N + ∑ i ∈ Finset.range (r + 1),
          integerBinomial (n + 1) (i + 1) • a i := by
    have hnp : 0 ≤ n + 1 := by omega
    have hpascal (i : ℕ) :
        integerBinomial (n + 1) (i + 1) =
          integerBinomial n i + integerBinomial n (i + 1) := by
      simp only [integerBinomial, if_pos hn, if_pos hnp]
      rw [Int.toNat_add hn (by norm_num), Int.toNat_one,
        Nat.choose_succ_succ']
      exact_mod_cast rfl
    have hcond :
        (∑ j ∈ Finset.range (r + 1),
            integerBinomial n (j + 1) •
              (if j + 1 ≤ r then a (j + 1) else 0)) =
          ∑ j ∈ Finset.range r, integerBinomial n (j + 1) • a (j + 1) := by
      rw [Finset.sum_range_succ]
      have hr : ¬ r + 1 ≤ r := by omega
      simp only [hr, if_false, smul_zero, add_zero]
      apply Finset.sum_congr rfl
      intro j hj
      have hj' : j + 1 ≤ r := Nat.succ_le_of_lt (Finset.mem_range.1 hj)
      simp [hj']
    have hshift :
        (∑ j ∈ Finset.range (r + 1),
            integerBinomial n (j + 1) • b (j + 1)) =
          (∑ j ∈ Finset.range (r + 1),
              integerBinomial n (j + 1) • a j) +
            ∑ j ∈ Finset.range r, integerBinomial n (j + 1) • a (j + 1) := by
      change (∑ j ∈ Finset.range (r + 1),
          integerBinomial n (j + 1) •
            (a j + if j + 1 ≤ r then a (j + 1) else 0)) = _
      calc
        (∑ j ∈ Finset.range (r + 1),
            integerBinomial n (j + 1) •
              (a j + if j + 1 ≤ r then a (j + 1) else 0)) =
            ∑ j ∈ Finset.range (r + 1),
              (integerBinomial n (j + 1) • a j +
                integerBinomial n (j + 1) •
                  (if j + 1 ≤ r then a (j + 1) else 0)) := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [smul_add]
        _ = (∑ j ∈ Finset.range (r + 1),
                integerBinomial n (j + 1) • a j) +
              ∑ j ∈ Finset.range (r + 1),
                integerBinomial n (j + 1) •
                  (if j + 1 ≤ r then a (j + 1) else 0) := by
          rw [Finset.sum_add_distrib]
        _ = _ := by rw [hcond]
    have hdecomp :
        (∑ j ∈ Finset.range (r + 2), integerBinomial n j • b j) =
          integerBinomial n 0 • b 0 +
            ∑ j ∈ Finset.range (r + 1),
              integerBinomial n (j + 1) • b (j + 1) := by
      rw [show r + 2 = (r + 1) + 1 by omega, Finset.sum_range_succ']
      abel_nf
    have hz : integerBinomial n 0 • b 0 = d N + a 0 := by
      simp [b, integerBinomial, hn]
    rw [hdecomp, hz, hshift]
    simp_rw [hpascal, add_smul, Finset.sum_add_distrib]
    have hfirst :
        (∑ x ∈ Finset.range (r + 1), integerBinomial n x • a x) =
          integerBinomial n 0 • a 0 +
            ∑ x ∈ Finset.range r, integerBinomial n (x + 1) • a (x + 1) := by
      rw [Finset.sum_range_succ']
      abel
    /- Prior attempt:
    rw [hfirst]
    simp [integerBinomial, hn]
    abel_nf
    -/
    rw [hfirst]
    simp [integerBinomial, hn]
    abel
  refine ⟨r + 1, b, ?_⟩
  filter_upwards [Filter.Ici_mem_atTop N] with n hn
  obtain ⟨_, hn0⟩ := hN n hn
  have hdn : d n = d N := hconst n hn
  have hgn : g n = f n - d N := by
    calc
      g n = f n - d n := by dsimp [d]; abel
      _ = f n - d N := by rw [hdn]
  rw [hsum n hn0]
  dsimp [d, g] at hgn ⊢
  rw [hgn]
  abel

/- The elementary integer-valued-polynomial fact recalled in the source. -/
theorem integer_valued_polynomial_is_numerical
    (P : Polynomial ℚ)
    (hP : ∀ n : ℤ, ∃ z : ℤ, P.eval (n : ℚ) = (z : ℚ)) :
    ∃ f : ℤ → ℤ,
      (∀ n : ℤ, (f n : ℚ) = P.eval (n : ℚ)) ∧
        IsNumericalPolynomial f := by
  classical
  have aux : ∀ d : ℕ, ∀ P : Polynomial ℚ, P.natDegree = d →
      (∀ n : ℤ, ∃ z : ℤ, P.eval (n : ℚ) = (z : ℚ)) →
        ∃ f : ℤ → ℤ,
          (∀ n : ℤ, (f n : ℚ) = P.eval (n : ℚ)) ∧
            IsNumericalPolynomial f := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
        intro P hdeg hInt
        by_cases hzero : d = 0
        · let f : ℤ → ℤ := fun n => Classical.choose (hInt n)
          have hf_eval : ∀ n : ℤ, (f n : ℚ) = P.eval (n : ℚ) := by
            intro n
            exact (Classical.choose_spec (hInt n)).symm
          have hPconst : P = Polynomial.C (P.coeff 0) := by
            exact Polynomial.eq_C_of_natDegree_eq_zero (hzero ▸ hdeg)
          refine ⟨f, hf_eval, 0, (fun _ => f 0), ?_⟩
          filter_upwards [Filter.Ici_mem_atTop (0 : ℤ)] with n hn
          have hn0 : 0 ≤ n := hn
          have hfn : f n = f 0 := by
            apply Int.cast_injective (α := ℚ)
            rw [hf_eval n, hf_eval 0, hPconst]
            simp
          simp [hfn, integerBinomial, hn0]
        · have hpos : 0 < P.natDegree := by omega
          have hP0 : P ≠ 0 := by
            intro h
            simp [h] at hpos
          let q : Polynomial ℚ := Polynomial.X - Polynomial.C 1
          let Q : Polynomial ℚ := P - P.comp q
          have hqdegree : q.natDegree = 1 := by
            dsimp [q]
            rw [Polynomial.natDegree_X_sub_C]
          have hqdeg : q.natDegree ≠ 0 := by omega
          have hcomp0 : P.comp q ≠ 0 := by
            intro h
            have hh := congrArg Polynomial.natDegree h
            rw [Polynomial.natDegree_comp, hqdegree,
              Nat.mul_one, Polynomial.natDegree_zero] at hh
            exact (Nat.ne_of_gt hpos) hh
          have hdegcomp : (P.comp q).degree = P.degree := by
            rw [Polynomial.degree_eq_natDegree hcomp0,
              Polynomial.degree_eq_natDegree hP0, Polynomial.natDegree_comp,
              hqdegree, Nat.mul_one]
          have hlc : P.leadingCoeff = (P.comp q).leadingCoeff := by
            rw [Polynomial.leadingCoeff_comp hqdeg]
            rw [Polynomial.leadingCoeff_X_sub_C]
            simp
          have hQdeg : Q.natDegree < P.natDegree := by
            by_cases hQ0 : Q = 0
            · simp [hQ0, hpos]
            · apply Polynomial.natDegree_lt_natDegree hQ0
              dsimp [Q]
              exact Polynomial.degree_sub_lt hdegcomp.symm hP0 hlc
          have hQint : ∀ n : ℤ, ∃ z : ℤ, Q.eval (n : ℚ) = (z : ℚ) := by
            intro n
            rcases hInt n with ⟨z₁, hz₁⟩
            rcases hInt (n - 1) with ⟨z₂, hz₂⟩
            refine ⟨z₁ - z₂, ?_⟩
            dsimp [Q, q]
            rw [Polynomial.eval_sub, Polynomial.eval_comp,
              Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
            have hcast : (n : ℚ) - 1 = ((n - 1 : ℤ) : ℚ) := by norm_num
            rw [hcast, hz₁, hz₂]
            exact (Int.cast_sub z₁ z₂).symm
          have hQdeg' : Q.natDegree < d := hdeg ▸ hQdeg
          obtain ⟨g, hg_eval, hg_num⟩ :=
            ih Q.natDegree hQdeg' Q rfl hQint
          let f : ℤ → ℤ := fun n => Classical.choose (hInt n)
          have hf_eval : ∀ n : ℤ, (f n : ℚ) = P.eval (n : ℚ) := by
            intro n
            exact (Classical.choose_spec (hInt n)).symm
          have hdiff_eval : ∀ n : ℤ,
              ((f n - f (n - 1) : ℤ) : ℚ) = Q.eval (n : ℚ) := by
            intro n
            dsimp [Q, q]
            rw [Polynomial.eval_sub, Polynomial.eval_comp,
              Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C,
              Int.cast_sub]
            have hcast : (n : ℚ) - 1 = ((n - 1 : ℤ) : ℚ) := by norm_num
            rw [hcast, hf_eval n, hf_eval (n - 1)]
          have hdiff : ∀ n : ℤ, f n - f (n - 1) = g n := by
            intro n
            apply Int.cast_injective (α := ℚ)
            exact (hdiff_eval n).trans (hg_eval n).symm
          refine ⟨f, hf_eval, isNumericalPolynomial_of_sub f ?_⟩
          simpa [hdiff] using hg_num
  exact aux P.natDegree P rfl hP

theorem shifted_integerBinomial_is_numerical (i : ℕ) :
    IsNumericalPolynomial (fun n : ℤ => integerBinomial (n + 1) (i + 1)) := by
  refine ⟨i + 1,
    (fun j => if j = i then (1 : ℤ) else if j = i + 1 then 1 else 0), ?_⟩
  filter_upwards [Filter.Ici_mem_atTop (0 : ℤ)] with n hn
  have hn0 : 0 ≤ n := hn
  have hnp : 0 ≤ n + 1 := by omega
  simp only [integerBinomial, if_pos hn0, if_pos hnp]
  rw [Int.toNat_add hn0 (by norm_num), Int.toNat_one, Nat.choose_succ_succ']
  let s := Finset.range (i + 1 + 1)
  have hi : i ∈ s := by simp [s]
  have hi1 : i + 1 ∈ s := by simp [s]
  have hne : i ≠ i + 1 := by omega
  have hsum :
      (∑ x ∈ s, if x = i then (n.toNat.choose x : ℤ)
        else if x = i + 1 then (n.toNat.choose x : ℤ) else 0) =
        (n.toNat.choose i : ℤ) + (n.toNat.choose (i + 1) : ℤ) := by
    calc
      (∑ x ∈ s, if x = i then (n.toNat.choose x : ℤ)
          else if x = i + 1 then (n.toNat.choose x : ℤ) else 0) =
          (∑ x ∈ s, if x = i then (n.toNat.choose x : ℤ) else 0) +
            ∑ x ∈ s, if x = i + 1 then (n.toNat.choose x : ℤ) else 0 := by
              rw [← Finset.sum_add_distrib]
              apply Finset.sum_congr rfl
              intro x hx
              by_cases hxi : x = i <;> by_cases hxi1 : x = i + 1 <;>
                simp [hxi, hxi1]
      _ = (n.toNat.choose i : ℤ) + (n.toNat.choose (i + 1) : ℤ) := by
        rw [Finset.sum_eq_single_of_mem i hi,
          Finset.sum_eq_single_of_mem (i + 1) hi1]
        · simp
        · intro x hx hxi
          simp [hxi]
        · intro x hx hxi
          simp [hxi]
  simpa [s] using hsum.symm

/-! ## Finitely generated graded modules and Hilbert functions -/

/- A degree-zero scalar preserves each graded component.  Chapter 56 records
the components as additive subgroups, so this is the small module instance
needed by the K′₀ construction. -/
instance gradedComponentDegreeZeroModule
    (G : GradedRingData S) (𝓜 : GradedModuleData G M) (n : ℤ) :
    Module (degreeZeroSubring G) (𝓜.component n) where
  smul r x :=
    ⟨(r : S) • (x : M), by
      have h := 𝓜.gradedSMul.smul_mem r.property x.property
      change (r : S) • (x : M) ∈ 𝓜.component ((0 : ℤ) + n) at h
      simpa using h⟩
  one_smul x := by
    apply Subtype.ext
    change (1 : S) • (x : M) = (x : M)
    simp
  mul_smul r s x := by
    apply Subtype.ext
    change ((r : S) * (s : S)) • (x : M) = (r : S) • ((s : S) • (x : M))
    exact mul_smul (r : S) (s : S) (x : M)
  smul_add r x y := by
    apply Subtype.ext
    change (r : S) • ((x : M) + (y : M)) =
      (r : S) • (x : M) + (r : S) • (y : M)
    simp
  smul_zero r := by
    apply Subtype.ext
    change (r : S) • (0 : M) = 0
    simp
  add_smul r s x := by
    apply Subtype.ext
    change ((r : S) + (s : S)) • (x : M) =
      (r : S) • (x : M) + (s : S) • (x : M)
    exact add_smul (r : S) (s : S) (x : M)
  zero_smul x := by
    apply Subtype.ext
    change (0 : S) • (x : M) = 0
    simp

theorem graded_module_component_finite
    (G : GradedRingData S) (𝓜 : GradedModuleData G M)
    [Algebra.FiniteType (degreeZeroSubring G) S] [Module.Finite S M] :
    ∀ n : ℤ, Module.Finite (degreeZeroSubring G) (𝓜.component n) := by
  sorry

noncomputable def gradedHilbertFunction
    (G : GradedRingData S) (𝓜 : GradedModuleData G M)
    (h𝓜 : ∀ n : ℤ, Module.Finite (degreeZeroSubring G) (𝓜.component n)) :
    ℤ → KPrimeZero (degreeZeroSubring G) :=
  fun n =>
    letI : Module.Finite (degreeZeroSubring G) (𝓜.component n) := h𝓜 n
    kPrimeZeroClass (R := degreeZeroSubring G) (M := 𝓜.component n)

noncomputable def noetherianGradedHilbertFunction
    (G : GradedRingData S) (𝓜 : GradedModuleData G M)
    (hS : IsNoetherianRing S) [Module.Finite S M] :
    ℤ → KPrimeZero (degreeZeroSubring G) := by
  letI : Algebra.FiniteType (degreeZeroSubring G) S :=
    finiteType_of_noetherian_graded G hS
  exact gradedHilbertFunction G 𝓜 (graded_module_component_finite G 𝓜)

/-- The irrelevant ideal is generated in degree one. -/
def GeneratedInDegreeOne (G : GradedRingData S) : Prop :=
  ∃ t : Set S, (∀ x ∈ t, x ∈ G.component 1) ∧
    Ideal.span t = irrelevantIdeal G

theorem graded_hilbert_polynomial
    (G : GradedRingData S) (𝓜 : GradedModuleData G M)
    (hS : IsNoetherianRing S) [Module.Finite S M]
    (hdegree : GeneratedInDegreeOne G) :
    IsNumericalPolynomial (noetherianGradedHilbertFunction G 𝓜 hS) := by
  sorry

/-- A function is periodic-polynomial when its restriction to every residue
class modulo one positive period is a numerical polynomial in the quotient
variable. -/
def IsPeriodicNumericalPolynomial
    {A : Type v} [AddCommGroup A] (f : ℤ → A) : Prop :=
  ∃ q : ℕ, 0 < q ∧
    ∀ r : Fin q,
      IsNumericalPolynomial (fun m : ℤ => f ((r : ℤ) + (q : ℤ) * m))

theorem graded_hilbert_periodic_polynomial
    (G : GradedRingData S) (𝓜 : GradedModuleData G M)
    (hS : IsNoetherianRing S) [Module.Finite S M]
    (hnot : ¬ GeneratedInDegreeOne G) :
    IsPeriodicNumericalPolynomial (noetherianGradedHilbertFunction G 𝓜 hS) := by
  sorry

/- The field-valued example uses the existing K′₀-to-dimension theorem from
Chapter 55. -/
noncomputable def degreeZeroHilbertFunctionLength
    (G : GradedRingData S) (𝓜 : GradedModuleData G M)
    (hS : IsNoetherianRing S) [Module.Finite S M]
    [IsArtinianRing (degreeZeroSubring G)] : ℤ → ℤ :=
  fun n =>
    kPrimeZeroLength (R := degreeZeroSubring G)
      (noetherianGradedHilbertFunction G 𝓜 hS n)

theorem graded_hilbert_function_length_numerical
    (G : GradedRingData S) (𝓜 : GradedModuleData G M)
    (hS : IsNoetherianRing S) [Module.Finite S M]
    [IsArtinianRing (degreeZeroSubring G)]
    (hdegree : GeneratedInDegreeOne G) :
    IsNumericalPolynomial (degreeZeroHilbertFunctionLength G 𝓜 hS) := by
  sorry

theorem field_kprimeZero_length_eq_finrank
    {k : Type u} [Field k] {N : Type v}
    [AddCommGroup N] [Module k N] [Module.Finite k N] :
    kPrimeZeroLength (R := k)
        (kPrimeZeroClass (R := k) (M := N)) =
      (Module.finrank k N : ℤ) := by
  exact kPrimeZeroLength_field_eq_finrank

/-! ## The polynomial-ring quotient example -/

abbrev polynomialQuotientComponent
    (k : Type u) [Field k] (d : ℕ)
    (I : Ideal (MvPolynomial (Fin d) k)) (n : ℕ) : Type u :=
  MvPolynomial.homogeneousSubmodule (Fin d) k n ⧸
    Submodule.comap
      (MvPolynomial.homogeneousSubmodule (Fin d) k n).subtype
      (I.restrictScalars k)

def polynomialQuotientHilbertFunction
    (k : Type u) [Field k] (d : ℕ)
    (I : Ideal (MvPolynomial (Fin d) k)) : ℤ → ℤ :=
  fun n =>
    if _h : 0 ≤ n then
      (Module.finrank k (polynomialQuotientComponent k d I n.toNat) : ℤ)
    else 0

def IsPolynomialGradedIdeal
    (k : Type u) [Field k] (d : ℕ)
    (I : Ideal (MvPolynomial (Fin d) k)) : Prop :=
  ∀ n : ℕ, ∀ x : MvPolynomial (Fin d) k, x ∈ I →
    MvPolynomial.homogeneousComponent n x ∈ I

theorem polynomial_quotient_hilbert_function_degree_lt
    (k : Type u) [Field k] (d : ℕ) (hd : 0 < d)
    (I : Ideal (MvPolynomial (Fin d) k)) (hI : I ≠ ⊥)
    (hIgraded : IsPolynomialGradedIdeal k d I) :
    IsNumericalPolynomialOfDegreeLessThan
        (polynomialQuotientHilbertFunction k d I) (d - 1) ∨
      (d = 1 ∧
        IsEventuallyZero (polynomialQuotientHilbertFunction k d I)) := by
  sorry

end

end Formalization.Books.Algebra.Unit58
