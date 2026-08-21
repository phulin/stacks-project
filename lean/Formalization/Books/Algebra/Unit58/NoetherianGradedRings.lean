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
open scoped DirectSum

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

theorem isNumericalPolynomialOfDegreeLessThan_iff
    {A : Type v} [AddCommGroup A] (f : ℤ → A) (d : ℕ) :
    IsNumericalPolynomialOfDegreeLessThan f d ↔
      ∃ r : ℕ, r < d ∧ ∃ a : ℕ → A,
        ∀ᶠ n : ℤ in Filter.atTop,
          f n = ∑ i ∈ Finset.range (r + 1), integerBinomial n i • a i :=
  Iff.rfl

theorem IsNumericalPolynomialOfDegreeLessThan.isNumericalPolynomial
    {A : Type v} [AddCommGroup A] {f : ℤ → A} {d : ℕ}
    (hf : IsNumericalPolynomialOfDegreeLessThan f d) :
    IsNumericalPolynomial f := by
  rcases hf with ⟨r, -, a, ha⟩
  exact ⟨r, a, ha⟩

theorem isEventuallyZero_iff
    {A : Type v} [AddCommGroup A] (f : ℤ → A) :
    IsEventuallyZero f ↔ ∀ᶠ n : ℤ in Filter.atTop, f n = 0 :=
  Iff.rfl

theorem IsEventuallyZero.isNumericalPolynomial
    {A : Type v} [AddCommGroup A] {f : ℤ → A}
    (hf : IsEventuallyZero f) : IsNumericalPolynomial f := by
  refine ⟨0, fun _ => 0, ?_⟩
  filter_upwards [hf] with n hn
  simp [hn]

theorem isNumericalPolynomial_zero
    {A : Type v} [AddCommGroup A] :
    IsNumericalPolynomial (fun _ : ℤ => (0 : A)) :=
  IsEventuallyZero.isNumericalPolynomial (Filter.Eventually.of_forall fun _ => rfl)

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

/-! ## Associated graded modules and Hilbert functions -/

/- The quotient is written with the denominator pulled back to the subtype
   in the numerator.  This keeps the degreewise pieces definitionally equal
   to the usual quotients `I^n/I^(n+1)` and `I^n M/I^(n+1) M`. -/
abbrev associatedGradedSubquotient
    {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]
    (P Q : Submodule R M) : Type _ :=
  HasQuotient.Quotient (P : Type _) (Q.comap P.subtype)

/-- The degree-`n` component `I^n/I^(n+1)` of the associated graded ring. -/
abbrev associatedGradedRingPiece
    {R : Type u} [CommRing R] (I : Ideal R) (n : ℕ) : Type u :=
  associatedGradedSubquotient (I ^ n : Submodule R R) (I ^ (n + 1) : Submodule R R)

/-- The degree-`n` component `I^n M/I^(n+1) M` of the associated graded
module. -/
abbrev associatedGradedModulePiece
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (I : Ideal R) (n : ℕ) : Type _ :=
  associatedGradedSubquotient (I ^ n • (⊤ : Submodule R M))
    (I ^ (n + 1) • (⊤ : Submodule R M))

/-- The associated graded ring `Gr_I(R)`, with its direct-sum carrier. -/
abbrev associatedGradedRing
    {R : Type u} [CommRing R] (I : Ideal R) : Type u :=
  DirectSum ℕ (associatedGradedRingPiece I)

/-- The associated graded module `Gr_I(M)`, with its direct-sum carrier. -/
abbrev associatedGradedModule
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (I : Ideal R) : Type _ :=
  DirectSum ℕ (fun n => associatedGradedModulePiece (M := M) I n)

/-! The following small wrappers turn an external direct sum back into the
internal grading interface used by the Hilbert-polynomial argument. -/

def directSumComponent
    {ι : Type u} {A : ι → Type v} [∀ i, AddCommGroup (A i)] [DecidableEq ι]
    (i : ι) :
    AddSubgroup (DirectSum ι A) :=
  (DirectSum.of A i).range

@[instance_reducible]
def directSumComponent_decomposition
    {ι : Type u} {A : ι → Type v} [∀ i, AddCommGroup (A i)] [DecidableEq ι] :
    DirectSum.Decomposition (directSumComponent (A := A)) := by
  classical
  change DirectSum.Decomposition (fun i => (DirectSum.of A i).range)
  let f : (DirectSum ι A) →+
      (⨁ i, (DirectSum.of A i).range) :=
    DirectSum.map (fun i => (DirectSum.of A i).rangeRestrict)
  apply DirectSum.Decomposition.ofAddHom
    (ℳ := fun i => (DirectSum.of A i).range) f
  · apply DirectSum.addHom_ext
    intro i x
    change (DirectSum.coeAddMonoidHom
        (fun i => (DirectSum.of A i).range))
        (DirectSum.map (fun i => (DirectSum.of A i).rangeRestrict)
          (DirectSum.of A i x)) = DirectSum.of A i x
    rw [DirectSum.map_of, DirectSum.coeAddMonoidHom_of]
    rfl
  · apply DirectSum.addHom_ext
    intro i x
    rcases x with ⟨x, hx⟩
    rcases hx with ⟨y, rfl⟩
    simp [f]
    rfl

def directSumNatComponent
    {A : ℕ → Type u} [∀ i, AddCommGroup (A i)] (d : ℤ) :
    AddSubgroup (DirectSum ℕ A) :=
  if 0 ≤ d then directSumComponent (A := A) d.toNat else ⊥

instance directSumNatComponent_module
    {R : Type u} {A : ℕ → Type v} [CommRing R]
    [∀ i, AddCommGroup (A i)] [∀ i, Module R (A i)] (d : ℤ) :
    Module R (directSumNatComponent (A := A) d) where
  smul r x := ⟨r • (x : DirectSum ℕ A), by
    by_cases hd : 0 ≤ d
    · have hx : (x : DirectSum ℕ A) ∈ directSumComponent (A := A) d.toNat := by
        simpa [directSumNatComponent, hd] using x.property
      rcases hx with ⟨y, hy⟩
      simp only [directSumNatComponent, hd]
      refine ⟨r • y, ?_⟩
      rw [← hy, DirectSum.of_smul]
    · have hx : (x : DirectSum ℕ A) = 0 := by
        simpa [directSumNatComponent, hd] using x.property
      simp only [directSumNatComponent, hd]
      rw [hx, smul_zero]
      exact (⊥ : AddSubgroup (DirectSum ℕ A)).zero_mem⟩
  one_smul x := by
    apply Subtype.ext
    exact one_smul R (x : DirectSum ℕ A)
  mul_smul r s x := by
    apply Subtype.ext
    exact (smul_smul r s (x : DirectSum ℕ A)).symm
  smul_add r x y := by
    apply Subtype.ext
    exact smul_add r (x : DirectSum ℕ A) (y : DirectSum ℕ A)
  smul_zero r := by
    apply Subtype.ext
    exact smul_zero r
  add_smul r s x := by
    apply Subtype.ext
    exact add_smul r s (x : DirectSum ℕ A)
  zero_smul x := by
    apply Subtype.ext
    exact zero_smul R (x : DirectSum ℕ A)

@[instance_reducible]
def directSumNatComponent_decomposition
    {A : ℕ → Type u} [∀ i, AddCommGroup (A i)] :
    DirectSum.Decomposition (directSumNatComponent (A := A)) := by
  classical
  let φ : ∀ n : ℕ, A n →+
      directSumNatComponent (A := A) (n : ℤ) := fun n =>
    { toFun := fun x => ⟨DirectSum.of A n x, by
        simp [directSumNatComponent, directSumComponent]⟩
      map_zero' := by
        apply Subtype.ext
        simp
      map_add' := by
        intro x y
        apply Subtype.ext
        simp }
  let decompose : (DirectSum ℕ A) →+
      (⨁ d, directSumNatComponent (A := A) d) :=
    DirectSum.toAddMonoid (β := A) (fun n : ℕ =>
      (DirectSum.of (fun d : ℤ => directSumNatComponent (A := A) d) (n : ℤ)).comp
        (φ n))
  apply DirectSum.Decomposition.ofAddHom
    (ℳ := fun d => directSumNatComponent (A := A) d) decompose
  · apply DirectSum.addHom_ext
    intro n x
    simp [decompose, φ]
  · apply DirectSum.addHom_ext
    intro d x
    change decompose ((DirectSum.coeAddMonoidHom
        (fun d => directSumNatComponent (A := A) d))
        (DirectSum.of (fun d : ℤ => directSumNatComponent (A := A) d) d x)) =
      DirectSum.of (fun d : ℤ => directSumNatComponent (A := A) d) d x
    rw [DirectSum.coeAddMonoidHom_of]
    by_cases hd : 0 ≤ d
    · have hx : (x : DirectSum ℕ A) ∈ directSumComponent (A := A) d.toNat := by
        simpa [directSumNatComponent, hd] using x.property
      rcases hx with ⟨y, hy⟩
      have hcast : (d.toNat : ℤ) = d := Int.toNat_of_nonneg hd
      have hxy : (x : DirectSum ℕ A) = DirectSum.of A d.toNat y := hy.symm
      have hxeq :
          (⟨DirectSum.of A d.toNat y, by
            simpa [directSumNatComponent, hd] using
              (show DirectSum.of A d.toNat y ∈
                  directSumComponent (A := A) d.toNat from ⟨y, rfl⟩)⟩ :
            directSumNatComponent (A := A) d) = x := by
        apply Subtype.ext
        exact hxy.symm
      rw [← hxeq]
      dsimp [decompose]
      rw [DirectSum.toAddMonoid_of]
      dsimp [φ]
      cases d <;> simp_all [directSumNatComponent, directSumComponent]
    · have hx : (x : DirectSum ℕ A) = 0 := by
        simpa [directSumNatComponent, hd] using x.property
      have hxeq : x = (0 : directSumNatComponent (A := A) d) :=
        Subtype.ext hx
      rw [hxeq]
      simp [decompose, φ]

noncomputable def directSumNatComponent_linearEquiv
    {R : Type u} {A : ℕ → Type v} [CommRing R]
    [∀ i, AddCommGroup (A i)] [∀ i, Module R (A i)] (n : ℕ) :
    directSumNatComponent (A := A) (n : ℤ) ≃ₗ[R] A n := by
  let f : directSumNatComponent (A := A) (n : ℤ) →ₗ[R] A n :=
    { toFun := fun x => x.1 n
      map_add' := by intro x y; rfl
      map_smul' := by intro r x; rfl }
  let g : A n →ₗ[R] directSumNatComponent (A := A) (n : ℤ) :=
    { toFun := fun x => ⟨DirectSum.of A n x, by
        simp [directSumNatComponent, directSumComponent]
        ⟩
      map_add' := by
        intro x y
        apply Subtype.ext
        simp
      map_smul' := by
        intro r x
        apply Subtype.ext
        change DirectSum.of A n (r • x) = r • DirectSum.of A n x
        exact DirectSum.of_smul R n r x }
  exact { f with
    invFun := g
    left_inv := by
      intro x
      apply Subtype.ext
      have hx : (x : DirectSum ℕ A) ∈ directSumComponent (A := A) n := by
        simpa [directSumNatComponent] using x.property
      rcases hx with ⟨y, hy⟩
      change DirectSum.of A n (x.1 n) = x.1
      calc
        DirectSum.of A n (x.1 n) =
            DirectSum.of A n ((DirectSum.of A n y) n) := by rw [← hy]
        _ = DirectSum.of A n y := by simp
        _ = x.1 := hy
    right_inv := by
      intro x
      simp [f, g] }

def associatedGradedRingComponent
    {R : Type u} [CommRing R] (I : Ideal R) (n : ℕ) :
    AddSubgroup (associatedGradedRing I) :=
  directSumComponent (A := fun n => associatedGradedRingPiece I n) n


private def associatedGradedRingPieceMulAux
    {R : Type u} [CommRing R] (I : Ideal R) (i j : ℕ) :
    (I ^ i : Submodule R R) →ₗ[R] (I ^ j : Submodule R R) →ₗ[R]
      associatedGradedRingPiece I (i + j) := by
  exact {
    toFun := fun x => {
      toFun := fun y => Submodule.Quotient.mk ⟨(x : R) * (y : R), by
        rw [Ideal.IsTwoSided.pow_add]
        exact Ideal.mul_mem_mul x.property y.property⟩
      map_add' := by
        intro y z
        apply congrArg Submodule.Quotient.mk
        apply Subtype.ext
        exact mul_add (x : R) (y : R) (z : R)
      map_smul' := by
        intro r y
        rw [← Submodule.Quotient.mk_smul]
        apply congrArg Submodule.Quotient.mk
        apply Subtype.ext
        change (x : R) * (r * (y : R)) = r * ((x : R) * (y : R))
        ring
    }
    map_add' := by
      intro x y
      apply LinearMap.ext
      intro z
      apply congrArg Submodule.Quotient.mk
      apply Subtype.ext
      exact add_mul (x : R) (y : R) (z : R)
    map_smul' := by
      intro r x
      apply LinearMap.ext
      intro y
      change (Submodule.Quotient.mk _ : associatedGradedRingPiece I (i + j)) =
        r • (Submodule.Quotient.mk _ : associatedGradedRingPiece I (i + j))
      rw [← Submodule.Quotient.mk_smul]
      apply congrArg (fun z : (I ^ (i + j) : Submodule R R) =>
        (Submodule.Quotient.mk z : associatedGradedRingPiece I (i + j)))
      apply Subtype.ext
      change (r * (x : R)) * (y : R) = r * ((x : R) * (y : R))
      ring
  }

private def associatedGradedRingPieceMul
    {R : Type u} [CommRing R] (I : Ideal R) (i j : ℕ) :
    associatedGradedRingPiece I i → associatedGradedRingPiece I j →
      associatedGradedRingPiece I (i + j) := by
  intro x y
  refine Quotient.liftOn₂' x y (fun a b => associatedGradedRingPieceMulAux I i j a b) ?_
  intro a₁ a₂ b₁ b₂ ha hb
  apply (Submodule.Quotient.eq _).2
  rw [Submodule.quotientRel_def] at ha hb
  change (a₁ : R) - (b₁ : R) ∈ I ^ (i + 1) at ha
  change (a₂ : R) - (b₂ : R) ∈ I ^ (j + 1) at hb
  change (a₁ : R) * (a₂ : R) - (b₁ : R) * (b₂ : R) ∈ I ^ (i + j + 1)
  have h₁ : ((a₁ : R) - (b₁ : R)) * (a₂ : R) ∈ I ^ (i + j + 1) := by
    have h := Ideal.mul_mem_mul ha a₂.property
    rw [← Ideal.IsTwoSided.pow_add] at h
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h
  have h₂ : (b₁ : R) * ((a₂ : R) - (b₂ : R)) ∈ I ^ (i + j + 1) := by
    have h := Ideal.mul_mem_mul b₁.property hb
    rw [← Ideal.IsTwoSided.pow_add] at h
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h
  rw [show (a₁ : R) * (a₂ : R) - (b₁ : R) * (b₂ : R) =
      ((a₁ : R) - (b₁ : R)) * (a₂ : R) +
        (b₁ : R) * ((a₂ : R) - (b₂ : R)) by ring]
  exact (I ^ (i + j + 1) : Ideal R).add_mem h₁ h₂

private theorem associatedGradedRingPieceMul_mk
    {R : Type u} [CommRing R] (I : Ideal R) {i j : ℕ}
    (a : (I ^ i : Submodule R R)) (b : (I ^ j : Submodule R R)) :
    associatedGradedRingPieceMul I i j (Submodule.Quotient.mk a)
        (Submodule.Quotient.mk b) =
      (Submodule.Quotient.mk ⟨(a : R) * (b : R), by
        rw [Ideal.IsTwoSided.pow_add]
        exact Ideal.mul_mem_mul a.property b.property⟩ :
        associatedGradedRingPiece I (i + j)) := by
  rfl

private theorem associatedGradedRingPiece_cast_mk
    {R : Type u} [CommRing R] (I : Ideal R) {i j : ℕ} (h : i = j)
    (a : (I ^ i : Submodule R R)) :
    cast (congrArg (fun n => associatedGradedRingPiece I n) h)
        (Submodule.Quotient.mk a) =
      Submodule.Quotient.mk ⟨(a : R), by
        rw [← h]
        exact a.property⟩ := by
  cases h
  rfl

private theorem associatedGradedRingPiece_mk_heq
    {R : Type u} [CommRing R] (I : Ideal R) {i j : ℕ} (h : i = j)
    (a : (I ^ i : Submodule R R)) (b : (I ^ j : Submodule R R))
    (hab : (a : R) = (b : R)) :
    HEq (Submodule.Quotient.mk a : associatedGradedRingPiece I i)
      (Submodule.Quotient.mk b : associatedGradedRingPiece I j) := by
  apply heq_of_eqRec_eq
    (congrArg (fun n => associatedGradedRingPiece I n) h)
  cases h
  apply congrArg (fun z : (I ^ i : Submodule R R) =>
    (Submodule.Quotient.mk z : associatedGradedRingPiece I i))
  apply Subtype.ext
  exact hab

/-- The canonical ring operations on the associated graded ring. -/
@[instance_reducible] private noncomputable def associatedGradedRing_gcommRing_canonical
    {R : Type u} [CommRing R] (I : Ideal R) :
    DirectSum.GCommRing (associatedGradedRingPiece I) := by
  let one : associatedGradedRingPiece I 0 :=
    Submodule.Quotient.mk ⟨1, by simp⟩
  let : GradedMonoid.GOne (associatedGradedRingPiece I) := ⟨one⟩
  let : GradedMonoid.GMul (associatedGradedRingPiece I) :=
    ⟨@associatedGradedRingPieceMul R _ I⟩
  exact {
    mul := @associatedGradedRingPieceMul R _ I
    one := one
    one_mul := by
      rintro ⟨n, x⟩
      change GradedMonoid.mk 0 one * GradedMonoid.mk n x = GradedMonoid.mk n x
      have h : 0 + n = n := zero_add n
      apply Sigma.ext h
      refine Submodule.Quotient.induction_on _ x ?_
      intro a
      change HEq (associatedGradedRingPieceMul I 0 n one (Submodule.Quotient.mk a))
        (Submodule.Quotient.mk a)
      simp [one, associatedGradedRingPieceMul, Submodule.Quotient.mk,
        associatedGradedRingPieceMulAux]
      refine (heq_of_eqRec_eq
        (α := associatedGradedRingPiece I n)
        (β := associatedGradedRingPiece I (0 + n))
        (a := Submodule.Quotient.mk a)
        (b := Submodule.Quotient.mk ⟨(a : R), by rw [zero_add]; exact a.property⟩)
        (congrArg (fun k => associatedGradedRingPiece I k) h.symm)
        (associatedGradedRingPiece_cast_mk I h.symm a)).symm
    mul_one := by
      rintro ⟨n, x⟩
      change GradedMonoid.mk n x * GradedMonoid.mk 0 one = GradedMonoid.mk n x
      apply Sigma.ext (by
        change n + 0 = n
        exact add_zero n)
      refine Submodule.Quotient.induction_on _ x ?_
      intro a
      change HEq (associatedGradedRingPieceMul I n 0 (Submodule.Quotient.mk a) one)
        (Submodule.Quotient.mk a)
      simp [one, associatedGradedRingPieceMul, Submodule.Quotient.mk,
        associatedGradedRingPieceMulAux]
      rfl
    mul_assoc := by
      rintro ⟨i, x⟩ ⟨j, y⟩ ⟨k, z⟩
      change (GradedMonoid.mk i x * GradedMonoid.mk j y) * GradedMonoid.mk k z =
        GradedMonoid.mk i x * (GradedMonoid.mk j y * GradedMonoid.mk k z)
      apply Sigma.ext (add_assoc i j k)
      refine Submodule.Quotient.induction_on _ x ?_
      intro a
      refine Submodule.Quotient.induction_on _ y ?_
      intro b
      refine Submodule.Quotient.induction_on _ z ?_
      intro c
      change HEq (associatedGradedRingPieceMul I (i + j) k
          (associatedGradedRingPieceMul I i j
            (Submodule.Quotient.mk a) (Submodule.Quotient.mk b))
          (Submodule.Quotient.mk c))
        (associatedGradedRingPieceMul I i (j + k)
          (Submodule.Quotient.mk a)
          (associatedGradedRingPieceMul I j k
            (Submodule.Quotient.mk b) (Submodule.Quotient.mk c)))
      exact (associatedGradedRingPiece_mk_heq I (add_assoc i j k)
          (⟨((a : R) * (b : R)) * (c : R), by
            rw [Ideal.IsTwoSided.pow_add, Ideal.IsTwoSided.pow_add]
            exact Ideal.mul_mem_mul
              (Ideal.mul_mem_mul a.property b.property) c.property⟩)
          (⟨(a : R) * ((b : R) * (c : R)), by
            rw [Ideal.IsTwoSided.pow_add, Ideal.IsTwoSided.pow_add]
            exact Ideal.mul_mem_mul a.property
              (Ideal.mul_mem_mul b.property c.property)⟩) (by ring))
    natCast := fun n => Submodule.Quotient.mk ⟨n, by simp⟩
    natCast_zero := by
      apply (Submodule.Quotient.mk_eq_zero _).2
      simp
    natCast_succ := by
      intro n
      apply (Submodule.Quotient.eq _).2
      simp
    intCast := fun z => Submodule.Quotient.mk ⟨z, by simp⟩
    intCast_ofNat := by
      intro n
      apply (Submodule.Quotient.eq _).2
      simp
    intCast_negSucc_ofNat := by
      intro n
      apply (Submodule.Quotient.eq _).2
      simp
    mul_comm := by
      rintro ⟨i, x⟩ ⟨j, y⟩
      change GradedMonoid.mk i x * GradedMonoid.mk j y =
        GradedMonoid.mk j y * GradedMonoid.mk i x
      apply Sigma.ext (add_comm i j)
      refine Submodule.Quotient.induction_on _ x ?_
      intro a
      refine Submodule.Quotient.induction_on _ y ?_
      intro b
      change HEq (associatedGradedRingPieceMul I i j
          (Submodule.Quotient.mk a) (Submodule.Quotient.mk b))
        (associatedGradedRingPieceMul I j i
          (Submodule.Quotient.mk b) (Submodule.Quotient.mk a))
      simpa [associatedGradedRingPieceMul, Submodule.Quotient.mk,
        associatedGradedRingPieceMulAux, add_comm] using
        (associatedGradedRingPiece_mk_heq I (add_comm i j)
          (⟨(a : R) * (b : R), by
            rw [Ideal.IsTwoSided.pow_add]
            exact Ideal.mul_mem_mul a.property b.property⟩)
          (⟨(b : R) * (a : R), by
            rw [Ideal.IsTwoSided.pow_add]
            exact Ideal.mul_mem_mul b.property a.property⟩) (by ring))
    mul_zero := by
      intro i j a
      rw [← Submodule.Quotient.mk_zero]
      refine Submodule.Quotient.induction_on _ a ?_
      intro a
      change associatedGradedRingPieceMul I i j
          (Submodule.Quotient.mk a)
          (Submodule.Quotient.mk (0 : (I ^ j : Submodule R R))) =
        (0 : associatedGradedRingPiece I (i + j))
      simp [associatedGradedRingPieceMul, Submodule.Quotient.mk,
        associatedGradedRingPieceMulAux]
      apply (Submodule.Quotient.mk_eq_zero _).2
      simp
    zero_mul := by
      intro i j a
      rw [← Submodule.Quotient.mk_zero]
      refine Submodule.Quotient.induction_on _ a ?_
      intro a
      change associatedGradedRingPieceMul I i j
          (Submodule.Quotient.mk (0 : (I ^ i : Submodule R R)))
          (Submodule.Quotient.mk a) =
        (0 : associatedGradedRingPiece I (i + j))
      simp [associatedGradedRingPieceMul, Submodule.Quotient.mk,
        associatedGradedRingPieceMulAux]
      apply (Submodule.Quotient.mk_eq_zero _).2
      simp
    mul_add := by
      intro i j a b c
      refine Submodule.Quotient.induction_on _ a ?_
      intro a
      refine Submodule.Quotient.induction_on _ b ?_
      intro b
      refine Submodule.Quotient.induction_on _ c ?_
      intro c
      rw [← Submodule.Quotient.mk_add]
      apply (Submodule.Quotient.eq _).2
      change (a : R) * ((b : R) + (c : R)) -
          ((a : R) * (b : R) + (a : R) * (c : R)) ∈ I ^ (i + j + 1)
      rw [show (a : R) * ((b : R) + (c : R)) -
          ((a : R) * (b : R) + (a : R) * (c : R)) = 0 by ring]
      exact (I ^ (i + j + 1) : Ideal R).zero_mem
    add_mul := by
      intro i j a b c
      refine Submodule.Quotient.induction_on _ a ?_
      intro a
      refine Submodule.Quotient.induction_on _ b ?_
      intro b
      refine Submodule.Quotient.induction_on _ c ?_
      intro c
      rw [← Submodule.Quotient.mk_add]
      apply (Submodule.Quotient.eq _).2
      change ((a : R) + (b : R)) * (c : R) -
          ((a : R) * (c : R) + (b : R) * (c : R)) ∈ I ^ (i + j + 1)
      rw [show ((a : R) + (b : R)) * (c : R) -
          ((a : R) * (c : R) + (b : R) * (c : R)) = 0 by ring]
      exact (I ^ (i + j + 1) : Ideal R).zero_mem
  }

theorem associatedGradedRing_gcommRing_exists
    {R : Type u} [CommRing R] (I : Ideal R) :
    Nonempty (DirectSum.GCommRing (associatedGradedRingPiece I)) :=
  ⟨associatedGradedRing_gcommRing_canonical I⟩

noncomputable instance associatedGradedRing_gcommRing
    {R : Type u} [CommRing R] (I : Ideal R) :
    DirectSum.GCommRing (associatedGradedRingPiece I) :=
  associatedGradedRing_gcommRing_canonical I

private theorem associatedGradedModulePiece_cast_mk
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (I : Ideal R) {i j : ℕ} (h : i = j)
    (a : ((I ^ i : Submodule R R) • (⊤ : Submodule R M) : Submodule R M)) :
    cast (congrArg (fun n => associatedGradedModulePiece (M := M) I n) h)
        (Submodule.Quotient.mk a) =
      Submodule.Quotient.mk ⟨(a : M), by
        rw [← h]
        exact a.property⟩ := by
  cases h
  rfl

private theorem associatedGradedModulePiece_mk_heq
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (I : Ideal R) {i j : ℕ} (h : i = j)
    (a : ((I ^ i : Submodule R R) • (⊤ : Submodule R M) : Submodule R M))
    (b : ((I ^ j : Submodule R R) • (⊤ : Submodule R M) : Submodule R M))
    (hab : (a : M) = (b : M)) :
    HEq (Submodule.Quotient.mk a : associatedGradedModulePiece (M := M) I i)
      (Submodule.Quotient.mk b : associatedGradedModulePiece (M := M) I j) := by
  apply heq_of_eqRec_eq
    (congrArg (fun n => associatedGradedModulePiece (M := M) I n) h)
  cases h
  apply congrArg (fun z : ((I ^ i : Submodule R R) • (⊤ : Submodule R M) : Submodule R M) =>
    (Submodule.Quotient.mk z : associatedGradedModulePiece (M := M) I i))
  apply Subtype.ext
  exact hab

private noncomputable def associatedGradedModule_smul
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (I : Ideal R) : {i j : ℕ} → associatedGradedRingPiece I i →
      associatedGradedModulePiece (M := M) I j →
        associatedGradedModulePiece (M := M) I (i + j) := by
  intro i j a b
  refine Quotient.liftOn₂' a b (fun x y =>
    Submodule.Quotient.mk ⟨(x : R) • (y : M), ?_⟩) ?_
  · have h := Submodule.smul_mem_smul x.property y.property
    rw [← Submodule.smul_assoc, Ideal.smul_eq_mul,
      ← Ideal.IsTwoSided.pow_add] at h
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h
  · intro a₁ a₂ b₁ b₂ ha hb
    apply (Submodule.Quotient.eq _).2
    rw [Submodule.quotientRel_def] at ha hb
    change (a₁ : R) - (b₁ : R) ∈ I ^ (i + 1) at ha
    change (a₂ : M) - (b₂ : M) ∈ I ^ (j + 1) • (⊤ : Submodule R M) at hb
    change (a₁ : R) • (a₂ : M) - (b₁ : R) • (b₂ : M) ∈
      I ^ (i + j + 1) • (⊤ : Submodule R M)
    have h₁ : ((a₁ : R) - (b₁ : R)) • (a₂ : M) ∈
        I ^ (i + j + 1) • (⊤ : Submodule R M) := by
      have h := Submodule.smul_mem_smul ha a₂.property
      rw [← Submodule.smul_assoc, Ideal.smul_eq_mul,
        ← Ideal.IsTwoSided.pow_add] at h
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h
    have h₂ : (b₁ : R) • ((a₂ : M) - (b₂ : M)) ∈
        I ^ (i + j + 1) • (⊤ : Submodule R M) := by
      have h := Submodule.smul_mem_smul b₁.property hb
      rw [← Submodule.smul_assoc, Ideal.smul_eq_mul,
        ← Ideal.IsTwoSided.pow_add] at h
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h
    rw [show (a₁ : R) • (a₂ : M) - (b₁ : R) • (b₂ : M) =
        ((a₁ : R) - (b₁ : R)) • (a₂ : M) +
          (b₁ : R) • ((a₂ : M) - (b₂ : M)) by
        simp only [sub_smul, smul_sub]
        abel]
    exact Submodule.add_mem _ h₁ h₂

private theorem associatedGradedModule_smul_mk
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (I : Ideal R) {i j : ℕ}
    (a : (I ^ i : Submodule R R))
    (b : ((I ^ j : Submodule R R) • (⊤ : Submodule R M) : Submodule R M)) :
    associatedGradedModule_smul I (Submodule.Quotient.mk a)
      (Submodule.Quotient.mk b)
      = (Submodule.Quotient.mk ⟨(a : R) • (b : M), by
        have h := Submodule.smul_mem_smul a.property b.property
        rw [← Submodule.smul_assoc, Ideal.smul_eq_mul,
          ← Ideal.IsTwoSided.pow_add] at h
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h⟩ :
        associatedGradedModulePiece (M := M) I (i + j)) := by
  simp [associatedGradedModule_smul, Submodule.Quotient.mk]

@[reducible] private noncomputable def associatedGradedModule_gmulAction
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (I : Ideal R) : GradedMonoid.GMulAction (associatedGradedRingPiece I)
      (fun n => associatedGradedModulePiece (M := M) I n) := by
  let one : associatedGradedRingPiece I 0 :=
    Submodule.Quotient.mk ⟨1, by simp⟩
  let gsmul : GradedMonoid.GSMul (associatedGradedRingPiece I)
      (fun n => associatedGradedModulePiece (M := M) I n) :=
    { smul := associatedGradedModule_smul I }
  exact {
    toGSMul := gsmul
    one_smul := by
      rintro ⟨j, b⟩
      change GradedMonoid.mk 0 one • GradedMonoid.mk j b = _
      apply Sigma.ext (zero_add j)
      refine Submodule.Quotient.induction_on _ b ?_
      intro y
      change HEq (associatedGradedModule_smul I (i := 0) (j := j) one
          (Submodule.Quotient.mk y)) (Submodule.Quotient.mk y)
      rw [associatedGradedModule_smul_mk]
      exact associatedGradedModulePiece_mk_heq I (zero_add j)
        (⟨(1 : R) • (y : M), by
          have h := Submodule.smul_mem_smul
            (show (1 : R) ∈ (I ^ 0 : Submodule R R) by simp) y.property
          rw [← Submodule.smul_assoc, Ideal.smul_eq_mul,
            ← Ideal.IsTwoSided.pow_add] at h
          simp only [one_smul, zero_add] at h ⊢
          exact h⟩)
        (⟨(y : M), y.property⟩) (by simp)
    mul_smul := by
      rintro ⟨i, a⟩ ⟨j, a'⟩ ⟨k, b⟩
      change (GradedMonoid.mk i a * GradedMonoid.mk j a') •
          GradedMonoid.mk k b =
        GradedMonoid.mk i a • (GradedMonoid.mk j a' • GradedMonoid.mk k b)
      apply Sigma.ext (add_assoc i j k)
      refine Submodule.Quotient.induction_on _ a ?_
      intro a
      refine Submodule.Quotient.induction_on _ a' ?_
      intro a'
      refine Submodule.Quotient.induction_on _ b ?_
      intro b
      change HEq
        (associatedGradedModule_smul I (i := i + j) (j := k)
          (associatedGradedRingPieceMul I i j
            (Submodule.Quotient.mk a) (Submodule.Quotient.mk a'))
          (Submodule.Quotient.mk b))
        (associatedGradedModule_smul I (i := i) (j := j + k)
          (Submodule.Quotient.mk a)
          (associatedGradedModule_smul I (i := j) (j := k)
            (Submodule.Quotient.mk a') (Submodule.Quotient.mk b)))
      rw [associatedGradedRingPieceMul_mk]
      rw [associatedGradedModule_smul_mk, associatedGradedModule_smul_mk,
        associatedGradedModule_smul_mk]
      exact associatedGradedModulePiece_mk_heq I (add_assoc i j k)
        (⟨((a : R) * (a' : R)) • (b : M), by
          have h := Submodule.smul_mem_smul
            (show (a : R) * (a' : R) ∈ (I ^ (i + j) : Submodule R R) by
              rw [Ideal.IsTwoSided.pow_add]
              exact Ideal.mul_mem_mul a.property a'.property) b.property
          simpa [← Submodule.smul_assoc, Ideal.smul_eq_mul,
            ← Ideal.IsTwoSided.pow_add, Nat.add_assoc, Nat.add_comm,
            Nat.add_left_comm] using h⟩)
        (⟨(a : R) • ((a' : R) • (b : M)), by
          have h := Submodule.smul_mem_smul
            (show (a : R) * (a' : R) ∈ (I ^ (i + j) : Submodule R R) by
              rw [Ideal.IsTwoSided.pow_add]
              exact Ideal.mul_mem_mul a.property a'.property) b.property
          simpa [← Submodule.smul_assoc, Ideal.smul_eq_mul,
            ← Ideal.IsTwoSided.pow_add, smul_smul, Nat.add_assoc,
            Nat.add_comm, Nat.add_left_comm] using h⟩)
        (by
          change ((a : R) * (a' : R)) • (b : M) =
            (a : R) • ((a' : R) • (b : M))
          rw [smul_smul]) }

/-- The canonical graded-module action of `Gr_I(R)` on `Gr_I(M)`. -/
@[instance_reducible] private noncomputable def associatedGradedModule_gmodule_canonical
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (I : Ideal R) :
    DirectSum.Gmodule (associatedGradedRingPiece I)
      (fun n => associatedGradedModulePiece (M := M) I n) := by
  let gmulAction : GradedMonoid.GMulAction (associatedGradedRingPiece I)
      (fun n => associatedGradedModulePiece (M := M) I n) :=
    associatedGradedModule_gmulAction I
  let gdistrib : DirectSum.GdistribMulAction (associatedGradedRingPiece I)
      (fun n => associatedGradedModulePiece (M := M) I n) :=
    { toGMulAction := gmulAction
      smul_add := by
        have hsmul : gmulAction.toGSMul =
            ({ smul := associatedGradedModule_smul I } :
              GradedMonoid.GSMul (associatedGradedRingPiece I)
                (fun n => associatedGradedModulePiece (M := M) I n)) := by
          rfl
        intro i j a b c
        refine Submodule.Quotient.induction_on _ a ?_
        intro a
        refine Submodule.Quotient.induction_on _ b ?_
        intro b
        refine Submodule.Quotient.induction_on _ c ?_
        intro c
        rw [← Submodule.Quotient.mk_add]
        rw [hsmul]
        change associatedGradedModule_smul I (Submodule.Quotient.mk a)
            (Submodule.Quotient.mk (b + c)) =
          associatedGradedModule_smul I (Submodule.Quotient.mk a)
              (Submodule.Quotient.mk b) +
            associatedGradedModule_smul I (Submodule.Quotient.mk a)
              (Submodule.Quotient.mk c)
        apply (Submodule.Quotient.eq _).2
        change (a : R) • ((b : M) + (c : M)) -
            ((a : R) • (b : M) + (a : R) • (c : M)) ∈
          I ^ (i + j + 1) • (⊤ : Submodule R M)
        rw [show (a : R) • ((b : M) + (c : M)) -
            ((a : R) • (b : M) + (a : R) • (c : M)) = 0 by
          rw [smul_add, sub_self]]
        exact Submodule.zero_mem _
      smul_zero := by
        intro i j a
        refine Submodule.Quotient.induction_on _ a ?_
        intro a
        simp [Submodule.Quotient.mk]
        apply (Submodule.Quotient.mk_eq_zero _).2
        simp }
  exact { gdistrib with
    smul := fun {i j} => associatedGradedModule_smul I
    add_smul := by
      intro i j a a' b
      refine Submodule.Quotient.induction_on _ a ?_
      intro a
      refine Submodule.Quotient.induction_on _ a' ?_
      intro a'
      refine Submodule.Quotient.induction_on _ b ?_
      intro b
      rw [← Submodule.Quotient.mk_add]
      rw [associatedGradedModule_smul_mk, associatedGradedModule_smul_mk,
        associatedGradedModule_smul_mk]
      apply (Submodule.Quotient.eq _).2
      change ((a : R) + (a' : R)) • (b : M) -
          ((a : R) • (b : M) + (a' : R) • (b : M)) ∈
        I ^ (i + j + 1) • (⊤ : Submodule R M)
      rw [show ((a : R) + (a' : R)) • (b : M) -
          ((a : R) • (b : M) + (a' : R) • (b : M)) = 0 by
        rw [add_smul, sub_self]]
      exact Submodule.zero_mem _
    zero_smul := by
      intro i j b
      refine Submodule.Quotient.induction_on _ b ?_
      intro b
      simp [associatedGradedModule_smul, Submodule.Quotient.mk]
      apply (Submodule.Quotient.mk_eq_zero _).2
      simp }

/-- The canonical graded-module action of `Gr_I(R)` on `Gr_I(M)`. -/
theorem associatedGradedModule_gmodule_exists
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (I : Ideal R) :
    Nonempty (DirectSum.Gmodule (associatedGradedRingPiece I)
      (fun n => associatedGradedModulePiece (M := M) I n)) :=
  ⟨associatedGradedModule_gmodule_canonical I⟩
/-
  let smul : {i j : ℕ} → associatedGradedRingPiece I i →
      associatedGradedModulePiece (M := M) I j →
        associatedGradedModulePiece (M := M) I (i + j)) := by
    intro i j a b
    refine Quotient.liftOn₂' a b (fun x y =>
      Submodule.Quotient.mk ⟨(x : R) • (y : M), ?_⟩) ?_
    · have h := Submodule.smul_mem_smul x.property y.property
      rw [← Submodule.smul_assoc, Ideal.smul_eq_mul,
        ← Ideal.IsTwoSided.pow_add] at h
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h
    · intro a₁ a₂ b₁ b₂ ha hb
      apply (Submodule.Quotient.eq _).2
      rw [Submodule.quotientRel_def] at ha hb
      change (a₁ : R) - (b₁ : R) ∈ I ^ (i + 1) at ha
      change (a₂ : M) - (b₂ : M) ∈ I ^ (j + 1) • (⊤ : Submodule R M) at hb
      change (a₁ : R) • (a₂ : M) - (b₁ : R) • (b₂ : M) ∈
        I ^ (i + j + 1) • (⊤ : Submodule R M)
      have h₁ : ((a₁ : R) - (b₁ : R)) • (a₂ : M) ∈
          I ^ (i + j + 1) • (⊤ : Submodule R M) := by
        have h := Submodule.smul_mem_smul ha a₂.property
        rw [← Submodule.smul_assoc, Ideal.smul_eq_mul,
          ← Ideal.IsTwoSided.pow_add] at h
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h
      have h₂ : (b₁ : R) • ((a₂ : M) - (b₂ : M)) ∈
          I ^ (i + j + 1) • (⊤ : Submodule R M) := by
        have h := Submodule.smul_mem_smul b₁.property hb
        rw [← Submodule.smul_assoc, Ideal.smul_eq_mul,
          ← Ideal.IsTwoSided.pow_add] at h
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h
      rw [show (a₁ : R) • (a₂ : M) - (b₁ : R) • (b₂ : M) =
          ((a₁ : R) - (b₁ : R)) • (a₂ : M) +
            (b₁ : R) • ((a₂ : M) - (b₂ : M)) by
          simp only [sub_smul, smul_sub]
          abel]
      exact Submodule.add_mem _ h₁ h₂
  let one : associatedGradedRingPiece I 0 :=
    Submodule.Quotient.mk ⟨1, by simp⟩
  let gsmul : GradedMonoid.GSMul (associatedGradedRingPiece I)
      (fun n => associatedGradedModulePiece (M := M) I n) :=
    { smul := smul }
  let gmulAction : GradedMonoid.GMulAction (associatedGradedRingPiece I)
      (fun n => associatedGradedModulePiece (M := M) I n) :=
    { gsmul with
      one_smul := by
        rintro ⟨j, b⟩
        change GradedMonoid.mk 0 one • GradedMonoid.mk j b = _
        apply Sigma.ext (zero_add j)
        refine Submodule.Quotient.induction_on _ b ?_
        intro y
        change HEq (smul (i := 0) (j := j) one (Submodule.Quotient.mk y))
          (Submodule.Quotient.mk y)
        simp [one, smul, Submodule.Quotient.mk]
        refine (heq_of_eqRec_eq
          (α := associatedGradedModulePiece (M := M) I j)
          (β := associatedGradedModulePiece (M := M) I (0 + j))
          (a := Submodule.Quotient.mk y)
          (b := Submodule.Quotient.mk ⟨(y : M), by rw [zero_add]; exact y.property⟩)
          (congrArg (fun k => associatedGradedModulePiece (M := M) I k)
            (zero_add j).symm)
          (associatedGradedModulePiece_cast_mk I (zero_add j).symm y)).symm
      mul_smul := by
        rintro ⟨i, a⟩ ⟨j, a'⟩ ⟨k, b⟩
        change (GradedMonoid.mk i a * GradedMonoid.mk j a') •
            GradedMonoid.mk k b =
          GradedMonoid.mk i a • (GradedMonoid.mk j a' • GradedMonoid.mk k b)
        apply Sigma.ext (add_assoc i j k)
        refine Submodule.Quotient.induction_on _ a ?_
        intro a
        refine Submodule.Quotient.induction_on _ a' ?_
        intro a'
        refine Submodule.Quotient.induction_on _ b ?_
        intro b
        change HEq
          (smul (i := i + j) (j := k)
            (associatedGradedRingPieceMul I i j
              (Submodule.Quotient.mk a) (Submodule.Quotient.mk a'))
            (Submodule.Quotient.mk b))
          (smul (i := i) (j := j + k) (Submodule.Quotient.mk a)
            (smul (i := j) (j := k) (Submodule.Quotient.mk a')
              (Submodule.Quotient.mk b)))
        simp [smul, associatedGradedRingPieceMul, Submodule.Quotient.mk,
          associatedGradedRingPieceMulAux]
        exact associatedGradedModulePiece_mk_heq I (add_assoc i j k)
          (⟨((a : R) * (a' : R)) • (b : M), by
            have h := Submodule.smul_mem_smul
              (show (a : R) * (a' : R) ∈ (I ^ (i + j) : Submodule R R) by
                rw [Ideal.IsTwoSided.pow_add]
                exact Ideal.mul_mem_mul a.property a'.property) b.property
            simpa [← Submodule.smul_assoc, Ideal.smul_eq_mul,
              ← Ideal.IsTwoSided.pow_add, Nat.add_assoc, Nat.add_comm,
              Nat.add_left_comm] using h⟩)
          (⟨(a : R) • ((a' : R) • (b : M)), by
            have h := Submodule.smul_mem_smul
              (show (a : R) * (a' : R) ∈ (I ^ (i + j) : Submodule R R) by
                rw [Ideal.IsTwoSided.pow_add]
                exact Ideal.mul_mem_mul a.property a'.property) b.property
            simpa [← Submodule.smul_assoc, Ideal.smul_eq_mul,
              ← Ideal.IsTwoSided.pow_add, smul_smul, Nat.add_assoc,
              Nat.add_comm, Nat.add_left_comm] using h⟩)
          (by simp only [Subtype.coe_mk]; rw [smul_smul]) }
  let gdistrib : DirectSum.GdistribMulAction (associatedGradedRingPiece I)
      (fun n => associatedGradedModulePiece (M := M) I n) :=
    { gmulAction with
      smul_add := by
        intro i j a b c
        refine Submodule.Quotient.induction_on _ a ?_
        intro a
        refine Submodule.Quotient.induction_on _ b ?_
        intro b
        refine Submodule.Quotient.induction_on _ c ?_
        intro c
        rw [← Submodule.Quotient.mk_add]
        apply (Submodule.Quotient.eq _).2
        change (a : R) • ((b : M) + (c : M)) -
            ((a : R) • (b : M) + (a : R) • (c : M)) ∈
          I ^ (i + j + 1) • (⊤ : Submodule R M)
        rw [show (a : R) • ((b : M) + (c : M)) -
            ((a : R) • (b : M) + (a : R) • (c : M)) = 0 by
          rw [smul_add, sub_self]]
        exact Submodule.zero_mem _
      smul_zero := by
        intro i j a
        rw [← Submodule.Quotient.mk_zero]
        refine Submodule.Quotient.induction_on _ a ?_
        intro a
        simp only [gmulAction, gsmul]
        change smul (i := i) (j := 0) (Submodule.Quotient.mk a)
            (Submodule.Quotient.mk
              (0 : ((I ^ 0 : Submodule R R) • (⊤ : Submodule R M) :
                Submodule R M))) = 0
        simp [smul, Submodule.Quotient.mk]
        apply (Submodule.Quotient.mk_eq_zero _).2
        simp
      }
  exact ⟨{ gdistrib with
    add_smul := by
      intro i j a a' b
      refine Submodule.Quotient.induction_on _ a ?_
      intro a
      refine Submodule.Quotient.induction_on _ a' ?_
      intro a'
      refine Submodule.Quotient.induction_on _ b ?_
      intro b
      rw [← Submodule.Quotient.mk_add]
      apply (Submodule.Quotient.eq _).2
      change ((a : R) + (a' : R)) • (b : M) -
          ((a : R) • (b : M) + (a' : R) • (b : M)) ∈
        I ^ (i + j + 1) • (⊤ : Submodule R M)
      rw [show ((a : R) + (a' : R)) • (b : M) -
          ((a : R) • (b : M) + (a' : R) • (b : M)) = 0 by
        rw [add_smul, sub_self]]
      exact Submodule.zero_mem _
    zero_smul := by
      intro i j b
      rw [← Submodule.Quotient.mk_zero]
      refine Submodule.Quotient.induction_on _ b ?_
      intro b
      simp only [gmulAction, gsmul]
      change smul (i := 0) (j := j)
          (Submodule.Quotient.mk (0 : (I ^ 0 : Submodule R R)))
          (Submodule.Quotient.mk b) = 0
      simp [smul, Submodule.Quotient.mk]
      apply (Submodule.Quotient.mk_eq_zero _).2
      simp }⟩

-/

noncomputable instance associatedGradedModule_gmodule
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (I : Ideal R) :
    DirectSum.Gmodule (associatedGradedRingPiece I)
      (fun n => associatedGradedModulePiece (M := M) I n) :=
  associatedGradedModule_gmodule_canonical I

private theorem associatedGradedModule_gmodule_canonical_smul_mk
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (I : Ideal R) {i j : ℕ}
    (a : (I ^ i : Submodule R R))
    (b : ((I ^ j : Submodule R R) • (⊤ : Submodule R M) : Submodule R M)) :
    (associatedGradedModule_gmodule I).toGdistribMulAction.toGMulAction.toGSMul.smul
        (Submodule.Quotient.mk a : associatedGradedRingPiece I i)
        (Submodule.Quotient.mk b : associatedGradedModulePiece (M := M) I j) =
      (Submodule.Quotient.mk ⟨(a : R) • (b : M), by
        have h := Submodule.smul_mem_smul a.property b.property
        rw [← Submodule.smul_assoc, Ideal.smul_eq_mul,
          ← Ideal.IsTwoSided.pow_add] at h
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h⟩ :
        associatedGradedModulePiece (M := M) I (i + j)) := by
  change associatedGradedModule_smul I (Submodule.Quotient.mk a)
      (Submodule.Quotient.mk b) = _
  exact associatedGradedModule_smul_mk I a b

/-- The associated graded module is finite over the associated graded ring. -/
theorem associatedGradedModule_finite
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [IsNoetherianRing R] [Module.Finite R M] (I : Ideal R) :
    Module.Finite (associatedGradedRing I) (associatedGradedModule (M := M) I) := by
  sorry

/- The degreewise length function used by the ideal Hilbert function. -/
abbrev idealPowerPiece
    {R : Type u} [CommRing R] (I : Ideal R) (M : Type v)
    [AddCommGroup M] [Module R M] (n : ℕ) : Type v :=
  associatedGradedModulePiece (M := M) I n

def idealHilbertFunction
    {R : Type u} [CommRing R] (I : Ideal R) (M : Type v)
    [AddCommGroup M] [Module R M] (n : ℕ) : ℕ :=
  (Module.length R (associatedGradedModulePiece (M := M) I n)).toNat

theorem associatedGradedModulePiece_length_eq_idealHilbertFunction
    {R : Type u} [CommRing R] (I : Ideal R) (M : Type v)
    [AddCommGroup M] [Module R M] (n : ℕ) :
    (Module.length R (associatedGradedModulePiece (M := M) I n)).toNat =
      idealHilbertFunction I M n := by
  rfl

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
  intro n
  let _ : Module (degreeZeroSubring G) (𝓜.component n) :=
    gradedComponentDegreeZeroModule G 𝓜 n
  exact Formalization.Books.Algebra.Unit56.graded_module_component_finite
    G 𝓜 n (by intro c y; rfl)

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

theorem associatedGradedRingComponent_graded
    {R : Type u} [CommRing R] (I : Ideal R) :
    SetLike.GradedMonoid (associatedGradedRingComponent I) := by
  refine { one_mem := ?_, mul_mem := ?_ }
  · change (1 : associatedGradedRing I) ∈
      directSumComponent (A := fun n => associatedGradedRingPiece I n) 0
    refine ⟨GradedMonoid.GOne.one, ?_⟩
    rfl
  · intro i j x y hx hy
    rcases hx with ⟨x, rfl⟩
    rcases hy with ⟨y, rfl⟩
    refine ⟨@GradedMonoid.GMul.mul ℕ
      (fun n => associatedGradedRingPiece I n) _ _ _ _ x y, ?_⟩
    rw [DirectSum.of_mul_of]

noncomputable def associatedGradedRingData
    {R : Type u} [CommRing R] (I : Ideal R) :
    GradedRingData (associatedGradedRing I) := by
  let D : DirectSum.Decomposition (associatedGradedRingComponent I) :=
    directSumComponent_decomposition
  let G : SetLike.GradedMonoid (associatedGradedRingComponent I) :=
    associatedGradedRingComponent_graded I
  exact ⟨associatedGradedRingComponent I,
    { one_mem := G.one_mem, mul_mem := G.mul_mem,
      decompose' := D.decompose', left_inv := D.left_inv,
      right_inv := D.right_inv }⟩

def associatedGradedModuleComponent
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (I : Ideal R) (d : ℤ) : AddSubgroup (associatedGradedModule (M := M) I) :=
  directSumNatComponent
    (A := fun n => associatedGradedModulePiece (M := M) I n) d

theorem associatedGradedModuleComponent_gradedSMul
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (I : Ideal R) :
    SetLike.GradedSMul (associatedGradedRingComponent I)
      (associatedGradedModuleComponent I (M := M)) := by
  refine { smul_mem := ?_ }
  intro i j x y hx hy
  rcases hx with ⟨a, rfl⟩
  by_cases hj : 0 ≤ j
  · have hy' : (y : associatedGradedModule (M := M) I) ∈
        directSumComponent
          (A := fun n => associatedGradedModulePiece (M := M) I n) j.toNat := by
      simpa [associatedGradedModuleComponent, directSumNatComponent, hj] using hy
    rcases hy' with ⟨b, hb⟩
    have hcast : ((i + j.toNat : ℕ) : ℤ) = (i : ℤ) + j := by
      simp [Int.toNat_of_nonneg hj]
    have hpos : 0 ≤ (i : ℤ) + j := by omega
    have htoNat : ((i : ℤ) + j).toNat = i + j.toNat := by
      apply Int.ofNat_inj.mp
      rw [Int.toNat_of_nonneg hpos]
      exact hcast.symm
    have hsmul :
        (DirectSum.of (fun n => associatedGradedRingPiece I n) i a) • y =
          DirectSum.of
            (fun n => associatedGradedModulePiece (M := M) I n)
            (i + j.toNat)
            ((associatedGradedModule_gmodule I).toGdistribMulAction.toGMulAction.toGSMul.smul
              a b) := by
      rw [← hb]
      simp [vadd_eq_add]
    rw [hsmul]
    change DirectSum.of
        (fun n => associatedGradedModulePiece (M := M) I n)
        (i + j.toNat)
        ((associatedGradedModule_gmodule I).toGdistribMulAction.toGMulAction.toGSMul.smul a b) ∈
      if 0 ≤ (i : ℤ) + j then
        directSumComponent
          (A := fun n => associatedGradedModulePiece (M := M) I n)
          ((i : ℤ) + j).toNat else ⊥
    rw [if_pos hpos, htoNat]
    exact ⟨_, rfl⟩
  · have hy0 : (y : associatedGradedModule (M := M) I) = 0 := by
      simp [associatedGradedModuleComponent, directSumNatComponent, hj] at hy
      exact hy
    have hzero :
        (DirectSum.of (fun n => associatedGradedRingPiece I n) i a :
            associatedGradedRing I) •
            (0 : associatedGradedModule (M := M) I) = 0 := by
      change DirectSum.Gmodule.smulAddMonoidHom
          (associatedGradedRingPiece I)
          (fun n => associatedGradedModulePiece (M := M) I n)
          (DirectSum.of (fun n => associatedGradedRingPiece I n) i a) 0 = 0
      exact (DirectSum.Gmodule.smulAddMonoidHom
        (associatedGradedRingPiece I)
        (fun n => associatedGradedModulePiece (M := M) I n)
        (DirectSum.of (fun n => associatedGradedRingPiece I n) i a)).map_zero
    rw [hy0, hzero]
    exact (associatedGradedModuleComponent I (M := M) ((i : ℤ) + j)).zero_mem

noncomputable def associatedGradedModuleData
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (I : Ideal R) :
    GradedModuleData (associatedGradedRingData I)
      (associatedGradedModule (M := M) I) := by
  let D : DirectSum.Decomposition
      (associatedGradedModuleComponent I (M := M)) :=
    directSumNatComponent_decomposition
  exact ⟨associatedGradedModuleComponent I (M := M), D, by
      change SetLike.GradedSMul (associatedGradedRingComponent I)
        (associatedGradedModuleComponent I (M := M))
      exact associatedGradedModuleComponent_gradedSMul I⟩

theorem associatedGradedModule_external_smul_of_of
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (I : Ideal R) {i j : ℕ}
    (a : associatedGradedRingPiece I i)
    (b : associatedGradedModulePiece (M := M) I j) :
    (DirectSum.of (fun n => associatedGradedRingPiece I n) i a :
        associatedGradedRing I) •
        (DirectSum.of (fun n => associatedGradedModulePiece (M := M) I n)
          j b : associatedGradedModule (M := M) I) =
      DirectSum.of
        (fun n => associatedGradedModulePiece (M := M) I n)
        (i +ᵥ j)
          ((associatedGradedModule_gmodule I).toGdistribMulAction.toGMulAction.toGSMul.smul a b) := by
    simp [vadd_eq_add]

theorem associatedGradedRingData_generatedInDegreeOne
    {R : Type u} [CommRing R] (I : Ideal R) :
    GeneratedInDegreeOne (associatedGradedRingData I) := by
  let : GradedRing (associatedGradedRingComponent I) :=
    (associatedGradedRingData I).graded
  let : GradedRing (associatedGradedRingData I).component :=
    (associatedGradedRingData I).graded
  let : Algebra (degreeZeroSubring (associatedGradedRingData I))
      (associatedGradedRing I) :=
    Algebra.ofSubsemiring (degreeZeroSubring (associatedGradedRingData I))
  let f : associatedGradedRingPiece I 1 → associatedGradedRing I :=
    fun x => DirectSum.of (fun n => associatedGradedRingPiece I n) 1 x
  have hf : ∀ x, IsHomogeneousElement (associatedGradedRingData I) (f x) ∧
      f x ∈ irrelevantIdeal (associatedGradedRingData I) := by
    intro x
    refine ⟨⟨1, ?_⟩, ?_⟩
    · exact ⟨x, rfl⟩
    · exact HomogeneousIdeal.mem_irrelevant_of_mem
        (𝒜 := associatedGradedRingComponent I) (by omega) ⟨x, rfl⟩
  have hgen : Algebra.adjoin (degreeZeroSubring (associatedGradedRingData I))
      (Set.range f) = (⊤ : Subalgebra (degreeZeroSubring (associatedGradedRingData I))
        (associatedGradedRing I)) := by
    let P := Algebra.adjoin (degreeZeroSubring (associatedGradedRingData I))
      (Set.range f)
    have hpow : ∀ n : ℕ, ∀ x : R, ∀ hx : x ∈ I ^ n,
        DirectSum.of (fun n => associatedGradedRingPiece I n) n
            (Submodule.Quotient.mk ⟨x, hx⟩) ∈ P := by
      intro n x hx
      exact Submodule.pow_induction_on_left' I
        (C := fun n x hx =>
          DirectSum.of (fun n => associatedGradedRingPiece I n) n
              (Submodule.Quotient.mk ⟨x, hx⟩) ∈ P)
        (algebraMap := by
          intro r
          let q : associatedGradedRingPiece I 0 :=
            Submodule.Quotient.mk ⟨algebraMap R R r, by simp⟩
          have hq : (DirectSum.of
              (fun n => associatedGradedRingPiece I n) 0 q : associatedGradedRing I) ∈ P := by
            have hzero : (DirectSum.of
                (fun n => associatedGradedRingPiece I n) 0 q : associatedGradedRing I) ∈
                (associatedGradedRingData I).component 0 := by
              change (DirectSum.of
                  (fun n => associatedGradedRingPiece I n) 0 q : associatedGradedRing I) ∈
                associatedGradedRingComponent I 0
              exact ⟨q, rfl⟩
            let hz : degreeZeroSubring (associatedGradedRingData I) :=
              ⟨(DirectSum.of (fun n => associatedGradedRingPiece I n) 0 q :
                  associatedGradedRing I), hzero⟩
            have hq' := P.algebraMap_mem hz
            change (hz : associatedGradedRing I) ∈ P at hq'
            have hq'' : (DirectSum.of
                (fun n => associatedGradedRingPiece I n) 0 q : associatedGradedRing I) ∈ P := by
              simpa only [hz] using hq'
            simpa [q] using hq''
          exact hq)
        (add := by
          intro x y n hx hy h₁ h₂
          change (DirectSum.of (fun n => associatedGradedRingPiece I n) n)
              (Submodule.Quotient.mk
                ((⟨x, hx⟩ : (I ^ n : Submodule R R)) +
                  (⟨y, hy⟩ : (I ^ n : Submodule R R)))) ∈ P
          rw [Submodule.Quotient.mk_add, map_add]
          exact P.add_mem h₁ h₂)
        (mem_mul := by
          intro m hm n x hx hxn
          have hm' : m ∈ I ^ 1 := by simpa using hm
          have hmP : f (Submodule.Quotient.mk ⟨m, hm'⟩) ∈ P :=
            Algebra.subset_adjoin
              (Set.mem_range.mpr ⟨Submodule.Quotient.mk ⟨m, hm'⟩, rfl⟩)
          have hmul := P.mul_mem hmP hxn
          rw [DirectSum.of_mul_of] at hmul
          change (DirectSum.of (fun n => associatedGradedRingPiece I n) (1 + n))
              (associatedGradedRingPieceMul I 1 n
                (Submodule.Quotient.mk ⟨m, hm'⟩)
                (Submodule.Quotient.mk ⟨x, hx⟩)) ∈ P at hmul
          have hpiece := associatedGradedRingPieceMul_mk I
            (a := (⟨m, hm'⟩ : (I ^ 1 : Submodule R R)))
            (b := (⟨x, hx⟩ : (I ^ n : Submodule R R)))
          have hmul' :
              (DirectSum.of (fun n => associatedGradedRingPiece I n) (1 + n))
                  (Submodule.Quotient.mk ⟨m * x, by
                    rw [Ideal.IsTwoSided.pow_add]
                    exact Ideal.mul_mem_mul hm' hx⟩) ∈ P := by
            rw [← hpiece]
            exact hmul
          have hindex : 1 + n = n.succ := by omega
          have hp₂ : m * x ∈ I ^ n.succ := by
            have hpow : I ^ n.succ = I ^ 1 * I ^ n := by
              calc
                I ^ n.succ = I ^ (1 + n) := by
                  congr 1
                  omega
                _ = I ^ 1 * I ^ n := Ideal.IsTwoSided.pow_add 1 n
            rw [hpow]
            exact Ideal.mul_mem_mul hm' hx
          let a : (I ^ (1 + n) : Submodule R R) := ⟨m * x, by
            rw [Ideal.IsTwoSided.pow_add]
            exact Ideal.mul_mem_mul hm' hx⟩
          let b : (I ^ n.succ : Submodule R R) := ⟨m * x, hp₂⟩
          have hval :
              (DirectSum.of (fun n => associatedGradedRingPiece I n) (1 + n)
                (Submodule.Quotient.mk a)) =
                DirectSum.of (fun n => associatedGradedRingPiece I n) n.succ
                  (Submodule.Quotient.mk b) := by
            apply DirectSum.of_eq_of_gradedMonoid_eq
            apply Sigma.ext hindex
            exact associatedGradedRingPiece_mk_heq I hindex a b rfl
          have hmul_a :
              (DirectSum.of (fun n => associatedGradedRingPiece I n) (1 + n)
                (Submodule.Quotient.mk a)) ∈ P := by
            change (DirectSum.of (fun n => associatedGradedRingPiece I n) (1 + n)
              (Submodule.Quotient.mk a)) ∈ P at hmul'
            exact hmul'
          change (DirectSum.of (fun n => associatedGradedRingPiece I n) n.succ
            (Submodule.Quotient.mk b)) ∈ P
          rw [← hval]
          exact hmul_a)
        hx
    apply top_unique
    intro z hz
    clear hz
    induction z using DirectSum.Decomposition.inductionOn
      (ℳ := (associatedGradedRingData I).component) with
    | zero => exact P.zero_mem
    | @homogeneous n z =>
        rcases z.property with ⟨a, ha⟩
        rw [← ha]
        refine Submodule.Quotient.induction_on _ a ?_
        intro a
        exact hpow n (a : R) a.property
    | add z w hz hw => exact P.add_mem hz hw
  refine ⟨Set.range f, ?_, ?_⟩
  · intro x hx
    rcases Set.mem_range.mp hx with ⟨i, rfl⟩
    change DirectSum.of (fun n => associatedGradedRingPiece I n) 1 i ∈
      directSumComponent (A := fun n => associatedGradedRingPiece I n) 1
    exact ⟨i, rfl⟩
  · exact (sPlus_generated_iff (associatedGradedRingData I) f hf).mp hgen

instance associatedGradedModuleData_component_module
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (I : Ideal R) (d : ℤ) :
    Module R ((associatedGradedModuleData (M := M) I).component d) := by
  change Module R
    (directSumNatComponent
      (A := fun n => associatedGradedModulePiece (M := M) I n) d)
  infer_instance

noncomputable def associatedGradedModuleComponentLinearEquiv
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (I : Ideal R) (n : ℕ) :
    (associatedGradedModuleData (M := M) I).component (n : ℤ) ≃ₗ[R]
    associatedGradedModulePiece (M := M) I n :=
  by
    change directSumNatComponent
      (A := fun n => associatedGradedModulePiece (M := M) I n) (n : ℤ) ≃ₗ[R]
      associatedGradedModulePiece (M := M) I n
    exact directSumNatComponent_linearEquiv n

theorem associatedGradedModuleComponent_length_eq
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (I : Ideal R) (n : ℕ) :
    Module.length R ((associatedGradedModuleData (M := M) I).component (n : ℤ)) =
      Module.length R (associatedGradedModulePiece (M := M) I n) := by
  exact (associatedGradedModuleComponentLinearEquiv I n).length_eq

private noncomputable def gradedKernelModule
    (G : GradedRingData S) {A B : Type v}
    [AddCommGroup A] [Module S A] [AddCommGroup B] [Module S B]
    (𝓐 : GradedModuleData G A) (𝓑 : GradedModuleData G B)
    (f : A →ₗ[S] B) (hf : IsGradedLinearMap G 𝓐 𝓑 f) :
    GradedModuleData G (LinearMap.ker f) := by
  classical
  let K := LinearMap.ker f
  let component : ℤ → AddSubgroup K := fun d =>
    { carrier := {x | (x : A) ∈ 𝓐.component d}
      zero_mem' := by simp
      add_mem' := by intro x y hx hy; exact 𝓐.component d |>.add_mem hx hy
      neg_mem' := by intro x hx; exact 𝓐.component d |>.neg_mem hx }
  have hmap (x : A) :
      DirectSum.coeAddMonoidHom 𝓑.component
          (DirectSum.map (fun d => componentAddHom G 𝓐 𝓑 f hf d)
            (DirectSum.decompose 𝓐.component x)) = f x := by
    induction x using DirectSum.Decomposition.inductionOn
      (ℳ := 𝓐.component) with
    | zero => simp
    | homogeneous x => simp [componentAddHom]
    | add x y hx hy => simp [DirectSum.decompose_add, hx, hy]
  have hcomponent (x : A) (d : ℤ) :
      componentAddHom G 𝓐 𝓑 f hf d (DirectSum.decompose 𝓐.component x d) =
        DirectSum.decompose 𝓑.component (f x) d := by
    have h : DirectSum.decompose 𝓑.component (f x) =
        DirectSum.map (fun d => componentAddHom G 𝓐 𝓑 f hf d)
          (DirectSum.decompose 𝓐.component x) := by
      rw [← hmap x]
      exact (DirectSum.decompose 𝓑.component).apply_symm_apply _
    simpa using congrArg (fun z => z d) h.symm
  have hcomponentK (x : K) (d : ℤ) :
      f (DirectSum.decompose 𝓐.component (x : A) d) = 0 := by
    have hx : f (x : A) = 0 := x.property
    have h := hcomponent (x : A) d
    rw [hx] at h
    simpa [componentAddHom] using congrArg Subtype.val h
  let componentOf (x : K) (d : ℤ) : component d :=
    ⟨⟨DirectSum.decompose 𝓐.component (x : A) d,
        hcomponentK x d⟩,
      (DirectSum.decompose 𝓐.component (x : A) d).property⟩
  have hdecompose_exists (x : K) :
      ∃ y : DirectSum ℤ (fun d : ℤ => component d),
        DirectSum.coeAddMonoidHom component y = x := by
    let y : DirectSum ℤ (fun d : ℤ => component d) :=
      ∑ d ∈ (DirectSum.decompose 𝓐.component (x : A)).support,
        DirectSum.of (fun d : ℤ => component d) d (componentOf x d)
    refine ⟨y, ?_⟩
    apply Subtype.ext
    simpa [y, componentOf] using
      (DirectSum.sum_support_decompose 𝓐.component (x : A))
  let incl (d : ℤ) : component d →+ 𝓐.component d :=
    { toFun := fun x => ⟨(x : A), x.property⟩
      map_zero' := by ext; simp
      map_add' := by intro x y; ext; simp }
  have hcoeA_injective : Function.Injective
      (DirectSum.coeAddMonoidHom 𝓐.component) := by
    intro y z h
    exact (DirectSum.decomposeAddEquiv 𝓐.component).symm.injective h
  have hmap (y : DirectSum ℤ (fun d : ℤ => component d)) :
      DirectSum.coeAddMonoidHom 𝓐.component
          (DirectSum.map (fun d => incl d) y) =
        (DirectSum.coeAddMonoidHom component y : A) := by
    induction y using DirectSum.induction_on with
    | zero => simp
    | add y z hy hz =>
        calc
          DirectSum.coeAddMonoidHom 𝓐.component
              (DirectSum.map (fun d => incl d) (y + z)) =
                DirectSum.coeAddMonoidHom 𝓐.component
                (DirectSum.map (fun d => incl d) y) +
                DirectSum.coeAddMonoidHom 𝓐.component
                  (DirectSum.map (fun d => incl d) z) := by
            simpa only [map_add] using
              (DirectSum.coeAddMonoidHom 𝓐.component).map_add
                (DirectSum.map (fun d => incl d) y)
                (DirectSum.map (fun d => incl d) z)
          _ = (DirectSum.coeAddMonoidHom component y : A) +
                (DirectSum.coeAddMonoidHom component z : A) :=
            congrArg₂ (· + ·) hy hz
          _ = (DirectSum.coeAddMonoidHom component (y + z) : A) := by
            change
              ((DirectSum.coeAddMonoidHom component y +
                DirectSum.coeAddMonoidHom component z : K) : A) =
                (DirectSum.coeAddMonoidHom component (y + z) : A)
            exact congrArg Subtype.val
              ((DirectSum.coeAddMonoidHom component).map_add y z).symm
    | @of d y => rfl
  have hcoe_injective : Function.Injective
      (DirectSum.coeAddMonoidHom component) := by
    intro y z h
    have h' : DirectSum.map (fun d => incl d) y =
        DirectSum.map (fun d => incl d) z := by
      apply hcoeA_injective
      rw [hmap, hmap]
      exact congrArg Subtype.val h
    apply DirectSum.ext
    intro d
    have hd := congrArg (fun w : DirectSum ℤ (fun d : ℤ => 𝓐.component d) => w d) h'
    simpa [incl] using hd
  have hchoose (x : K) :
      DirectSum.coeAddMonoidHom component
          (Classical.choose (hdecompose_exists x)) = x :=
    Classical.choose_spec (hdecompose_exists x)
  let decomposeK : K →+ DirectSum ℤ (fun d : ℤ => component d) :=
    { toFun := fun x => Classical.choose (hdecompose_exists x)
      map_zero' := by
        apply hcoe_injective
        rw [hchoose]
        simp
      map_add' := by
        intro x y
        apply hcoe_injective
        rw [map_add, hchoose, hchoose, hchoose]
        }
  have hdecompose (x : K) :
      DirectSum.coeAddMonoidHom component (decomposeK x) = x := by
    exact hchoose x
  have hleft :
      (DirectSum.coeAddMonoidHom component).comp decomposeK = AddMonoidHom.id _ := by
    apply AddMonoidHom.ext
    intro x
    exact hdecompose x
  have hright :
      decomposeK.comp (DirectSum.coeAddMonoidHom component) =
        AddMonoidHom.id _ := by
    apply DirectSum.addHom_ext
    intro d z
    apply hcoe_injective
    simp [hdecompose]
  exact
    { component := component
      decomposition := DirectSum.Decomposition.ofAddHom
        (fun d : ℤ => component d) decomposeK hleft hright
      gradedSMul := by
        refine { smul_mem := ?_ }
        intro i j a x ha hx
        change (a : S) • (x : A) ∈ 𝓐.component (i + j)
        exact 𝓐.gradedSMul.smul_mem ha hx }

private def componentLinearMap
    (G : GradedRingData S) {M N : Type v} [AddCommGroup M] [Module S M]
    [AddCommGroup N] [Module S N]
    (𝓜 : GradedModuleData G M) (𝓝 : GradedModuleData G N)
    (f : M →ₗ[S] N) (hf : IsGradedLinearMap G 𝓜 𝓝 f) (d : ℤ) :
    𝓜.component d →ₗ[degreeZeroSubring G] 𝓝.component d :=
  { toFun := componentAddHom G 𝓜 𝓝 f hf d
    map_add' := by
      intro x y
      apply Subtype.ext
      simp [componentAddHom]
    map_smul' := by
      intro c x
      apply Subtype.ext
      change f ((c : S) • (x : M)) = (c : S) • f x
      exact f.map_smul (c : S) (x : M) }

private def gradedGeneratorMap
    (G : GradedRingData S) {N : Type v} [AddCommGroup N] [Module S N]
    (𝓝 : GradedModuleData G N) (n : ℕ) (x : Fin n → S)
    (hx : ∀ i, x i ∈ G.component 1) (d : ℤ) :
    (Fin n → 𝓝.component (d - 1)) →ₗ[degreeZeroSubring G] 𝓝.component d :=
  { toFun := fun y =>
      ⟨∑ i, (x i) • (y i : N), by
        apply (𝓝.component d).sum_mem
        intro i hi
        have h := 𝓝.gradedSMul.smul_mem (hx i) (y i).property
        change (x i) • (y i : N) ∈ 𝓝.component ((1 : ℤ) + (d - 1)) at h
        simpa [sub_eq_add_neg, add_assoc] using h⟩
    map_add' := by
      intro y z
      apply Subtype.ext
      change (∑ i, x i • ((y i : N) + (z i : N))) =
        (∑ i, x i • (y i : N)) + ∑ i, x i • (z i : N)
      simp only [smul_add, Finset.sum_add_distrib]
    map_smul' := by
      intro r y
      apply Subtype.ext
      change (∑ i, x i • ((r : S) • (y i : N))) =
        (r : S) • ∑ i, x i • (y i : N)
      rw [Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      simp only [smul_smul]
      rw [mul_comm]
  }

private def EventuallyGeneratedBy
    (G : GradedRingData S) {N : Type v} [AddCommGroup N] [Module S N]
    (𝓝 : GradedModuleData G N) (n : ℕ) (x : Fin n → S)
    (hx : ∀ i, x i ∈ G.component 1) : Prop :=
  ∃ c : ℤ, ∀ d : ℤ, c ≤ d →
    Function.Surjective (gradedGeneratorMap G 𝓝 n x hx d)

private theorem eventuallyGeneratedBy_tail
    (G : GradedRingData S) {N : Type v} [AddCommGroup N] [Module S N]
    (𝓝 : GradedModuleData G N) (n : ℕ) (x : Fin (n + 1) → S)
    (hx : ∀ i, x i ∈ G.component 1)
    (hgen : EventuallyGeneratedBy G 𝓝 (n + 1) x hx)
    (hzero : ∀ y : N, (x 0) • y = 0) :
    EventuallyGeneratedBy G 𝓝 n (fun i : Fin n => x i.succ)
      (fun i : Fin n => hx i.succ) := by
  rcases hgen with ⟨c, hgen⟩
  refine ⟨c, fun d hd z => ?_⟩
  rcases hgen d hd z with ⟨y, hy⟩
  refine ⟨fun i => y i.succ, ?_⟩
  apply Subtype.ext
  change (∑ i : Fin n, (x i.succ) • (y i.succ : N)) = (z : N)
  have hsum : (∑ i : Fin n, (x i.succ) • (y i.succ : N)) =
      (∑ i : Fin (n + 1), (x i) • (y i : N)) -
        (x 0) • (y 0 : N) := by
    rw [Fin.sum_univ_succ]
    simp only [sub_eq_add_neg]
    abel
  rw [hsum]
  rw [hzero]
  simpa [gradedGeneratorMap] using congrArg Subtype.val hy

private theorem exists_degree_one_generators
    (G : GradedRingData S) (hS : IsNoetherianRing S)
    (hdegree : GeneratedInDegreeOne G) :
    ∃ n : ℕ, ∃ x : Fin n → S,
      (∀ i, x i ∈ G.component 1) ∧
        Ideal.span (Set.range x) = irrelevantIdeal G := by
  letI : IsNoetherianRing S := hS
  have hR : IsNoetherianRing (degreeZeroSubring G) :=
    (graded_noetherian_iff G).mp hS |>.1
  letI : IsNoetherianRing (degreeZeroSubring G) := hR
  letI : Algebra.FiniteType (degreeZeroSubring G) S :=
    finiteType_of_noetherian_graded G hS
  letI : Module (degreeZeroSubring G) (G.component 1) := by
    change Module (degreeZeroSubring G)
      ((ringAsGradedModule G).component (1 : ℤ))
    exact gradedComponentDegreeZeroModule G (ringAsGradedModule G) (1 : ℤ)
  have hfinite : Module.Finite (degreeZeroSubring G) (G.component 1) := by
    have h := graded_module_component_finite G (ringAsGradedModule G) (1 : ℤ)
    change Module.Finite (degreeZeroSubring G) (G.component 1) at h
    exact h
  letI : Module.Finite (degreeZeroSubring G) (G.component 1) := hfinite
  obtain ⟨n, x, hxspan⟩ :=
    Module.Finite.exists_fin (R := degreeZeroSubring G) (M := G.component 1)
  let xS : Fin n → S := fun i => x i
  have hx : ∀ i, xS i ∈ G.component 1 := fun i => (x i).property
  rcases hdegree with ⟨t, ht, hspan⟩
  have htmem : ∀ y : t, IsHomogeneousElement G (y : S) ∧
      (y : S) ∈ irrelevantIdeal G := by
    intro y
    exact ⟨SetLike.isHomogeneousElem_coe
        (⟨y, ht y y.property⟩ : G.component 1),
      homogeneous_component_mem_irrelevantIdeal G (by norm_num) _ (ht y y.property)⟩
  have hspan_t : Ideal.span (Set.range (fun y : t => (y : S))) = irrelevantIdeal G := by
    have hrange : Set.range (fun y : t => (y : S)) = t := by
      ext y
      constructor
      · rintro ⟨z, rfl⟩
        exact z.property
      · intro hy
        exact ⟨⟨y, hy⟩, rfl⟩
    rw [hrange, hspan]
  have htadjoin :
      Algebra.adjoin (degreeZeroSubring G) (Set.range (fun y : t => (y : S))) = ⊤ :=
    (sPlus_generated_iff G (fun y : t => (y : S)) htmem).mpr hspan_t
  have ht_in : ∀ y : S, y ∈ t →
      y ∈ Algebra.adjoin (degreeZeroSubring G) (Set.range xS) := by
    intro y hy
    have hy' : (⟨y, ht y hy⟩ : G.component 1) ∈
        Submodule.span (degreeZeroSubring G) (Set.range x) := by
      rw [hxspan]
      trivial
    refine Submodule.span_induction (R := degreeZeroSubring G)
      (M := G.component 1)
      (p := fun z _ => (z : S) ∈
        Algebra.adjoin (degreeZeroSubring G) (Set.range xS)) ?_ ?_ ?_ ?_ hy'
    · intro z hz
      rcases hz with ⟨i, rfl⟩
      exact Algebra.subset_adjoin ⟨i, rfl⟩
    · exact (Algebra.adjoin (degreeZeroSubring G) (Set.range xS)).zero_mem
    · intro z w _ _ hz hw
      exact (Algebra.adjoin (degreeZeroSubring G) (Set.range xS)).add_mem hz hw
    · intro c z _ hz
      exact (Algebra.adjoin (degreeZeroSubring G) (Set.range xS)).smul_mem hz c
  have hxadjoin :
      Algebra.adjoin (degreeZeroSubring G) (Set.range xS) = ⊤ := by
    apply top_unique
    rw [← htadjoin]
    exact Algebra.adjoin_le (by
      intro z hz
      rcases hz with ⟨y, rfl⟩
      exact ht_in y y.property)
  have hxspanI :=
    (sPlus_generated_iff G xS (fun i => ⟨SetLike.isHomogeneousElem_coe _,
      homogeneous_component_mem_irrelevantIdeal G (by norm_num) _ (hx i)⟩)).mp hxadjoin
  exact ⟨n, xS, hx, hxspanI⟩

private theorem homogeneous_ideal_factorization
    (G : GradedRingData S) (n : ℕ) (x : Fin n → S)
    (hx : ∀ i, x i ∈ G.component 1)
    (hspan : Ideal.span (Set.range x) = irrelevantIdeal G) :
    ∀ d : ℕ, 0 < d → ∀ a : S, a ∈ G.component d →
      ∃ b : Fin n → G.component (d - 1),
        a = ∑ i, (b i : S) * x i := by
  let P : S → Prop := fun a =>
    (DirectSum.decompose G.component a 0 : S) = 0 ∧
      ∀ d : ℕ, 0 < d → ∃ b : Fin n → G.component (d - 1),
        (DirectSum.decompose G.component a d : S) = ∑ i, (b i : S) * x i
  have hP : ∀ a : S, a ∈ Ideal.span (Set.range x) → P a := by
    intro a ha
    refine Submodule.span_induction (p := fun a _ => P a) ?_ ?_ ?_ ?_ ha
    · rintro a ⟨i, rfl⟩
      constructor
      · rw [DirectSum.decompose_of_mem_ne G.component (hx i) (by norm_num)]
      · intro d hd
        by_cases hdi : d = 1
        · subst d
          let b : Fin n → G.component (1 - 1) := fun j =>
            if j = i then ⟨1, by simpa using SetLike.one_mem_graded G.component⟩ else 0
          refine ⟨b, ?_⟩
          rw [DirectSum.decompose_of_mem_same G.component (hx i)]
          rw [Finset.sum_eq_single i]
          · simp [b]
          · intro j hj hji
            simp [b, hji]
          · intro hi
            simp at hi
        · refine ⟨fun _ => 0, ?_⟩
          rw [DirectSum.decompose_of_mem_ne G.component (hx i) (by
            intro h
            apply hdi
            omega)]
          simp
    · constructor
      · simp
      · intro d hd
        exact ⟨fun _ => 0, by simp⟩
    · intro a b ha hb hPa hPb
      constructor
      · rw [DirectSum.decompose_add]
        change (DirectSum.decompose G.component a 0 : S) +
          (DirectSum.decompose G.component b 0 : S) = 0
        rw [hPa.1, hPb.1, add_zero]
      · intro d hd
        rcases hPa.2 d hd with ⟨ba, hba⟩
        rcases hPb.2 d hd with ⟨bb, hbb⟩
        refine ⟨fun i => ba i + bb i, ?_⟩
        rw [DirectSum.decompose_add]
        change (DirectSum.decompose G.component a d : S) +
          (DirectSum.decompose G.component b d : S) = _
        rw [hba, hbb, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i hi
        change (ba i : S) * x i + (bb i : S) * x i =
          ((ba i : S) + (bb i : S)) * x i
        ring
    · intro r a _ hPa
      have hPsmul : ∀ r : S, P (r * a) := by
        intro r
        induction r using DirectSum.Decomposition.inductionOn
          (ℳ := G.component) with
        | zero =>
            constructor
            · simp
            · intro d hd
              exact ⟨fun _ => 0, by simp⟩
        | add r s hr hs =>
            constructor
            · rw [add_mul, DirectSum.decompose_add]
              change (DirectSum.decompose G.component (r * a) 0 : S) +
                (DirectSum.decompose G.component (s * a) 0 : S) = 0
              rw [hr.1, hs.1, add_zero]
            · intro d hd
              rcases hr.2 d hd with ⟨br, hbr⟩
              rcases hs.2 d hd with ⟨bs, hbs⟩
              refine ⟨fun i => br i + bs i, ?_⟩
              rw [add_mul, DirectSum.decompose_add]
              change (DirectSum.decompose G.component (r * a) d : S) +
                (DirectSum.decompose G.component (s * a) d : S) = _
              rw [hbr, hbs, ← Finset.sum_add_distrib]
              apply Finset.sum_congr rfl
              intro i hi
              change (br i : S) * x i + (bs i : S) * x i =
                ((br i : S) + (bs i : S)) * x i
              ring
        | @homogeneous q r =>
            constructor
            · by_cases hi0 : q = 0
              · subst q
                rw [DirectSum.coe_decompose_mul_of_left_mem_zero G.component
                    r.property, hPa.1, mul_zero]
              · rw [DirectSum.coe_decompose_mul_of_left_mem_of_not_le
                    G.component r.property (by omega)]
            · intro d hd
              by_cases hjd : q ≤ d
              · rw [DirectSum.coe_decompose_mul_of_left_mem_of_le
                  G.component r.property hjd]
                by_cases hzero : d - q = 0
                · rw [hzero, hPa.1]
                  exact ⟨fun _ => 0, by simp⟩
                · have hepos : 0 < d - q := by omega
                  rcases hPa.2 (d - q) hepos with ⟨b, hb⟩
                  let c : Fin n → G.component (d - 1) := fun i =>
                    ⟨(r : S) * (b i : S), by
                      have hm := SetLike.mul_mem_graded (A := G.component)
                        r.property (b i).property
                      have hdeg : q + ((d - q) - 1) = d - 1 := by omega
                      simpa [hdeg] using hm⟩
                  refine ⟨c, ?_⟩
                  rw [hb, Finset.mul_sum]
                  apply Finset.sum_congr rfl
                  intro i hi
                  dsimp [c]
                  ring
              · exact ⟨fun _ => 0, by
                  rw [DirectSum.coe_decompose_mul_of_left_mem_of_not_le
                    G.component r.property hjd]
                  simp⟩
      exact hPsmul r
  intro d hd a ha
  have haI : a ∈ Ideal.span (Set.range x) := by
    rw [hspan]
    exact homogeneous_component_mem_irrelevantIdeal G hd a ha
  rcases hP a haI with ⟨_, hfactor⟩
  rcases hfactor d hd with ⟨b, hb⟩
  rw [DirectSum.decompose_of_mem_same G.component ha] at hb
  exact ⟨b, hb⟩

private theorem eventuallyGeneratedBy_of_hdegree
    (G : GradedRingData S) (hS : IsNoetherianRing S)
    (hdegree : GeneratedInDegreeOne G)
    {N : Type v} [AddCommGroup N] [Module S N]
    (𝓝 : GradedModuleData G N) [Module.Finite S N]
    (n : ℕ) (x : Fin n → S) (hx : ∀ i, x i ∈ G.component 1)
    (hspan : Ideal.span (Set.range x) = irrelevantIdeal G) :
    EventuallyGeneratedBy G 𝓝 n x hx := by
  letI : IsNoetherianRing S := hS
  have hR : IsNoetherianRing (degreeZeroSubring G) :=
    (graded_noetherian_iff G).mp hS |>.1
  letI : IsNoetherianRing (degreeZeroSubring G) := hR
  obtain ⟨m, d₀, y, hy, hyspan⟩ := graded_finite_homogeneous_generators G 𝓝
  let c : ℤ := 1 + ∑ i : Fin m, max (d₀ i) 0
  have hdc : ∀ i, d₀ i < c := by
    intro i
    calc
      d₀ i ≤ max (d₀ i) 0 := le_max_left _ _
      _ < 1 + ∑ j : Fin m, max (d₀ j) 0 := by
        exact Finset.single_le_sum (fun j _ => le_max_right _ _)
          (Finset.mem_univ i) |>.trans_lt (by omega)
  letI (e : ℤ) : Module (degreeZeroSubring G) (𝓝.component e) :=
    gradedComponentDegreeZeroModule G 𝓝 e
  refine ⟨c, fun d hd z => ?_⟩
  let T : Submodule (degreeZeroSubring G) (𝓝.component d) :=
    LinearMap.range (gradedGeneratorMap G 𝓝 n x hx d)
  have hd0 : 0 ≤ d := by
    have hc : 0 ≤ c := by
      dsimp [c]
      have hs : 0 ≤ ∑ i : Fin m, max (d₀ i) 0 :=
        Finset.sum_nonneg (fun i _ => le_max_right _ _)
      omega
    omega
  have hproj : ∀ (i : ℕ) (a : S), a ∈ G.component i →
      ∀ k : ℤ, ∀ w : N,
        (DirectSum.decompose 𝓝.component (a • w) k : N) =
          a • (DirectSum.decompose 𝓝.component w (k - (i : ℤ)) : N) := by
    intro i a ha k w
    induction w using DirectSum.Decomposition.inductionOn
      (ℳ := 𝓝.component) with
    | zero => simp
    | add w z hw hz =>
        rw [smul_add, DirectSum.decompose_add, DirectSum.add_apply,
          DirectSum.decompose_add, DirectSum.add_apply]
        change (DirectSum.decompose 𝓝.component (a • w) k : N) +
            (DirectSum.decompose 𝓝.component (a • z) k : N) =
          a • ((DirectSum.decompose 𝓝.component w (k - (i : ℤ)) : N) +
            (DirectSum.decompose 𝓝.component z (k - (i : ℤ)) : N))
        rw [hw, hz]
        simp [smul_add, add_assoc]
    | @homogeneous j w =>
        have hmul := 𝓝.gradedSMul.smul_mem ha w.property
        have hmul' : a • (w : N) ∈ 𝓝.component ((i : ℤ) + j) := by
          change a • (w : N) ∈ 𝓝.component ((i : ℤ) + j) at hmul
          exact hmul
        by_cases hjeq : (i : ℤ) + j = k
        · have hidx : k - (i : ℤ) = j := by omega
          have hidx' : (i : ℤ) + j - (i : ℤ) = j := by omega
          rw [← hjeq, DirectSum.decompose_of_mem_same 𝓝.component hmul',
            hidx', DirectSum.decompose_of_mem_same 𝓝.component w.property]
        · have hjeq' : j ≠ k - (i : ℤ) := by
            intro h
            apply hjeq
            omega
          rw [DirectSum.decompose_of_mem_ne 𝓝.component hmul' hjeq,
            DirectSum.decompose_of_mem_ne 𝓝.component w.property hjeq']
          simp
  have hcomponent : ∀ w : N, w ∈ Submodule.span S (Set.range y) →
      (⟨(DirectSum.decompose 𝓝.component w d : N),
        (DirectSum.decompose 𝓝.component w d).property⟩ : 𝓝.component d) ∈ T := by
    intro w hw
    refine Submodule.span_induction (p := fun w _ =>
      (⟨(DirectSum.decompose 𝓝.component w d : N),
        (DirectSum.decompose 𝓝.component w d).property⟩ : 𝓝.component d) ∈ T)
      ?_ ?_ ?_ ?_ hw
    · rintro w ⟨i, rfl⟩
      have hzero : d ≠ d₀ i := by
        intro h
        have := hdc i
        omega
      have hdec : (DirectSum.decompose 𝓝.component (y i) d : N) = 0 :=
        DirectSum.decompose_of_mem_ne 𝓝.component (hy i) (Ne.symm hzero)
      have hsub : (⟨(DirectSum.decompose 𝓝.component (y i) d : N),
          (DirectSum.decompose 𝓝.component (y i) d).property⟩ : 𝓝.component d) = 0 := by
        apply Subtype.ext
        exact hdec
      rw [hsub]
      exact T.zero_mem
    · have hz : (⟨(DirectSum.decompose 𝓝.component (0 : N) d : N),
          (DirectSum.decompose 𝓝.component (0 : N) d).property⟩ :
            𝓝.component d) = 0 := by
        apply Subtype.ext
        simp
      rw [hz]
      exact T.zero_mem
    · intro w z _ _ hw hz
      rw [DirectSum.decompose_add, DirectSum.add_apply]
      change
        (⟨(DirectSum.decompose 𝓝.component w d : N),
          (DirectSum.decompose 𝓝.component w d).property⟩ : 𝓝.component d) +
            ⟨(DirectSum.decompose 𝓝.component z d : N),
              (DirectSum.decompose 𝓝.component z d).property⟩ ∈ T
      exact T.add_mem hw hz
    · intro a w _ hw
      induction a using DirectSum.Decomposition.inductionOn
        (ℳ := G.component) with
      | zero =>
          convert T.zero_mem using 1
          apply Subtype.ext
          simp
      | add a b ha hb =>
          rw [add_smul, DirectSum.decompose_add, DirectSum.add_apply]
          change
            (⟨(DirectSum.decompose 𝓝.component (a • w) d : N),
              (DirectSum.decompose 𝓝.component (a • w) d).property⟩ : 𝓝.component d) +
                ⟨(DirectSum.decompose 𝓝.component (b • w) d : N),
                  (DirectSum.decompose 𝓝.component (b • w) d).property⟩ ∈ T
          exact T.add_mem ha hb
      | @homogeneous i a =>
          by_cases hi0 : i = 0
          · subst i
            have ha0 : (a : S) ∈ G.component 0 := a.property
            have hmem : (a : S) •
                (DirectSum.decompose 𝓝.component w d : N) ∈
                  𝓝.component d := by
              have h := 𝓝.gradedSMul.smul_mem ha0
                (DirectSum.decompose 𝓝.component w d).property
              change (a : S) • (DirectSum.decompose 𝓝.component w d : N) ∈
                𝓝.component ((0 : ℤ) + d) at h
              simpa using h
            have hsub :
                (⟨(DirectSum.decompose 𝓝.component ((a : S) • w) d : N),
                  (DirectSum.decompose 𝓝.component ((a : S) • w) d).property⟩ :
                𝓝.component d) =
                ⟨(a : S) • (DirectSum.decompose 𝓝.component w d : N), hmem⟩ := by
              apply Subtype.ext
              have h := hproj 0 (a : S) ha0 d w
              have hidx : d - ((0 : ℕ) : ℤ) = d := by omega
              rw [hidx] at h
              exact h
            rw [hsub]
            change (⟨(a : S) • (DirectSum.decompose 𝓝.component w d : N), _⟩ :
              𝓝.component d) ∈ T
            exact T.smul_mem ⟨(a : S), ha0⟩ hw
          · have hi0' : 0 < i := Nat.pos_of_ne_zero hi0
            rcases homogeneous_ideal_factorization G n x hx hspan i hi0'
                (a : S) a.property with ⟨b, hb⟩
            let q : Fin n → 𝓝.component (d - 1) := fun j =>
              ⟨(DirectSum.decompose 𝓝.component ((b j : S) • w) (d - 1) : N),
                (DirectSum.decompose 𝓝.component ((b j : S) • w) (d - 1)).property⟩
            refine ⟨q, ?_⟩
            apply Subtype.ext
            symm
            have hproj' := hproj i (a : S) a.property d w
            rw [hproj', hb, Finset.sum_smul]
            have hq : ∀ j, (DirectSum.decompose 𝓝.component
                  ((b j : S) • w) (d - 1) : N) =
                  (b j : S) •
                    (DirectSum.decompose 𝓝.component w (d - (i : ℤ)) : N) := by
              intro j
              rw [hproj (i - 1) (b j : S) (b j).property (d - 1) w]
              have hidx : (d - 1) - ((i - 1 : ℕ) : ℤ) =
                  d - (i : ℤ) := by omega
              rw [hidx]
            change _ = ∑ j, (x j) •
              (DirectSum.decompose 𝓝.component
                ((b j : S) • w) (d - 1) : N)
            simp_rw [hq]
            apply Finset.sum_congr rfl
            intro j hj
            rw [smul_smul]
            ring
  have hzT := hcomponent (z : N) (by rw [hyspan]; trivial)
  rcases hzT with ⟨q, hq⟩
  refine ⟨q, hq.trans ?_⟩
  apply Subtype.ext
  exact DirectSum.decompose_of_mem_same 𝓝.component z.property

private theorem kPrimeZeroClass_of_subsingleton
    {R : Type u} {W : Type v} [CommRing R] [AddCommGroup W] [Module R W]
    [Module.Finite R W] (hW : ∀ x y : W, x = y) :
    kPrimeZeroClass (R := R) (M := W) = 0 := by
  letI : Subsingleton W := ⟨hW⟩
  have hs : Function.Surjective (0 : W →ₗ[R] W) := by
    intro x
    exact ⟨0, Subsingleton.elim _ _⟩
  have hi : Function.Injective (0 : W →ₗ[R] W) := by
    intro x y _
    exact Subsingleton.elim _ _
  have h := kPrimeZeroClass_exact (0 : W →ₗ[R] W) (0 : W →ₗ[R] W)
    hi hs ((LinearMap.exact_zero_iff_surjective W (0 : W →ₗ[R] W)).2 hs)
  have h' : kPrimeZeroClass (R := R) (M := W) +
      kPrimeZeroClass (R := R) (M := W) =
      kPrimeZeroClass (R := R) (M := W) := h.symm
  calc
    kPrimeZeroClass (R := R) (M := W) =
        kPrimeZeroClass (R := R) (M := W) + 0 := (add_zero _).symm
    _ = kPrimeZeroClass (R := R) (M := W) +
        (kPrimeZeroClass (R := R) (M := W) -
          kPrimeZeroClass (R := R) (M := W)) := by rw [sub_self, add_zero]
    _ = (kPrimeZeroClass (R := R) (M := W) +
          kPrimeZeroClass (R := R) (M := W)) -
        kPrimeZeroClass (R := R) (M := W) := by abel
    _ = kPrimeZeroClass (R := R) (M := W) -
        kPrimeZeroClass (R := R) (M := W) := by rw [h']
    _ = 0 := sub_self _

private theorem isNumericalPolynomial_sub
    {A : Type v} [AddCommGroup A] {f g : ℤ → A}
    (hf : IsNumericalPolynomial f) (hg : IsNumericalPolynomial g) :
    IsNumericalPolynomial (fun n => f n - g n) := by
  rcases hf with ⟨r, a, ha⟩
  rcases hg with ⟨s, b, hb⟩
  let m := max r s
  let c : ℕ → A := fun i =>
    (if i ≤ r then a i else 0) - (if i ≤ s then b i else 0)
  have hsumA (n : ℤ) :
      (∑ i ∈ Finset.range (m + 1), integerBinomial n i •
          (if i ≤ r then a i else 0)) =
        ∑ i ∈ Finset.range (r + 1), integerBinomial n i • a i := by
    symm
    calc
      (∑ i ∈ Finset.range (r + 1), integerBinomial n i • a i) =
          ∑ i ∈ Finset.range (r + 1), integerBinomial n i •
            (if i ≤ r then a i else 0) := by
        apply Finset.sum_congr rfl
        intro i hi
        simp only [Finset.mem_range] at hi
        simp [Nat.lt_succ_iff.mp hi]
      _ = ∑ i ∈ Finset.range (m + 1), integerBinomial n i •
            (if i ≤ r then a i else 0) := by
        dsimp [m]
        apply Finset.sum_subset (show Finset.range (r + 1) ⊆
            Finset.range (max r s + 1) from
          Finset.range_subset_range.mpr (by omega))
        intro i hi hnot
        simp only [Finset.mem_range, not_lt] at hnot
        have hir : ¬ i ≤ r := by omega
        simp [hir]
  have hsumB (n : ℤ) :
      (∑ i ∈ Finset.range (m + 1), integerBinomial n i •
          (if i ≤ s then b i else 0)) =
        ∑ i ∈ Finset.range (s + 1), integerBinomial n i • b i := by
    symm
    calc
      (∑ i ∈ Finset.range (s + 1), integerBinomial n i • b i) =
          ∑ i ∈ Finset.range (s + 1), integerBinomial n i •
            (if i ≤ s then b i else 0) := by
        apply Finset.sum_congr rfl
        intro i hi
        simp only [Finset.mem_range] at hi
        simp [Nat.lt_succ_iff.mp hi]
      _ = ∑ i ∈ Finset.range (m + 1), integerBinomial n i •
            (if i ≤ s then b i else 0) := by
        dsimp [m]
        apply Finset.sum_subset (show Finset.range (s + 1) ⊆
            Finset.range (max r s + 1) from
          Finset.range_subset_range.mpr (by omega))
        intro i hi hnot
        simp only [Finset.mem_range, not_lt] at hnot
        have his : ¬ i ≤ s := by omega
        simp [his]
  refine ⟨m, c, ?_⟩
  filter_upwards [ha, hb] with n hfa hfb
  rw [hfa, hfb, ← hsumA n, ← hsumB n, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  simp [c, smul_sub]

private def dropGenerators
    {m : ℕ} (x : Fin m → S) (k : ℕ) (hk : k ≤ m) : Fin (m - k) → S :=
  fun i => x ⟨k + i, by omega⟩

private theorem eventuallyGeneratedBy_reindex
    (G : GradedRingData S) {N : Type v} [AddCommGroup N] [Module S N]
    (𝓝 : GradedModuleData G N) (n n' : ℕ)
    (x : Fin n → S) (x' : Fin n' → S)
    (hx : ∀ i, x i ∈ G.component 1)
    (hx' : ∀ i, x' i ∈ G.component 1)
    (hn : n = n')
    (hxx : ∀ i : Fin n, x i = x' (Fin.cast hn i))
    (hgen : EventuallyGeneratedBy G 𝓝 n x hx) :
    EventuallyGeneratedBy G 𝓝 n' x' hx' := by
  subst n'
  have hxy : x = x' := by
    funext i
    simpa using hxx i
  subst x'
  simpa using hgen

private def prefixAnnihilated
    (G : GradedRingData S) {m : ℕ} (x : Fin m → S)
    {N : Type v} [AddCommGroup N] [Module S N]
    (k : ℕ) (hk : k ≤ m) (𝓝 : GradedModuleData G N) : Prop :=
  ∀ i : Fin k, ∀ y : N, x ⟨i, by omega⟩ • y = 0

private theorem eventuallyGeneratedBy_drop
    (G : GradedRingData S) {m : ℕ} (x : Fin m → S)
    (hx : ∀ i, x i ∈ G.component 1) {k : ℕ} (hk : k ≤ m)
    {N : Type v} [AddCommGroup N] [Module S N]
    (𝓝 : GradedModuleData G N)
    (hgen : EventuallyGeneratedBy G 𝓝 m x hx)
    (hzero : prefixAnnihilated G x k hk 𝓝) :
    EventuallyGeneratedBy G 𝓝 (m - k) (dropGenerators x k hk)
      (fun i => hx ⟨k + i, by omega⟩) := by
  revert hk hgen hzero
  induction k with
  | zero =>
      intro hk hgen hzero
      rcases hgen with ⟨c, hgen⟩
      refine ⟨c, fun d hd z => ?_⟩
      rcases hgen d hd z with ⟨y, hy⟩
      refine ⟨fun i => y ⟨i.1, by omega⟩, ?_⟩
      apply Subtype.ext
      simpa [gradedGeneratorMap, dropGenerators] using
        congrArg Subtype.val hy
  | succ k ih =>
      intro hk hgen hzero
      have hk' : k ≤ m := by omega
      have hzero_k : prefixAnnihilated G x k hk' 𝓝 := by
        intro i y
        exact hzero ⟨i, by omega⟩ y
      have hgen_k := ih hk' hgen hzero_k
      let y : Fin (m - k - 1 + 1) → S := fun i =>
        dropGenerators x k hk' ⟨i, by omega⟩
      have hzero_head : ∀ z : N, (y 0) • z = 0 := by
        intro z
        exact hzero ⟨k, by omega⟩ z
      have hy : ∀ i, y i ∈ G.component 1 := by
        intro i
        exact hx ⟨k + i, by omega⟩
      have hgen_y : EventuallyGeneratedBy G 𝓝 (m - k - 1 + 1) y hy := by
        apply eventuallyGeneratedBy_reindex G 𝓝 (m - k) (m - k - 1 + 1)
          (dropGenerators x k hk') y (fun i => hx ⟨k + i, by omega⟩) hy
          (show m - k = m - k - 1 + 1 by omega) (by
            intro i
            rfl) hgen_k
      have htail := eventuallyGeneratedBy_tail G 𝓝 (m - k - 1)
        y hy hgen_y hzero_head
      apply eventuallyGeneratedBy_reindex G 𝓝 (m - k - 1) (m - (k + 1))
        (fun i => y i.succ) (dropGenerators x (k + 1) hk) (fun i => hy i.succ)
        (fun i => hx ⟨k + 1 + i, by omega⟩)
        (show m - k - 1 = m - (k + 1) by omega) (by
          intro i
          apply congrArg x
          apply Fin.ext
          simp [y, dropGenerators]
          omega) htail

private theorem graded_hilbert_difference
    (G : GradedRingData S) (hS : IsNoetherianRing S)
    {N : Type v} [AddCommGroup N] [Module S N]
    (𝓝 : GradedModuleData G N) [Module.Finite S N]
    (a : S) (ha : a ∈ G.component 1)
    (hN : ∀ d : ℤ, Module.Finite (degreeZeroSubring G) (𝓝.component d))
    (hKnum : ∀ (𝓚 : GradedModuleData G (LinearMap.ker
        (LinearMap.lsmul S N a)))
        (hf : IsGradedLinearMap G (twist G 𝓝 (-1)) 𝓝
          (LinearMap.lsmul S N a))
        (h𝓚 : ∀ d : ℤ,
          Module.Finite (degreeZeroSubring G) (𝓚.component d)),
        IsNumericalPolynomial (gradedHilbertFunction G 𝓚 h𝓚))
    (hQnum : ∀ (𝓠 : GradedModuleData G
        (N ⧸ LinearMap.range (LinearMap.lsmul S N a)))
        (hR : IsGradedSubmodule G 𝓝
          (LinearMap.range (LinearMap.lsmul S N a)))
        (h𝓠 : ∀ d : ℤ,
          Module.Finite (degreeZeroSubring G) (𝓠.component d)),
        IsNumericalPolynomial (gradedHilbertFunction G 𝓠 h𝓠)) :
    IsNumericalPolynomial
      (fun d => gradedHilbertFunction G 𝓝 hN d -
        gradedHilbertFunction G 𝓝 hN (d - 1)) := by
  letI : Algebra.FiniteType (degreeZeroSubring G) S :=
    finiteType_of_noetherian_graded G hS
  let 𝓣 := twist G 𝓝 (-1)
  let f : N →ₗ[S] N := LinearMap.lsmul S N a
  have hf : IsGradedLinearMap G 𝓣 𝓝 f := by
    intro d y hy
    have h := 𝓝.gradedSMul.smul_mem ha hy
    change a • (y : N) ∈ 𝓝.component ((1 : ℤ) + (-1 + d)) at h
    change a • (y : N) ∈ 𝓝.component d
    simpa [add_assoc, add_left_comm, add_comm] using h
  let K := LinearMap.ker f
  let 𝓚 := gradedKernelModule G 𝓣 𝓝 f hf
  have hRng : IsGradedSubmodule G 𝓝 (LinearMap.range f) := by
    intro d y hy
    rcases hy with ⟨z, rfl⟩
    have hmap (w : N) :
        DirectSum.coeAddMonoidHom 𝓝.component
            (DirectSum.map (fun e => componentAddHom G 𝓣 𝓝 f hf e)
              (DirectSum.decompose 𝓣.component w)) = f w := by
      induction w using DirectSum.Decomposition.inductionOn
        (ℳ := 𝓣.component) with
      | zero => simp
      | homogeneous w => simp [componentAddHom]
      | add w z hw hz => simp [DirectSum.decompose_add, hw, hz]
    have hcomp (w : N) (e : ℤ) :
        componentAddHom G 𝓣 𝓝 f hf e (DirectSum.decompose 𝓣.component w e) =
          DirectSum.decompose 𝓝.component (f w) e := by
      have h : DirectSum.decompose 𝓝.component (f w) =
          DirectSum.map (fun e => componentAddHom G 𝓣 𝓝 f hf e)
            (DirectSum.decompose 𝓣.component w) := by
        rw [← hmap w]
        exact (DirectSum.decompose 𝓝.component).apply_symm_apply _
      simpa using congrArg (fun q => q e) h.symm
    rw [← hcomp z d]
    exact ⟨DirectSum.decompose 𝓣.component z d, rfl⟩
  let 𝓠 := gradedQuotientModule G 𝓝 (LinearMap.range f) hRng
  let q : N →ₗ[S] (N ⧸ LinearMap.range f) := (LinearMap.range f).mkQ
  have hq : IsGradedLinearMap G 𝓝 𝓠 q := by
    simpa [q] using gradedQuotient_mk_isGraded G 𝓝
      (LinearMap.range f) hRng
  let R := LinearMap.ker q
  let 𝓡 := gradedKernelModule G 𝓝 𝓠 q hq
  let g : N →ₗ[S] R :=
    { toFun := fun z =>
        ⟨f z, by
          change q (f z) = 0
          change Submodule.Quotient.mk (f z) = 0
          apply (Submodule.Quotient.mk_eq_zero _).2
          exact ⟨z, rfl⟩⟩
      map_add' := by
        intro z w
        apply Subtype.ext
        simp [f]
      map_smul' := by
        intro c z
        apply Subtype.ext
        simp [f] }
  have hg : IsGradedLinearMap G 𝓣 𝓡 g := by
    intro d z hz
    change f z ∈ 𝓝.component d
    exact hf d z hz
  have hRsub : IsGradedLinearMap G 𝓡 𝓝 R.subtype := by
    intro d z hz
    exact hz
  have hsurjg : Function.Surjective g := by
    intro z
    have hz : (z : N) ∈ LinearMap.range f := by
      have hzq : q (z : N) = 0 := z.property
      change Submodule.Quotient.mk (z : N) = 0 at hzq
      exact (Submodule.Quotient.mk_eq_zero _).1 hzq
    rcases hz with ⟨w, hw⟩
    refine ⟨w, ?_⟩
    apply Subtype.ext
    exact hw
  have hexact1 : Function.Exact K.subtype g := by
    rw [LinearMap.exact_iff]
    change LinearMap.ker g = LinearMap.range K.subtype
    apply le_antisymm
    · intro z hz
      change g z = 0 at hz
      refine ⟨⟨z, ?_⟩, rfl⟩
      exact congrArg Subtype.val hz
    · intro z hz
      rcases hz with ⟨w, rfl⟩
      change g (w : N) = 0
      apply Subtype.ext
      exact w.property
  have hexact2 : Function.Exact R.subtype q := by
    simpa [R] using (LinearMap.exact_subtype_ker_map q)
  letI (e : ℤ) : Module (degreeZeroSubring G) (𝓝.component e) :=
    gradedComponentDegreeZeroModule G 𝓝 e
  letI (e : ℤ) : Module (degreeZeroSubring G) (𝓣.component e) := by
    dsimp [𝓣]
    change Module (degreeZeroSubring G) (𝓝.component (-1 + e))
    exact gradedComponentDegreeZeroModule G 𝓝 (-1 + e)
  letI (e : ℤ) : Module (degreeZeroSubring G) (𝓚.component e) :=
    gradedComponentDegreeZeroModule G 𝓚 e
  letI (e : ℤ) : Module (degreeZeroSubring G) (𝓡.component e) :=
    gradedComponentDegreeZeroModule G 𝓡 e
  letI (e : ℤ) : Module (degreeZeroSubring G) (𝓠.component e) :=
    gradedComponentDegreeZeroModule G 𝓠 e
  have hKfin : ∀ d : ℤ,
      Module.Finite (degreeZeroSubring G) (𝓚.component d) :=
    graded_module_component_finite G 𝓚
  have hRfin : ∀ d : ℤ,
      Module.Finite (degreeZeroSubring G) (𝓡.component d) :=
    graded_module_component_finite G 𝓡
  have hQfin : ∀ d : ℤ,
      Module.Finite (degreeZeroSubring G) (𝓠.component d) :=
    graded_module_component_finite G 𝓠
  have hKnum' := hKnum 𝓚 hf hKfin
  have hQnum' := hQnum 𝓠 hRng hQfin
  have hcomponent1 :=
    (graded_short_exact_iff_componentwise G 𝓚 𝓣 𝓡 K.subtype g
      (by
        intro d y hy
        exact hy) hg).mp
      ⟨Submodule.injective_subtype _, hexact1, hsurjg⟩
  have hcomponent2 :=
    (graded_short_exact_iff_componentwise G 𝓡 𝓝 𝓠 R.subtype q hRsub hq).mp
      ⟨Submodule.injective_subtype _, hexact2,
        Submodule.mkQ_surjective _⟩
  have hTfin : ∀ d : ℤ,
      Module.Finite (degreeZeroSubring G) (𝓣.component d) := by
    intro d
    dsimp [𝓣]
    change Module.Finite (degreeZeroSubring G) (𝓝.component (-1 + d))
    exact hN (-1 + d)
  have hrelT : ∀ d : ℤ,
      gradedHilbertFunction G 𝓣 hTfin d =
      gradedHilbertFunction G 𝓚 hKfin d +
        kPrimeZeroClass (R := degreeZeroSubring G) (M := 𝓡.component d) := by
    intro d
    letI : Module.Finite (degreeZeroSubring G) (𝓚.component d) := hKfin d
    letI : Module.Finite (degreeZeroSubring G) (𝓣.component d) := by
      dsimp [𝓣]
      change Module.Finite (degreeZeroSubring G) (𝓝.component (-1 + d))
      exact hN (-1 + d)
    letI : Module.Finite (degreeZeroSubring G) (𝓡.component d) := hRfin d
    change kPrimeZeroClass (R := degreeZeroSubring G) (M := 𝓣.component d) = _
    let f1 := componentLinearMap G 𝓚 𝓣 K.subtype (by
      intro e y hy
      exact hy) d
    let g1 := componentLinearMap G 𝓣 𝓡 g hg d
    have hf1 : Function.Injective f1 := by
      simpa [f1, componentLinearMap] using (hcomponent1 d).1
    have hg1 : Function.Surjective g1 := by
      simpa [g1, componentLinearMap] using (hcomponent1 d).2.2
    have hfg1 : Function.Exact f1 g1 := by
      simpa [f1, g1, componentLinearMap] using (hcomponent1 d).2.1
    have h1 := kPrimeZeroClass_exact
      (R := degreeZeroSubring G) (M' := 𝓚.component d)
      (M := 𝓣.component d) (M'' := 𝓡.component d)
      f1 g1 hf1 hg1 hfg1
    exact h1
  have hrelN : ∀ d : ℤ,
      gradedHilbertFunction G 𝓝 hN d =
      kPrimeZeroClass (R := degreeZeroSubring G) (M := 𝓡.component d) +
        gradedHilbertFunction G 𝓠 hQfin d := by
    intro d
    letI : Module.Finite (degreeZeroSubring G) (𝓡.component d) := hRfin d
    letI : Module.Finite (degreeZeroSubring G) (𝓝.component d) := hN d
    letI : Module.Finite (degreeZeroSubring G) (𝓠.component d) := hQfin d
    change kPrimeZeroClass (R := degreeZeroSubring G) (M := 𝓝.component d) = _
    let f2 := componentLinearMap G 𝓡 𝓝 R.subtype hRsub d
    let g2 := componentLinearMap G 𝓝 𝓠 q hq d
    have hf2 : Function.Injective f2 := by
      simpa [f2, componentLinearMap] using (hcomponent2 d).1
    have hg2 : Function.Surjective g2 := by
      simpa [g2, componentLinearMap] using (hcomponent2 d).2.2
    have hfg2 : Function.Exact f2 g2 := by
      simpa [f2, g2, componentLinearMap] using (hcomponent2 d).2.1
    have h2 := kPrimeZeroClass_exact
      (R := degreeZeroSubring G) (M' := 𝓡.component d)
      (M := 𝓝.component d) (M'' := 𝓠.component d)
      f2 g2 hf2 hg2 hfg2
    exact h2
  have hdiff : IsNumericalPolynomial (fun d =>
      gradedHilbertFunction G 𝓠 hQfin d -
      gradedHilbertFunction G 𝓚 hKfin d) :=
    isNumericalPolynomial_sub hQnum' hKnum'
  have hdiff' : IsNumericalPolynomial (fun d =>
      gradedHilbertFunction G 𝓝 hN d -
        gradedHilbertFunction G 𝓝 hN (d - 1)) := by
    rw [show (fun d => gradedHilbertFunction G 𝓝 hN d -
        gradedHilbertFunction G 𝓝 hN (d - 1)) =
      (fun d => gradedHilbertFunction G 𝓠 hQfin d -
        gradedHilbertFunction G 𝓚 hKfin d) by
      funext d
      have hT' : gradedHilbertFunction G 𝓣 hTfin d =
          gradedHilbertFunction G 𝓝 hN (d - 1) := by
        change kPrimeZeroClass (R := degreeZeroSubring G)
            (M := 𝓣.component d) =
          kPrimeZeroClass (R := degreeZeroSubring G)
            (M := 𝓝.component (d - 1))
        have hcomponent : 𝓣.component d = 𝓝.component (d - 1) := by
          change 𝓝.component (-1 + d) = 𝓝.component (d - 1)
          congr 1
          omega
        let e : 𝓣.component d ≃ₗ[degreeZeroSubring G]
            𝓝.component (d - 1) :=
          { toFun := fun z => ⟨(z : N), hcomponent ▸ z.property⟩
            invFun := fun z => ⟨(z : N), hcomponent.symm ▸ z.property⟩
            left_inv := by intro z; apply Subtype.ext; rfl
            right_inv := by intro z; apply Subtype.ext; rfl
            map_add' := by intro z w; apply Subtype.ext; rfl
            map_smul' := by
              intro c z
              apply Subtype.ext
              rfl }
        exact kPrimeZeroClass_eq_of_linearEquiv e
      rw [hrelN d, ← hT', hrelT d]
      abel]
    exact hdiff
  exact hdiff'

private theorem graded_hilbert_aux
    (G : GradedRingData S) (hS : IsNoetherianRing S)
    (hdegree : GeneratedInDegreeOne G) {m : ℕ} (x : Fin m → S)
    (hx : ∀ i, x i ∈ G.component 1)
    (hspan : Ideal.span (Set.range x) = irrelevantIdeal G) :
    ∀ k : ℕ, ∀ hk : k ≤ m, ∀ {N : Type v} [AddCommGroup N] [Module S N]
      (𝓝 : GradedModuleData G N) [Module.Finite S N],
      prefixAnnihilated G x k hk 𝓝 →
      (hN : ∀ d : ℤ,
        Module.Finite (degreeZeroSubring G) (𝓝.component d)) →
      IsNumericalPolynomial (gradedHilbertFunction G 𝓝 hN) := by
  letI : IsNoetherianRing S := hS
  letI : Algebra.FiniteType (degreeZeroSubring G) S :=
    finiteType_of_noetherian_graded G hS
  let rec aux (k : ℕ) (hk : k ≤ m) {N : Type v} [AddCommGroup N] [Module S N]
      (𝓝 : GradedModuleData G N) [Module.Finite S N]
      (hzero : prefixAnnihilated G x k hk 𝓝)
      (hN : ∀ d : ℤ, Module.Finite (degreeZeroSubring G) (𝓝.component d)) :
      IsNumericalPolynomial (gradedHilbertFunction G 𝓝 hN) := by
    have hfull := eventuallyGeneratedBy_of_hdegree G hS hdegree 𝓝 m x hx hspan
    have hgen := eventuallyGeneratedBy_drop G x hx hk 𝓝 hfull hzero
    by_cases hkm : k = m
    · subst k
      rcases hgen with ⟨c, hgen⟩
      apply IsEventuallyZero.isNumericalPolynomial
      filter_upwards [Filter.Ici_mem_atTop c] with d hd
      letI : Module.Finite (degreeZeroSubring G) (𝓝.component d) := hN d
      have hs : ∀ u v : 𝓝.component d, u = v := by
        intro u v
        rcases hgen d hd u with ⟨p, hp⟩
        rcases hgen d hd v with ⟨q, hq⟩
        have hpq : p = q := by
          funext i
          exact Fin.elim0 ⟨i.1, by omega⟩
        apply Subtype.ext
        rw [hpq] at hp
        exact congrArg Subtype.val (hp.symm.trans hq)
      change kPrimeZeroClass (R := degreeZeroSubring G)
        (M := 𝓝.component d) = 0
      exact kPrimeZeroClass_of_subsingleton hs
    · have hkm' : k < m := Nat.lt_of_le_of_ne hk hkm
      obtain ⟨n, hn⟩ : ∃ n : ℕ, m - k = n + 1 := by
        exact ⟨m - k - 1, by omega⟩
      let y : Fin (n + 1) → S := fun i =>
        dropGenerators x k hk ⟨i, by omega⟩
      have hy : ∀ i, y i ∈ G.component 1 := by
        intro i
        exact hx ⟨k + i, by omega⟩
      have hgen' : EventuallyGeneratedBy G 𝓝 (n + 1) y hy := by
        apply eventuallyGeneratedBy_reindex G 𝓝 (m - k) (n + 1)
          (dropGenerators x k hk) y (fun i => hx ⟨k + i, by omega⟩) hy hn (by
            intro i
            rfl) hgen
      let a : S := y 0
      have ha : a ∈ G.component 1 := hy 0
      let 𝓣 := twist G 𝓝 (-1)
      let f : N →ₗ[S] N := LinearMap.lsmul S N a
      have hf : IsGradedLinearMap G 𝓣 𝓝 f := by
        intro d z hz
        have h := 𝓝.gradedSMul.smul_mem ha hz
        change a • (z : N) ∈ 𝓝.component ((1 : ℤ) + (-1 + d)) at h
        change a • (z : N) ∈ 𝓝.component d
        simpa [add_assoc, add_left_comm, add_comm] using h
      let K := LinearMap.ker f
      let 𝓚 := gradedKernelModule G 𝓣 𝓝 f hf
      have hRng : IsGradedSubmodule G 𝓝 (LinearMap.range f) := by
        intro d z hz
        rcases hz with ⟨w, rfl⟩
        have hmap (u : N) :
            DirectSum.coeAddMonoidHom 𝓝.component
                (DirectSum.map (fun e => componentAddHom G 𝓣 𝓝 f hf e)
                  (DirectSum.decompose 𝓣.component u)) = f u := by
          induction u using DirectSum.Decomposition.inductionOn
            (ℳ := 𝓣.component) with
          | zero => simp
          | homogeneous u => simp [componentAddHom]
          | add u v hu hv => simp [DirectSum.decompose_add, hu, hv]
        have hcomp (u : N) (e : ℤ) :
            componentAddHom G 𝓣 𝓝 f hf e (DirectSum.decompose 𝓣.component u e) =
              DirectSum.decompose 𝓝.component (f u) e := by
          have h : DirectSum.decompose 𝓝.component (f u) =
              DirectSum.map (fun e => componentAddHom G 𝓣 𝓝 f hf e)
                (DirectSum.decompose 𝓣.component u) := by
            rw [← hmap u]
            exact (DirectSum.decompose 𝓝.component).apply_symm_apply _
          simpa using congrArg (fun q => q e) h.symm
        rw [← hcomp w d]
        exact ⟨DirectSum.decompose 𝓣.component w d, rfl⟩
      let 𝓠 := gradedQuotientModule G 𝓝 (LinearMap.range f) hRng
      have hzeroK : prefixAnnihilated G x (k + 1) (by omega) 𝓚 := by
        intro i z
        by_cases hik : (i : ℕ) < k
        · apply Subtype.ext
          change x ⟨i, by omega⟩ • (z : N) = 0
          exact hzero ⟨i, hik⟩ (z : N)
        · have hik' : (i : ℕ) = k := by omega
          have hi : i = ⟨k, by omega⟩ := by
            apply Fin.ext
            exact hik'
          have hz : a • (z : N) = 0 := by
            have hz0 : f (z : N) = 0 := z.property
            change a • (z : N) = 0 at hz0
            exact hz0
          apply Subtype.ext
          change x ⟨(i : ℕ), by omega⟩ • (z : N) = 0
          simpa [hi, a, y, dropGenerators] using hz
      have hzeroQ : prefixAnnihilated G x (k + 1) (by omega) 𝓠 := by
        intro i z
        refine Submodule.Quotient.induction_on (LinearMap.range f) z ?_
        intro w
        by_cases hik : (i : ℕ) < k
        · have hz := hzero ⟨i, hik⟩ w
          change Submodule.Quotient.mk (x ⟨i, by omega⟩ • w) = 0
          rw [hz]
          exact Submodule.Quotient.mk_zero _
        · have hik' : (i : ℕ) = k := by omega
          have hi : i = ⟨k, by omega⟩ := by
            apply Fin.ext
            exact hik'
          rw [hi]
          change Submodule.Quotient.mk (x ⟨k, by omega⟩ • w) = 0
          apply (Submodule.Quotient.mk_eq_zero _).2
          exact ⟨w, rfl⟩
      have hKnum : ∀ (𝓚' : GradedModuleData G K)
          (hf' : IsGradedLinearMap G 𝓣 𝓝 f),
          (h𝓚' : ∀ d : ℤ,
            Module.Finite (degreeZeroSubring G) (𝓚'.component d)) →
          IsNumericalPolynomial (gradedHilbertFunction G 𝓚' h𝓚') := by
        intro 𝓚' hf' h𝓚'
        exact aux (k + 1) (by omega) 𝓚' hzeroK
          h𝓚'
      have hQnum : ∀ (𝓠' : GradedModuleData G
          (N ⧸ LinearMap.range f))
          (hR : IsGradedSubmodule G 𝓝 (LinearMap.range f)),
          (h𝓠' : ∀ d : ℤ,
            Module.Finite (degreeZeroSubring G) (𝓠'.component d)) →
          IsNumericalPolynomial (gradedHilbertFunction G 𝓠' h𝓠') := by
        intro 𝓠' hR h𝓠'
        exact aux (k + 1) (by omega) 𝓠' hzeroQ
          h𝓠'
      have hdiff := graded_hilbert_difference G hS 𝓝 a ha hN hKnum hQnum
      exact isNumericalPolynomial_of_sub
        (gradedHilbertFunction G 𝓝 hN) hdiff
  termination_by m - k
  decreasing_by
    all_goals exact Nat.sub_lt_sub_left hkm' (Nat.lt_succ_self k)
  intro k hk N iAdd iModule 𝓝 iFinite hzero hN
  exact aux k hk 𝓝 hzero hN

theorem graded_hilbert_polynomial
    (G : GradedRingData S) (𝓜 : GradedModuleData G M)
    (hS : IsNoetherianRing S) [Module.Finite S M]
    (hdegree : GeneratedInDegreeOne G) :
    IsNumericalPolynomial (noetherianGradedHilbertFunction G 𝓜 hS) := by
  letI : IsNoetherianRing S := hS
  letI : Algebra.FiniteType (degreeZeroSubring G) S :=
    finiteType_of_noetherian_graded G hS
  obtain ⟨n, x, hx, hspan⟩ := exists_degree_one_generators G hS hdegree
  have hN : ∀ d : ℤ,
      Module.Finite (degreeZeroSubring G) (𝓜.component d) :=
    graded_module_component_finite G 𝓜
  have hzero : prefixAnnihilated G x 0 (by omega) 𝓜 := by
    intro i
    exact Fin.elim0 i
  have hmain := graded_hilbert_aux G hS hdegree x hx hspan 0 (by omega)
    𝓜 hzero hN
  simpa [noetherianGradedHilbertFunction] using hmain

/-- A function is periodic-polynomial when its restriction to every residue
class modulo one positive period is a numerical polynomial in the quotient
variable. -/
def IsPeriodicNumericalPolynomial
    {A : Type v} [AddCommGroup A] (f : ℤ → A) : Prop :=
  ∃ q : ℕ, 0 < q ∧
    ∀ r : Fin q,
      IsNumericalPolynomial (fun m : ℤ => f ((r : ℤ) + (q : ℤ) * m))

theorem IsNumericalPolynomial.isPeriodicNumericalPolynomial
    {A : Type v} [AddCommGroup A] {f : ℤ → A}
    (hf : IsNumericalPolynomial f) :
    IsPeriodicNumericalPolynomial f := by
  refine ⟨1, by omega, fun r => ?_⟩
  simpa using hf

theorem IsEventuallyZero.isPeriodicNumericalPolynomial
    {A : Type v} [AddCommGroup A] {f : ℤ → A}
    (hf : IsEventuallyZero f) :
    IsPeriodicNumericalPolynomial f :=
  hf.isNumericalPolynomial.isPeriodicNumericalPolynomial

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
  rcases graded_hilbert_polynomial G 𝓜 hS hdegree with ⟨r, a, ha⟩
  refine ⟨r, fun i => kPrimeZeroLength (R := degreeZeroSubring G) (a i), ?_⟩
  filter_upwards [ha] with n hn
  change kPrimeZeroLength (R := degreeZeroSubring G)
      (noetherianGradedHilbertFunction G 𝓜 hS n) = _
  rw [hn]
  simp only [map_sum, map_zsmul]

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
