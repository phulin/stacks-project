import Mathlib.Algebra.CharP.Frobenius
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.RingTheory.Ideal.Cotangent
import Mathlib.RingTheory.Length
import Mathlib.RingTheory.Regular.RegularSequence
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RingHom.Flat

namespace Formalization.Books.LocalCohomology.Unit17

noncomputable section

open scoped BigOperators TensorProduct

/-!
This file records the declarations from Chapter 17, “Frobenius action”.  The
proofs are intentionally deferred; the definitions use Mathlib's canonical
Frobenius, cotangent-module, tensor-product, length, and flatness APIs.
-/

/-- Frobenius base change of a module, with the scalar action on the second
factor restricted along the Frobenius endomorphism. -/
def frobeniusBaseChange
    {A M : Type*} [CommRing A] [AddCommGroup M] [Module A M]
    (p : ℕ) [ExpChar A p] : Prop :=
  letI : Module A A := Module.compHom A (frobenius A p)
  Nonempty ((M ⊗[A] A) ≃ₗ[A] M)

/-- A finite Frobenius-stable module over a Noetherian local ring is free. -/
theorem finite_frobenius_base_change_is_free
    {A M : Type*} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    [AddCommGroup M] [Module A M] [Module.Finite A M]
    (p : ℕ) [Fact p.Prime] [CharP A p]
    (hM : frobeniusBaseChange (A := A) (M := M) p) :
    Module.Free A M := by
  sorry

/-- The conormal class represented by an entry of a list of generators. -/
def conormalGenerator
    {A : Type*} [CommRing A] (xs : List A) (i : Fin xs.length) :
    Ideal.Cotangent (Ideal.ofList xs) :=
  Ideal.toCotangent (Ideal.ofList xs)
    ⟨xs.get i, by
      apply Ideal.subset_span
      exact xs.get_mem i⟩

/-- Independence of a list of ring elements, as used in the chapter. -/
def independent {A : Type*} [CommRing A] (xs : List A) : Prop :=
  ∀ (a : Fin xs.length → A),
    (∑ i, a i * xs.get i = 0) →
      ∀ i, a i ∈ Ideal.ofList xs

private theorem ofList_rep
    {A : Type*} [CommRing A] (xs : List A) {c : A}
    (hc : c ∈ Ideal.ofList xs) :
    ∃ q : Fin xs.length → A, (∑ i, q i * xs.get i) = c := by
  have hrange : {x : A | x ∈ xs} =
      Set.range (fun i : Fin xs.length => xs.get i) := by
    ext x
    constructor
    · intro hx
      rcases List.mem_iff_get.mp hx with ⟨i, hi⟩
      exact ⟨i, hi⟩
    · rintro ⟨i, rfl⟩
      exact xs.get_mem i
  change c ∈ Ideal.span {x : A | x ∈ xs} at hc
  rw [hrange] at hc
  exact Ideal.mem_span_range_iff_exists_fun.mp hc

/-- The list formulation of independence is equivalent to the conormal basis
formulation in the text. -/
theorem independent_iff_cotangent_has_basis
    {A : Type*} [CommRing A] (xs : List A) :
    independent xs ↔
      ∃ b : Module.Basis (Fin xs.length) (A ⧸ Ideal.ofList xs)
          (Ideal.Cotangent (Ideal.ofList xs)),
        ∀ i, b i = conormalGenerator xs i := by
  classical
  let I : Ideal A := Ideal.ofList xs
  let v : Fin xs.length → I.Cotangent := fun i => conormalGenerator xs i
  have hxi (i : Fin xs.length) : xs.get i ∈ I := by
    change xs.get i ∈ Ideal.ofList xs
    apply Ideal.subset_span
    exact xs.get_mem i
  have hsum_conormal (c : Fin xs.length → A) :
      I.toCotangent ⟨∑ i, c i * xs.get i,
        I.sum_mem fun i _ => I.mul_mem_left (c i) (hxi i)⟩ =
        ∑ i, (Ideal.Quotient.mk I (c i)) • v i := by
    have heq : (⟨∑ i, c i * xs.get i,
        I.sum_mem fun i _ => I.mul_mem_left (c i) (hxi i)⟩ : I) =
        ∑ i, (⟨c i * xs.get i, I.mul_mem_left (c i) (hxi i)⟩ : I) := by
      ext
      simp
    rw [heq, map_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rfl
  have hgen : I = Ideal.span (Set.range (fun i : Fin xs.length => xs.get i)) := by
    change Ideal.span {x : A | x ∈ xs} = _
    congr 1
    ext x
    constructor
    · intro hx
      rcases List.mem_iff_get.mp hx with ⟨i, hi⟩
      exact ⟨i, hi⟩
    · rintro ⟨i, rfl⟩
      exact xs.get_mem i
  have hspan : Submodule.span (A ⧸ I) (Set.range v) = ⊤ := by
    refine top_unique ?_
    intro z hz
    obtain ⟨y, rfl⟩ := I.toCotangent_surjective z
    rcases ofList_rep xs (c := y.1) y.2 with ⟨c, hc⟩
    have hy : y = ⟨∑ i, c i * xs.get i, hc ▸ y.2⟩ := Subtype.ext hc.symm
    rw [hy]
    rw [hsum_conormal]
    apply Submodule.sum_mem
    intro i hi
    have hmem : (Ideal.Quotient.mk I (c i)) • v i ∈
        Submodule.span (A ⧸ I) (Set.range v) :=
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    simpa [v, conormalGenerator] using hmem
  have hli : LinearIndependent (A ⧸ I) v ↔ independent xs := by
    constructor
    · intro hv a ha i
      have hrel : (∑ j, (Ideal.Quotient.mk I (a j)) • v j) = 0 := by
        rw [← hsum_conormal a]
        rw [Ideal.toCotangent_eq_zero]
        change (∑ j, a j * xs.get j) ∈ I ^ 2
        rw [ha]
        exact (I ^ 2).zero_mem
      have hzero := (Fintype.linearIndependent_iff.mp hv)
        (fun j => Ideal.Quotient.mk I (a j)) hrel i
      exact (Ideal.Quotient.eq_zero_iff_mem).mp hzero
    · intro hi
      rw [Fintype.linearIndependent_iff]
      intro c hc i
      let a : Fin xs.length → A := fun j => Classical.choose
        (Ideal.Quotient.mk_surjective (c j))
      have ha (j : Fin xs.length) : Ideal.Quotient.mk I (a j) = c j := by
        exact Classical.choose_spec (Ideal.Quotient.mk_surjective (c j))
      have hrel : I.toCotangent
          ⟨∑ j, a j * xs.get j, I.sum_mem fun j _ =>
            I.mul_mem_left (a j) (hxi j)⟩ = 0 := by
        rw [hsum_conormal a]
        simpa [ha] using hc
      have hsquare : (∑ j, a j * xs.get j) ∈ I ^ 2 := by
        exact I.mem_toCotangent_ker.mp hrel
      have hmem : (∑ j, a j * xs.get j) ∈
          I • Submodule.span A (Set.range (fun j : Fin xs.length => xs.get j)) := by
        simpa [hgen, pow_two, smul_eq_mul] using hsquare
      rcases (Submodule.mem_ideal_smul_span_iff_exists_sum I
        (fun j : Fin xs.length => xs.get j) _).mp hmem with ⟨q, hq, hqsum⟩
      have hqsum' : (∑ j, q j * xs.get j) = ∑ j, a j * xs.get j := by
        simpa [Finsupp.sum_fintype] using hqsum
      have hzero : (∑ j, (a j - q j) * xs.get j) = 0 := by
        calc
          (∑ j, (a j - q j) * xs.get j) =
              ∑ j, (a j * xs.get j - q j * xs.get j) := by
                apply Finset.sum_congr rfl
                intro j hj
                ring
          _ = (∑ j, a j * xs.get j) - ∑ j, q j * xs.get j := by
            rw [Finset.sum_sub_distrib]
          _ = 0 := by rw [hqsum']; exact sub_self _
      have hcoeff := hi (fun j => a j - q j) hzero i
      have hqi : q i ∈ I := hq i
      have hai : a i ∈ I := by
        simpa [sub_eq_add_neg, add_comm] using I.add_mem hcoeff hqi
      rw [← (Ideal.Quotient.eq_zero_iff_mem).mpr hai, ha]
  constructor
  · intro hi
    let b : Module.Basis (Fin xs.length) (A ⧸ I) I.Cotangent :=
      Module.Basis.mk (hli.mpr hi) (by simpa [hspan])
    refine ⟨b, ?_⟩
    intro i
    exact Module.Basis.mk_apply _ _ i
  · rintro ⟨b, hb⟩
    apply hli.mp
    change LinearIndependent (A ⧸ I) v
    change LinearIndependent (A ⧸ Ideal.ofList xs)
      (fun i => conormalGenerator xs i)
    have heq : (fun i => conormalGenerator xs i) = b :=
      funext fun i => (hb i).symm
    exact heq ▸ b.linearIndependent

private theorem independent_append_mul_factor_pullback
    {A : Type*} [CommRing A] (xs : List A) (f g : A)
    (h : independent (xs ++ [f * g]))
    (b : Fin (xs.length + 1) → A)
    (hb : (∑ i : Fin xs.length, b i.castSucc * xs.get i) +
        b (Fin.last xs.length) * (f * g) = 0) :
    ∀ i, b i ∈ Ideal.ofList xs ⊔ Ideal.span {f * g} := by
  classical
  let efg : Fin (xs.length + 1) ≃ Fin (xs ++ [f * g]).length :=
    finCongr (by simp)
  have sum_fg :
      (∑ i, b i * (xs ++ [f * g]).get (efg i)) =
        (∑ i : Fin xs.length, b i.castSucc * xs.get i) +
          b (Fin.last xs.length) * (f * g) := by
    rw [Fin.sum_univ_castSucc]
    simp [efg, finCongr_apply]
  have hsum : (∑ j, b (efg.symm j) * (xs ++ [f * g]).get j) = 0 := by
    have he := Fintype.sum_equiv efg
      (fun i => b i * (xs ++ [f * g]).get (efg i))
      (fun j => b (efg.symm j) * (xs ++ [f * g]).get j)
      (by intro i; simp)
    rw [← he, sum_fg]
    exact hb
  have hh := h (fun j => b (efg.symm j)) hsum
  intro i
  simpa using hh (efg i)

private theorem independent_append_mul_factor_last
    {A : Type*} [CommRing A] (xs : List A) (f g : A)
    (a : Fin (xs.length + 1) → A)
    (ha : (∑ i : Fin xs.length, a i.castSucc * xs.get i) +
        a (Fin.last xs.length) * f = 0)
    (hp : ∀ b : Fin (xs.length + 1) → A,
      (∑ i : Fin xs.length, b i.castSucc * xs.get i) +
          b (Fin.last xs.length) * (f * g) = 0 →
        ∀ i, b i ∈ Ideal.ofList xs ⊔ Ideal.span {f * g}) :
    a (Fin.last xs.length) ∈ Ideal.ofList xs ⊔ Ideal.span {f * g} := by
  classical
  let b : Fin (xs.length + 1) → A :=
    Fin.snoc (fun i => a i.castSucc * g) (a (Fin.last xs.length))
  have hb : (∑ i : Fin xs.length, b i.castSucc * xs.get i) +
      b (Fin.last xs.length) * (f * g) = 0 := by
    simp only [b, Fin.snoc_castSucc, Fin.snoc_last]
    calc
      (∑ i : Fin xs.length, a i.castSucc * g * xs.get i) +
          a (Fin.last xs.length) * (f * g) =
        g * ((∑ i : Fin xs.length, a i.castSucc * xs.get i) +
          a (Fin.last xs.length) * f) := by
            calc
              (∑ i : Fin xs.length, a i.castSucc * g * xs.get i) +
                  a (Fin.last xs.length) * (f * g) =
                (∑ i : Fin xs.length, g * (a i.castSucc * xs.get i)) +
                  g * (a (Fin.last xs.length) * f) := by
                    congr 1
                    · apply Finset.sum_congr rfl
                      intro i hi
                      ring
                    · ring
              _ = g * ((∑ i : Fin xs.length, a i.castSucc * xs.get i) +
                  a (Fin.last xs.length) * f) := by
                    have hm := Finset.mul_sum (Finset.univ : Finset (Fin xs.length))
                      (fun i => a i.castSucc * xs.get i) g
                    rw [← hm]
                    ring
      _ = 0 := by rw [ha, mul_zero]
  have hb' := hp b hb
  simpa [b] using hb' (Fin.last xs.length)

private theorem independent_append_mul_factor_nonlast
    {A : Type*} [CommRing A] (xs : List A) (f g : A)
    (a : Fin (xs.length + 1) → A)
    (ha : (∑ i : Fin xs.length, a i.castSucc * xs.get i) +
        a (Fin.last xs.length) * f = 0)
    (hp : ∀ b : Fin (xs.length + 1) → A,
      (∑ i : Fin xs.length, b i.castSucc * xs.get i) +
          b (Fin.last xs.length) * (f * g) = 0 →
        ∀ i, b i ∈ Ideal.ofList xs ⊔ Ideal.span {f * g})
    (c d : A) (q : Fin xs.length → A) (r : A)
    (hq : (∑ i : Fin xs.length, q i * xs.get i) = c)
    (hr : r * (f * g) = d)
    (hcd : c + d = a (Fin.last xs.length)) :
    ∀ i : Fin xs.length, a i.castSucc ∈ Ideal.ofList xs ⊔ Ideal.span {f} := by
  classical
  let cfn : Fin (xs.length + 1) → A :=
    Fin.snoc (fun i => a i.castSucc + q i * f) (r * f)
  have hcfn : (∑ i : Fin xs.length, cfn i.castSucc * xs.get i) +
      cfn (Fin.last xs.length) * (f * g) = 0 := by
    simp only [cfn, Fin.snoc_castSucc, Fin.snoc_last]
    have hsum_add :
        (∑ i : Fin xs.length, (a i.castSucc + q i * f) * xs.get i) =
          (∑ i : Fin xs.length, a i.castSucc * xs.get i) +
            (∑ i : Fin xs.length, (q i * f) * xs.get i) := by
      calc
        (∑ i : Fin xs.length, (a i.castSucc + q i * f) * xs.get i) =
            ∑ i : Fin xs.length,
              ((a i.castSucc * xs.get i) + ((q i * f) * xs.get i)) := by
                apply Finset.sum_congr rfl
                intro i hi
                ring
        _ = (∑ i : Fin xs.length, a i.castSucc * xs.get i) +
            (∑ i : Fin xs.length, (q i * f) * xs.get i) := by
              simpa using (Finset.sum_add_distrib
                (s := (Finset.univ : Finset (Fin xs.length)))
                (f := fun i => a i.castSucc * xs.get i)
                (g := fun i => (q i * f) * xs.get i))
    have hqsum :
        (∑ i : Fin xs.length, (q i * f) * xs.get i) =
          f * (∑ i : Fin xs.length, q i * xs.get i) := by
      calc
        (∑ i : Fin xs.length, (q i * f) * xs.get i) =
            ∑ i : Fin xs.length, f * (q i * xs.get i) := by
              apply Finset.sum_congr rfl
              intro i hi
              ring
        _ = f * (∑ i : Fin xs.length, q i * xs.get i) := by
              have hm := Finset.mul_sum (Finset.univ : Finset (Fin xs.length))
                (fun i => q i * xs.get i) f
              exact hm.symm
    have hr' : (r * f) * (f * g) = f * d := by
      calc
        (r * f) * (f * g) = f * (r * (f * g)) := by ring
        _ = f * d := by rw [hr]
    calc
      (∑ i : Fin xs.length, (a i.castSucc + q i * f) * xs.get i) +
          (r * f) * (f * g) =
        (∑ i : Fin xs.length, a i.castSucc * xs.get i) + f * c + f * d := by
            rw [hsum_add, hqsum, hq, hr']
      _ = (∑ i : Fin xs.length, a i.castSucc * xs.get i) +
          f * (c + d) := by ring
      _ = (∑ i : Fin xs.length, a i.castSucc * xs.get i) +
          a (Fin.last xs.length) * f := by rw [hcd]; ring
      _ = 0 := by simpa [mul_comm] using ha
  have hcfn' := hp cfn hcfn
  have hprodle :
      Ideal.ofList xs ⊔ Ideal.span {f * g} ≤ Ideal.ofList xs ⊔ Ideal.span {f} := by
    refine sup_le le_sup_left ?_
    refine Ideal.span_le.2 ?_
    intro x hx
    rcases Set.mem_singleton_iff.mp hx with rfl
    simpa [mul_comm] using
      (Ideal.mul_mem_left (Ideal.ofList xs ⊔ Ideal.span {f}) g
        (Ideal.mem_sup_right (Ideal.subset_span (Set.mem_singleton f))))
  intro i
  have hi := hcfn' i.castSucc
  have hi' := hprodle hi
  have hqf : q i * f ∈ Ideal.ofList xs ⊔ Ideal.span {f} :=
    Ideal.mul_mem_left (Ideal.ofList xs ⊔ Ideal.span {f}) (q i)
      (Ideal.mem_sup_right (Ideal.subset_span (Set.mem_singleton f)))
  simpa [cfn] using
    (Ideal.sub_mem (Ideal.ofList xs ⊔ Ideal.span {f}) hi' hqf)

private theorem independent_append_mul_factor_finish
    {A : Type*} [CommRing A] (xs : List A) (f g : A)
    (a : Fin (xs.length + 1) → A)
    (hlast : a (Fin.last xs.length) ∈
      Ideal.ofList xs ⊔ Ideal.span {f * g})
    (hnon : ∀ i : Fin xs.length,
      a i.castSucc ∈ Ideal.ofList xs ⊔ Ideal.span {f}) :
    ∀ i, a i ∈ Ideal.ofList xs ⊔ Ideal.span {f} := by
  have hprodle :
      Ideal.ofList xs ⊔ Ideal.span {f * g} ≤ Ideal.ofList xs ⊔ Ideal.span {f} := by
    refine sup_le le_sup_left ?_
    refine Ideal.span_le.2 ?_
    intro x hx
    rcases Set.mem_singleton_iff.mp hx with rfl
    simpa [mul_comm] using (Ideal.mul_mem_left (Ideal.ofList xs ⊔ Ideal.span {f}) g
      (Ideal.mem_sup_right (Ideal.subset_span (Set.mem_singleton f))))
  intro i
  refine Fin.lastCases ?_ ?_ i
  · exact hprodle hlast
  · intro i
    exact hnon i

private theorem independent_append_mul_factor_sup_decompose
    {A : Type*} [CommRing A] {I J : Ideal A} {x : A}
    (hx : x ∈ I ⊔ J) :
    ∃ c ∈ I, ∃ d ∈ J, c + d = x := by
  exact Submodule.mem_sup.mp hx

private theorem independent_mul_colon
    {A : Type*} [CommRing A] (xs : List A) (f g : A)
    (h : independent (xs ++ [f * g])) (x : A)
    (hx : f * x ∈ Ideal.ofList (xs ++ [f * g])) :
    x ∈ Ideal.ofList (xs ++ [g]) := by
  classical
  have hx' : f * x ∈ Ideal.ofList xs ⊔ Ideal.span {f * g} := by
    simpa [Ideal.ofList_append] using hx
  have rep : ∀ {c : A}, c ∈ Ideal.ofList xs →
      ∃ q : Fin xs.length → A, (∑ i, q i * xs.get i) = c := by
    intro c hc
    have hrange : {y : A | y ∈ xs} =
        Set.range (fun i : Fin xs.length => xs.get i) := by
      ext y
      constructor
      · intro hy
        rcases List.mem_iff_get.mp hy with ⟨i, hi⟩
        exact ⟨i, hi⟩
      · rintro ⟨i, rfl⟩
        exact xs.get_mem i
    change c ∈ Ideal.span {y : A | y ∈ xs} at hc
    rw [hrange] at hc
    exact Ideal.mem_span_range_iff_exists_fun.mp hc
  rcases independent_append_mul_factor_sup_decompose hx' with
    ⟨c, hc, d, hd, hcd⟩
  rcases rep hc with ⟨q, hq⟩
  rcases Ideal.mem_span_singleton'.mp hd with ⟨r, hr⟩
  let b : Fin (xs.length + 1) → A :=
    Fin.snoc (fun i => q i * g) (r * g - x)
  have hb : (∑ i : Fin xs.length, b i.castSucc * xs.get i) +
      b (Fin.last xs.length) * (f * g) = 0 := by
    simp only [b, Fin.snoc_castSucc, Fin.snoc_last]
    have hsum :
        (∑ i : Fin xs.length, q i * g * xs.get i) = g * c := by
      have hm := Finset.mul_sum (Finset.univ : Finset (Fin xs.length))
        (fun i => q i * xs.get i) g
      calc
        (∑ i : Fin xs.length, q i * g * xs.get i) =
            ∑ i : Fin xs.length, g * (q i * xs.get i) := by
              apply Finset.sum_congr rfl
              intro i hi
              ring
        _ = g * (∑ i : Fin xs.length, q i * xs.get i) := hm.symm
        _ = g * c := by rw [hq]
    have hr' : (r * g) * (f * g) = g * d := by
      calc
        (r * g) * (f * g) = g * (r * (f * g)) := by ring
        _ = g * d := by rw [hr]
    have hdiff : (r * g - x) * (f * g) = g * d - x * (f * g) := by
      calc
        (r * g - x) * (f * g) = (r * g) * (f * g) - x * (f * g) := by
          rw [sub_mul]
        _ = g * d - x * (f * g) := by rw [hr']
    calc
      (∑ i : Fin xs.length, q i * g * xs.get i) +
          (r * g - x) * (f * g) = g * c + g * d - x * (f * g) := by
            rw [hsum, hdiff]
            ring
      _ = g * (c + d) - x * (f * g) := by ring
      _ = 0 := by rw [hcd]; ring
  have hb' := independent_append_mul_factor_pullback xs f g h b hb
  have hlast : r * g - x ∈ Ideal.ofList xs ⊔ Ideal.span {f * g} := by
    simpa [b] using hb' (Fin.last xs.length)
  have hle : Ideal.ofList xs ⊔ Ideal.span {f * g} ≤
      Ideal.ofList xs ⊔ Ideal.span {g} := by
    refine sup_le le_sup_left ?_
    refine Ideal.span_le.2 ?_
    intro y hy
    rcases Set.mem_singleton_iff.mp hy with rfl
    simpa [mul_comm] using (Ideal.mul_mem_left
      (Ideal.ofList xs ⊔ Ideal.span {g}) f
      (Ideal.mem_sup_right (Ideal.subset_span (Set.mem_singleton g))))
  have hrg : r * g ∈ Ideal.ofList xs ⊔ Ideal.span {g} :=
    Ideal.mul_mem_left (Ideal.ofList xs ⊔ Ideal.span {g}) r
      (Ideal.mem_sup_right (Ideal.subset_span (Set.mem_singleton g)))
  have hsub := Ideal.sub_mem (Ideal.ofList xs ⊔ Ideal.span {g}) hrg (hle hlast)
  simpa [Ideal.ofList_append] using hsub

private theorem independent_append_mul_factor_ofList_rep
    {A : Type*} [CommRing A] (xs : List A) {c : A}
    (hc : c ∈ Ideal.ofList xs) :
    ∃ q : Fin xs.length → A, (∑ i, q i * xs.get i) = c := by
  have hrange : {x : A | x ∈ xs} =
      Set.range (fun i : Fin xs.length => xs.get i) := by
    ext x
    constructor
    · intro hx
      rcases List.mem_iff_get.mp hx with ⟨i, hi⟩
      exact ⟨i, hi⟩
    · rintro ⟨i, rfl⟩
      exact xs.get_mem i
  change c ∈ Ideal.span {x : A | x ∈ xs} at hc
  rw [hrange] at hc
  exact Ideal.mem_span_range_iff_exists_fun.mp hc

private theorem independent_append_mul_factor_coeff
    {A : Type*} [CommRing A] (xs : List A) (f g : A)
    (a : Fin (xs.length + 1) → A)
    (ha : (∑ i : Fin xs.length, a i.castSucc * xs.get i) +
        a (Fin.last xs.length) * f = 0)
    (hp : ∀ b : Fin (xs.length + 1) → A,
      (∑ i : Fin xs.length, b i.castSucc * xs.get i) +
          b (Fin.last xs.length) * (f * g) = 0 →
        ∀ i, b i ∈ Ideal.ofList xs ⊔ Ideal.span {f * g}) :
    ∀ i, a i ∈ Ideal.ofList xs ⊔ Ideal.span {f} := by
  classical
  have hlast := independent_append_mul_factor_last xs f g a ha hp
  have hprodle :
      Ideal.ofList xs ⊔ Ideal.span {f * g} ≤ Ideal.ofList xs ⊔ Ideal.span {f} := by
    refine sup_le le_sup_left ?_
    refine Ideal.span_le.2 ?_
    intro x hx
    rcases Set.mem_singleton_iff.mp hx with rfl
    simpa [mul_comm] using (Ideal.mul_mem_left (Ideal.ofList xs ⊔ Ideal.span {f}) g
      (Ideal.mem_sup_right (Ideal.subset_span (Set.mem_singleton f))))
  intro i
  refine Fin.lastCases ?_ ?_ i
  · exact hprodle hlast
  · intro i
    rcases independent_append_mul_factor_sup_decompose hlast with
      ⟨c, hc, d, hd, hcd⟩
    rcases independent_append_mul_factor_ofList_rep xs hc with ⟨q, hq⟩
    rcases Ideal.mem_span_singleton'.mp hd with ⟨r, hr⟩
    have hnon := independent_append_mul_factor_nonlast xs f g a ha hp c d q r hq hr hcd
    exact hnon i

private theorem independent_append_mul_factor_relation
    {A : Type*} [CommRing A] (xs : List A) (f : A)
    (a : Fin (xs ++ [f]).length → A)
    (ha : ∑ i, a i * (xs ++ [f]).get i = 0) :
    (∑ i : Fin xs.length, a ((finCongr (by simp) :
        Fin (xs.length + 1) ≃ Fin (xs ++ [f]).length) i.castSucc) * xs.get i) +
      a ((finCongr (by simp) :
        Fin (xs.length + 1) ≃ Fin (xs ++ [f]).length) (Fin.last xs.length)) * f = 0 := by
  classical
  let ef : Fin (xs.length + 1) ≃ Fin (xs ++ [f]).length := finCongr (by simp)
  have sum_f (b : Fin (xs.length + 1) → A) :
      (∑ i, b i * (xs ++ [f]).get (ef i)) =
        (∑ i : Fin xs.length, b i.castSucc * xs.get i) +
          b (Fin.last xs.length) * f := by
    rw [Fin.sum_univ_castSucc]
    simp [ef, finCongr_apply]
  rw [← sum_f (fun i => a (ef i))]
  have he := Fintype.sum_equiv ef
    (fun i => a (ef i) * (xs ++ [f]).get (ef i))
    (fun j => a j * (xs ++ [f]).get j)
    (by intro i; simp)
  rw [he]
  exact ha

private theorem independent_append_mul_factor_core
    {A : Type*} [CommRing A] (xs : List A) (f g : A)
    (h : independent (xs ++ [f * g])) :
    independent (xs ++ [f]) := by
  classical
  intro a ha
  let ef : Fin (xs.length + 1) ≃ Fin (xs ++ [f]).length := finCongr (by simp)
  have ha' := independent_append_mul_factor_relation xs f a ha
  have hp := independent_append_mul_factor_pullback xs f g h
  have hres := independent_append_mul_factor_coeff xs f g
    (fun i => a (ef i)) ha' hp
  intro i
  simpa [Ideal.ofList_append] using hres (ef.symm i)

/-- Lemma 1: an independent product in the last position can be replaced by
its first factor. -/
theorem independent_append_mul_factor
    {A : Type*} [CommRing A] (xs : List A) (f g : A)
    (h : independent (xs ++ [f * g])) :
    independent (xs ++ [f]) := by
  exact independent_append_mul_factor_core xs f g h

/-- The exact sequence used to split the length of a quotient after replacing
the last generator by a product.  The two maps are characterized on quotient
representatives by the displayed multiplication and quotient maps. -/
theorem independent_multiplication_exact
    {A : Type*} [CommRing A] (xs : List A) (f g : A)
    (h : independent (xs ++ [f * g])) :
    ∃ (u : (A ⧸ Ideal.ofList (xs ++ [g])) →ₗ[A]
          (A ⧸ Ideal.ofList (xs ++ [f * g])))
      (v : (A ⧸ Ideal.ofList (xs ++ [f * g])) →ₗ[A]
          (A ⧸ Ideal.ofList (xs ++ [f]))),
      Function.Injective u ∧ Function.Surjective v ∧ Function.Exact u v ∧
        (∀ x : A,
          u (Ideal.Quotient.mk (Ideal.ofList (xs ++ [g])) x) =
            Ideal.Quotient.mk (Ideal.ofList (xs ++ [f * g])) (f * x)) ∧
        (∀ x : A,
          v (Ideal.Quotient.mk (Ideal.ofList (xs ++ [f * g])) x) =
            Ideal.Quotient.mk (Ideal.ofList (xs ++ [f])) x) := by
  classical
  let Ig : Ideal A := Ideal.ofList (xs ++ [g])
  let Ifg : Ideal A := Ideal.ofList (xs ++ [f * g])
  let If : Ideal A := Ideal.ofList (xs ++ [f])
  have hmul : ∀ y, y ∈ Ig → f * y ∈ Ifg := by
    intro y hy
    rw [show Ig = Ideal.ofList xs ⊔ Ideal.span {g} by
      simp [Ig, Ideal.ofList_append]] at hy
    rw [show Ifg = Ideal.ofList xs ⊔ Ideal.span {f * g} by
      simp [Ifg, Ideal.ofList_append]]
    rcases Submodule.mem_sup.mp hy with ⟨c, hc, d, hd, hcd⟩
    rw [← hcd, mul_add]
    apply add_mem
    · exact Ideal.mul_mem_left (Ideal.ofList xs ⊔ Ideal.span {f * g}) f
        ((show Ideal.ofList xs ≤ Ideal.ofList xs ⊔ Ideal.span {f * g} from le_sup_left) hc)
    · rcases Ideal.mem_span_singleton'.mp hd with ⟨r, hr⟩
      rw [← hr]
      simpa [mul_assoc, mul_comm, mul_left_comm] using
        (Ideal.mul_mem_left (Ideal.ofList xs ⊔ Ideal.span {f * g}) r
          (Ideal.mem_sup_right (Ideal.subset_span (Set.mem_singleton (f * g)))))
  let hu0 : A →ₗ[A] (A ⧸ Ifg) :=
    Ifg.mkQ.comp (LinearMap.mulLeft A f)
  have hu : Ig ≤ LinearMap.ker hu0 := by
    intro y hy
    rw [LinearMap.mem_ker]
    simpa [hu0] using (Ideal.Quotient.eq_zero_iff_mem.mpr (hmul y hy))
  let u : (A ⧸ Ig) →ₗ[A] (A ⧸ Ifg) := Ig.liftQ hu0 hu
  have hcolon : LinearMap.ker hu0 ≤ Ig := by
    intro y hy
    rw [LinearMap.mem_ker] at hy
    change Ideal.Quotient.mk Ifg (f * y) = 0 at hy
    rw [Ideal.Quotient.eq_zero_iff_mem] at hy
    exact independent_mul_colon xs f g h y hy
  have huinj : Function.Injective u := by
    apply LinearMap.ker_eq_bot.mp
    exact Submodule.ker_liftQ_eq_bot Ig hu0 hu hcolon
  have hv : Ifg ≤ LinearMap.ker If.mkQ := by
    intro y hy
    rw [LinearMap.mem_ker]
    change Ideal.Quotient.mk If y = 0
    rw [Ideal.Quotient.eq_zero_iff_mem]
    rw [show Ifg = Ideal.ofList xs ⊔ Ideal.span {f * g} by
      simp [Ifg, Ideal.ofList_append]] at hy
    rw [show If = Ideal.ofList xs ⊔ Ideal.span {f} by
      simp [If, Ideal.ofList_append]]
    rcases Submodule.mem_sup.mp hy with ⟨c, hc, d, hd, hcd⟩
    rw [← hcd]
    apply add_mem
    · exact (show Ideal.ofList xs ≤ Ideal.ofList xs ⊔ Ideal.span {f} from le_sup_left) hc
    rcases Ideal.mem_span_singleton'.mp hd with ⟨r, hr⟩
    rw [← hr]
    have hfg : f * g ∈ Ideal.ofList xs ⊔ Ideal.span {f} := by
      simpa [mul_comm] using
        (Ideal.mul_mem_left (Ideal.ofList xs ⊔ Ideal.span {f}) g
          (Ideal.mem_sup_right (Ideal.subset_span (Set.mem_singleton f))))
    exact Ideal.mul_mem_left (Ideal.ofList xs ⊔ Ideal.span {f}) r hfg
  let v : (A ⧸ Ifg) →ₗ[A] (A ⧸ If) := Ifg.liftQ If.mkQ hv
  have hvsurj : Function.Surjective v := by
    intro y
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    exact ⟨Ideal.Quotient.mk Ifg x, by
      simpa [v] using (Submodule.liftQ_apply Ifg If.mkQ x)
      ⟩
  have hexact : Function.Exact u v := by
    apply LinearMap.exact_of_comp_of_mem_range
    · apply LinearMap.ext
      intro y
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
      dsimp [u]
      rw [← Ideal.Quotient.mk_eq_mk]
      rw [Submodule.liftQ_apply]
      dsimp [v, hu0]
      rw [← Ideal.Quotient.mk_eq_mk]
      rw [Submodule.liftQ_apply]
      change Ideal.Quotient.mk If (f * x) = 0
      rw [Ideal.Quotient.eq_zero_iff_mem]
      have hfIf : f ∈ If := by
        rw [show If = Ideal.ofList xs ⊔ Ideal.span {f} by
          simp [If, Ideal.ofList_append]]
        exact Ideal.mem_sup_right (Ideal.subset_span (Set.mem_singleton f))
      exact Ideal.mul_mem_right _ If hfIf
    · intro y hy
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
      change Ideal.Quotient.mk If x = 0 at hy
      rw [Ideal.Quotient.eq_zero_iff_mem] at hy
      have hy' : x ∈ Ideal.ofList xs ⊔ Ideal.span {f} := by
        simpa [If, Ideal.ofList_append] using hy
      rcases Submodule.mem_sup.mp hy' with ⟨c, hc, d, hd, hcd⟩
      rcases ofList_rep xs hc with ⟨q, hq⟩
      rcases Ideal.mem_span_singleton'.mp hd with ⟨r, hr⟩
      refine ⟨Ideal.Quotient.mk Ig r, ?_⟩
      change Ideal.Quotient.mk Ifg (f * r) = Ideal.Quotient.mk Ifg x
      rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem]
      have hdiff : f * r - x = -c := by
        rw [← hcd, ← hr]
        ring
      rw [hdiff]
      exact Ifg.neg_mem ((show Ideal.ofList xs ≤ Ifg from by
        simp [Ifg, Ideal.ofList_append]) hc)
  refine ⟨u, v, huinj, hvsurj, hexact, ?_, ?_⟩
  · intro x
    dsimp [u, hu0]
    rw [← Ideal.Quotient.mk_eq_mk]
    rw [Submodule.liftQ_apply]
    exact map_mul (Ideal.Quotient.mk Ifg) f x
  · intro x
    dsimp [v]
    rw [← Ideal.Quotient.mk_eq_mk]
    rw [Submodule.liftQ_apply]
    exact Ideal.Quotient.mk_eq_mk x

/-- Length additivity for the independent product replacement in Lemma 2. -/
theorem independent_length_mul
    {A : Type*} [CommRing A] (xs : List A) (f g : A)
    (h : independent (xs ++ [f * g]))
    (hfinite : IsFiniteLength A
      (A ⧸ Ideal.ofList (xs ++ [f * g]))) :
    Module.length A (A ⧸ Ideal.ofList (xs ++ [f * g])) =
      Module.length A (A ⧸ Ideal.ofList (xs ++ [f])) +
        Module.length A (A ⧸ Ideal.ofList (xs ++ [g])) := by
  rcases independent_multiplication_exact xs f g h with
    ⟨u, v, hu, hv, hexact, -, -⟩
  simpa [add_comm] using Module.length_eq_add_of_exact u v hu hv hexact

/-- The list of powers appearing in Lemma 3. -/
def powerList {A : Type*} [CommRing A] (xs : List A)
    (e : Fin xs.length → ℕ) : List A :=
  List.ofFn (fun i => (xs.get i) ^ e i)

/-- The length of a quotient by independent powers of a system of generators. -/
theorem length_quotient_of_independent_powers
    {A : Type*} [CommRing A] [IsLocalRing A] (xs : List A)
    (hmax : Ideal.ofList xs = IsLocalRing.maximalIdeal A)
    (e : Fin xs.length → ℕ) (he : ∀ i, 0 < e i)
    (h : independent (powerList xs e)) :
    Module.length A (A ⧸ Ideal.ofList (powerList xs e)) =
      (↑(∏ i : Fin xs.length, e i) : ℕ∞) := by
  sorry

/-- Flat extension preserves the chapter's independence condition. -/
theorem independent_map_of_flat
    {A B : Type*} [CommRing A] [CommRing B] (φ : A →+* B)
    (hφ : RingHom.Flat φ) (xs : List A) (h : independent xs) :
    independent (xs.map φ) := by
  sorry

/-- Kunz's characterization of regular Noetherian rings by flat Frobenius. -/
theorem kunz_frobenius_flat_iff_regular
    {A : Type*} [CommRing A] [IsNoetherianRing A] (p : ℕ)
    [Fact p.Prime] [CharP A p] :
    IsRegularRing A ↔ RingHom.Flat (frobenius A p) := by
  sorry

end

end Formalization.Books.LocalCohomology.Unit17
