import Formalization.Books.Algebra.Unit07.FiniteRingMaps
import Formalization.Books.Algebra.Unit39.FlatModules
import Formalization.Books.MoreAlgebra.Unit16.FlatteningStratification
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Extension.Generators
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.TensorProduct.Basic

/-!
# More on Algebra, Chapter 21: Descent of flatness along integral maps

This file records the seven lemmas in the source section.  Polynomial rings in
finitely many variables use `MvPolynomial (Fin n) R`, and the source's
quotient presentation with split one-variable relations is bundled in
`SplitPolynomialPresentation` so that the displayed ideals and evaluation
maps have a reusable Lean interface.
-/

namespace Formalization.Books.MoreAlgebra.Unit21

open Set
open scoped BigOperators TensorProduct

noncomputable section

universe u v

/-! ## Splitting data -/

/- The source writes a product of linear factors in one variable.  This is
   the canonical polynomial representative of that product. -/
/-- The monic polynomial whose roots are the entries of `α`. -/
def splitPolynomial {R : Type*} [CommRing R] {d : ℕ} (α : Fin d → R) : Polynomial R :=
  ∏ j : Fin d, (Polynomial.X - Polynomial.C (α j))

/- The map `T_i ↦ α_{i,k_i}` in the source is the canonical multivariate
   evaluation homomorphism. -/
/-- Evaluation of a finite-variable polynomial at one selected root in each
variable. -/
def splitEvaluationHom {R : Type*} [CommRing R] {n : ℕ}
    {d : Fin n → ℕ} (α : ∀ i, Fin (d i) → R) (k : ∀ i, Fin (d i)) :
    MvPolynomial (Fin n) R →+* R :=
  MvPolynomial.eval₂Hom (RingHom.id R) (fun i => α i (k i))

/- `J_k = Φ_k(J)` is ideal image along the evaluation map. -/
/-- The image of an ideal under a selected-root evaluation map. -/
def splitImageIdeal {R : Type*} [CommRing R] {n : ℕ}
    (J : Ideal (MvPolynomial (Fin n) R)) {d : Fin n → ℕ}
    (α : ∀ i, Fin (d i) → R) (k : ∀ i, Fin (d i)) : Ideal R :=
  J.map (splitEvaluationHom α k)

/- The structure is a source-facing presentation, not a parallel polynomial
   ring: its polynomial ring and quotient are Mathlib's canonical ones. -/
/-- A quotient presentation whose defining one-variable relations split into
linear factors over the coefficient ring. -/
structure SplitPolynomialPresentation
    (R S : Type*) [CommRing R] [CommRing S] [Algebra R S] where
  number : ℕ
  degree : Fin number → ℕ
  polynomial : Fin number → Polynomial R
  root : ∀ i, Fin (degree i) → R
  factorization : ∀ i, polynomial i = splitPolynomial (root i)
  ideal : Ideal (MvPolynomial (Fin number) R)
  ideal_contains : ∀ i, Polynomial.toMvPolynomial i (polynomial i) ∈ ideal
  quotientEquiv :
    (MvPolynomial (Fin number) R ⧸ ideal) ≃ₐ[R] S

/-! ## Root factorization and finite splitting -/

/- The polynomial evaluation hypothesis is written with Mathlib's canonical
   `Polynomial.eval`; the factor is `X - C α`. -/
/-- A root of a monic polynomial gives a monic linear factor. -/
theorem have_one_root
    {R : Type*} [CommRing R] (P : Polynomial R) (hP : P.Monic)
    (α : R) (hα : P.eval α = 0) :
    ∃ Q : Polynomial R, Q.Monic ∧
      P = (Polynomial.X - Polynomial.C α) * Q := by
  have hdiv : Polynomial.X - Polynomial.C α ∣ P :=
    Polynomial.dvd_iff_isRoot.mpr hα
  rcases hdiv with ⟨Q, hQ⟩
  refine ⟨Q, ?_, hQ⟩
  apply (Polynomial.monic_X_sub_C α).of_mul_monic_left
  rw [← hQ]
  exact hP

/- The ring map and its finite/free module structure are exposed explicitly;
   no injectivity is asserted here, matching the source's `R → R'`. -/
/-- A monic polynomial acquires a root after a finite free ring extension. -/
theorem adjoin_one_root
    {R : Type u} [CommRing R] (P : Polynomial R) (hP : P.Monic) :
    ∃ (R' : Type u) (_ : CommRing R') (f : R →+* R'),
      letI : Algebra R R' := f.toAlgebra
      Module.Finite R R' ∧ Module.Free R R' ∧
      ∃ (α : R') (Q : Polynomial R'), Q.Monic ∧
        Polynomial.map f P = (Polynomial.X - Polynomial.C α) * Q := by
  refine ⟨AdjoinRoot P, inferInstance, AdjoinRoot.of P, ?_⟩
  letI : Algebra R (AdjoinRoot P) := AdjoinRoot.instAlgebra (S := R) P
  have halg : (AdjoinRoot.of P).toAlgebra = (inferInstance : Algebra R (AdjoinRoot P)) := by
    rw [← AdjoinRoot.algebraMap_eq]
    exact toAlgebra_algebraMap
  refine ⟨halg.symm ▸ hP.finite_adjoinRoot, halg.symm ▸ hP.free_adjoinRoot, ?_⟩
  have hα : (Polynomial.map (AdjoinRoot.of P) P).eval (AdjoinRoot.root P) = 0 := by
    rw [Polynomial.eval_map]
    exact AdjoinRoot.eval₂_root P
  obtain ⟨Q, hQ, hfactor⟩ := have_one_root (Polynomial.map (AdjoinRoot.of P) P)
    (hP.map _) (AdjoinRoot.root P) hα
  exact ⟨AdjoinRoot.root P, Q, hQ, hfactor⟩

/- The finite extension in the source is represented by an injective ring map
   together with finite/free module structures.  The target tensor product
   uses its canonical right-algebra structure over the new coefficient ring. -/
/-- A finite ring map becomes a split polynomial quotient after a finite free
injective base extension. -/
theorem finite_split
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : RingHom.Finite f) :
    letI : Algebra R S := f.toAlgebra
    ∃ (R' : Type u) (_ : CommRing R') (g : R →+* R'),
      letI : Algebra R R' := g.toAlgebra
      Function.Injective g ∧ Module.Finite R R' ∧ Module.Free R R' ∧
        letI : Algebra R' (S ⊗[R] R') := Algebra.TensorProduct.rightAlgebra
        Nonempty (SplitPolynomialPresentation R' (S ⊗[R] R')) := by
  letI : Algebra R S := f.toAlgebra
  classical
  rcases subsingleton_or_nontrivial R with hR | hR
  · letI : Subsingleton R := hR
    have hS : Subsingleton S := by
      have h01 : (0 : S) = 1 := by
        calc
          (0 : S) = f 0 := (f.map_zero).symm
          _ = f 1 := congrArg f (Subsingleton.elim 0 1)
          _ = 1 := f.map_one
      exact ⟨fun x y => by
        calc
          x = x * 1 := (mul_one x).symm
          _ = x * 0 := by rw [h01]
          _ = 0 := mul_zero x
          _ = y * 0 := (mul_zero y).symm
          _ = y * 1 := by rw [h01]
          _ = y := mul_one y⟩
    letI : Subsingleton S := hS
    let T := S ⊗[R] R
    letI : Algebra R R := (RingHom.id R).toAlgebra
    letI : Algebra R T := Algebra.TensorProduct.rightAlgebra
    have hT : Subsingleton T := by
      refine ⟨?_⟩
      intro x y
      induction x using TensorProduct.induction_on with
      | zero => exact Subsingleton.elim _ _
      | add x y hx hy => exact Subsingleton.elim _ _
      | tmul x y => exact Subsingleton.elim _ _
    letI : Subsingleton T := hT
    have hφ : Function.Surjective
        (MvPolynomial.aeval (R := R) (fun i : Fin 0 => (0 : T))) := by
      intro x
      exact ⟨0, Subsingleton.elim _ _⟩
    let φ : MvPolynomial (Fin 0) R →ₐ[R] T :=
      MvPolynomial.aeval (R := R) (fun i : Fin 0 => (0 : T))
    have hker : RingHom.ker φ.toRingHom = (⊤ : Ideal (MvPolynomial (Fin 0) R)) := by
      apply top_unique
      intro p hp
      rw [RingHom.mem_ker]
      exact Subsingleton.elim _ _
    have he : (MvPolynomial (Fin 0) R ⧸ (⊤ : Ideal (MvPolynomial (Fin 0) R))) ≃ₐ[R] T := by
      rw [← hker]
      exact Ideal.quotientKerAlgEquivOfSurjective hφ
    refine ⟨R, inferInstance, RingHom.id R, ?_⟩
    letI : Algebra R R := (RingHom.id R).toAlgebra
    refine ⟨Function.bijective_id.injective, inferInstance, inferInstance, ?_⟩
    exact ⟨{
      number := 0
      degree := Fin.elim0
      polynomial := Fin.elim0
      root := fun i => Fin.elim0 i
      factorization := fun i => Fin.elim0 i
      ideal := ⊤
      ideal_contains := fun i => Fin.elim0 i
      quotientEquiv := he }⟩
  · letI : Nontrivial R := hR
    letI : Module.Finite R S := hf
    obtain ⟨n, ⟨P⟩⟩ := (Algebra.FiniteType.iff_exists_generators.mp
      (RingHom.Finite.finiteType hf))
    choose q hq using fun i => IsIntegral.of_finite R (P.val i)
    let p : Polynomial R := ∏ i, q i
    have hp : p.Monic := by
      dsimp [p]
      exact Polynomial.monic_prod_of_monic Finset.univ q (fun i _ => (hq i).1)
    have hroot : ∀ i, Polynomial.eval₂ (algebraMap R S) (P.val i) p = 0 := by
      intro i
      dsimp [p]
      change (Polynomial.eval₂RingHom (algebraMap R S) (P.val i)) (∏ j, q j) = 0
      rw [map_prod]
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      exact (hq i).2
    obtain ⟨R', _, alg, hfinite, hfree, hnontrivial, hsplit⟩ := hp.exists_splits_map
    letI : CommRing R' := ‹CommRing R'›
    letI : Algebra R R' := alg
    letI : Module.Finite R R' := hfinite
    letI : Module.Free R R' := hfree
    letI : Nontrivial R' := hnontrivial
    have hinj : Function.Injective (algebraMap R R') :=
      FaithfulSMul.algebraMap_injective R R'
    obtain ⟨m, hm⟩ := Polynomial.splits_iff_exists_multiset.mp hsplit
    let d := m.toList.length
    let roots : Fin d → R' := fun j => m.toList[j.1]
    have hfactor : Polynomial.map (algebraMap R R') p =
        splitPolynomial roots := by
      rw [hm]
      dsimp [splitPolynomial, roots, d]
      rw [(hp.map (algebraMap R R')).leadingCoeff]
      simp only [map_one, Polynomial.C_1, one_mul]
      simpa using (Fin.prod_univ_fun_getElem m.toList
        (fun x => Polynomial.X - Polynomial.C x)).symm
    let T := S ⊗[R] R'
    letI : Algebra R' T := Algebra.TensorProduct.rightAlgebra
    let iota : S →ₐ[R] T :=
      Algebra.TensorProduct.includeLeft (R := R) (S := R) (A := S) (B := R')
    let val : Fin n → T := fun i => iota (P.val i)
    have hbase : iota.toRingHom.comp (algebraMap R S) =
        (algebraMap R' T).comp (algebraMap R R') := by
      rw [show iota.toRingHom = Algebra.TensorProduct.includeLeftRingHom
        (R := R) (A := S) (B := R') from rfl]
      rw [Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap]
      rfl
    have hsurj : Function.Surjective (MvPolynomial.aeval (R := R') val) := by
      intro x
      induction x using TensorProduct.induction_on with
      | zero => exact ⟨0, map_zero _⟩
      | add x y hx hy =>
          obtain ⟨x, rfl⟩ := hx
          obtain ⟨y, rfl⟩ := hy
          exact ⟨x + y, map_add _ _ _⟩
      | tmul x y =>
          obtain ⟨q, hq'⟩ := P.aeval_val_surjective x
          refine ⟨q.map (algebraMap R R') * MvPolynomial.C y, ?_⟩
          have hqeval : MvPolynomial.eval₂ ((algebraMap R' T).comp (algebraMap R R'))
              val q = iota x := by
            calc
              MvPolynomial.eval₂ ((algebraMap R' T).comp (algebraMap R R')) val q =
                  MvPolynomial.eval₂ (iota.toRingHom.comp (algebraMap R S)) val q := by
                    rw [hbase]
              _ = iota (MvPolynomial.eval₂ (algebraMap R S) P.val q) := by
                symm
                simpa [val] using
                  (MvPolynomial.hom_eval₂ q (algebraMap R S) iota.toRingHom P.val)
              _ = iota x := by simpa [MvPolynomial.aeval_def] using congrArg iota hq'
          rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_map]
          rw [hqeval]
          simp only [MvPolynomial.eval₂_C]
          change (x ⊗ₜ[R] (1 : R')) * ((1 : S) ⊗ₜ[R] y) = x ⊗ₜ[R] y
          simp
    let ψ : MvPolynomial (Fin n) R' →ₐ[R'] T := MvPolynomial.aeval val
    have hcontains : ∀ i, Polynomial.toMvPolynomial i (Polynomial.map (algebraMap R R') p) ∈
        RingHom.ker ψ.toRingHom := by
      intro i
      rw [RingHom.mem_ker]
      change MvPolynomial.aeval val
        (Polynomial.toMvPolynomial i (Polynomial.map (algebraMap R R') p)) = 0
      rw [MvPolynomial.aeval_toMvPolynomial, Polynomial.aeval_def, Polynomial.eval₂_map]
      calc
        Polynomial.eval₂ ((algebraMap R' T).comp (algebraMap R R')) (val i)
              (p) = Polynomial.eval₂ (iota.toRingHom.comp (algebraMap R S)) (val i) p := by
                rw [hbase]
        _ = iota (Polynomial.eval₂ (algebraMap R S) (P.val i) p) := by
          symm
          simpa [val] using
            (Polynomial.hom_eval₂ (algebraMap R S) iota.toRingHom p (P.val i))
        _ = 0 := by simpa using congrArg iota (hroot i)
    let e : (MvPolynomial (Fin n) R' ⧸ RingHom.ker ψ.toRingHom) ≃ₐ[R'] T :=
      Ideal.quotientKerAlgEquivOfSurjective hsurj
    have hpres : Nonempty (SplitPolynomialPresentation R' T) := ⟨{
      number := n
      degree := fun _ => d
      polynomial := fun _ => Polynomial.map (algebraMap R R') p
      root := fun _ => roots
      factorization := fun _ => hfactor
      ideal := RingHom.ker ψ.toRingHom
      ideal_contains := hcontains
      quotientEquiv := e }⟩
    have hAlg : alg.algebraMap.toAlgebra = alg := toAlgebra_algebraMap
    refine ⟨R', inferInstance, alg.algebraMap, hinj, hAlg.symm ▸ hfinite,
      hAlg.symm ▸ hfree, ?_⟩
    exact hAlg.symm ▸ hpres

/-! ## The split-image lemma -/

/- The source's index condition `1 ≤ k_i ≤ d_i` is represented by the
   canonical finite type `Fin (degree i)`.  The quotient equivalence in the
   presentation identifies its structure map with the source's `R → S`. -/
/-- The image of the spectrum of a split polynomial quotient is the union of
the vanishing loci of the selected-root ideal images. -/
private theorem mvPolynomial_sub_eval_mem_span
    {R σ : Type*} [CommRing R] (p : MvPolynomial σ R) (a : σ → R) :
    p - MvPolynomial.C (MvPolynomial.eval₂Hom (RingHom.id R) a p) ∈
      Ideal.span (Set.range (fun i => MvPolynomial.X i - MvPolynomial.C (a i))) := by
  induction p using MvPolynomial.induction_on with
  | C r => simp
  | add p q hp hq =>
      simpa [map_add, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
        add_mem hp hq
  | mul_X p i hp =>
      have hxi := Ideal.subset_span (show MvPolynomial.X i - MvPolynomial.C (a i) ∈
        Set.range (fun i => MvPolynomial.X i - MvPolynomial.C (a i)) from ⟨i, rfl⟩)
      have hmul := (Ideal.span (Set.range (fun i =>
        MvPolynomial.X i - MvPolynomial.C (a i)))).mul_mem_left
          (MvPolynomial.C (MvPolynomial.eval₂Hom (RingHom.id R) a p)) hxi
      have hright := (Ideal.span (Set.range (fun i =>
        MvPolynomial.X i - MvPolynomial.C (a i)))).mul_mem_right
          (MvPolynomial.X i) hp
      convert add_mem hright hmul using 1
      simp only [MvPolynomial.eval₂Hom_X', map_mul]
      ring

private theorem exists_iInf_le_of_isPrime
    {R ι : Type*} [CommRing R] [Fintype ι]
    (P : Ideal R) (hP : P.IsPrime) (I : ι → Ideal R)
    (h : ⨅ i, I i ≤ P) : ∃ i, I i ≤ P := by
  classical
  rw [← Finset.inf_univ_eq_iInf] at h
  obtain ⟨i, hi, hIP⟩ := hP.inf_le'.mp h
  exact ⟨i, hIP⟩

private theorem toMvPolynomial_splitPolynomial
    {R : Type*} [CommRing R] {σ : Type*} (i : σ) {d : ℕ} (a : Fin d → R) :
    Polynomial.toMvPolynomial i (splitPolynomial a) =
      ∏ j, (MvPolynomial.X i - MvPolynomial.C (a j)) := by
  simp [splitPolynomial, map_prod]

theorem split_image
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (presentation : SplitPolynomialPresentation R S) :
    Set.range (PrimeSpectrum.comap (algebraMap R S)) =
      PrimeSpectrum.zeroLocus
        ((⨅ k : ∀ i, Fin (presentation.degree i),
          splitImageIdeal presentation.ideal presentation.root k : Ideal R) : Set R) := by
  ext p
  constructor
  · rintro ⟨q, rfl⟩
    let e := presentation.quotientEquiv
    let q' : PrimeSpectrum (MvPolynomial (Fin presentation.number) R ⧸
        presentation.ideal) := PrimeSpectrum.comap e.toRingHom q
    let q'' : PrimeSpectrum (MvPolynomial (Fin presentation.number) R) :=
      PrimeSpectrum.comap (Ideal.Quotient.mk presentation.ideal) q'
    have hbase : e.toRingHom.comp
        (algebraMap R (MvPolynomial (Fin presentation.number) R ⧸ presentation.ideal)) =
        algebraMap R S := by
      ext r
      exact e.commutes r
    have hpoint : PrimeSpectrum.comap (algebraMap R S) q =
        PrimeSpectrum.comap (algebraMap R
          (MvPolynomial (Fin presentation.number) R ⧸ presentation.ideal)) q' := by
      apply PrimeSpectrum.ext
      change Ideal.comap (algebraMap R S) q.asIdeal =
        Ideal.comap (algebraMap R (MvPolynomial (Fin presentation.number) R ⧸
          presentation.ideal)) q'.asIdeal
      change Ideal.comap (algebraMap R S) q.asIdeal =
        (Ideal.comap e.toRingHom q.asIdeal).comap
          (algebraMap R (MvPolynomial (Fin presentation.number) R ⧸ presentation.ideal))
      change Ideal.comap (algebraMap R S) q.asIdeal =
        Ideal.comap (e.toRingHom.comp
          (algebraMap R (MvPolynomial (Fin presentation.number) R ⧸ presentation.ideal)))
          q.asIdeal
      rw [hbase]
    have hq'' : presentation.ideal ≤ q''.asIdeal := by
      intro x hx
      change Ideal.Quotient.mk presentation.ideal x ∈ q'.asIdeal
      have hx0 : Ideal.Quotient.mk presentation.ideal x = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.mpr hx
      rw [hx0]
      exact q'.asIdeal.zero_mem
    have hfactor : ∀ i, (Finset.univ.prod (fun j : Fin (presentation.degree i) =>
        MvPolynomial.X i - MvPolynomial.C (presentation.root i j))) ∈ q''.asIdeal := by
      intro i
      rw [← toMvPolynomial_splitPolynomial]
      rw [← presentation.factorization i]
      exact hq'' (presentation.ideal_contains i)
    have hroot : ∀ i, ∃ j : Fin (presentation.degree i),
        MvPolynomial.X i - MvPolynomial.C (presentation.root i j) ∈ q''.asIdeal := by
      intro i
      obtain ⟨j, hj, hjq⟩ := Ideal.IsPrime.prod_mem_iff.mp (hfactor i)
      exact ⟨j, hjq⟩
    choose k hk using hroot
    rw [PrimeSpectrum.mem_zeroLocus]
    change (⨅ k : ∀ i, Fin (presentation.degree i),
      splitImageIdeal presentation.ideal presentation.root k) ≤
      (PrimeSpectrum.comap (algebraMap R S) q).asIdeal
    apply (iInf_le _ k).trans
    rw [splitImageIdeal, Ideal.map_le_iff_le_comap]
    intro a ha
    let φ := splitEvaluationHom presentation.root k
    have hspan : Ideal.span (Set.range (fun i : Fin presentation.number =>
        MvPolynomial.X i - MvPolynomial.C (presentation.root i (k i)))) ≤ q''.asIdeal := by
      refine Ideal.span_le.mpr ?_
      rintro _ ⟨i, rfl⟩
      exact hk i
    have hsub := mvPolynomial_sub_eval_mem_span a
      (fun i : Fin presentation.number => presentation.root i (k i))
    have hsub' : a - MvPolynomial.C (φ a) ∈ q''.asIdeal := by
      apply hspan
      simpa [φ, splitEvaluationHom, MvPolynomial.aeval_def] using hsub
    have hconst : MvPolynomial.C (φ a) ∈ q''.asIdeal := by
      have haQ : a ∈ q''.asIdeal := hq'' ha
      have := q''.asIdeal.sub_mem haQ hsub'
      convert this using 1
      all_goals ring
    have hconst' : Ideal.Quotient.mk presentation.ideal (MvPolynomial.C (φ a)) ∈ q'.asIdeal :=
      hconst
    change φ a ∈ (PrimeSpectrum.comap (algebraMap R S) q).asIdeal
    rw [congrArg PrimeSpectrum.asIdeal hpoint]
    change algebraMap R
        (MvPolynomial (Fin presentation.number) R ⧸ presentation.ideal) (φ a) ∈ q'.asIdeal
    change Ideal.Quotient.mk presentation.ideal (MvPolynomial.C (φ a)) ∈ q'.asIdeal
    exact hconst'
  · intro hp
    rw [PrimeSpectrum.mem_zeroLocus] at hp
    have hle : (⨅ k : ∀ i, Fin (presentation.degree i),
        splitImageIdeal presentation.ideal presentation.root k) ≤ p.asIdeal := hp
    obtain ⟨k, hk⟩ := exists_iInf_le_of_isPrime p.asIdeal p.isPrime _ hle
    let φ := splitEvaluationHom presentation.root k
    let ψ : MvPolynomial (Fin presentation.number) R →+*
        R ⧸ p.asIdeal := (Ideal.Quotient.mk p.asIdeal).comp φ
    have hker : ∀ a, a ∈ presentation.ideal → ψ a = 0 := by
      intro a ha
      have ha' : φ a ∈ p.asIdeal := by
        apply (Ideal.map_le_iff_le_comap.mp hk) ha
      exact Ideal.Quotient.eq_zero_iff_mem.mpr ha'
    let l : MvPolynomial (Fin presentation.number) R ⧸ presentation.ideal →+*
        R ⧸ p.asIdeal := Ideal.Quotient.lift presentation.ideal ψ hker
    let q' : PrimeSpectrum (MvPolynomial (Fin presentation.number) R ⧸ presentation.ideal) :=
      ⟨RingHom.ker l, RingHom.ker_isPrime l⟩
    let e := presentation.quotientEquiv
    let q : PrimeSpectrum S := PrimeSpectrum.comap e.symm.toRingHom q'
    have hbase : e.symm.toRingHom.comp (algebraMap R S) =
        algebraMap R (MvPolynomial (Fin presentation.number) R ⧸ presentation.ideal) := by
      ext r
      exact e.symm.commutes r
    have hp' : Ideal.comap
        (algebraMap R (MvPolynomial (Fin presentation.number) R ⧸ presentation.ideal))
        q'.asIdeal = p.asIdeal := by
      ext r
      change l (Ideal.Quotient.mk presentation.ideal (MvPolynomial.C r)) = 0 ↔
        r ∈ p.asIdeal
      simpa [l, ψ, φ, splitEvaluationHom, MvPolynomial.aeval_def] using
        (Ideal.Quotient.eq_zero_iff_mem (I := p.asIdeal) (a := r))
    refine ⟨q, ?_⟩
    apply PrimeSpectrum.ext
    change Ideal.comap (algebraMap R S) q.asIdeal = p.asIdeal
    change Ideal.comap (e.symm.toRingHom.comp (algebraMap R S)) q'.asIdeal = p.asIdeal
    rw [hbase, hp']

/-! ## Descent of flatness -/

/- This is Ferrand's finite Noetherian descent theorem.  The tensor product
   is written in Mathlib's standard base-change orientation `S ⊗[R] M`. -/
/-- Flatness descends along a finite injective map of Noetherian rings. -/
theorem descent_flatness_injective_finite_noetherian_rings
    {R S M : Type*} [CommRing R] [CommRing S]
    [AddCommGroup M] [Module R M] [IsNoetherianRing R] [IsNoetherianRing S]
    (f : R →+* S) (hf : RingHom.Finite f) (hinj : Function.Injective f)
    (hflat :
      letI : Algebra R S := f.toAlgebra
      Module.Flat S (S ⊗[R] M)) :
    Module.Flat R M := by
  sorry

/- The polynomial ring in the source is represented by the finite-variable
   `MvPolynomial`; its R-module structure on M is restriction of scalars. -/
/-- Flatness descends along an injective integral ring map for a module finitely
presented over a polynomial algebra. -/
theorem descent_flatness_injective_integral
    {R S M : Type*} [CommRing R] [CommRing S] [AddCommGroup M]
    (f : R →+* S) (hinj : Function.Injective f) (hIntegral : f.IsIntegral)
    (n : ℕ) [Module (MvPolynomial (Fin n) R) M]
    (hM : Module.FinitePresentation (MvPolynomial (Fin n) R) M)
    (hflat :
      letI : Module R M :=
        Module.compHom M (algebraMap R (MvPolynomial (Fin n) R))
      letI : Algebra R S := f.toAlgebra
      Module.Flat S (S ⊗[R] M)) :
    letI : Module R M :=
      Module.compHom M (algebraMap R (MvPolynomial (Fin n) R))
    Module.Flat R M := by
  sorry

/- The projective statement has the same finite Noetherian and injective
   hypotheses, with `Module.Projective` as Mathlib's canonical predicate. -/
/-- Projectivity descends along a finite injective map of Noetherian rings. -/
theorem descent_projective_injective_finite_noetherian_rings
    {R S P : Type*} [CommRing R] [CommRing S]
    [AddCommGroup P] [Module R P] [IsNoetherianRing R] [IsNoetherianRing S]
    (f : R →+* S) (hf : RingHom.Finite f) (hinj : Function.Injective f)
    (hprojective :
      letI : Algebra R S := f.toAlgebra
      Module.Projective S (S ⊗[R] P)) :
    Module.Projective R P := by
  sorry

end

end Formalization.Books.MoreAlgebra.Unit21
