import Formalization.Books.Algebra.Unit136.SyntomicMorphisms
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Smooth.Basic
import Mathlib.RingTheory.Smooth.Fiber
import Mathlib.RingTheory.Smooth.Locus
import Mathlib.RingTheory.Smooth.Pi
import Mathlib.RingTheory.Smooth.StandardSmooth
import Mathlib.RingTheory.Smooth.StandardSmoothCotangent
import Mathlib.RingTheory.Smooth.StandardSmoothOfFree

/-!
# Commutative Algebra, Chapter 137: Smooth ring maps

The canonical Mathlib classes `Algebra.Smooth` and
`Algebra.IsStandardSmooth` are used for the two notions in this chapter.
The source's presentation-independent cotangent complex is the one exposed
by Chapter 134, while the standard-smooth presentation and its Jacobian are
Mathlib's `SubmersivePresentation`.
-/

namespace Formalization.Books.Algebra.Unit137

open Set
open Module
open scoped BigOperators TensorProduct

noncomputable section

universe u v w

/-! ## The cotangent criterion for smoothness -/

/- The exact sequence in the hypersurface example is the specialization of
   `PresentationExtension.exact_cotangentComplex_toKaehler`; the displayed
   polynomial basis is already provided by `Presentation.cotangentSpaceBasis`.
   The source writes `S` for the first term, but the canonical term is the
   conormal module `I/I²` unless a regularity hypothesis on the equation is
   added.  We therefore record the presentation-level statement. -/
theorem presentation_exact_sequence
    {R S ι : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (P : Formalization.Books.Algebra.Unit134.Presentation R S ι) :
    Function.Exact P.toExtension.cotangentComplex P.toExtension.toKaehler := by
  exact P.toExtension.exact_cotangentComplex_toKaehler

theorem presentation_differential_formula
    {R S ι : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (P : Formalization.Books.Algebra.Unit134.Presentation R S ι)
    (x : P.toExtension.ker) :
    P.toExtension.cotangentComplex (Algebra.Extension.Cotangent.mk x) =
      1 ⊗ₜ[P.Ring] KaehlerDifferential.D R P.Ring x.1 := by
  exact P.toExtension.cotangentComplex_mk x

/- The source's rank-two computation and its failure of smoothness are kept as
   one warning theorem.  The free module is the canonical
   `ModuleOfDifferentials`; no parallel differential object is introduced. -/
abbrev Hypersurface (R : Type u) [CommRing R]
    (f : MvPolynomial (Fin 2) R) : Type u :=
  MvPolynomial (Fin 2) R ⧸
    Ideal.span ({f} : Set (MvPolynomial (Fin 2) R))

noncomputable def hypersurfacePartial
    {R : Type u} [CommRing R] {f : MvPolynomial (Fin 2) R}
    (i : Fin 2) : Hypersurface R f :=
  Ideal.Quotient.mk _ (MvPolynomial.pderiv i f)

noncomputable def hypersurfacePresentation
    {R : Type u} [CommRing R] (f : MvPolynomial (Fin 2) R) :
    Formalization.Books.Algebra.Unit134.Presentation R (Hypersurface R f) (Fin 2) :=
  Algebra.Generators.ofAlgHom
    (Ideal.Quotient.mkₐ R (Ideal.span ({f} : Set (MvPolynomial (Fin 2) R))))
    (Ideal.Quotient.mkₐ_surjective R (Ideal.span ({f} : Set (MvPolynomial (Fin 2) R))))

private theorem hypersurface_quotient_aeval_eq
    {R : Type u} [CommRing R] (f : MvPolynomial (Fin 2) R)
    (A : Algebra R (Hypersurface R f))
    (hA : A = Ideal.Quotient.algebra R) :
    letI : Algebra R (Hypersurface R f) := A
    (MvPolynomial.aeval (fun i =>
        Ideal.Quotient.mk (Ideal.span ({f} : Set (MvPolynomial (Fin 2) R)))
          (MvPolynomial.X i))).toRingHom =
      Ideal.Quotient.mk (Ideal.span ({f} : Set (MvPolynomial (Fin 2) R))) := by
  subst A
  have h := congrArg (fun z => z.toRingHom)
    (MvPolynomial.mkₐ_eq_aeval
      (Ideal.span ({f} : Set (MvPolynomial (Fin 2) R)))).symm
  exact h.trans (Ideal.Quotient.mkₐ_toRingHom R
    (Ideal.span ({f} : Set (MvPolynomial (Fin 2) R))))

theorem hypersurface_exact_sequence
    {R : Type u} [CommRing R] (f : MvPolynomial (Fin 2) R) :
    Function.Exact
        (hypersurfacePresentation (R := R) f).toExtension.cotangentComplex
        (hypersurfacePresentation (R := R) f).toExtension.toKaehler ∧
      Function.Surjective
        (hypersurfacePresentation (R := R) f).toExtension.toKaehler := by
  constructor
  · exact (hypersurfacePresentation (R := R) f).toExtension.exact_cotangentComplex_toKaehler
  · exact (hypersurfacePresentation (R := R) f).toExtension.toKaehler_surjective

/-- A source-facing formulation of a finite module being locally free of a
    fixed rank, using Mathlib's free locus and stalk rank. -/
def IsLocallyFreeOfRank
    (A M : Type*) [CommRing A] [AddCommGroup M] [Module A M] (n : ℕ) : Prop :=
  Module.freeLocus A M = Set.univ ∧
    ∀ q : PrimeSpectrum A, Module.rankAtStalk M q = n

theorem hypersurface_jacobian_smooth
    {R : Type u} [CommRing R] (f : MvPolynomial (Fin 2) R)
    (hjac : Ideal.span (Set.range (hypersurfacePartial (f := f))) =
      (⊤ : Ideal (Hypersurface R f))) :
    Algebra.Smooth R (Hypersurface R f) ∧
      IsLocallyFreeOfRank (Hypersurface R f)
        (Formalization.Books.Algebra.Unit131.ModuleOfDifferentials R
          (Hypersurface R f)) 1 := by
  let P := hypersurfacePresentation (R := R) f
  have hker : P.ker = Ideal.span ({f} : Set (MvPolynomial (Fin 2) R)) := by
    simp [P, hypersurfacePresentation, Algebra.Generators.ker_ofAlgHom]
  let rf : P.toExtension.ker := ⟨f, by
    change f ∈ P.ker
    rw [hker]
    exact Ideal.subset_span (by simp)⟩
  let m : P.toExtension.Cotangent := Algebra.Extension.Cotangent.mk rf
  have hdm_repr (i : Fin 2) :
      P.cotangentSpaceBasis.repr (P.toExtension.cotangentComplex m) i =
        hypersurfacePartial (f := f) i := by
    dsimp [m]
    have heval :
        MvPolynomial.aeval P.val =
          Ideal.Quotient.mkₐ R (Ideal.span ({f} : Set (MvPolynomial (Fin 2) R))) := by
      change MvPolynomial.aeval
          (fun d : Fin 2 =>
            Ideal.Quotient.mk (Ideal.span ({f} : Set (MvPolynomial (Fin 2) R)))
              (MvPolynomial.X d)) = _
      exact (MvPolynomial.mkₐ_eq_aeval
        (Ideal.span ({f} : Set (MvPolynomial (Fin 2) R)))).symm
    have hx := Algebra.Generators.cotangentSpaceBasis_repr_one_tmul P f i
    simpa [hypersurfacePartial, heval] using hx
  have h1 : (1 : Hypersurface R f) ∈
      Ideal.span (Set.range (hypersurfacePartial (f := f))) := by
    rw [hjac]
    simp
  obtain ⟨c, hc⟩ := (Ideal.mem_span_range_iff_exists_fun.mp h1)
  have hc' : c 0 * hypersurfacePartial (f := f) 0 +
      c 1 * hypersurfacePartial (f := f) 1 = 1 := by
    simpa [Fin.sum_univ_two] using hc
  let l : P.toExtension.CotangentSpace →ₗ[Hypersurface R f]
      P.toExtension.Cotangent :=
    P.cotangentSpaceBasis.constr (Hypersurface R f) (fun i => c i • m)
  have hlm : l (P.toExtension.cotangentComplex m) = m := by
    rw [← P.cotangentSpaceBasis.sum_repr (P.toExtension.cotangentComplex m)]
    have h := congrArg (fun z : Hypersurface R f => z • m) hc
    simp only [Fin.sum_univ_two] at h
    rw [add_smul] at h
    simpa [l, hdm_repr, Fin.sum_univ_two, smul_smul, mul_comm] using h
  have hl : l.comp P.toExtension.cotangentComplex = LinearMap.id := by
    ext x
    obtain ⟨y, rfl⟩ := Algebra.Extension.Cotangent.mk_surjective x
    have hy : y.1 ∈ P.ker := y.2
    have hyspan : y.1 ∈ Ideal.span ({f} : Set (MvPolynomial (Fin 2) R)) := by
      simpa only [hker] using hy
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp hyspan
    have hy' : y = a • rf := by
      apply Subtype.ext
      change (y : P.toExtension.Ring) = a * (rf : P.toExtension.Ring)
      exact ha.symm
    have hmk : Algebra.Extension.Cotangent.mk y =
        algebraMap P.toExtension.Ring (Hypersurface R f) a • m := by
      rw [hy']
      change Algebra.Extension.Cotangent.mk (a • rf) =
        algebraMap P.toExtension.Ring (Hypersurface R f) a •
          Algebra.Extension.Cotangent.mk rf
      rw [map_smul, ← algebraMap_smul (Hypersurface R f)]
    rw [hmk]
    change l (P.toExtension.cotangentComplex
      (algebraMap P.toExtension.Ring (Hypersurface R f) a • m)) =
      algebraMap P.toExtension.Ring (Hypersurface R f) a • m
    rw [map_smul, map_smul, hlm]
  let a : Fin 2 → Hypersurface R f := hypersurfacePartial (f := f)
  let q : P.toExtension.CotangentSpace →ₗ[Hypersurface R f]
      Hypersurface R f :=
    P.cotangentSpaceBasis.constr (Hypersurface R f)
      (fun i => Fin.cases (-a 1) (fun _ => a 0) i)
  have hq0 : q (P.cotangentSpaceBasis 0) = -a 1 := by
    simp only [q, Module.Basis.constr_basis, Fin.cases_zero]
  have hq1 : q (P.cotangentSpaceBasis 1) = a 0 := by
    simp only [q, Module.Basis.constr_basis]
    have h1 : (1 : Fin 2) = Fin.succ (0 : Fin 1) := by decide
    rw [h1, Fin.cases_succ]
  have hqv : q (P.toExtension.cotangentComplex m) = 0 := by
    rw [← P.cotangentSpaceBasis.sum_repr (P.toExtension.cotangentComplex m)]
    simp [q, a, hdm_repr, Fin.sum_univ_two]
    have h1 : (1 : Fin 2) = Fin.succ (0 : Fin 1) := by decide
    rw [h1, Fin.cases_succ]
    ring
  have hq_comp : q.comp P.toExtension.cotangentComplex = 0 := by
    ext z
    obtain ⟨w, rfl⟩ := Algebra.Extension.Cotangent.mk_surjective z
    have hw : w.1 ∈ P.ker := w.2
    have hwspan : w.1 ∈ Ideal.span ({f} : Set (MvPolynomial (Fin 2) R)) := by
      simpa only [hker] using hw
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.mp hwspan
    have hwb : w = b • rf := by
      apply Subtype.ext
      change (w : P.toExtension.Ring) = b * (rf : P.toExtension.Ring)
      exact hb.symm
    rw [hwb]
    rw [LinearMap.comp_apply]
    change q (P.toExtension.cotangentComplex
      (Algebra.Extension.Cotangent.mk (b • rf))) = 0
    have hmk : Algebra.Extension.Cotangent.mk (b • rf) =
        algebraMap P.toExtension.Ring (Hypersurface R f) b • m := by
      change Algebra.Extension.Cotangent.mk (b • rf) =
        algebraMap P.toExtension.Ring (Hypersurface R f) b •
          Algebra.Extension.Cotangent.mk rf
      rw [map_smul, ← algebraMap_smul (Hypersurface R f)]
    rw [hmk]
    rw [P.toExtension.cotangentComplex.map_smul, q.map_smul, hqv, smul_zero]
  have hq_surj : Function.Surjective q := by
    intro b
    refine ⟨b • ((-c 1) • P.cotangentSpaceBasis 0 +
      (c 0) • P.cotangentSpaceBasis 1), ?_⟩
    simp [q, a, Fin.sum_univ_two]
    have h1 : (1 : Fin 2) = Fin.succ (0 : Fin 1) := by decide
    rw [h1, Fin.cases_succ]
    have hc'' : c 0 * hypersurfacePartial (f := f) 0 +
        c (Fin.succ (0 : Fin 1)) *
          hypersurfacePartial (f := f) (Fin.succ (0 : Fin 1)) = 1 := by
      simpa [Fin.sum_univ_two] using hc
    linear_combination b * hc''
  have hkerq : LinearMap.ker q = LinearMap.range P.toExtension.cotangentComplex := by
    apply le_antisymm
    · intro x hx
      have hqx :
          -(a 1) * (P.cotangentSpaceBasis.repr x 0) +
              (a 0) * (P.cotangentSpaceBasis.repr x 1) = 0 := by
        rw [LinearMap.mem_ker] at hx
        rw [← P.cotangentSpaceBasis.sum_repr x, Fin.sum_univ_two,
          map_add, map_smul, map_smul, hq0, hq1] at hx
        linear_combination hx
      let t := c 0 * P.cotangentSpaceBasis.repr x 0 +
        c 1 * P.cotangentSpaceBasis.repr x 1
      have hxt : x = t • P.toExtension.cotangentComplex m := by
        apply P.cotangentSpaceBasis.repr.injective
        ext i
        fin_cases i
        · simp [t, hdm_repr, a]
          linear_combination
            -(P.cotangentSpaceBasis.repr x 0) * hc' -
              (c 1) * hqx
        · simp [t, hdm_repr, a]
          linear_combination
            -(P.cotangentSpaceBasis.repr x 1) * hc' +
              (c 0) * hqx
      refine ⟨t • m, ?_⟩
      rw [map_smul]
      exact hxt.symm
    · rintro x ⟨y, rfl⟩
      rw [LinearMap.mem_ker]
      rw [← LinearMap.comp_apply, hq_comp]
      rfl
  let eQ :
      (P.toExtension.CotangentSpace ⧸
          LinearMap.range P.toExtension.cotangentComplex) ≃ₗ[Hypersurface R f]
        Hypersurface R f :=
    (Submodule.quotEquivOfEq (R := Hypersurface R f)
      (M := P.toExtension.CotangentSpace) _ _ hkerq.symm).trans
      (q.quotKerEquivOfSurjective hq_surj)
  obtain ⟨eP⟩ :=
    Formalization.Books.Algebra.Unit134.presentation_cokernel_equiv_differentials P
  let eΩ :
      Formalization.Books.Algebra.Unit131.ModuleOfDifferentials R
          (Hypersurface R f) ≃ₗ[Hypersurface R f]
        Hypersurface R f := eP.symm.trans eQ
  have hsmooth : Algebra.Smooth R (Hypersurface R f) :=
    by
      let _ : Algebra.FormallySmooth R P.toExtension.Ring :=
        Algebra.instFormallySmoothMvPolynomial (σ := Fin 2)
      let hformal : Algebra.FormallySmooth R (Hypersurface R f) :=
        (Algebra.Extension.formallySmooth_iff_split_injection
          P.toExtension).mpr ⟨l, hl⟩
      exact { formallySmooth := hformal, finitePresentation :=
        Algebra.FinitePresentation.quotient (Submodule.fg_span_singleton f) }
  letI : Algebra.Smooth R (Hypersurface R f) := hsmooth
  have hfree :
      Module.freeLocus (Hypersurface R f)
          (Formalization.Books.Algebra.Unit131.ModuleOfDifferentials R
            (Hypersurface R f)) = Set.univ := by
    exact Module.freeLocus_eq_univ_iff.mpr inferInstance
  have hrank : ∀ q : PrimeSpectrum (Hypersurface R f),
      Module.rankAtStalk
          (Formalization.Books.Algebra.Unit131.ModuleOfDifferentials R
            (Hypersurface R f)) q = 1 := by
    intro q
    by_cases hnt : Nontrivial (Hypersurface R f)
    · letI : Nontrivial (Hypersurface R f) := hnt
      rw [Module.rankAtStalk_eq_of_equiv eΩ, Module.rankAtStalk_self]
      rfl
    · haveI : Subsingleton (Hypersurface R f) := not_nontrivial_iff_subsingleton.mp hnt
      exfalso
      apply q.2.ne_top
      exact Subsingleton.elim _ _
  exact ⟨hsmooth, hfree, hrank⟩

/- The inseparable specialization uses the same hypersurface presentation. -/
abbrev InseparableHypersurface (R : Type u) [CommRing R] (p : ℕ) : Type u :=
  Hypersurface R (MvPolynomial.X (0 : Fin 2) ^ p +
    MvPolynomial.X (1 : Fin 2) ^ p)

theorem inseparable_hypersurface_warning
    {R : Type u} [CommRing R] [Nontrivial R]
    (p : ℕ) (hp : Nat.Prime p) [CharP R p] :
    IsLocallyFreeOfRank (InseparableHypersurface R p)
        (Formalization.Books.Algebra.Unit131.ModuleOfDifferentials R
          (InseparableHypersurface R p)) 2 ∧
      Formalization.Books.Algebra.Unit136.IsRelativeGlobalCompleteIntersection
        (algebraMap R (InseparableHypersurface R p)) ∧
      ¬ Algebra.Smooth R (InseparableHypersurface R p) := by
  letI : Fact p.Prime := ⟨hp⟩
  let g : MvPolynomial (Fin 2) R :=
    MvPolynomial.X (0 : Fin 2) ^ p + MvPolynomial.X (1 : Fin 2) ^ p
  have hpderiv (i : Fin 2) : MvPolynomial.pderiv i g = 0 := by
    dsimp [g]
    rw [map_add, MvPolynomial.pderiv_pow, MvPolynomial.pderiv_pow]
    simp [CharP.cast_eq_zero R p]
  let P : Formalization.Books.Algebra.Unit134.Presentation R
      (InseparableHypersurface R p) (Fin 2) :=
    hypersurfacePresentation (R := R)
    (MvPolynomial.X (0 : Fin 2) ^ p + MvPolynomial.X (1 : Fin 2) ^ p)
  have hker : P.ker = Ideal.span ({g} : Set (MvPolynomial (Fin 2) R)) := by
    simp [P, hypersurfacePresentation, Algebra.Generators.ker_ofAlgHom, g]
  let rf : P.toExtension.ker := ⟨g, by
    change g ∈ P.ker
    rw [hker]
    exact Ideal.subset_span (by simp)⟩
  let m : P.toExtension.Cotangent := Algebra.Extension.Cotangent.mk rf
  have hdmzero : P.toExtension.cotangentComplex m = 0 := by
    apply P.cotangentSpaceBasis.repr.injective
    ext i
    dsimp [m]
    have hx := Algebra.Generators.cotangentSpaceBasis_repr_one_tmul P g i
    simpa [rf, hpderiv] using hx
  have hdzero : P.toExtension.cotangentComplex = 0 := by
    ext x
    obtain ⟨y, rfl⟩ := Algebra.Extension.Cotangent.mk_surjective x
    have hy : y.1 ∈ P.ker := y.2
    have hyspan : y.1 ∈ Ideal.span ({g} : Set (MvPolynomial (Fin 2) R)) := by
      simpa only [hker] using hy
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp hyspan
    have hy' : y = a • rf := by
      apply Subtype.ext
      change (y : P.toExtension.Ring) = a * (rf : P.toExtension.Ring)
      exact ha.symm
    rw [hy']
    change P.toExtension.cotangentComplex
      (Algebra.Extension.Cotangent.mk (a • rf)) = 0
    rw [map_smul]
    rw [← algebraMap_smul (Hypersurface R g), map_smul, hdmzero, smul_zero]
  have hto_inj : Function.Injective P.toExtension.toKaehler := by
    intro x y hxy
    have hzero : P.toExtension.toKaehler (x - y) = 0 := by
      rw [map_sub, hxy, sub_self]
    obtain ⟨z, hz⟩ :=
      (P.toExtension.exact_cotangentComplex_toKaehler _).mp hzero
    apply sub_eq_zero.mp
    rw [← hz, hdzero]
    rfl
  let eΩ :
      Formalization.Books.Algebra.Unit131.ModuleOfDifferentials R
          (Hypersurface R g) ≃ₗ[Hypersurface R g]
        P.toExtension.CotangentSpace :=
    (LinearEquiv.ofBijective P.toExtension.toKaehler
      ⟨hto_inj, P.toExtension.toKaehler_surjective⟩).symm
  letI : Module.Projective (Hypersurface R g) P.toExtension.CotangentSpace :=
    Module.Projective.of_basis P.cotangentSpaceBasis
  letI : Module.Projective (Hypersurface R g)
      (Formalization.Books.Algebra.Unit131.ModuleOfDifferentials R
        (Hypersurface R g)) := Module.Projective.of_equiv' eΩ.symm
  letI : Module.FinitePresentation (Hypersurface R g)
      (Formalization.Books.Algebra.Unit131.ModuleOfDifferentials R
        (Hypersurface R g)) :=
    Module.finitePresentation_of_projective (Hypersurface R g) _
  have hfree :
      Module.freeLocus (Hypersurface R g)
          (Formalization.Books.Algebra.Unit131.ModuleOfDifferentials R
            (Hypersurface R g)) = Set.univ := by
    exact Module.freeLocus_eq_univ_iff.mpr inferInstance
  have hrank : ∀ q : PrimeSpectrum (Hypersurface R g),
      Module.rankAtStalk
          (Formalization.Books.Algebra.Unit131.ModuleOfDifferentials R
            (Hypersurface R g)) q = 2 := by
    intro q
    by_cases hnt : Nontrivial (Hypersurface R g)
    · letI : Nontrivial (Hypersurface R g) := hnt
      rw [Module.rankAtStalk_eq_of_equiv eΩ,
        Module.rankAtStalk_eq_finrank_of_free,
        Module.finrank_eq_card_basis P.cotangentSpaceBasis]
      simp
    · haveI : Subsingleton (Hypersurface R g) := not_nontrivial_iff_subsingleton.mp hnt
      exfalso
      apply q.2.ne_top
      exact Subsingleton.elim _ _
  have hg0 : g ≠ 0 := by
    intro hg
    have hc := congrArg
      (fun h : MvPolynomial (Fin 2) R =>
        MvPolynomial.coeff (Finsupp.single (0 : Fin 2) p) h) hg
    have hne : Finsupp.single (1 : Fin 2) p ≠
        Finsupp.single (0 : Fin 2) p := by
      intro h
      have h' := congrArg (fun z => z (1 : Fin 2)) h
      simpa [Finsupp.single_apply, hp.ne_zero] using h'
    have hc' : (1 : R) = 0 := by
      simpa [g, hp.ne_zero, MvPolynomial.coeff_X_pow, hne] using hc
    exact one_ne_zero hc'
  let evalX : MvPolynomial (Fin 2) R →ₐ[R] Polynomial R :=
    MvPolynomial.aeval (fun i => Fin.cases Polynomial.X (fun _ => 0) i)
  have hevalg : evalX g = Polynomial.X ^ p := by
    simp [evalX, g, hp.ne_zero]
    have h1 : (1 : Fin 2) = Fin.succ (0 : Fin 1) := by decide
    rw [h1, Fin.cases_succ]
    simp [hp.ne_zero]
  have hnot : g ∉ P.ker ^ 2 := by
    intro h
    have h' : g ∈ Ideal.span ({g ^ 2} : Set (MvPolynomial (Fin 2) R)) := by
      simpa [hker, Ideal.span_singleton_pow] using h
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.mp h'
    have hbe := congrArg evalX hb
    have hcancel : evalX b * Polynomial.X ^ p = 1 := by
      apply (Polynomial.isRegular_X_pow (R := R) p).1
      simpa [hevalg, map_mul, pow_two, mul_assoc, mul_comm, mul_left_comm] using hbe
    have hzero := congrArg (fun z : Polynomial R => z.eval 0) hcancel
    have hzero' : (0 : R) = 1 := by simpa [hp.ne_zero] using hzero
    exact zero_ne_one hzero'
  have hm0 : m ≠ 0 := by
    intro hm
    apply hnot
    apply (Algebra.Extension.Cotangent.mk_eq_zero_iff rf).mp
    simpa [m] using hm
  have hns : ¬ Algebra.Smooth R (Hypersurface R g) := by
    intro hs
    letI : Algebra.Smooth R (Hypersurface R g) := hs
    let _ : Algebra.FormallySmooth R P.toExtension.Ring :=
      Algebra.instFormallySmoothMvPolynomial (σ := Fin 2)
    obtain ⟨l, hl⟩ :=
      (Algebra.Extension.formallySmooth_iff_split_injection
        P.toExtension).mp hs.formallySmooth
    have hsub : ∀ x : P.toExtension.Cotangent, x = 0 := by
      intro x
      have hx := congrArg (fun q => q x) hl
      have hx' : (0 : P.toExtension.Cotangent) = x := by
        simpa only [LinearMap.comp_apply, hdzero, LinearMap.zero_apply,
          map_zero,
          LinearMap.id_apply] using hx
      exact hx'.symm
    exact hm0 (hsub m)
  refine ⟨⟨hfree, hrank⟩, ?_, hns⟩
  let alg : Algebra R (InseparableHypersurface R p) :=
    (algebraMap R (InseparableHypersurface R p)).toAlgebra
  letI : Algebra R (InseparableHypersurface R p) := alg
  have halg : alg = Ideal.Quotient.algebra R := by
    apply Algebra.algebra_ext
    intro r
    rfl
  let φ : MvPolynomial (Fin 2) R →ₐ[R] InseparableHypersurface R p :=
    MvPolynomial.aeval (fun i =>
      Ideal.Quotient.mk _ (MvPolynomial.X i))
  have hφ_eq : φ.toRingHom =
      Ideal.Quotient.mk
        (Ideal.span ({g} : Set (MvPolynomial (Fin 2) R))) := by
    simpa [φ] using hypersurface_quotient_aeval_eq g alg halg
  have hφ : Function.Surjective φ := by
    intro s
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective s
    refine ⟨a, ?_⟩
    exact congrArg (fun h => h a) hφ_eq
  let P' := @Algebra.Generators.ofAlgHom R
    (InseparableHypersurface R p) _ _ alg (Fin 2) φ hφ
  have hker' : P'.ker = Ideal.span ({g} : Set (MvPolynomial (Fin 2) R)) := by
    rw [Algebra.Generators.ker_ofAlgHom]
    change RingHom.ker φ.toRingHom = _
    rw [hφ_eq]
    simpa [g] using
      (Ideal.mk_ker (I := Ideal.span
        ({g} : Set (MvPolynomial (Fin 2) R))))
  let fs : Fin 1 → P'.Ring := fun _ => g
  refine ⟨2, 1, P', fs, ?_, ?_⟩
  · dsimp [Formalization.Books.Algebra.Unit136.IsPolynomialQuotientPresentation, fs]
    rw [hker']
    simp [Ideal.ofList]
  · intro q hq
    constructor
    · decide
    let K := q.asIdeal.ResidueField
    let T := MvPolynomial (Fin 2) R
    let I : Ideal T := Ideal.span ({g} : Set T)
    letI : Algebra R (T ⧸ I) := Ideal.Quotient.algebra R
    let e1 : K ⊗[R] (T ⧸ I) ≃ₐ[K]
        (K ⊗[R] T) ⧸ I.map
          (Algebra.TensorProduct.includeRight (A := K) (R := R)) :=
      Algebra.TensorProduct.tensorQuotientEquiv (R := R) K T K I
    let e2 : K ⊗[R] T ≃ₐ[K] MvPolynomial (Fin 2) K :=
      MvPolynomial.algebraTensorAlgEquiv R K
    let I1 : Ideal (K ⊗[R] T) :=
      I.map (Algebra.TensorProduct.includeRight (A := K) (R := R))
    let J : Ideal (MvPolynomial (Fin 2) K) :=
      I1.map (e2 : (K ⊗[R] T) →+* MvPolynomial (Fin 2) K)
    have hJ : J = I1.map (e2 : (K ⊗[R] T) →+* MvPolynomial (Fin 2) K) := by
      rfl
    have heFiber :
        @Unit136.Fiber R (InseparableHypersurface R p) _ _ alg q ≃ₐ[K]
          MvPolynomial (Fin 2) K ⧸ J := by
      rw [halg]
      exact e1.trans (Ideal.quotientEquivAlg I1 J e2 hJ)
    let r : MvPolynomial (Fin 2) K := e2 (1 ⊗ₜ[R] g)
    have hr_map : r = MvPolynomial.map (algebraMap R K) g := by
      change MvPolynomial.algebraTensorAlgEquiv R K (1 ⊗ₜ[R] g) = _
      rw [MvPolynomial.algebraTensorAlgEquiv_tmul]
      simp
    have hJspan : J = Ideal.span ({r} : Set (MvPolynomial (Fin 2) K)) := by
      simp [J, I1, I, r, Ideal.map_span]
    have hr0 : r ≠ 0 := by
      intro hr
      have hc := congrArg
        (fun h : MvPolynomial (Fin 2) K =>
          MvPolynomial.coeff (Finsupp.single (0 : Fin 2) p) h) hr
      have hne : Finsupp.single (1 : Fin 2) p ≠
          Finsupp.single (0 : Fin 2) p := by
        intro h
        have h' := congrArg (fun z => z (1 : Fin 2)) h
        simpa [Finsupp.single_apply, hp.ne_zero] using h'
      have hcoeff : MvPolynomial.coeff (Finsupp.single (0 : Fin 2) p) r = 1 := by
        rw [hr_map]
        simp [g, MvPolynomial.coeff_X_pow, hp.ne_zero, hne]
      rw [hcoeff] at hc
      have hc' : (1 : K) = 0 := by simpa using hc
      exact one_ne_zero hc'
    have hrreg : r ∈ nonZeroDivisors (MvPolynomial (Fin 2) K) :=
      mem_nonZeroDivisors_of_ne_zero hr0
    have hdimPoly : ringKrullDim (MvPolynomial (Fin 2) K) = 2 := by
      rw [MvPolynomial.ringKrullDim_of_isNoetherianRing,
        ringKrullDim_eq_zero_of_field]
      simp
    have hupper :
        ringKrullDim (MvPolynomial (Fin 2) K ⧸ J) + 1 ≤
          ringKrullDim (MvPolynomial (Fin 2) K) := by
      rw [hJspan]
      exact ringKrullDim_quotient_succ_le_of_nonZeroDivisor hrreg
    have hupper' : ringKrullDim (MvPolynomial (Fin 2) K ⧸ J) ≤ 1 := by
      apply (ENat.WithBot.add_le_add_one_right_iff).mp
      norm_num [hdimPoly] at hupper ⊢
      exact hupper
    let evalY : MvPolynomial (Fin 2) K →ₐ[K] Polynomial K :=
      MvPolynomial.aeval (fun i =>
        Fin.cases Polynomial.X (fun _ => -Polynomial.X) i)
    letI : CharP K p := by
      obtain ⟨q', hq'⟩ := CharP.exists K
      have hd : q' ∣ p :=
        CharP.dvd_of_ringHom (algebraMap R K) p q'
      obtain rfl | rfl := (Nat.dvd_prime hp).mp hd
      · exact (CharP.char_ne_one K 1 rfl).elim
      · exact hq'
    have hevalY_r : evalY r = 0 := by
      rw [hr_map]
      simp [evalY, g, hp.ne_zero]
      have h1 : (1 : Fin 2) = Fin.succ (0 : Fin 1) := by decide
      rw [h1, Fin.cases_succ]
      rw [← add_pow_char]
      simp [hp.ne_zero]
    have hevalY_surj : Function.Surjective evalY := by
      have hcomp :
          evalY.comp (Polynomial.aeval (MvPolynomial.X (0 : Fin 2))) =
            AlgHom.id K (Polynomial K) := by
        apply AlgHom.ext
        intro z
        induction z using Polynomial.induction_on' with
        | add p q hp hq =>
            simpa [AlgHom.comp_apply, AlgHom.id_apply] using
              congrArg₂ (· + ·) hp hq
        | monomial n a =>
            simp [evalY, Fin.cases_succ]
            rw [← Polynomial.C_mul_X_pow_eq_monomial]
      intro z
      refine ⟨Polynomial.aeval (MvPolynomial.X (0 : Fin 2)) z, ?_⟩
      have hz := congrArg (fun h => h z) hcomp
      simpa using hz
    have hJzero : ∀ a : MvPolynomial (Fin 2) K, a ∈ J → evalY a = 0 := by
      intro a ha
      rw [hJspan] at ha
      rw [Ideal.mem_span_singleton'] at ha
      obtain ⟨b, rfl⟩ := ha
      simp [map_mul, hevalY_r]
    let hevalQ : MvPolynomial (Fin 2) K ⧸ J →ₐ[K] Polynomial K :=
      Ideal.Quotient.liftₐ J evalY hJzero
    have hevalQ_surj : Function.Surjective hevalQ := by
      intro z
      obtain ⟨a, ha⟩ := hevalY_surj z
      refine ⟨Ideal.Quotient.mk J a, ?_⟩
      change evalY a = z
      exact ha
    have hlower : 1 ≤ ringKrullDim (MvPolynomial (Fin 2) K ⧸ J) := by
      have hdimPoly1 : ringKrullDim (Polynomial K) = 1 := by
        rw [Polynomial.ringKrullDim_of_isNoetherianRing,
          ringKrullDim_eq_zero_of_field]
        simp
      have hsurr := ringKrullDim_le_of_surjective
        (hevalQ : (MvPolynomial (Fin 2) K ⧸ J) →+* Polynomial K) hevalQ_surj
      rw [hdimPoly1] at hsurr
      exact hsurr
    have hdimQ : ringKrullDim (MvPolynomial (Fin 2) K ⧸ J) = 1 :=
      le_antisymm hupper' hlower
    calc
      ringKrullDim (@Unit136.Fiber R (InseparableHypersurface R p) _ _ alg q) =
          ringKrullDim (MvPolynomial (Fin 2) K ⧸ J) :=
        ringKrullDim_eq_of_ringEquiv heFiber.toRingEquiv
      _ = 1 := hdimQ
      _ = (((2 - 1 : ℕ) : ℕ∞) : WithBot ℕ∞) := by norm_num

/- The textbook definition is exactly Mathlib's `Smooth` class: formal
   smoothness (projective Kähler differentials and vanishing H₁) together with
   finite presentation. -/
theorem smooth_iff_formallySmooth_and_finitePresentation
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] :
    Algebra.Smooth R S ↔
      Algebra.FormallySmooth R S ∧ Algebra.FinitePresentation R S := by
  constructor
  · intro h
    exact ⟨h.formallySmooth, h.finitePresentation⟩
  · rintro ⟨hformal, hfp⟩
    exact { formallySmooth := hformal, finitePresentation := hfp }

theorem smooth_presentation_iff_split_injection
    {R S ι : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (P : Formalization.Books.Algebra.Unit134.Presentation R S ι)
    [Algebra.FinitePresentation R S] :
    Algebra.Smooth R S ↔
      ∃ l : P.toExtension.CotangentSpace →ₗ[S] P.toExtension.Cotangent,
        l ∘ₗ P.toExtension.cotangentComplex = LinearMap.id := by
  constructor
  · intro h
    let _ : Algebra.FormallySmooth R P.toExtension.Ring :=
      Algebra.instFormallySmoothMvPolynomial ι
    exact (Algebra.Extension.formallySmooth_iff_split_injection
      P.toExtension).mp h.formallySmooth
  · intro h
    let _ : Algebra.FormallySmooth R P.toExtension.Ring :=
      Algebra.instFormallySmoothMvPolynomial ι
    let hformal : Algebra.FormallySmooth R S :=
      (Algebra.Extension.formallySmooth_iff_split_injection
        P.toExtension).mpr h
    exact { formallySmooth := hformal, finitePresentation := inferInstance }

/- The conormal/cokernel formulation is the source-facing strengthening of
   the split-injection criterion.  The quotient is Mathlib's module quotient,
   and the conormal is `PresentationConormal P`. -/
theorem smooth_presentation_conormal_cokernel
    {R S ι : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Finite ι]
    (P : Formalization.Books.Algebra.Unit134.Presentation R S ι)
    [Algebra.Smooth R S] :
    Function.Injective P.toExtension.cotangentComplex ∧
      Module.Finite S
        (P.toExtension.CotangentSpace ⧸
          LinearMap.range P.toExtension.cotangentComplex) ∧
      Module.Projective S
        (P.toExtension.CotangentSpace ⧸
          LinearMap.range P.toExtension.cotangentComplex) ∧
    Module.Finite S P.toExtension.Cotangent ∧
      Module.Projective S P.toExtension.Cotangent := by
  rcases (smooth_presentation_iff_split_injection P).mp inferInstance with ⟨l, hl⟩
  have hQ : Nonempty ((P.toExtension.CotangentSpace ⧸
      LinearMap.range P.toExtension.cotangentComplex) ≃ₗ[S]
      Formalization.Books.Algebra.Unit131.ModuleOfDifferentials R S) :=
    Formalization.Books.Algebra.Unit134.presentation_cokernel_equiv_differentials P
  rcases hQ with ⟨e⟩
  let _ : Module.Projective S
      (P.toExtension.CotangentSpace ⧸ LinearMap.range P.toExtension.cotangentComplex) :=
    Module.Projective.of_equiv' e.symm
  let _ : Module.Finite S P.toExtension.CotangentSpace :=
    Module.Finite.of_basis P.cotangentSpaceBasis
  have hQfinite : Module.Finite S (P.toExtension.CotangentSpace ⧸
      LinearMap.range P.toExtension.cotangentComplex) :=
    Module.Finite.of_surjective (Submodule.mkQ _) (Submodule.mkQ_surjective _)
  let _ : Module.Projective S P.toExtension.CotangentSpace :=
    Module.Projective.of_basis P.cotangentSpaceBasis
  have hCprojective : Module.Projective S P.toExtension.Cotangent :=
    Module.Projective.of_split P.toExtension.cotangentComplex l hl
  refine ⟨?_, hQfinite, inferInstance,
    Algebra.Extension.Cotangent.finite
      (Algebra.Generators.fg_ker_of_finitePresentation (R := R) (S := S) (α := ι) P),
    hCprojective⟩
  · intro x y hxy
    have : l (P.toExtension.cotangentComplex x) =
        l (P.toExtension.cotangentComplex y) := congrArg l hxy
    simpa only [← LinearMap.comp_apply, hl, LinearMap.id_apply] using this

theorem smooth_presentation_module_decomposition
    {R S ι : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Finite ι]
    (P : Formalization.Books.Algebra.Unit134.Presentation R S ι)
    [Algebra.Smooth R S] :
    Nonempty (P.toExtension.CotangentSpace ≃ₗ[S]
      P.toExtension.Cotangent ×
        Formalization.Books.Algebra.Unit131.ModuleOfDifferentials R S) := by
  rcases (smooth_presentation_iff_split_injection P).mp inferInstance with ⟨l, hl⟩
  let d := P.toExtension.cotangentComplex
  let f := P.toExtension.toKaehler
  have hdf : f.comp d = 0 := by
    apply LinearMap.ext
    intro x
    exact (P.toExtension.exact_cotangentComplex_toKaehler _).mpr ⟨x, rfl⟩
  have hld : l.comp d = LinearMap.id := by
    simpa [d] using hl
  have hfd (z : P.toExtension.Cotangent) : f (d z) = 0 := by
    have hz := congrArg (fun g => g z) hdf
    simpa only [LinearMap.comp_apply, LinearMap.zero_apply] using hz
  obtain ⟨s, hs⟩ := f.exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr P.toExtension.toKaehler_surjective)
  let s' := s - d.comp (l.comp s)
  have hs' : f.comp s' = LinearMap.id := by
    apply LinearMap.ext
    intro ω
    dsimp [s']
    rw [map_sub, hfd, sub_zero]
    simpa only [LinearMap.comp_apply, LinearMap.id_apply] using
      congrArg (fun g => g ω) hs
  have hls' : l.comp s' = 0 := by
    apply LinearMap.ext
    intro ω
    dsimp [s']
    rw [map_sub]
    have hldx : l (d (l (s ω))) = l (s ω) := by
      have h := congrArg (fun g => g (l (s ω))) hld
      simpa only [LinearMap.comp_apply, LinearMap.id_apply] using h
    rw [hldx]
    rw [sub_self]
  let e : P.toExtension.CotangentSpace →ₗ[S]
      P.toExtension.Cotangent × Formalization.Books.Algebra.Unit131.ModuleOfDifferentials R S :=
    l.prod f
  let k : (P.toExtension.Cotangent ×
      Formalization.Books.Algebra.Unit131.ModuleOfDifferentials R S) →ₗ[S]
      P.toExtension.CotangentSpace :=
    d.coprod s'
  refine ⟨LinearEquiv.ofBijective e ⟨?_, ?_⟩⟩
  · intro x y hxy
    have hzero : e (x - y) = 0 := by rw [map_sub, hxy, sub_self]
    have hfx : f (x - y) = 0 := congrArg Prod.snd hzero
    have hlx : l (x - y) = 0 := congrArg Prod.fst hzero
    obtain ⟨c, hc⟩ := (P.toExtension.exact_cotangentComplex_toKaehler _).mp hfx
    have hc0 : c = 0 := by
      rw [← hc] at hlx
      have hldc : l (d c) = c := by
        have h := congrArg (fun g => g c) hld
        simpa only [LinearMap.comp_apply, LinearMap.id_apply] using h
      calc
        c = l (d c) := hldc.symm
        _ = 0 := hlx
    apply sub_eq_zero.mp
    rw [← hc, hc0, map_zero]
  · rintro ⟨c, ω⟩
    refine ⟨k (c, ω), ?_⟩
    apply Prod.ext
    · change l (d c + s' ω) = c
      rw [map_add]
      have hldc : l (d c) = c := by
        simpa only [← LinearMap.comp_apply, hld, LinearMap.id_apply]
      have hlsw : l (s' ω) = 0 := by
        have hw := congrArg (fun g => g ω) hls'
        simpa only [LinearMap.comp_apply, LinearMap.zero_apply] using hw
      rw [hldc, hlsw, add_zero]
    · change f (d c + s' ω) = ω
      rw [map_add, hfd]
      have hsω : f (s' ω) = ω := by
        have hw := congrArg (fun g => g ω) hs'
        simpa only [LinearMap.comp_apply, LinearMap.id_apply] using hw
      rw [hsω, zero_add]

/-! ## Localization, base change, and the field case -/

theorem smooth_localization
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.Smooth R S] (g : S) :
    Algebra.Smooth R (Localization.Away g) := by
  exact Algebra.Smooth.comp R S (Localization.Away g)

theorem smooth_localization_of_base
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (r : R) [Algebra (Localization.Away r) S]
    [IsScalarTower R (Localization.Away r) S]
    (hunit : IsUnit (algebraMap R S r)) [Algebra.Smooth R S] :
    Algebra.Smooth (Localization.Away r) S := by
  let _ : Algebra.FormallyEtale R (Localization.Away r) :=
    Algebra.FormallyEtale.of_isLocalization (Submonoid.powers r)
  exact Algebra.Smooth.mk
    (Algebra.FormallySmooth.of_restrictScalars R (Localization.Away r) S)
    (Algebra.FinitePresentation.of_restrict_scalars_finitePresentation
      R (Localization.Away r) S)

theorem smooth_base_change
    {R S R' : Type*} [CommRing R] [CommRing S] [CommRing R']
    [Algebra R S] [Algebra R R'] [Algebra.Smooth R S] :
    Algebra.Smooth R' (R' ⊗[R] S) := by
  infer_instance

theorem smooth_over_field_is_local_complete_intersection
    {k S : Type u} [Field k] [CommRing S] [Algebra k S]
    [Algebra.Smooth k S] :
    Formalization.Books.Algebra.Unit135.IsLocalCompleteIntersection k S := by
  sorry

/-! ## Standard smooth presentations -/

/- `Algebra.IsStandardSmooth` is Mathlib's quotient-by-relations definition:
   it is existence of a finite `SubmersivePresentation`, whose `map` selects
   the variables used by the Jacobian minor. -/
theorem standard_smooth_is_smooth
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.IsStandardSmooth R S] :
    Algebra.Smooth R S := by
  infer_instance

theorem submersive_presentation_consequences
    {R S ι σ : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Finite ι] [Finite σ] (P : Algebra.SubmersivePresentation R S ι σ) :
    Algebra.Smooth R S ∧
      Function.Injective P.toExtension.cotangentComplex ∧
      Module.Free S P.toExtension.Cotangent ∧
      Nonempty (Basis σ S P.toExtension.Cotangent) ∧
      Module.Free S (Formalization.Books.Algebra.Unit131.ModuleOfDifferentials R S) ∧
        Nonempty (Basis ((Set.range P.map)ᶜ : Set ι) S
        (Formalization.Books.Algebra.Unit131.ModuleOfDifferentials R S)) := by
  let _ : Algebra.IsStandardSmooth R S := P.isStandardSmooth
  constructor
  · exact standard_smooth_is_smooth (R := R) (S := S)
  constructor
  · exact P.cotangentComplex_injective
  constructor
  · infer_instance
  constructor
  · exact ⟨P.basisCotangent⟩
  constructor
  · infer_instance
  · exact ⟨P.basisKaehler⟩

theorem submersive_presentation_relative_dimension
    {R S ι σ : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Finite ι] [Finite σ] [Nontrivial S]
    (P : Algebra.SubmersivePresentation R S ι σ) :
    Module.rank S (Formalization.Books.Algebra.Unit131.ModuleOfDifferentials R S) =
      P.dimension := by
  sorry

theorem standard_smooth_localization
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.IsStandardSmooth R S] (g : S) :
    Algebra.IsStandardSmooth R (Localization.Away g) := by
  sorry

theorem standard_smooth_base_change
    {R S R' : Type*} [CommRing R] [CommRing S] [CommRing R']
    [Algebra R S] [Algebra R R'] [Algebra.IsStandardSmooth R S] :
    Algebra.IsStandardSmooth R' (R' ⊗[R] S) := by
  infer_instance

theorem standard_smooth_localization_of_base
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (r : R) [Algebra (Localization.Away r) S]
    [IsScalarTower R (Localization.Away r) S]
    (hunit : IsUnit (algebraMap R S r))
    [Algebra.IsStandardSmooth R S] :
    Algebra.IsStandardSmooth (Localization.Away r) S := by
  sorry

theorem standard_smooth_is_relative_global_complete_intersection
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.IsStandardSmooth R S] :
    Formalization.Books.Algebra.Unit136.IsRelativeGlobalCompleteIntersection
      (algebraMap R S) := by
  sorry

/-- The polynomial lift along the inclusion of variables `Fin n ↪ Fin (n+1)`. -/
noncomputable def liftPolynomialToSucc
    {R : Type u} [CommRing R] {n : ℕ}
    (f : MvPolynomial (Fin n) R) : MvPolynomial (Fin (n + 1)) R :=
  MvPolynomial.rename (Fin.castLE (Nat.le_succ n)) f

/-- The Jacobian determinant on the first `c` variables. -/
noncomputable def jacobianDeterminant
    {R : Type u} [CommRing R] {n c : ℕ} (hcn : c ≤ n)
    (fs : Fin c → MvPolynomial (Fin n) R) : MvPolynomial (Fin n) R :=
  Matrix.det (fun i j =>
    MvPolynomial.pderiv (Fin.castLE hcn i) (fs j))

/-- The quotient in the standard-smooth localization example. -/
noncomputable def jacobianInversionIdeal
    {R : Type u} [CommRing R] {n c : ℕ} (hcn : c ≤ n)
    (fs : Fin c → MvPolynomial (Fin n) R) :
    Ideal (MvPolynomial (Fin (n + 1)) R) :=
  Ideal.span
    (Set.range (fun i : Fin c => liftPolynomialToSucc (fs i)) ∪
      {MvPolynomial.X (Fin.last n) *
          liftPolynomialToSucc (jacobianDeterminant hcn fs) - 1})

noncomputable abbrev jacobianInversionRing
    {R : Type u} [CommRing R] {n c : ℕ} (hcn : c ≤ n)
    (fs : Fin c → MvPolynomial (Fin n) R) : Type u :=
  MvPolynomial (Fin (n + 1)) R ⧸ jacobianInversionIdeal hcn fs

theorem jacobian_inversion_is_standard_smooth
    {R : Type u} [CommRing R] {n c : ℕ} (hcn : c ≤ n)
    (fs : Fin c → MvPolynomial (Fin n) R) :
    Algebra.IsStandardSmooth R (jacobianInversionRing hcn fs) := by
  sorry

theorem standard_smooth_comp
    {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] [Algebra S T]
    [IsScalarTower R S T] [Algebra.IsStandardSmooth R S]
    [Algebra.IsStandardSmooth S T] :
    Algebra.IsStandardSmooth R T := by
  exact Algebra.IsStandardSmooth.trans R S T

theorem smooth_standard_smooth_cover
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.Smooth R S] :
    ∃ s : Set S, Ideal.span s = (⊤ : Ideal S) ∧
      ∀ g ∈ s, Algebra.IsStandardSmooth R (Localization.Away g) := by
  exact Algebra.Smooth.exists_span_eq_top_isStandardSmooth R S

theorem smooth_standard_smooth_basic_open_cover
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.Smooth R S] :
    ∃ s : Set S,
      (⋃ g ∈ s, (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum S))) = Set.univ ∧
        ∀ g ∈ s, Algebra.IsStandardSmooth R (Localization.Away g) := by
  sorry

theorem smooth_is_syntomic
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.Smooth R S] :
    Formalization.Books.Algebra.Unit136.IsSyntomic (algebraMap R S) := by
  sorry

/-! ## Smoothness at points and the Jacobian criterion -/

/-- Source-facing smoothness at a prime: smoothness on some basic open. -/
def IsSmoothAt
    (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
    (q : PrimeSpectrum S) : Prop :=
  ∃ g : S, g ∉ q.asIdeal ∧ Algebra.Smooth R (Localization.Away g)

def SmoothLocus
    (R S : Type*) [CommRing R] [CommRing S] [Algebra R S] :
    Set (PrimeSpectrum S) := {q | IsSmoothAt R S q}

def H1VanishingAt
    (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
    (q : PrimeSpectrum S) : Prop :=
  Subsingleton (Algebra.H1Cotangent R (Localization.AtPrime q.asIdeal))

def DifferentialsFiniteFreeAt
    (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
    (q : PrimeSpectrum S) : Prop :=
  Module.Finite (Localization.AtPrime q.asIdeal)
      (Formalization.Books.Algebra.Unit131.ModuleOfDifferentials R
        (Localization.AtPrime q.asIdeal)) ∧
    Module.Free (Localization.AtPrime q.asIdeal)
      (Formalization.Books.Algebra.Unit131.ModuleOfDifferentials R
        (Localization.AtPrime q.asIdeal))

def DifferentialsProjectiveAt
    (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
    (q : PrimeSpectrum S) : Prop :=
  Module.Projective (Localization.AtPrime q.asIdeal)
    (Formalization.Books.Algebra.Unit131.ModuleOfDifferentials R
      (Localization.AtPrime q.asIdeal))

def DifferentialsFlatAt
    (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
    (q : PrimeSpectrum S) : Prop :=
  Module.Flat (Localization.AtPrime q.asIdeal)
    (Formalization.Books.Algebra.Unit131.ModuleOfDifferentials R
      (Localization.AtPrime q.asIdeal))

theorem smooth_at_iff_local_cotangent_conditions
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.FinitePresentation R S] (q : PrimeSpectrum S) :
    List.TFAE
      [ IsSmoothAt R S q,
        H1VanishingAt R S q ∧ DifferentialsFiniteFreeAt R S q,
        H1VanishingAt R S q ∧ DifferentialsProjectiveAt R S q,
        H1VanishingAt R S q ∧ DifferentialsFlatAt R S q ] := by
  sorry

theorem smooth_iff_smooth_at_all_primes
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] :
    Algebra.Smooth R S ↔ ∀ q : PrimeSpectrum S, IsSmoothAt R S q := by
  sorry

theorem isOpen_smoothLocus
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    :
    IsOpen (SmoothLocus R S) := by
  sorry

theorem smooth_comp
    {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] [Algebra S T]
    [IsScalarTower R S T] [Algebra.Smooth R S] [Algebra.Smooth S T] :
    Algebra.Smooth R T := by
  exact Algebra.Smooth.comp R S T

theorem smooth_product_iff
    {R S' S'' : Type*} [CommRing R] [CommRing S'] [CommRing S'']
    [Algebra R S'] [Algebra R S''] :
    Algebra.Smooth R (S' × S'') ↔
      Algebra.Smooth R S' ∧ Algebra.Smooth R S'' := by
  sorry

/-- A maximal Jacobian minor indexed by an embedding of variables. -/
noncomputable def jacobianMinor
    {R : Type u} [CommRing R] {n c : ℕ}
    (fs : Fin c → MvPolynomial (Fin n) R) (e : Fin c ↪ Fin n) :
    MvPolynomial (Fin n) R :=
  Matrix.det (fun i j => MvPolynomial.pderiv (e i) (fs j))

theorem relative_global_complete_intersection_jacobian_criterion
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    {n c : ℕ} (P : Formalization.Books.Algebra.Unit134.Presentation
      R S (Fin n)) (fs : Fin c → P.Ring)
    (hker : P.ker = Ideal.ofList (List.ofFn fs))
    (hdim : ∀ p : PrimeSpectrum R,
      Nonempty (PrimeSpectrum
        (Formalization.Books.Algebra.Unit136.Fiber R S p)) →
        c ≤ n ∧
          ringKrullDim (Formalization.Books.Algebra.Unit136.Fiber R S p) =
            (((n - c : ℕ) : ℕ∞) : WithBot ℕ∞))
    (q : PrimeSpectrum S) :
    IsSmoothAt R S q ↔
      ∃ e : Fin c ↪ Fin n,
        (algebraMap P.Ring S) (jacobianMinor (R := R) (fun i => fs i) e) ∉ q.asIdeal := by
  sorry

/-! ## Flat fibres, smooth loci, field extension, and lifting -/

/-- Smoothness on a fibre at a chosen prime, in the same basic-open language. -/
def FiberSmoothAt
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (p : PrimeSpectrum R) (q : PrimeSpectrum (Formalization.Books.Algebra.Unit136.Fiber R S p)) : Prop :=
  letI : Algebra p.asIdeal.ResidueField
      (Formalization.Books.Algebra.Unit136.Fiber R S p) :=
    Algebra.TensorProduct.leftAlgebra
  ∃ g, g ∉ q.asIdeal ∧
    Algebra.Smooth p.asIdeal.ResidueField
      (Localization.Away g)

noncomputable def fiberMap
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (p : PrimeSpectrum R) :
    S →ₐ[R]
      Formalization.Books.Algebra.Unit136.Fiber R S p := by
  exact Algebra.TensorProduct.includeRight

theorem smooth_at_of_flat_fiber
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (p : PrimeSpectrum R) (q : PrimeSpectrum S)
    (hlying : p.asIdeal = q.asIdeal.comap (algebraMap R S))
    (hfp : ∃ g : S, g ∉ q.asIdeal ∧
      Algebra.FinitePresentation R (Localization.Away g))
    (hflat : RingHom.Flat
      (Localization.localRingHom p.asIdeal q.asIdeal
        (algebraMap R S) hlying))
    (qf : PrimeSpectrum (Formalization.Books.Algebra.Unit136.Fiber R S p))
    (hcorresponding : PrimeSpectrum.comap
      (fiberMap (R := R) (S := S) p).toRingHom qf = q)
    (hfiber : FiberSmoothAt p qf) :
    IsSmoothAt R S q := by
  sorry

theorem flat_base_change_smooth_locus
    {R S R' : Type*} [CommRing R] [CommRing S] [CommRing R']
    [Algebra R S] [Algebra R R'] [Algebra.FinitePresentation R S]
    [Module.Flat R R'] :
    SmoothLocus R' (R' ⊗[R] S) =
      (PrimeSpectrum.comap
      (Algebra.TensorProduct.includeRight :
        S →ₐ[R] (R' ⊗[R] S)).toRingHom) ⁻¹' SmoothLocus R S := by
  sorry

theorem smooth_field_change_at
    {k K S : Type*} [Field k] [Field K] [CommRing S]
    [Algebra k S] [Algebra k K] [Algebra.FiniteType k S]
    (qK : PrimeSpectrum (K ⊗[k] S)) (q : PrimeSpectrum S)
    (hlying : q.asIdeal = qK.asIdeal.comap
      (Algebra.TensorProduct.includeRight :
        S →ₐ[k] (K ⊗[k] S)).toRingHom) :
    letI : Algebra K (K ⊗[k] S) := Algebra.TensorProduct.leftAlgebra
    IsSmoothAt k S q ↔ IsSmoothAt K (K ⊗[k] S) qK := by
  sorry

/-- The source's local lifting conclusion, expressed using algebra equivalences
    and the canonical quotient ideal `I Sᵢ`. -/
def HasStandardSmoothLiftCover
    {R Sbar : Type u} [CommRing R] [CommRing Sbar]
    (I : Ideal R) [Algebra (R ⧸ I) Sbar] : Prop :=
  letI : Algebra R Sbar := Algebra.compHom Sbar
    ((algebraMap (R ⧸ I) Sbar).comp (Ideal.Quotient.mk I))
  ∃ (ι : Type*) (g : ι → Sbar),
    Ideal.span (Set.range g) = (⊤ : Ideal Sbar) ∧
      ∀ i, ∃ (T : Type*) (hT : CommRing T) (hRT : Algebra R T),
        letI : CommRing T := hT
        letI : Algebra R T := hRT
        letI : Algebra (R ⧸ I)
            (T ⧸ Ideal.map (algebraMap R T) I) :=
          Ideal.Quotient.algebraQuotientOfLEComap Ideal.le_comap_map
        Algebra.IsStandardSmooth R T ∧
          Nonempty (Localization.Away (g i) ≃ₐ[R ⧸ I]
            (T ⧸ Ideal.map (algebraMap R T) I))

theorem smooth_lift_standard_smooth_cover
    {R Sbar : Type u} [CommRing R] [CommRing Sbar]
    (I : Ideal R) [Algebra (R ⧸ I) Sbar]
    (h : Algebra.Smooth (R ⧸ I) Sbar) :
    HasStandardSmoothLiftCover (Sbar := Sbar) I := by
  sorry

end
end Formalization.Books.Algebra.Unit137
