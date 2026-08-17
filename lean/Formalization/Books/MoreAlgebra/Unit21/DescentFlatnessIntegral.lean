import Formalization.Books.Algebra.Unit07.FiniteRingMaps
import Formalization.Books.Algebra.Unit39.FlatModules
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.RingTheory.AdjoinRoot
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
  sorry

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
  sorry

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
  sorry

/-! ## The split-image lemma -/

/- The source's index condition `1 ≤ k_i ≤ d_i` is represented by the
   canonical finite type `Fin (degree i)`.  The quotient equivalence in the
   presentation identifies its structure map with the source's `R → S`. -/
/-- The image of the spectrum of a split polynomial quotient is the union of
the vanishing loci of the selected-root ideal images. -/
theorem split_image
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (presentation : SplitPolynomialPresentation R S) :
    Set.range (PrimeSpectrum.comap (algebraMap R S)) =
      PrimeSpectrum.zeroLocus
        ((⨅ k : ∀ i, Fin (presentation.degree i),
          splitImageIdeal presentation.ideal presentation.root k : Ideal R) : Set R) := by
  sorry

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
