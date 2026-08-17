import Formalization.Books.Algebra.Unit68.RegularSequences
import Formalization.Books.Algebra.Unit69.QuasiRegularSequences
import Formalization.Books.MoreAlgebra.Unit29.KoszulComplex
import Mathlib.Algebra.Homology.Single
import Mathlib.RingTheory.Localization.Basic
import Mathlib.RingTheory.MvPolynomial
import Mathlib.RingTheory.RingHom.FaithfullyFlat
import Mathlib.RingTheory.RingHom.Smooth

/-!
# More on Algebra, Chapter 30: Koszul regular sequences

The predicates below use the actual homological Koszul complexes from Chapter 29.
Finite sequences are represented by lists, as in the canonical regular- and
quasi-regular APIs from Algebra Chapters 68 and 69.
-/

namespace Formalization.Books.MoreAlgebra.Unit30

open CategoryTheory
open CategoryTheory.Limits
open Formalization.Books.MoreAlgebra.Unit29
open scoped TensorProduct

noncomputable section

universe u

/-! ## The complexes and the four regularity predicates -/

/- The list presentation is the bridge between the book-facing `List` APIs and
   Chapter 29's canonical `Fin r → R` presentation. -/
noncomputable def koszulComplexOnList
    (R : Type u) [CommRing R] (f : List R) :
    ChainComplex (ModuleCat.{u} R) ℕ :=
  koszulComplexOnNat R f.length (fun i => f.get i)

/- Tensoring with the complex concentrated in degree zero at `M` is the
   canonical categorical model of `K_•(R, f) ⊗_R M`. -/
noncomputable def koszulComplexOnListWithCoefficients
    (R M : Type u) [CommRing R] [AddCommGroup M] [Module R M]
    (f : List R) : ChainComplex (ModuleCat.{u} R) ℕ :=
  tensorChainComplex R (koszulComplexOnList R f)
    ((ChainComplex.single₀ (ModuleCat.{u} R)).obj (ModuleCat.of R M))

/-- A sequence is Koszul-regular on `M` when its coefficient Koszul complex
has zero homology in every positive degree. -/
def IsMKoszulRegular
    (R M : Type u) [CommRing R] [AddCommGroup M] [Module R M]
    (f : List R) : Prop :=
  ∀ i : ℕ, i ≠ 0 →
    IsZero ((koszulComplexOnListWithCoefficients R M f).homology i)

/-- A sequence is `H₁`-regular on `M` when the first Koszul homology vanishes. -/
def IsMHOneRegular
    (R M : Type u) [CommRing R] [AddCommGroup M] [Module R M]
    (f : List R) : Prop :=
  IsZero ((koszulComplexOnListWithCoefficients R M f).homology 1)

/-- Koszul regularity of a sequence in a ring. -/
def IsKoszulRegular (R : Type u) [CommRing R] (f : List R) : Prop :=
  IsMKoszulRegular R R f

/-- `H₁`-regularity of a sequence in a ring. -/
def IsHOneRegular (R : Type u) [CommRing R] (f : List R) : Prop :=
  IsMHOneRegular R R f

/-! ## The comparison chain and the length-one example -/

theorem isMKoszulRegular_of_isWeaklyRegular
    (R M : Type u) [CommRing R] [AddCommGroup M] [Module R M]
    (f : List R) (hf : RingTheory.Sequence.IsWeaklyRegular M f) :
    IsMKoszulRegular R M f := by
  sorry

theorem isMKoszulRegular_of_isRegular
    (R M : Type u) [CommRing R] [AddCommGroup M] [Module R M]
    (f : List R) (hf : RingTheory.Sequence.IsRegular M f) :
    IsMKoszulRegular R M f := by
  exact isMKoszulRegular_of_isWeaklyRegular R M f hf.toIsWeaklyRegular

theorem isKoszulRegular_of_isRegular
    (R : Type u) [CommRing R] (f : List R)
    (hf : RingTheory.Sequence.IsRegular R f) :
    IsKoszulRegular R f := by
  exact isMKoszulRegular_of_isRegular R R f hf

theorem isMHOneRegular_of_isMKoszulRegular
    (R M : Type u) [CommRing R] [AddCommGroup M] [Module R M]
    (f : List R) (hf : IsMKoszulRegular R M f) :
    IsMHOneRegular R M f := by
  sorry

theorem isHOneRegular_of_isKoszulRegular
    (R : Type u) [CommRing R] (f : List R)
    (hf : IsKoszulRegular R f) :
    IsHOneRegular R f := by
  exact isMHOneRegular_of_isMKoszulRegular R R f hf

theorem isMQuasiRegular_of_isMHOneRegular
    (R M : Type u) [CommRing R] [AddCommGroup M] [Module R M]
    (f : List R) (hf : IsMHOneRegular R M f) :
    Formalization.Books.Algebra.Unit69.IsMQuasiRegular R M f := by
  sorry

theorem regular_koszul_hone_quasi_chain
    (R : Type u) [CommRing R] (f : List R)
    (hf : RingTheory.Sequence.IsRegular R f) :
    IsKoszulRegular R f ∧
      (IsKoszulRegular R f → IsHOneRegular R f) ∧
        (IsHOneRegular R f →
          Formalization.Books.Algebra.Unit69.IsQuasiRegular R f) := by
  exact ⟨isKoszulRegular_of_isRegular R f hf,
    isHOneRegular_of_isKoszulRegular R f,
    isMQuasiRegular_of_isMHOneRegular R R f⟩

/- The source's statement that none of the three comparison arrows has a
   converse is recorded for the actual Chapter 29 complexes. -/
theorem koszul_regularities_no_general_converse :
    (¬ ∀ (R : Type u) [CommRing R] (f : List R),
        IsKoszulRegular R f → RingTheory.Sequence.IsRegular R f) ∧
      (¬ ∀ (R : Type u) [CommRing R] (f : List R),
        IsHOneRegular R f → IsKoszulRegular R f) ∧
      (¬ ∀ (R : Type u) [CommRing R] (f : List R),
        Formalization.Books.Algebra.Unit69.IsQuasiRegular R f →
          IsHOneRegular R f) := by
  sorry

theorem length_one_regular_koszul_hone_tfae
    (R : Type u) [CommRing R] (f : R) (hunit : ¬ IsUnit f) :
    List.TFAE [
      RingTheory.Sequence.IsRegular R [f],
      IsKoszulRegular R [f],
      IsHOneRegular R [f]] := by
  sorry

theorem length_one_regular_koszul_hone_imply_quasi
    (R : Type u) [CommRing R] (f : R) :
    IsKoszulRegular R [f] →
      IsHOneRegular R [f] ∧
        Formalization.Books.Algebra.Unit69.IsQuasiRegular R [f] := by
  intro hf
  exact ⟨isHOneRegular_of_isKoszulRegular R [f] hf,
    isMQuasiRegular_of_isMHOneRegular R R [f]
      (isHOneRegular_of_isKoszulRegular R [f] hf)⟩

/- The example in the source is kept explicit rather than represented by an
   existential counterexample, so its defining relations remain usable. -/
inductive lengthOneExampleVariable
  | x
  | y (n : ℕ)
deriving DecidableEq

def lengthOneExampleX (k : Type u) [CommRing k] :
    MvPolynomial lengthOneExampleVariable k :=
  MvPolynomial.X .x

def lengthOneExampleY (k : Type u) [CommRing k] (n : ℕ) :
    MvPolynomial lengthOneExampleVariable k :=
  MvPolynomial.X (.y n)

def lengthOneExampleRelations (k : Type u) [CommRing k] :
    Set (MvPolynomial lengthOneExampleVariable k) :=
  {lengthOneExampleX k * lengthOneExampleY k 0} ∪
    Set.range (fun n : ℕ =>
      lengthOneExampleX k * lengthOneExampleY k (n + 1) -
        lengthOneExampleY k n)

def lengthOneExampleIdeal (k : Type u) [CommRing k] :
    Ideal (MvPolynomial lengthOneExampleVariable k) :=
  Ideal.span (lengthOneExampleRelations k)

abbrev lengthOneExampleRing (k : Type u) [Field k] :=
  MvPolynomial lengthOneExampleVariable k ⧸ lengthOneExampleIdeal k

def lengthOneExampleXbar (k : Type u) [Field k] : lengthOneExampleRing k :=
  Ideal.Quotient.mk (lengthOneExampleIdeal k) (lengthOneExampleX k)

def lengthOneExampleYbar (k : Type u) [Field k] (n : ℕ) :
    lengthOneExampleRing k :=
  Ideal.Quotient.mk (lengthOneExampleIdeal k) (lengthOneExampleY k n)

theorem length_one_example_is_zero_divisor (k : Type u) [Field k] :
    ¬ IsSMulRegular (lengthOneExampleRing k) (lengthOneExampleXbar k) := by
  sorry

theorem length_one_example_is_quasi_regular (k : Type u) [Field k] :
    Formalization.Books.Algebra.Unit69.IsQuasiRegular
      (lengthOneExampleRing k) [lengthOneExampleXbar k] := by
  sorry

/- This is the source's associated-graded assertion in the canonical form of
   Algebra Chapter 69: the source of the map is the polynomial presentation
   and the target is the direct sum of the powers quotient. -/
theorem length_one_example_associated_graded_map_bijective
    (k : Type u) [Field k] :
    Function.Bijective
      (Formalization.Books.Algebra.Unit69.quasiRegularCanonicalMap
        (lengthOneExampleRing k) (lengthOneExampleRing k)
        [lengthOneExampleXbar k]) := by
  exact length_one_example_is_quasi_regular k

/-! ## Multiplication, base change, and quasi-regularity -/

theorem isMHOneRegular_append_mul
    (R M : Type u) [CommRing R] [AddCommGroup M] [Module R M]
    (pre : List R) (f g : R)
    (hf : IsMHOneRegular R M (pre ++ [f]))
    (hg : IsMHOneRegular R M (pre ++ [g])) :
    IsMHOneRegular R M (pre ++ [f * g]) := by
  sorry

theorem isMKoszulRegular_append_mul
    (R M : Type u) [CommRing R] [AddCommGroup M] [Module R M]
    (pre : List R) (f g : R)
    (hf : IsMKoszulRegular R M (pre ++ [f]))
    (hg : IsMKoszulRegular R M (pre ++ [g])) :
    IsMKoszulRegular R M (pre ++ [f * g]) := by
  sorry

theorem isMHOneRegular_of_flat_baseChange
    (R S M : Type u) [CommRing R] [CommRing S]
    [AddCommGroup M] [Module R M] [Algebra R S]
    (hflat : RingHom.Flat (algebraMap R S)) (f : List R)
    (hf : IsMHOneRegular R M f) :
    IsMHOneRegular S (S ⊗[R] M) (f.map (algebraMap R S)) := by
  sorry

theorem isMKoszulRegular_of_flat_baseChange
    (R S M : Type u) [CommRing R] [CommRing S]
    [AddCommGroup M] [Module R M] [Algebra R S]
    (hflat : RingHom.Flat (algebraMap R S)) (f : List R)
    (hf : IsMKoszulRegular R M f) :
    IsMKoszulRegular S (S ⊗[R] M) (f.map (algebraMap R S)) := by
  sorry

theorem isMQuasiRegular_of_isMHOneRegular_of_flat_baseChange
    (R S M : Type u) [CommRing R] [CommRing S]
    [AddCommGroup M] [Module R M] [Algebra R S]
    (hflat : RingHom.Flat (algebraMap R S)) (f : List R)
    (hf : IsMHOneRegular R M f) :
    Formalization.Books.Algebra.Unit69.IsMQuasiRegular S
      (S ⊗[R] M) (f.map (algebraMap R S)) := by
  exact isMQuasiRegular_of_isMHOneRegular S (S ⊗[R] M)
    (f.map (algebraMap R S))
    (isMHOneRegular_of_flat_baseChange R S M hflat f hf)

/-! ## The Noetherian local equivalence -/

theorem noetherian_local_regular_koszul_hone_quasi_tfae
    (R M : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M] [Nontrivial M]
    (f : List R) (hf : ∀ x ∈ f, x ∈ IsLocalRing.maximalIdeal R) :
    List.TFAE [
      RingTheory.Sequence.IsRegular M f,
      IsMKoszulRegular R M f,
      IsMHOneRegular R M f,
      Formalization.Books.Algebra.Unit69.IsMQuasiRegular R M f] := by
  sorry

theorem noetherian_local_regular_koszul_hone_quasi_tfae_ring
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (f : List R)
    (hf : ∀ x ∈ f, x ∈ IsLocalRing.maximalIdeal R) :
    List.TFAE [
      RingTheory.Sequence.IsRegular R f,
      IsKoszulRegular R f,
      IsHOneRegular R f,
      Formalization.Books.Algebra.Unit69.IsQuasiRegular R f] := by
  exact noetherian_local_regular_koszul_hone_quasi_tfae R R f hf

/-! ## Quotients, conormal ideals, and joins -/

theorem ideal_inf_ofList_eq_mul_of_isHOneRegular_quotient
    (A : Type u) [CommRing A] (I : Ideal A) (g : List A)
    (hg : IsHOneRegular (A ⧸ I)
      (g.map (Ideal.Quotient.mk I))) :
    I ⊓ Ideal.ofList g = I * Ideal.ofList g := by
  sorry

theorem ideal_inf_sq_eq_mul_of_isHOneRegular_quotient
    (A : Type u) [CommRing A] (I J : Ideal A) (hIJ : I ≤ J)
    (hgen : ∃ g : List A,
      I ⊔ Ideal.ofList g = J ∧
        IsHOneRegular (A ⧸ I) (g.map (Ideal.Quotient.mk I))) :
    I ⊓ J ^ 2 = I * J := by
  sorry

theorem isQuasiRegular_append_of_isQuasiRegular_of_isHOneRegular_quotient
    (A : Type u) [CommRing A] (I : Ideal A) (f g : List A)
    (hI : Ideal.ofList f = I)
    (hf : Formalization.Books.Algebra.Unit69.IsQuasiRegular A f)
    (hg : IsHOneRegular (A ⧸ I) (g.map (Ideal.Quotient.mk I))) :
    Formalization.Books.Algebra.Unit69.IsQuasiRegular A (f ++ g) := by
  sorry

theorem isHOneRegular_append_of_isHOneRegular_of_isHOneRegular_quotient
    (A : Type u) [CommRing A] (I : Ideal A) (f g : List A)
    (hI : Ideal.ofList f = I)
    (hf : IsHOneRegular A f)
    (hg : IsHOneRegular (A ⧸ I) (g.map (Ideal.Quotient.mk I))) :
    IsHOneRegular A (f ++ g) := by
  sorry

theorem isHOneRegular_quotient_of_isHOneRegular_append
    (A : Type u) [CommRing A] (f g : List A)
    (hf : IsHOneRegular A (f ++ g)) :
    IsHOneRegular (A ⧸ Ideal.ofList f)
      (g.map (Ideal.Quotient.mk (Ideal.ofList f))) := by
  sorry

theorem isKoszulRegular_append_of_isKoszulRegular_of_isKoszulRegular_quotient
    (A : Type u) [CommRing A] (I : Ideal A) (f g : List A)
    (hI : Ideal.ofList f = I)
    (hf : IsKoszulRegular A f)
    (hg : IsKoszulRegular (A ⧸ I) (g.map (Ideal.Quotient.mk I))) :
    IsKoszulRegular A (f ++ g) := by
  sorry

/- The source explicitly warns that the prefix regularity hypothesis in the
   truncation theorem below is essential; the theorem therefore retains both
   Koszul-regularity assumptions rather than weakening its interface. -/
theorem isKoszulRegular_quotient_of_isKoszulRegular_append
    (A : Type u) [CommRing A] (f g : List A)
    (hf : IsKoszulRegular A f)
    (hfg : IsKoszulRegular A (f ++ g)) :
    IsKoszulRegular (A ⧸ Ideal.ofList f)
      (g.map (Ideal.Quotient.mk (Ideal.ofList f))) := by
  sorry

/-! ## Independence of generators -/

theorem isQuasiRegular_of_same_length_quasiRegular_generators
    (R : Type u) [CommRing R] (I : Ideal R) (f : List R)
    (hI : Ideal.ofList f = I)
    (hgen : ∃ g : List R, g.length = f.length ∧
      Ideal.ofList g = I ∧
        Formalization.Books.Algebra.Unit69.IsQuasiRegular R g) :
    Formalization.Books.Algebra.Unit69.IsQuasiRegular R f := by
  sorry

theorem isHOneRegular_of_same_length_HOneRegular_generators
    (R : Type u) [CommRing R] (I : Ideal R) (f : List R)
    (hI : Ideal.ofList f = I)
    (hgen : ∃ g : List R, g.length = f.length ∧
      Ideal.ofList g = I ∧ IsHOneRegular R g) :
    IsHOneRegular R f := by
  sorry

theorem isKoszulRegular_of_same_length_KoszulRegular_generators
    (R : Type u) [CommRing R] (I : Ideal R) (f : List R)
    (hI : Ideal.ofList f = I)
    (hgen : ∃ g : List R, g.length = f.length ∧
      Ideal.ofList g = I ∧ IsKoszulRegular R g) :
    IsKoszulRegular R f := by
  sorry

/-! ## A linear polynomial nonzerodivisor -/

/- The injectivity hypothesis in the McCoy lemma, written using the
   finite-function model of `R^{⊕ n}`. -/
def coefficientMultiplicationInjective
    (R : Type u) [CommRing R] (n : ℕ) (a : Fin n → R) : Prop :=
  Function.Injective (fun x : R => fun i => x * a i)

/- The polynomial `∑ aᵢ tᵢ` attached to a finite family of coefficients. -/
def linearPolynomialCombination
    (R : Type u) [CommRing R] (n : ℕ) (a : Fin n → R) :
    MvPolynomial (Fin n) R :=
  ∑ i : Fin n, MvPolynomial.C (a i) * MvPolynomial.X i

theorem linearPolynomialCombination_is_non_zero_divisor
    (R : Type u) [CommRing R] (n : ℕ) (a : Fin n → R)
    (ha : coefficientMultiplicationInjective R n a) :
    IsSMulRegular (MvPolynomial (Fin n) R)
      (linearPolynomialCombination R n a) := by
  sorry

/-! ## Making a Koszul-regular sequence regular after smooth base change -/

/- Inverting the product of the diagonal variables is canonically equivalent
   to inverting each diagonal variable; this keeps the localization a single
   `Localization (Submonoid.powers ·)` while retaining the source's ring. -/
abbrev triangularIndex (n : ℕ) :=
  {ij : Fin n × Fin n // ij.1 ≤ ij.2}

def triangularVariable
    (R : Type u) [CommRing R] (n : ℕ) (i j : Fin n) (hij : i ≤ j) :
    MvPolynomial (triangularIndex n) R :=
  MvPolynomial.X ⟨(i, j), hij⟩

def triangularDiagonalProduct
    (R : Type u) [CommRing R] (n : ℕ) :
    MvPolynomial (triangularIndex n) R :=
  ∏ i : Fin n, triangularVariable R n i i le_rfl

abbrev triangularKoszulRing
    (R : Type u) [CommRing R] (n : ℕ) :=
  Localization (Submonoid.powers (triangularDiagonalProduct R n))

def triangularAlgebraMap
    (R : Type u) [CommRing R] (n : ℕ) :
    R →+* triangularKoszulRing R n :=
  algebraMap R (triangularKoszulRing R n)

def triangularElement
    (R : Type u) [CommRing R] (n : ℕ) (f : Fin n → R) (i : Fin n) :
    triangularKoszulRing R n :=
  ∑ j : {j : Fin n // i ≤ j},
    algebraMap (MvPolynomial (triangularIndex n) R)
      (triangularKoszulRing R n)
      (MvPolynomial.C (f j.1) * triangularVariable R n i j.1 j.2)

def triangularSequence
    (R : Type u) [CommRing R] (n : ℕ) (f : Fin n → R) :
    Fin n → triangularKoszulRing R n :=
  fun i => triangularElement R n f i

theorem triangularAlgebraMap_faithfullyFlat_smooth
    (R : Type u) [CommRing R] (n : ℕ) :
    (triangularAlgebraMap R n).FaithfullyFlat ∧
      (triangularAlgebraMap R n).Smooth := by
  sorry

theorem koszulRegular_becomes_regular_after_triangular_baseChange
    (R : Type u) [CommRing R] (n : ℕ) (f : Fin n → R)
    (hf : IsKoszulRegular R (List.ofFn f))
    (hI : Ideal.ofList (List.ofFn f) ≠ (⊤ : Ideal R)) :
    RingTheory.Sequence.IsRegular (triangularKoszulRing R n)
        (List.ofFn (triangularSequence R n f)) ∧
      Ideal.map (triangularAlgebraMap R n)
          (Ideal.ofList (List.ofFn f)) =
        Ideal.ofList (List.ofFn (triangularSequence R n f)) := by
  sorry

end

end Formalization.Books.MoreAlgebra.Unit30
