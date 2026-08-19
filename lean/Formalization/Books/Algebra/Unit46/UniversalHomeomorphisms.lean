import Formalization.Books.Algebra.Unit03.BasicNotions
import Formalization.Books.Algebra.Unit14.BaseChange
import Formalization.Books.Algebra.Unit36.FiniteIntegralRingExtensions
import Mathlib.Algebra.Algebra.ZMod
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Data.Nat.Choose.Factorization
import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.FieldTheory.PurelyInseparable.PerfectClosure
import Mathlib.RingTheory.Adjoin.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Mathlib.RingTheory.Spectrum.Prime.Homeomorph
import Mathlib.RingTheory.Spectrum.Prime.RingHom
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.Topology.Maps.Basic

/-!
# Commutative Algebra, Chapter 46: Universal homeomorphisms

The source's ring-map conditions are expressed using Mathlib's canonical
`PrimeSpectrum.comap`, `RingHom.IsIntegral`, tensor-product maps, residue
fields, and `IsPurelyInseparable`.  The elementwise locally nilpotent-kernel
condition reuses Chapter 3's `locallyNilpotentIdeal`.
-/

namespace Formalization.Books.Algebra.Unit46

open Set
open Topology
open scoped TensorProduct
open Formalization.Books.Algebra.Unit14

universe u v w

noncomputable section

/-! ## Source-facing predicates and maps -/

/- The source's locally nilpotent kernel is exactly the earlier chapter's
   elementwise locally nilpotent ideal predicate applied to `RingHom.ker`. -/
/-- The kernel of a ring map is locally nilpotent elementwise. -/
def locallyNilpotentKernel {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) : Prop :=
  Formalization.Books.Algebra.Unit03.locallyNilpotentIdeal (RingHom.ker f)

/- The source repeatedly says that a ring is generated as an algebra by a
   specified set.  `Algebra.adjoin` is the canonical construction; the
   algebra structure here is the one induced by the ring map. -/
/-- The target is generated over the source by a set of elements. -/
def generatedBy {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (s : Set S) : Prop :=
  letI : Algebra R S := f.toAlgebra
  Algebra.adjoin R s = ⊤

/-- Every target element has a positive power in the image of a ring map. -/
def powerSurjective {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) : Prop :=
  ∀ x : S, ∃ n : ℕ, 0 < n ∧ x ^ n ∈ f.range

/-- The source's ``square and cube in the image'' generation condition. -/
def twoThreeGenerated {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) : Prop :=
  generatedBy f {x : S | x ^ 2 ∈ f.range ∧ x ^ 3 ∈ f.range}

/-- The source's positive-characteristic generation condition for a ring map. -/
def pPowerGenerated {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (p : ℕ) : Prop :=
  generatedBy f
    {x : S | ∃ n : ℕ, 0 < n ∧
      x ^ (p ^ n) ∈ f.range ∧ (p ^ n : S) * x ∈ f.range}

/- `ZMod p` is Mathlib's canonical prime field.  The characteristic witness
   is explicit because `ZMod.algebra` is intentionally not a global instance. -/
/-- Algebraicity over the prime field of characteristic `p`. -/
def isAlgebraicOverPrimeField (p : ℕ) (K : Type*) [Field K]
    (hK : CharP K p) : Prop :=
  letI : CharP K p := hK
  letI : Algebra (ZMod p) K := ZMod.algebra K p
  Algebra.IsAlgebraic (ZMod p) K

/-- The first condition in the source's powers-field lemma. -/
def fieldPowerProperty {k k' : Type*} [Field k] [Field k']
    [Algebra k k'] : Prop :=
  ∀ x : k', ∃ n : ℕ, 0 < n ∧ x ^ n ∈ (algebraMap k k').range

/-- The classification condition in the source's powers-field lemma. -/
def fieldPowerClassification {k k' : Type*} [Field k] [Field k']
    [Algebra k k'] : Prop :=
  Function.Surjective (algebraMap k k') ∨
    ∃ p : ℕ, p.Prime ∧
      ∃ hk : CharP k p, ∃ hk' : CharP k' p,
        IsPurelyInseparable k k' ∨
          (isAlgebraicOverPrimeField p k hk ∧
            isAlgebraicOverPrimeField p k' hk')

/-- The source's positive-characteristic generation condition for a field extension. -/
def pPowerFieldGenerated {k k' : Type*} [Field k] [Field k']
    [Algebra k k'] (p : ℕ) : Prop :=
  IntermediateField.adjoin k
      {x : k' | ∃ n : ℕ, 0 < n ∧
        x ^ (p ^ n) ∈ (algebraMap k k').range ∧
          (p ^ n : k') * x ∈ (algebraMap k k').range} = ⊤

/-- The corrected positive-characteristic classification in the source's
    `p`-power field lemma. -/
def pPowerFieldClassification {k k' : Type*} [Field k] [Field k']
    [Algebra k k'] (p : ℕ) : Prop :=
  Function.Surjective (algebraMap k k') ∨
    ∃ _hk : CharP k p, ∃ _hk' : CharP k' p, IsPurelyInseparable k k'

/- The source's `Z[x^(p^n), p^n x, ...]` is represented by the canonical
   subalgebra of a two-variable integer polynomial ring. -/
/-- The integer polynomial subalgebra used in the auxiliary powers lemma. -/
def helpWithPowersSubalgebra (p n m : ℕ) :
    Subalgebra ℤ (MvPolynomial (Fin 2) ℤ) :=
  Algebra.adjoin ℤ
    { (MvPolynomial.X (0 : Fin 2)) ^ (p ^ n),
      (p ^ n : MvPolynomial (Fin 2) ℤ) * MvPolynomial.X (0 : Fin 2),
      (MvPolynomial.X (1 : Fin 2)) ^ (p ^ m),
      (p ^ m : MvPolynomial (Fin 2) ℤ) * MvPolynomial.X (1 : Fin 2) }

/- The map between residue fields at a prime and its inverse image is the
   canonical Mathlib map. -/
/-- The residue-field map induced by a ring map at a target prime. -/
noncomputable def residueFieldMap {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (q : PrimeSpectrum S) :
    (PrimeSpectrum.comap f q).asIdeal.ResidueField →+* q.asIdeal.ResidueField :=
  Ideal.ResidueField.map (PrimeSpectrum.comap f q).asIdeal q.asIdeal f rfl

/-- Every residue-field map induced by `f` is bijective. -/
def residueFieldMapsBijective {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) : Prop :=
  ∀ q : PrimeSpectrum S, Function.Bijective (residueFieldMap f q)

/-- Every residue-field extension induced by `f` is purely inseparable. -/
def residueFieldExtensionsPurelyInseparable {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) : Prop :=
  ∀ q : PrimeSpectrum S,
    letI : Algebra ((PrimeSpectrum.comap f q).asIdeal.ResidueField)
        (q.asIdeal.ResidueField) := (residueFieldMap f q).toAlgebra
    IsPurelyInseparable ((PrimeSpectrum.comap f q).asIdeal.ResidueField)
      (q.asIdeal.ResidueField)

/-- The two equivalent powers-field conditions for every residue-field extension. -/
def residueFieldPowerProperties {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) : Prop :=
  ∀ q : PrimeSpectrum S,
    letI : Algebra ((PrimeSpectrum.comap f q).asIdeal.ResidueField)
        (q.asIdeal.ResidueField) := (residueFieldMap f q).toAlgebra
    fieldPowerProperty (k := (PrimeSpectrum.comap f q).asIdeal.ResidueField)
        (k' := q.asIdeal.ResidueField) ∧
      fieldPowerClassification (k := (PrimeSpectrum.comap f q).asIdeal.ResidueField)
        (k' := q.asIdeal.ResidueField)

/-- The two equivalent `p`-power conditions for every residue-field extension. -/
def pResidueFieldProperties {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (p : ℕ) : Prop :=
  ∀ q : PrimeSpectrum S,
    letI : Algebra ((PrimeSpectrum.comap f q).asIdeal.ResidueField)
        (q.asIdeal.ResidueField) := (residueFieldMap f q).toAlgebra
    pPowerFieldGenerated (k := (PrimeSpectrum.comap f q).asIdeal.ResidueField)
        (k' := q.asIdeal.ResidueField) p ∧
      pPowerFieldClassification (k := (PrimeSpectrum.comap f q).asIdeal.ResidueField)
        (k' := q.asIdeal.ResidueField) p

/-- The polynomial-generation condition in the final source lemma. -/
def universallyBijectiveGenerated {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) : Prop :=
  generatedBy f
    {x : S | ∃ n : ℕ, 0 < n ∧ ∃ P : Polynomial R,
      P.map f = (Polynomial.X - Polynomial.C x) ^ n}

/-! ## Universal homeomorphisms -/

/-- Tensoring an algebraically purely inseparable field extension with an
    algebra induces a homeomorphism on spectra. -/
theorem tensorProduct_spectrum_homeomorph_of_isPurelyInseparable
    {k K R : Type*} [Field k] [Field K] [CommRing R]
    [Algebra k K] [Algebra k R] [IsPurelyInseparable k K] :
    IsHomeomorph (PrimeSpectrum.comap
      (Algebra.TensorProduct.includeRight : R →ₐ[k] K ⊗[k] R).toRingHom) := by
  let e := Algebra.TensorProduct.comm k R K
  have he : e.toAlgHom.comp
      (Algebra.TensorProduct.includeLeft : R →ₐ[k] R ⊗[k] K) =
      (Algebra.TensorProduct.includeRight : R →ₐ[k] K ⊗[k] R) := by
    exact Algebra.TensorProduct.comm_comp_includeLeft k R K
  rw [← he]
  simp only [AlgHom.toRingHom_eq_coe, AlgHom.comp_toRingHom,
    AlgEquiv.toAlgHom_toRingHom, PrimeSpectrum.comap_comp]
  exact (PrimeSpectrum.isHomeomorph_comap_of_isPurelyInseparable k K R).comp
    (PrimeSpectrum.isHomeomorph_comap_of_bijective e.bijective)

/-- The source's powers-field criterion: every element has a positive power in
    the base field exactly in the classified cases. -/
theorem fieldPowerProperty_iff_classification
    {k k' : Type*} [Field k] [Field k'] [Algebra k k'] :
    fieldPowerProperty (k := k) (k' := k') ↔
      fieldPowerClassification (k := k) (k' := k') := by
  sorry

/-- A surjective map with locally nilpotent kernel is a homeomorphism on
    spectra, isomorphic on residue fields, and retains these kernel facts
    after arbitrary base change. -/
theorem surjective_locallyNilpotentKernel
    {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (hf : Function.Surjective f) (hker : locallyNilpotentKernel f) :
    IsHomeomorph (PrimeSpectrum.comap f) ∧
      residueFieldMapsBijective f ∧
      ∀ (R' : Type*) [CommRing R'] (g : R →+* R'),
          Function.Surjective (baseChangeRingMap f g) ∧
            locallyNilpotentKernel (baseChangeRingMap f g) := by
  let hker' : RingHom.ker f ≤ nilradical R := by
    intro x hx
    exact (mem_nilradical).2 (hker x hx)
  refine ⟨PrimeSpectrum.isHomeomorph_comap f (fun x => ?_) hker', ?_, ?_⟩
  · obtain ⟨y, rfl⟩ := hf x
    exact ⟨1, by simp, y, by simp⟩
  · intro q
    exact RingHom.SurjectiveOnStalks.residueFieldMap_bijective
      (RingHom.surjectiveOnStalks_of_surjective hf) _ _ rfl
  · intro R' _ g
    let : Algebra R S := f.toAlgebra
    let : Algebra R R' := g.toAlgebra
    constructor
    · exact Algebra.TensorProduct.includeRight_surjective (T := R') hf
    · intro x hx
      let fa : R →ₐ[R] S := AlgHom.mk' f (by
        intro c y
        simp [Algebra.smul_def, RingHom.algebraMap_toAlgebra])
      let b : R ⊗[R] R' →ₐ[R] S ⊗[R] R' :=
        Algebra.TensorProduct.map fa (AlgHom.id R R')
      let a : R' →ₐ[R] R ⊗[R] R' := Algebra.TensorProduct.includeRight
      have hbker : RingHom.ker b.toRingHom ≤ nilradical (R ⊗[R] R') := by
        change RingHom.ker ((Algebra.TensorProduct.map fa (AlgHom.id R R')).toRingHom) ≤
          nilradical (R ⊗[R] R')
        have hEq : RingHom.ker ((Algebra.TensorProduct.map fa (AlgHom.id R R')).toRingHom) =
            (RingHom.ker fa).map
              (Algebra.TensorProduct.includeLeft : R →ₐ[R] R ⊗[R] R') := by
          have hmap : RingHom.ker ((Algebra.TensorProduct.map fa (AlgHom.id R R')).toRingHom) =
              RingHom.ker (Algebra.TensorProduct.map fa (AlgHom.id R R')) := by
            ext y
            rfl
          rw [hmap]
          exact Algebra.TensorProduct.rTensor_ker
            (R := R) (S := R) (A := R) (B := S) (C := R') fa hf
        rw [hEq]
        rw [Ideal.map_le_iff_le_comap]
        intro y hy
        have hy' : IsNilpotent y := (mem_nilradical).1 (hker' hy)
        exact (mem_nilradical).2 (hy'.map
          (Algebra.TensorProduct.includeLeft : R →ₐ[R] R ⊗[R] R').toRingHom)
      have hcomp : b.toRingHom.comp a.toRingHom = baseChangeRingMap f g := by
        ext y
        simp [b, a, fa, baseChangeRingMap]
      have hax : a.toRingHom x ∈ RingHom.ker b.toRingHom := by
        change b (a x) = 0
        change (b.toRingHom.comp a.toRingHom) x = 0
        rw [hcomp]
        exact hx
      have ha : Function.Injective a :=
        (Algebra.TensorProduct.includeRight_bijective
          (R := R) (A := R) (B := R') ⟨by intro x y h; exact h, by intro x; exact ⟨x, rfl⟩⟩).injective
      exact (IsNilpotent.map_iff (f := a.toRingHom) ha).mp ((mem_nilradical).1 (hbker hax))

/-- The powers criterion gives a homeomorphism on spectra and the source's
    powers-field description of all residue-field extensions. -/
theorem powerSurjective_locallyNilpotentKernel
    {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (hpower : powerSurjective f) (hker : locallyNilpotentKernel f) :
    IsHomeomorph (PrimeSpectrum.comap f) ∧ residueFieldPowerProperties f := by
  let hker' : RingHom.ker f ≤ nilradical R := by
    intro x hx
    exact (mem_nilradical).2 (hker x hx)
  refine ⟨PrimeSpectrum.isHomeomorph_comap f (fun x => ?_) hker', ?_⟩
  · simpa [powerSurjective] using hpower x
  · intro q
    let : Algebra ((PrimeSpectrum.comap f q).asIdeal.ResidueField)
        (q.asIdeal.ResidueField) := (residueFieldMap f q).toAlgebra
    have hfield : fieldPowerProperty
        (k := (PrimeSpectrum.comap f q).asIdeal.ResidueField)
        (k' := q.asIdeal.ResidueField) := by
      intro z
      obtain ⟨a, b, hb, hz⟩ :=
        IsFractionRing.div_surjective (S ⧸ q.asIdeal) z
      obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective a
      obtain ⟨w, hw⟩ := Ideal.Quotient.mk_surjective b
      obtain ⟨n, hn, r, hr⟩ := hpower y
      obtain ⟨m, hm, s, hs⟩ := hpower w
      refine ⟨n * m, Nat.mul_pos hn hm, ?_⟩
      refine ⟨algebraMap R ((PrimeSpectrum.comap f q).asIdeal.ResidueField) r ^ m /
          algebraMap R ((PrimeSpectrum.comap f q).asIdeal.ResidueField) s ^ n, ?_⟩
      have hY : residueFieldMap f q
          (algebraMap R ((PrimeSpectrum.comap f q).asIdeal.ResidueField) r) =
          algebraMap S (q.asIdeal.ResidueField) y ^ n := by
        calc
          residueFieldMap f q
              (algebraMap R ((PrimeSpectrum.comap f q).asIdeal.ResidueField) r) =
              algebraMap S (q.asIdeal.ResidueField) (f r) := by
                simpa [residueFieldMap] using
                  (Ideal.ResidueField.map_algebraMap
                    (PrimeSpectrum.comap f q).asIdeal q.asIdeal f rfl r)
          _ = algebraMap S (q.asIdeal.ResidueField) (y ^ n) := by rw [hr]
          _ = algebraMap S (q.asIdeal.ResidueField) y ^ n := by rw [map_pow]
      have hW : residueFieldMap f q
          (algebraMap R ((PrimeSpectrum.comap f q).asIdeal.ResidueField) s) =
          algebraMap S (q.asIdeal.ResidueField) w ^ m := by
        calc
          residueFieldMap f q
              (algebraMap R ((PrimeSpectrum.comap f q).asIdeal.ResidueField) s) =
              algebraMap S (q.asIdeal.ResidueField) (f s) := by
                simpa [residueFieldMap] using
                  (Ideal.ResidueField.map_algebraMap
                    (PrimeSpectrum.comap f q).asIdeal q.asIdeal f rfl s)
          _ = algebraMap S (q.asIdeal.ResidueField) (w ^ m) := by rw [hs]
          _ = algebraMap S (q.asIdeal.ResidueField) w ^ m := by rw [map_pow]
      have hz' : algebraMap S (q.asIdeal.ResidueField) y /
          algebraMap S (q.asIdeal.ResidueField) w = z := by
        simpa [Ideal.algebraMap_quotient_residueField_mk, ← hy, ← hw] using hz
      calc
        residueFieldMap f q
              (algebraMap R ((PrimeSpectrum.comap f q).asIdeal.ResidueField) r ^ m /
                algebraMap R ((PrimeSpectrum.comap f q).asIdeal.ResidueField) s ^ n) =
            (algebraMap S (q.asIdeal.ResidueField) y ^ n) ^ m /
              (algebraMap S (q.asIdeal.ResidueField) w ^ m) ^ n := by
                rw [map_div₀, map_pow, map_pow, hY, hW]
        _ = (algebraMap S (q.asIdeal.ResidueField) y /
              algebraMap S (q.asIdeal.ResidueField) w) ^ (n * m) := by
                rw [div_pow, ← pow_mul, ← pow_mul, Nat.mul_comm m n]
        _ = z ^ (n * m) := by rw [hz']
    exact ⟨hfield, (fieldPowerProperty_iff_classification
      (k := (PrimeSpectrum.comap f q).asIdeal.ResidueField)
      (k' := q.asIdeal.ResidueField)).mp hfield⟩

/-- The square-and-cube criterion gives a universal homeomorphism with
    residue-field isomorphisms. -/
theorem twoThreeGenerated_locallyNilpotentKernel
    {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (hgen : twoThreeGenerated f) (hker : locallyNilpotentKernel f) :
    IsHomeomorph (PrimeSpectrum.comap f) ∧
      residueFieldMapsBijective f ∧
        ∀ (R' : Type*) [CommRing R'] (g : R →+* R'),
          twoThreeGenerated (baseChangeRingMap f g) ∧
            locallyNilpotentKernel (baseChangeRingMap f g) := by
  sorry

/-- The auxiliary powers lemma for integer polynomials in two variables. -/
theorem exists_helpWithPowers_exponent
    (p n m : ℕ) (hp : p.Prime) (hn : 0 < n) (hm : 0 < m) :
    ∃ a : ℕ,
      (MvPolynomial.X (0 : Fin 2) + MvPolynomial.X (1 : Fin 2)) ^ (p ^ a) ∈
          helpWithPowersSubalgebra p n m ∧
        (p ^ a : MvPolynomial (Fin 2) ℤ) *
            (MvPolynomial.X (0 : Fin 2) + MvPolynomial.X (1 : Fin 2)) ∈
          helpWithPowersSubalgebra p n m := by
  refine ⟨n * p ^ n + m * p ^ m + n + m, ?_, ?_⟩
  · let a : ℕ := n * p ^ n + m * p ^ m + n + m
    let A := helpWithPowersSubalgebra p n m
    change (MvPolynomial.X (0 : Fin 2) + MvPolynomial.X (1 : Fin 2)) ^ (p ^ a) ∈ A
    rw [(Commute.all (MvPolynomial.X (0 : Fin 2)) (MvPolynomial.X (1 : Fin 2))).add_pow]
    apply A.sum_mem
    intro i hi
    have hiN : i ≤ p ^ a := by
      exact Nat.le_of_lt_succ (Finset.mem_range.1 hi)
    let j : ℕ := p ^ a - i
    let r : ℕ := i % p ^ n
    let s : ℕ := j % p ^ m
    have hp_pos : 0 < p := hp.pos
    have hj : j + i = p ^ a := by
      dsimp [j]
      omega
    have hrlt : r < p ^ n := by
      exact Nat.mod_lt _ (by positivity)
    have hslt : s < p ^ m := by
      exact Nat.mod_lt _ (by positivity)
    have hidecomp : i = p ^ n * (i / p ^ n) + r := by
      have hmod := Nat.mod_add_div i (p ^ n)
      dsimp [r]
      omega
    have hjdecomp : j = p ^ m * (j / p ^ m) + s := by
      have hmod := Nat.mod_add_div j (p ^ m)
      dsimp [s]
      omega
    have hchoose : p ^ (n * r + m * s) ∣ (p ^ a).choose i := by
      by_cases hri : r = 0
      · by_cases hsj : s = 0
        · simp [hri, hsj]
        · have hjpos : 0 < j := by
            by_contra hj0
            have hjz : j = 0 := Nat.eq_zero_of_not_pos hj0
            apply hsj
            simp [s, hjz]
          have hfacj : j.factorization p < m := by
            by_contra hfac
            have hdvd : p ^ m ∣ j :=
              (hp.pow_dvd_iff_le_factorization (Nat.ne_of_gt hjpos)).2
                (Nat.le_of_not_gt hfac)
            exact hsj (by simpa [s] using Nat.mod_eq_zero_of_dvd hdvd)
          have hchoosefac :
              ((p ^ a).choose j).factorization p = a - j.factorization p :=
            Nat.factorization_choose_prime_pow hp (by omega) (Nat.ne_of_gt hjpos)
          have hchooseeq : (p ^ a).choose i = (p ^ a).choose j := by
            dsimp [j]
            exact (Nat.choose_symm hiN).symm
          apply (hp.pow_dvd_iff_le_factorization (Nat.choose_ne_zero hiN)).2
          rw [hchooseeq, hchoosefac]
          have hsle : s ≤ p ^ m - 1 := by omega
          have hms : m * s ≤ m * (p ^ m - 1) := Nat.mul_le_mul_left _ hsle
          have hmuln : n * (p ^ n - 1) = n * p ^ n - n := by
            rw [Nat.mul_sub_left_distrib]
            simp
          have hmulm : m * (p ^ m - 1) = m * p ^ m - m := by
            rw [Nat.mul_sub_left_distrib]
            simp
          dsimp [a]
          simp [hri] at *
          omega
      · have hipos : 0 < i := by
          by_contra hi0
          have hiz : i = 0 := Nat.eq_zero_of_not_pos hi0
          apply hri
          simp [r, hiz]
        have hfaci : i.factorization p < n := by
          by_contra hfac
          have hdvd : p ^ n ∣ i :=
            (hp.pow_dvd_iff_le_factorization (Nat.ne_of_gt hipos)).2
              (Nat.le_of_not_gt hfac)
          exact hri (by simpa [r] using Nat.mod_eq_zero_of_dvd hdvd)
        have hchoosefac :
            ((p ^ a).choose i).factorization p = a - i.factorization p :=
          Nat.factorization_choose_prime_pow hp hiN (Nat.ne_of_gt hipos)
        apply (hp.pow_dvd_iff_le_factorization (Nat.choose_ne_zero hiN)).2
        rw [hchoosefac]
        have hrle : r ≤ p ^ n - 1 := by omega
        have hsle : s ≤ p ^ m - 1 := by omega
        have hnr : n * r ≤ n * (p ^ n - 1) := Nat.mul_le_mul_left _ hrle
        have hms : m * s ≤ m * (p ^ m - 1) := Nat.mul_le_mul_left _ hsle
        have hmuln : n * (p ^ n - 1) = n * p ^ n - n := by
          rw [Nat.mul_sub_left_distrib]
          simp
        have hmulm : m * (p ^ m - 1) = m * p ^ m - m := by
          rw [Nat.mul_sub_left_distrib]
          simp
        dsimp [a]
        omega
    have hxp : MvPolynomial.X (0 : Fin 2) ^ (p ^ n) ∈ A :=
      Algebra.subset_adjoin (by simp [A, helpWithPowersSubalgebra])
    have hyp : MvPolynomial.X (1 : Fin 2) ^ (p ^ m) ∈ A :=
      Algebra.subset_adjoin (by simp [A, helpWithPowersSubalgebra])
    have hxr : (p ^ n : MvPolynomial (Fin 2) ℤ) * MvPolynomial.X (0 : Fin 2) ∈ A :=
      Algebra.subset_adjoin (by simp [A, helpWithPowersSubalgebra])
    have hyr : (p ^ m : MvPolynomial (Fin 2) ℤ) * MvPolynomial.X (1 : Fin 2) ∈ A :=
      Algebra.subset_adjoin (by simp [A, helpWithPowersSubalgebra])
    have hxterm : (p ^ (n * r) : MvPolynomial (Fin 2) ℤ) *
        MvPolynomial.X (0 : Fin 2) ^ i ∈ A := by
      have hpow : (MvPolynomial.X (0 : Fin 2) : MvPolynomial (Fin 2) ℤ) ^ i =
          (MvPolynomial.X (0 : Fin 2) : MvPolynomial (Fin 2) ℤ) ^ r *
            (MvPolynomial.X (0 : Fin 2) : MvPolynomial (Fin 2) ℤ) ^
              (p ^ n * (i / p ^ n)) := by
        calc
          _ = (MvPolynomial.X (0 : Fin 2) : MvPolynomial (Fin 2) ℤ) ^
              (p ^ n * (i / p ^ n) + r) := congrArg _ hidecomp
          _ = _ := by rw [pow_add]; ac_rfl
      have hmem := A.mul_mem (A.pow_mem hxr r) (A.pow_mem hxp (i / p ^ n))
      convert hmem using 1
      rw [hpow]
      simp only [Nat.cast_pow, pow_mul]
      ring
    have hyterm : (p ^ (m * s) : MvPolynomial (Fin 2) ℤ) *
        MvPolynomial.X (1 : Fin 2) ^ j ∈ A := by
      have hpow : (MvPolynomial.X (1 : Fin 2) : MvPolynomial (Fin 2) ℤ) ^ j =
          (MvPolynomial.X (1 : Fin 2) : MvPolynomial (Fin 2) ℤ) ^ s *
            (MvPolynomial.X (1 : Fin 2) : MvPolynomial (Fin 2) ℤ) ^
              (p ^ m * (j / p ^ m)) := by
        calc
          _ = (MvPolynomial.X (1 : Fin 2) : MvPolynomial (Fin 2) ℤ) ^
              (p ^ m * (j / p ^ m) + s) := congrArg _ hjdecomp
          _ = _ := by rw [pow_add]; ac_rfl
      have hmem := A.mul_mem (A.pow_mem hyr s) (A.pow_mem hyp (j / p ^ m))
      convert hmem using 1
      rw [hpow]
      simp only [Nat.cast_pow, pow_mul]
      ring
    obtain ⟨d, hd⟩ := hchoose
    have hterm := A.mul_mem (A.algebraMap_mem d) (A.mul_mem hxterm hyterm)
    simpa [hd, Nat.cast_mul, Nat.cast_pow, pow_add, mul_assoc, mul_comm, mul_left_comm] using hterm
  · let A := helpWithPowersSubalgebra p n m
    have hx : (p ^ n : MvPolynomial (Fin 2) ℤ) * MvPolynomial.X (0 : Fin 2) ∈ A :=
      Algebra.subset_adjoin (by simp [A, helpWithPowersSubalgebra])
    have hy : (p ^ m : MvPolynomial (Fin 2) ℤ) * MvPolynomial.X (1 : Fin 2) ∈ A :=
      Algebra.subset_adjoin (by simp [A, helpWithPowersSubalgebra])
    have hpn : (p ^ (n * p ^ n + m * p ^ m + n + m) :
        MvPolynomial (Fin 2) ℤ) * MvPolynomial.X (0 : Fin 2) ∈ A := by
      have hna : n ≤ n * p ^ n + m * p ^ m + n + m := by omega
      rw [← Nat.add_sub_of_le hna, pow_add]
      simpa [mul_assoc, mul_comm, mul_left_comm] using
        A.mul_mem hx (A.algebraMap_mem (p ^ (n * p ^ n + m * p ^ m + n + m - n)))
    have hpm : (p ^ (n * p ^ n + m * p ^ m + n + m) :
        MvPolynomial (Fin 2) ℤ) * MvPolynomial.X (1 : Fin 2) ∈ A := by
      have hma : m ≤ n * p ^ n + m * p ^ m + n + m := by omega
      rw [← Nat.add_sub_of_le hma, pow_add]
      simpa [mul_assoc, mul_comm, mul_left_comm] using
        A.mul_mem hy (A.algebraMap_mem (p ^ (n * p ^ n + m * p ^ m + n + m - m)))
    rw [mul_add]
    exact A.add_mem hpn hpm

/-- The corrected field-extension classification for the `p`-power
    generation condition. -/
theorem pPowerFieldGenerated_iff
    {k k' : Type*} [Field k] [Field k'] [Algebra k k']
    (p : ℕ) (hp : p.Prime) :
    pPowerFieldGenerated (k := k) (k' := k') p ↔
      Function.Surjective (algebraMap k k') ∨
        ∃ _ : CharP k p, ∃ _ : CharP k' p, IsPurelyInseparable k k' := by
  classical
  let T : Set k' := {x : k' | ∃ n : ℕ, 0 < n ∧
    x ^ (p ^ n) ∈ (algebraMap k k').range ∧
      (p ^ n : k') * x ∈ (algebraMap k k').range}
  change IntermediateField.adjoin k T = ⊤ ↔ _
  constructor
  · intro hgen
    by_cases hsurj : Function.Surjective (algebraMap k k')
    · exact Or.inl hsurj
    · have hchar' : CharP k' p := by
        apply (CharP.charP_iff_prime_eq_zero hp).2
        by_contra hp0
        have hT : T ⊆ (⊥ : IntermediateField k k') := by
          intro x hx
          obtain ⟨n, hn, _hxpow, ⟨y, hy⟩⟩ := hx
          change ∃ z : k, algebraMap k k' z = x
          refine ⟨(p ^ n : k)⁻¹ * y, ?_⟩
          rw [map_mul, map_inv₀, map_pow, map_natCast, hy]
          field_simp
        have hle : IntermediateField.adjoin k T ≤ (⊥ : IntermediateField k k') :=
          IntermediateField.adjoin_le_iff.mpr hT
        have htop : (⊤ : IntermediateField k k') ≤ (⊥ : IntermediateField k k') := by
          rw [← hgen]
          exact hle
        apply hsurj
        intro x
        have hx : x ∈ (⊥ : IntermediateField k k') := htop trivial
        exact hx
      have hchar : CharP k p := (Algebra.charP_iff k k' p).mpr hchar'
      let : CharP k p := hchar
      let : ExpChar k p := ExpChar.prime hp
      have hpureAdjoin : IsPurelyInseparable k (IntermediateField.adjoin k T) :=
        (IntermediateField.isPurelyInseparable_adjoin_iff_pow_mem k k' p).2
          (fun x hx ↦ by
            obtain ⟨n, hn, ⟨y, hy⟩, _hxmul⟩ := hx
            exact ⟨n, y, hy⟩)
      have hpureTop : IsPurelyInseparable k (⊤ : IntermediateField k k') := by
        rw [← hgen]
        exact hpureAdjoin
      let : IsPurelyInseparable k (⊤ : IntermediateField k k') := hpureTop
      exact Or.inr ⟨hchar, hchar', IntermediateField.topEquiv.isPurelyInseparable⟩
  · rintro (hsurj | ⟨hk, hk', hpure⟩)
    · apply top_unique
      intro x _
      obtain ⟨y, hy⟩ := hsurj (x ^ p)
      obtain ⟨z, hz⟩ := hsurj ((p : k') * x)
      exact IntermediateField.subset_adjoin k _ ⟨1, by simp, ⟨y, by simpa using hy⟩,
        ⟨z, by simpa using hz⟩⟩
    · let : CharP k p := hk
      let : CharP k' p := hk'
      let : ExpChar k p := ExpChar.prime hp
      let : IsPurelyInseparable k k' := hpure
      apply top_unique
      intro x _
      obtain ⟨n, y, hy⟩ := IsPurelyInseparable.pow_mem k p x
      by_cases hn : 0 < n
      · have hp0 : (p : k') = 0 := CharP.cast_eq_zero k' p
        have hpn : (p : k') ^ n = 0 := by rw [hp0, zero_pow hn.ne']
        exact IntermediateField.subset_adjoin k _ ⟨n, hn, ⟨y, hy⟩,
          ⟨0, by rw [hpn, zero_mul]; simp⟩⟩
      · have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
        subst n
        exact IntermediateField.subset_adjoin k _ ⟨1, by simp, ⟨y ^ p, by
          rw [map_pow, hy]
          simp⟩, ⟨0, by simp⟩⟩

/-- The `p`-power ring-map criterion, including its residue-field statement
    and stability under arbitrary base change. -/
theorem pPowerGenerated_locallyNilpotentKernel
    {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (p : ℕ)
    (hp : p.Prime) (hgen : pPowerGenerated f p) (hker : locallyNilpotentKernel f) :
    IsHomeomorph (PrimeSpectrum.comap f) ∧ pResidueFieldProperties f p ∧
      ∀ (R' : Type*) [CommRing R'] (g : R →+* R'),
        pPowerGenerated (baseChangeRingMap f g) p ∧
          locallyNilpotentKernel (baseChangeRingMap f g) := by
  letI : Algebra R S := f.toAlgebra
  let T : Set S := {x : S | ∃ n : ℕ, 0 < n ∧
    x ^ (p ^ n) ∈ f.range ∧ (p ^ n : S) * x ∈ f.range}
  have hgen' : Algebra.adjoin R T = ⊤ := by
    simpa [T, pPowerGenerated, generatedBy] using hgen
  let B : Subalgebra R S :=
    { carrier := T
      zero_mem' := by
        refine ⟨1, by simp, ?_, ?_⟩
        · exact ⟨0, by simp [hp.ne_zero]⟩
        · exact ⟨0, by simp [hp.ne_zero]⟩
      one_mem' := by
        refine ⟨1, by simp, ?_, ?_⟩
        · exact ⟨1, by simp⟩
        · exact ⟨p, by simp⟩
      add_mem' := by
        rintro x y ⟨n, hn, hxn, hnx⟩ ⟨m, hm, hym, hmy⟩
        obtain ⟨a, ha1, ha2⟩ := exists_helpWithPowers_exponent p n m hp hn hm
        let C : Subalgebra ℤ S :=
          { carrier := f.range
            zero_mem' := ⟨0, by simp⟩
            one_mem' := ⟨1, by simp⟩
            add_mem' := by
              rintro _ _ ⟨u, rfl⟩ ⟨v, rfl⟩
              exact ⟨u + v, by simp⟩
            mul_mem' := by
              rintro _ _ ⟨u, rfl⟩ ⟨v, rfl⟩
              exact ⟨u * v, by simp⟩
            algebraMap_mem' := by
              intro z
              exact ⟨z, by simp⟩ }
        let e : MvPolynomial (Fin 2) ℤ →ₐ[ℤ] S :=
          { MvPolynomial.eval₂Hom (Int.castRingHom S)
              (fun i : Fin 2 => if i = 0 then x else y) with
            commutes' := by intro z; simp }
        have he : ∀ z ∈ helpWithPowersSubalgebra p n m, e z ∈ C := by
          intro z hz
          have hle : helpWithPowersSubalgebra p n m ≤ C.comap e :=
            Algebra.adjoin_le (by
              rintro z (rfl | rfl | rfl | rfl)
              · simpa [e, C] using hxn
              · simpa [e, C] using hnx
              · simpa [e, C] using hym
              · simpa [e, C] using hmy)
          exact hle hz
        refine ⟨a + 1, by omega, ?_, ?_⟩
        · have hz := C.pow_mem (he _ ha1) p
          have hz' : ((x + y) ^ (p ^ a)) ^ p ∈ f.range := by
            simpa [e, C] using hz
          change (x + y) ^ (p ^ (a + 1)) ∈ f.range
          simpa [pow_succ, pow_mul] using hz'
        · have hz := C.mul_mem (C.algebraMap_mem p) (he _ ha2)
          simpa [e, C, pow_succ, mul_comm, mul_left_comm, mul_assoc] using hz
      mul_mem' := by
        rintro x y ⟨n, hn, hxn, hnx⟩ ⟨m, hm, hym, hmy⟩
        refine ⟨n + m, by omega, ?_, ?_⟩
        · obtain ⟨u, hu⟩ := hxn
          obtain ⟨v, hv⟩ := hym
          refine ⟨u ^ (p ^ m) * v ^ (p ^ n), ?_⟩
          simp only [map_mul, map_pow, hu, hv]
          rw [← pow_mul, ← pow_mul, pow_add, mul_pow]
          simp [Nat.mul_comm (p ^ m) (p ^ n)]
        · obtain ⟨u, hu⟩ := hnx
          obtain ⟨v, hv⟩ := hmy
          refine ⟨u * v, ?_⟩
          rw [map_mul, hu, hv]
          simp [pow_add, mul_comm, mul_left_comm, mul_assoc]
      algebraMap_mem' := by
        intro r
        refine ⟨1, by simp, ?_, ?_⟩
        · exact ⟨r ^ (p ^ 1), by simp [RingHom.algebraMap_toAlgebra]⟩
        · exact ⟨(p ^ 1 : R) * r, by simp [RingHom.algebraMap_toAlgebra]⟩ }
  have hBT : B = ⊤ := by
    apply top_unique
    rw [← hgen']
    exact Algebra.adjoin_le (by intro x hx; exact hx)
  have hpower : ∀ x : S, ∃ n : ℕ, 0 < n ∧ x ^ (p ^ n) ∈ f.range ∧
      (p ^ n : S) * x ∈ f.range := by
    intro x
    have hx : x ∈ B := by rw [hBT]; trivial
    exact hx
  have hpower' : powerSurjective f := by
    intro x
    obtain ⟨n, hn, ⟨r, hr⟩, _⟩ := hpower x
    exact ⟨p ^ n, pow_pos hp.pos n, r, hr⟩
  have hmain := powerSurjective_locallyNilpotentKernel f hpower' hker
  refine ⟨hmain.1, ?_, ?_⟩
  · intro q
    let K := (PrimeSpectrum.comap f q).asIdeal.ResidueField
    let L := q.asIdeal.ResidueField
    letI : Algebra K L := (residueFieldMap f q).toAlgebra
    have hgenq : pPowerFieldGenerated (k := K) (k' := L) p := by
      change IntermediateField.adjoin K
        {z : L | ∃ n : ℕ, 0 < n ∧ z ^ (p ^ n) ∈
          (algebraMap K L).range ∧ (p ^ n : L) * z ∈ (algebraMap K L).range} = ⊤
      apply top_unique
      intro z hz
      obtain ⟨aa, bb, hbb, hzdiv⟩ := IsFractionRing.div_surjective (S ⧸ q.asIdeal) z
      obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective aa
      obtain ⟨w, hw⟩ := Ideal.Quotient.mk_surjective bb
      obtain ⟨n, hn, ⟨r, hr⟩, ⟨r₁, hr₁⟩⟩ := hpower y
      obtain ⟨m, hm, ⟨s, hs⟩, ⟨s₁, hs₁⟩⟩ := hpower w
      have hY : residueFieldMap f q (algebraMap R K r) =
          algebraMap S L y ^ (p ^ n) := by
        calc
          residueFieldMap f q (algebraMap R K r) =
              algebraMap S L (f r) := by
                simpa [K, L, residueFieldMap] using
                  (Ideal.ResidueField.map_algebraMap
                    (PrimeSpectrum.comap f q).asIdeal q.asIdeal f rfl r)
          _ = algebraMap S L (y ^ (p ^ n)) := by rw [hr]
          _ = algebraMap S L y ^ (p ^ n) := by rw [map_pow]
      have hW : residueFieldMap f q (algebraMap R K s) =
          algebraMap S L w ^ (p ^ m) := by
        calc
          residueFieldMap f q (algebraMap R K s) =
              algebraMap S L (f s) := by
                simpa [K, L, residueFieldMap] using
                  (Ideal.ResidueField.map_algebraMap
                    (PrimeSpectrum.comap f q).asIdeal q.asIdeal f rfl s)
          _ = algebraMap S L (w ^ (p ^ m)) := by rw [hs]
          _ = algebraMap S L w ^ (p ^ m) := by rw [map_pow]
      have hYr : residueFieldMap f q (algebraMap R K r₁) =
          (p ^ n : L) * algebraMap S L y := by
        calc
          residueFieldMap f q (algebraMap R K r₁) =
              algebraMap S L (f r₁) := by
                simpa [K, L, residueFieldMap] using
                  (Ideal.ResidueField.map_algebraMap
                    (PrimeSpectrum.comap f q).asIdeal q.asIdeal f rfl r₁)
          _ = algebraMap S L ((p ^ n : S) * y) := by rw [hr₁]
          _ = (p ^ n : L) * algebraMap S L y := by simp [map_mul, map_natCast]
      have hWr : residueFieldMap f q (algebraMap R K s₁) =
          (p ^ m : L) * algebraMap S L w := by
        calc
          residueFieldMap f q (algebraMap R K s₁) =
              algebraMap S L (f s₁) := by
                simpa [K, L, residueFieldMap] using
                  (Ideal.ResidueField.map_algebraMap
                    (PrimeSpectrum.comap f q).asIdeal q.asIdeal f rfl s₁)
          _ = algebraMap S L ((p ^ m : S) * w) := by rw [hs₁]
          _ = (p ^ m : L) * algebraMap S L w := by simp [map_mul, map_natCast]
      have hz' : algebraMap S L y / algebraMap S L w = z := by
        simpa [K, L, Ideal.algebraMap_quotient_residueField_mk, ← hy, ← hw] using hzdiv
      have hw0 : algebraMap S L w ≠ 0 := by
        have hq0 : Ideal.Quotient.mk q.asIdeal w ≠ 0 := by
          intro hzero
          have hbb0 : bb ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hbb
          apply hbb0
          rw [← hw]
          exact hzero
        intro hzero
        apply hq0
        apply (Ideal.injective_algebraMap_quotient_residueField)
        simpa only [Ideal.algebraMap_quotient_residueField_mk, map_zero] using hzero
      refine IntermediateField.subset_adjoin K _ ⟨n + m, by omega, ?_, ?_⟩
      · refine ⟨(algebraMap R K r) ^ (p ^ m) /
          (algebraMap R K s) ^ (p ^ n), ?_⟩
        calc
          residueFieldMap f q
              ((algebraMap R K r) ^ (p ^ m) /
                (algebraMap R K s) ^ (p ^ n)) =
              (algebraMap S L y ^ (p ^ n)) ^ (p ^ m) /
                (algebraMap S L w ^ (p ^ m)) ^ (p ^ n) := by
                  rw [map_div₀, map_pow, map_pow, hY, hW]
          _ = (algebraMap S L y / algebraMap S L w) ^
                (p ^ n * p ^ m) := by
                  rw [← pow_mul, ← pow_mul, div_pow]
                  rw [Nat.mul_comm (p ^ m) (p ^ n)]
          _ = z ^ (p ^ (n + m)) := by rw [hz', pow_add]
      · by_cases hpL : (p : L) = 0
        · refine ⟨0, ?_⟩
          have hnm : 0 < n + m := by omega
          have hpow : (p : L) ^ (n + m) = 0 := by
            rw [hpL, zero_pow hnm.ne']
          rw [map_zero, hpow, zero_mul]
        · refine ⟨(algebraMap R K r₁) * (p ^ m : K) ^ 2 /
              algebraMap R K s₁, ?_⟩
          change residueFieldMap f q
              ((algebraMap R K r₁) * (p ^ m : K) ^ 2 /
                algebraMap R K s₁) = (p ^ (n + m) : L) * z
          rw [map_div₀, map_mul, map_pow, hYr, hWr, map_pow, map_natCast]
          have hyz : algebraMap S L y = z * algebraMap S L w :=
            (div_eq_iff hw0).mp hz'
          field_simp [hpL, hw0]
          rw [hyz]
          rw [pow_add]
          ring
    exact ⟨hgenq, (pPowerFieldGenerated_iff p hp).mp hgenq⟩
  · intro R' _ g
    letI : Algebra R R' := g.toAlgebra
    let bc : R' →+* S ⊗[R] R' := baseChangeRingMap f g
    letI : Algebra R' (S ⊗[R] R') := bc.toAlgebra
    let T' : Set (S ⊗[R] R') := {x : S ⊗[R] R' | ∃ n : ℕ, 0 < n ∧
      x ^ (p ^ n) ∈ bc.range ∧ (p ^ n : S ⊗[R] R') * x ∈ bc.range}
    let D : Subalgebra R' (S ⊗[R] R') :=
      { carrier := T'
        zero_mem' := by
          refine ⟨1, by simp, ?_, ?_⟩
          · exact ⟨0, by simp [hp.ne_zero]⟩
          · exact ⟨0, by simp [hp.ne_zero]⟩
        one_mem' := by
          refine ⟨1, by simp, ?_, ?_⟩
          · exact ⟨1, by simp⟩
          · exact ⟨p, by simp⟩
        add_mem' := by
          rintro x y ⟨n, hn, hxn, hnx⟩ ⟨m, hm, hym, hmy⟩
          obtain ⟨a, ha1, ha2⟩ := exists_helpWithPowers_exponent p n m hp hn hm
          let C : Subalgebra ℤ (S ⊗[R] R') :=
            { carrier := bc.range
              zero_mem' := ⟨0, by simp⟩
              one_mem' := ⟨1, by simp⟩
              add_mem' := by
                rintro _ _ ⟨u, rfl⟩ ⟨v, rfl⟩
                exact ⟨u + v, by simp⟩
              mul_mem' := by
                rintro _ _ ⟨u, rfl⟩ ⟨v, rfl⟩
                exact ⟨u * v, by simp⟩
              algebraMap_mem' := by
                intro z
                exact ⟨z, by simp⟩ }
          let e : MvPolynomial (Fin 2) ℤ →ₐ[ℤ] (S ⊗[R] R') :=
            { MvPolynomial.eval₂Hom (Int.castRingHom (S ⊗[R] R'))
                (fun i : Fin 2 => if i = 0 then x else y) with
              commutes' := by intro z; simp }
          have he : ∀ z ∈ helpWithPowersSubalgebra p n m, e z ∈ C := by
            intro z hz
            have hle : helpWithPowersSubalgebra p n m ≤ C.comap e :=
              Algebra.adjoin_le (by
                rintro z (rfl | rfl | rfl | rfl)
                · simpa [e, C] using hxn
                · simpa [e, C] using hnx
                · simpa [e, C] using hym
                · simpa [e, C] using hmy)
            exact hle hz
          refine ⟨a + 1, by omega, ?_, ?_⟩
          · have hz := C.pow_mem (he _ ha1) p
            have hz' : ((x + y) ^ (p ^ a)) ^ p ∈ bc.range := by
              simpa [e, C] using hz
            change (x + y) ^ (p ^ (a + 1)) ∈ bc.range
            simpa [pow_succ, pow_mul] using hz'
          · have hz := C.mul_mem (C.algebraMap_mem p) (he _ ha2)
            simpa [e, C, pow_succ, mul_comm, mul_left_comm, mul_assoc] using hz
        mul_mem' := by
          rintro x y ⟨n, hn, hxn, hnx⟩ ⟨m, hm, hym, hmy⟩
          refine ⟨n + m, by omega, ?_, ?_⟩
          · obtain ⟨u, hu⟩ := hxn
            obtain ⟨v, hv⟩ := hym
            refine ⟨u ^ (p ^ m) * v ^ (p ^ n), ?_⟩
            simp only [map_mul, map_pow, hu, hv]
            rw [← pow_mul, ← pow_mul, pow_add, mul_pow]
            simp [Nat.mul_comm (p ^ m) (p ^ n)]
          · obtain ⟨u, hu⟩ := hnx
            obtain ⟨v, hv⟩ := hmy
            refine ⟨u * v, ?_⟩
            rw [map_mul, hu, hv]
            simp [pow_add, mul_comm, mul_left_comm, mul_assoc]
        algebraMap_mem' := by
          intro r
          refine ⟨1, by simp, ?_, ?_⟩
          · exact ⟨r ^ (p ^ 1), by simp [RingHom.algebraMap_toAlgebra]⟩
          · exact ⟨(p ^ 1 : R') * r, by simp [RingHom.algebraMap_toAlgebra]⟩ }
    let a : S →+* S ⊗[R] R' := baseChangeAlgebraMap f g
    have hcomp : a.comp f = bc.comp g := by
      change Algebra.TensorProduct.includeLeftRingHom.comp f =
        Algebra.TensorProduct.includeRight.toRingHom.comp g
      exact Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap
    have hleft : ∀ s : S, a s ∈ D := by
      intro s
      have hs : s ∈ Algebra.adjoin R T := by rw [hgen']; trivial
      refine Algebra.adjoin_induction (p := fun x _ => a x ∈ D) ?_ ?_ ?_ ?_ hs
      · intro x hx
        rcases hx with ⟨n, hn, hxn, hnx⟩
        refine ⟨n, hn, ?_, ?_⟩
        · obtain ⟨r, hr⟩ := hxn
          refine ⟨g r, ?_⟩
          calc
            bc (g r) = a (f r) := by
              exact congrArg (fun h : R →+* S ⊗[R] R' => h r) hcomp.symm
            _ = a (x ^ (p ^ n)) := by rw [hr]
            _ = a x ^ (p ^ n) := by rw [map_pow]
        · obtain ⟨r, hr⟩ := hnx
          refine ⟨g r, ?_⟩
          calc
            bc (g r) = a (f r) := by
              exact congrArg (fun h : R →+* S ⊗[R] R' => h r) hcomp.symm
            _ = a ((p ^ n : S) * x) := by rw [hr]
            _ = (p ^ n : S ⊗[R] R') * a x := by
              simp [map_mul, map_natCast]
      · intro r
        refine ⟨1, by simp, ?_, ?_⟩
        · exact ⟨(g r) ^ p, by
            have hcr : bc (g r) = a (algebraMap R S r) := by
              exact congrArg (fun h : R →+* S ⊗[R] R' => h r) hcomp.symm
            rw [map_pow, hcr]
            simp⟩
        · exact ⟨(p : R') * g r, by
            have hcr : bc (g r) = a (algebraMap R S r) := by
              exact congrArg (fun h : R →+* S ⊗[R] R' => h r) hcomp.symm
            rw [map_mul, hcr]
            simp⟩
      · intro x y hx hy hxp hyp
        simpa only [map_add] using D.add_mem hxp hyp
      · intro x y hx hy hxp hyp
        simpa only [map_mul] using D.mul_mem hxp hyp
    have hD : D = ⊤ := by
      apply top_unique
      intro z _
      refine TensorProduct.induction_on z ?_ ?_ ?_
      · exact D.zero_mem
      · intro s r'
        have hbc : bc r' = (1 : S) ⊗ₜ[R] r' := by
          simp [bc, baseChangeRingMap, RingHom.algebraMap_toAlgebra]
        have hmul := D.mul_mem (hleft s) (D.algebraMap_mem r')
        change a s * bc r' ∈ D at hmul
        rw [hbc] at hmul
        have ha : a s = s ⊗ₜ[R] (1 : R') := by
          simp [a, baseChangeAlgebraMap]
        rw [ha] at hmul
        simpa [Algebra.TensorProduct.tmul_mul_tmul] using hmul
      · intro x y hx hy
        exact D.add_mem hx hy
    have hpgen : pPowerGenerated bc p := by
      change Algebra.adjoin R' T' = ⊤
      apply top_unique
      intro z hz
      have hzD : z ∈ D := by rw [hD]; exact hz
      exact Algebra.subset_adjoin hzD
    exact ⟨hpgen, by sorry⟩

/-- Injectivity on spectra and purely inseparable residue fields are stable
    under arbitrary base change. -/
theorem radicial_baseChange
    {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (hinj : Function.Injective (PrimeSpectrum.comap f))
    (hres : residueFieldExtensionsPurelyInseparable f) :
    ∀ (R' : Type*) [CommRing R'] (g : R →+* R'),
      Function.Injective (PrimeSpectrum.comap (baseChangeRingMap f g)) ∧
        residueFieldExtensionsPurelyInseparable (baseChangeRingMap f g) := by
  sorry

/-- An integral radicial map is a closed embedding on spectra, and its three
    defining properties survive arbitrary base change. -/
theorem integral_radicial_baseChange
    {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (hint : f.IsIntegral)
    (hinj : Function.Injective (PrimeSpectrum.comap f))
    (hres : residueFieldExtensionsPurelyInseparable f) :
    IsClosedEmbedding (PrimeSpectrum.comap f) ∧
      ∀ (R' : Type*) [CommRing R'] (g : R →+* R'),
        (baseChangeRingMap f g).IsIntegral ∧
          Function.Injective (PrimeSpectrum.comap (baseChangeRingMap f g)) ∧
            residueFieldExtensionsPurelyInseparable (baseChangeRingMap f g) := by
  sorry

/-- An integral radicial map that is bijective on spectra is a homeomorphism,
    and its three defining properties survive arbitrary base change. -/
theorem integral_radicial_bijective_baseChange
    {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (hint : f.IsIntegral)
    (hbij : Function.Bijective (PrimeSpectrum.comap f))
    (hres : residueFieldExtensionsPurelyInseparable f) :
    IsHomeomorph (PrimeSpectrum.comap f) ∧
      ∀ (R' : Type*) [CommRing R'] (g : R →+* R'),
        (baseChangeRingMap f g).IsIntegral ∧
          Function.Injective (PrimeSpectrum.comap (baseChangeRingMap f g)) ∧
            residueFieldExtensionsPurelyInseparable (baseChangeRingMap f g) := by
  sorry

/-- The final universally bijective criterion: a locally nilpotent kernel and
    polynomial powers of algebra generators imply a universal homeomorphism
    with purely inseparable residue fields. -/
theorem universallyBijective
    {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (hker : locallyNilpotentKernel f)
    (hgen : universallyBijectiveGenerated f) :
    IsHomeomorph (PrimeSpectrum.comap f) ∧
      residueFieldExtensionsPurelyInseparable f ∧
        ∀ (R' : Type*) [CommRing R'] (g : R →+* R'),
          locallyNilpotentKernel (baseChangeRingMap f g) ∧
            universallyBijectiveGenerated (baseChangeRingMap f g) := by
  sorry

end

end Formalization.Books.Algebra.Unit46
