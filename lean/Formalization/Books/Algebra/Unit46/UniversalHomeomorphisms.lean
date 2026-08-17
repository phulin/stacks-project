import Formalization.Books.Algebra.Unit03.BasicNotions
import Formalization.Books.Algebra.Unit14.BaseChange
import Formalization.Books.Algebra.Unit36.FiniteIntegralRingExtensions
import Mathlib.Algebra.Algebra.ZMod
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.FieldTheory.PurelyInseparable.Basic
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
  sorry

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
  sorry

/-- The powers criterion gives a homeomorphism on spectra and the source's
    powers-field description of all residue-field extensions. -/
theorem powerSurjective_locallyNilpotentKernel
    {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (hpower : powerSurjective f) (hker : locallyNilpotentKernel f) :
    IsHomeomorph (PrimeSpectrum.comap f) ∧ residueFieldPowerProperties f := by
  sorry

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
  sorry

/-- The corrected field-extension classification for the `p`-power
    generation condition. -/
theorem pPowerFieldGenerated_iff
    {k k' : Type*} [Field k] [Field k'] [Algebra k k']
    (p : ℕ) (hp : p.Prime) :
    pPowerFieldGenerated (k := k) (k' := k') p ↔
      Function.Surjective (algebraMap k k') ∨
        ∃ hk : CharP k p, ∃ hk' : CharP k' p, IsPurelyInseparable k k' := by
  sorry

/-- The `p`-power ring-map criterion, including its residue-field statement
    and stability under arbitrary base change. -/
theorem pPowerGenerated_locallyNilpotentKernel
    {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (p : ℕ)
    (hp : p.Prime) (hgen : pPowerGenerated f p) (hker : locallyNilpotentKernel f) :
    IsHomeomorph (PrimeSpectrum.comap f) ∧ pResidueFieldProperties f p ∧
      ∀ (R' : Type*) [CommRing R'] (g : R →+* R'),
        pPowerGenerated (baseChangeRingMap f g) p ∧
          locallyNilpotentKernel (baseChangeRingMap f g) := by
  sorry

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
