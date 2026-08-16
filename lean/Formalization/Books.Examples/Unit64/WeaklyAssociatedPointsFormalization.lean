import Mathlib.Algebra.Ring.Subring.Defs
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.AlgebraicGeometry.Restrict
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Topology.Compactification.OnePoint.Basic
import Mathlib.Topology.Compactification.StoneCech
import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Topology.LocallyConstant.Algebra

/-!
# Examples, Chapter 64: Weakly associated points and scheme theoretic density

This file records the two examples in the source section.  Mathlib's
`IsAssociatedPrime` is the canonical algebraic API for weakly associated
primes, and `IsSchemeTheoreticallyDominant` is the canonical API for
scheme-theoretic density.  The definitions follow the source order so that
the displayed rings and open subsets remain available to the theorem
interfaces below.
-/

noncomputable section

open Filter TopologicalSpace
open AlgebraicGeometry

universe u v

namespace Formalization.«Books.Examples».Unit64

/-! ## The weak-association interfaces used by the source -/

/-- The textbook's weakly associated prime, exposed as Mathlib's canonical API. -/
abbrev IsWeaklyAssociatedPrime {R : Type*} [CommSemiring R]
    (p : Ideal R) (M : Type*) [AddCommMonoid M] [Module R M] : Prop :=
  IsAssociatedPrime p M

/-- The set of weakly associated primes, exposed as Mathlib's canonical set. -/
abbrev weaklyAssociatedPrimes (R M : Type*) [CommSemiring R]
    [AddCommMonoid M] [Module R M] : Set (Ideal R) :=
  associatedPrimes R M

/-- A scheme point is weakly associated to its structure sheaf when its stalk
maximal ideal is weakly associated to the stalk as a module over itself. -/
def IsWeaklyAssociatedPoint (X : Scheme) (x : X) : Prop :=
  IsWeaklyAssociatedPrime
    (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x)

/-! ## The first ring example -/

/-- Variables for `z`, the `xᵢ`, and the `yᵢ` in the first example. -/
abbrev firstExampleVariable := Option (ℕ ⊕ ℕ)

/-- The polynomial ring `k[z, xᵢ, yᵢ]`. -/
abbrev firstExamplePolynomialRing (k : Type u) [Field k] :=
  MvPolynomial (firstExampleVariable) k

/-- The polynomial variable `z`. -/
def firstExampleZPolynomial (k : Type u) [Field k] :
    firstExamplePolynomialRing k :=
  MvPolynomial.X none

/-- The polynomial variable `xᵢ`. -/
def firstExampleXPolynomial (k : Type u) [Field k] (i : ℕ) :
    firstExamplePolynomialRing k :=
  MvPolynomial.X (some (.inl i))

/-- The polynomial variable `yᵢ`. -/
def firstExampleYPolynomial (k : Type u) [Field k] (i : ℕ) :
    firstExamplePolynomialRing k :=
  MvPolynomial.X (some (.inr i))

/-- The displayed relations `z²` and `z xᵢ yᵢ`. -/
def firstExampleRelationGenerators (k : Type u) [Field k] :
    Set (firstExamplePolynomialRing k) :=
  Set.insert (firstExampleZPolynomial k ^ 2)
    (Set.range fun i : ℕ =>
      firstExampleZPolynomial k * firstExampleXPolynomial k i *
        firstExampleYPolynomial k i)

/-- The relation ideal `(z², z xᵢ yᵢ)`. -/
def firstExampleRelationIdeal (k : Type u) [Field k] :
    Ideal (firstExamplePolynomialRing k) :=
  Ideal.span (firstExampleRelationGenerators k)

/-- The ring `R = k[z, xᵢ, yᵢ]/(z², z xᵢ yᵢ)`. -/
abbrev firstExampleRing (k : Type u) [Field k] :=
  firstExamplePolynomialRing k ⧸ firstExampleRelationIdeal k

/-- The affine scheme `S = Spec(R)` in the first example. -/
abbrev firstExampleScheme (k : Type u) [Field k] : Scheme :=
  Spec (.of (firstExampleRing k))

/-- The images of the displayed polynomial variables in `R`. -/
def firstExampleZ (k : Type u) [Field k] : firstExampleRing k :=
  Ideal.Quotient.mk (firstExampleRelationIdeal k) (firstExampleZPolynomial k)

def firstExampleX (k : Type u) [Field k] (i : ℕ) : firstExampleRing k :=
  Ideal.Quotient.mk (firstExampleRelationIdeal k) (firstExampleXPolynomial k i)

def firstExampleY (k : Type u) [Field k] (i : ℕ) : firstExampleRing k :=
  Ideal.Quotient.mk (firstExampleRelationIdeal k) (firstExampleYPolynomial k i)

/-- The polynomial subring `R₀ = k[xᵢ, yᵢ]`. -/
abbrev firstExampleR0 (k : Type u) [Field k] := MvPolynomial (ℕ ⊕ ℕ) k

def firstExampleR0X (k : Type u) [Field k] (i : ℕ) : firstExampleR0 k :=
  MvPolynomial.X (.inl i)

def firstExampleR0Y (k : Type u) [Field k] (i : ℕ) : firstExampleR0 k :=
  MvPolynomial.X (.inr i)

/-- The ideal `(xᵢ yᵢ)` defining the square-zero coefficient module. -/
def firstExampleM0Ideal (k : Type u) [Field k] : Ideal (firstExampleR0 k) :=
  Ideal.span (Set.range fun i : ℕ => firstExampleR0X k i * firstExampleR0Y k i)

/-- The module `M₀ ≅ R₀/(xᵢ yᵢ)`. -/
abbrev firstExampleM0 (k : Type u) [Field k] :=
  firstExampleR0 k ⧸ firstExampleM0Ideal k

/-- The map of polynomial rings sending `xᵢ` and `yᵢ` to their copies in `R`. -/
def firstExampleR0ToPolynomial (k : Type u) [Field k] :
    firstExampleR0 k →+* firstExamplePolynomialRing k :=
  MvPolynomial.eval₂Hom (MvPolynomial.C : k →+* firstExamplePolynomialRing k)
    (fun v : ℕ ⊕ ℕ =>
    MvPolynomial.X (some v))

/-- The inclusion of `R₀` into the quotient ring `R`. -/
def firstExampleR0ToR (k : Type u) [Field k] :
    firstExampleR0 k →+* firstExampleRing k :=
  (Ideal.Quotient.mk (firstExampleRelationIdeal k)).comp
    (firstExampleR0ToPolynomial k)

/-- The `R₀`-algebra structure on `R` induced by the preceding map. -/
@[instance_reducible] noncomputable def firstExampleR0Algebra (k : Type u) [Field k] :
    Algebra (firstExampleR0 k) (firstExampleRing k) :=
  RingHom.toAlgebra (firstExampleR0ToR k)

noncomputable instance firstExampleR0Algebra_inst (k : Type u) [Field k] :
    Algebra (firstExampleR0 k) (firstExampleRing k) :=
  firstExampleR0Algebra k

/-- The ideal generated by `z`, which is the square-zero summand in `R`. -/
def firstExampleSquareZeroIdeal (k : Type u) [Field k] : Ideal (firstExampleRing k) :=
  Ideal.span ({firstExampleZ k} : Set (firstExampleRing k))

/-- The square-zero assertion for the ideal generated by `z`. -/
theorem firstExampleSquareZeroIdeal_sq_eq_bot (k : Type u) [Field k] :
    firstExampleSquareZeroIdeal k * firstExampleSquareZeroIdeal k = ⊥ := by
  sorry

/-- The square-zero ideal viewed as an `R₀`-submodule. -/
abbrev firstExampleSquareZeroIdealOverR0 (k : Type u) [Field k] :=
  (firstExampleSquareZeroIdeal k).restrictScalars (firstExampleR0 k)

/-- The source's module identification `M₀ ≅ R₀/(xᵢ yᵢ)`. -/
theorem firstExampleSquareZeroIdeal_equiv_M0 (k : Type u) [Field k] :
    Nonempty (firstExampleSquareZeroIdealOverR0 k ≃ₗ[firstExampleR0 k]
      firstExampleM0 k) := by
  sorry

/-- The direct-sum decomposition `R = R₀ ⊕ M₀` as an `R₀`-module. -/
theorem firstExampleRing_decomposition (k : Type u) [Field k] :
    Nonempty (firstExampleRing k ≃ₗ[firstExampleR0 k]
      firstExampleR0 k × firstExampleM0 k) := by
  sorry

/-! ## The weakly associated prime in the first example -/

/-- The ideal `(z, xᵢ)` in `R`. -/
def firstExamplePrime (k : Type u) [Field k] : Ideal (firstExampleRing k) :=
  Ideal.span <| Set.insert (firstExampleZ k) (Set.range (firstExampleX k))

/-- The displayed ideal `(z, xᵢ)` is prime. -/
theorem firstExamplePrime_isPrime (k : Type u) [Field k] :
    (firstExamplePrime k).IsPrime := by
  sorry

noncomputable instance firstExamplePrime_isPrime_inst (k : Type u) [Field k] :
    (firstExamplePrime k).IsPrime :=
  firstExamplePrime_isPrime k

/-- The corresponding point of `Spec(R)`. -/
def firstExamplePrimePoint (k : Type u) [Field k] :
    PrimeSpectrum (firstExampleRing k) :=
  ⟨firstExamplePrime k, firstExamplePrime_isPrime k⟩

/-- The prime `(z, xᵢ)` is weakly associated to `R`. -/
theorem firstExamplePrime_isWeaklyAssociated (k : Type u) [Field k] :
    IsWeaklyAssociatedPrime (firstExamplePrime k) (firstExampleRing k) := by
  sorry

/-- The localization of `R` at the displayed prime. -/
abbrev firstExamplePrimeLocalization (k : Type u) [Field k] :=
  Localization.AtPrime (firstExamplePrime k)

/-- The element `z` in the localized ring `Rₚ`. -/
def firstExampleLocalizedZ (k : Type u) [Field k] :
    firstExamplePrimeLocalization k :=
  algebraMap (firstExampleRing k) (firstExamplePrimeLocalization k)
    (firstExampleZ k)

/-- The element `z` remains nonzero after localizing at `p`. -/
theorem firstExampleLocalizedZ_ne_zero (k : Type u) [Field k] :
    firstExampleLocalizedZ k ≠ 0 := by
  sorry

/-- Every element of `p` annihilates the localized element `z`. -/
theorem firstExampleLocalizedZ_annihilated_by_prime (k : Type u) [Field k] :
    ∀ a : firstExampleRing k, a ∈ firstExamplePrime k →
      algebraMap (firstExampleRing k) (firstExamplePrimeLocalization k) a *
          firstExampleLocalizedZ k = 0 := by
  sorry

/-! ## The open union and the localization calculation -/

/-- The open `U = ⋃ D(xᵢ) ⊆ Spec(R)`. -/
def firstExampleOpen (k : Type u) [Field k] : (firstExampleScheme k).Opens :=
  ⨆ i : ℕ, PrimeSpectrum.basicOpen (firstExampleX k i)

/-- The inclusion of the open union into `Spec(R)`. -/
def firstExampleOpenInclusion (k : Type u) [Field k] :
    (firstExampleOpen k).toScheme ⟶ firstExampleScheme k :=
  (firstExampleOpen k).ι

theorem firstExampleOpenInclusion_isOpenImmersion (k : Type u) [Field k] :
    IsOpenImmersion (firstExampleOpenInclusion k) := by
  dsimp [firstExampleOpenInclusion]
  infer_instance

/-- The open union is scheme-theoretically dense. -/
theorem firstExampleOpen_isSchemeTheoreticallyDense (k : Type u) [Field k] :
    IsSchemeTheoreticallyDominant (firstExampleOpenInclusion k) := by
  sorry

/-- The canonical map `R_g → R_{xᵢg}`. -/
noncomputable def firstExampleLocalizationComponentMap
    (k : Type u) [Field k] (g : firstExampleRing k) (i : ℕ) :
    Localization.Away g →+* Localization.Away (firstExampleX k i * g) :=
  IsLocalization.Away.awayToAwayLeft g (firstExampleX k i)

/-- The displayed map `R_g → ∏ᵢ R_{xᵢg}`. -/
noncomputable def firstExampleLocalizationMap
    (k : Type u) [Field k] (g : firstExampleRing k) :
    Localization.Away g →+* (∀ i : ℕ, Localization.Away (firstExampleX k i * g)) :=
  RingHom.pi (fun i => firstExampleLocalizationComponentMap k g i)

/-- The localization map in the source is injective for every `g`. -/
theorem firstExampleLocalizationMap_injective (k : Type u) [Field k] :
    ∀ g : firstExampleRing k, Function.Injective (firstExampleLocalizationMap k g) := by
  sorry

/-! ## Gabber's function rings -/

/-- The ring of all functions `ℕ → k`. -/
abbrev gabberFunctionRing (k : Type u) [Field k] := ℕ → k

abbrev gabberFunctionRingSpectrum (k : Type u) [Field k] :=
  PrimeSpectrum (CommRingCat.of (gabberFunctionRing k))

/-- The predicate that a function is eventually constant. -/
def GabberEventuallyConstant {k : Type u} [Field k]
    (f : gabberFunctionRing k) : Prop :=
  ∃ c : k, ∀ᶠ n : ℕ in atTop, f n = c

/-- The eventually constant functions form a subring of `k^ℕ`. -/
def gabberEventuallyConstantSubring (k : Type u) [Field k] :
    Subring (gabberFunctionRing k) where
  carrier := {f | GabberEventuallyConstant f}
  zero_mem' := by
    refine ⟨0, Eventually.of_forall (fun _ => rfl)⟩
  one_mem' := by
    refine ⟨1, Eventually.of_forall (fun _ => rfl)⟩
  add_mem' := by
    rintro f g ⟨a, ha⟩ ⟨b, hb⟩
    refine ⟨a + b, ?_⟩
    filter_upwards [ha, hb] with n hna hnb
    change f n + g n = a + b
    rw [hna, hnb]
  mul_mem' := by
    rintro f g ⟨a, ha⟩ ⟨b, hb⟩
    refine ⟨a * b, ?_⟩
    filter_upwards [ha, hb] with n hna hnb
    change f n * g n = a * b
    rw [hna, hnb]
  neg_mem' := by
    rintro f ⟨a, ha⟩
    refine ⟨-a, ?_⟩
    filter_upwards [ha] with n hn
    change -(f n) = -a
    rw [hn]

/-- The ring `R'` of eventually constant functions. -/
abbrev gabberEventuallyConstantRing (k : Type u) [Field k] :=
  gabberEventuallyConstantSubring k

/-- The inclusion `R' → R`. -/
def gabberEventuallyConstantRingInclusion (k : Type u) [Field k] :
    gabberEventuallyConstantRing k →+* gabberFunctionRing k :=
  (gabberEventuallyConstantSubring k).subtype

/-- Every function in `R` is a unit times an idempotent. -/
theorem gabberFunctionRing_unit_mul_idempotent (k : Type u) [Field k] :
    ∀ f : gabberFunctionRing k, ∃ u e : gabberFunctionRing k,
      IsUnit u ∧ IsIdempotentElem e ∧ f = u * e := by
  sorry

/-- The characteristic function of the singleton `{n}`. -/
def gabberFunctionRingCoordinateIdempotent (k : Type u) [Field k] (n : ℕ) :
    gabberFunctionRing k :=
  fun m => if m = n then 1 else 0

/-- The evaluation prime corresponding to `n ∈ ℕ` in `Spec(k^ℕ)`. -/
def gabberFunctionRingPoint (k : Type u) [Field k] (n : ℕ) :
    gabberFunctionRingSpectrum k :=
  ⟨RingHom.ker (Pi.evalRingHom (fun _ : ℕ => k) n),
    RingHom.ker_isPrime _⟩

/-- The natural points inside the spectrum of the full function ring. -/
def gabberFunctionRingNaturalPoints (k : Type u) [Field k] :
    Set (gabberFunctionRingSpectrum k) :=
  Set.range (gabberFunctionRingPoint k)

/-- The open union of the coordinate basic opens. -/
def gabberFunctionRingNaturalOpen (k : Type u) [Field k] :
    (Spec (.of (gabberFunctionRing k))).Opens :=
  ⨆ n : ℕ, PrimeSpectrum.basicOpen
    (gabberFunctionRingCoordinateIdempotent k n)

/-- The coordinate-open description agrees with the set of natural points. -/
theorem gabberFunctionRingNaturalOpen_coe (k : Type u) [Field k] :
    ((gabberFunctionRingNaturalOpen k).1 : Set (gabberFunctionRingSpectrum k)) =
      gabberFunctionRingNaturalPoints k := by
  sorry

/-- The natural points form a dense open subset of the spectrum. -/
theorem gabberFunctionRingNaturalPoints_isOpen_and_dense
    (k : Type u) [Field k] :
    IsOpen (gabberFunctionRingNaturalPoints k) ∧
      Dense (gabberFunctionRingNaturalPoints k) := by
  sorry

/-- The spectrum of the full function ring is Hausdorff. -/
theorem gabberFunctionRing_primeSpectrum_isHausdorff
    (k : Type u) [Field k] :
    T2Space (gabberFunctionRingSpectrum k) := by
  sorry

/-- The spectrum of the full function ring is the Stone–Čech compactification of `ℕ`. -/
theorem gabberFunctionRing_primeSpectrum_homeomorph_stoneCech
    (k : Type u) [Field k] :
    Nonempty (gabberFunctionRingSpectrum k ≃ₜ StoneCech ℕ) := by
  sorry

/-! ## The locally constant-function map from the Stone–Čech footnote -/

/-- Restriction of a locally constant function along a map from the discrete `ℕ`. -/
noncomputable def gabberLocallyConstantRestriction
    (k : Type u) [Field k] (X : Type v) [TopologicalSpace X]
    (f : ℕ → X) : LocallyConstant X k →+* gabberFunctionRing k :=
  (LocallyConstant.coeFnRingHom).comp
    (LocallyConstant.comapRingHom
      (⟨f, continuous_of_discreteTopology⟩ : C(ℕ, X)))

/-- The spectrum map induced by the locally constant-function restriction. -/
noncomputable def gabberLocallyConstantSpectrumMap
    (k : Type u) [Field k] (X : Type v) [TopologicalSpace X]
    (f : ℕ → X) :
    PrimeSpectrum (gabberFunctionRing k) → PrimeSpectrum (LocallyConstant X k) :=
  PrimeSpectrum.comap (gabberLocallyConstantRestriction k X f)

/-- For a compact Hausdorff totally disconnected target, the locally constant
function spectrum is the target space.  The extra total-disconnectedness
hypothesis records the condition needed by the source's informal footnote. -/
theorem gabberLocallyConstant_primeSpectrum_homeomorph
    (k : Type u) [Field k] (X : Type v) [TopologicalSpace X]
    [CompactSpace X] [T2Space X] [TotallyDisconnectedSpace X] :
    Nonempty (PrimeSpectrum (LocallyConstant X k) ≃ₜ X) := by
  sorry

/-! ## The eventually constant ring -/

/-- The evaluation prime corresponding to a natural number in `Spec(R')`. -/
def gabberEventuallyConstantPoint (k : Type u) [Field k] (n : ℕ) :
    PrimeSpectrum (CommRingCat.of (gabberEventuallyConstantRing k)) :=
  ⟨RingHom.ker <|
      (Pi.evalRingHom (fun _ : ℕ => k) n).comp
        (gabberEventuallyConstantRingInclusion k),
    RingHom.ker_isPrime _⟩

/-- The natural points of `Spec(R')`. -/
def gabberEventuallyConstantNaturalPoints (k : Type u) [Field k] :
    Set (PrimeSpectrum (CommRingCat.of (gabberEventuallyConstantRing k))) :=
  Set.range (gabberEventuallyConstantPoint k)

/-- The spectrum of `R'` is the one-point compactification of `ℕ`. -/
theorem gabberEventuallyConstant_primeSpectrum_homeomorph_onePoint
    (k : Type u) [Field k] :
    ∃ e : PrimeSpectrum (CommRingCat.of (gabberEventuallyConstantRing k)) ≃ₜ OnePoint ℕ,
      ∀ n : ℕ, e (gabberEventuallyConstantPoint k n) = (n : OnePoint ℕ) := by
  sorry

/-- There is exactly one point of `Spec(R')` outside the natural points. -/
theorem gabberEventuallyConstant_primeSpectrum_unique_extra_point
    (k : Type u) [Field k] :
    ∃! p : PrimeSpectrum (CommRingCat.of (gabberEventuallyConstantRing k)),
      p ∉ gabberEventuallyConstantNaturalPoints k := by
  sorry

/-! ## Minimal primes and weak association in Gabber's examples -/

/-- Every prime of the full function ring is minimal. -/
theorem gabberFunctionRing_all_primes_are_minimal
    (k : Type u) [Field k] :
    ∀ p : Ideal (gabberFunctionRing k), p.IsPrime →
      p ∈ minimalPrimes (gabberFunctionRing k) := by
  sorry

/-- Every prime of the full function ring is weakly associated to the ring. -/
theorem gabberFunctionRing_all_primes_are_weaklyAssociated
    (k : Type u) [Field k] :
    ∀ p : Ideal (gabberFunctionRing k), p.IsPrime →
      IsWeaklyAssociatedPrime p (gabberFunctionRing k) := by
  sorry

/-- Every prime of the eventually constant ring is minimal. -/
theorem gabberEventuallyConstant_all_primes_are_minimal
    (k : Type u) [Field k] :
    ∀ p : Ideal (gabberEventuallyConstantRing k), p.IsPrime →
      p ∈ minimalPrimes (gabberEventuallyConstantRing k) := by
  sorry

/-- Every prime of the eventually constant ring is weakly associated to the ring. -/
theorem gabberEventuallyConstant_all_primes_are_weaklyAssociated
    (k : Type u) [Field k] :
    ∀ p : Ideal (gabberEventuallyConstantRing k), p.IsPrime →
      IsWeaklyAssociatedPrime p (gabberEventuallyConstantRing k) := by
  sorry

/-- The two Gabber rings are reduced. -/
theorem gabberFunctionRing_isReduced (k : Type u) [Field k] :
    _root_.IsReduced (gabberFunctionRing k) := by
  sorry

theorem gabberEventuallyConstantRing_isReduced (k : Type u) [Field k] :
    _root_.IsReduced (gabberEventuallyConstantRing k) := by
  sorry

/-- The reduced Gabber example has a weakly associated point outside its
dense open set of natural points. -/
theorem gabberFunctionRing_exists_weaklyAssociatedPoint_not_mem_naturalOpen
    (k : Type u) [Field k] :
    ∃ x : (Spec (.of (gabberFunctionRing k))),
      IsWeaklyAssociatedPoint (Spec (.of (gabberFunctionRing k))) x ∧
        x ∉ gabberFunctionRingNaturalOpen k := by
  sorry

/-! ## The chapter's final lemma -/

/-- There is a reduced scheme with a scheme-theoretically dense open missing
a weakly associated point. -/
theorem exists_reduced_scheme_schemeTheoreticallyDenseOpen_missing_weaklyAssociatedPoint :
    ∃ (X : Scheme) (U : X.Opens),
      IsReduced X ∧ IsSchemeTheoreticallyDominant U.ι ∧
        ∃ x : X, IsWeaklyAssociatedPoint X x ∧ x ∉ U := by
  sorry

end Formalization.«Books.Examples».Unit64
