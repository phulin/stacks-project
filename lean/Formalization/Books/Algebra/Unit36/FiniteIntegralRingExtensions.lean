import Mathlib.Algebra.Algebra.Subalgebra.Pi
import Mathlib.LinearAlgebra.Prod
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.RingTheory.FinitePresentation
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Localization.Integral
import Mathlib.RingTheory.RingHom.Finite
import Mathlib.RingTheory.RingHom.FinitePresentation
import Mathlib.RingTheory.RingHom.FiniteType
import Mathlib.RingTheory.RingHom.Integral
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Formalization.Books.Algebra.Unit14.BaseChange

/-!
# Commutative Algebra, Chapter 36: Finite and integral ring extensions

Mathlib's canonical `RingHom.IsIntegralElem`, `RingHom.IsIntegral`,
`integralClosure`, `RingHom.Finite`, and `RingHom.FiniteType` interfaces are
used throughout.  The declarations below record the source's definitions and
theorem interfaces in source order; theorem proofs are deferred to the proving
stage.
-/

namespace Formalization.Books.Algebra.Unit36

universe u v w z

noncomputable section

open Set
open scoped Polynomial TensorProduct

/-! ## Integral elements and finite extensions -/

/- The definition of integrality is Mathlib's `RingHom.IsIntegralElem` and
`RingHom.IsIntegral`; the following iff records its polynomial presentation
explicitly in the chapter namespace. -/

/-- An element is integral over a ring map exactly when it is a root of a
monic polynomial after applying the map to its coefficients. -/
theorem isIntegralElem_iff
    {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (s : S) :
    f.IsIntegralElem s ↔
      ∃ p : R[X], p.Monic ∧ Polynomial.eval₂ f s p = 0 :=
  Iff.rfl

/-- A ring map is integral exactly when each target element is integral. -/
theorem isIntegral_iff
    {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) :
    f.IsIntegral ↔ ∀ s : S, f.IsIntegralElem s :=
  Iff.rfl

/-- The algebra form of integrality is the pointwise form of `Algebra.IsIntegral`. -/
theorem algebraIsIntegral_iff
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] :
    Algebra.IsIntegral R S ↔ ∀ s : S, IsIntegral R s :=
  Algebra.isIntegral_def

/-- The determinant-trick criterion for an integral element. -/
theorem isIntegral_of_finite_submodule
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (M : Submodule R S) [Module.Finite R M] (y : S)
    (h1 : (1 : S) ∈ M) (hstable : ∀ m ∈ M, y * m ∈ M) :
    IsIntegral R y := by
  sorry

/-- A finite ring map is integral. -/
theorem finite_isIntegral
    {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : f.Finite) : f.IsIntegral := by
  exact hf.to_isIntegral

/-- A finite set of integral elements is contained in a finite subalgebra, and
conversely every finite subalgebra consists of integral elements. -/
theorem finite_subalgebra_of_integral_elements
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (s : Finset S) :
    (∀ x ∈ s, IsIntegral R x) ↔
      ∃ A : Subalgebra R S, Module.Finite R A ∧ ∀ x ∈ s, x ∈ A := by
  sorry

/-- Finite is equivalent to integral and finite type. -/
theorem finite_iff_isIntegral_and_finiteType
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] :
    Module.Finite R S ↔ Algebra.IsIntegral R S ∧ Algebra.FiniteType R S :=
  Algebra.finite_iff_isIntegral_and_finiteType

/-- A ring map is finite exactly when it has finitely many integral algebra
generators. -/
theorem finite_iff_finite_integral_generators
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] :
    Module.Finite R S ↔
      ∃ s : Finset S,
        Algebra.adjoin R (s : Set S) = ⊤ ∧ ∀ x ∈ s, IsIntegral R x := by
  sorry

/-- Integrality is transitive in an algebra tower. -/
theorem integral_transitive
    {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T]
    [Algebra.IsIntegral R S] [Algebra.IsIntegral S T] :
    Algebra.IsIntegral R T := by
  exact Algebra.IsIntegral.trans S

/-! ## Integral closures -/

/- `integralClosure R S : Subalgebra R S` is Mathlib's integral-closure
construction and is the source's `R`-subalgebra of integral elements. -/

/-- The carrier of the canonical integral closure is the set of integral
elements. -/
theorem integralClosure_carrier
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] :
    (integralClosure R S : Set S) = {s : S | IsIntegral R s} :=
  rfl

/-- The base algebra is integral exactly when its integral closure is the top
subalgebra. -/
theorem integral_iff_integralClosure_eq_top
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] :
    Algebra.IsIntegral R S ↔ integralClosure R S = ⊤ := by
  exact integralClosure_eq_top_iff.symm

/-- For an injective structure map, being integrally closed is the statement
that the integral closure is just the image of the base algebra. -/
theorem integrallyClosed_iff_integralClosure_eq_bot
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (hinj : Function.Injective (algebraMap R S)) :
    integralClosure R S = ⊥ ↔ IsIntegrallyClosedIn R S := by
  exact IsIntegrallyClosedIn.integralClosure_eq_bot_iff S hinj

/-- The integral closure is integrally closed in the ambient algebra. -/
theorem integralClosure_isIntegrallyClosedIn
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] :
    IsIntegrallyClosedIn (integralClosure R S) S := by
  infer_instance

/-- Integrality of a finite product is coordinatewise. -/
theorem product_isIntegral_iff
    {ι : Type u} [Fintype ι]
    {R S : ι → Type v} [∀ i, CommRing (R i)] [∀ i, CommRing (S i)]
    (f : ∀ i, R i →+* S i) (s : ∀ i, S i) :
    (RingHom.pi (fun i => (f i).comp (Pi.evalRingHom R i))).IsIntegralElem s ↔
      ∀ i, (f i).IsIntegralElem (s i) := by
  sorry

/-- Membership in the integral closure of a product is coordinatewise. -/
theorem product_integralClosure_mem_iff
    {ι : Type u} [Fintype ι]
    {R S : ι → Type v} [∀ i, CommRing (R i)] [∀ i, CommRing (S i)]
    [∀ i, Algebra (R i) (S i)] (s : ∀ i, S i) :
    s ∈ integralClosure (∀ i, R i) (∀ i, S i) ↔
      ∀ i, s i ∈ integralClosure (R i) (S i) := by
  sorry

/-- A product extension is integrally closed exactly when each factor is. -/
theorem product_isIntegrallyClosedIn_iff
    {ι : Type u} [Fintype ι]
    {R S : ι → Type v} [∀ i, CommRing (R i)] [∀ i, CommRing (S i)]
    [∀ i, Algebra (R i) (S i)] :
    IsIntegrallyClosedIn (∀ i, R i) (∀ i, S i) ↔
      ∀ i, IsIntegrallyClosedIn (R i) (S i) := by
  sorry

/-- The integral-closure construction commutes with localization. -/
theorem integralClosure_localization
    {R S Rf Sf : Type*}
    [CommRing R] [CommRing S] [CommRing Rf] [CommRing Sf]
    [Algebra R S] [Algebra R Rf] [Algebra S Sf] [Algebra Rf Sf]
    [Algebra R Sf] [IsScalarTower R S Sf] [IsScalarTower R Rf Sf]
    (M : Submonoid R) [IsLocalization M Rf]
    [IsLocalization (Algebra.algebraMapSubmonoid S M) Sf]
    [Algebra (integralClosure R S) (integralClosure Rf Sf)]
    [IsScalarTower (integralClosure R S) (integralClosure Rf Sf) Sf]
    [IsScalarTower R (integralClosure R S) (integralClosure Rf Sf)] :
    IsLocalization
      (Algebra.algebraMapSubmonoid (integralClosure R S) M)
      (integralClosure Rf Sf) := by
  sorry

/-- An element is integral exactly when its image in every prime localization
is integral. -/
theorem isIntegral_iff_integral_at_prime
    {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (x : S) :
    f.IsIntegralElem x ↔
      ∀ p : PrimeSpectrum R,
        (IsLocalization.map
            (M := p.asIdeal.primeCompl)
            (S := Localization p.asIdeal.primeCompl)
            (P := S)
            (T := Submonoid.map (f : R →* S) p.asIdeal.primeCompl)
            (Q := Localization (Submonoid.map (f : R →* S) p.asIdeal.primeCompl))
            f
            (show p.asIdeal.primeCompl ≤
                Submonoid.comap (f : R →* S)
                  (Submonoid.map (f : R →* S) p.asIdeal.primeCompl) from
              p.asIdeal.primeCompl.le_comap_map)).IsIntegralElem
          (algebraMap S (Localization (Submonoid.map (f : R →* S) p.asIdeal.primeCompl)) x) := by
  sorry

/-! ## Base change and locality -/

/-- Integrality is preserved by the tensor-product base change map. -/
theorem integral_base_change
    {R S R' : Type*} [CommRing R] [CommRing S] [CommRing R']
    (f : R →+* S) (g : R →+* R') (hf : f.IsIntegral) :
    letI : Algebra R S := f.toAlgebra
    letI : Algebra R R' := g.toAlgebra
    (Formalization.Books.Algebra.Unit14.baseChangeRingMap f g).IsIntegral := by
  sorry

/-- Finiteness is preserved by the tensor-product base change map. -/
theorem finite_base_change
    {R S R' : Type*} [CommRing R] [CommRing S] [CommRing R']
    (f : R →+* S) (g : R →+* R') (hf : f.Finite) :
    letI : Algebra R S := f.toAlgebra
    letI : Algebra R R' := g.toAlgebra
    (Formalization.Books.Algebra.Unit14.baseChangeRingMap f g).Finite := by
  sorry

/-- Integrality and finiteness can be checked on a finite principal-open cover. -/
theorem integral_finite_local_iff
    {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (s : Finset R) (hs : Ideal.span (s : Set R) = ⊤) :
    ((∀ r : s, (Localization.awayMap f r).IsIntegral) → f.IsIntegral) ∧
      ((∀ r : s, (Localization.awayMap f r).Finite) → f.Finite) := by
  sorry

/-- If a composite is integral, then its second map is integral; the finite
analogue holds as well. -/
theorem integral_finite_permanence
    {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
    (f : A →+* B) (g : B →+* C)
    : ((g.comp f).IsIntegral → g.IsIntegral) ∧
      ((g.comp f).Finite → g.Finite) := by
  sorry

/- The canonical `IsIntegralClosure.tower_top` is the source-facing
transitivity principle for successive integral closures. -/
/-- Integral closures are transitive in a ring tower. -/
theorem integralClosure_transitive
    {A B C B' C' : Type*}
    [CommRing A] [CommRing B] [CommRing C] [CommRing B'] [CommRing C']
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    [Algebra A B'] [Algebra B' B] [IsScalarTower A B' B]
    [Algebra B' C] [Algebra C' C] [IsScalarTower A B' C]
    [IsIntegralClosure B' A B] [IsIntegralClosure C' B' C] :
    IsIntegralClosure C' A C := by
  sorry

/-! ## Spectra and field consequences -/

/-- An injective integral ring map induces a surjection on prime spectra. -/
theorem primeSpectrum_comap_surjective_of_integral
    {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : f.IsIntegral) (hinj : Function.Injective f) :
    Function.Surjective (PrimeSpectrum.comap f) := by
  sorry

/-- An integral subring of a field is a field, and the field is algebraic over
the subring. -/
theorem integral_subring_of_field
    {R K : Type*} [CommRing R] [Field K] [Algebra R K]
    [FaithfulSMul R K] [Algebra.IsIntegral R K] :
    IsField R ∧ Algebra.IsAlgebraic R K := by
  sorry

/-- A finite subring of a field is a field and the field is finite algebraic
over it. -/
theorem finite_subring_of_field
    {R K : Type*} [CommRing R] [Field K] [Algebra R K]
    [FaithfulSMul R K] [Module.Finite R K] :
    IsField R ∧ Module.Finite R K ∧ Algebra.IsAlgebraic R K := by
  sorry

/-- A domain that is integral over a field is a field. -/
theorem integral_domain_over_field_isField
    {k S : Type*} [Field k] [CommRing S] [Algebra k S]
    [IsDomain S] [Algebra.IsIntegral k S] :
    IsField S := by
  sorry

/-- A finite-dimensional domain algebra over a field is a field. -/
theorem finiteDimensional_domain_over_field_isField
    {k S : Type*} [Field k] [CommRing S] [Algebra k S]
    [IsDomain S] [Module.Finite k S] :
    IsField S := by
  sorry

/-- In an integral algebra over a field, every prime ideal is maximal. -/
theorem prime_isMaximal_of_integral_over_field
    {k S : Type*} [Field k] [CommRing S] [Algebra k S]
    [Algebra.IsIntegral k S] (p : PrimeSpectrum S) :
    p.asIdeal.IsMaximal := by
  sorry

/-- Distinct primes in an integral extension with the same contraction are
incomparable. -/
theorem primes_incomparable_of_same_comap
    {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : f.IsIntegral)
    (q q' : PrimeSpectrum S)
    (heq : PrimeSpectrum.comap f q = PrimeSpectrum.comap f q')
    (hneq : q ≠ q') :
    ¬ q.asIdeal ≤ q'.asIdeal ∧ ¬ q'.asIdeal ≤ q.asIdeal := by
  sorry

/-- A finite ring map has finite fibers on prime spectra. -/
theorem finite_primeSpectrum_fiber
    {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : f.Finite) (p : PrimeSpectrum R) :
    {q : PrimeSpectrum S | PrimeSpectrum.comap f q = p}.Finite := by
  sorry

/-- Going up for integral ring maps. -/
theorem integral_going_up
    {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : f.IsIntegral)
    (p p' : Ideal R) [hp : p.IsPrime] [hp' : p'.IsPrime]
    (hpp' : p ≤ p') (q : Ideal S) [hq : q.IsPrime]
    (hqp : q.comap f = p) :
    ∃ q' : Ideal S, q ≤ q' ∧ q'.IsPrime ∧ q'.comap f = p' := by
  sorry

/-! ## Finite and finitely presented modules -/

/-- For a finite, finitely presented ring map, finite presentation of an
S-module is independent of whether scalars are restricted to R. -/
theorem finite_finitelyPresented_module_iff
    {R S M : Type*} [CommRing R] [CommRing S]
    [AddCommGroup M] [Module S M]
    (f : R →+* S) (hfinite : f.Finite)
    (hfp : f.FinitePresentation) :
    (letI : Module R M := Module.compHom M f;
      Module.FinitePresentation R M) ↔
      Module.FinitePresentation S M := by
  sorry

/-! ## The final short exact sequence -/

/-- The canonical common localization used for the two ratio subalgebras. -/
abbrev ratioLocalization (R : Type u) [CommRing R] (x y : R) :=
  Localization.Away (x * y)

/-- The element denoted by `x / y` in the localization away from `x * y`. -/
noncomputable def ratioXY
    {R : Type u} [CommRing R] (x y : R) : ratioLocalization R x y := by
  let hy : IsUnit (algebraMap R (ratioLocalization R x y) y) :=
    IsLocalization.Away.isUnit_of_dvd (x * y) (dvd_mul_left y x)
  exact algebraMap R (ratioLocalization R x y) x *
    ((hy.unit⁻¹ : Units (ratioLocalization R x y)) : ratioLocalization R x y)

/-- The element denoted by `y / x` in the localization away from `x * y`. -/
noncomputable def ratioYX
    {R : Type u} [CommRing R] (x y : R) : ratioLocalization R x y := by
  let hx : IsUnit (algebraMap R (ratioLocalization R x y) x) :=
    IsLocalization.Away.isUnit_of_dvd (x * y) (dvd_mul_right x y)
  exact algebraMap R (ratioLocalization R x y) y *
    ((hx.unit⁻¹ : Units (ratioLocalization R x y)) : ratioLocalization R x y)

/-- The `R[x/y]` subalgebra in the common localization. -/
noncomputable def ratioXYSubalgebra
    {R : Type u} [CommRing R] (x y : R) :
    Subalgebra R (ratioLocalization R x y) :=
  Algebra.adjoin R ({ratioXY x y} : Set (ratioLocalization R x y))

/-- The `R[y/x]` subalgebra in the common localization. -/
noncomputable def ratioYXSubalgebra
    {R : Type u} [CommRing R] (x y : R) :
    Subalgebra R (ratioLocalization R x y) :=
  Algebra.adjoin R ({ratioYX x y} : Set (ratioLocalization R x y))

/-- The subalgebra generated by both ratios.  It is written as a supremum so
the two inclusion maps are canonical lattice inclusions. -/
noncomputable def ratioBothSubalgebra
    {R : Type u} [CommRing R] (x y : R) :
    Subalgebra R (ratioLocalization R x y) :=
  ratioXYSubalgebra x y ⊔ ratioYXSubalgebra x y

/-- The source's “generated by both ratios” description agrees with the
supremum used for the inclusion maps. -/
theorem ratioBothSubalgebra_eq_adjoin
    {R : Type u} [CommRing R] (x y : R) :
    ratioBothSubalgebra x y =
      Algebra.adjoin R ({ratioXY x y, ratioYX x y} : Set (ratioLocalization R x y)) := by
  sorry

/-- Inclusion of `R[x/y]` into `R[x/y,y/x]`. -/
noncomputable def ratioXYToBoth
    {R : Type u} [CommRing R] (x y : R) :
    ratioXYSubalgebra x y →ₐ[R] ratioBothSubalgebra x y :=
  Subalgebra.inclusion le_sup_left

/-- Inclusion of `R[y/x]` into `R[x/y,y/x]`. -/
noncomputable def ratioYXToBoth
    {R : Type u} [CommRing R] (x y : R) :
    ratioYXSubalgebra x y →ₐ[R] ratioBothSubalgebra x y :=
  Subalgebra.inclusion le_sup_right

/-- The left map in the final sequence, `r ↦ (-r,r)`. -/
noncomputable def sillyNormalLeft
    {R : Type u} [CommRing R] (x y : R) :
    R →ₗ[R] ratioXYSubalgebra x y × ratioYXSubalgebra x y :=
  (-Algebra.linearMap R (ratioXYSubalgebra x y)).prod
    (Algebra.linearMap R (ratioYXSubalgebra x y))

/-- The right map in the final sequence, `(a,b) ↦ a+b`. -/
noncomputable def sillyNormalRight
    {R : Type u} [CommRing R] (x y : R) :
    (ratioXYSubalgebra x y × ratioYXSubalgebra x y) →ₗ[R]
      ratioBothSubalgebra x y :=
  (ratioXYToBoth x y).toLinearMap.comp
      (LinearMap.fst R (ratioXYSubalgebra x y) (ratioYXSubalgebra x y)) +
    (ratioYXToBoth x y).toLinearMap.comp
      (LinearMap.snd R (ratioXYSubalgebra x y) (ratioYXSubalgebra x y))

/-- The final source sequence is short exact for nonzerodivisors when the base
ring is integrally closed in either of the two one-element localizations. -/
theorem silly_normal_short_exact
    {R : Type u} [CommRing R] (x y : R)
    (hx : x ∈ nonZeroDivisors R) (hy : y ∈ nonZeroDivisors R)
    (hclosed :
      IsIntegrallyClosedIn R (Localization.Away x) ∨
        IsIntegrallyClosedIn R (Localization.Away y)) :
    Function.Injective (sillyNormalLeft x y) ∧
      Function.Exact (sillyNormalLeft x y) (sillyNormalRight x y) ∧
      Function.Surjective (sillyNormalRight x y) := by
  sorry

end

end Formalization.Books.Algebra.Unit36
